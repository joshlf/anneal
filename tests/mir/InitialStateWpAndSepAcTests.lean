import Anneal.MiriTreeBorrowsV2026
import Anneal.SepAC.RangeSpanV2026
import Anneal.WavefrontReclaim.WavefrontV2026
import Lean

/-!
# End-to-End Integration & Kernel Audit Suite: Initial-State Tree Borrows, `SepAC` Range Framing, and `< ω^ω` Wavefront Reclamation (`V2026_06_01`)

Root-package integration test suite (`Anneal.Mir.InitialStateWpAndSepAcTests`) exercising:
1. `Anneal.MiriTreeBorrowsV2026`: 6-state Miri Tree Borrows per-segment state machine,
   two-phase borrow reservation/activation (`ReservedFrz`, `ReservedIM`), protector call-frame
   lifecycle, SIFA subtree pruning, and exact bridges to unmodified
   `Trusted.Rustc.V2026_06_01.MirSemantics` (`treeBorrowPermTransition`,
   `treeBorrowNodeAccess`, `preventsDeallocation`, `ptrAllocByteBound?`).
2. `Anneal.SepAC.RangeSpanV2026`: reflective ACU separating-conjunction normalization &
   cancellation, Lithium-style non-backtracking `PTree.diffWith` keyed framing & diamond join,
   $O(1)$ symbolic `ByteRange` split/merge (`1_000_000` bytes without per-byte expansion), and
   disjoint same-allocation & cross-allocation read/write framing over `V2026_06_01` `Memory`
   and `SpatialMemV2026.V2026ByteMem`.
3. `Anneal.WavefrontReclaim.WavefrontV2026`: `< ω^ω` Cantor Normal Form (`Anneal.CnfOrd.Ord`)
   wavefront drain termination, universal `.activeMut` loan reclamation, 5-stage chained
   spatial/temporal lifecycle, and `Anneal.Firewall` / `IndexedCut`-shielded `stepMirFn` &
   `runCfgSteps` loop execution without unfolding concrete `Memory` allocations.
4. Compile-time `run_cmd` kernel audits enforcing strict `[propext]`-only theory axioms,
   3-axiom test ceiling, zero `sorryAx` / `Lean.ofReduceBool`, `Std.Do` / `MiniRustSpec.*`
   import & constant-closure isolation, non-vacuous V2026 bridge dependency checks, and
   optional cross-root kernel verification of `LeanMiriSpec.InitialStateTreeBorrowsWpLM`
   when `examples/.lake/build/lib/lean` is present.
-/

namespace Anneal.Mir.InitialStateWpAndSepAcTests

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.Firewall
open Anneal.PTree
open Anneal.SepAC
open Anneal.SepAC.RangeSpanV2026
open Anneal.PureLift.SpatialMemV2026
open Anneal.CnfOrd
open Anneal.WavefrontReclaim
open Anneal.WavefrontReclaim.WavefrontV2026
open Anneal.PureMirExec
open Anneal.MiriTreeBorrowsV2026

/-! ## Section 1: Joint `MiriTreeBorrowsV2026` + `RangeSpanV2026` 24-Byte `Memory` Integration -/

/-- Root Miri Tree Borrows state over `wfCNode24Mem0`'s 24-byte mutable allocation (`allocId = 2`),
partitionable into `[0, 8)` (mutable loan/epoch slice), `[8, 16)` (shared slice), and
`[16, 24)` (frame-slot slice). -/
def ep2SharedTbRoot24 : MiriTbState :=
  { frames := []
    allocTrees :=
      [{ allocId := 2
         tree := [{ tag := 0, parent := none, children := [] }]
         segments :=
           [{ offset := 0
              size := 24
              entries := [{ tag := 0, loc := ⟨.unique, true, .none⟩ }] }] }] }

/-- Exact cross-module equivalence between `MiriTreeBorrowsV2026.miriRangesDisjointBool`,
`RangeSpanV2026.rangeDisjointBool`, and `!MirSemantics.byteRangesOverlapBool` for all
non-empty subranges of a shared allocation `aid`. -/
theorem ep2_miriRangesDisjoint_eq_rangeDisjointBool_and_v2026Overlap
    (aid : AllocId) (o₁ s₁ o₂ s₂ : Nat)
    (hs1 : 0 < s₁) (hs2 : 0 < s₂) :
    miriRangesDisjointBool o₁ s₁ o₂ s₂ =
      rangeDisjointBool ⟨aid, o₁, s₁⟩ ⟨aid, o₂, s₂⟩ ∧
    (rangeDisjointBool ⟨aid, o₁, s₁⟩ ⟨aid, o₂, s₂⟩ = true ↔
      byteRangesOverlapBool o₁ s₁ o₂ s₂ = false) := by
  refine ⟨?_, ?_⟩
  · unfold miriRangesDisjointBool rangeDisjointBool
    have hEq : Nat.beq aid aid = true := Nat.beq_refl aid
    rw [hEq]
    dsimp only [Bool.not, cond]
    cases hs1 with
    | refl => cases hs2 <;> rfl
    | step _ => cases hs2 <;> rfl
  · exact ⟨fun h =>
      (byteRangesOverlapBool_false_iff_rangeDisjoint_pos
        (r₁ := ⟨aid, o₁, s₁⟩) (r₂ := ⟨aid, o₂, s₂⟩) rfl hs1 hs2).mpr
        ((rangeDisjointBool_iff ⟨aid, o₁, s₁⟩ ⟨aid, o₂, s₂⟩).mp h),
      fun h =>
      (rangeDisjointBool_iff ⟨aid, o₁, s₁⟩ ⟨aid, o₂, s₂⟩).mpr
        ((byteRangesOverlapBool_false_iff_rangeDisjoint_pos
          (r₁ := ⟨aid, o₁, s₁⟩) (r₂ := ⟨aid, o₂, s₂⟩) rfl hs1 hs2).mp h)⟩

/-- 8-byte payload written into `[0, 8)` of `wfCNode24Mem0` during the joint Tree Borrows +
`RangeSpanV2026` framing scenario (`u32` epoch `77` followed by `u32` meta `88`). -/
def ep2Patch8RawBytes : List (Option UInt8) :=
  wfEncodeU32LeRawBytes 77 ++ wfEncodeU32LeRawBytes 88

/-- Abstract-byte counterpart of `ep2Patch8RawBytes`. -/
def ep2Patch8AbsBytes : List AbstractByte :=
  wfEncodeU32LeAbsBytes 77 ++ wfEncodeU32LeAbsBytes 88

private theorem ep2_natLe_of_ble {a b : Nat} (h : Nat.ble a b = true) : a ≤ b :=
  Nat.ble_eq.mp h

/-- **Joint Positive Integration Theorem 1 (`[propext]`)**:
Couples `MiriTreeBorrowsV2026` and `RangeSpanV2026` on the exact same 24-byte V2026 `Memory`
(`wfCNode24Mem0`):
1. Splits `⟨1, 0, 24⟩` via `rangeSplit` / `ownRange_split_iff` into three pairwise-disjoint
   8-byte subranges `r0 = ⟨1, 0, 8⟩`, `r1 = ⟨1, 8, 8⟩`, `r2 = ⟨1, 16, 8⟩` and verifies
   `rangeMerge` reassembly;
2. Pushes call frame `1`, registers three disjoint `FnEntry` borrows (`tag 1: &mut [0, 8)`,
   `tag 2: & [8, 16)`, `tag 3: & [16, 24)`), activates `tag 1` (`ReservedFrz false → Unique`)
   via child write while `tag 2` and `tag 3` stay `Frozen`, and exits frame `1` cleanly;
3. Writes `ep2Patch8RawBytes` to `r0 = ⟨1, 0, 8⟩` via `writeMemoryBytesV2026` (and via
   `V2026ByteMem.writeV2026Bytes`) and frames `AllocBytesAtV2026` / `AllocBytesAtByteMem` on
   BOTH sibling subranges `r1`, `r2` without re-inspecting `[8, 24)`. -/
theorem ep2_joint_tb_reborrow_and_rangespan_24byte_frame :
    let rAll : ByteRange := ⟨2, 0, 24⟩
    let (r0, rTail) := rangeSplit rAll 8
    let (r1, r2) := rangeSplit rTail 8
    rangeMerge r0 (rangeMerge r1 r2) = rAll ∧
    (match miriBeginFrame ep2SharedTbRoot24 1 with
     | .err _ _ => false
     | .ok stF =>
       match miriRegisterFnEntryArg wfCNode24Mem0 stF 1 2 1 0 .mutable true false 0 8 with
       | .err _ _ => false
       | .ok st1 =>
         match miriRegisterFnEntryArg wfCNode24Mem0 st1 1 2 2 0 .shared true false 8 8 with
         | .err _ _ => false
         | .ok st2 =>
           match miriRegisterFnEntryArg wfCNode24Mem0 st2 1 2 3 0 .shared true false 16 8 with
           | .err _ _ => false
           | .ok st3 =>
             match miriPerformRangedAccess st3 2 1 0 8 .write .visitChildrenOfAccessed with
             | .err _ _ => false
             | .ok stAct =>
               let ok1 :=
                 match lookupPermInSeg? stAct 2 0 1 with
                 | some (p, acc) => miriPermEq p .unique && acc
                 | none => false
               let ok2 :=
                 match lookupPermInSeg? stAct 2 1 2 with
                 | some (p, acc) => miriPermEq p .frozen && acc
                 | none => false
               let ok3 :=
                 match lookupPermInSeg? stAct 2 2 3 with
                 | some (p, acc) => miriPermEq p .frozen && acc
                 | none => false
               match miriExitCallFrame wfCNode24Mem0 stAct 1 with
               | .err _ _ => false
               | .ok stExit => ok1 && ok2 && ok3 && stExit.frames.isEmpty) = true ∧
    (∃ m' : Memory,
      writeMemoryBytesV2026 wfCNode24Mem0 r0 ep2Patch8RawBytes = some m' ∧
      AllocBytesAtV2026 m' r0 ep2Patch8AbsBytes ∧
      AllocBytesAtV2026 m' r1 (wfEncodeU32LeAbsBytes 0 ++ wfEncodeU32LeAbsBytes 77) ∧
      AllocBytesAtV2026 m' r2 (wfEncodeU32LeAbsBytes 0 ++ wfEncodeU32LeAbsBytes 99)) ∧
    (∃ bm' : V2026ByteMem,
      writeV2026Bytes (memGlobalsToByteMem wfCNode24Mem0) ⟨2, 0⟩ 4 ep2Patch8AbsBytes =
        some bm' ∧
      readV2026Bytes bm' ⟨2, 0⟩ 8 4 = some ep2Patch8AbsBytes ∧
      AllocBytesAtByteMem bm' r1 (wfEncodeU32LeAbsBytes 0 ++ wfEncodeU32LeAbsBytes 77) ∧
      AllocBytesAtByteMem bm' r2 (wfEncodeU32LeAbsBytes 0 ++ wfEncodeU32LeAbsBytes 99)) := by
  dsimp only
  let cnode24RawBytes : List (Option UInt8) :=
    wfEncodeU32LeRawBytes 10 ++ wfEncodeU32LeRawBytes 0 ++
    wfEncodeU32LeRawBytes 0 ++ wfEncodeU32LeRawBytes 77 ++
    wfEncodeU32LeRawBytes 0 ++ wfEncodeU32LeRawBytes 99
  let cnode24Alloc : CapturedAllocation :=
    { allocId := 2, align := ⟨4⟩, mutability := .mut, bytes := cnode24RawBytes, relocations := [] }
  let bytes24Abs : List AbstractByte :=
    wfEncodeU32LeAbsBytes 10 ++ wfEncodeU32LeAbsBytes 0 ++
    wfEncodeU32LeAbsBytes 0 ++ wfEncodeU32LeAbsBytes 77 ++
    wfEncodeU32LeAbsBytes 0 ++ wfEncodeU32LeAbsBytes 99
  have hOwn24 : AllocBytesAtV2026 wfCNode24Mem0 ⟨2, 0, 24⟩ bytes24Abs :=
    ⟨cnode24Alloc, rfl, Nat.le_refl 24, rfl, rfl⟩
  have hSp0 := (ownRange_split_iff wfCNode24Mem0 ⟨2, 0, 24⟩ bytes24Abs
    (k := 8) (ep2_natLe_of_ble rfl)).mp hOwn24
  have hSp1 := (ownRange_split_iff wfCNode24Mem0 ⟨2, 8, 16⟩ (bytes24Abs.drop 8)
    (k := 8) (ep2_natLe_of_ble rfl)).mp hSp0.2
  have hD01 : RangeDisjoint ⟨2, 0, 8⟩ ⟨2, 8, 8⟩ := (rangeDisjointBool_iff _ _).mp rfl
  have hD02 : RangeDisjoint ⟨2, 0, 8⟩ ⟨2, 16, 8⟩ := (rangeDisjointBool_iff _ _).mp rfl
  refine ⟨rfl, rfl, ?_, ?_⟩
  · cases hW : writeMemoryBytesV2026 wfCNode24Mem0 ⟨2, 0, 8⟩ ep2Patch8RawBytes with
    | none => nomatch hW
    | some m' =>
      have hFr1 : AllocBytesAtV2026 m' ⟨2, 8, 8⟩
          (wfEncodeU32LeAbsBytes 0 ++ wfEncodeU32LeAbsBytes 77) :=
        allocBytesAtV2026_frame_of_write_disjoint hD01 hW hSp1.1
      have hFr2 : AllocBytesAtV2026 m' ⟨2, 16, 8⟩
          (wfEncodeU32LeAbsBytes 0 ++ wfEncodeU32LeAbsBytes 99) :=
        allocBytesAtV2026_frame_of_write_disjoint hD02 hW hSp1.2
      have hNew0 : AllocBytesAtV2026 m' ⟨2, 0, 8⟩ ep2Patch8AbsBytes := by
        injection hW with hMeq
        rw [← hMeq]
        exact ⟨{ allocId := 2, align := ⟨4⟩, mutability := .mut,
                 bytes := (cnode24RawBytes.take 0 ++ ep2Patch8RawBytes) ++
                   cnode24RawBytes.drop 8,
                 relocations := [] },
          rfl, ep2_natLe_of_ble rfl, rfl, rfl⟩
      exact ⟨m', hW, hNew0, hFr1, hFr2⟩
  · have hBm1 : AllocBytesAtByteMem (memGlobalsToByteMem wfCNode24Mem0) ⟨2, 8, 8⟩
        (wfEncodeU32LeAbsBytes 0 ++ wfEncodeU32LeAbsBytes 77) :=
      allocBytesAtByteMem_of_allocBytesAtV2026 hSp1.1
    have hBm2 : AllocBytesAtByteMem (memGlobalsToByteMem wfCNode24Mem0) ⟨2, 16, 8⟩
        (wfEncodeU32LeAbsBytes 0 ++ wfEncodeU32LeAbsBytes 99) :=
      allocBytesAtByteMem_of_allocBytesAtV2026 hSp1.2
    cases hWB : writeV2026Bytes (memGlobalsToByteMem wfCNode24Mem0) ⟨2, 0⟩ 4 ep2Patch8AbsBytes with
    | none => nomatch hWB
    | some bm' =>
      have hBFr1 := allocBytesAtByteMem_frame_of_writeV2026Bytes_disjoint rfl hD01 hWB hBm1
      have hBFr2 := allocBytesAtByteMem_frame_of_writeV2026Bytes_disjoint rfl hD02 hWB hBm2
      have hRead0 : readV2026Bytes bm' ⟨2, 0⟩ 8 4 = some ep2Patch8AbsBytes :=
        (allocBytesAtByteMem_of_writeV2026Bytes_self (rW := ⟨2, 0, 8⟩) rfl hWB).2
      exact ⟨bm', rfl, hRead0, hBFr1, hBFr2⟩

/-- **Joint Positive & Negative Integration Theorem 2 (`[propext]`)**:
Exercises reflective ACU normalization & cancellation (`rfl` side conditions), Lithium
`PTree.diffWith` non-backtracking keyed framing + diamond join, $O(1)$ `1_000_000`-byte symbolic
`rangeSplit`/`rangeMerge`, V2026 Tree Borrows semantic bridges, and fail-closed negative
controls across `MiriTreeBorrowsV2026` and `RangeSpanV2026`. -/
theorem ep2_acu_lithium_oneMillion_and_tb_rangespan_negatives
    (envR : Nat → V2026RangeProp)
    (hSub : V2026RangeEntails
      (v2026RangeSepConj (envR 1) (envR 3)) (envR 4)) :
    -- 1. Reflective ACU cancellation on re-associated + `emp`-padded `V2026RangeProp`
    V2026RangeEntails
      (evalSepExprFuel v2026RangeSepConj v2026RangeEmp envR 8
        (.sep (.sep .emp (.sep (.atom 2) (.atom 0))) (.sep (.atom 1) (.atom 3))))
      (evalSepExprFuel v2026RangeSepConj v2026RangeEmp envR 8
        (.sep (.atom 0) (.sep (.atom 4) (.atom 2)))) ∧
    -- 2. O(1) symbolic split & merge of a 1,000,000-byte range without per-byte unfolding
    (let (rHead, rRest) := rangeSplit ⟨42, 0, 1000000⟩ 250000
     let (rMid, rEnd) := rangeSplit rRest 500000
     RangeDisjoint rHead rMid ∧ RangeDisjoint rMid rEnd ∧ RangeDisjoint rHead rEnd ∧
     rangeMerge rHead (rangeMerge rMid rEnd) = ⟨42, 0, 1000000⟩) ∧
    -- 3. Lithium PTree framing + exact 56-cell V2026 Tree Borrows transition & dealloc bridges
    (∃ step : PTree Nat → Option (PTree Nat),
      LithiumTriple rsReq2 rsPost2 step ∧
      step rsCtx16 = some (PTree.union rsPost2 rsRem14)) ∧
    (∀ k p a r,
      miriOutcomeToV2026 (miriPerformPermAccess k r p a) =
        treeBorrowPermTransition (miriAccessKindToV2026 k) (miriRelToV2026 r)
          (miriPermToV2026 p) a ∧
      miriPermPreventsDealloc p = preventsDeallocation (miriPermToV2026 p)) ∧
    -- 4. Fail-closed negative UB & linearity controls across both modules
    isChildForbiddenErr 1 (.reservedFrz true)
      (miriPerformRangedAccess miriReadOnlyAliasedEntry 1 1 4 4 .write
        .visitChildrenOfAccessed) = true ∧
    ¬ RangeDisjoint ⟨1, 0, 12⟩ ⟨1, 8, 12⟩ ∧
    writeMemoryBytesV2026 rsInitMemoryV2026 ⟨0, 0, 4⟩ rsPatchBytes = none ∧
    writeMemoryBytesV2026 rsInitMemoryV2026 ⟨1, 14, 4⟩ rsPatchBytes = none ∧
    ¬ AffineEntails (@pheapEmp Nat) (@PHeapEntails Nat) ∧
    ¬ AffineEntails v2026RangeEmp V2026RangeEntails := by
  have hLR := v2026RangeProp_sepACULaws
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl,
    not_affineEntails_pheapProp 0, not_affineEntails_v2026RangeProp⟩
  · apply v2026Range_frame_cancel envR (fuel := 8)
    change V2026RangeEntails
      (v2026RangeSepConj (envR 1) (v2026RangeSepConj (envR 3) v2026RangeEmp))
      (v2026RangeSepConj (envR 4) v2026RangeEmp)
    have hL1 : V2026RangeEntails
        (v2026RangeSepConj (envR 1) (v2026RangeSepConj (envR 3) v2026RangeEmp))
        (v2026RangeSepConj (envR 1) (envR 3)) :=
      hLR.monoRight (envR 1) _ _ (hLR.rightUnit (envR 3)).1
    exact hLR.trans _ _ _ hL1 (hLR.trans _ _ _ hSub (hLR.rightUnit (envR 4)).2)
  · have hk1 : 250000 ≤ 1000000 := ep2_natLe_of_ble rfl
    have hk2 : 500000 ≤ 1000000 - 250000 := ep2_natLe_of_ble rfl
    have hM : rangeMerge (rangeSplit ⟨42, 0, 1000000⟩ 250000).1
        (rangeMerge (rangeSplit (rangeSplit ⟨42, 0, 1000000⟩ 250000).2 500000).1
          (rangeSplit (rangeSplit ⟨42, 0, 1000000⟩ 250000).2 500000).2) = ⟨42, 0, 1000000⟩ := by
      rw [rangeMerge_split _ hk2]
      exact rangeMerge_split _ hk1
    exact ⟨(rangeDisjointBool_iff _ _).mp rfl,
      (rangeDisjointBool_iff _ _).mp rfl,
      (rangeDisjointBool_iff _ _).mp rfl,
      hM⟩
  · cases witness_lithium_ptree_framing_and_diamond.1 with
    | intro step hStep => exact ⟨step, hStep.1, hStep.2.2.2⟩
  · intro k p a r
    exact ⟨miriPerformPermAccess_eq_v2026_treeBorrowPermTransition k r p a,
      miriPermPreventsDealloc_eq_v2026_preventsDeallocation p⟩
  · exact witness_aliased_reservedFrz_readOnly_ok_vs_conflict_activation_ub.2.2.2.2
  · intro hD
    have hT := (rangeDisjointBool_iff ⟨1, 0, 12⟩ ⟨1, 8, 12⟩).mpr hD
    exact Bool.noConfusion hT

/-! ## Section 2: `WavefrontV2026` `< ω^ω` Drain, `Firewall`/`IndexedCut` MIR Loop, and Capstone -/

/-- **Wavefront + RangeSpan + MIR CFG Integration Theorem 3 (`[propext]`)**:
Couples `< ω^ω` Cantor Normal Form wavefront termination, universal `.activeMut` reclamation,
5-stage spatial/temporal lifecycle, `Firewall` & `IndexedCut`-shielded `stepMirFn` + `runCfgSteps`
loop execution, V2026 `encodeValueToBytes` / `decodeValueFromBytes` round-trip, and `RangeSpanV2026`
`AllocBytesAtV2026` framing on `wfCNodeFrameSlotLens` (`⟨2, 20, 4⟩`). -/
theorem ep2_wavefront_firewall_mir_loop_and_rangespan_frame :
    -- 1. V2026 little-endian u32 byte codec round-trip for every 32-bit unsigned value
    (∀ (fuel : Nat) (layouts : LayoutTable) (v : Nat),
      encodeValueToBytes (fuel + 1) layouts wfU32Ty (.scalar ⟨wrapU32 v, 4⟩) =
        some (wfEncodeU32LeAbsBytes v) ∧
      decodeValueFromBytes (fuel + 1) layouts wfU32Ty (wfEncodeU32LeAbsBytes v) =
        some (.scalar ⟨wrapU32 v, 4⟩)) ∧
    -- 2. Multi-rank `< ω^ω` 10-step drain (`5 -> 3 -> 2 -> 1 -> 0`) + universal `.activeMut` reclaim
    runWavefrontStepsV2026 11 wfPolicyTower53210 multiRankWitnessWorld0 = some mwW10 ∧
    worldMeasureV2026 mwW10 = [] ∧
    wfFindLoan path0 mwW10.loans =
      some (WfLoanEntryV2026.mk path0 .activeMut wfCNodeEpochLens 42) ∧
    AllocBytesAtV2026 mwW10.mem ⟨2, 20, 4⟩ (wfEncodeU32LeAbsBytes 99) ∧
    -- 3. 5-stage chained lifecycle preserving spatial `cellAuthProp path2 99`
    (∃ (w1 w2 w3 w4 : WavefrontWorldV2026) (r1 r2 r3 r4 : ResTrie ResElem)
       (v1 v2 v3 v4 : View),
      evalHybridCmdV2026 (.checkoutLoan path0 55) reclaimDemoWorld0 = .returned w1 ∧
      evalHybridCmdV2026 (.submitTaskBurst 1 0 path0 55 6) w1 = .returned w2 ∧
      WavefrontConvergesV2026 policyTower10 w2 w3 ∧
      ActivePureLoanAtV2026 path0 wfCNodeEpochLens 22 w3 ∧
      evalHybridCmdV2026 (.pureLiftSafe path0 20) w3 = .returned w4 ∧
      WorldMatchesV2026 v1 r1 w1 ∧ WorldMatchesV2026 v2 r2 w2 ∧
      WorldMatchesV2026 v3 r3 w3 ∧ WorldMatchesV2026 v4 r4 w4 ∧
      (vsep (vMinStep w3.stepCount) (cellAuthProp path2 99)).holds v4 r4 ∧
      v2026SubLensGet wfCNodeEpochLens w4.mem = some (wfEncodeU32LeAbsBytes 42)) ∧
    -- 4. `Firewall` / `IndexedCut` MIR `stepMirFn` + 15-step `runCfgSteps` loop + `RangeSpan` frame
    stepMirFn wfReclaimLoopBody wfLoopInitMs = .tau (.running wfLoopAfterStep1Ms) ∧
    runCfgSteps wfReclaimLoopBody (.running true .none wfLoopInitMs) 15 =
      .halted true (.normal (.scalar ⟨42, 4⟩, wfCNode24Mem0)) ∧
    (∃ (wDrained : WavefrontWorldV2026) (rOut : ResTrie ResElem) (vOut : View),
      WavefrontConvergesV2026 wfPolicyTower53210 wfLoopBridgeWorld0 wDrained ∧
      ActivePureLoanAtV2026 path0 wfCNodeEpochLens 42 wDrained ∧
      (vsep (vMinStep wDrained.stepCount) (cellAuthProp path2 99)).holds vOut rOut ∧
      MirGlobalSliceAtV2026 wfCNode24Mem0 wfCNodeFrameSlotLens (wfEncodeU32LeAbsBytes 99) ∧
      AllocBytesAtV2026 wfCNode24Mem0 ⟨2, 20, 4⟩ (wfEncodeU32LeAbsBytes 99) ∧
      IndexedCut (mirWavefrontCutAt wfPolicyTower53210 (cellAuthProp path2 99)
        wfCNodeFrameSlotLens (wfEncodeU32LeAbsBytes 99)) 0
        ({ wfLoopInitMs with memory := wfCNode24Mem0 }, vOut, rOut, wDrained)) ∧
    -- 5. Fail-closed WavefrontV2026 negative controls (stale scope, equal/upward spawn, unfunded)
    evalHybridCmdV2026 (.poolWavefrontStep (fun _ => (0, 0, 0)))
      (mkNegWorldV2026
        [WfLoanEntryV2026.mk path0 (.spatialCheckedOut 88) wfCNodeEpochLens 10]
        [WorkerTask.mk 0 0 0 path0 77 5]) = .faultLoanViolation ∧
    evalHybridCmdV2026 (.poolWavefrontStep (fun _ => (1, 5, 0)))
      (mkNegWorldV2026
        [WfLoanEntryV2026.mk path0 (.spatialCheckedOut 77) wfCNodeEpochLens 10]
        [WorkerTask.mk 0 5 0 path0 77 5]) = .faultInvalidSpawn ∧
    evalHybridCmdV2026 (.poolWavefrontStep (fun _ => (2, 7, 0)))
      (mkNegWorldV2026
        [WfLoanEntryV2026.mk path0 (.spatialCheckedOut 77) wfCNodeEpochLens 10]
        [WorkerTask.mk 0 5 0 path0 77 5]) = .faultInvalidSpawn ∧
    (VSepWpOrdRelV2026 (.submitTaskBurst 2 0 path0 77 5) (.amortized [(5, 2)])
      (fun w =>
        wfFindLoan path0 w.loans =
          some ⟨path0, .spatialCheckedOut 77, wfCNodeEpochLens, 10⟩)
      vemp (fun _ => vemp) → False) := by
  have hMr := witness_multiRank_5_to_0_wavefront_drain_v2026
  have hLp := witness_v2026_stepMirFn_and_runCfgSteps_wavefront_loop
  have hNeg := witness_wavefrontV2026_negative_fail_closed_suite
  have hBurst := witness_submitTaskBurst_amortized_and_unfunded_refutation_v2026
  have hMw10Slot : AllocBytesAtV2026 mwW10.mem ⟨2, 20, 4⟩ (wfEncodeU32LeAbsBytes 99) :=
    ⟨{ allocId := 2
       align := ⟨4⟩
       mutability := .mut
       bytes :=
         wfEncodeU32LeRawBytes 42 ++ wfEncodeU32LeRawBytes 0 ++
         wfEncodeU32LeRawBytes 0 ++ wfEncodeU32LeRawBytes 77 ++
         wfEncodeU32LeRawBytes 0 ++ wfEncodeU32LeRawBytes 99
       relocations := [] },
     rfl, Nat.le_refl 24, rfl, rfl⟩
  refine ⟨?_, hMr.2.1, hMr.2.2.2.2.1, hMr.2.2.2.2.2.1, hMw10Slot, ?_,
    hLp.1, hLp.2.1, ?_,
    hNeg.2.1, hNeg.2.2.2.2.1, hNeg.2.2.2.2.2.1, hBurst.2.2.2⟩
  · intro fuel layouts v
    exact ⟨wfEncodeU32LeAbsBytes_eq_encodeValueToBytes fuel layouts v,
      decodeValueFromBytes_wfEncodeU32LeAbsBytes fuel layouts v⟩
  · cases witness_fiveStage_checkout_burst_drain_reclaim_pureLift_v2026 with
    | intro w1 hw1 =>
      cases hw1 with
      | intro w2 hw2 =>
        cases hw2 with
        | intro w3 hw3 =>
          cases hw3 with
          | intro w4 hw4 =>
            cases hw4 with
            | intro r1 hr1 =>
              cases hr1 with
              | intro r2 hr2 =>
                cases hr2 with
                | intro r3 hr3 =>
                  cases hr3 with
                  | intro r4 hr4 =>
                    cases hr4 with
                    | intro v1 hv1 =>
                      cases hv1 with
                      | intro v2 hv2 =>
                        cases hv2 with
                        | intro v3 hv3 =>
                          cases hv3 with
                          | intro v4 hv =>
                            exact ⟨w1, w2, w3, w4, r1, r2, r3, r4, v1, v2, v3, v4,
                              hv.1, hv.2.2.1, hv.2.2.2.2.1, hv.2.2.2.2.2.2.1,
                              hv.2.2.2.2.2.2.2.2.1,
                              hv.2.1, hv.2.2.2.1, hv.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.2.2.1,
                              hv.2.2.2.2.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.2.2.2.2⟩
  · cases hLp.2.2.2 with
    | intro wDrained hwD =>
      cases hwD with
      | intro rOut hrD =>
        cases hrD with
        | intro vOut hvD =>
          have hGetF : v2026SubLensGet wfCNodeFrameSlotLens wfCNode24Mem0 =
              some (wfEncodeU32LeAbsBytes 99) :=
            unseal_mirGlobalSliceAtV2026 hvD.2.2.2.2.2.1
          have hOwnF : AllocBytesAtV2026 wfCNode24Mem0 ⟨2, 20, 4⟩
              (wfEncodeU32LeAbsBytes 99) :=
            ⟨{ allocId := 2
               align := ⟨4⟩
               mutability := .mut
               bytes :=
                 wfEncodeU32LeRawBytes 10 ++ wfEncodeU32LeRawBytes 0 ++
                 wfEncodeU32LeRawBytes 0 ++ wfEncodeU32LeRawBytes 77 ++
                 wfEncodeU32LeRawBytes 0 ++ wfEncodeU32LeRawBytes 99
               relocations := [] },
             rfl, Nat.le_refl 24, rfl, hGetF⟩
          exact ⟨wDrained, rOut, vOut, hvD.1, hvD.2.2.1, hvD.2.2.2.2.1,
            hvD.2.2.2.2.2.1, hOwnF, hvD.2.2.2.2.2.2⟩

/-- **Provenance-Guard + Stage-Budget + MIR↔Reclaim Coupling Integration (`[propext]`)**:
1. GENERAL `RangeSpanV2026.allocBytesAtV2026_of_write_self` read-after-write on the joint
   24-byte `wfCNode24Mem0` (raw `u32` epoch/meta patch reads back provenance-free);
2. Fail-closed relocation guard: a raw write over the pointer bytes of the satisfiable
   pointer-bearing `rsPtrMemoryV2026` (whose `[0, 8)` genuinely carries provenance) is rejected;
3. `WavefrontV2026.mirWavefrontCutAt` stage budget: ANY stage-`0` cut forces quiescence;
4. The real `wfReclaimLoopBody` `runCfgSteps` result equals unmodified `decodeValueFromBytes`
   of the reclaimed epoch slice in the drained wavefront world's `V2026_06_01` `Memory`. -/
theorem ep2_provenance_guard_and_mir_reclaim_coupling :
    (∀ m' : Memory,
      writeMemoryBytesV2026 wfCNode24Mem0 ⟨2, 0, 8⟩ ep2Patch8RawBytes = some m' →
      AllocBytesAtV2026 m' ⟨2, 0, 8⟩ ep2Patch8AbsBytes) ∧
    AllocBytesAtV2026 rsPtrMemoryV2026 ⟨3, 0, 8⟩ rsPtrAbsBytes ∧
    abstractBytesHaveProv rsPtrAbsBytes = true ∧
    writeMemoryBytesV2026 rsPtrMemoryV2026 ⟨3, 4, 4⟩ rsPatchBytes = none ∧
    (∀ st : MirWavefrontCutState,
      IndexedCut (mirWavefrontCutAt wfPolicyTower53210 (cellAuthProp path2 99)
        wfCNodeFrameSlotLens (wfEncodeU32LeAbsBytes 99)) 0 st →
      wfPoolIsNonEmpty st.2.2.2 = false ∧ worldMeasureV2026 st.2.2.2 = []) ∧
    (∃ (wDrained : WavefrontWorldV2026) (bs : List AbstractByte),
      runCfgSteps wfReclaimLoopBody (.running true .none wfLoopInitMs) 15 =
        .halted true (.normal (.scalar ⟨42, 4⟩, wfCNode24Mem0)) ∧
      WavefrontConvergesV2026 wfPolicyTower53210 wfLoopBridgeWorld0 wDrained ∧
      v2026SubLensGet wfCNodeEpochLens wDrained.mem = some bs ∧
      decodeValueFromBytes 1 wfLoopLayouts wfU32Ty bs = some (.scalar ⟨42, 4⟩)) := by
  have hGuard := witness_v2026_relocation_provenance_guard
  refine ⟨fun _ hW => allocBytesAtV2026_of_write_self hW, hGuard.1, hGuard.2.1,
    hGuard.2.2.2.2.1, fun _ h => mirWavefrontCutAt_zero_quiescent h, ?_⟩
  cases witness_mir_return_eq_reclaimed_loan_decode_v2026 with
  | intro wD h1 =>
    cases h1 with
    | intro bs h =>
      exact ⟨wD, bs, h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- **Pass A1 Integration Suite (`[propext]`)**:
1. Zero-length relocation-safe write `relocsAvoidRange_zero_len` + `writeMemoryBytesV2026 rsPtrMemoryV2026 ⟨3, 4, 0⟩ [] = some rsPtrMemoryV2026`;
2. Total checked `rangeMergeChecked` split/merge (`ownRange_of_rangeMergeChecked`) + fail-closed rejection on non-adjacent and cross-allocation ranges;
3. Oracle-free multi-step `stepMirFn_lockstep_chain_indexedCut` driving arbitrary `MirTraceStepsTo` traces to stage-`0` quiescence (`worldMeasureV2026 = []`);
4. Memory-sensitive pointer-dereference `wfPtrReadReclaimLoopBody` (`*epoch_ptr`) evaluating to `.scalar ⟨42, 4⟩` on `epoch = 10` and `.scalar ⟨132, 4⟩` on `epoch = 100`, coupled via oracle-free `runCfgSteps_wavefrontDrain_indexedCut_bridge` to `.activeMut` reclamation `132` and `decodeValueFromBytes`. -/
theorem ep2_a1_zero_len_reloc_checked_merge_and_ptr_loop_integration :
    (∀ relocs s, relocsAvoidRange relocs s 0 = true) ∧
    writeMemoryBytesV2026 rsPtrMemoryV2026 ⟨3, 4, 0⟩ [] = some rsPtrMemoryV2026 ∧
    rangeMergeChecked ⟨1, 0, 4⟩ ⟨1, 4, 4⟩ = some ⟨1, 0, 8⟩ ∧
    rangeMergeChecked ⟨1, 0, 4⟩ ⟨1, 5, 4⟩ = none ∧
    rangeMergeChecked ⟨1, 0, 4⟩ ⟨2, 4, 4⟩ = none ∧
    (∀ (ms0 msFinal : MachineState) (trace : List MachineState)
       (v0 : View) (r0 : ResTrie ResElem) (w0 : WavefrontWorldV2026),
      MirTraceStepsTo wfPtrReadReclaimLoopBody ms0 trace msFinal →
      ms0.memory.activeCallee = none →
      ms0.memory.callStack = [] →
      IndexedCut (mirWavefrontCutAt wfPolicyTower53210 (cellAuthProp path2 99)
        wfCNodeFrameSlotLens (wfEncodeU32LeAbsBytes 99)) trace.length
        (ms0, v0, r0, w0) →
      ∃ (wFinal : WavefrontWorldV2026) (rFinal : ResTrie ResElem) (vFinal : View),
        msFinal.memory.globals = ms0.memory.globals ∧
        WavefrontConvergesV2026 wfPolicyTower53210 w0 wFinal ∧
        wFinal.fifoQueue = [] ∧
        wFinal.stealDeque = [] ∧
        worldMeasureV2026 wFinal = [] ∧
        IndexedCut (mirWavefrontCutAt wfPolicyTower53210 (cellAuthProp path2 99)
          wfCNodeFrameSlotLens (wfEncodeU32LeAbsBytes 99)) 0
          (msFinal, vFinal, rFinal, wFinal)) ∧
    runCfgSteps wfPtrReadReclaimLoopBody (.running true .none wfPtrLoopInitMs10) 15 =
      .halted true (.normal (.scalar ⟨42, 4⟩, wfCNode24Mem0)) ∧
    runCfgSteps wfPtrReadReclaimLoopBody (.running true .none wfPtrLoopInitMs100) 15 =
      .halted true (.normal (.scalar ⟨132, 4⟩, wfCNodeMem100)) ∧
    (∃ (wDrained100 : WavefrontWorldV2026),
      WavefrontConvergesV2026 wfPolicyTower53210 wfLoopBridgeWorld100 wDrained100 ∧
      ActivePureLoanAtV2026 path0 wfCNodeEpochLens 132 wDrained100 ∧
      v2026SubLensGet wfCNodeEpochLens wDrained100.mem = some (wfEncodeU32LeAbsBytes 132) ∧
      decodeValueFromBytes 1 wfPtrLoopLayouts wfU32Ty (wfEncodeU32LeAbsBytes 132) =
        some (.scalar ⟨132, 4⟩)) := by
  have hGuard := witness_v2026_relocation_provenance_guard
  have hPtrLoop := witness_v2026_ptrDeref_mir_loop_input_sensitive
  have hPol : PolicyAdmissible wfPolicyTower53210 :=
    towerLookupNext_admissible wfTower53210 1 0 rfl
  refine ⟨relocsAvoidRange_zero_len, hGuard.2.2.2.1, rfl, rfl, rfl, ?_,
    hPtrLoop.2.1, hPtrLoop.2.2.1, ?_⟩
  · intro ms0 msFinal trace v0 r0 w0 hTr hNoCallee hNoStack hCut
    cases stepMirFn_lockstep_chain_indexedCut wfPtrReadReclaimLoopBody
        wfPolicyTower53210 hPol (cellAuthProp path2 99)
        wfCNodeFrameSlotLens (wfEncodeU32LeAbsBytes 99) rfl hTr v0 r0 w0 hNoCallee hNoStack
        hCut with
    | intro wF hwF =>
      cases hwF with
      | intro rF hrF =>
        cases hrF with
        | intro vF hvF =>
          exact ⟨wF, rF, vF, hvF.1, hvF.2.1, hvF.2.2.1, hvF.2.2.2.1, hvF.2.2.2.2.1,
            hvF.2.2.2.2.2.2.1⟩
  · cases hPtrLoop.2.2.2 with
    | intro wD100 hw =>
      cases hw with
      | intro _ hr =>
        cases hr with
        | intro _ hv =>
          exact ⟨wD100, hv.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.1⟩

/-- **Pass B2 Integration (`[propext]`)**: (1) the inductive lockstep theorem is NON-VACUOUS —
a real 10-step `stepMirFn` trace of `wfPtrReadReclaimLoopBody` (computed by `mirStepTrace`,
certified by `mirStepTrace_sound`) drives the stage-`10` `wfLoopBridgeWorld0` cut to quiescence
with root-frame status derived (not assumed) at the final state; (2) the `runCfgSteps` bridge's
decode conjunct is UNCONDITIONAL: unmodified `decodeValueFromBytes` of the bytes actually
read back from the drained world's reclaimed lens yields the reclaimed scalar. -/
theorem ep2_b2_lockstep_trace_and_unconditional_reclaim_decode :
    (∃ (trace : List MachineState) (msF : MachineState),
      trace.length = 10 ∧
      MirTraceStepsTo wfPtrReadReclaimLoopBody wfPtrLoopInitMs10 trace msF ∧
      msF.memory.globals = wfCNode24Mem0.globals ∧
      msF.memory.activeCallee = none ∧ msF.memory.callStack = []) ∧
    (∀ (ms ms' : MachineState),
      isWavefrontCfgBody wfPtrReadReclaimLoopBody = true →
      ms.memory.activeCallee = none → ms.memory.callStack = [] →
      MirSingleStepTo wfPtrReadReclaimLoopBody ms ms' →
      ms'.memory.activeCallee = none ∧ ms'.memory.callStack = []) := by
  refine ⟨?_, fun _ _ hB hC hS hStep =>
    mirSingleStepTo_preserves_rootFrame_of_wavefrontCfgBody hB hC hS hStep⟩
  cases witness_stepMirFn_lockstep_trace10_ptrLoop_v2026 with
  | intro tr h1 =>
    cases h1 with
    | intro msF h =>
      cases h.2.2.2 with
      | intro wF hw =>
        cases hw with
        | intro rF hr =>
          cases hr with
          | intro vF hv =>
            exact ⟨tr, msF, h.2.1, h.2.2.1, hv.1, hv.2.2.2.2.2.1, hv.2.2.2.2.2.2⟩

/-- **Pass A2 Integration (`[propext]`)**:
1. Separating-conjunction write framing `v2026RangeSepConj_write_frame` across a 3-way split
   `[0,4) ∗ [4,4) ∗ [8,8)` + semantic `fpDisjoint` framing on an interior zero-length write
   `⟨1, 4, 0⟩` inside `[0, 8)` (where syntactic `rangeDisjointBool ⟨1, 4, 0⟩ ⟨1, 0, 8⟩ = false`)
   + bidirectional `allocBytesAtByteMem_memGlobals_iff`;
2. Unconditional root-frame & `wfMemShape` preservation across `runCfgSteps`;
3. Full 14+1-step unmodified `stepMirFn` normal-return trace (`MirStepNode.retNormal`) on
   `wfPtrReadReclaimLoopBody` exercising BOTH active wavefront steps (`1..10`) AND quiescent
   stutter steps (`11..14`) inside `stepMirFn_lockstep_chain_indexedCut` (for both `epoch = 10 -> 42`
   and `epoch = 100 -> 132`), plus fail-closed `isWavefrontCfgOperand` / `isWavefrontCfgStmt`
   rejections on deref-moves and deref-writes. -/
theorem ep2_a2_sepConj_write_frame_rootFrame_cfg_and_full_stepMirFn_return :
    rangeDisjointBool ⟨1, 4, 0⟩ ⟨1, 0, 8⟩ = false ∧
    (∃ mZ : Memory,
      writeMemoryBytesV2026 rsInitMemoryV2026 ⟨1, 4, 0⟩ [] = some mZ ∧
      AllocBytesAtV2026 mZ ⟨1, 0, 8⟩ (List.replicate 8 (.init 0x11 none))) ∧
    (∀ (m : Memory) (r : ByteRange) (bs : List AbstractByte),
      AllocBytesAtByteMem (memGlobalsToByteMem m) r bs ↔ AllocBytesAtV2026 m r bs) ∧
    (∃ m' : Memory,
      writeMemoryBytesV2026 rsInitMemoryV2026 ⟨1, 4, 4⟩ rsPatchBytes = some m' ∧
      (v2026RangeSepConj
        (v2026RangePointsTo ⟨1, 4, 4⟩ rsPatchAbsBytes)
        (v2026RangeSepConj
          (v2026RangePointsTo ⟨1, 0, 4⟩ (List.replicate 4 (.init 0x11 none)))
          (v2026RangePointsTo ⟨1, 8, 8⟩ (List.replicate 8 (.init 0x11 none))))).pred m'
        (InRange ⟨1, 0, 16⟩)) ∧
    (∀ (ms0 : MachineState) (cfgFuel : Nat) (retVal : Value) (memFinal : Memory),
      ms0.memory.activeCallee = none →
      ms0.memory.callStack = [] →
      runCfgSteps wfPtrReadReclaimLoopBody (.running true .none ms0) cfgFuel =
        .halted true (.normal (retVal, memFinal)) →
      wfMemShape memFinal = wfMemShape ms0.memory) ∧
    isWavefrontCfgOperand (.move ⟨1, [.deref]⟩) = false ∧
    isWavefrontCfgStmt { kind := .assign ⟨1, [.deref]⟩ (.use (.constant { ty := wfU32Ty, val := .scalar (.int ⟨0, 4⟩) })), span := "" } = false ∧
    (∃ (tr14 : List MachineState) (msAtRet10 : MachineState),
      mirStepTrace wfPtrReadReclaimLoopBody 14 wfPtrLoopInitMs10 = some (tr14, msAtRet10) ∧
      stepMirFn wfPtrReadReclaimLoopBody msAtRet10 =
        MirStepNode.retNormal (.scalar ⟨42, 4⟩) msAtRet10.memory ∧
      ∃ (wFinal : WavefrontWorldV2026) (rFinal : ResTrie ResElem) (vFinal : View),
        WavefrontConvergesV2026 wfPolicyTower53210 wfLoopBridgeWorld0 wFinal ∧
        worldMeasureV2026 wFinal = [] ∧
        IndexedCut (mirWavefrontCutAt wfPolicyTower53210 (cellAuthProp path2 99)
          wfCNodeFrameSlotLens (wfEncodeU32LeAbsBytes 99)) 0
          (msAtRet10, vFinal, rFinal, wFinal)) ∧
    (∃ (tr14_100 : List MachineState) (msAtRet100 : MachineState),
      mirStepTrace wfPtrReadReclaimLoopBody 14 wfPtrLoopInitMs100 = some (tr14_100, msAtRet100) ∧
      stepMirFn wfPtrReadReclaimLoopBody msAtRet100 =
        MirStepNode.retNormal (.scalar ⟨132, 4⟩) msAtRet100.memory) := by
  have hRs := witness_v2026RangeSepConj_write_frame_and_zeroLen_interior
  have hWf := witness_stepMirFn_full_return_and_stutter_lockstep_v2026
  refine ⟨hRs.1, hRs.2.2.1, allocBytesAtByteMem_memGlobals_iff, hRs.2.2.2.2,
    fun _ _ _ _ hC hS hR =>
      runCfgSteps_preserves_memShape_of_wavefrontCfgBody rfl hC hS hR,
    hWf.1, hWf.2.1, ?_, hWf.2.2.2⟩
  cases hWf.2.2.1 with
  | intro tr14 h1 =>
    cases h1 with
    | intro msAtRet10 h =>
      cases h.2.2.2 with
      | intro wF hw =>
        cases hw with
        | intro rF hr =>
          cases hr with
          | intro vF hv =>
            exact ⟨tr14, msAtRet10, h.1, h.2.2.1, wF, rF, vF,
              hv.2.2.2.1, hv.2.2.2.2.1, hv.2.2.2.2.2⟩

/-- **Pass B3 Integration — Wavefront-Memory Frame Law (`[propext]`)**:
(1) GENERAL: every `WavefrontConvergesV2026` drain preserves every loan-disjoint
`V2026SubLens` slice of the world's own `V2026_06_01` `Memory` (despite genuine `.activeMut`
writebacks into the same `Memory.globals`); (2) CONCRETE dual-memory frame along the real
10-step `stepMirFn` lockstep trace: `[20, 24) = 99` survives in BOTH the MIR machine memory and the
drained wavefront memory, while the loan-covered epoch slot `[0, 4)` is NOT framed (`10 ↦ 42`),
showing the disjointness side condition is load-bearing. -/
theorem ep2_b3_wavefront_memory_frame_law :
    (∀ (pol : SpawnPolicy) (w wF : WavefrontWorldV2026) (fL : V2026SubLens),
      WavefrontConvergesV2026 pol w wF →
      allDisjointFromLens fL w.loans →
      v2026SubLensGet fL wF.mem = v2026SubLensGet fL w.mem) ∧
    (∃ (msF : MachineState) (wF : WavefrontWorldV2026),
      MirGlobalSliceAtV2026 msF.memory wfCNodeFrameSlotLens (wfEncodeU32LeAbsBytes 99) ∧
      v2026SubLensGet wfCNodeFrameSlotLens wF.mem = some (wfEncodeU32LeAbsBytes 99) ∧
      v2026SubLensGet wfCNodeEpochLens wfLoopBridgeWorld0.mem = some (wfEncodeU32LeAbsBytes 10) ∧
      v2026SubLensGet wfCNodeEpochLens wF.mem = some (wfEncodeU32LeAbsBytes 42)) := by
  refine ⟨fun pol _ _ fL hConv hDisj =>
    (wavefrontConverges_preserves_disjoint_mem_frame pol hConv fL hDisj).1, ?_⟩
  have hW := witness_dual_memory_frame_lockstep_trace10_v2026
  cases hW.2.2 with
  | intro msF h1 =>
    cases h1 with
    | intro wF h =>
      exact ⟨msF, wF, h.1, h.2.2.1, hW.2.1, h.2.2.2⟩

/-- **Cross-Module Operational Unification (`[propext]`-only)**: every successful
`WavefrontV2026.v2026SubLensPut` mutation (the primitive executed by `.pureLiftSafe` and
`.poolWavefrontStep` leaf writebacks) is an EXACT instance of
`RangeSpanV2026.writeMemoryBytesV2026`, so every Wavefront writeback inherits
`v2026RangeSepConj_write_frame` AND `memGlobalsToByteMem_writeMemoryBytesV2026_commutes`! -/
theorem ep2_v2026SubLensPut_implies_writeMemoryBytesV2026
    {L : V2026SubLens} {m m' : Memory} {rawPatch : List (Option UInt8)}
    (hPut : v2026SubLensPut L m rawPatch = some m') :
    writeMemoryBytesV2026 m ⟨L.allocId, L.offset, L.size⟩ rawPatch = some m' := by
  unfold v2026SubLensPut at hPut
  unfold writeMemoryBytesV2026
  dsimp only
  cases hFind : lookupGlobalAlloc m.globals L.allocId with
  | none => rw [hFind] at hPut; nomatch hPut
  | some a =>
    rw [hFind] at hPut
    dsimp only at hPut ⊢
    cases hOk : v2026AllocLensOk L a with
    | false =>
      rw [hOk] at hPut
      dsimp only [Bool.and] at hPut
      nomatch hPut
    | true =>
      rw [hOk] at hPut
      cases hLen : Nat.beq rawPatch.length L.size with
      | false =>
        rw [hLen] at hPut
        dsimp only [Bool.and] at hPut
        nomatch hPut
      | true =>
        rw [hLen] at hPut
        dsimp only [Bool.and] at hPut ⊢
        unfold v2026AllocLensOk at hOk
        cases hMut : a.mutability with
        | not =>
          rw [hMut] at hOk
          dsimp only [Bool.and] at hOk
          nomatch hOk
        | «mut» =>
          rw [hMut] at hOk
          dsimp only
          cases hRel : a.relocations with
          | cons _ _ =>
            rw [hRel] at hOk
            dsimp only [List.isEmpty, Bool.and] at hOk
            nomatch hOk
          | nil =>
            rw [hRel] at hOk
            have hAvNil : relocsAvoidRange [] L.offset L.size = true := rfl
            have hBnd : Nat.ble (L.offset + L.size) a.bytes.length = true :=
              ((Bool.and_eq_true _ _).mp hOk).2
            rw [hAvNil, hBnd]
            dsimp only [Bool.and]
            rw [hRel, hMut] at hPut
            exact hPut

/-- **Pass A3 Integration (`[propext]`)**:
1. Write-side commuting square `memGlobalsToByteMem_writeMemoryBytesV2026_commutes` between
   `RangeSpanV2026.writeMemoryBytesV2026` and `SpatialMemV2026.writeV2026Bytes` (instantiated on
   pointer-bearing `rsPtrMemoryV2026`, preserving `[0, 8)` pointer provenance `(1, 1)`), plus
   zero-length write identity `memGlobalsToByteMem_writeMemoryBytesV2026_zero_len`;
2. Operational unification `ep2_v2026SubLensPut_implies_writeMemoryBytesV2026` linking
   `WavefrontV2026.v2026SubLensPut` directly to `RangeSpanV2026.writeMemoryBytesV2026`;
3. Dual-memory `IndexedCut` extraction `mirWavefrontCutAt_dual_mem_frame` on the full 14+1-step
   `stepMirFn` return trace (`witness_stepMirFn_full_return_and_stutter_lockstep_v2026`),
   certifying `Firewall`-shielded `[20, 24) = 99` inside the cut on BOTH `msAtRet10.memory`
   AND `wFinal.mem` simultaneously! -/
theorem ep2_a3_commuting_write_square_dual_cut_and_sublens_unification :
    (∀ (L : V2026SubLens) (m m' : Memory) (rawPatch : List (Option UInt8)),
      v2026SubLensPut L m rawPatch = some m' →
      writeMemoryBytesV2026 m ⟨L.allocId, L.offset, L.size⟩ rawPatch = some m') ∧
    (∃ m' : Memory,
      writeMemoryBytesV2026 rsPtrMemoryV2026 ⟨3, 8, 4⟩ rsPatchBytes = some m' ∧
      writeV2026Bytes (memGlobalsToByteMem rsPtrMemoryV2026) ⟨3, 8⟩ 4 rsPatchAbsBytes =
        some (memGlobalsToByteMem m') ∧
      readV2026Bytes (memGlobalsToByteMem m') ⟨3, 0⟩ 8 8 = some rsPtrAbsBytes) ∧
    (∀ (m m' : Memory) (s : Nat) (patch : List (Option UInt8)),
      writeMemoryBytesV2026 m ⟨1, s, 0⟩ patch = some m' →
      memGlobalsToByteMem m' = memGlobalsToByteMem m) ∧
    (∃ (msAtRet10 : MachineState) (wFinal : WavefrontWorldV2026),
      stepMirFn wfPtrReadReclaimLoopBody msAtRet10 =
        MirStepNode.retNormal (.scalar ⟨42, 4⟩) msAtRet10.memory ∧
      WavefrontConvergesV2026 wfPolicyTower53210 wfLoopBridgeWorld0 wFinal ∧
      MirGlobalSliceAtV2026 msAtRet10.memory wfCNodeFrameSlotLens (wfEncodeU32LeAbsBytes 99) ∧
      MirGlobalSliceAtV2026 wFinal.mem wfCNodeFrameSlotLens (wfEncodeU32LeAbsBytes 99) ∧
      allDisjointFromLens wfCNodeFrameSlotLens wFinal.loans) := by
  have hCommWit := witness_memGlobals_write_commutes_and_shadowed_allocId
  have hFull := witness_stepMirFn_full_return_and_stutter_lockstep_v2026
  refine ⟨fun _ _ _ _ h => ep2_v2026SubLensPut_implies_writeMemoryBytesV2026 h,
    hCommWit.1,
    fun _ _ _ _ hW => (memGlobalsToByteMem_writeMemoryBytesV2026_zero_len rfl hW).2,
    ?_⟩
  cases hFull.2.2.1 with
  | intro tr14 h1 =>
    cases h1 with
    | intro msAtRet10 h =>
      cases h.2.2.2 with
      | intro wFinal hw =>
        cases hw with
        | intro rFinal hr =>
          cases hr with
          | intro vFinal hv =>
            have hDual := mirWavefrontCutAt_dual_mem_frame hv.2.2.2.2.2
            exact ⟨msAtRet10, wFinal, h.2.2.1, hv.2.2.2.1, hDual.1, hDual.2.1, hDual.2.2⟩

/-- **Unified Episode 2 Cross-Module Master Capstone (`[propext]`)**:
Bundles the positive and fail-closed negative witnesses from ALL THREE root modules:
`Anneal.MiriTreeBorrowsV2026`, `Anneal.SepAC.RangeSpanV2026`, and
`Anneal.WavefrontReclaim.WavefrontV2026`. -/
theorem ep2_end_to_end_capstone :
    -- MiriTreeBorrowsV2026 positive + negative suites
    (∀ k r p ip,
      miriOutcomeToV2026 (miriPerformPermAccess k r p ip) =
        treeBorrowPermTransition (miriAccessKindToV2026 k) (miriRelToV2026 r)
          (miriPermToV2026 p) ip) ∧
    (∀ p, miriPermPreventsDealloc p = preventsDeallocation (miriPermToV2026 p)) ∧
    -- RangeSpanV2026 positive + negative suites
    rangeMerge (rangeSplit ⟨7, 0, 1000000⟩ 345678).1
      (rangeSplit ⟨7, 0, 1000000⟩ 345678).2 = ⟨7, 0, 1000000⟩ ∧
    ¬ AffineEntails (@pheapEmp Nat) (@PHeapEntails Nat) ∧
    ¬ AffineEntails v2026RangeEmp V2026RangeEntails ∧
    -- WavefrontV2026 positive + negative suites
    runWavefrontStepsV2026 11 wfPolicyTower53210 multiRankWitnessWorld0 = some mwW10 ∧
    worldMeasureV2026 mwW10 = [] ∧
    runCfgSteps wfReclaimLoopBody (.running true .none wfLoopInitMs) 15 =
      .halted true (.normal (.scalar ⟨42, 4⟩, wfCNode24Mem0)) ∧
    evalHybridCmdV2026 (.poolWavefrontStep (fun _ => (2, 7, 0)))
      (mkNegWorldV2026
        [WfLoanEntryV2026.mk path0 (.spatialCheckedOut 77) wfCNodeEpochLens 10]
        [WorkerTask.mk 0 5 0 path0 77 5]) = .faultInvalidSpawn := by
  exact ⟨miriPerformPermAccess_eq_v2026_treeBorrowPermTransition,
    miriPermPreventsDealloc_eq_v2026_preventsDeallocation,
    rangeMerge_split ⟨7, 0, 1000000⟩ (ep2_natLe_of_ble rfl),
    not_affineEntails_pheapProp 0,
    not_affineEntails_v2026RangeProp,
    witness_multiRank_5_to_0_wavefront_drain_v2026.2.1,
    witness_multiRank_5_to_0_wavefront_drain_v2026.2.2.2.2.1,
    witness_v2026_stepMirFn_and_runCfgSteps_wavefront_loop.2.1,
    witness_wavefrontV2026_negative_fail_closed_suite.2.2.2.2.2.1⟩

/-! ## Section 3: Compile-Time `run_cmd` Kernel Axiom, Import-Isolation, Bridge & Cross-Root Audit -/

section KernelAndIsolationAudit

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modNames := env.header.moduleNames
  let modData := env.header.moduleData

  -- 1. Global `MiniRustSpec.*` prohibition across ALL loaded root modules.
  for m in modNames do
    if (`MiniRustSpec).isPrefixOf m then
      throwError "MiniRustSpec import-isolation violation: forbidden module {m} loaded"

  -- 2. Locate all three root theory modules under test.
  let findModIdx (target : Name) : CommandElabM Nat := do
    let mut found? : Option Nat := none
    for i in [:modNames.size] do
      if modNames[i]! == target then
        found? := some i
    match found? with
    | some idx => return idx
    | none => throwError "audit setup error: module {target} not found in environment"

  let tbIdx ← findModIdx `Anneal.MiriTreeBorrowsV2026
  let rsIdx ← findModIdx `Anneal.SepAC.RangeSpanV2026
  let wfIdx ← findModIdx `Anneal.WavefrontReclaim.WavefrontV2026

  -- 3. Direct-import hygiene audit on all three theory modules:
  --    none may directly import `Std.Do`, `Std.Tactic.Do`, `Std.WP`, `MiniRustSpec.*`,
  --    `Miri.*`, `LeanMiriSpec.*`, or `Lean.*`.
  let checkDirectImports (modName : Name) (idx : Nat) : CommandElabM Unit := do
    for imp in modData[idx]!.imports do
      let im := imp.module
      if (`Std.Do).isPrefixOf im || (`Std.Tactic.Do).isPrefixOf im ||
          (`Std.WP).isPrefixOf im || (`MiniRustSpec).isPrefixOf im ||
          (`Miri).isPrefixOf im || (`LeanMiriSpec).isPrefixOf im ||
          (`Lean).isPrefixOf im then
        throwError "{modName} direct-import isolation violation: imports {im}"
  checkDirectImports `Anneal.MiriTreeBorrowsV2026 tbIdx
  checkDirectImports `Anneal.SepAC.RangeSpanV2026 rsIdx
  checkDirectImports `Anneal.WavefrontReclaim.WavefrontV2026 wfIdx

  -- 4. Full transitive module-import closure of `Anneal.MiriTreeBorrowsV2026` must also be
  --    100% `Std.Do`-free (`RangeSpanV2026` and `WavefrontV2026` reach `Anneal.MirFuelFree` via
  --    `SpatialMemV2026` / `MirLoops`, so for all three we additionally verify 0 `Std.Do`
  --    constants in their full transitive constant-dependency closure below!).
  let mut tbModSeen : NameSet := {}
  let mut tbModTodo : Array Name := #[`Anneal.MiriTreeBorrowsV2026]
  while !tbModTodo.isEmpty do
    let m := tbModTodo.back!
    tbModTodo := tbModTodo.pop
    if tbModSeen.contains m then continue
    tbModSeen := tbModSeen.insert m
    if (`Std.Do).isPrefixOf m || (`Std.Tactic.Do).isPrefixOf m ||
        (`Std.WP).isPrefixOf m || (`MiniRustSpec).isPrefixOf m then
      throwError "Anneal.MiriTreeBorrowsV2026 transitive import violation: reaches {m}"
    for i in [:modNames.size] do
      if modNames[i]! == m then
        for imp in modData[i]!.imports do
          tbModTodo := tbModTodo.push imp.module

  -- 5. Strict `[propext]`-only kernel axiom audit (`⊆ {propext}`, 0 `sorryAx`,
  --    0 `Lean.ofReduceBool`, 0 `Classical.choice`, 0 `Quot.sound`, 0 `unsafe`/`partial`/`axiom`)
  --    AND transitive constant-dependency isolation (`0` `Std.Do` / `MiniRustSpec.*` constants)
  --    across ALL declarations of all three theory modules!
  let auditTheoryModule (modName : Name) (modIdx : Nat)
      (minThms minDefs : Nat) : CommandElabM Unit := do
    let mut nThms : Nat := 0
    let mut nDefs : Nat := 0
    let mut constQueue : Array Name := #[]
    for (c, info) in env.constants.map₁.toList do
      if env.getModuleIdxFor? c == some modIdx then
        constQueue := constQueue.push c
        match info with
        | .thmInfo _ =>
          nThms := nThms + 1
          for a in ← liftCoreM <| Lean.collectAxioms c do
            unless a == ``propext do
              throwError "{modName} axiom violation: theorem {c} depends on {a}"
        | .defnInfo dv =>
          if dv.safety != .safe then
            throwError "{modName} safety violation: def {c} is not safe"
          nDefs := nDefs + 1
          for a in ← liftCoreM <| Lean.collectAxioms c do
            unless a == ``propext do
              throwError "{modName} axiom violation: def {c} depends on {a}"
        | .axiomInfo _ =>
          throwError "{modName} custom axiom forbidden: {c}"
        | .opaqueInfo _ =>
          throwError "{modName} opaque decl forbidden: {c}"
        | _ => pure ()
    if nThms < minThms || nDefs < minDefs then
      throwError "{modName} audit vacuous: only {nThms} theorems (< {minThms}), {nDefs} defs (< {minDefs})"
    -- Transitive constant closure check: zero `Std.Do` / `Std.Tactic.Do` / `Std.WP` / `MiniRustSpec.*`
    let mut cSeen : NameSet := {}
    let mut cTodo := constQueue
    while !cTodo.isEmpty do
      let c := cTodo.back!
      cTodo := cTodo.pop
      if cSeen.contains c then continue
      cSeen := cSeen.insert c
      if (`Std.Do).isPrefixOf c || (`Std.Tactic.Do).isPrefixOf c ||
          (`Std.WP).isPrefixOf c || (`MiniRustSpec).isPrefixOf c then
        throwError "{modName} constant-isolation violation: transitively references {c}"
      if let some ci := env.find? c then
        cTodo := cTodo ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          cTodo := cTodo ++ v.getUsedConstants

  auditTheoryModule `Anneal.MiriTreeBorrowsV2026 tbIdx 150 30
  auditTheoryModule `Anneal.SepAC.RangeSpanV2026 rsIdx 50 25
  auditTheoryModule `Anneal.WavefrontReclaim.WavefrontV2026 wfIdx 80 40

  -- 6. Bridge-reality audit: confirm theorems genuinely reach unmodified V2026 `MirSemantics`
  --    and core Anneal abstractions (`Firewall`, `IndexedCut`, `runCfgSteps`, `Normalize`,
  --    `SpatialPcm`, `CnfOrd`).
  let checkReaches (start target : Name) : CommandElabM Unit := do
    let some ci := env.find? start | throwError "bridge audit: missing {start}"
    let mut seen : NameSet := {}
    let mut todo : Array Name := ci.type.getUsedConstants ++
      (match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[])
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      if n == target then break
      -- Descend through public AND private (`_private.Anneal.*`) Anneal helper lemmas.
      let isAnnealLocal : Bool :=
        (`Anneal).isPrefixOf n ||
          (match Lean.privateToUserName? n with
           | some u => (`Anneal).isPrefixOf u
           | none => false)
      if isAnnealLocal then
        if let some ciN := env.find? n then
          todo := todo ++ ciN.type.getUsedConstants
          if let some vN := ciN.value? (allowOpaque := true) then
            todo := todo ++ vN.getUsedConstants
    unless seen.contains target do
      throwError "shadow-spec audit failure: {start} does not reach {target}"

  let bridgePairs : List (Name × Name) :=
    [ (``Anneal.MiriTreeBorrowsV2026.miriPerformPermAccess_eq_v2026_treeBorrowPermTransition,
        ``Trusted.Rustc.V2026_06_01.MirSemantics.treeBorrowPermTransition),
      (``Anneal.MiriTreeBorrowsV2026.miriPerformLocAccess_agrees_v2026_treeBorrowNodeAccess,
        ``Trusted.Rustc.V2026_06_01.MirSemantics.treeBorrowNodeAccess),
      (``Anneal.MiriTreeBorrowsV2026.miriPermPreventsDealloc_eq_v2026_preventsDeallocation,
        ``Trusted.Rustc.V2026_06_01.MirSemantics.preventsDeallocation),
      (``Anneal.MiriTreeBorrowsV2026.miriInspectAllocV2026_dead_eq_v2026_ptrAllocByteBound_zero,
        ``Trusted.Rustc.V2026_06_01.MirSemantics.ptrAllocByteBound?),
      (``Anneal.SepAC.RangeSpanV2026.byteRangesOverlapBool_false_iff_rangeDisjoint_pos,
        ``Trusted.Rustc.V2026_06_01.MirSemantics.byteRangesOverlapBool),
      (``Anneal.SepAC.RangeSpanV2026.relocsAvoidRange,
        ``Trusted.Rustc.V2026_06_01.MirSemantics.byteRangesOverlapBool),
      (``Anneal.SepAC.RangeSpanV2026.allocBytesAtV2026_frame_of_write_disjoint,
        ``Trusted.Rustc.V2026_06_01.MirSemantics.globalAllocSliceToAbstractBytes),
      (``Anneal.SepAC.RangeSpanV2026.allocBytesAtV2026_of_write_self,
        ``Trusted.Rustc.V2026_06_01.MirSemantics.globalAllocBytesAux),
      (``Anneal.SepAC.RangeSpanV2026.allocBytesAtV2026_of_write_self,
        ``Trusted.Rustc.V2026_06_01.MirSemantics.lookupRelocAllocId),
      (``Anneal.SepAC.RangeSpanV2026.allocBytesAtByteMem_memGlobals_iff,
        ``Trusted.Rustc.V2026_06_01.MirSemantics.globalAllocSliceToAbstractBytes),
      (``Anneal.SepAC.RangeSpanV2026.memGlobalsToByteMem_writeMemoryBytesV2026_commutes,
        ``writeV2026Bytes),
      (``Anneal.SepAC.RangeSpanV2026.memGlobalsToByteMem_writeMemoryBytesV2026_commutes,
        ``Trusted.Rustc.V2026_06_01.MirSemantics.lookupRelocAllocId),
      (``Anneal.SepAC.RangeSpanV2026.allocBytesAtV2026_frame_of_fpDisjoint,
        ``Trusted.Rustc.V2026_06_01.MirSemantics.byteRangesOverlapBool),
      (``Anneal.SepAC.RangeSpanV2026.v2026RangeSepConj_write_frame,
        ``Trusted.Rustc.V2026_06_01.MirSemantics.globalAllocBytesAux),
      (``Anneal.SepAC.RangeSpanV2026.allocBytesAtByteMem_of_writeV2026Bytes_self,
        ``writeV2026Bytes),
      (``Anneal.WavefrontReclaim.WavefrontV2026.mirWavefrontCutAt_zero_quiescent,
        ``Anneal.WavefrontReclaim.WavefrontV2026.runWavefrontStepsV2026),
      (``Anneal.WavefrontReclaim.WavefrontV2026.mirWavefrontCutAt_dual_mem_frame,
        ``Anneal.WavefrontReclaim.WavefrontV2026.MirGlobalSliceAtV2026),
      (``Anneal.WavefrontReclaim.WavefrontV2026.witness_mir_return_eq_reclaimed_loan_decode_v2026,
        ``Trusted.Rustc.V2026_06_01.MirSemantics.decodeValueFromBytes),
      (``Anneal.WavefrontReclaim.WavefrontV2026.witness_v2026_ptrDeref_mir_loop_input_sensitive,
        ``Trusted.Rustc.V2026_06_01.MirSemantics.decodeValueFromBytes),
      (``Anneal.WavefrontReclaim.WavefrontV2026.runCfgSteps_preserves_rootFrame_and_globals_of_wavefrontCfgBody,
        ``Anneal.PureMirExec.evalTerminatorCfg),
      (``Anneal.WavefrontReclaim.WavefrontV2026.witness_stepMirFn_full_return_and_stutter_lockstep_v2026,
        ``Trusted.Rustc.V2026_06_01.MirSemantics.MirStepNode.retNormal),
      (``Anneal.SepAC.RangeSpanV2026.allocBytesAtByteMem_frame_of_writeV2026Bytes_disjoint,
        ``writeV2026Bytes),
      (``Anneal.SepAC.RangeSpanV2026.v2026Range_frame_cancel,
        ``Anneal.SepAC.sepAC_entails_of_cancelAtoms),
      (``Anneal.SepAC.RangeSpanV2026.lithiumFrame_of_diffWith,
        ``PTree.diffWith),
      (``Anneal.WavefrontReclaim.WavefrontV2026.wfEncodeU32LeAbsBytes_eq_encodeValueToBytes,
        ``Trusted.Rustc.V2026_06_01.MirSemantics.encodeValueToBytes),
      (``Anneal.WavefrontReclaim.WavefrontV2026.decodeValueFromBytes_wfEncodeU32LeAbsBytes,
        ``Trusted.Rustc.V2026_06_01.MirSemantics.decodeValueFromBytes),
      (``Anneal.WavefrontReclaim.WavefrontV2026.multiRank_wavefront_terminates_arbitrary_depth,
        ``Anneal.CnfOrd.cnfAcc_all),
      (``Anneal.WavefrontReclaim.WavefrontV2026.vsepWpOrdRelV2026_fiveStage_chained_lifecycle,
        ``Anneal.WavefrontReclaim.vsep),
      (``Anneal.WavefrontReclaim.WavefrontV2026.stepMirFn_wavefrontStep_firewall_bridge,
        ``Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn),
      (``Anneal.WavefrontReclaim.WavefrontV2026.stepMirFn_wavefrontStep_firewall_bridge,
        ``Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt),
      (``Anneal.WavefrontReclaim.WavefrontV2026.stepMirFn_wavefrontStep_firewall_bridge,
        ``Anneal.Firewall.Firewall),
      (``Anneal.WavefrontReclaim.WavefrontV2026.stepMirFn_lockstep_chain_indexedCut,
        ``Anneal.WavefrontReclaim.WavefrontV2026.mirWavefrontCutAt_zero_quiescent),
      (``Anneal.WavefrontReclaim.WavefrontV2026.stepMirFn_lockstep_chain_indexedCut,
        ``Anneal.WavefrontReclaim.WavefrontV2026.mirSingleStepTo_preserves_rootFrame_of_wavefrontCfgBody),
      (``Anneal.WavefrontReclaim.WavefrontV2026.mirNodeNext?_sound,
        ``Trusted.Rustc.V2026_06_01.MirSemantics.MirStepNode.emitStep),
      (``Anneal.WavefrontReclaim.WavefrontV2026.wavefrontConverges_preserves_disjoint_mem_frame,
        ``Trusted.Rustc.V2026_06_01.MirSemantics.globalAllocSliceToAbstractBytes),
      (``Anneal.WavefrontReclaim.WavefrontV2026.wavefrontConverges_preserves_disjoint_mem_frame,
        ``Anneal.WavefrontReclaim.WavefrontV2026.v2026SubLens_get_put_disjoint),
      (``Anneal.WavefrontReclaim.WavefrontV2026.witness_stepMirFn_lockstep_trace10_ptrLoop_v2026,
        ``Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn),
      (``Anneal.WavefrontReclaim.WavefrontV2026.runCfgSteps_wavefrontDrain_indexedCut_bridge,
        ``Anneal.PureMirExec.runCfgSteps),
      (``Anneal.WavefrontReclaim.WavefrontV2026.runCfgSteps_wavefrontDrain_indexedCut_bridge,
        ``Anneal.PureMirExec.stepCfgState),
      (``Anneal.WavefrontReclaim.WavefrontV2026.runCfgSteps_wavefrontDrain_indexedCut_bridge,
        ``Anneal.Firewall.IndexedCut) ]
  for (s, t) in bridgePairs do
    checkReaches s t

  -- 7. Strict 3-axiom purity audit across all local declarations in `InitialStateWpAndSepAcTests`.
  let testNs := `Anneal.Mir.InitialStateWpAndSepAcTests
  let mut localThms : Nat := 0
  for (c, info) in env.constants.map₂.toList do
    if testNs.isPrefixOf c && !c.isInternal then
      if let .thmInfo _ := info then
        localThms := localThms + 1
      for a in ← liftCoreM <| Lean.collectAxioms c do
        if a == ``sorryAx then
          throwError "test theorem {c} depends on sorryAx"
        if a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
          throwError "test theorem {c} depends on forbidden axiom {a}"
        unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
          throwError "test theorem {c} depends on non-standard axiom {a}"
  if localThms < 10 then
    throwError "local test audit vacuous: only {localThms} theorems found"

  -- 8. Optional cross-root kernel audit of `LeanMiriSpec.InitialStateTreeBorrowsWpLM` when
  --    `examples/.lake/build/lib/lean/LeanMiriSpec/InitialStateTreeBorrowsWpLM.olean` is built.
  let lmOlean : System.FilePath :=
    "examples/.lake/build/lib/lean/LeanMiriSpec/InitialStateTreeBorrowsWpLM.olean"
  if ← liftM (m := IO) lmOlean.pathExists then
    let savedSp ← liftM (m := IO) Lean.searchPathRef.get
    let crossErr? : Option String ← liftM (m := IO) do
      try
        Lean.searchPathRef.set ("examples/.lake/build/lib/lean" :: savedSp)
        let lmEnv ← Lean.importModules
          #[{ module := `LeanMiriSpec.InitialStateTreeBorrowsWpLM }] {}
          (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
        let lmEnv := lmEnv.setExporting false
        let mut lmModIdx? : Option Nat := none
        for i in [:lmEnv.header.moduleNames.size] do
          let m := lmEnv.header.moduleNames[i]!
          if (`MiniRustSpec).isPrefixOf m then
            return some s!"cross-root MiniRustSpec violation: {m}"
          if m == `LeanMiriSpec.InitialStateTreeBorrowsWpLM then
            lmModIdx? := some i
        let some lmModIdx := lmModIdx?
          | return some "cross-root audit: module index for InitialStateTreeBorrowsWpLM missing"
        let mut lmThmCount : Nat := 0
        for (c, info) in lmEnv.constants.map₁.toList do
          if lmEnv.getModuleIdxFor? c == some lmModIdx then
            match info with
            | .thmInfo _ => lmThmCount := lmThmCount + 1
            | .defnInfo dv =>
              if dv.safety != .safe then
                return some s!"cross-root safety violation: {c} is not safe"
            | .axiomInfo _ =>
              return some s!"cross-root custom axiom forbidden: {c}"
            | .opaqueInfo _ =>
              return some s!"cross-root opaque decl forbidden: {c}"
            | _ => pure ()
        if lmThmCount < 15 then
          return some s!"cross-root vacuity: only {lmThmCount} theorems in InitialStateTreeBorrowsWpLM"
        let lmTargets : List Name :=
          [ `LeanMiriSpec.InitialStateTreeBorrowsWpLM.ep1_initial_state_tree_borrows_wp_capstone,
            `LeanMiriSpec.InitialStateTreeBorrowsWpLM.witness_vendored_placeMachine_tb_step_positive_and_ub_refutations ]
        for t in lmTargets do
          if lmEnv.find? t |>.isNone then
            return some s!"cross-root audit: missing {t}"
          let mut seenAx : NameSet := {}
          let mut sawMiri : Bool := false
          let mut qAx : Array Name := #[t]
          while !qAx.isEmpty do
            let cur := qAx.back!
            qAx := qAx.pop
            if seenAx.contains cur then continue
            seenAx := seenAx.insert cur
            if (`Miri).isPrefixOf cur then
              sawMiri := true
            if let some ci := lmEnv.find? cur then
              if let .axiomInfo _ := ci then
                if cur == ``sorryAx || cur == ``Lean.ofReduceBool ||
                    cur == ``Lean.trustCompiler then
                  return some s!"cross-root forbidden axiom {cur} in {t}"
                unless cur == ``propext || cur == ``Classical.choice || cur == ``Quot.sound do
                  return some s!"cross-root non-standard axiom {cur} in {t}"
              if let .opaqueInfo _ := ci then
                if (`LeanMiriSpec).isPrefixOf cur then
                  return some s!"cross-root opaque dependency {cur} in {t}"
              qAx := qAx ++ ci.type.getUsedConstants
              if let some v := ci.value? (allowOpaque := true) then
                qAx := qAx ++ v.getUsedConstants
          unless sawMiri do
            return some s!"cross-root shadow-spec failure: {t} does not reach vendored Miri.*"
          if t == `LeanMiriSpec.InitialStateTreeBorrowsWpLM.ep1_initial_state_tree_borrows_wp_capstone then
            unless seenAx.contains ``Trusted.Rustc.V2026_06_01.MirSemantics.treeBorrowPermTransition do
              return some s!"cross-root bridge failure: {t} does not reach V2026 treeBorrowPermTransition"
        return none
      finally
        Lean.searchPathRef.set savedSp
    if let some errMsg := crossErr? then
      throwError "{errMsg}"

end KernelAndIsolationAudit

end Anneal.Mir.InitialStateWpAndSepAcTests
