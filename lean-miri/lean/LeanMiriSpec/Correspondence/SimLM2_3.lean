/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.EnumLM2_3

/-!
# Multi-Variant Enum Simulation (`LM-2.3`)

Kernel-checked correspondence theorems between Anneal's `MirSemantics` and
vendored `lean-miri` (`Miri.Interpreter.Discriminant`,
`Miri.Interpreter.writeAggregate`, `Miri.Interpreter.project` /
`projectDowncast` / `projectField`, `Miri.Interpreter.Step`, and
`Miri.Interpreter.ControlFlow.evalTerminator`) for multi-variant direct-tagged
enums (`Variants.Multiple` + `TagEncoding.Direct`):

1. `evalRvalue_aggregate_enum_simulation`
2. `step_setDiscriminant_simulation`
3. `step_setDiscriminant_uninit_divergence`
4. `evalRvalue_discriminant_simulation`
5. `evalProjection_downcast_field_simulation`
6. `evalProjection_downcast_field_initialized_divergence`
7. `enum_match_switchInt_simulation`
8. `step_storageLive_LM2_3_simulation`
9. `step_storageDead_LM2_3_simulation`
10. `step_enum_copy_move_simulation`
11. `step_downcast_field_write_simulation`
12. `step_downcast_field_write_inactive_divergence`
13. `step_downcast_field_write_uninit_divergence`
14. `step_enum_self_move_simulation`
15. `step_enum_self_copy_dead_or_uninit_simulation`
16. `step_enum_self_copy_overlap_divergence`
17. `step_enum_copy_move_uninitInd_divergence`
18. `step_return_enum_lm2_3_simulation`
19. `step_return_enum_uninitInd_divergence`

Every lockstep simulation theorem covers both valid `.step` / `.emitStep` /
`.retNormal` transitions and lockstep `.ub` transitions on `.dead`, `.uninit`,
and inactive-variant accesses, paired with explicit divergence theorems at the
typed-value vs. raw-byte abstraction boundaries.
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. Sub-Range Uninitialized `InitMask` Query Lemma -/

private def lm23MaxSizeBytes : Nat := 18446744073709551615
private def lm23WordMask : Nat := 18446744073709551615
private def lm23BlockSize : Nat := 64
private def lm23SizeBytes (size : Miri.ABI.Size) : Nat := size.bytes.toNat

private def lm23SizeFromNat (n : Nat) :
    Except Miri.Memory.InitMaskError Miri.ABI.Size :=
  if n ≤ lm23MaxSizeBytes then .ok (Miri.ABI.Size.ofBytes (UInt64.ofNat n))
  else .error (.sizeFromNatOverflow n)

private def lm23BitAt (word bit : Nat) : Bool := Nat.testBit word bit

private def lm23BitIndex (offset : Miri.ABI.Size) : Nat × Nat :=
  let bytes := lm23SizeBytes offset
  (bytes / lm23BlockSize, bytes % lm23BlockSize)

private def lm23GetBlock (self : Miri.Memory.InitMaskMaterialized) (block : Nat) :
    Except Miri.Memory.InitMaskError UInt64 :=
  match self.blocks[block]? with
  | some word => .ok word
  | none => .error (.blockIndexOutOfBounds block self.blocks.size)

private def lm23FirstSetBit (word startBit : Nat) : Option Nat :=
  ((List.range (64 - startBit)).find? fun offset =>
    lm23BitAt word (startBit + offset)).map (· + startBit)

private def lm23SearchBlock (word : UInt64) (block startBit : Nat)
    (isInit : Bool) :
    Except Miri.Memory.InitMaskError (Option Miri.ABI.Size) := do
  let bits := if isInit then word.toNat else lm23WordMask - word.toNat
  match lm23FirstSetBit bits startBit with
  | none => return none
  | some bit => return some (← lm23SizeFromNat (block * lm23BlockSize + bit))

private def lm23FindBitFast (self : Miri.Memory.InitMaskMaterialized)
    (start finish : Miri.ABI.Size) (isInit : Bool) :
    Except Miri.Memory.InitMaskError (Option Miri.ABI.Size) := do
  let startBytes := lm23SizeBytes start
  let finishBytes := lm23SizeBytes finish
  if startBytes >= finishBytes then return none
  let (startBlock, startBit) := lm23BitIndex start
  let endInclusive ← lm23SizeFromNat (finishBytes - 1)
  let (endBlockInclusive, _) := lm23BitIndex endInclusive
  let first ← lm23SearchBlock (← lm23GetBlock self startBlock) startBlock startBit isInit
  match first with
  | some index =>
    if lm23SizeBytes index < finishBytes then return some index else return none
  | none =>
    if startBlock < endBlockInclusive then
      for block in [startBlock + 1:endBlockInclusive + 1] do
        match ← lm23SearchBlock (← lm23GetBlock self block) block 0 isInit with
        | some index =>
          if lm23SizeBytes index < finishBytes then return some index else return none
        | none => pure ()
    return none

private def lm23IsRangeInitialized (self : Miri.Memory.InitMask)
    (range : Miri.Memory.AllocRange) :
    Except Miri.Memory.InitMaskError (Except Miri.Memory.AllocRange Unit) := do
  let finish ← range.endExclusive
  if finish.bytes > self.len.bytes then
    return .error (← Miri.Memory.AllocRange.fromEndpoints self.len finish)
  match self.blocks with
  | .Lazy state =>
    if state then return .ok () else return .error range
  | .Materialized blocks =>
    match ← lm23FindBitFast blocks range.start finish false with
    | none => return .ok ()
    | some uninitStart =>
      let uninitEnd := (← lm23FindBitFast blocks uninitStart finish true).getD finish
      return .error (← Miri.Memory.AllocRange.fromEndpoints uninitStart uninitEnd)

private theorem lm23_isRangeInitialized_eq (self : Miri.Memory.InitMask)
    (range : Miri.Memory.AllocRange) :
    self.isRangeInitialized range = lm23IsRangeInitialized self range := rfl

private theorem lm23_list_range'_find?_some_le {f : Nat → Bool} :
    ∀ k s {p : Nat}, s ≤ p → p < s + k → f p = true →
      ∃ m, (List.range' s k).find? f = some m ∧ s ≤ m ∧ m ≤ p
  | 0, _, _, h1, h2, _ => by omega
  | k + 1, s, p, h1, h2, hfp => by
    rw [List.range'_succ, List.find?_cons]
    cases hfs : f s
    · have hne : p ≠ s := by
        intro heq; subst heq; rw [hfs] at hfp; cases hfp
      obtain ⟨m, hm, hm1, hm2⟩ :=
        lm23_list_range'_find?_some_le k (s + 1) (by omega) (by omega) hfp
      exact ⟨m, hm, by omega, hm2⟩
    · exact ⟨s, rfl, Nat.le_refl s, h1⟩

private theorem lm23_testBit_wordMask_sub (word : UInt64) {b : Nat} (hb : b < 64) :
    Nat.testBit (lm23WordMask - word.toNat) b = !Nat.testBit word.toNat b := by
  have hcomp : lm23WordMask - word.toNat = (~~~word.toBitVec).toNat := by
    rw [BitVec.toNat_not]
    simp [lm23WordMask]
  have h1 : (~~~word.toBitVec).toNat.testBit b = (~~~word.toBitVec).getLsbD b := rfl
  have h2 : word.toNat.testBit b = word.toBitVec.getLsbD b := rfl
  rw [hcomp, h1, h2, BitVec.getLsbD_not]
  simp [hb]

private theorem lm23SearchBlock_ok (word : UInt64)
    {block startBit : Nat} (isInit : Bool)
    (hblk : block * 64 + 64 ≤ 2 ^ 64) :
    ∃ opt : Option Miri.ABI.Size,
      lm23SearchBlock word block startBit isInit = .ok opt ∧
      ∀ idx, opt = some idx →
        block * 64 + startBit ≤ idx.bytes.toNat ∧
        idx.bytes.toNat < (block + 1) * 64 := by
  let bits := if isInit then word.toNat else lm23WordMask - word.toNat
  unfold lm23SearchBlock lm23FirstSetBit
  cases hopt : (List.range (64 - startBit)).find?
      (fun offset => lm23BitAt bits (startBit + offset)) with
  | none =>
    refine ⟨none, ?_, fun _ h => (by cases h)⟩
    simp [bits, hopt, pure, Except.pure]
  | some offset =>
    have hmem : offset ∈ List.range (64 - startBit) := List.mem_of_find?_eq_some hopt
    have hoff_lt64 : offset + startBit < 64 := by
      have := List.mem_range.mp hmem
      omega
    have hoff_le_max : block * lm23BlockSize + (offset + startBit) ≤ lm23MaxSizeBytes := by
      unfold lm23BlockSize lm23MaxSizeBytes; omega
    have hoff_u64 :
        (UInt64.ofNat (block * lm23BlockSize + (offset + startBit))).toNat =
          block * lm23BlockSize + (offset + startBit) := by
      rw [UInt64.toNat_ofNat']
      unfold lm23BlockSize at *
      exact Nat.mod_eq_of_lt (by omega)
    refine ⟨some (Miri.ABI.Size.ofBytes
        (UInt64.ofNat (block * lm23BlockSize + (offset + startBit)))), ?_, ?_⟩
    · simp [bits, hopt, Option.map, lm23SizeFromNat, hoff_le_max,
        bind, Except.bind, pure, Except.pure]
    · intro idx hidx
      injection hidx with hidx_eq
      subst hidx_eq
      simp only [Miri.ABI.Size.ofBytes, hoff_u64]
      unfold lm23BlockSize
      omega

private theorem lm23SearchBlock_false_exists (word : UInt64)
    {block startBit finishBytes : Nat}
    (hblk : block * 64 + 64 ≤ 2 ^ 64)
    {bit : Nat} (hlo : startBit ≤ bit) (hhi : bit < 64)
    (hfin : block * 64 + bit < finishBytes)
    (hfalse : Nat.testBit word.toNat bit = false) :
    ∃ idx : Miri.ABI.Size,
      lm23SearchBlock word block startBit false = .ok (some idx) ∧
      block * 64 + startBit ≤ idx.bytes.toNat ∧
      idx.bytes.toNat < finishBytes := by
  have hfp : lm23BitAt (lm23WordMask - word.toNat) (startBit + (bit - startBit)) = true := by
    unfold lm23BitAt
    rw [Nat.add_sub_of_le hlo, lm23_testBit_wordMask_sub word hhi, hfalse]
    rfl
  obtain ⟨m, hm, _, hm_le⟩ :=
    lm23_list_range'_find?_some_le (64 - startBit) 0
      (f := fun offset => lm23BitAt (lm23WordMask - word.toNat) (startBit + offset))
      (p := bit - startBit) (by omega) (by omega) hfp
  have hfirst : lm23FirstSetBit (lm23WordMask - word.toNat) startBit = some (m + startBit) := by
    unfold lm23FirstSetBit
    rw [List.range_eq_range', hm]
    rfl
  have hm_lt64 : m + startBit < 64 := by omega
  have hm_le_max : block * lm23BlockSize + (m + startBit) ≤ lm23MaxSizeBytes := by
    unfold lm23BlockSize lm23MaxSizeBytes; omega
  have hm_u64 :
      (UInt64.ofNat (block * lm23BlockSize + (m + startBit))).toNat =
        block * lm23BlockSize + (m + startBit) := by
    rw [UInt64.toNat_ofNat']
    unfold lm23BlockSize at *
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨Miri.ABI.Size.ofBytes (UInt64.ofNat (block * lm23BlockSize + (m + startBit))),
    ?_, ?_, ?_⟩
  · unfold lm23SearchBlock
    simp only [Bool.false_eq_true, ↓reduceIte, hfirst, lm23SizeFromNat, hm_le_max,
      bind, Except.bind, pure, Except.pure]
  · simp only [Miri.ABI.Size.ofBytes, hm_u64]; unfold lm23BlockSize; omega
  · simp only [Miri.ABI.Size.ofBytes, hm_u64]; unfold lm23BlockSize; omega

private def lm23FindBitStep (self : Miri.Memory.InitMaskMaterialized)
    (finishBytes : Nat) (isInit : Bool) (block : Nat)
    (_ : Option (Option Miri.ABI.Size) × PUnit) :
    Except Miri.Memory.InitMaskError
      (ForInStep (Option (Option Miri.ABI.Size) × PUnit)) := do
  match ← lm23SearchBlock (← lm23GetBlock self block) block 0 isInit with
  | some index =>
    if lm23SizeBytes index < finishBytes then
      return ForInStep.done (some (some index), ())
    else
      return ForInStep.done (some none, ())
  | none =>
    return ForInStep.yield (none, ())

private theorem lm23FindBitStep_loop_ok
    (words : Array UInt64) {finishBytes : Nat} (isInit : Bool)
    (hfin_blk : ((finishBytes - 1) / 64) * 64 + 64 ≤ 2 ^ 64)
    (hbp_sz : (finishBytes - 1) / 64 < words.size) :
    ∀ m k, k + m ≤ (finishBytes - 1) / 64 + 1 →
      ∃ res : Option (Option Miri.ABI.Size),
        forIn (List.range' k m) (none, ()) (lm23FindBitStep ⟨words⟩ finishBytes isInit) =
          .ok (res, ()) ∧
        ∀ opt idx, res = some opt → opt = some idx →
          k * 64 ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finishBytes := by
  intro m
  induction m with
  | zero =>
    intro k _
    exact ⟨none, rfl, fun _ _ h => (by cases h)⟩
  | succ m ih =>
    intro k hkm
    rw [List.range'_succ, List.forIn_cons]
    have hk_sz : k < words.size := by omega
    have hk_blk : k * 64 + 64 ≤ 2 ^ 64 := by omega
    have hget_k : lm23GetBlock ⟨words⟩ k = .ok (words[k]'hk_sz) := by
      simp [lm23GetBlock, hk_sz]
    obtain ⟨optK, hsearchK, hboundsK⟩ := lm23SearchBlock_ok (words[k]'hk_sz) isInit hk_blk (startBit := 0)
    cases optK with
    | none =>
      have hstep_k :
          lm23FindBitStep ⟨words⟩ finishBytes isInit k (none, ()) = .ok (.yield (none, ())) := by
        unfold lm23FindBitStep
        simp [hget_k, hsearchK, bind, Except.bind, pure, Except.pure]
      rw [hstep_k]
      obtain ⟨res, hfor, hres⟩ := ih (k + 1) (by omega)
      refine ⟨res, hfor, fun opt idx h1 h2 => ?_⟩
      obtain ⟨hlo, hhi⟩ := hres opt idx h1 h2
      exact ⟨by omega, hhi⟩
    | some idxK =>
      obtain ⟨hloK, _⟩ := hboundsK idxK rfl
      by_cases hlt_fin : lm23SizeBytes idxK < finishBytes
      · have hstep_k :
            lm23FindBitStep ⟨words⟩ finishBytes isInit k (none, ()) =
              .ok (.done (some (some idxK), ())) := by
          unfold lm23FindBitStep
          simp [hget_k, hsearchK, hlt_fin, bind, Except.bind, pure, Except.pure]
        rw [hstep_k]
        refine ⟨some (some idxK), rfl, fun opt idx h1 h2 => ?_⟩
        injection h1 with h1'; subst h1'
        injection h2 with h2'; subst h2'
        unfold lm23SizeBytes at hlt_fin
        exact ⟨by omega, hlt_fin⟩
      · have hstep_k :
            lm23FindBitStep ⟨words⟩ finishBytes isInit k (none, ()) =
              .ok (.done (some none, ())) := by
          unfold lm23FindBitStep
          simp [hget_k, hsearchK, hlt_fin, bind, Except.bind, pure, Except.pure]
        rw [hstep_k]
        refine ⟨some none, rfl, fun opt idx h1 h2 => ?_⟩
        injection h1 with h1'; subst h1'; cases h2

private theorem lm23FindBitFast_ok (words : Array UInt64)
    {start finish : Miri.ABI.Size} (isInit : Bool)
    (hfin_blk : ((finish.bytes.toNat - 1) / 64) * 64 + 64 ≤ 2 ^ 64)
    (hsz : (finish.bytes.toNat - 1) / 64 < words.size) :
    ∃ opt : Option Miri.ABI.Size,
      lm23FindBitFast ⟨words⟩ start finish isInit = .ok opt ∧
      ∀ idx, opt = some idx →
        start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat := by
  by_cases hge : lm23SizeBytes start ≥ lm23SizeBytes finish
  · unfold lm23FindBitFast
    simp only [hge, ↓reduceIte, pure, Except.pure]
    exact ⟨none, rfl, fun _ h => (by cases h)⟩
  · have hlt : start.bytes.toNat < finish.bytes.toNat := by
      unfold lm23SizeBytes at hge; omega
    have hsub1_le : finish.bytes.toNat - 1 ≤ lm23MaxSizeBytes := by
      unfold lm23MaxSizeBytes; omega
    have hsub1_u64 : (UInt64.ofNat (finish.bytes.toNat - 1)).toNat = finish.bytes.toNat - 1 := by
      rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
    let startBlock := start.bytes.toNat / 64
    let startBit := start.bytes.toNat % 64
    let endBlock := (finish.bytes.toNat - 1) / 64
    have hstart_sz : startBlock < words.size := by omega
    have hstart_blk : startBlock * 64 + 64 ≤ 2 ^ 64 := by omega
    have hget_start : lm23GetBlock ⟨words⟩ startBlock = .ok (words[startBlock]'hstart_sz) := by
      simp [lm23GetBlock, hstart_sz]
    have hbit_start : lm23BitIndex start = (startBlock, startBit) := rfl
    have hsz_end : lm23SizeFromNat (lm23SizeBytes finish - 1) =
        .ok (Miri.ABI.Size.ofBytes (UInt64.ofNat (finish.bytes.toNat - 1))) := by
      simp [lm23SizeFromNat, lm23SizeBytes, hsub1_le]
    have hbit_end :
        (lm23BitIndex (Miri.ABI.Size.ofBytes (UInt64.ofNat (finish.bytes.toNat - 1)))).1 = endBlock := by
      simp [lm23BitIndex, lm23SizeBytes, lm23BlockSize, Miri.ABI.Size.ofBytes, hsub1_u64, endBlock]
    obtain ⟨first, hsearch_ok, hbounds0⟩ :=
      lm23SearchBlock_ok (words[startBlock]'hstart_sz) isInit hstart_blk (startBit := startBit)
    unfold lm23FindBitFast
    simp only [hge, ↓reduceIte, hbit_start, hsz_end, bind, Except.bind,
      hbit_end, hget_start, hsearch_ok]
    cases first with
    | some idx0 =>
      obtain ⟨hlo0, _⟩ := hbounds0 idx0 rfl
      have hlo0' : start.bytes.toNat ≤ idx0.bytes.toNat := by omega
      by_cases hlt0 : lm23SizeBytes idx0 < lm23SizeBytes finish
      · simp only [hlt0, ↓reduceIte, pure, Except.pure]
        refine ⟨some idx0, rfl, fun idx h => ?_⟩
        injection h with h'; subst h'
        unfold lm23SizeBytes at hlt0
        exact ⟨hlo0', hlt0⟩
      · simp only [hlt0, ↓reduceIte, pure, Except.pure]
        exact ⟨none, rfl, fun _ h => (by cases h)⟩
    | none =>
      by_cases hlt_blk : startBlock < endBlock
      · obtain ⟨res, hloop, hres⟩ :=
          lm23FindBitStep_loop_ok words (finishBytes := lm23SizeBytes finish) isInit
            (by unfold lm23SizeBytes; exact hfin_blk)
            (by unfold lm23SizeBytes; exact hsz)
            (endBlock + 1 - (startBlock + 1)) (startBlock + 1)
            (by unfold lm23SizeBytes; omega)
        simp only [hlt_blk, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range',
          Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
        unfold lm23FindBitStep at hloop
        dsimp only [bind, Except.bind] at hloop
        rw [hloop]
        cases res with
        | none =>
          exact ⟨none, rfl, fun _ h => (by cases h)⟩
        | some opt =>
          refine ⟨opt, rfl, fun idx h => ?_⟩
          obtain ⟨hloL, hhiL⟩ := hres opt idx rfl h
          unfold lm23SizeBytes at hhiL
          exact ⟨by omega, hhiL⟩
      · simp only [hlt_blk, ↓reduceIte, pure, Except.pure]
        exact ⟨none, rfl, fun _ h => (by cases h)⟩

private theorem lm23FindBitStep_loop_exists_false
    (words : Array UInt64) {finishBytes blockP : Nat}
    (hfin_blk : ((finishBytes - 1) / 64) * 64 + 64 ≤ 2 ^ 64)
    (hbp_le : blockP ≤ (finishBytes - 1) / 64)
    (hbp_sz : (finishBytes - 1) / 64 < words.size)
    {idxP : Miri.ABI.Size}
    (hsearchP : lm23SearchBlock (words[blockP]'(by omega)) blockP 0 false = .ok (some idxP))
    (hidxP_lo : blockP * 64 ≤ idxP.bytes.toNat)
    (hidxP_lt : lm23SizeBytes idxP < finishBytes) :
    ∀ m k, k ≤ blockP → blockP < k + m →
      ∃ idx : Miri.ABI.Size,
        forIn (List.range' k m) (none, ()) (lm23FindBitStep ⟨words⟩ finishBytes false) =
          .ok (some (some idx), ()) ∧
        k * 64 ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finishBytes := by
  intro m
  induction m with
  | zero => intro _ _ _; omega
  | succ m ih =>
    intro k hk_le hbp_lt
    rw [List.range'_succ, List.forIn_cons]
    have hk_sz : k < words.size := by omega
    have hget_k : lm23GetBlock ⟨words⟩ k = .ok (words[k]'hk_sz) := by
      simp [lm23GetBlock, hk_sz]
    by_cases hkeq : k = blockP
    · subst hkeq
      refine ⟨idxP, ?_, hidxP_lo, hidxP_lt⟩
      unfold lm23FindBitStep
      simp [hget_k, hsearchP, hidxP_lt, bind, Except.bind, pure, Except.pure]
    · have hk_lt_bp : k < blockP := by omega
      have hk_blk : k * 64 + 64 ≤ 2 ^ 64 := by omega
      have hk_succ_le : (k + 1) * 64 ≤ finishBytes := by omega
      obtain ⟨optK, hsearchK, hboundsK⟩ :=
        lm23SearchBlock_ok (words[k]'hk_sz) false hk_blk (startBit := 0)
      cases optK with
      | none =>
        have hstep_k :
            lm23FindBitStep ⟨words⟩ finishBytes false k (none, ()) = .ok (.yield (none, ())) := by
          unfold lm23FindBitStep
          simp [hget_k, hsearchK, bind, Except.bind, pure, Except.pure]
        rw [hstep_k]
        obtain ⟨idx, hfor, hlo, hhi⟩ := ih (k + 1) (by omega) (by omega)
        exact ⟨idx, hfor, by omega, hhi⟩
      | some idxK =>
        obtain ⟨hloK, hhiK⟩ := hboundsK idxK rfl
        have hltK_fin : lm23SizeBytes idxK < finishBytes := by
          unfold lm23SizeBytes; omega
        refine ⟨idxK, ?_, by omega, hltK_fin⟩
        unfold lm23FindBitStep
        simp [hget_k, hsearchK, hltK_fin, bind, Except.bind, pure, Except.pure]

/-- Sub-range uninitialized query: if byte `p ∈ [start, start + sz)` is
uninitialized (`mask.get p = .ok false`) in an `InitMaskWordRel` mask of length
`len < 2 ^ 32`, then `mask.isRangeInitialized (allocRange start sz)` succeeds
with `.ok (.error badRange)`. -/
theorem initMaskWordRel_isRangeInitialized_error_of_get_false
    {mask : Miri.Memory.InitMask} {len start sz : Miri.ABI.Size}
    {words : Array UInt64} {p : Nat}
    (hrel : InitMaskWordRel mask len words)
    (hlen_lt : len.bytes.toNat < 2 ^ 32)
    (hbound : start.bytes.toNat + sz.bytes.toNat ≤ len.bytes.toNat)
    (hp_lo : start.bytes.toNat ≤ p)
    (hp_hi : p < start.bytes.toNat + sz.bytes.toNat)
    (hget : mask.get (Miri.ABI.Size.ofBytes (UInt64.ofNat p)) = .ok false) :
    ∃ badRange,
      mask.isRangeInitialized (Miri.Memory.allocRange start sz) =
        .ok (.error badRange) := by
  have hp_len : p < len.bytes.toNat := by omega
  have hget_word := initMaskWordRel_get hrel hp_len
  rw [hget] at hget_word
  injection hget_word with hbit_p
  obtain ⟨hlen, hsize, hblocks⟩ := hrel
  have hfits : start.bytes.toNat + sz.bytes.toNat < 2 ^ 64 := by omega
  let finish := Miri.ABI.Size.ofBytes (start.bytes + sz.bytes)
  have hfinish_nat : finish.bytes.toNat = start.bytes.toNat + sz.bytes.toNat := by
    simp [finish, Miri.ABI.Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt hfits]
  have hend : (Miri.Memory.allocRange start sz).endExclusive = .ok finish := by
    unfold Miri.Memory.AllocRange.endExclusive Miri.Memory.AllocRange.end Miri.Memory.allocRange
    have hno_wrap : ¬ start.bytes + sz.bytes < start.bytes := by
      simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, Nat.mod_eq_of_lt hfits]
      omega
    simp [Miri.ABI.Size.add, hno_wrap, Except.mapError, finish]
  have hnot_gt : ¬ finish.bytes > mask.len.bytes := by
    rw [hlen]
    simp only [GT.gt, UInt64.lt_iff_toNat_lt]
    omega
  rw [lm23_isRangeInitialized_eq]
  unfold lm23IsRangeInitialized
  simp only [hend, bind, Except.bind, hnot_gt, ↓reduceIte]
  rcases hblocks with ⟨hb, _⟩ | ⟨_, rfl⟩ | hb
  · rw [hb]
    exact ⟨Miri.Memory.allocRange start sz, rfl⟩
  · rw [maskBlocksGetBit_initWordsTrue hp_len] at hbit_p
    cases hbit_p
  · rw [hb]
    dsimp only
    have hfin_blk : ((finish.bytes.toNat - 1) / 64) * 64 + 64 ≤ 2 ^ 64 := by omega
    have hfin_sz : (finish.bytes.toNat - 1) / 64 < words.size := by
      rw [hsize]; omega
    have hbp_sz : p / 64 < words.size := by rw [hsize]; omega
    have hbit_false : Nat.testBit (words[p / 64]'hbp_sz).toNat (p % 64) = false := by
      unfold maskBlocksGetBit at hbit_p
      rw [Array.getElem?_eq_getElem hbp_sz] at hbit_p
      exact hbit_p.symm
    have hfind_uninit :
        ∃ uninitStart : Miri.ABI.Size,
          lm23FindBitFast ⟨words⟩ start finish false = .ok (some uninitStart) ∧
          start.bytes.toNat ≤ uninitStart.bytes.toNat ∧
          uninitStart.bytes.toNat < finish.bytes.toNat := by
      have hnot_ge : ¬ lm23SizeBytes start ≥ lm23SizeBytes finish := by
        unfold lm23SizeBytes; omega
      have hsub1_le : finish.bytes.toNat - 1 ≤ lm23MaxSizeBytes := by
        unfold lm23MaxSizeBytes; omega
      have hsub1_u64 : (UInt64.ofNat (finish.bytes.toNat - 1)).toNat = finish.bytes.toNat - 1 := by
        rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
      let startBlock := start.bytes.toNat / 64
      let startBit := start.bytes.toNat % 64
      let endBlock := (finish.bytes.toNat - 1) / 64
      have hstart_sz : startBlock < words.size := by omega
      have hstart_blk : startBlock * 64 + 64 ≤ 2 ^ 64 := by omega
      have hget_start : lm23GetBlock ⟨words⟩ startBlock = .ok (words[startBlock]'hstart_sz) := by
        simp [lm23GetBlock, hstart_sz]
      have hbit_start : lm23BitIndex start = (startBlock, startBit) := rfl
      have hsz_end : lm23SizeFromNat (lm23SizeBytes finish - 1) =
          .ok (Miri.ABI.Size.ofBytes (UInt64.ofNat (finish.bytes.toNat - 1))) := by
        simp [lm23SizeFromNat, lm23SizeBytes, hsub1_le]
      have hbit_end :
          (lm23BitIndex (Miri.ABI.Size.ofBytes (UInt64.ofNat (finish.bytes.toNat - 1)))).1 = endBlock := by
        simp [lm23BitIndex, lm23SizeBytes, lm23BlockSize, Miri.ABI.Size.ofBytes, hsub1_u64, endBlock]
      by_cases hsame_blk : p / 64 = startBlock
      · have hlo_bit : startBit ≤ p % 64 := by omega
        have hfalse_start : Nat.testBit (words[startBlock]'hstart_sz).toNat (p % 64) = false := by
          simpa [hsame_blk] using hbit_false
        obtain ⟨idx0, hsearch0, hlo0, hhi0⟩ :=
          lm23SearchBlock_false_exists (words[startBlock]'hstart_sz) hstart_blk
            hlo_bit (Nat.mod_lt p (by decide))
            (finishBytes := lm23SizeBytes finish)
            (by unfold lm23SizeBytes; omega) hfalse_start
        refine ⟨idx0, ?_, by omega, by unfold lm23SizeBytes at hhi0; exact hhi0⟩
        unfold lm23FindBitFast
        simp only [hnot_ge, ↓reduceIte, hbit_start, hsz_end, bind, Except.bind,
          hget_start, hsearch0, pure, Except.pure]
        have hlt_fin : lm23SizeBytes idx0 < lm23SizeBytes finish := hhi0
        simp [hlt_fin]
      · have hbp_gt : startBlock < p / 64 := by omega
        have hlt_blk : startBlock < endBlock := by omega
        obtain ⟨first, hsearch0, hbounds0⟩ :=
          lm23SearchBlock_ok (words[startBlock]'hstart_sz) false hstart_blk (startBit := startBit)
        cases first with
        | some idx0 =>
          obtain ⟨hlo0, hhi0⟩ := hbounds0 idx0 rfl
          have hlt0 : lm23SizeBytes idx0 < lm23SizeBytes finish := by
            unfold lm23SizeBytes; omega
          refine ⟨idx0, ?_, by omega, by unfold lm23SizeBytes at hlt0; exact hlt0⟩
          unfold lm23FindBitFast
          simp [hnot_ge, hbit_start, hsz_end, bind, Except.bind,
            hget_start, hsearch0, hlt0, pure, Except.pure]
        | none =>
          obtain ⟨idxP, hsearchP, hloP, hhiP⟩ :=
            lm23SearchBlock_false_exists (words[p / 64]'hbp_sz) (block := p / 64) (by omega)
              (startBit := 0) (Nat.zero_le _) (Nat.mod_lt p (by decide))
              (finishBytes := lm23SizeBytes finish)
              (by unfold lm23SizeBytes; omega) hbit_false
          obtain ⟨idxL, hloop, hloL, hhiL⟩ :=
            lm23FindBitStep_loop_exists_false words (finishBytes := lm23SizeBytes finish)
              (blockP := p / 64)
              (by unfold lm23SizeBytes; exact hfin_blk)
              (by unfold lm23SizeBytes; omega)
              (by unfold lm23SizeBytes; exact hfin_sz)
              hsearchP (by omega) hhiP
              (endBlock + 1 - (startBlock + 1)) (startBlock + 1)
              (by omega) (by omega)
          refine ⟨idxL, ?_, by omega, by unfold lm23SizeBytes at hhiL; exact hhiL⟩
          unfold lm23FindBitFast
          simp only [hnot_ge, ↓reduceIte, hbit_start, hsz_end, bind, Except.bind,
            hbit_end, hget_start, hsearch0, hlt_blk,
            Std.Legacy.Range.forIn_eq_forIn_range',
            Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
          unfold lm23FindBitStep at hloop
          dsimp only [bind, Except.bind] at hloop
          rw [hloop]
          rfl
    obtain ⟨uninitStart, hfind_f, _, hus_lt⟩ := hfind_uninit
    obtain ⟨optEnd, hfind_t, hbounds_t⟩ :=
      lm23FindBitFast_ok words (start := uninitStart) (finish := finish) true hfin_blk hfin_sz
    have hend_ge : uninitStart.bytes.toNat ≤ (optEnd.getD finish).bytes.toNat := by
      cases optEnd with
      | none => dsimp; omega
      | some e => dsimp; exact (hbounds_t e rfl).1
    have hfrom : ∃ rng, Miri.Memory.AllocRange.fromEndpoints uninitStart (optEnd.getD finish) = .ok rng := by
      unfold Miri.Memory.AllocRange.fromEndpoints Miri.ABI.Size.sub
      have hnot_lt : ¬ (optEnd.getD finish).bytes < uninitStart.bytes := by
        simp only [UInt64.lt_iff_toNat_lt]; omega
      simp [hnot_lt, Except.mapError, bind, Except.bind, pure, Except.pure]
    obtain ⟨rng, hrng⟩ := hfrom
    refine ⟨rng, ?_⟩
    simp only [Miri.Memory.allocRange, hfind_f, hfind_t, hrng, pure, Except.pure]

/-! ## 2. `Discriminant` Pipeline Lemmas (`Miri.Interpreter.Discriminant`) -/

theorem validScalarBytes_of_tagBytes {tagBytes : Nat}
    (htb : tagBytes = 1 ∨ tagBytes = 2 ∨ tagBytes = 4 ∨ tagBytes = 8) :
    ValidScalarBytes tagBytes := by
  rcases htb with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))

theorem abiIntegerByteWidth_translate {tagBytes : Nat}
    (htb : tagBytes = 1 ∨ tagBytes = 2 ∨ tagBytes = 4 ∨ tagBytes = 8) :
    abiIntegerByteWidth (translateAbiIntegerBytes tagBytes) = tagBytes := by
  rcases htb with rfl | rfl | rfl | rfl <;> rfl

theorem translateSizeBytes_toNat_eq {sz : Nat} (hsz : ValidScalarBytes sz) :
    (translateSizeBytes sz).bytes.toNat = sz := by
  rcases hsz with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem translateSizeBytes_ne_zero {sz : Nat} (hsz : ValidScalarBytes sz) :
    translateSizeBytes sz ≠ Miri.ABI.Size.ZERO := by
  rcases hsz with rfl | rfl | rfl | rfl | rfl <;> decide

theorem scalarFromUInt_of_lt {sz v : Nat} (hsz : ValidScalarBytes sz)
    (hv : v < 2 ^ (8 * sz)) :
    ∃ msc : Miri.Memory.ScalarInt,
      ScalarRel ⟨v, sz⟩ msc ∧
      Miri.Memory.Scalar.fromUInt (Prov := AnnealProv)
        (BitVec.ofNat 128 v) (translateSizeBytes sz) =
        .ok (.fromScalarInt msc) := by
  have hcan : v < scalarModulus sz := by
    rw [scalarModulus_eq_two_pow]; exact hv
  obtain ⟨msc, htry, hrel⟩ :=
    tryFromUInt_of_valid_canonical (sc := ⟨v, sz⟩) hsz hcan
  refine ⟨msc, hrel, ?_⟩
  unfold Miri.Memory.Scalar.fromUInt
  simp [htry, bind, Except.bind, pure, Except.pure, Except.mapError]

theorem tagLayoutOfAbiScalar_enum {tagBytes : Nat}
    (htb : tagBytes = 1 ∨ tagBytes = 2 ∨ tagBytes = 4 ∨ tagBytes = 8)
    (vr : Miri.ABI.WrappingRange) :
    ∃ tagLay : Miri.Interpreter.LocalLayout,
      tagLayoutOfAbiScalar
        (.Initialized
          (value := .Int (translateAbiIntegerBytes tagBytes) false)
          (validRange := vr)) = some tagLay ∧
      tagLay.layout.size = translateSizeBytes tagBytes ∧
      tagLay.layout.size ≠ Miri.ABI.Size.ZERO ∧
      tagLay.layout.fields = .Primitive ∧
      tagLay.layout.backendRepr =
        .Scalar (.Initialized
          (value := .Int (translateAbiIntegerBytes tagBytes) false)
          (validRange := vr)) ∧
      tagLay.layout.backendRepr.isSigned = .ok false ∧
      tagLay.layout.isSized = true ∧
      ((Miri.ABI.Scalar.Initialized
          (value := .Int (translateAbiIntegerBytes tagBytes) false)
          (validRange := vr)).size annealRuntimeDataLayout =
        .ok (translateSizeBytes tagBytes)) := by
  rcases htb with rfl | rfl | rfl | rfl <;>
    refine ⟨_, rfl, rfl, (fun h => by cases h), rfl, rfl, rfl, rfl, rfl⟩

theorem ValidEnumLayout.isVariantUninhabited_false
    {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)}
    (hvalid : ValidEnumLayout ty layouts tagBytes variants)
    {v : Nat} (hv : v < variants.length) :
    (translateTy ty layouts).layout.isVariantUninhabited v = false := by
  obtain ⟨_, _, _, _, _, _, _, _, _, vars, hsz, hvars, hvf⟩ := hvalid.table_entry
  have hv_sz : v < vars.size := by omega
  have hinh := (hvf v hv).vl_inhabited
  unfold Miri.ABI.LayoutData.isVariantUninhabited
  rw [hvars]
  dsimp only
  rw [Array.getElem?_eq_getElem hv_sz]
  simp [hinh]

theorem ValidEnumLayout.isUnresolvedLayoutIdx_false
    {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)}
    (hvalid : ValidEnumLayout ty layouts tagBytes variants) :
    isUnresolvedLayoutIdx layouts ty.layoutIdx = false := by
  obtain ⟨tl, _, _, _, hlook, _⟩ := hvalid.table_entry
  have hpos := hvalid.layoutIdx_pos
  have hbeq : Nat.beq ty.layoutIdx 0 = false := by
    cases h : ty.layoutIdx with
    | zero => exact False.elim (Nat.ne_of_gt hpos h)
    | succ _ => rfl
  unfold isUnresolvedLayoutIdx
  rw [hbeq]
  change (match layouts.lookup ty.layoutIdx with | .some _ => false | .none => true) = false
  rw [hlook]

theorem ValidEnumLayout.resolveTyWithLocalDecls_eq
    {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)}
    (hvalid : ValidEnumLayout ty layouts tagBytes variants)
    (localDecls : List LocalDecl) :
    resolveTyWithLocalDecls localDecls layouts ty = ty := by
  unfold resolveTyWithLocalDecls
  rw [hvalid.isUnresolvedLayoutIdx_false]

theorem ValidEnumLayout.isUnionLayout_false
    {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)}
    (hvalid : ValidEnumLayout ty layouts tagBytes variants) :
    isUnionLayout layouts ty = false := by
  obtain ⟨defPath, adtArgs, hk⟩ := hvalid.is_adt
  obtain ⟨tl, _, _, _, hlook, _⟩ := hvalid.table_entry
  have hof := hvalid.outer_fields_tag0
  unfold translateTy at hof
  rw [hk] at hof
  dsimp only at hof
  rw [hlook] at hof
  dsimp only [translateTypeLayout] at hof
  unfold isUnionLayout
  rw [hk]
  change (match layouts.lookup ty.layoutIdx with
    | .some { fields := .union _, .. } => true
    | _ => false) = false
  rw [hlook]
  rcases tl with ⟨_, _, _, fields_s, _, _, _⟩
  dsimp only at hof ⊢
  cases fields_s with
  | union _ => cases hof
  | primitive | array _ _ | arbitrary _ _ => rfl

theorem ValidEnumLayout.placeTouchesUnion_downcast_field
    {decl : LocalDecl} {localDecls : List LocalDecl} {layouts : LayoutTable}
    {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    (hvalid : ValidEnumLayout decl.ty layouts tagBytes variants)
    {idx : Local} (hdecl : get? localDecls idx = some decl)
    (vName : Option String) (variantIdx fieldIdx : Nat) (fieldTy : Ty) :
    placeTouchesUnion localDecls layouts
      { local_ := idx, projection := [.downcast vName variantIdx, .field fieldIdx fieldTy] } =
      false := by
  unfold placeTouchesUnion
  dsimp only
  cases localDecls with
  | nil => rfl
  | cons _ _ =>
    cases layouts.entries with
    | nil => rfl
    | cons _ _ =>
      rw [hdecl]
      dsimp only [tyProjTouchesUnion]
      rw [hvalid.resolveTyWithLocalDecls_eq, hvalid.isUnionLayout_false]

theorem ValidEnumLayout.evalPlaceDiscriminant_eq
    {srcDecl : LocalDecl} {localDecls : List LocalDecl} {layouts : LayoutTable}
    {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    (hvalid : ValidEnumLayout srcDecl.ty layouts tagBytes variants)
    {srcIdx : Local} (hdecl : get? localDecls srcIdx = some srcDecl)
    {v_act : Nat} (hv : v_act < variants.length)
    (fieldVals : List Value) (locals : List LocalSlot) (mem : Memory) :
    evalPlaceDiscriminant (.aggregate v_act fieldVals) locals mem ⟨srcIdx, .nil⟩
      localDecls layouts = .ok (.scalar ⟨v_act, 8⟩) locals mem := by
  obtain ⟨defPath, adtArgs, hk⟩ := hvalid.is_adt
  have hnot_ord := hvalid.not_ordering defPath adtArgs hk
  obtain ⟨tl, _, rawTag, rawShapes, hlook, htl_vars, hlen_eq, _⟩ := hvalid.table_entry
  have hu := hvalid.uninhabited_false
  unfold translateTy at hu
  rw [hk] at hu
  dsimp only at hu
  rw [hlook] at hu
  dsimp only [translateTypeLayout] at hu
  have hpty : placeTyResolved localDecls layouts ⟨srcIdx, .nil⟩ = some srcDecl.ty := by
    unfold placeTyResolved
    dsimp only
    rw [hdecl]
  unfold evalPlaceDiscriminant
  dsimp only
  rw [hpty]
  dsimp only
  rw [hk]
  dsimp only
  have hlook' : LayoutTable.lookup layouts srcDecl.ty.layoutIdx = some tl := hlook
  rw [hlook', hnot_ord]
  have hmv := hvalid.multi_variant
  rcases tl with ⟨_, _, _, _, vars_s, isUninh, _⟩
  dsimp only at hu htl_vars ⊢
  subst hu
  rw [htl_vars]
  cases rawShapes with
  | nil => simp at hlen_eq; omega
  | cons r0 rs =>
    dsimp only
    have hble : Nat.ble (.succ v_act) (length (r0 :: rs)) = true := by
      have hlen_c : length (r0 :: rs) = (r0 :: rs).length := by
        clear hlen_eq; induction rs generalizing r0 <;> simp [length, *]
      exact Nat.ble_eq.mpr (by omega)
    rw [hble]; rfl

theorem ValidEnumLayout.validateLoadedValue_unproj
    {decl : LocalDecl} {localDecls : List LocalDecl} {layouts : LayoutTable}
    {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    (hvalid : ValidEnumLayout decl.ty layouts tagBytes variants)
    {idx : Local} (hdecl : get? localDecls idx = some decl)
    {op : MirAst.Operand} (hop : op = .copy ⟨idx, .nil⟩ ∨ op = .move ⟨idx, .nil⟩)
    (v : Value) :
    validateLoadedValue layouts localDecls op v = true := by
  obtain ⟨defPath, adtArgs, hk⟩ := hvalid.is_adt
  rcases hop with rfl | rfl <;> {
    unfold validateLoadedValue
    dsimp only [operandTy, placeTy]
    rw [hdecl]
    dsimp only [resolveProjectedTy]
    rw [hk]
  }

theorem projectField_fixed_offset {layouts : LayoutTable}
    {parent fixedLay : Miri.Interpreter.LocalLayout}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {idx : Nat} {off : Miri.ABI.Size}
    (hoff : parent.layout.fields.offset idx = .ok off)
    (hsized : fixedLay.layout.isSized = true)
    (hno_ovf : mp.ptr.offset.bytes.toNat + off.bytes.toNat < 2 ^ 64) :
    Miri.Interpreter.projectField (fixedFieldProjectionCx layouts fixedLay)
        ⟨.indirect mp, parent⟩ idx =
      .ok ⟨.indirect
            ⟨⟨Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + off.bytes),
              mp.ptr.provenance⟩, .none, mp.misaligned⟩,
            fixedLay⟩ := by
  obtain ⟨hadd, _⟩ := size_add_of_no_overflow hno_ovf
  unfold Miri.Interpreter.projectField Miri.Interpreter.OpTy.offsetWithMeta
    fixedFieldProjectionCx annealStructProjectionCx
  simp [hoff, hsized, Miri.Interpreter.MemPlaceMeta.hasMeta,
    hadd, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem projectField_fixed_zero {layouts : LayoutTable}
    {parent fixedLay : Miri.Interpreter.LocalLayout}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hfields : parent.layout.fields = .Arbitrary #[Miri.ABI.Size.ZERO] #[0])
    (hsized : fixedLay.layout.isSized = true)
    (hmeta : mp.metadata = .none) :
    Miri.Interpreter.projectField (fixedFieldProjectionCx layouts fixedLay)
        ⟨.indirect mp, parent⟩ 0 =
      .ok ⟨.indirect mp, fixedLay⟩ := by
  have hoff : parent.layout.fields.offset 0 = .ok Miri.ABI.Size.ZERO := by
    rw [hfields]; rfl
  have hovf : mp.ptr.offset.bytes.toNat + Miri.ABI.Size.ZERO.bytes.toNat < 2 ^ 64 := by
    dsimp [Miri.ABI.Size.ZERO]; exact mp.ptr.offset.bytes.toNat_lt
  rw [projectField_fixed_offset hoff hsized hovf]
  rcases mp with ⟨⟨⟨b⟩, p⟩, meta_, mis⟩
  dsimp only at hmeta
  subst hmeta
  simp [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes]

theorem projectField_fixed_zero_uninit {layouts : LayoutTable}
    {parent fixedLay : Miri.Interpreter.LocalLayout}
    (hfields : parent.layout.fields = .Arbitrary #[Miri.ABI.Size.ZERO] #[0])
    (hsized : fixedLay.layout.isSized = true)
    (hle : fixedLay.layout.size.bytes ≤ parent.layout.size.bytes) :
    Miri.Interpreter.projectField (fixedFieldProjectionCx layouts fixedLay)
        ⟨.immediate .uninit, parent⟩ 0 =
      .ok ⟨.immediate .uninit, fixedLay⟩ := by
  have hoff : parent.layout.fields.offset 0 = .ok Miri.ABI.Size.ZERO := by
    rw [hfields]; rfl
  have hovf : Miri.ABI.Size.ZERO.bytes.toNat + fixedLay.layout.size.bytes.toNat < 2 ^ 64 := by
    dsimp [Miri.ABI.Size.ZERO]
    rw [Nat.zero_add]
    exact fixedLay.layout.size.bytes.toNat_lt
  obtain ⟨hadd, _⟩ := size_add_of_no_overflow hovf
  have hof : Miri.ABI.Size.ofBytes (Miri.ABI.Size.ZERO.bytes + fixedLay.layout.size.bytes) =
      fixedLay.layout.size := by
    cases fixedLay.layout.size
    simp [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes]
  have hnot_gt : ¬ (fixedLay.layout.size.bytes > parent.layout.size.bytes) := by
    simp only [gt_iff_lt, UInt64.lt_iff_toNat_lt]
    simp only [UInt64.le_iff_toNat_le] at hle
    omega
  unfold Miri.Interpreter.projectField Miri.Interpreter.OpTy.offsetWithMeta
    fixedFieldProjectionCx annealStructProjectionCx Miri.Interpreter.projectionImmediateOffset
  simp [hoff, hsized, Miri.Interpreter.MemPlaceMeta.hasMeta, hadd, hof, hnot_gt,
    Except.mapError, bind, Except.bind, pure, Except.pure]

/-- `Discriminant.discriminantForVariant` produces the canonical `isize`
(8-byte) discriminant scalar `⟨v, 8⟩` for any declared variant
`v < variants.length` of a `ValidEnumLayout` enum. -/
theorem discriminantForVariant_enum_ok
    (localDecls : List LocalDecl)
    {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)}
    (hvalid : ValidEnumLayout ty layouts tagBytes variants)
    {v : Nat} (hv : v < variants.length)
    (m : AnnealStepState) :
    ∃ msc8 : Miri.Memory.ScalarInt,
      ScalarRel ⟨v, 8⟩ msc8 ∧
      Miri.Interpreter.Discriminant.discriminantForVariant
          (annealDiscriminantHooksLM2_3 localDecls layouts) ()
          (translateTy ty layouts).ty v m =
        .ok ⟨.scalar (.fromScalarInt msc8),
              translateTy { kind := .int .isize, layoutIdx := 0 } layouts⟩ m := by
  obtain ⟨tl, vr, rawTag, rawShapes, hlookup, htl_vars, hraw_len, _, _, _, _, _, _⟩ :=
    hvalid.table_entry
  have htb_le8 : tagBytes ≤ 8 := by
    rcases hvalid.tagBytes_valid with rfl | rfl | rfl | rfl <;> omega
  have hv_lt64 : v < 2 ^ (8 * 8) := by
    have hpow : 2 ^ (8 * tagBytes) ≤ 2 ^ (8 * 8) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    exact Nat.lt_of_lt_of_le hv (Nat.le_trans hvalid.variants_fit_tag hpow)
  obtain ⟨msc8, hrel8, hfrom8⟩ :=
    scalarFromUInt_of_lt (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hv_lt64
  refine ⟨msc8, hrel8, ?_⟩
  have hty_eq := hvalid.translateTy_ty_eq
  have hge100 : 100 ≤ 100 + ty.layoutIdx := Nat.le_add_right 100 ty.layoutIdx
  have hsub100 : 100 + ty.layoutIdx - 100 = ty.layoutIdx :=
    Nat.add_sub_cancel_left 100 ty.layoutIdx
  have hv_raw : v < rawShapes.length := by omega
  have hisize_sz :
      (translateTy { kind := .int .isize, layoutIdx := 0 } layouts).layout.size =
        translateSizeBytes 8 := rfl
  have hisize_ty :
      (translateTy { kind := .int .isize, layoutIdx := 0 } layouts).ty = 15 := rfl
  unfold Miri.Interpreter.Discriminant.discriminantForVariant
    annealDiscriminantHooksLM2_3
  dsimp only [bind, EStateM.bind, pure, EStateM.pure]
  rw [hty_eq]
  simp only [hge100, ↓reduceIte, hsub100, hlookup, htl_vars, hv_raw,
    hisize_ty, hisize_sz]
  dsimp only [EStateM.bind, EStateM.pure]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  dsimp only [EStateM.bind, EStateM.pure]
  rw [hfrom8]
  rfl

private theorem tryToScalarInt_fromScalarInt (s : Miri.Memory.ScalarInt) :
    (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) s).tryToScalarInt =
      .ok (.integer s) := rfl

private theorem toScalarInt_fromScalarInt (s : Miri.Memory.ScalarInt) :
    (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) s).toScalarInt =
      .ok s := rfl

private theorem rvalueM_bind_ok {α β : Type}
    {x : Miri.Interpreter.RvalueM AnnealStepState α}
    {f : α → Miri.Interpreter.RvalueM AnnealStepState β}
    {a : α} {s s' : AnnealStepState} (hx : x s = .ok a s') :
    (x >>= f) s = f a s' := by
  change EStateM.bind x f s = f a s'
  dsimp [EStateM.bind]
  rw [hx]

private theorem rvalueM_bind_err {α β : Type}
    {x : Miri.Interpreter.RvalueM AnnealStepState α}
    {f : α → Miri.Interpreter.RvalueM AnnealStepState β}
    {e : Miri.Interpreter.StepError} {s s' : AnnealStepState}
    (hx : x s = .error e s') :
    (x >>= f) s = .error e s' := by
  change EStateM.bind x f s = .error e s'
  dsimp [EStateM.bind]
  rw [hx]

private theorem rvalueM_bind_same {α β : Type}
    {x : Miri.Interpreter.RvalueM AnnealStepState α}
    {f : α → Miri.Interpreter.RvalueM AnnealStepState β}
    {s : AnnealStepState} (a : α) (hx : x s = .ok a s) :
    (x >>= f) s = f a s :=
  rvalueM_bind_ok hx

/-- `Discriminant.tagForVariant` computes `some (mscTag, 0)` with
`ScalarRel ⟨v, tagBytes⟩ mscTag` for any declared variant `v < variants.length`
of a `ValidEnumLayout` enum. -/
theorem tagForVariant_enum_ok
    (localDecls : List LocalDecl)
    {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)}
    (hvalid : ValidEnumLayout ty layouts tagBytes variants)
    {v : Nat} (hv : v < variants.length)
    (m : AnnealStepState) :
    ∃ mscTag : Miri.Memory.ScalarInt,
      ScalarRel ⟨v, tagBytes⟩ mscTag ∧
      Miri.Interpreter.Discriminant.tagForVariant
          (annealDiscriminantHooksLM2_3 localDecls layouts) ()
          (translateTy ty layouts) v m =
        .ok (some (mscTag, 0)) m := by
  obtain ⟨_, vr, _, _, _, _, _, _, _, vars, _, hvars, _⟩ := hvalid.table_entry
  have htb_valid := validScalarBytes_of_tagBytes hvalid.tagBytes_valid
  have hv_lt_tag : v < 2 ^ (8 * tagBytes) :=
    Nat.lt_of_lt_of_le hv hvalid.variants_fit_tag
  obtain ⟨msc8, hrel8, hdiscr⟩ :=
    discriminantForVariant_enum_ok localDecls hvalid hv m
  obtain ⟨_, _, _, _, _, _, _, _, htag_sz⟩ :=
    tagLayoutOfAbiScalar_enum hvalid.tagBytes_valid vr
  obtain ⟨mscTag, hrelTag, hfromTag⟩ := scalarFromUInt_of_lt htb_valid hv_lt_tag
  have hinh := hvalid.isVariantUninhabited_false hv
  have hisize_sz :
      (translateTy { kind := .int .isize, layoutIdx := 0 } layouts).layout.size =
        translateSizeBytes 8 := rfl
  have h8_nz : ((translateSizeBytes 8).bytes == 0) = false := by decide
  have hbits8 : msc8.toBits (translateSizeBytes 8) = .ok (BitVec.ofNat 128 v) :=
    hrel8.toBits_eq
  have htrunc :
      (translateSizeBytes tagBytes).truncate (BitVec.ofNat 128 v) =
        .ok (BitVec.ofNat 128 v) := by
    rw [size_truncate_translateSizeBytes htb_valid]
    have hbv := bitVec_ofNat_toNat_of_valid htb_valid
      (by rw [scalarModulus_eq_two_pow]; exact hv_lt_tag)
    rw [hbv, Nat.mod_eq_of_lt hv_lt_tag]
  have hsc_bits :
      (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc8).toBits (translateSizeBytes 8) =
        .ok (BitVec.ofNat 128 v) := by
    unfold Miri.Memory.Scalar.toBits
    simp [h8_nz, toScalarInt_fromScalarInt, hbits8, bind, Except.bind, Except.mapError]
  refine ⟨mscTag, hrelTag, ?_⟩
  unfold Miri.Interpreter.Discriminant.tagForVariant
  rw [hinh, hvars]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine (rvalueM_bind_ok hdiscr).trans ?_
  refine (rvalueM_bind_same (Miri.Memory.Scalar.fromScalarInt msc8) rfl).trans ?_
  refine (rvalueM_bind_same (BitVec.ofNat 128 v) ?_).trans ?_
  · dsimp only
    rw [hisize_sz]
    conv => lhs; whnf
    dsimp only [Miri.Interpreter.RvalueM]
    rw [hsc_bits]; rfl
  refine (rvalueM_bind_same (translateSizeBytes tagBytes) ?_).trans ?_
  · change ((match (Miri.ABI.Scalar.Initialized
        (value := .Int (translateAbiIntegerBytes tagBytes) false)
        (validRange := vr)).size annealRuntimeDataLayout with
      | .ok val => pure val
      | .error e =>
          throw (Miri.Interpreter.StepError.invalidProgram s!"tag scalar size: {repr e}") :
        Miri.Interpreter.RvalueM AnnealStepState Miri.ABI.Size)) m =
      EStateM.Result.ok (translateSizeBytes tagBytes) m
    rw [htag_sz]; rfl
  refine (rvalueM_bind_same (BitVec.ofNat 128 v) ?_).trans ?_
  · rw [htrunc]; rfl
  refine (rvalueM_bind_same (.fromScalarInt mscTag) ?_).trans ?_
  · rw [hfromTag]; rfl
  refine (rvalueM_bind_same mscTag ?_).trans rfl
  rw [toScalarInt_fromScalarInt]; rfl

/-- `Discriminant.readDiscriminant` on a live `EnumMemRel` indirect enum operand
reads the tag scalar at `[0, tagBytes)` and returns the active variant index
`v_act`. -/
theorem readDiscriminant_enumInd_ok
    (localDecls : List LocalDecl)
    {m : AnnealStepState} {ty : Ty} {layouts : LayoutTable}
    {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    {v_act : Nat} {fieldVals : List Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hmem : EnumMemRel m.machine ty layouts tagBytes variants v_act fieldVals mp) :
    Miri.Interpreter.Discriminant.readDiscriminant
        (annealDiscriminantHooksLM2_3 localDecls layouts) ()
        ⟨.indirect mp, translateTy ty layouts⟩ m =
      .ok v_act m := by
  rcases hmem with ⟨allocId, borTag, baseAddr, localAlloc, words, msc_tag,
    hvalid, hv_lt, hprov, _, hmeta, hlive, hbase, hptr, _, _, _, _, _, _, _,
    htag_rel, _, _, htag_read, _⟩
  obtain ⟨hfind_live, _⟩ := hlive
  obtain ⟨tl, vr, rawTag, rawShapes, hlookup, htl_vars, hraw_len, _, hvr_in,
    vars, _, hvars, _⟩ := hvalid.table_entry
  obtain ⟨tagLay, htag_lay, htag_sz, htag_nz, htag_fields, htag_repr,
    htag_signed, htag_sized, _⟩ :=
    tagLayoutOfAbiScalar_enum hvalid.tagBytes_valid vr
  have henum_tag : enumTagLayoutOf (translateTy ty layouts) = some tagLay := by
    unfold enumTagLayoutOf; rw [hvars]; exact htag_lay
  have hproj := projectField_fixed_zero (layouts := layouts)
    hvalid.outer_fields_tag0 htag_sized hmeta
  have hptr0 : mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + Miri.ABI.Size.ZERO.bytes) := by
    rw [hptr]; dsimp [Miri.ABI.Size.ZERO]; rw [UInt64.add_zero]
  have hread_tag :
      annealReadImmediateLM2_2 ⟨.indirect mp, tagLay⟩ m =
        .ok ⟨.scalar (.fromScalarInt msc_tag), tagLay⟩ m := by
    apply annealReadIndirectImmediate_scalarRepr_ok htag_nz
      (by rw [htag_fields]; nofun) htag_repr hprov hbase hptr0 hfind_live
    rw [htag_sz]; exact htag_read
  have hbits_tag : msc_tag.toBits tagLay.layout.size = .ok (BitVec.ofNat 128 v_act) := by
    rw [htag_sz]; exact htag_rel.toBits_eq
  have hvr_ok :
      (Miri.ABI.Scalar.Initialized
        (value := .Int (translateAbiIntegerBytes tagBytes) false)
        (validRange := vr)).validRange annealRuntimeDataLayout = .ok vr := rfl
  have hcontains := hvr_in v_act hv_lt
  have hv_lt64 : v_act < 2 ^ (8 * 8) := by
    have htb_le8 : tagBytes ≤ 8 := by
      rcases hvalid.tagBytes_valid with rfl | rfl | rfl | rfl <;> omega
    exact Nat.lt_of_lt_of_le hv_lt
      (Nat.le_trans hvalid.variants_fit_tag (Nat.pow_le_pow_right (by decide) (by omega)))
  have htrunc8 :
      (translateTy { kind := .int .isize, layoutIdx := 0 } layouts).layout.size.truncate
        (BitVec.ofNat 128 v_act) = .ok (BitVec.ofNat 128 v_act) := by
    change (translateSizeBytes 8).truncate (BitVec.ofNat 128 v_act) = _
    rw [size_truncate_translateSizeBytes (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]
    have hbv := bitVec_ofNat_toNat_of_valid (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (by rw [scalarModulus_eq_two_pow]; exact hv_lt64)
    rw [hbv, Nat.mod_eq_of_lt hv_lt64]
  have hbv_nat : (BitVec.ofNat 128 v_act).toNat = v_act :=
    bitVec_ofNat_toNat_of_valid (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (by rw [scalarModulus_eq_two_pow]; exact hv_lt64)
  have hty_eq := hvalid.translateTy_ty_eq
  have hge100 : 100 ≤ 100 + ty.layoutIdx := Nat.le_add_right 100 ty.layoutIdx
  have hsub100 : 100 + ty.layoutIdx - 100 = ty.layoutIdx :=
    Nat.add_sub_cancel_left 100 ty.layoutIdx
  have hv_raw : v_act < rawShapes.length := by omega
  have hinh := hvalid.isVariantUninhabited_false hv_lt
  unfold Miri.Interpreter.Discriminant.readDiscriminant
  rw [hvars]
  dsimp only
  refine (rvalueM_bind_same (translateTy { kind := .int .isize, layoutIdx := 0 } layouts) rfl).trans ?_
  refine (rvalueM_bind_same tagLay ?_).trans ?_
  · dsimp only [annealDiscriminantHooksLM2_3]; rw [htag_lay]; rfl
  refine (rvalueM_bind_same ⟨.indirect mp, tagLay⟩ ?_).trans ?_
  · dsimp only [annealDiscriminantHooksLM2_3]; rw [henum_tag]; dsimp only; rw [hproj]; rfl
  refine (rvalueM_bind_ok hread_tag).trans ?_
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  refine (rvalueM_bind_same false ?_).trans ?_
  · change ((match tagLay.layout.backendRepr.isSigned with
      | .ok val => pure val
      | .error _ => throw
          (Miri.Interpreter.StepError.invalidProgram
            "discriminant requires scalar backend representation") :
        Miri.Interpreter.RvalueM AnnealStepState Bool)) m = EStateM.Result.ok false m
    rw [htag_signed]; rfl
  refine (rvalueM_bind_same false ?_).trans ?_
  · change ((match tagLay.layout.backendRepr.isSigned with
      | .ok val => pure val
      | .error _ => throw
          (Miri.Interpreter.StepError.invalidProgram
            "discriminant requires scalar backend representation") :
        Miri.Interpreter.RvalueM AnnealStepState Bool)) m = EStateM.Result.ok false m
    rw [htag_signed]; rfl
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  refine (rvalueM_bind_same (Miri.Memory.Scalar.fromScalarInt msc_tag) rfl).trans ?_
  refine (rvalueM_bind_same (Miri.Memory.ScalarIntCastResult.integer msc_tag) ?_).trans ?_
  · rw [tryToScalarInt_fromScalarInt]; rfl
  dsimp only
  refine (rvalueM_bind_same (BitVec.ofNat 128 v_act) ?_).trans ?_
  · rw [hbits_tag]; rfl
  refine (rvalueM_bind_same vr ?_).trans ?_
  · change ((match (Miri.ABI.Scalar.Initialized
        (value := .Int (translateAbiIntegerBytes tagBytes) false)
        (validRange := vr)).validRange annealRuntimeDataLayout with
      | .ok val => pure val
      | .error e => throw
          (Miri.Interpreter.StepError.invalidProgram s!"tag scalar range: {repr e}") :
        Miri.Interpreter.RvalueM AnnealStepState Miri.ABI.WrappingRange)) m =
      EStateM.Result.ok vr m
    rw [hvr_ok]; rfl
  rw [hcontains]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine (rvalueM_bind_same (BitVec.ofNat 128 v_act) rfl).trans ?_
  refine (rvalueM_bind_same (BitVec.ofNat 128 v_act) ?_).trans ?_
  · rw [htrunc8]; rfl
  refine (rvalueM_bind_same (some v_act) ?_).trans ?_
  · dsimp only [annealDiscriminantHooksLM2_3]
    rw [hty_eq]
    simp only [hge100, ↓reduceIte, hsub100, hlookup, htl_vars, hbv_nat, hv_raw]
    rfl
  refine (rvalueM_bind_same v_act rfl).trans ?_
  rw [hinh]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rfl

/-- `Discriminant.readDiscriminant` on an uninitialized immediate enum operand
projects the tag field to `.immediate .uninit` and diagnoses
`StepError.undefinedBehavior "read of uninitialized local"`. -/
theorem readDiscriminant_uninitImm_ub
    (localDecls : List LocalDecl)
    {m : AnnealStepState} {ty : Ty} {layouts : LayoutTable}
    {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    (hvalid : ValidEnumLayout ty layouts tagBytes variants) :
    Miri.Interpreter.Discriminant.readDiscriminant
        (annealDiscriminantHooksLM2_3 localDecls layouts) ()
        ⟨.immediate .uninit, translateTy ty layouts⟩ m =
      .error (.undefinedBehavior "read of uninitialized local") m := by
  obtain ⟨_, vr, _, _, _, _, _, _, _, _, _, hvars, _⟩ := hvalid.table_entry
  obtain ⟨tagLay, htag_lay, htag_sz, _, _, _, _, htag_sized, _⟩ :=
    tagLayoutOfAbiScalar_enum hvalid.tagBytes_valid vr
  have henum_tag : enumTagLayoutOf (translateTy ty layouts) = some tagLay := by
    unfold enumTagLayoutOf; rw [hvars]; exact htag_lay
  have htb_nat := translateSizeBytes_toNat_eq (validScalarBytes_of_tagBytes hvalid.tagBytes_valid)
  have hinb : tagLay.layout.size.bytes ≤ (translateTy ty layouts).layout.size.bytes := by
    rw [htag_sz]; simp only [UInt64.le_iff_toNat_le, htb_nat]; exact hvalid.size_ge_tag
  have hproj := projectField_fixed_zero_uninit (layouts := layouts)
    hvalid.outer_fields_tag0 htag_sized hinb
  unfold Miri.Interpreter.Discriminant.readDiscriminant
  rw [hvars]
  dsimp only [Miri.Interpreter.RvalueM, annealDiscriminantHooksLM2_3,
    bind, EStateM.bind, pure, EStateM.pure]
  rw [htag_lay]
  dsimp only
  rw [henum_tag]
  dsimp only
  rw [hproj]
  rfl

/-- `Discriminant.readDiscriminant` on an uninitialized indirect enum allocation
(`UninitEnumMemRel`) queries `[0, tagBytes)` on `InitMask.new enumSize false`
and diagnoses `StepError.undefinedBehavior`
(`"read of uninitialized memory field"`). -/
theorem readDiscriminant_uninitInd_ub
    (localDecls : List LocalDecl)
    {m : AnnealStepState} {ty : Ty} {layouts : LayoutTable}
    {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hmem : UninitEnumMemRel m.machine ty layouts tagBytes variants mp) :
    Miri.Interpreter.Discriminant.readDiscriminant
        (annealDiscriminantHooksLM2_3 localDecls layouts) ()
        ⟨.indirect mp, translateTy ty layouts⟩ m =
      .error (.undefinedBehavior "read of uninitialized memory field") m := by
  rcases hmem with ⟨allocId, _, baseAddr, localAlloc, hvalid, hprov, _, hmeta,
    hlive, hbase, hptr, _, _, _, _, _, _, hmask_uninit⟩
  obtain ⟨hfind_live, _⟩ := hlive
  obtain ⟨_, vr, _, _, _, _, _, _, _, _, _, hvars, _⟩ := hvalid.table_entry
  obtain ⟨tagLay, htag_lay, htag_sz, htag_nz, htag_fields, htag_repr, _,
    htag_sized, _⟩ :=
    tagLayoutOfAbiScalar_enum hvalid.tagBytes_valid vr
  have henum_tag : enumTagLayoutOf (translateTy ty layouts) = some tagLay := by
    unfold enumTagLayoutOf; rw [hvars]; exact htag_lay
  have hproj := projectField_fixed_zero (layouts := layouts)
    hvalid.outer_fields_tag0 htag_sized hmeta
  have hptr0 : mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + Miri.ABI.Size.ZERO.bytes) := by
    rw [hptr]; dsimp [Miri.ABI.Size.ZERO]; rw [UInt64.add_zero]
  have htb_valid := validScalarBytes_of_tagBytes hvalid.tagBytes_valid
  have htb_nat := translateSizeBytes_toNat_eq htb_valid
  have hend :
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO tagLay.layout.size).endExclusive =
        .ok tagLay.layout.size := by
    rw [htag_sz]
    unfold Miri.Memory.AllocRange.endExclusive Miri.Memory.AllocRange.end Miri.Memory.allocRange
    have h0 : Miri.ABI.Size.ZERO.bytes + (translateSizeBytes tagBytes).bytes =
        (translateSizeBytes tagBytes).bytes := UInt64.zero_add _
    have hnw : ¬ (translateSizeBytes tagBytes).bytes < Miri.ABI.Size.ZERO.bytes := by
      simp [Miri.ABI.Size.ZERO, UInt64.lt_iff_toNat_lt]
    have hof : Miri.ABI.Size.ofBytes (translateSizeBytes tagBytes).bytes =
        translateSizeBytes tagBytes := by cases translateSizeBytes tagBytes; rfl
    simp [Miri.ABI.Size.add, h0, hnw, hof, Except.mapError]
  have hinb : tagLay.layout.size.bytes ≤ (translateTy ty layouts).layout.size.bytes := by
    rw [htag_sz]
    simp only [UInt64.le_iff_toNat_le, htb_nat]
    exact hvalid.size_ge_tag
  have huninit_q :
      localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO tagLay.layout.size) =
        .ok (.error (Miri.Memory.allocRange Miri.ABI.Size.ZERO tagLay.layout.size)) := by
    rw [hmask_uninit]
    exact Miri.Memory.InitMask.lazy_uninitialized_query
      (translateTy ty layouts).layout.size _ _ hend hinb
  have hread_err :=
    annealReadIndirectImmediate_scalarRepr_uninit_ub htag_nz
      (by rw [htag_fields]; nofun) htag_repr hprov hbase hptr0 hfind_live huninit_q
  unfold Miri.Interpreter.Discriminant.readDiscriminant
  rw [hvars]
  dsimp only [Miri.Interpreter.RvalueM, annealDiscriminantHooksLM2_3,
    bind, EStateM.bind, pure, EStateM.pure]
  rw [htag_lay]
  dsimp only [EStateM.bind, EStateM.pure]
  rw [henum_tag]
  dsimp only [EStateM.bind, EStateM.pure]
  rw [hproj]
  dsimp only [annealReadImmediateLM2_2, EStateM.bind, EStateM.pure]
  rw [hread_err]

/-- `Discriminant.writeDiscriminant` on enum local `dstIdx` once
`annealForceEnumAllocation` has resolved the local to the thin indirect place
`mp` in state `m₁`. The tag scalar `⟨v, tagBytes⟩` lands at `[0, tagBytes)` of
the backing allocation, and every byte and initialization bit at offsets
`b ≥ tagBytes` is preserved. `tagForVariant` reads no state, so the only state
change before the tag write is the one `annealForceEnumAllocation` makes; in
particular, no initialization check runs on the destination. -/
theorem writeDiscriminant_local_of_forced_ok
    (localDecls : List LocalDecl)
    {m m₁ : AnnealStepState}
    {tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Nat} {iden : Miri.Interpreter.LocalsIdentity}
    {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {allocId : Miri.Memory.AllocId} {borTag : Miri.Memory.BorTag}
    {baseAddr : UInt64} {localAlloc : AnnealLocalAlloc}
    {words : Array UInt64} {v : Nat}
    (hfa : annealForceEnumAllocation localDecls layouts
        ⟨.local 0 dstIdx none iden, translateTy ty layouts⟩ m =
      .ok ⟨mp, translateTy ty layouts⟩ m₁)
    (hframes₁ : m₁.stack.frames = #[tf₁])
    (hvalid : ValidEnumLayout ty layouts tagBytes variants)
    (hv : v < variants.length)
    (hprov : mp.ptr.provenance = some (.concrete allocId borTag))
    (hmeta : mp.metadata = .none)
    (hlive : LiveAllocEntry m₁.machine.memory.live allocId localAlloc)
    (hbase : m₁.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
    (hbs : localAlloc.allocation.byteSize = (translateTy ty layouts).layout.size)
    (hlen : localAlloc.allocation.len = localAlloc.allocation.byteSize.bytes.toNat)
    (hmut : localAlloc.allocation.mutability = .Mut)
    (hpmap : localAlloc.allocation.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask : InitMaskWordRel localAlloc.allocation.initializationMask
      localAlloc.allocation.byteSize words) :
    ∃ (u : Nat) (hu_lt : u < m₁.machine.memory.live.size)
      (alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
      (words' : Array UInt64) (mscTag : Miri.Memory.ScalarInt),
      m₁.machine.memory.live[u]'hu_lt = (allocId, localAlloc) ∧
      Miri.Interpreter.Discriminant.writeDiscriminant
          (annealDiscriminantHooksLM2_3 localDecls layouts) () v
          ⟨.local 0 dstIdx none iden, translateTy ty layouts⟩ m =
        .ok () { m₁ with machine := updateAllocMachine m₁.machine u allocId localAlloc.kind alloc' } ∧
      LiveAllocEntry
        (updateAllocMachine m₁.machine u allocId localAlloc.kind alloc').memory.live
        allocId ⟨localAlloc.kind, alloc'⟩ ∧
      ScalarRel ⟨v, tagBytes⟩ mscTag ∧
      alloc'.byteSize = localAlloc.allocation.byteSize ∧
      alloc'.len = localAlloc.allocation.len ∧
      alloc'.mutability = .Mut ∧
      alloc'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      InitMaskWordRel alloc'.initializationMask localAlloc.allocation.byteSize words' ∧
      (∀ b < localAlloc.allocation.byteSize.bytes.toNat,
        maskBlocksGetBit words' b =
          (maskBlocksGetBit words b || decide (b < tagBytes))) ∧
      lm22AllocRaw alloc' =
        (lm22AllocRaw localAlloc.allocation).extract 0 0 ++
          lm22LeBytes v (translateSizeBytes tagBytes).bytes.toNat ++
          (lm22AllocRaw localAlloc.allocation).extract
            (translateSizeBytes tagBytes).bytes.toNat
            (lm22AllocRaw localAlloc.allocation).size ∧
      alloc'.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes tagBytes)) =
        .ok (.ok ()) ∧
      alloc'.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes tagBytes)) false =
        .ok (.fromScalarInt mscTag) := by
  obtain ⟨hfind_live, u, hu_lt, hfidx, hget⟩ := hlive
  obtain ⟨mscTag, hrelTag, htag_v⟩ := tagForVariant_enum_ok localDecls hvalid hv m
  obtain ⟨_, vr, _, _, _, _, _, _, _, _, _, hvars, _⟩ := hvalid.table_entry
  obtain ⟨tagLay, htag_lay, _, _, _, _, _, htag_sized, _⟩ :=
    tagLayoutOfAbiScalar_enum hvalid.tagBytes_valid vr
  have henum_tag : enumTagLayoutOf (translateTy ty layouts) = some tagLay := by
    unfold enumTagLayoutOf; rw [hvars]; exact htag_lay
  have hproj := projectField_fixed_zero (layouts := layouts)
    hvalid.outer_fields_tag0 htag_sized hmeta
  have htb_valid := validScalarBytes_of_tagBytes hvalid.tagBytes_valid
  have htb_nat := translateSizeBytes_toNat_eq htb_valid
  have hge_tag := hvalid.size_ge_tag
  have hbnd :
      Miri.ABI.Size.ZERO.bytes.toNat + (translateSizeBytes tagBytes).bytes.toNat ≤
        localAlloc.allocation.byteSize.bytes.toNat := by
    rw [hbs, htb_nat]; dsimp [Miri.ABI.Size.ZERO]; omega
  obtain ⟨alloc', words', hw_sc, hbs', hlen', hmut', hpmap', hmask', hbits',
      hraw', hinit', hread'⟩ :=
    alloc_writeScalar_at_offset_mask (sc := ⟨v, tagBytes⟩) hrelTag
      (start := Miri.ABI.Size.ZERO) hlen hmut hpmap hmask hbnd
  have hptr0 : mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + Miri.ABI.Size.ZERO.bytes) := by
    rw [hptr]; dsimp [Miri.ABI.Size.ZERO]; rw [UInt64.add_zero]
  have hzz : Miri.ABI.Size.ofBytes (Miri.ABI.Size.ZERO.bytes + Miri.ABI.Size.ZERO.bytes) =
      Miri.ABI.Size.ZERO := rfl
  have hmsc_sz : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) mscTag).size =
      mscTag.size := rfl
  have hcf := stack_currentFrame?_singleton m₁.stack tf₁ hframes₁
  have hw_ind :
      annealWriteIndirectImmediate (.scalar (.fromScalarInt mscTag)) mp Miri.ABI.Size.ZERO tagLay m₁ =
        .ok () { m₁ with machine := updateAllocMachine m₁.machine u allocId localAlloc.kind alloc' } :=
    annealWriteIndirectImmediate_scalar_ok (mpOff := Miri.ABI.Size.ZERO)
      (relOffset := Miri.ABI.Size.ZERO) (fieldLay := tagLay)
      hprov hbase hptr0 hu_lt hfidx hget (by rw [hzz, hmsc_sz]; exact hw_sc)
  have hw_imm :
      annealWriteImmediateLM2_2 (.scalar (.fromScalarInt mscTag)) ⟨.memory mp, tagLay⟩ m₁ =
        .ok () { m₁ with machine := updateAllocMachine m₁.machine u allocId localAlloc.kind alloc' } := by
    unfold annealWriteImmediateLM2_2
    simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hcf]
    exact hw_ind
  refine ⟨u, hu_lt, alloc', words', mscTag, hget, ?_,
    LiveAllocEntry.of_set!_self ⟨hfind_live, u, hu_lt, hfidx, hget⟩ hu_lt hfidx
      ⟨localAlloc.kind, alloc'⟩,
    hrelTag, hbs', hlen', hmut', hpmap', hmask', ?_, ?_, hinit', hread'⟩
  · have hdest :
        (annealDiscriminantHooksLM2_3 localDecls layouts).destLayout
          ⟨.local 0 dstIdx none iden, translateTy ty layouts⟩ =
        translateTy ty layouts := rfl
    unfold Miri.Interpreter.Discriminant.writeDiscriminant
    dsimp only [Miri.Interpreter.RvalueM, bind, EStateM.bind, pure, EStateM.pure]
    rw [hdest, htag_v]
    dsimp only [Miri.Interpreter.RvalueM, annealDiscriminantHooksLM2_3,
      bind, EStateM.bind, pure, EStateM.pure]
    rw [henum_tag]
    dsimp only [EStateM.bind, EStateM.pure]
    rw [hfa]
    dsimp only [EStateM.bind, EStateM.pure]
    rw [hproj]
    exact hw_imm
  · intro b hb
    rw [hbits' b hb]
    dsimp [Miri.ABI.Size.ZERO]
    rw [htb_nat]
    congr 1
    simp
  · dsimp [Miri.ABI.Size.ZERO] at hraw'
    simpa using hraw'

/-- `Discriminant.writeDiscriminant` on a live `.indirect mp` enum local writes
the variant tag scalar `⟨v, tagBytes⟩` at `[0, tagBytes)` of the backing stack
allocation and preserves all bytes and initialization bits at offsets
`b ≥ tagBytes`. The allocation's initialization state is arbitrary (`words`),
so this covers both initialized and all-uninitialized enum allocations. -/
theorem writeDiscriminant_indirect_local_ok
    (localDecls : List LocalDecl)
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Nat} {c : Option Miri.Interpreter.LocalLayout}
    {iden : Miri.Interpreter.LocalsIdentity}
    {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {allocId : Miri.Memory.AllocId} {borTag : Miri.Memory.BorTag}
    {baseAddr : UInt64} {localAlloc : AnnealLocalAlloc}
    {words : Array UInt64} {v : Nat}
    (hframes : m.stack.frames = #[tf])
    (hlt : dstIdx < tf.locals.size)
    (hind : tf.locals[dstIdx]'hlt = ⟨.live (.indirect mp), c⟩)
    (hvalid : ValidEnumLayout ty layouts tagBytes variants)
    (hv : v < variants.length)
    (hprov : mp.ptr.provenance = some (.concrete allocId borTag))
    (hmeta : mp.metadata = .none)
    (hlive : LiveAllocEntry m.machine.memory.live allocId localAlloc)
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
    (hbs : localAlloc.allocation.byteSize = (translateTy ty layouts).layout.size)
    (hlen : localAlloc.allocation.len = localAlloc.allocation.byteSize.bytes.toNat)
    (hmut : localAlloc.allocation.mutability = .Mut)
    (hpmap : localAlloc.allocation.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask : InitMaskWordRel localAlloc.allocation.initializationMask
      localAlloc.allocation.byteSize words) :
    ∃ (u : Nat) (hu_lt : u < m.machine.memory.live.size)
      (alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
      (words' : Array UInt64) (mscTag : Miri.Memory.ScalarInt),
      m.machine.memory.live[u]'hu_lt = (allocId, localAlloc) ∧
      Miri.Interpreter.Discriminant.writeDiscriminant
          (annealDiscriminantHooksLM2_3 localDecls layouts) () v
          ⟨.local 0 dstIdx none iden, translateTy ty layouts⟩ m =
        .ok () { m with machine := updateAllocMachine m.machine u allocId localAlloc.kind alloc' } ∧
      LiveAllocEntry
        (updateAllocMachine m.machine u allocId localAlloc.kind alloc').memory.live
        allocId ⟨localAlloc.kind, alloc'⟩ ∧
      ScalarRel ⟨v, tagBytes⟩ mscTag ∧
      alloc'.byteSize = localAlloc.allocation.byteSize ∧
      alloc'.len = localAlloc.allocation.len ∧
      alloc'.mutability = .Mut ∧
      alloc'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      InitMaskWordRel alloc'.initializationMask localAlloc.allocation.byteSize words' ∧
      (∀ b < localAlloc.allocation.byteSize.bytes.toNat,
        maskBlocksGetBit words' b =
          (maskBlocksGetBit words b || decide (b < tagBytes))) ∧
      lm22AllocRaw alloc' =
        (lm22AllocRaw localAlloc.allocation).extract 0 0 ++
          lm22LeBytes v (translateSizeBytes tagBytes).bytes.toNat ++
          (lm22AllocRaw localAlloc.allocation).extract
            (translateSizeBytes tagBytes).bytes.toNat
            (lm22AllocRaw localAlloc.allocation).size ∧
      alloc'.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes tagBytes)) =
        .ok (.ok ()) ∧
      alloc'.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes tagBytes)) false =
        .ok (.fromScalarInt mscTag) := by
  have hfa :
      annealForceEnumAllocation localDecls layouts
        ⟨.local 0 dstIdx none iden, translateTy ty layouts⟩ m =
      .ok ⟨mp, translateTy ty layouts⟩ m := by
    unfold annealForceEnumAllocation
    rw [forceAllocation_indirect_none_ok hframes hlt hind]
  exact writeDiscriminant_local_of_forced_ok localDecls hfa hframes hvalid hv
    hprov hmeta hlive hbase hptr hbs hlen hmut hpmap hmask

/-- `Discriminant.writeDiscriminant` on a dead enum local fails with
`"write to dead local"` UB (rustc's `DeadLocal`) in `projectWrite`'s
`annealForceEnumAllocation`, after `tagForVariant` succeeds without changing
the state. -/
theorem writeDiscriminant_dead_local_err
    (localDecls : List LocalDecl)
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Nat} {c : Option Miri.Interpreter.LocalLayout}
    {iden : Miri.Interpreter.LocalsIdentity}
    {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)} {v : Nat}
    (hframes : m.stack.frames = #[tf])
    (hlt : dstIdx < tf.locals.size)
    (hdead : tf.locals[dstIdx]'hlt = ⟨.dead, c⟩)
    (hvalid : ValidEnumLayout ty layouts tagBytes variants)
    (hv : v < variants.length) :
    Miri.Interpreter.Discriminant.writeDiscriminant
        (annealDiscriminantHooksLM2_3 localDecls layouts) () v
        ⟨.local 0 dstIdx none iden, translateTy ty layouts⟩ m =
      .error (.undefinedBehavior "write to dead local") m := by
  obtain ⟨_, _, htag_v⟩ := tagForVariant_enum_ok localDecls hvalid hv m
  obtain ⟨_, vr, _, _, _, _, _, _, _, _, _, hvars, _⟩ := hvalid.table_entry
  obtain ⟨tagLay, htag_lay, _, _, _, _, _, _, _⟩ :=
    tagLayoutOfAbiScalar_enum hvalid.tagBytes_valid vr
  have henum_tag : enumTagLayoutOf (translateTy ty layouts) = some tagLay := by
    unfold enumTagLayoutOf; rw [hvars]; exact htag_lay
  have hfa :
      annealForceEnumAllocation localDecls layouts
        ⟨.local 0 dstIdx none iden, translateTy ty layouts⟩ m =
      .error (.undefinedBehavior "write to dead local") m := by
    unfold annealForceEnumAllocation
    rw [forceAllocation_dead_err hframes hlt hdead]
  have hdest :
      (annealDiscriminantHooksLM2_3 localDecls layouts).destLayout
        ⟨.local 0 dstIdx none iden, translateTy ty layouts⟩ =
      translateTy ty layouts := rfl
  unfold Miri.Interpreter.Discriminant.writeDiscriminant
  dsimp only [Miri.Interpreter.RvalueM, bind, EStateM.bind, pure, EStateM.pure]
  rw [hdest, htag_v]
  dsimp only [Miri.Interpreter.RvalueM, annealDiscriminantHooksLM2_3,
    bind, EStateM.bind, pure, EStateM.pure]
  rw [henum_tag]
  dsimp only [EStateM.bind, EStateM.pure]
  rw [hfa]

/-- `Discriminant.writeDiscriminant` on an uninitialized immediate enum local
succeeds: `projectWrite`'s `annealForceEnumAllocation` moves the local into a
fresh all-uninitialized stack allocation, and the tag scalar is then written at
`[0, tagBytes)`. Nothing reads the destination first. -/
theorem writeDiscriminant_uninit_imm_local_ok
    (localDecls : List LocalDecl)
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Nat} {iden : Miri.Interpreter.LocalsIdentity}
    {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)} {v k : Nat}
    (hframes : m.stack.frames = #[tf])
    (hlt : dstIdx < tf.locals.size)
    (himm : tf.locals[dstIdx]'hlt =
      ⟨.live (.immediate .uninit), some (translateTy ty layouts)⟩)
    (hvalid : ValidEnumLayout ty layouts tagBytes variants)
    (hv : v < variants.length)
    (hsup : AllocIdSupplyValid (k + 1) m.machine.memory) :
    ∃ m', Miri.Interpreter.Discriminant.writeDiscriminant
        (annealDiscriminantHooksLM2_3 localDecls layouts) () v
        ⟨.local 0 dstIdx none iden, translateTy ty layouts⟩ m = .ok () m' ∧
      ∃ tf', m'.stack.frames = #[tf'] ∧ tf'.location = tf.location := by
  obtain ⟨rawAlloc, htry, hbs0, hlen0, hmut0, hpmap0, hmask0⟩ :=
    tryNew_uninit_of_pow2_le_29 (translateTy ty layouts).layout.size
      (translateTy ty layouts).layout.align.abi hvalid.align_pow2_le
  obtain ⟨mem', newId, hres, _, hlive_eq, hfresh, _, _⟩ := hsup.of_succ.reserve_step
  let a0 := rawAlloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree)
  let tf_down :=
    { tf with
      locals := tf.locals.set dstIdx
        ⟨.live (.indirect (stackAllocPlace newId)), some (translateTy ty layouts)⟩ hlt }
  let m_down : AnnealStepState :=
    ⟨⟨#[tf_down]⟩, stackAllocMachine m.machine mem' newId a0⟩
  have hfa :
      annealForceEnumAllocation localDecls layouts
        ⟨.local 0 dstIdx none iden, translateTy ty layouts⟩ m =
      .ok ⟨stackAllocPlace newId, translateTy ty layouts⟩ m_down := by
    unfold annealForceEnumAllocation
    rw [forceAllocation_uninit_none_ok hframes hlt himm hvalid.isSized_true htry hres]
  have hfresh' : mem'.live.any (fun entry => entry.1 == newId) = false := by
    rw [hlive_eq]; exact hfresh
  have hmask_a0 : InitMaskWordRel a0.initializationMask a0.byteSize
      (initWordsFalse (translateTy ty layouts).layout.size) := by
    dsimp [a0]
    rw [hmask0, hbs0]
    exact initMaskWordRel_new_false
  obtain ⟨_, _, _, _, _, _, hw, _⟩ :=
    writeDiscriminant_local_of_forced_ok localDecls hfa (tf₁ := tf_down) rfl hvalid hv
      rfl rfl (LiveAllocEntry.of_push_fresh_self _ hfresh')
      (lookupBaseAddr_stackAllocMachine_self _ _ _ _) rfl hbs0
      (by dsimp [a0]; rw [hlen0, hbs0]) hmut0 hpmap0 hmask_a0
  exact ⟨_, hw, tf_down, rfl, rfl⟩

/-! ## 3. Scalar Destination Plumbing and Primitive Scalar Operands -/

/-- Under a valid `EnumTypeEnv`, any primitive scalar type maps to `none`. -/
theorem env_none_of_isPrimScalarTy {env : EnumTypeEnv} {layouts : LayoutTable}
    {ty : Ty}
    (henv : ∀ t tb vs, env t = some (tb, vs) → ValidEnumLayout t layouts tb vs)
    (hprim : IsPrimScalarTy ty) :
    env ty = none := by
  cases h : env ty with
  | none => rfl
  | some pair =>
    rcases pair with ⟨tb, vs⟩
    obtain ⟨p, a, hadt⟩ := (henv ty tb vs h).is_adt
    rcases hprim with hk | hk | ⟨_, hk⟩ | ⟨_, hk⟩ <;> rw [hadt] at hk <;> cases hk

/-- When `env decl.ty = none`, `LocalRelLM2_3` reduces to `LocalRel`. -/
theorem LocalRelLM2_3.to_localRel_of_none {env : EnumTypeEnv}
    {mach : AnnealMachine} {decl : LocalDecl} {layouts : LayoutTable}
    {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (hnone : env decl.ty = none)
    (h : LocalRelLM2_3 env mach decl layouts slot mls) :
    LocalRel mach decl layouts slot mls := by
  cases h with
  | base _ _ _ hb => exact hb
  | enumDead _ _ _ hs _ _ => rw [hnone] at hs; cases hs
  | enumUninitImm _ _ _ hs _ _ => rw [hnone] at hs; cases hs
  | enumUninitInd _ _ _ _ hs _ _ => rw [hnone] at hs; cases hs
  | enumInd _ _ _ _ _ _ hs _ _ => rw [hnone] at hs; cases hs

/-- `EnumLocalByteUninit` is invariant under changing a frame's program
counter. -/
theorem EnumLocalByteUninit.of_set_location {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {loc : Miri.Interpreter.FrameLocation} {localId b : Nat}
    (hframes : m.stack.frames = #[topFrame])
    (h : EnumLocalByteUninit m localId b) :
    EnumLocalByteUninit
      { m with stack := ⟨#[{ topFrame with location := loc }]⟩ }
      localId b := by
  intro tf' mp c allocId borTag localAlloc hf' hloc' hprov hfind
  injection hf' with hf_arr
  injection hf_arr with htf_eq
  subst htf_eq
  exact h topFrame mp c allocId borTag localAlloc hframes hloc' hprov hfind

/-- Local `j` holds an immediate (or dead) value in the single active frame of
`m`, lifted to `AnnealStepState` for multi-step symbolic composition. -/
def IsImmediateStepLocal (m : AnnealStepState) (j : Nat) : Prop :=
  ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf j

theorem IsImmediateStepLocal.of_cache_layout {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx : Nat} {hlt : idx < topFrame.locals.size}
    {lay : Miri.Interpreter.LocalLayout} {j : Nat}
    (hframes : m.stack.frames = #[topFrame])
    (h : IsImmediateStepLocal m j) :
    IsImmediateStepLocal
      { m with stack := ⟨#[cacheFrameLocalLayout topFrame idx hlt lay]⟩ } j := by
  intro tf' hf'
  injection hf' with ha; injection ha with htf; subst htf
  exact (h topFrame hframes).cache_layout hlt lay

theorem IsImmediateStepLocal.of_set_location {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {loc : Miri.Interpreter.FrameLocation} {j : Nat}
    (hframes : m.stack.frames = #[topFrame])
    (h : IsImmediateStepLocal m j) :
    IsImmediateStepLocal
      { m with stack := ⟨#[{ topFrame with location := loc }]⟩ } j := by
  intro tf' hf'
  injection hf' with ha; injection ha with htf; subst htf
  exact h topFrame hframes

theorem IsImmediateStepLocal.of_write_immediate {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Nat} {hlt : dstIdx < topFrame.locals.size}
    {imm : Miri.Interpreter.Immediate AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout} {j : Nat}
    (hframes : m.stack.frames = #[topFrame])
    (h : IsImmediateStepLocal m j) :
    IsImmediateStepLocal
      { m with
        stack := ⟨#[{ topFrame with
          locals := topFrame.locals.set dstIdx ⟨.live (.immediate imm), lay⟩ hlt }]⟩ }
      j := by
  intro tf' hf' mls hmls mp hv
  injection hf' with ha; injection ha with htf; subst htf
  dsimp at hmls
  by_cases hj : dstIdx = j
  · subst hj
    rw [Array.getElem?_set_self hlt] at hmls
    injection hmls with hm; subst hm; cases hv
  · simp only [Array.getElem?_set, hj, ↓reduceIte] at hmls
    exact h topFrame hframes mls hmls mp hv

theorem write_after_rvalue_step_LM2_3
    {PlaceTy : Type}
    (H : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit PlaceTy)
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    {tf₀ topFrame₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Local} {dstDecl : LocalDecl}
    {val : Value} {imm : Miri.Interpreter.Immediate AnnealProv}
    {id0 : Miri.Interpreter.LocalsIdentity}
    {bb : BasicBlockData} {stmt : Statement}
    (hretCont : topFrame₁.returnContinuation = .stop false)
    (hretPlace :
      ∃ retLay,
        topFrame₁.returnPlace = .frameLocal 0 0 none retLay topFrame₁.localsIdentity)
    (halloc : AllocIdSupplyValid allocBudget m.machine.memory)
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
    (hframe₁ : FrameRelLM2_3 body env m.machine s.frame topFrame₁)
    (hdisj : MemoryAllocDisjoint topFrame₁)
    (hdecl : get? body.localDecls dstIdx = some dstDecl)
    (henv_dst : env dstDecl.ty = none)
    (himm_dst : IsImmediateFrameLocal topFrame₁ dstIdx)
    (himmRel : ImmediateRel dstDecl.ty body.layouts val imm)
    (heval_m : Miri.Interpreter.Step.evalStatement H () (translateStmt stmt) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediateLM2_2 imm
          ⟨.local 0 dstIdx none id0, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[topFrame₁]⟩ }) :
    StepRelLM2_3 body env allocBudget m
      (match get? s.frame.locals dstIdx with
      | .some .dead => MirStepNode.fail .ub
      | .some _ =>
        match set? s.frame.locals dstIdx (.init val) with
        | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
        | .none => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub)
      (Miri.Interpreter.Step.step H () m) ∧
    (∀ localId b, localId ≠ dstIdx →
      EnumLocalByteUninit { m with stack := ⟨#[topFrame₁]⟩ } localId b →
      EnumLocalByteUninit (Miri.Interpreter.Step.step H () m).1 localId b) ∧
    (∀ j,
      IsImmediateStepLocal { m with stack := ⟨#[topFrame₁]⟩ } j →
      IsImmediateStepLocal (Miri.Interpreter.Step.step H () m).1 j) := by
  obtain ⟨slot_d, mls_d, hlt_mf, hslot_d, hmls_eq, hloc_d⟩ :=
    hframe₁.lookup_local hdecl
  have hlt_af : dstIdx < s.frame.locals.length := by
    have hs := hslot_d
    unfold get? at hs
    exact (List.getElem?_eq_some_iff.mp hs).1
  have hmls_d : topFrame₁.locals[dstIdx]? = some mls_d := by
    rw [Array.getElem?_eq_getElem hlt_mf, hmls_eq]
  have hget_d := frame_getLocal_of_getElem? topFrame₁ dstIdx mls_d hmls_d
  have himm_d := himm_dst mls_d hmls_d
  have hloc_base := hloc_d.to_localRel_of_none henv_dst
  rw [hslot_d]
  rcases mls_d with ⟨vd, cd⟩
  cases vd with
  | live op =>
    cases op with
    | indirect mp => exact False.elim (himm_d mp rfl)
    | immediate imm_old =>
      obtain ⟨_, hval⟩ := hloc_base.immediate_cases
      have hc := hloc_base.cachedLayout_eq
      have hset_af :
          set? s.frame.locals dstIdx (.init val) =
            some (s.frame.locals.set dstIdx (.init val)) :=
        set?_eq_some_set hlt_af (.init val)
      have hnot_dead' : (match some slot_d with
          | .some .dead => MirStepNode.fail .ub
          | .some _ =>
            match set? s.frame.locals dstIdx (.init val) with
            | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
            | .none => MirStepNode.fail .ub
          | .none => MirStepNode.fail .ub) =
          MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx (.init val)) s.memory) := by
        rcases hval with ⟨rfl, _⟩ | ⟨_, rfl, _⟩ <;> simp [hset_af]
      rw [hnot_dead']
      let topFrame₂ :=
        { topFrame₁ with
          locals := topFrame₁.locals.set dstIdx
            { topFrame₁.locals[dstIdx]'hlt_mf with value := .live (.immediate imm) } hlt_mf }
      have hm_ok : Miri.Interpreter.Step.evalStatement H () (translateStmt stmt) m =
          ({ m with stack := ⟨#[topFrame₂]⟩ }, .ok ()) := by
        rw [heval_m]
        unfold Miri.Interpreter.runRvalue
        rw [annealWriteImmediateLM2_2_live (topFrame := topFrame₁) rfl hlt_mf hget_d]
      have hloc₁ : topFrame₂.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ :=
        hframe₁.location_eq
      rw [miri_step_at_statement_ok _ hframes hbody₀ hloc₀ hbb hstmt hm_ok rfl hloc₁]
      refine ⟨?_, ?_, ?_⟩
      · apply StepRelLM2_3.step
        have hloc_new : LocalRelLM2_3 env m.machine dstDecl body.layouts (.init val)
            { topFrame₁.locals[dstIdx]'hlt_mf with value := .live (.immediate imm) } := by
          rw [hmls_eq]
          exact .base _ _ henv_dst
            (.immediate (.init val) imm cd hc (Or.inr ⟨val, rfl, himmRel⟩))
        have hfr₂ := hframe₁.update_local hdecl hset_af hlt_mf hloc_new
        obtain ⟨retLay, hretP⟩ := hretPlace
        exact StateRelLM2_3.mk
          { topFrame₂ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
          rfl hretCont ⟨retLay, hretP⟩
          hfr₂.step_pc halloc hcal hstack hbor hprot hcaller
          (by
            apply MemoryAllocDisjoint.mono_immediate hdisj
            intro k
            by_cases hk : k = dstIdx
            · subst hk
              right
              exists imm, (topFrame₁.locals[k]'hlt_mf).layout
              dsimp [topFrame₂]
              rw [Array.getElem?_set_self hlt_mf]
            · left
              dsimp [topFrame₂]
              rw [Array.getElem?_set_ne _ (Ne.symm hk)])
      · intro localId b hne hu
        have hu₁ : EnumLocalByteUninit { m with stack := ⟨#[topFrame₂]⟩ } localId b :=
          EnumLocalByteUninit.of_replace_other
            (m := { m with stack := ⟨#[topFrame₁]⟩ }) (Ne.symm hne) rfl hu
        exact EnumLocalByteUninit.of_set_location
          (m := { m with stack := ⟨#[topFrame₂]⟩ }) rfl hu₁
      · intro j hj
        have hj₂ : IsImmediateStepLocal { m with stack := ⟨#[topFrame₂]⟩ } j :=
          IsImmediateStepLocal.of_write_immediate (m := { m with stack := ⟨#[topFrame₁]⟩ }) rfl hj
        exact IsImmediateStepLocal.of_set_location
          (m := { m with stack := ⟨#[topFrame₂]⟩ }) rfl hj₂
  | dead =>
    cases hloc_base with
    | dead _ _ =>
      have hm_err : Miri.Interpreter.Step.evalStatement H () (translateStmt stmt) m =
          ({ m with stack := ⟨#[topFrame₁]⟩ },
            .error (.undefinedBehavior "write to dead local")) := by
        rw [heval_m]
        unfold Miri.Interpreter.runRvalue
        rw [annealWriteImmediateLM2_2_dead (topFrame := topFrame₁) rfl hget_d]
      rw [miri_step_at_statement_error _ hframes hbody₀ hloc₀ hbb hstmt hm_err]
      exact ⟨.ub _ _, (fun _ _ _ hu => hu), (fun _ hj => hj)⟩

/-- `StateRelLM2_3` counterpart of `write_after_rvalue_simulation_ext`: once an
rvalue evaluates to `val` / `imm`
(`ImmediateRel dstDecl.ty body.layouts val imm`) at intermediate frame
`topFrame₁`, writing `imm` into immediate scalar local `dstIdx`
(`env dstDecl.ty = none`) steps both machines in lockstep (`.step` on live
`dstIdx`, `.ub` on `.dead` `dstIdx`), preserves `EnumLocalByteUninit` on every
`localId ≠ dstIdx`, and preserves `IsImmediateStepLocal` on all locals. -/
theorem write_after_rvalue_simulation_LM2_3
    {PlaceTy : Type}
    (H : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit PlaceTy)
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    {tf₀ topFrame₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Local} {dstDecl : LocalDecl}
    {val : Value} {imm : Miri.Interpreter.Immediate AnnealProv}
    {id0 : Miri.Interpreter.LocalsIdentity}
    {bb : BasicBlockData} {stmt : Statement}
    (hretCont : topFrame₁.returnContinuation = .stop false)
    (hretPlace :
      ∃ retLay,
        topFrame₁.returnPlace = .frameLocal 0 0 none retLay topFrame₁.localsIdentity)
    (halloc : AllocIdSupplyValid allocBudget m.machine.memory)
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
    (hframe₁ : FrameRelLM2_3 body env m.machine s.frame topFrame₁)
    (hdisj : MemoryAllocDisjoint topFrame₁)
    (hdecl : get? body.localDecls dstIdx = some dstDecl)
    (henv_dst : env dstDecl.ty = none)
    (himm_dst : IsImmediateFrameLocal topFrame₁ dstIdx)
    (himmRel : ImmediateRel dstDecl.ty body.layouts val imm)
    (heval_a : evalStmt s stmt body.localDecls body.layouts =
      match get? s.frame.locals dstIdx with
      | .some .dead => MirStepNode.fail .ub
      | .some _ =>
        match set? s.frame.locals dstIdx (.init val) with
        | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
        | .none => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub)
    (heval_m : Miri.Interpreter.Step.evalStatement H () (translateStmt stmt) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediateLM2_2 imm
          ⟨.local 0 dstIdx none id0, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[topFrame₁]⟩ }) :
    StepRelLM2_3 body env allocBudget m
      (evalStmt s stmt body.localDecls body.layouts)
      (Miri.Interpreter.Step.step H () m) ∧
    (∀ localId b, localId ≠ dstIdx →
      EnumLocalByteUninit { m with stack := ⟨#[topFrame₁]⟩ } localId b →
      EnumLocalByteUninit (Miri.Interpreter.Step.step H () m).1 localId b) ∧
    (∀ j,
      IsImmediateStepLocal { m with stack := ⟨#[topFrame₁]⟩ } j →
      IsImmediateStepLocal (Miri.Interpreter.Step.step H () m).1 j) := by
  rw [heval_a]
  exact write_after_rvalue_step_LM2_3 H hretCont hretPlace halloc hcal hstack hbor hprot hcaller
    hframes hbody₀ hloc₀ hbb hstmt hframe₁ hdisj hdecl henv_dst himm_dst himmRel heval_m

/-- Primitive scalar operand predicate for enum aggregate construction and
`SwitchInt` discriminant operands in `LM-2.3`: either a canonical scalar
constant or a `copy _idx` of a non-address-taken primitive scalar local. -/
inductive WellTypedEnumScalarOp
    (body : CapturedMir)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    MirAst.Operand → Ty → Prop where
  | constScalar (c : ConstOperand) (sc : MirAst.ScalarInt) :
      c.val = .scalar (.int sc) →
      IsPrimScalarTy c.ty →
      ValidScalarBytes sc.sizeBytes →
      sc.bits < scalarModulus sc.sizeBytes →
      (translateTy c.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes →
      (c.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) →
      (c.ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) →
      WellTypedEnumScalarOp body topFrame (.constant c) c.ty
  | copyLocal (idx : Local) (decl : LocalDecl) :
      get? body.localDecls idx = some decl →
      IsPrimScalarTy decl.ty →
      IsImmediateFrameLocal topFrame idx →
      WellTypedEnumScalarOp body topFrame (.copy ⟨idx, .nil⟩) decl.ty

namespace WellTypedEnumScalarOp

theorem isPrimScalarTy {body : CapturedMir}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : MirAst.Operand} {ty : Ty}
    (h : WellTypedEnumScalarOp body tf op ty) :
    IsPrimScalarTy ty := by
  cases h with
  | constScalar _ _ _ hp _ _ _ _ _ => exact hp
  | copyLocal _ _ _ hp _ => exact hp

theorem mono_immediate {body : CapturedMir}
    {tf tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : MirAst.Operand} {ty : Ty}
    (h : WellTypedEnumScalarOp body tf op ty)
    (hmono : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) :
    WellTypedEnumScalarOp body tf' op ty := by
  cases h with
  | constScalar c sc hv hp hsz hcan hl hb hc =>
    exact .constScalar c sc hv hp hsz hcan hl hb hc
  | copyLocal idx decl hd hp himm =>
    exact .copyLocal idx decl hd hp (hmono idx himm)

theorem lm23Operand_false {body : CapturedMir}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : MirAst.Operand} {ty : Ty}
    (h : WellTypedEnumScalarOp body tf op ty) :
    lm23Operand (translateOperand op) = false := by
  cases h <;> rfl

theorem miriOperandLayout_eq {body : CapturedMir}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : MirAst.Operand} {ty : Ty}
    (h : WellTypedEnumScalarOp body tf op ty) :
    miriOperandLayout body.localDecls body.layouts (translateOperand op) =
      some (translateTy ty body.layouts) := by
  cases h with
  | constScalar c sc hv hp _ _ _ _ _ =>
    unfold translateOperand translateConstOperand miriOperandLayout
    dsimp only
    rw [hv]
    dsimp [translateConstValue]
    exact congrArg some hp.layoutOfEncoded
  | copyLocal idx decl hd _ _ =>
    unfold translateOperand translatePlace miriOperandLayout lookupLocalDeclLayout
    simp [hd]

end WellTypedEnumScalarOp

/-- Joint evaluation of a `WellTypedEnumScalarOp` in Anneal's `evalOperand` and
`lean-miri`'s `annealEvalOperandLM2_3 >>= annealReadImmediateLM2_2` on a
`FrameRelLM2_3`-related frame: either both produce a `ScalarRel`-related scalar
while preserving `FrameRelLM2_3`, `MemoryAllocDisjoint`,
`IsImmediateFrameLocal`, and `EnumLocalByteUninit`, or both diagnose `.ub` (on
`.dead` or `.uninit`). -/
theorem evalEnumScalarOp_lm2_3
    {body : CapturedMir} {env : EnumTypeEnv} {af : StackFrame}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {m : AnnealStepState} {op : MirAst.Operand} {ty : Ty}
    (henv_valid : ∀ t tb vs, env t = some (tb, vs) → ValidEnumLayout t body.layouts tb vs)
    (hframes : m.stack.frames = #[topFrame])
    (hframe : FrameRelLM2_3 body env m.machine af topFrame)
    (hop : WellTypedEnumScalarOp body topFrame op ty)
    (globals : List CapturedAllocation)
    (known : Option Miri.Interpreter.LocalLayout) :
    (∃ (sc : MirAst.ScalarInt) (msc : Miri.Memory.ScalarInt)
        (topFrame' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      evalOperand af.locals op .nil globals body.layouts .nil =
        .ok (.scalar sc) af.locals ∧
      (annealEvalOperandLM2_3 body.localDecls body.layouts (translateOperand op) known >>=
        annealReadImmediateLM2_2) m =
        .ok ⟨.scalar (.fromScalarInt msc), translateTy ty body.layouts⟩
          { m with stack := ⟨#[topFrame']⟩ } ∧
      ScalarRel sc msc ∧
      (translateTy ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes ∧
      (ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) ∧
      (ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) ∧
      FrameRelLM2_3 body env m.machine af topFrame' ∧
      topFrame' = { topFrame with locals := topFrame'.locals } ∧
      (∀ (j : Nat), (topFrame'.locals[j]?).map Miri.Interpreter.LocalState.value =
        (topFrame.locals[j]?).map Miri.Interpreter.LocalState.value) ∧
      (∀ (j : Nat), IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame' j) ∧
      (MemoryAllocDisjoint topFrame → MemoryAllocDisjoint topFrame') ∧
      (∀ localId b, EnumLocalByteUninit m localId b →
        EnumLocalByteUninit { m with stack := ⟨#[topFrame']⟩ } localId b)) ∨
    (∃ m' msg,
      evalOperand af.locals op .nil globals body.layouts .nil = .ub ∧
      (annealEvalOperandLM2_3 body.localDecls body.layouts (translateOperand op) known >>=
        annealReadImmediateLM2_2) m = .error (.undefinedBehavior msg) m') := by
  have hsame : { m with stack := ⟨#[topFrame]⟩ } = m :=
    stepState_with_same_singleton m topFrame hframes
  cases hop with
  | constScalar c sc hval hprim hsz hcan hlaysz hbool hchar =>
    obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hsz hcan
    have heval_a : evalOperand af.locals (.constant c) .nil globals body.layouts .nil =
        .ok (.scalar sc) af.locals := by
      unfold evalOperand; dsimp only; rw [hval]; rfl
    have heval_m :
        annealEvalOperandLM2_3 body.localDecls body.layouts
          (translateOperand (.constant c)) known m =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩ m := by
      with_unfolding_all
        unfold annealEvalOperandLM2_3 translateOperand translateConstOperand
          annealEvalOperand evalMirConstImmediate
        dsimp only
        rw [hval]
        simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
          EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
          stack_currentFrame?_singleton m.stack topFrame hframes, Option.isNone_some,
          Bool.false_eq_true, ↓reduceIte, htry, hprim.layoutOfEncoded]
    left
    refine ⟨sc, msc, topFrame, heval_a, ?_, hrel, hlaysz, hbool, hchar,
      hframe, rfl, (fun _ => rfl), (fun _ h => h), (fun h => h),
      (fun _ _ hu => by rw [hsame]; exact hu)⟩
    rw [EStateM.bind_eq_ok heval_m, hsame]
    rfl
  | copyLocal idx decl hdecl hprim himm =>
    obtain ⟨slot, mls, hlt_mf, hslot, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
    have hnone := env_none_of_isPrimScalarTy henv_valid hprim
    have hloc_base := hloc.to_localRel_of_none hnone
    have hcache := hloc_base.layout_eq
    have hmls_get : topFrame.locals[idx]? = some mls := by
      rw [Array.getElem?_eq_getElem hlt_mf, hmls_eq]
    have himm' := himm mls hmls_get
    have hlm_eq :
        annealEvalOperandLM2_3 body.localDecls body.layouts
          (translateOperand (.copy ⟨idx, .nil⟩)) known =
        annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩) known := rfl
    rw [hlm_eq]
    cases hloc_base with
    | dead cachedLayout _ =>
      right
      have herr := rvalueM_bind_err (f := annealReadImmediateLM2_2)
        (annealEvalOperand_copy_dead (known := known) hframes hlt_mf hdecl hmls_eq hcache)
      exact ⟨_, "read of dead local", by simp [evalOperand, hslot], herr⟩
    | indirect _ mp _ _ _ _ =>
      exact False.elim (himm' mp rfl)
    | immediate _ imm cachedLayout _ hval =>
      let topFrame' :=
        cacheFrameLocalLayout topFrame idx hlt_mf (translateTy decl.ty body.layouts)
      rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
      · right
        have herr :
            (annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩) known >>=
              annealReadImmediateLM2_2) m =
            .error (.undefinedBehavior "read of uninitialized local")
              { m with stack := ⟨#[topFrame']⟩ } := by
          rw [EStateM.bind_eq_ok
            (annealEvalOperand_copy_live hframes hlt_mf hdecl hmls_eq hcache)]
          rfl
        exact ⟨_, "read of uninitialized local", by simp [evalOperand, hslot], herr⟩
      · obtain ⟨sc, msc, rfl, rfl, hrel, hlaysz, hbool, hchar⟩ :=
          himmRel.of_primitive_scalar hprim
        left
        refine ⟨sc, msc, topFrame', ?_, ?_, hrel, hlaysz, hbool, hchar,
          hframe.cache_local_layout hdecl hlt_mf, rfl, ?_, ?_,
          (fun hd => MemoryAllocDisjoint_cacheFrameLocalLayout hd hlt_mf _),
          (fun _ _ hu => EnumLocalByteUninit.of_cache_layout hframes hu)⟩
        · simp [evalOperand, hslot, readProjectedValue]
        · rw [EStateM.bind_eq_ok
            (annealEvalOperand_copy_live hframes hlt_mf hdecl hmls_eq hcache)]
          rfl
        · intro j
          by_cases hj : j = idx
          · subst hj
            dsimp [topFrame', cacheFrameLocalLayout]
            rw [Array.getElem?_set_self hlt_mf, Array.getElem?_eq_getElem hlt_mf]
            rfl
          · dsimp [topFrame', cacheFrameLocalLayout]
            rw [Array.getElem?_set_ne _ (Ne.symm hj)]
        · intro j hj
          exact hj.cache_layout hlt_mf (translateTy decl.ty body.layouts)

/-! ## 4. `PlaceElem.Downcast` + `PlaceElem.Field` (`LM-2.3` Deliverable 4) -/

/-- `downcastEnumLayout` on variant `v < variants.length` of a `ValidEnumLayout`
installs `variants[v]`'s field offsets while preserving byte size and
sizedness. -/
theorem downcastEnumLayout_ok
    {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)} {v : Nat}
    (hvalid : ValidEnumLayout ty layouts tagBytes variants)
    (hv : v < variants.length) :
    ∃ varLay : Miri.Interpreter.LocalLayout,
      downcastEnumLayout (translateTy ty layouts) v = .ok varLay ∧
      varLay.ty = (translateTy ty layouts).ty ∧
      varLay.layout.size = (translateTy ty layouts).layout.size ∧
      varLay.layout.isSized = true ∧
      varLay.layout.backendRepr = .Memory (sized := true) ∧
      varLay.layout.uninhabited = false ∧
      ∀ i (hi : i < (variants[v]'hv).length),
        varLay.layout.fields.offset i = .ok ((variants[v]'hv)[i]'hi).offset := by
  obtain ⟨_, _, _, _, _, _, _, _, _, vars, hsz, hvars, hvf_all⟩ := hvalid.table_entry
  have hv_arr : v < vars.size := by omega
  have hvf := hvf_all v hv
  have hget? : vars[v]? = some (vars[v]'hv_arr) := Array.getElem?_eq_getElem hv_arr
  unfold downcastEnumLayout
  rw [hvars]
  dsimp only
  rw [hget?]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, hvf.vl_inhabited, ?_⟩
  intro i hi
  dsimp [Miri.ABI.FieldsShape.offset, Miri.ABI.FieldsShape.count]
  rw [hvf.vl_offsets_eq]
  have hnot_le : ¬ (variants[v]'hv).length ≤ i := Nat.not_le_of_gt hi
  have hget_v : (variants[v]'hv)[i]? = some ((variants[v]'hv)[i]'hi) :=
    List.getElem?_eq_getElem hi
  simp [hnot_le, hget_v, pure, Except.pure]

/-- `Miri.Interpreter.projectDowncast` under `annealEnumProjectionCx` on a thin
`.indirect mp` enum operand shifts by `0` bytes (`mp` unchanged) and installs
`varLay`. -/
theorem projectDowncast_enum_indirect_ok
    {layouts : LayoutTable} {hintTy : Option Miri.MIR.TyId}
    {enumLay varLay : Miri.Interpreter.LocalLayout}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {v : Nat}
    (hmeta : mp.metadata = .none)
    (hdown : downcastEnumLayout enumLay v = .ok varLay)
    (hsized : varLay.layout.isSized = true) :
    Miri.Interpreter.projectDowncast (annealEnumProjectionCx layouts hintTy)
        ⟨.indirect mp, enumLay⟩ v =
      .ok ⟨.indirect mp, varLay⟩ := by
  have hadd0 : mp.ptr.offset.add Miri.ABI.Size.ZERO = .ok mp.ptr.offset := by
    obtain ⟨ha, _⟩ := size_add_of_no_overflow (a := mp.ptr.offset) (b := Miri.ABI.Size.ZERO)
      (by dsimp [Miri.ABI.Size.ZERO]; exact mp.ptr.offset.bytes.toNat_lt)
    rw [ha]; dsimp [Miri.ABI.Size.ZERO]; rw [UInt64.add_zero]
    cases mp.ptr.offset; rfl
  have hmp_eq : { mp with ptr := { mp.ptr with offset := mp.ptr.offset }, metadata := .none } = mp := by
    rcases mp with ⟨⟨off, prov⟩, meta_, mis⟩
    dsimp at hmeta; subst hmeta; rfl
  unfold Miri.Interpreter.projectDowncast Miri.Interpreter.OpTy.offset
    Miri.Interpreter.OpTy.offsetWithMeta annealEnumProjectionCx annealStructProjectionCx
    Miri.Interpreter.OpTy.metadata
  simp [hmeta, Miri.Interpreter.MemPlaceMeta.hasMeta, hdown, hsized, hadd0, hmp_eq,
    Except.mapError, bind, Except.bind, pure, Except.pure]

/-- `Miri.Interpreter.projectDowncast` under `annealEnumProjectionCx` on an
`.immediate .uninit` enum operand evaluates to `.immediate .uninit` at
`varLay`. -/
theorem projectDowncast_enum_uninit_ok
    {layouts : LayoutTable} {hintTy : Option Miri.MIR.TyId}
    {enumLay varLay : Miri.Interpreter.LocalLayout}
    {v : Nat}
    (hdown : downcastEnumLayout enumLay v = .ok varLay)
    (hsized : varLay.layout.isSized = true)
    (hsz_eq : varLay.layout.size = enumLay.layout.size) :
    Miri.Interpreter.projectDowncast (annealEnumProjectionCx layouts hintTy)
        ⟨.immediate .uninit, enumLay⟩ v =
      .ok ⟨.immediate .uninit, varLay⟩ := by
  have hadd0 : Miri.ABI.Size.ZERO.add varLay.layout.size = .ok varLay.layout.size := by
    obtain ⟨ha, _⟩ := size_add_of_no_overflow (a := Miri.ABI.Size.ZERO) (b := varLay.layout.size)
      (by dsimp [Miri.ABI.Size.ZERO]; rw [Nat.zero_add]; exact varLay.layout.size.bytes.toNat_lt)
    rw [ha]; dsimp [Miri.ABI.Size.ZERO]; rw [UInt64.zero_add]
    cases varLay.layout.size; rfl
  have hnot_gt : ¬ (varLay.layout.size.bytes > enumLay.layout.size.bytes) := by
    rw [hsz_eq]; exact Nat.lt_irrefl _
  unfold Miri.Interpreter.projectDowncast Miri.Interpreter.OpTy.offset
    Miri.Interpreter.OpTy.offsetWithMeta annealEnumProjectionCx annealStructProjectionCx
    Miri.Interpreter.projectionImmediateOffset Miri.Interpreter.OpTy.metadata
  simp [Miri.Interpreter.MemPlaceMeta.hasMeta, hdown, hsized, hadd0, hnot_gt,
    Except.mapError, bind, Except.bind, pure, Except.pure]

/-- Two-step `annealEvalEnumProjection` for
`[.Downcast vName v, .Field i (encodeTyId fty)]` on a thin `.indirect mp` enum
operand. -/
theorem annealEvalEnumProjection_downcast_field_indirect_ok
    {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {vName : Option String} {v i : Nat} {fty : Ty}
    (hvalid : ValidEnumLayout ty layouts tagBytes variants)
    (hv : v < variants.length)
    (hi : i < (variants[v]'hv).length)
    (hfty : fty = ((variants[v]'hv)[i]'hi).ty)
    (hmeta : mp.metadata = .none)
    (hno_ovf : mp.ptr.offset.bytes.toNat +
      (translateTy ty layouts).layout.size.bytes.toNat < 2 ^ 64)
    (m : AnnealStepState) :
    annealEvalEnumProjection layouts ⟨.indirect mp, translateTy ty layouts⟩
        [.Downcast vName v, .Field i (encodeTyId fty)] m =
      .ok ⟨.indirect
            ⟨⟨Miri.ABI.Size.ofBytes
                (mp.ptr.offset.bytes + ((variants[v]'hv)[i]'hi).offset.bytes),
              mp.ptr.provenance⟩,
              .none, mp.misaligned⟩,
            translateTy fty layouts⟩ m := by
  obtain ⟨varLay, hdown, _, hsz_eq, hsized_var, _, _, hoff_all⟩ :=
    downcastEnumLayout_ok hvalid hv
  obtain ⟨_, _, _, _, _, _, _, _, _, vars, _, _, hvf_all⟩ := hvalid.table_entry
  have hvf := hvf_all v hv
  obtain ⟨hprim_f, hfl_f⟩ := hvf.fields_prim i hi
  rw [← hfty] at hprim_f
  obtain ⟨hrt_f, hsized_f, _⟩ := hprim_f.layout_props (layouts := layouts)
  have hbnd_f := hvf.fields_in_bounds i hi
  have hoff_i := hoff_all i hi
  have hstep1 :
      Miri.Interpreter.project (annealEnumProjectionCx layouts none)
        ⟨.indirect mp, translateTy ty layouts⟩ (.Downcast vName v) =
      .ok ⟨.indirect mp, varLay⟩ :=
    projectDowncast_enum_indirect_ok hmeta hdown hsized_var
  have hstep2 :
      Miri.Interpreter.project (annealEnumProjectionCx layouts (some (encodeTyId fty)))
        ⟨.indirect mp, varLay⟩ (.Field i (encodeTyId fty)) =
      .ok ⟨.indirect
            ⟨⟨Miri.ABI.Size.ofBytes
                (mp.ptr.offset.bytes + ((variants[v]'hv)[i]'hi).offset.bytes),
              mp.ptr.provenance⟩,
              .none, mp.misaligned⟩,
            translateTy fty layouts⟩ := by
    have hpf := projectField_indirect_eq (layouts := layouts) (baseLay := varLay)
      (mp := mp) (idx := i) (fty := fty) (off := ((variants[v]'hv)[i]'hi).offset)
      hrt_f hoff_i hsized_f (by omega)
    unfold Miri.Interpreter.project Miri.Interpreter.projectField
      Miri.Interpreter.OpTy.offsetWithMeta annealEnumProjectionCx at *
    exact hpf
  unfold annealEvalEnumProjection
  dsimp only
  rw [hstep1]
  simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  unfold annealEvalEnumProjection
  dsimp only
  rw [hstep2]
  simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  rfl

/-- Two-step `annealEvalEnumProjection` for
`[.Downcast vName v, .Field i (encodeTyId fty)]` on an `.immediate .uninit` enum
operand. -/
theorem annealEvalEnumProjection_downcast_field_uninit_ok
    {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)}
    {vName : Option String} {v i : Nat} {fty : Ty}
    (hvalid : ValidEnumLayout ty layouts tagBytes variants)
    (hv : v < variants.length)
    (hi : i < (variants[v]'hv).length)
    (hfty : fty = ((variants[v]'hv)[i]'hi).ty)
    (m : AnnealStepState) :
    annealEvalEnumProjection layouts ⟨.immediate .uninit, translateTy ty layouts⟩
        [.Downcast vName v, .Field i (encodeTyId fty)] m =
      .ok ⟨.immediate .uninit, translateTy fty layouts⟩ m := by
  obtain ⟨varLay, hdown, _, hsz_eq, hsized_var, _, _, hoff_all⟩ :=
    downcastEnumLayout_ok hvalid hv
  obtain ⟨_, _, _, _, _, _, _, _, _, vars, _, _, hvf_all⟩ := hvalid.table_entry
  have hvf := hvf_all v hv
  obtain ⟨hprim_f, hfl_f⟩ := hvf.fields_prim i hi
  rw [← hfty] at hprim_f
  obtain ⟨hrt_f, hsized_f, _⟩ := hprim_f.layout_props (layouts := layouts)
  have hbnd_f :
      ((variants[v]'hv)[i]'hi).offset.bytes.toNat +
        (translateTy fty layouts).layout.size.bytes.toNat ≤
        varLay.layout.size.bytes.toNat := by
    rw [hsz_eq, hfty, ← hfl_f]
    exact hvf.fields_in_bounds i hi
  have hoff_i := hoff_all i hi
  have hstep1 :
      Miri.Interpreter.project (annealEnumProjectionCx layouts none)
        ⟨.immediate .uninit, translateTy ty layouts⟩ (.Downcast vName v) =
      .ok ⟨.immediate .uninit, varLay⟩ :=
    projectDowncast_enum_uninit_ok hdown hsized_var hsz_eq
  have hstep2 :
      Miri.Interpreter.project (annealEnumProjectionCx layouts (some (encodeTyId fty)))
        ⟨.immediate .uninit, varLay⟩ (.Field i (encodeTyId fty)) =
      .ok ⟨.immediate .uninit, translateTy fty layouts⟩ := by
    have hpf := projectField_immediate_uninit_eq (layouts := layouts) (baseLay := varLay)
      (idx := i) (fty := fty) (off := ((variants[v]'hv)[i]'hi).offset)
      hrt_f hoff_i hsized_f hbnd_f
    unfold Miri.Interpreter.project Miri.Interpreter.projectField
      Miri.Interpreter.OpTy.offsetWithMeta annealEnumProjectionCx at *
    exact hpf
  unfold annealEvalEnumProjection
  dsimp only
  rw [hstep1]
  simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  unfold annealEvalEnumProjection
  dsimp only
  rw [hstep2]
  simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  rfl

/-- Primitive scalar destinations never take the memory-to-memory `struct` copy
path (`usesStructMemCopyDest = false`). -/
theorem usesStructMemCopyDest_false_of_primScalar
    {layouts : LayoutTable} (dest : Miri.Interpreter.RuntimePlace AnnealProv) {ty : Ty}
    (hdst : dest.layout = translateTy ty layouts)
    (hprim : IsPrimScalarTy ty) :
    usesStructMemCopyDest dest = false := by
  obtain ⟨_, _, _, _, _, abiSc, hrepr⟩ := hprim.layout_props (layouts := layouts)
  unfold usesStructMemCopyDest
  rw [hdst, hrepr]

/-- **`evalProjection_downcast_field_simulation`** (`LM-2.3` Deliverable 4):
Evaluating `_dst = copy ((_src as variantIdx).fieldIdx)` or
`_dst = move ((_src as variantIdx).fieldIdx)` from a `StateRelLM2_3`-related
state simulates vendored `Miri.Interpreter.project` (`projectDowncast` +
`projectField`) + `annealReadImmediateLM2_2` + `annealWriteImmediateLM2_2` in lockstep:
* `.dead` `_src` → `StepRelLM2_3.ub` (`"read of dead local"`);
* `.uninit` `_src` (immediate or indirect) → `StepRelLM2_3.ub`;
* `.init (.aggregate v_act fieldVals)` with `variantIdx = v_act`: if
  `get? fieldVals fieldIdx = some (.scalar sc)`, reads active payload scalar
  `sc` and steps `.step` (or `.ub` if `_dst` is `.dead`); if
  `get? fieldVals fieldIdx = none` (e.g. reading an uninitialized trailing field
  after `SetDiscriminant` switched from a narrower variant to a wider variant),
  both Anneal and `lean-miri` step to `StepRelLM2_3.ub`, preserving
  `EnumLocalByteUninit` on all `enumId ≠ dstIdx`;
* `.init (.aggregate v_act fieldVals)` with `variantIdx ≠ v_act` (inactive
  variant whose target field slice contains an uninitialized byte
  `EnumLocalByteUninit m srcIdx b`): both Anneal and `lean-miri` step to
  `StepRelLM2_3.ub`! -/
theorem evalProjection_downcast_field_simulation
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_3 body env allocBudget s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    (henv_valid : ∀ t tb vs, env t = some (tb, vs) → ValidEnumLayout t body.layouts tb vs)
    {bb : BasicBlockData} {stmt : Statement}
    {dstIdx srcIdx : Local} {dstDecl srcDecl : LocalDecl}
    {isMove : Bool} {vName : Option String} {variantIdx fieldIdx : Nat} {fieldTy : Ty}
    {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hkind : stmt.kind = .assign ⟨dstIdx, .nil⟩
      (.use (if isMove then
        .move ⟨srcIdx, [.downcast vName variantIdx, .field fieldIdx fieldTy]⟩
      else
        .copy ⟨srcIdx, [.downcast vName variantIdx, .field fieldIdx fieldTy]⟩)))
    (hsrc_decl : get? body.localDecls srcIdx = some srcDecl)
    (hdst_decl : get? body.localDecls dstIdx = some dstDecl)
    (henv_src : env srcDecl.ty = some (tagBytes, variants))
    (hv_lt : variantIdx < variants.length)
    (hf_lt : fieldIdx < (variants[variantIdx]'hv_lt).length)
    (hfty_eq : fieldTy = ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).ty)
    (hdst_ty : dstDecl.ty = fieldTy)
    (hdst_imm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx)
    (hinactive_uninit :
      ∀ v_act fieldVals,
        get? s.frame.locals srcIdx = some (.init (.aggregate v_act fieldVals)) →
        variantIdx ≠ v_act →
        ∃ b,
          ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).offset.bytes.toNat ≤ b ∧
          b < ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).offset.bytes.toNat +
            ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).fieldLayout.size.bytes.toNat ∧
          EnumLocalByteUninit m srcIdx b) :
    StepRelLM2_3 body env allocBudget m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_3 body.localDecls body.layouts) () m) ∧
    (∀ enumId b, enumId ≠ dstIdx →
      EnumLocalByteUninit m enumId b →
      EnumLocalByteUninit
        (Miri.Interpreter.Step.step (annealStepHooksLM2_3 body.localDecls body.layouts) () m).1
        enumId b) ∧
    (∀ j,
      IsImmediateStepLocal m j →
      IsImmediateStepLocal
        (Miri.Interpreter.Step.step (annealStepHooksLM2_3 body.localDecls body.layouts) () m).1
        j) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe, halloc,
      hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hvalid_enum := henv_valid srcDecl.ty tagBytes variants henv_src
  obtain ⟨_, _, _, _, _, _, _, _, _, vars, _, _, hvf_all⟩ := hvalid_enum.table_entry
  have hvf := hvf_all variantIdx hv_lt
  obtain ⟨hprim_f, hfl_f⟩ := hvf.fields_prim fieldIdx hf_lt
  have hprim_dst : IsPrimScalarTy dstDecl.ty := by rw [hdst_ty, hfty_eq]; exact hprim_f
  have henv_dst := env_none_of_isPrimScalarTy henv_valid hprim_dst
  -- Step 1: evaluate destination `⟨dstIdx, #[]⟩` (`tf₀` caches `dstIdx`).
  obtain ⟨_, mls_d0, hlt_d, _, hmls_d0_eq, hloc_d0⟩ := hframe.lookup_local hdst_decl
  have hcache_d0 : ∀ l, (topFrame.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d0_eq]; exact hloc_d0.layout_eq
  let tf₀ := cacheFrameLocalLayout topFrame dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  let m₀ : AnnealStepState := { m with stack := ⟨#[tf₀]⟩ }
  have heval_dst := annealEvalPlace_unprojected hframes hlt_d hdst_decl hcache_d0
  have hframe₀ := hframe.cache_local_layout hdst_decl hlt_d
  have hdisj₀ := MemoryAllocDisjoint_cacheFrameLocalLayout hdisj hlt_d
    (translateTy dstDecl.ty body.layouts)
  have himm_dst₀ : IsImmediateFrameLocal tf₀ dstIdx :=
    (hdst_imm topFrame hframes).cache_layout hlt_d (translateTy dstDecl.ty body.layouts)
  -- Step 2: lookup `srcIdx` in `tf₀` and cache its layout (`tf₁`).
  obtain ⟨slot_s, mls_s, hlt_s, hslot_s, hmls_s_eq, hloc_s⟩ := hframe₀.lookup_local hsrc_decl
  have hcache_s : ∀ l, (tf₀.locals[srcIdx]'hlt_s).layout = some l →
      l = translateTy srcDecl.ty body.layouts := by
    rw [hmls_s_eq]; exact hloc_s.layout_eq
  let tf₁ := cacheFrameLocalLayout tf₀ srcIdx hlt_s (translateTy srcDecl.ty body.layouts)
  let m₁ : AnnealStepState := { m with stack := ⟨#[tf₁]⟩ }
  have hres_src :
      annealResolveAndCacheLocalLayout body.localDecls body.layouts srcIdx
        (some (translateTy dstDecl.ty body.layouts)) m₀ =
      .ok (tf₁, translateTy srcDecl.ty body.layouts) m₁ :=
    annealResolveAndCacheLocalLayout_eq (m := m₀) rfl hlt_s hsrc_decl hcache_s
  have hframe₁ := hframe₀.cache_local_layout hsrc_decl hlt_s
  have hdisj₁ := MemoryAllocDisjoint_cacheFrameLocalLayout hdisj₀ hlt_s
    (translateTy srcDecl.ty body.layouts)
  have himm_dst₁ : IsImmediateFrameLocal tf₁ dstIdx :=
    himm_dst₀.cache_layout hlt_s (translateTy srcDecl.ty body.layouts)
  -- Common `lm23Assign` and `evalStatement` reduction on `stmt`.
  let projPlace : Place := ⟨srcIdx, [.downcast vName variantIdx, .field fieldIdx fieldTy]⟩
  let useOp : MirAst.Operand := if isMove then .move projPlace else .copy projPlace
  have htr_place :
      translatePlace projPlace =
        ⟨srcIdx, #[.Downcast vName variantIdx, .Field fieldIdx (encodeTyId fieldTy)]⟩ := rfl
  have hlm23_op : lm23Operand (translateOperand useOp) = true := by
    cases isMove <;> rfl
  have hlm23_asgn :
      lm23Assign body.localDecls body.layouts ⟨dstIdx, #[]⟩
        (.Use (translateOperand useOp) .No) = true := by
    unfold lm23Assign; simp [hlm23_op]
  have heval_op_down :
      annealEvalOperandLM2_3 body.localDecls body.layouts (translateOperand useOp)
        (some (translateTy dstDecl.ty body.layouts)) =
      annealEvalDowncastOperand body.localDecls body.layouts
        ⟨srcIdx, #[.Downcast vName variantIdx, .Field fieldIdx (encodeTyId fieldTy)]⟩
        (some (translateTy dstDecl.ty body.layouts)) := by
    cases isMove <;> rfl
  dsimp only [useOp, projPlace] at hlm23_asgn heval_op_down
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
  have hnot_memcopy : usesStructMemCopyDest destPlace = false :=
    usesStructMemCopyDest_false_of_primScalar destPlace rfl hprim_dst
  have hm_base :
      Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_3 body.localDecls body.layouts) () (translateStmt stmt) m =
      Miri.Interpreter.runRvalue
        ((annealEvalDowncastOperand body.localDecls body.layouts
            ⟨srcIdx, #[.Downcast vName variantIdx, .Field fieldIdx (encodeTyId fieldTy)]⟩
            (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediateLM2_2) >>=
          fun r => annealWriteImmediateLM2_2 r.imm destPlace) m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    rw [hkind]
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
      translateRvalue, annealStepHooksLM2_3]
    rw [hlm23_asgn]
    simp only [↓reduceIte]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooksLM2_3
    dsimp only [annealRvalueHooksLM2_2]
    rw [show annealEvalPlaceLM2_3 body.localDecls body.layouts ⟨dstIdx, #[]⟩ =
          annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ from rfl,
      EStateM.bind_eq_ok heval_dst]
    dsimp only
    rw [heval_op_down]
    exact bind_copyOp_eq_of_not_usesStructMemCopyDest hnot_memcopy m₀
  have hget_s1 :
      tf₁.getLocal srcIdx = .ok ⟨mls_s.value, some (translateTy srcDecl.ty body.layouts)⟩ := by
    have hg := cacheFrameLocalLayout_getLocal tf₀ hlt_s (translateTy srcDecl.ty body.layouts)
    rw [hmls_s_eq] at hg
    exact hg
  have hcf₀ := stack_currentFrame?_singleton m₀.stack tf₀ rfl
  have huninit_m₁ : ∀ enumId b, EnumLocalByteUninit m enumId b → EnumLocalByteUninit m₁ enumId b :=
    fun _ _ hu =>
      EnumLocalByteUninit.of_cache_layout (m := m₀) rfl
        (EnumLocalByteUninit.of_cache_layout hframes hu)
  have himm_m₁ : ∀ j, IsImmediateStepLocal m j → IsImmediateStepLocal m₁ j :=
    fun _ hj =>
      IsImmediateStepLocal.of_cache_layout (m := m₀) rfl
        (IsImmediateStepLocal.of_cache_layout hframes hj)
  -- Case-split on `LocalRelLM2_3` for `srcIdx`!
  cases hloc_s with
  | base _ _ hnone _ =>
    rw [henv_src] at hnone; cases hnone
  | enumDead _ _ c_s _ _ _ =>
    have hop_s1 := frame_getLocalOperand_dead tf₁ hget_s1
    have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; rw [hkind]
      cases isMove <;> simp [evalRvalue, evalOperand, hslot_s]
    have hdown_err :
        annealEvalDowncastOperand body.localDecls body.layouts
          ⟨srcIdx, #[.Downcast vName variantIdx, .Field fieldIdx (encodeTyId fieldTy)]⟩
          (some (translateTy dstDecl.ty body.layouts)) m₀ =
        .error (.undefinedBehavior "read of dead local") m₁ := by
      unfold annealEvalDowncastOperand
      simp only [get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
        hcf₀, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, hres_src, hop_s1]
      rfl
    have hm_err :
        Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_3 body.localDecls body.layouts) () (translateStmt stmt) m =
        (m₁, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_base]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_error (EStateM.bind_eq_error hdown_err)]
    rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
    exact ⟨.ub _ _, (fun _ _ _ hu => huninit_m₁ _ _ hu), (fun _ hj => himm_m₁ _ hj)⟩
  | enumUninitImm tb' vs' c_s henv' _ _ =>
    have hop_s1 := frame_getLocalOperand_live tf₁ hget_s1
    rw [henv_src] at henv'; injection henv' with heq_p; rcases heq_p with ⟨rfl, rfl⟩
    have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; rw [hkind]
      cases isMove <;> simp [evalRvalue, evalOperand, hslot_s]
    have hproj_u := annealEvalEnumProjection_downcast_field_uninit_ok
      (vName := vName) hvalid_enum hv_lt hf_lt hfty_eq m₁
    have hdown_ok :
        annealEvalDowncastOperand body.localDecls body.layouts
          ⟨srcIdx, #[.Downcast vName variantIdx, .Field fieldIdx (encodeTyId fieldTy)]⟩
          (some (translateTy dstDecl.ty body.layouts)) m₀ =
        .ok ⟨.immediate .uninit, translateTy fieldTy body.layouts⟩ m₁ := by
      unfold annealEvalDowncastOperand
      simp only [get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
        Pure.pure, EStateM.pure, hcf₀, Option.isNone_some, Bool.false_eq_true, ↓reduceIte,
        hres_src, hop_s1]
      exact hproj_u
    have hm_err :
        Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_3 body.localDecls body.layouts) () (translateStmt stmt) m =
        (m₁, .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_base]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_error (by rw [EStateM.bind_eq_ok hdown_ok]; rfl)]
    rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
    exact ⟨.ub _ _, (fun _ _ _ hu => huninit_m₁ _ _ hu), (fun _ hj => himm_m₁ _ hj)⟩
  | enumUninitInd tb' vs' mp c_s henv' _ hmem_u =>
    have hop_s1 := frame_getLocalOperand_live tf₁ hget_s1
    rw [henv_src] at henv'; injection henv' with heq_p; rcases heq_p with ⟨rfl, rfl⟩
    have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; rw [hkind]
      cases isMove <;> simp [evalRvalue, evalOperand, hslot_s]
    rcases hmem_u with ⟨allocId, borTag, baseAddr, localAlloc, _, hprov, _, hmeta,
      hlive, hbase, hptr, hovf, _, _, _, _, _, hmask_uninit⟩
    have hptr_ovf :
        mp.ptr.offset.bytes.toNat +
          (translateTy srcDecl.ty body.layouts).layout.size.bytes.toNat < 2 ^ 64 := by
      rw [hptr]; dsimp [Miri.ABI.Size.ofBytes]; exact hovf
    have hproj_i := annealEvalEnumProjection_downcast_field_indirect_ok
      (vName := vName) hvalid_enum hv_lt hf_lt hfty_eq hmeta hptr_ovf m₁
    have hdown_ok :
        annealEvalDowncastOperand body.localDecls body.layouts
          ⟨srcIdx, #[.Downcast vName variantIdx, .Field fieldIdx (encodeTyId fieldTy)]⟩
          (some (translateTy dstDecl.ty body.layouts)) m₀ =
        .ok ⟨.indirect
              ⟨⟨Miri.ABI.Size.ofBytes
                  (mp.ptr.offset.bytes +
                    ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).offset.bytes),
                mp.ptr.provenance⟩,
                .none, mp.misaligned⟩,
              translateTy fieldTy body.layouts⟩ m₁ := by
      unfold annealEvalDowncastOperand
      simp only [get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
        Pure.pure, EStateM.pure, hcf₀, Option.isNone_some, Bool.false_eq_true, ↓reduceIte,
        hres_src, hop_s1]
      exact hproj_i
    let fDesc := (variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt
    have hf_inb :
        fDesc.offset.bytes.toNat + fDesc.fieldLayout.size.bytes.toNat ≤
          (translateTy srcDecl.ty body.layouts).layout.size.bytes.toNat :=
      hvf.fields_in_bounds fieldIdx hf_lt
    have hfl_eq : (translateTy fieldTy body.layouts).layout = fDesc.fieldLayout := by
      rw [hfty_eq]; exact hfl_f.symm
    obtain ⟨hend_add, hend_nat⟩ :=
      size_add_of_no_overflow (a := fDesc.offset) (b := (translateTy fieldTy body.layouts).layout.size)
        (by rw [hfl_eq]; have := (translateTy srcDecl.ty body.layouts).layout.size.bytes.toNat_lt; omega)
    have hend_ex :
        (Miri.Memory.allocRange fDesc.offset
          (translateTy fieldTy body.layouts).layout.size).endExclusive =
        .ok (Miri.ABI.Size.ofBytes
          (fDesc.offset.bytes + (translateTy fieldTy body.layouts).layout.size.bytes)) := by
      unfold Miri.Memory.AllocRange.endExclusive Miri.Memory.AllocRange.end Miri.Memory.allocRange
      simp [hend_add, Except.mapError]
    have hinb_u64 :
        (Miri.ABI.Size.ofBytes
          (fDesc.offset.bytes + (translateTy fieldTy body.layouts).layout.size.bytes)).bytes ≤
        (translateTy srcDecl.ty body.layouts).layout.size.bytes := by
      dsimp only [Miri.ABI.Size.ofBytes]
      rw [UInt64.le_iff_toNat_le, hend_nat, hfl_eq]
      exact hf_inb
    have huninit_q :
        localAlloc.allocation.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange fDesc.offset (translateTy fieldTy body.layouts).layout.size) =
        .ok (.error
          (Miri.Memory.allocRange fDesc.offset (translateTy fieldTy body.layouts).layout.size)) := by
      rw [hmask_uninit]
      exact Miri.Memory.InitMask.lazy_uninitialized_query
        (translateTy srcDecl.ty body.layouts).layout.size _ _ hend_ex hinb_u64
    have hprim_fty : IsPrimScalarTy fieldTy := by rw [hfty_eq]; exact hprim_f
    have hptr_f :
        Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + fDesc.offset.bytes) =
        Miri.ABI.Size.ofBytes (baseAddr + fDesc.offset.bytes) := by
      rw [hptr]; rfl
    have hread_err := annealReadIndirectImmediate_scalar_uninit_ub
      (mp := ⟨⟨Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + fDesc.offset.bytes),
        mp.ptr.provenance⟩, .none, mp.misaligned⟩)
      (m := m₁) hprim_fty hprov hbase hptr_f hlive.1 huninit_q
    have hm_err :
        Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_3 body.localDecls body.layouts) () (translateStmt stmt) m =
        (m₁, .error (.undefinedBehavior "read of uninitialized memory field")) := by
      rw [hm_base]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_error (by
        rw [EStateM.bind_eq_ok hdown_ok]; dsimp [annealReadImmediateLM2_2]; exact hread_err)]
    rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
    exact ⟨.ub _ _, (fun _ _ _ hu => huninit_m₁ _ _ hu), (fun _ hj => himm_m₁ _ hj)⟩
  | enumInd tb' vs' v_act fieldVals mp c_s henv' _ hmem_i =>
    have hop_s1 := frame_getLocalOperand_live tf₁ hget_s1
    rw [henv_src] at henv'; injection henv' with heq_p; rcases heq_p with ⟨rfl, rfl⟩
    rcases hmem_i with ⟨allocId, borTag, baseAddr, localAlloc, words, _,
      _, hv_act_lt, hprov, _, hmeta, hlive, hbase, hptr, hovf, _, _,
      hbs_eq, _, _, hmask_rel, _, _, _, _, hpayload⟩
    have hptr_ovf :
        mp.ptr.offset.bytes.toNat +
          (translateTy srcDecl.ty body.layouts).layout.size.bytes.toNat < 2 ^ 64 := by
      rw [hptr]; dsimp [Miri.ABI.Size.ofBytes]; exact hovf
    have hproj_i := annealEvalEnumProjection_downcast_field_indirect_ok
      (vName := vName) hvalid_enum hv_lt hf_lt hfty_eq hmeta hptr_ovf m₁
    have hdown_ok :
        annealEvalDowncastOperand body.localDecls body.layouts
          ⟨srcIdx, #[.Downcast vName variantIdx, .Field fieldIdx (encodeTyId fieldTy)]⟩
          (some (translateTy dstDecl.ty body.layouts)) m₀ =
        .ok ⟨.indirect
              ⟨⟨Miri.ABI.Size.ofBytes
                  (mp.ptr.offset.bytes +
                    ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).offset.bytes),
                mp.ptr.provenance⟩,
                .none, mp.misaligned⟩,
              translateTy fieldTy body.layouts⟩ m₁ := by
      unfold annealEvalDowncastOperand
      simp only [get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
        Pure.pure, EStateM.pure, hcf₀, Option.isNone_some, Bool.false_eq_true, ↓reduceIte,
        hres_src, hop_s1]
      exact hproj_i
    have hprim_fty : IsPrimScalarTy fieldTy := by rw [hfty_eq]; exact hprim_f
    -- Subcase A (`variantIdx = v_act`: active variant read) vs
    -- Subcase B (`variantIdx ≠ v_act`: inactive UB)
    by_cases hv_eq : variantIdx = v_act
    · subst hv_eq
      rcases hpayload fieldIdx hf_lt with
        ⟨sc, msc, hget_fv, hrel_sc, hsz_sc, hbool_sc, hchar_sc, _, _, hread_sc⟩ |
        ⟨hget_none, b_u, hb_ge, hb_lt, hbit_false⟩
      · have hfl_eq : (translateTy fieldTy body.layouts).layout =
            ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).fieldLayout := by
          rw [hfty_eq]; exact hfl_f.symm
        have hread_sc' :
            localAlloc.allocation.readScalar annealTargetDataLayout
              (Miri.Memory.allocRange ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).offset
                (translateTy fieldTy body.layouts).layout.size) false =
            .ok (.fromScalarInt msc) := by
          rw [hfl_eq]; exact hread_sc
        have hptr_f :
            Miri.ABI.Size.ofBytes
              (mp.ptr.offset.bytes + ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).offset.bytes) =
            Miri.ABI.Size.ofBytes
              (baseAddr + ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).offset.bytes) := by
          rw [hptr]; rfl
        have hread_ok := annealReadIndirectImmediate_scalar_ok
          (mp := ⟨⟨Miri.ABI.Size.ofBytes
            (mp.ptr.offset.bytes + ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).offset.bytes),
            mp.ptr.provenance⟩, .none, mp.misaligned⟩)
          (m := m₁) hprim_fty hprov hbase hptr_f hlive.1 hread_sc'
        have ha_ok : evalStmt s stmt body.localDecls body.layouts =
            match get? s.frame.locals dstIdx with
            | .some .dead => MirStepNode.fail .ub
            | .some _ =>
              match set? s.frame.locals dstIdx (.init (.scalar sc)) with
              | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
              | .none => MirStepNode.fail .ub
            | .none => MirStepNode.fail .ub := by
          have hbeq_v : Nat.beq variantIdx variantIdx = true := by simp
          have hptu := hvalid_enum.placeTouchesUnion_downcast_field hsrc_decl
            vName variantIdx fieldIdx fieldTy
          have hbool_fty : fieldTy.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1) := by
            rw [hfty_eq]; exact hbool_sc
          have hval_sc : ∀ op_r,
              (op_r = Operand.move ⟨srcIdx, [.downcast vName variantIdx, .field fieldIdx fieldTy]⟩ ∨
               op_r = Operand.copy ⟨srcIdx, [.downcast vName variantIdx, .field fieldIdx fieldTy]⟩) →
              validateLoadedValue body.layouts body.localDecls op_r (.scalar sc) = true := by
            intro op_r hop_r
            rcases hop_r with rfl | rfl <;> {
              unfold validateLoadedValue
              dsimp only [operandTy, placeTy]
              rw [hsrc_decl]
              dsimp only [resolveProjectedTy]
              cases hk_f : fieldTy.kind <;> try rfl
              rcases (hbool_fty hk_f).2 with hb | hb <;> simp [hb]
            }
          unfold evalStmt; rw [hkind]
          have hval_mv := hval_sc _ (Or.inl rfl)
          have hval_cp := hval_sc _ (Or.inr rfl)
          cases isMove
          · simp only [Bool.false_eq_true, ↓reduceIte, evalRvalue, evalOperand,
              hptu, hval_cp, hbor, hcaller, hslot_s, readProjectedValue, hbeq_v,
              hget_fv, hprot, invalidateConflictingBorrows]
            cases get? s.frame.locals dstIdx with
            | none => rfl
            | some sl =>
              cases sl with
              | dead => rfl
              | uninit | init _ =>
                cases set? s.frame.locals dstIdx _ with
                | none => rfl
                | some locals₂ =>
                  apply congrArg MirStepNode.step
                  apply congrArg (fun mem' => advanceStmt s locals₂ mem')
                  cases hm : s.memory; simp_all
          · simp only [↓reduceIte, evalRvalue, evalOperand,
              hptu, hval_mv, hbor, hcaller, hslot_s, readProjectedValue, hbeq_v,
              hget_fv, hprot, invalidateConflictingBorrows]
            cases get? s.frame.locals dstIdx with
            | none => rfl
            | some sl =>
              cases sl with
              | dead => rfl
              | uninit | init _ =>
                cases set? s.frame.locals dstIdx _ with
                | none => rfl
                | some locals₂ =>
                  apply congrArg MirStepNode.step
                  apply congrArg (fun mem' => advanceStmt s locals₂ mem')
                  cases hm : s.memory; simp_all
        have hm_write :
            Miri.Interpreter.Step.evalStatement
              (annealStepHooksLM2_3 body.localDecls body.layouts) () (translateStmt stmt) m =
            Miri.Interpreter.runRvalue
              (annealWriteImmediateLM2_2 (.scalar (.fromScalarInt msc)) destPlace) m₁ := by
          rw [hm_base]
          apply runRvalue_eq_of_eq
          rw [EStateM.bind_eq_ok (by
            rw [EStateM.bind_eq_ok hdown_ok]; dsimp [annealReadImmediateLM2_2]; exact hread_ok)]
        have hlaysz_dst :
            (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes := by
          rw [hdst_ty, hfl_eq]; exact hsz_sc
        have hbool_dst : dstDecl.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1) := by
          rw [hdst_ty, hfty_eq]; exact hbool_sc
        have hchar_dst : dstDecl.ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true := by
          rw [hdst_ty, hfty_eq]; exact hchar_sc
        obtain ⟨hstep_rel, hpres_u, hpres_i⟩ :=
          write_after_rvalue_simulation_LM2_3
            (annealStepHooksLM2_3 body.localDecls body.layouts)
            (topFrame₁ := tf₁) (id0 := topFrame.localsIdentity)
            hretCont ⟨retLay, hretPlace⟩ halloc hcal hstack hbor hprot hcaller
            hframes hframe.body_eq hframe.location_eq hbb hstmt
            hframe₁ hdisj₁ hdst_decl henv_dst himm_dst₁
            (.scalar sc msc hrel_sc hlaysz_dst hbool_dst hchar_dst)
            ha_ok hm_write
        exact ⟨hstep_rel, (fun enumId b hne hu => hpres_u enumId b hne (huninit_m₁ enumId b hu)),
          (fun j hj => hpres_i j (himm_m₁ j hj))⟩
      · -- Active variant (`variantIdx = v_act`), missing trailing field
        -- (`get? fieldVals fieldIdx = none`): both step to `.ub`.
        let fDesc := (variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt
        have hfl_eq : (translateTy fieldTy body.layouts).layout = fDesc.fieldLayout := by
          rw [hfty_eq]; exact hfl_f.symm
        have hf_inb :
            fDesc.offset.bytes.toNat + (translateTy fieldTy body.layouts).layout.size.bytes.toNat ≤
              localAlloc.allocation.byteSize.bytes.toNat := by
          rw [hfl_eq, hbs_eq]
          exact hvf.fields_in_bounds fieldIdx hf_lt
        have hb_lt_ty :
            b_u < fDesc.offset.bytes.toNat +
              (translateTy fieldTy body.layouts).layout.size.bytes.toNat := by
          rw [hfl_eq]; exact hb_lt
        have hb_sz : b_u < localAlloc.allocation.byteSize.bytes.toNat :=
          Nat.lt_of_lt_of_le hb_lt_ty hf_inb
        have hget_false :
            localAlloc.allocation.initializationMask.get
              (Miri.ABI.Size.ofBytes (UInt64.ofNat b_u)) = .ok false := by
          rw [initMaskWordRel_get hmask_rel hb_sz, hbit_false]
        have hlen_lt_4g : localAlloc.allocation.byteSize.bytes.toNat < 2 ^ 32 := by
          rw [hbs_eq]; exact hvalid_enum.size_lt_4gib
        obtain ⟨badRng, huninit_q⟩ :=
          initMaskWordRel_isRangeInitialized_error_of_get_false
            hmask_rel hlen_lt_4g hf_inb hb_ge hb_lt_ty hget_false
        have hptr_f :
            Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + fDesc.offset.bytes) =
            Miri.ABI.Size.ofBytes (baseAddr + fDesc.offset.bytes) := by
          rw [hptr]; rfl
        have hread_err := annealReadIndirectImmediate_scalar_uninit_ub
          (mp := ⟨⟨Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + fDesc.offset.bytes),
            mp.ptr.provenance⟩, .none, mp.misaligned⟩)
          (m := m₁) hprim_fty hprov hbase hptr_f hlive.1 huninit_q
        have hbeq_v : Nat.beq variantIdx variantIdx = true := by simp
        have hptu := hvalid_enum.placeTouchesUnion_downcast_field hsrc_decl
          vName variantIdx fieldIdx fieldTy
        have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
          unfold evalStmt; rw [hkind]
          cases isMove <;> {
            simp only [Bool.false_eq_true, ↓reduceIte, evalRvalue, evalOperand,
              hptu, hslot_s, readProjectedValue, hbeq_v, hget_none]
          }
        have hm_err :
            Miri.Interpreter.Step.evalStatement
              (annealStepHooksLM2_3 body.localDecls body.layouts) () (translateStmt stmt) m =
            (m₁, .error (.undefinedBehavior "read of uninitialized memory field")) := by
          rw [hm_base]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_error (by
            rw [EStateM.bind_eq_ok hdown_ok]; dsimp [annealReadImmediateLM2_2]; exact hread_err)]
        rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
        exact ⟨.ub _ _, (fun _ _ _ hu => huninit_m₁ _ _ hu), (fun _ hj => himm_m₁ _ hj)⟩
    · -- Inactive variant (`variantIdx ≠ v_act`): both step to `.ub`.
      obtain ⟨b_u, hb_ge, hb_lt, huninit_src⟩ := hinactive_uninit v_act fieldVals hslot_s hv_eq
      have huninit_src₁ := huninit_m₁ srcIdx b_u huninit_src
      have hmls_s1 : tf₁.locals[srcIdx]? =
          some ⟨.live (.indirect mp), some (translateTy srcDecl.ty body.layouts)⟩ := by
        dsimp [tf₁, cacheFrameLocalLayout]
        rw [Array.getElem?_set_self hlt_s, hmls_s_eq]
      have hget_false :
          localAlloc.allocation.initializationMask.get
            (Miri.ABI.Size.ofBytes (UInt64.ofNat b_u)) = .ok false :=
        huninit_src₁ tf₁ mp _ allocId borTag localAlloc rfl hmls_s1 hprov hlive.1
      let fDesc := (variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt
      have hfl_eq : (translateTy fieldTy body.layouts).layout = fDesc.fieldLayout := by
        rw [hfty_eq]; exact hfl_f.symm
      have hf_inb :
          fDesc.offset.bytes.toNat + (translateTy fieldTy body.layouts).layout.size.bytes.toNat ≤
            localAlloc.allocation.byteSize.bytes.toNat := by
        rw [hfl_eq, hbs_eq]
        exact hvf.fields_in_bounds fieldIdx hf_lt
      have hlen_lt_4g : localAlloc.allocation.byteSize.bytes.toNat < 2 ^ 32 := by
        rw [hbs_eq]; exact hvalid_enum.size_lt_4gib
      have hb_lt_ty :
          b_u < fDesc.offset.bytes.toNat +
            (translateTy fieldTy body.layouts).layout.size.bytes.toNat := by
        rw [hfl_eq]; exact hb_lt
      obtain ⟨badRng, huninit_q⟩ :=
        initMaskWordRel_isRangeInitialized_error_of_get_false
          hmask_rel hlen_lt_4g hf_inb hb_ge hb_lt_ty hget_false
      have hptr_f :
          Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + fDesc.offset.bytes) =
          Miri.ABI.Size.ofBytes (baseAddr + fDesc.offset.bytes) := by
        rw [hptr]; rfl
      have hread_err := annealReadIndirectImmediate_scalar_uninit_ub
        (mp := ⟨⟨Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + fDesc.offset.bytes),
          mp.ptr.provenance⟩, .none, mp.misaligned⟩)
        (m := m₁) hprim_fty hprov hbase hptr_f hlive.1 huninit_q
      have hbeq_f : Nat.beq v_act variantIdx = false := by
        cases hb : Nat.beq v_act variantIdx
        · rfl
        · rw [Nat.beq_eq] at hb; exact absurd hb (Ne.symm hv_eq)
      have hptu := hvalid_enum.placeTouchesUnion_downcast_field hsrc_decl
        vName variantIdx fieldIdx fieldTy
      have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt; rw [hkind]
        cases isMove <;> {
          simp only [Bool.false_eq_true, ↓reduceIte, evalRvalue, evalOperand,
            hptu, hslot_s, readProjectedValue, hbeq_f]
        }
      have hm_err :
          Miri.Interpreter.Step.evalStatement
            (annealStepHooksLM2_3 body.localDecls body.layouts) () (translateStmt stmt) m =
          (m₁, .error (.undefinedBehavior "read of uninitialized memory field")) := by
        rw [hm_base]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_error (by
          rw [EStateM.bind_eq_ok hdown_ok]; dsimp [annealReadImmediateLM2_2]; exact hread_err)]
      rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
      exact ⟨.ub _ _, (fun _ _ _ hu => huninit_m₁ _ _ hu), (fun _ hj => himm_m₁ _ hj)⟩

/-- **`evalProjection_downcast_field_initialized_divergence`** (`LM-2.3`
Deliverable 4): When `_src` holds an initialized enum `.aggregate v_act
fieldVals` and a `Downcast(variantIdx) + Field(fieldIdx)` projection reads an
inactive variant (`variantIdx ≠ v_act`) whose target field descriptor
`(variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt` coincides with an initialized
field `(variants[v_act]'hv_act)[j]'hj` of the active variant `v_act`:
* Anneal's tree-shaped `readProjectedValue` checks
  `Nat.beq v_act variantIdx = false` and returns `.fail .ub` unconditionally;
* `lean-miri`'s byte-level `projectDowncast` + `projectField` offsets into the
  underlying allocation without checking the discriminant tag, reads the
  initialized scalar `fieldVals[j]` from that overlapping byte range, writes it
  into live `_dst`, and completes the step in `StateRelLM2_3` with the updated
  Anneal state! -/
theorem evalProjection_downcast_field_initialized_divergence
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_3 body env allocBudget s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    (henv_valid : ∀ t tb vs, env t = some (tb, vs) → ValidEnumLayout t body.layouts tb vs)
    {bb : BasicBlockData} {stmt : Statement}
    {dstIdx srcIdx : Local} {dstDecl srcDecl : LocalDecl}
    {isMove : Bool} {vName : Option String} {variantIdx fieldIdx : Nat} {fieldTy : Ty}
    {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    {v_act j : Nat} {fieldVals : List Value}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hkind : stmt.kind = .assign ⟨dstIdx, .nil⟩
      (.use (if isMove then
        .move ⟨srcIdx, [.downcast vName variantIdx, .field fieldIdx fieldTy]⟩
      else
        .copy ⟨srcIdx, [.downcast vName variantIdx, .field fieldIdx fieldTy]⟩)))
    (hsrc_decl : get? body.localDecls srcIdx = some srcDecl)
    (hdst_decl : get? body.localDecls dstIdx = some dstDecl)
    (henv_src : env srcDecl.ty = some (tagBytes, variants))
    (hv_lt : variantIdx < variants.length)
    (hf_lt : fieldIdx < (variants[variantIdx]'hv_lt).length)
    (hfty_eq : fieldTy = ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).ty)
    (hdst_ty : dstDecl.ty = fieldTy)
    (hdst_imm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx)
    (hdst_not_dead : get? s.frame.locals dstIdx ≠ some .dead)
    (hslot_src : get? s.frame.locals srcIdx = some (.init (.aggregate v_act fieldVals)))
    (hv_ne : variantIdx ≠ v_act)
    (hv_act : v_act < variants.length)
    (hj : j < (variants[v_act]'hv_act).length)
    (hj_val : j < fieldVals.length)
    (hf_overlap : ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt) = ((variants[v_act]'hv_act)[j]'hj)) :
    stepMirFn body s = .fail .ub ∧
    ∃ (sc : MirAst.ScalarInt) (m' : AnnealStepState),
      get? fieldVals j = some (.scalar sc) ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_3 body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      StateRelLM2_3 body env allocBudget
        (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar sc))) s.memory) m' ∧
      (∀ enumId b, enumId ≠ dstIdx →
        EnumLocalByteUninit m enumId b → EnumLocalByteUninit m' enumId b) ∧
      (∀ k, IsImmediateStepLocal m k → IsImmediateStepLocal m' k) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe, halloc,
      hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hvalid_enum := henv_valid srcDecl.ty tagBytes variants henv_src
  obtain ⟨_, _, _, _, _, _, _, _, _, vars, _, _, hvf_all⟩ := hvalid_enum.table_entry
  have hvf := hvf_all variantIdx hv_lt
  obtain ⟨hprim_f, hfl_f⟩ := hvf.fields_prim fieldIdx hf_lt
  have hprim_dst : IsPrimScalarTy dstDecl.ty := by rw [hdst_ty, hfty_eq]; exact hprim_f
  have henv_dst := env_none_of_isPrimScalarTy henv_valid hprim_dst
  obtain ⟨slot_d0, mls_d0, hlt_d, hslot_d0, hmls_d0_eq, hloc_d0⟩ := hframe.lookup_local hdst_decl
  have hcache_d0 : ∀ l, (topFrame.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d0_eq]; exact hloc_d0.layout_eq
  let tf₀ := cacheFrameLocalLayout topFrame dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  let m₀ : AnnealStepState := { m with stack := ⟨#[tf₀]⟩ }
  have heval_dst := annealEvalPlace_unprojected hframes hlt_d hdst_decl hcache_d0
  have hframe₀ := hframe.cache_local_layout hdst_decl hlt_d
  have hdisj₀ := MemoryAllocDisjoint_cacheFrameLocalLayout hdisj hlt_d
    (translateTy dstDecl.ty body.layouts)
  have himm_dst₀ : IsImmediateFrameLocal tf₀ dstIdx :=
    (hdst_imm topFrame hframes).cache_layout hlt_d (translateTy dstDecl.ty body.layouts)
  obtain ⟨slot_s, mls_s, hlt_s, hslot_s, hmls_s_eq, hloc_s⟩ := hframe₀.lookup_local hsrc_decl
  have hcache_s : ∀ l, (tf₀.locals[srcIdx]'hlt_s).layout = some l →
      l = translateTy srcDecl.ty body.layouts := by
    rw [hmls_s_eq]; exact hloc_s.layout_eq
  let tf₁ := cacheFrameLocalLayout tf₀ srcIdx hlt_s (translateTy srcDecl.ty body.layouts)
  let m₁ : AnnealStepState := { m with stack := ⟨#[tf₁]⟩ }
  have hres_src :
      annealResolveAndCacheLocalLayout body.localDecls body.layouts srcIdx
        (some (translateTy dstDecl.ty body.layouts)) m₀ =
      .ok (tf₁, translateTy srcDecl.ty body.layouts) m₁ :=
    annealResolveAndCacheLocalLayout_eq (m := m₀) rfl hlt_s hsrc_decl hcache_s
  have hframe₁ := hframe₀.cache_local_layout hsrc_decl hlt_s
  have hdisj₁ := MemoryAllocDisjoint_cacheFrameLocalLayout hdisj₀ hlt_s
    (translateTy srcDecl.ty body.layouts)
  have himm_dst₁ : IsImmediateFrameLocal tf₁ dstIdx :=
    himm_dst₀.cache_layout hlt_s (translateTy srcDecl.ty body.layouts)
  let projPlace : Place := ⟨srcIdx, [.downcast vName variantIdx, .field fieldIdx fieldTy]⟩
  let useOp : MirAst.Operand := if isMove then .move projPlace else .copy projPlace
  have hlm23_op : lm23Operand (translateOperand useOp) = true := by
    cases isMove <;> rfl
  have hlm23_asgn :
      lm23Assign body.localDecls body.layouts ⟨dstIdx, #[]⟩
        (.Use (translateOperand useOp) .No) = true := by
    unfold lm23Assign; simp [hlm23_op]
  have heval_op_down :
      annealEvalOperandLM2_3 body.localDecls body.layouts (translateOperand useOp)
        (some (translateTy dstDecl.ty body.layouts)) =
      annealEvalDowncastOperand body.localDecls body.layouts
        ⟨srcIdx, #[.Downcast vName variantIdx, .Field fieldIdx (encodeTyId fieldTy)]⟩
        (some (translateTy dstDecl.ty body.layouts)) := by
    cases isMove <;> rfl
  dsimp only [useOp, projPlace] at hlm23_asgn heval_op_down
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
  have hnot_memcopy : usesStructMemCopyDest destPlace = false :=
    usesStructMemCopyDest_false_of_primScalar destPlace rfl hprim_dst
  have hm_base :
      Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_3 body.localDecls body.layouts) () (translateStmt stmt) m =
      Miri.Interpreter.runRvalue
        ((annealEvalDowncastOperand body.localDecls body.layouts
            ⟨srcIdx, #[.Downcast vName variantIdx, .Field fieldIdx (encodeTyId fieldTy)]⟩
            (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediateLM2_2) >>=
          fun r => annealWriteImmediateLM2_2 r.imm destPlace) m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    rw [hkind]
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
      translateRvalue, annealStepHooksLM2_3]
    rw [hlm23_asgn]
    simp only [↓reduceIte]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooksLM2_3
    dsimp only [annealRvalueHooksLM2_2]
    rw [show annealEvalPlaceLM2_3 body.localDecls body.layouts ⟨dstIdx, #[]⟩ =
          annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ from rfl,
      EStateM.bind_eq_ok heval_dst]
    dsimp only
    rw [heval_op_down]
    exact bind_copyOp_eq_of_not_usesStructMemCopyDest hnot_memcopy m₀
  have hget_s1 :
      tf₁.getLocal srcIdx = .ok ⟨mls_s.value, some (translateTy srcDecl.ty body.layouts)⟩ := by
    have hg := cacheFrameLocalLayout_getLocal tf₀ hlt_s (translateTy srcDecl.ty body.layouts)
    rw [hmls_s_eq] at hg
    exact hg
  have hcf₀ := stack_currentFrame?_singleton m₀.stack tf₀ rfl
  have huninit_m₁ : ∀ enumId b, EnumLocalByteUninit m enumId b → EnumLocalByteUninit m₁ enumId b :=
    fun _ _ hu =>
      EnumLocalByteUninit.of_cache_layout (m := m₀) rfl
        (EnumLocalByteUninit.of_cache_layout hframes hu)
  have himm_m₁ : ∀ k, IsImmediateStepLocal m k → IsImmediateStepLocal m₁ k :=
    fun _ hk =>
      IsImmediateStepLocal.of_cache_layout (m := m₀) rfl
        (IsImmediateStepLocal.of_cache_layout hframes hk)
  have hbeq_f : Nat.beq v_act variantIdx = false := by
    cases hb : Nat.beq v_act variantIdx
    · rfl
    · rw [Nat.beq_eq] at hb; exact absurd hb (Ne.symm hv_ne)
  have hptu := hvalid_enum.placeTouchesUnion_downcast_field hsrc_decl
    vName variantIdx fieldIdx fieldTy
  have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
    unfold evalStmt; rw [hkind]
    cases isMove <;> {
      simp only [Bool.false_eq_true, ↓reduceIte, evalRvalue, evalOperand,
        hptu, hslot_src, readProjectedValue, hbeq_f]
    }
  refine ⟨ha_ub, ?_⟩
  cases hloc_s with
  | base _ _ hnone _ =>
    rw [henv_src] at hnone; cases hnone
  | enumDead _ _ _ _ _ _ =>
    rw [hslot_src] at hslot_s; cases hslot_s
  | enumUninitImm _ _ _ _ _ _ =>
    rw [hslot_src] at hslot_s; cases hslot_s
  | enumUninitInd _ _ _ _ _ _ _ =>
    rw [hslot_src] at hslot_s; cases hslot_s
  | enumInd tb' vs' v_act' fieldVals' mp c_s henv' _ hmem_i =>
    rw [hslot_src] at hslot_s
    injection hslot_s with hs_eq
    injection hs_eq with hs_agg
    injection hs_agg with hv_eq' hfv_eq'
    subst hv_eq' hfv_eq'
    have hop_s1 := frame_getLocalOperand_live tf₁ hget_s1
    rw [henv_src] at henv'; injection henv' with heq_p; rcases heq_p with ⟨rfl, rfl⟩
    rcases hmem_i with ⟨allocId, borTag, baseAddr, localAlloc, words, _,
      _, _, hprov, _, hmeta, hlive, hbase, hptr, hovf, _, _,
      _, _, _, _, _, _, _, _, hpayload⟩
    have hptr_ovf :
        mp.ptr.offset.bytes.toNat +
          (translateTy srcDecl.ty body.layouts).layout.size.bytes.toNat < 2 ^ 64 := by
      rw [hptr]; dsimp [Miri.ABI.Size.ofBytes]; exact hovf
    have hproj_i := annealEvalEnumProjection_downcast_field_indirect_ok
      (vName := vName) hvalid_enum hv_lt hf_lt hfty_eq hmeta hptr_ovf m₁
    have hdown_ok :
        annealEvalDowncastOperand body.localDecls body.layouts
          ⟨srcIdx, #[.Downcast vName variantIdx, .Field fieldIdx (encodeTyId fieldTy)]⟩
          (some (translateTy dstDecl.ty body.layouts)) m₀ =
        .ok ⟨.indirect
              ⟨⟨Miri.ABI.Size.ofBytes
                  (mp.ptr.offset.bytes +
                    ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).offset.bytes),
                mp.ptr.provenance⟩,
                .none, mp.misaligned⟩,
              translateTy fieldTy body.layouts⟩ m₁ := by
      unfold annealEvalDowncastOperand
      simp only [get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
        Pure.pure, EStateM.pure, hcf₀, Option.isNone_some, Bool.false_eq_true, ↓reduceIte,
        hres_src, hop_s1]
      exact hproj_i
    have hprim_fty : IsPrimScalarTy fieldTy := by rw [hfty_eq]; exact hprim_f
    obtain ⟨sc, msc, hget_fv, hrel_sc, hsz_sc, hbool_sc, hchar_sc, _, _, hread_sc⟩ :
        let f := (variants[v_act]'hv_act)[j]'hj
        ∃ sc msc,
          get? fieldVals j = some (.scalar sc) ∧
          ScalarRel sc msc ∧
          f.fieldLayout.size = translateSizeBytes sc.sizeBytes ∧
          (f.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) ∧
          (f.ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) ∧
          (∀ b, f.offset.bytes.toNat ≤ b →
            b < f.offset.bytes.toNat + f.fieldLayout.size.bytes.toNat →
            maskBlocksGetBit words b = true) ∧
          localAlloc.allocation.initializationMask.isRangeInitialized
            (Miri.Memory.allocRange f.offset f.fieldLayout.size) = .ok (.ok ()) ∧
          localAlloc.allocation.readScalar annealTargetDataLayout
            (Miri.Memory.allocRange f.offset f.fieldLayout.size) false =
            .ok (.fromScalarInt msc) := by
      rcases hpayload j hj with hinit | ⟨hget_none, _⟩
      · exact hinit
      · unfold get? at hget_none
        exact absurd (List.getElem?_eq_none_iff.mp hget_none) (by omega)
    have hfl_eq : (translateTy fieldTy body.layouts).layout =
        ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).fieldLayout := by
      rw [hfty_eq]; exact hfl_f.symm
    have hread_sc' :
        localAlloc.allocation.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).offset
            (translateTy fieldTy body.layouts).layout.size) false =
        .ok (.fromScalarInt msc) := by
      rw [hfl_eq, hf_overlap]; exact hread_sc
    have hptr_f :
        Miri.ABI.Size.ofBytes
          (mp.ptr.offset.bytes + ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).offset.bytes) =
        Miri.ABI.Size.ofBytes
          (baseAddr + ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).offset.bytes) := by
      rw [hptr]; rfl
    have hread_ok := annealReadIndirectImmediate_scalar_ok
      (mp := ⟨⟨Miri.ABI.Size.ofBytes
        (mp.ptr.offset.bytes + ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).offset.bytes),
        mp.ptr.provenance⟩, .none, mp.misaligned⟩)
      (m := m₁) hprim_fty hprov hbase hptr_f hlive.1 hread_sc'
    have hm_write :
        Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_3 body.localDecls body.layouts) () (translateStmt stmt) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediateLM2_2 (.scalar (.fromScalarInt msc)) destPlace) m₁ := by
      rw [hm_base]
      apply runRvalue_eq_of_eq
      rw [EStateM.bind_eq_ok (by
        rw [EStateM.bind_eq_ok hdown_ok]; dsimp [annealReadImmediateLM2_2]; exact hread_ok)]
    have hlaysz_dst :
        (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes := by
      rw [hdst_ty, hfl_eq, hf_overlap]; exact hsz_sc
    have hbool_dst : dstDecl.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1) := by
      rw [hdst_ty, hfty_eq, hf_overlap]; exact hbool_sc
    have hchar_dst : dstDecl.ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true := by
      rw [hdst_ty, hfty_eq, hf_overlap]; exact hchar_sc
    obtain ⟨hstep_rel, hpres_u, hpres_i⟩ :=
      write_after_rvalue_step_LM2_3
        (annealStepHooksLM2_3 body.localDecls body.layouts)
        (topFrame₁ := tf₁) (id0 := topFrame.localsIdentity)
        (val := .scalar sc) (imm := .scalar (.fromScalarInt msc))
        hretCont ⟨retLay, hretPlace⟩ halloc hcal hstack hbor hprot hcaller
        hframes hframe.body_eq hframe.location_eq hbb hstmt
        hframe₁ hdisj₁ hdst_decl henv_dst himm_dst₁
        (.scalar sc msc hrel_sc hlaysz_dst hbool_dst hchar_dst)
        hm_write
    have hlt_af_d : dstIdx < s.frame.locals.length := by
      have hs := hslot_d0
      unfold get? at hs
      exact (List.getElem?_eq_some_iff.mp hs).1
    have hset_d :
        set? s.frame.locals dstIdx (.init (.scalar sc)) =
          some (s.frame.locals.set dstIdx (.init (.scalar sc))) :=
      set?_eq_some_set hlt_af_d (.init (.scalar sc))
    have hmatch_step :
        (match get? s.frame.locals dstIdx with
        | .some .dead => MirStepNode.fail .ub
        | .some _ =>
          match set? s.frame.locals dstIdx (.init (.scalar sc)) with
          | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
          | .none => MirStepNode.fail .ub
        | .none => MirStepNode.fail .ub) =
        MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar sc))) s.memory) := by
      rw [hslot_d0]
      cases slot_d0 with
      | dead => exact False.elim (hdst_not_dead hslot_d0)
      | uninit | init _ => simp [hset_d]
    rw [hmatch_step] at hstep_rel
    have hinv :
        ∀ {mRes : Miri.Interpreter.StepResult AnnealStepState Bool},
          StepRelLM2_3 body env allocBudget m
            (MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar sc))) s.memory))
            mRes →
          ∃ m',
            mRes = (m', .ok true) ∧
            StateRelLM2_3 body env allocBudget
              (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar sc))) s.memory) m' := by
      intro mRes hsr
      generalize ha_step :
        MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar sc))) s.memory) = aRes at hsr
      cases hsr with
      | step s₁ m' hst =>
        injection ha_step with hr; injection hr with hs; subst hs
        exact ⟨m', rfl, hst⟩
      | emitStep obs s₁ m' hst =>
        cases obs with
        | silent =>
          dsimp [MirStepNode.emitStep, MirStepNode.step] at ha_step
          injection ha_step with hr; injection hr with hs; subst hs
          exact ⟨m', rfl, hst⟩
        | event _ => cases ha_step
      | retRoot _ _ _ _ _ _ _ _ _ => cases ha_step
      | ub _ _ => cases ha_step
    obtain ⟨m', hm', hst'⟩ := hinv hstep_rel
    refine ⟨sc, m', hget_fv, hm', hst', ?_, ?_⟩
    · intro enumId b hne hu
      have hu' := hpres_u enumId b hne (huninit_m₁ enumId b hu)
      simpa [hm'] using hu'
    · intro k hk
      have hk' := hpres_i k (himm_m₁ k hk)
      simpa [hm'] using hk'

/-! ## 5. `Rvalue.Discriminant` & `StatementKind.SetDiscriminant` (`LM-2.3`) -/

/-- Valid 8-byte integer destination types (`usize`, `u64`, `isize`, `i64`) for
`Rvalue.Discriminant` in Anneal's 64-bit MIR semantics. -/
def IsEnumDiscrDestTy (ty : Ty) : Prop :=
  ty.kind = .uint .usize ∨ ty.kind = .uint .u64 ∨
  ty.kind = .int .isize ∨ ty.kind = .int .i64

theorem IsEnumDiscrDestTy.props {ty : Ty} {layouts : LayoutTable}
    (h : IsEnumDiscrDestTy ty) :
    IsPrimScalarTy ty ∧
    (translateTy ty layouts).layout.size = translateSizeBytes 8 ∧
    ty.kind ≠ .bool ∧ ty.kind ≠ .char := by
  rcases h with hk | hk | hk | hk
  · refine ⟨Or.inr (Or.inr (Or.inr ⟨.usize, hk⟩)), ?_, by rw [hk]; nofun, by rw [hk]; nofun⟩
    rcases ty with ⟨k, l⟩; dsimp at hk; subst hk; rfl
  · refine ⟨Or.inr (Or.inr (Or.inr ⟨.u64, hk⟩)), ?_, by rw [hk]; nofun, by rw [hk]; nofun⟩
    rcases ty with ⟨k, l⟩; dsimp at hk; subst hk; rfl
  · refine ⟨Or.inr (Or.inr (Or.inl ⟨.isize, hk⟩)), ?_, by rw [hk]; nofun, by rw [hk]; nofun⟩
    rcases ty with ⟨k, l⟩; dsimp at hk; subst hk; rfl
  · refine ⟨Or.inr (Or.inr (Or.inl ⟨.i64, hk⟩)), ?_, by rw [hk]; nofun, by rw [hk]; nofun⟩
    rcases ty with ⟨k, l⟩; dsimp at hk; subst hk; rfl

/-- **`evalRvalue_discriminant_simulation`** (`LM-2.3` Deliverable 3):
Evaluating `_dst = discriminant(_src)` from a `StateRelLM2_3`-related state
simulates vendored `Miri.Interpreter.Discriminant.readDiscriminant` +
`Miri.Interpreter.Discriminant.discriminantForVariant` + `annealWriteImmediateLM2_2`
in lockstep:
* `.dead` `_src` → `StepRelLM2_3.ub` (`"read of dead local"`);
* `.uninit` `_src` (immediate or indirect) → `StepRelLM2_3.ub`;
* `.init (.aggregate v_act fieldVals)`: reads tag scalar `[0, tagBytes)`,
  resolves variant `v_act` and discriminant `⟨v_act, 8⟩`, writes `_dst`, and
  preserves `EnumLocalByteUninit` on all `enumId ≠ dstIdx` (or reports `.ub` if
  `_dst` is `.dead`). -/
theorem evalRvalue_discriminant_simulation
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_3 body env allocBudget s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    (henv_valid : ∀ t tb vs, env t = some (tb, vs) → ValidEnumLayout t body.layouts tb vs)
    {bb : BasicBlockData} {stmt : Statement}
    {dstIdx srcIdx : Local} {dstDecl srcDecl : LocalDecl}
    {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hkind : stmt.kind = .assign ⟨dstIdx, .nil⟩ (.discriminant ⟨srcIdx, .nil⟩))
    (hsrc_decl : get? body.localDecls srcIdx = some srcDecl)
    (hdst_decl : get? body.localDecls dstIdx = some dstDecl)
    (henv_src : env srcDecl.ty = some (tagBytes, variants))
    (hdst_ty : IsEnumDiscrDestTy dstDecl.ty)
    (hdst_imm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx) :
    StepRelLM2_3 body env allocBudget m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_3 body.localDecls body.layouts) () m) ∧
    (∀ enumId b, enumId ≠ dstIdx →
      EnumLocalByteUninit m enumId b →
      EnumLocalByteUninit
        (Miri.Interpreter.Step.step (annealStepHooksLM2_3 body.localDecls body.layouts) () m).1
        enumId b) ∧
    (∀ j,
      IsImmediateStepLocal m j →
      IsImmediateStepLocal
        (Miri.Interpreter.Step.step (annealStepHooksLM2_3 body.localDecls body.layouts) () m).1
        j) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe, halloc,
      hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hvalid_enum := henv_valid srcDecl.ty tagBytes variants henv_src
  obtain ⟨hprim_dst, hsz_dst, hnot_bool, hnot_char⟩ := hdst_ty.props (layouts := body.layouts)
  have henv_dst := env_none_of_isPrimScalarTy henv_valid hprim_dst
  -- Step 1: evaluate destination `⟨dstIdx, #[]⟩` (`tf₀`).
  obtain ⟨_, mls_d0, hlt_d, _, hmls_d0_eq, hloc_d0⟩ := hframe.lookup_local hdst_decl
  have hcache_d0 : ∀ l, (topFrame.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d0_eq]; exact hloc_d0.layout_eq
  let tf₀ := cacheFrameLocalLayout topFrame dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  let m₀ : AnnealStepState := { m with stack := ⟨#[tf₀]⟩ }
  have heval_dst := annealEvalPlace_unprojected hframes hlt_d hdst_decl hcache_d0
  have hframe₀ := hframe.cache_local_layout hdst_decl hlt_d
  have hdisj₀ := MemoryAllocDisjoint_cacheFrameLocalLayout hdisj hlt_d
    (translateTy dstDecl.ty body.layouts)
  have himm_dst₀ : IsImmediateFrameLocal tf₀ dstIdx :=
    (hdst_imm topFrame hframes).cache_layout hlt_d (translateTy dstDecl.ty body.layouts)
  -- Step 2: lookup `srcIdx` in `tf₀` (`tf₁`).
  obtain ⟨slot_s, mls_s, hlt_s, hslot_s, hmls_s_eq, hloc_s⟩ := hframe₀.lookup_local hsrc_decl
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.layout_eq
  let tf₁ := cacheFrameLocalLayout tf₀ srcIdx hlt_s (translateTy srcDecl.ty body.layouts)
  let m₁ : AnnealStepState := { m with stack := ⟨#[tf₁]⟩ }
  have hframe₁ := hframe₀.cache_local_layout hsrc_decl hlt_s
  have hdisj₁ := MemoryAllocDisjoint_cacheFrameLocalLayout hdisj₀ hlt_s
    (translateTy srcDecl.ty body.layouts)
  have himm_dst₁ : IsImmediateFrameLocal tf₁ dstIdx :=
    himm_dst₀.cache_layout hlt_s (translateTy srcDecl.ty body.layouts)
  have huninit_m₁ : ∀ enumId b, EnumLocalByteUninit m enumId b → EnumLocalByteUninit m₁ enumId b :=
    fun _ _ hu =>
      EnumLocalByteUninit.of_cache_layout (m := m₀) rfl
        (EnumLocalByteUninit.of_cache_layout hframes hu)
  have himm_m₁ : ∀ j, IsImmediateStepLocal m j → IsImmediateStepLocal m₁ j :=
    fun _ hj =>
      IsImmediateStepLocal.of_cache_layout (m := m₀) rfl
        (IsImmediateStepLocal.of_cache_layout hframes hj)
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
  have hm_base :
      Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_3 body.localDecls body.layouts) () (translateStmt stmt) m =
      Miri.Interpreter.runRvalue
        (do
          let op ← annealEvalOperand body.localDecls body.layouts (.Copy ⟨srcIdx, #[]⟩) none
          let variant ← Miri.Interpreter.Discriminant.readDiscriminant
            (annealDiscriminantHooksLM2_3 body.localDecls body.layouts) () op
          let discr ← Miri.Interpreter.Discriminant.discriminantForVariant
            (annealDiscriminantHooksLM2_3 body.localDecls body.layouts) () op.layout.ty variant
          annealWriteImmediateLM2_2 discr.imm destPlace) m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    rw [hkind]
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
      translateRvalue, annealStepHooksLM2_3, lm23Assign, Array.toList_empty, List.any_nil,
      Bool.false_or, ↓reduceIte]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooksLM2_3
    dsimp only [annealRvalueHooksLM2_2]
    rw [show annealEvalPlaceLM2_3 body.localDecls body.layouts ⟨dstIdx, #[]⟩ =
          annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ from rfl,
      EStateM.bind_eq_ok heval_dst]
    rfl
  cases hloc_s with
  | base _ _ hnone _ =>
    rw [henv_src] at hnone; cases hnone
  | enumDead _ _ c_s _ _ _ =>
    have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; rw [hkind]
      simp [evalRvalue, evalOperand, hslot_s]
    have hop_err :=
      annealEvalOperand_copy_dead (m := m₀) (known := none) rfl hlt_s hsrc_decl hmls_s_eq hcache_s
    have hm_err :
        Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_3 body.localDecls body.layouts) () (translateStmt stmt) m =
        (m₁, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_base]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_error hop_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
    exact ⟨.ub _ _, (fun _ _ _ hu => huninit_m₁ _ _ hu), (fun _ hj => himm_m₁ _ hj)⟩
  | enumUninitImm tb' vs' c_s henv' _ _ =>
    rw [henv_src] at henv'; injection henv' with heq_p; rcases heq_p with ⟨rfl, rfl⟩
    have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; rw [hkind]
      simp [evalRvalue, evalOperand, hslot_s]
    have hop_ok :=
      annealEvalOperand_copy_live (m := m₀) (known := none) rfl hlt_s hsrc_decl hmls_s_eq hcache_s
    have hrd_err := readDiscriminant_uninitImm_ub body.localDecls (m := m₁) hvalid_enum
    have hm_err :
        Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_3 body.localDecls body.layouts) () (translateStmt stmt) m =
        (m₁, .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_base]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hop_ok]
      dsimp only
      rw [EStateM.bind_eq_error hrd_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
    exact ⟨.ub _ _, (fun _ _ _ hu => huninit_m₁ _ _ hu), (fun _ hj => himm_m₁ _ hj)⟩
  | enumUninitInd tb' vs' mp c_s henv' _ hmem_u =>
    rw [henv_src] at henv'; injection henv' with heq_p; rcases heq_p with ⟨rfl, rfl⟩
    have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; rw [hkind]
      simp [evalRvalue, evalOperand, hslot_s]
    have hop_ok :=
      annealEvalOperand_copy_live (m := m₀) (known := none) rfl hlt_s hsrc_decl hmls_s_eq hcache_s
    have hrd_err := readDiscriminant_uninitInd_ub body.localDecls (m := m₁) hmem_u
    have hm_err :
        Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_3 body.localDecls body.layouts) () (translateStmt stmt) m =
        (m₁, .error (.undefinedBehavior "read of uninitialized memory field")) := by
      rw [hm_base]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hop_ok]
      dsimp only
      rw [EStateM.bind_eq_error hrd_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
    exact ⟨.ub _ _, (fun _ _ _ hu => huninit_m₁ _ _ hu), (fun _ hj => himm_m₁ _ hj)⟩
  | enumInd tb' vs' v_act fieldVals mp c_s henv' _ hmem_i =>
    rw [henv_src] at henv'; injection henv' with heq_p; rcases heq_p with ⟨rfl, rfl⟩
    have hv_act_lt : v_act < variants.length := by
      rcases hmem_i with ⟨_, _, _, _, _, _, _, hv_lt, _⟩; exact hv_lt
    have hop_ok :=
      annealEvalOperand_copy_live (m := m₀) (known := none) rfl hlt_s hsrc_decl hmls_s_eq hcache_s
    have hrd_ok := readDiscriminant_enumInd_ok body.localDecls (m := m₁) hmem_i
    obtain ⟨msc_d, hrel_d, hdfv_ok⟩ :=
      discriminantForVariant_enum_ok body.localDecls hvalid_enum hv_act_lt m₁
    have ha_ok : evalStmt s stmt body.localDecls body.layouts =
        match get? s.frame.locals dstIdx with
        | .some .dead => MirStepNode.fail .ub
        | .some _ =>
          match set? s.frame.locals dstIdx (.init (.scalar ⟨v_act, 8⟩)) with
          | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
          | .none => MirStepNode.fail .ub
        | .none => MirStepNode.fail .ub := by
      unfold evalStmt; rw [hkind]
      simp only [evalRvalue, evalOperand, hbor, hcaller, hslot_s, readProjectedValue,
        hvalid_enum.evalPlaceDiscriminant_eq hsrc_decl hv_act_lt,
        hprot, invalidateConflictingBorrows]
      cases get? s.frame.locals dstIdx with
      | none => rfl
      | some sl =>
        cases sl with
        | dead => rfl
        | uninit | init _ =>
          cases set? s.frame.locals dstIdx _ with
          | none => rfl
          | some locals₂ =>
            apply congrArg MirStepNode.step
            apply congrArg (fun mem' => advanceStmt s locals₂ mem')
            cases hm : s.memory; simp_all
    have hm_write :
        Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_3 body.localDecls body.layouts) () (translateStmt stmt) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediateLM2_2 (.scalar (.fromScalarInt msc_d)) destPlace) m₁ := by
      rw [hm_base]
      apply runRvalue_eq_of_eq
      rw [EStateM.bind_eq_ok hop_ok]
      dsimp only
      rw [EStateM.bind_eq_ok hrd_ok, EStateM.bind_eq_ok hdfv_ok]
    obtain ⟨hstep_rel, hpres_u, hpres_i⟩ :=
      write_after_rvalue_simulation_LM2_3
        (annealStepHooksLM2_3 body.localDecls body.layouts)
        (topFrame₁ := tf₁) (id0 := topFrame.localsIdentity)
        hretCont ⟨retLay, hretPlace⟩ halloc hcal hstack hbor hprot hcaller
        hframes hframe.body_eq hframe.location_eq hbb hstmt
        hframe₁ hdisj₁ hdst_decl henv_dst himm_dst₁
        (.scalar ⟨v_act, 8⟩ msc_d hrel_d hsz_dst
          (fun hb => absurd hb hnot_bool) (fun hc => absurd hc hnot_char))
        ha_ok hm_write
    exact ⟨hstep_rel, (fun enumId b hne hu => hpres_u enumId b hne (huninit_m₁ enumId b hu)),
      (fun j hj => hpres_i j (himm_m₁ j hj))⟩

/-- **`step_setDiscriminant_simulation`** (`LM-2.3` Deliverable 2):
Executing `SetDiscriminant(_dst, variantIdx)` from a `StateRelLM2_3`-related
state simulates vendored `Miri.Interpreter.Discriminant.writeDiscriminant` in
lockstep whenever `_dst` is not `.uninit`:
* `.dead` `_dst` → `StepRelLM2_3.ub` (`"write to dead local"`, rustc's
  `DeadLocal`), raised by `projectWrite`'s `annealForceEnumAllocation`;
* `.init (.aggregate v_act fieldVals)` → both machines step. lean-miri writes
  the tag scalar `⟨variantIdx, tagBytes⟩` at `[0, tagBytes)` and leaves every
  payload byte alone, while Anneal keeps `fieldVals` under the new variant
  index. The step preserves `EnumLocalByteUninit` on every `enumId ≠ dstIdx`
  and on `dstIdx` at every non-tag byte `b ≥ tagBytes`.

`hpayload_compat` requires that for each field `i` of the target variant
`variants[variantIdx]`:
* either field `i` has the same `StructFieldDesc` as field `i` of the active
  variant `variants[v_act]` (e.g. a fieldless target variant, a prefix payload
  `V2 -> V1`, or a shared prefix field of `V1 -> V2`), or
* `get? fieldVals i = none` and at least one byte in field `i`'s slice is
  uninitialized (`EnumLocalByteUninit m dstIdx b`), as when `SetDiscriminant`
  switches from a narrower variant to a wider variant (`V1 -> V2`). In that
  case, shared prefix fields remain readable via
  `evalProjection_downcast_field_simulation` while reading the uninitialized
  trailing field `i` raises UB in lockstep in both Anneal and `lean-miri`.

`hnot_uninit` excludes an `.uninit` `_dst`, where the machines disagree:
Anneal reports UB, but `writeDiscriminant` forces the local into memory and
writes the tag. `step_setDiscriminant_uninit_divergence` states that case. -/
theorem step_setDiscriminant_simulation
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_3 body env allocBudget s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    (henv_valid : ∀ t tb vs, env t = some (tb, vs) → ValidEnumLayout t body.layouts tb vs)
    {bb : BasicBlockData} {stmt : Statement}
    {dstIdx : Local} {dstDecl : LocalDecl} {variantIdx : Nat}
    {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hkind : stmt.kind = .setDiscriminant ⟨dstIdx, .nil⟩ variantIdx)
    (hdst_decl : get? body.localDecls dstIdx = some dstDecl)
    (henv_dst : env dstDecl.ty = some (tagBytes, variants))
    (hv_lt : variantIdx < variants.length)
    (hnot_uninit : get? s.frame.locals dstIdx ≠ some .uninit)
    (hpayload_compat :
      ∀ v_act (hv_act : v_act < variants.length) fieldVals,
        get? s.frame.locals dstIdx = some (.init (.aggregate v_act fieldVals)) →
        ∀ i (hi : i < (variants[variantIdx]'hv_lt).length),
          (∃ (hi_act : i < (variants[v_act]'hv_act).length),
            (variants[variantIdx]'hv_lt)[i]'hi = (variants[v_act]'hv_act)[i]'hi_act) ∨
          (get? fieldVals i = none ∧
            ∃ b,
              ((variants[variantIdx]'hv_lt)[i]'hi).offset.bytes.toNat ≤ b ∧
              b < ((variants[variantIdx]'hv_lt)[i]'hi).offset.bytes.toNat +
                ((variants[variantIdx]'hv_lt)[i]'hi).fieldLayout.size.bytes.toNat ∧
              EnumLocalByteUninit m dstIdx b)) :
    StepRelLM2_3 body env allocBudget m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_3 body.localDecls body.layouts) () m) ∧
    (∀ enumId b,
      (enumId ≠ dstIdx ∨
        (tagBytes ≤ b ∧ b < (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat)) →
      EnumLocalByteUninit m enumId b →
      EnumLocalByteUninit
        (Miri.Interpreter.Step.step (annealStepHooksLM2_3 body.localDecls body.layouts) () m).1
        enumId b) ∧
    (∀ j,
      IsImmediateStepLocal m j →
      IsImmediateStepLocal
        (Miri.Interpreter.Step.step (annealStepHooksLM2_3 body.localDecls body.layouts) () m).1
        j) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe, halloc,
      hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hvalid_enum := henv_valid dstDecl.ty tagBytes variants henv_dst
  obtain ⟨slot_d, mls_d, hlt_d, hslot_d, hmls_d_eq, hloc_d⟩ := hframe.lookup_local hdst_decl
  have hlt_af : dstIdx < s.frame.locals.length := by
    have hs := hslot_d; unfold get? at hs; exact (List.getElem?_eq_some_iff.mp hs).1
  have hcache_d : ∀ l, (topFrame.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.layout_eq
  let tf₀ := cacheFrameLocalLayout topFrame dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  let m₀ : AnnealStepState := { m with stack := ⟨#[tf₀]⟩ }
  have heval_dst := annealEvalPlace_unprojected hframes hlt_d hdst_decl hcache_d
  have hframe₀ := hframe.cache_local_layout hdst_decl hlt_d
  have hdisj₀ := MemoryAllocDisjoint_cacheFrameLocalLayout hdisj hlt_d
    (translateTy dstDecl.ty body.layouts)
  have hlt_d0 : dstIdx < tf₀.locals.size := by
    dsimp [tf₀, cacheFrameLocalLayout]; rw [Array.size_set]; exact hlt_d
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
  have hm_base :
      Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_3 body.localDecls body.layouts) () (translateStmt stmt) m =
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.Discriminant.writeDiscriminant
          (annealDiscriminantHooksLM2_3 body.localDecls body.layouts) () variantIdx destPlace)
        m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    rw [hkind]
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
      annealStepHooksLM2_3, annealStepHooksLM2_2, annealStepHooks]
    unfold Miri.Interpreter.runRvalue
    rw [heval_dst]
  cases hloc_d with
  | base _ _ hnone _ =>
    rw [henv_dst] at hnone; cases hnone
  | enumDead _ _ c_d _ _ _ =>
    have hdead₀ :
        tf₀.locals[dstIdx]'hlt_d0 = ⟨.dead, some (translateTy dstDecl.ty body.layouts)⟩ := by
      dsimp [tf₀, cacheFrameLocalLayout]
      simp only [Array.getElem_set, ↓reduceIte, hmls_d_eq]
    have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; rw [hkind]; simp [hslot_d]
    have hm_err :
        Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_3 body.localDecls body.layouts) () (translateStmt stmt) m =
        (m₀, .error (.undefinedBehavior "write to dead local")) := by
      rw [hm_base]
      unfold Miri.Interpreter.runRvalue
      rw [writeDiscriminant_dead_local_err body.localDecls (m := m₀) (tf := tf₀) rfl hlt_d0
        hdead₀ hvalid_enum hv_lt]
    rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
    exact ⟨.ub _ _, (fun _ _ _ hu => EnumLocalByteUninit.of_cache_layout hframes hu),
      (fun _ hj => IsImmediateStepLocal.of_cache_layout hframes hj)⟩
  | enumUninitImm _ _ _ _ _ _ =>
    exact absurd hslot_d hnot_uninit
  | enumUninitInd _ _ _ _ _ _ _ =>
    exact absurd hslot_d hnot_uninit
  | enumInd tb' vs' v_act fieldVals mp c_d henv' _ hmem_i =>
    rw [henv_dst] at henv'; injection henv' with heq_p; rcases heq_p with ⟨rfl, rfl⟩
    rcases hmem_i with ⟨allocId, borTag, baseAddr, localAlloc, words, _,
      _, hv_act_lt, hprov, hmis, hmeta, hlive, hbase, hptr, hovf, hmut, halign,
      hbs, hlen, hpmap, hmask, _, _, _, _, hpayload⟩
    have hind₀ :
        tf₀.locals[dstIdx]'hlt_d0 =
          ⟨.live (.indirect mp), some (translateTy dstDecl.ty body.layouts)⟩ := by
      dsimp [tf₀, cacheFrameLocalLayout]
      simp only [Array.getElem_set, ↓reduceIte, hmls_d_eq]
    obtain ⟨u, hu_lt, alloc', words', mscTag', hu_eq, hw_disc, hlive', hrelTag',
        hbs', hlen', hmut', hpmap', hmask', hbits', hraw', hinit', hread'⟩ :=
      writeDiscriminant_indirect_local_ok body.localDecls (m := m₀) (tf := tf₀)
        (iden := topFrame.localsIdentity) rfl hlt_d0 hind₀ hvalid_enum hv_lt
        hprov hmeta hlive hbase hptr hbs hlen hmut hpmap hmask
    let mach' := updateAllocMachine m.machine u allocId localAlloc.kind alloc'
    have hm_ok :
        Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_3 body.localDecls body.layouts) () (translateStmt stmt) m =
        ({ stack := ⟨#[tf₀]⟩, machine := mach' }, .ok ()) := by
      rw [hm_base]
      unfold Miri.Interpreter.runRvalue
      rw [hw_disc]
    have hset_af :
        set? s.frame.locals dstIdx (.init (.aggregate variantIdx fieldVals)) =
          some (s.frame.locals.set dstIdx (.init (.aggregate variantIdx fieldVals))) :=
      set?_eq_some_set hlt_af (.init (.aggregate variantIdx fieldVals))
    have ha_ok :
        evalStmt s stmt body.localDecls body.layouts =
          MirStepNode.step
            (advanceStmt s (s.frame.locals.set dstIdx (.init (.aggregate variantIdx fieldVals)))) := by
      unfold evalStmt; rw [hkind]
      simp only [hslot_d, hset_af]
    have hloc₀ : tf₀.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ :=
      hframe₀.location_eq
    rw [ha_ok, miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq hbb hstmt
      hm_ok rfl hloc₀]
    refine ⟨?_, ?_, ?_⟩
    · apply StepRelLM2_3.step
      -- Build `EnumMemRel mach'` for `(variantIdx, fieldVals)`
      have htb_valid := validScalarBytes_of_tagBytes hvalid_enum.tagBytes_valid
      have htb_nat := translateSizeBytes_toNat_eq htb_valid
      have htag_bits' : ∀ b, b < tagBytes → maskBlocksGetBit words' b = true := by
        intro b hb
        have hb_sz : b < localAlloc.allocation.byteSize.bytes.toNat := by
          rw [hbs]; have := hvalid_enum.size_ge_tag; omega
        rw [hbits' b hb_sz, decide_eq_true hb, Bool.or_true]
      have hpayload' :
          ∀ (i : Nat) (hi : i < (variants[variantIdx]'hv_lt).length),
            let f := (variants[variantIdx]'hv_lt)[i]'hi
            (∃ sc msc,
              get? fieldVals i = some (.scalar sc) ∧
              ScalarRel sc msc ∧
              f.fieldLayout.size = translateSizeBytes sc.sizeBytes ∧
              (f.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) ∧
              (f.ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) ∧
              (∀ b, f.offset.bytes.toNat ≤ b →
                b < f.offset.bytes.toNat + f.fieldLayout.size.bytes.toNat →
                maskBlocksGetBit words' b = true) ∧
              alloc'.initializationMask.isRangeInitialized
                (Miri.Memory.allocRange f.offset f.fieldLayout.size) = .ok (.ok ()) ∧
              alloc'.readScalar annealTargetDataLayout
                (Miri.Memory.allocRange f.offset f.fieldLayout.size) false =
                .ok (.fromScalarInt msc)) ∨
            (get? fieldVals i = none ∧
              ∃ b,
                f.offset.bytes.toNat ≤ b ∧
                b < f.offset.bytes.toNat + f.fieldLayout.size.bytes.toNat ∧
                maskBlocksGetBit words' b = false) := by
        have hpre := hpayload_compat v_act hv_act_lt fieldVals hslot_d
        obtain ⟨_, _, _, _, _, _, _, _, _, vars, _, _, hvf_all⟩ := hvalid_enum.table_entry
        intro i hi
        rcases hpre i hi with ⟨hi_act, hf_eq⟩ | ⟨hget_none, b_u, hb_ge, hb_lt, huninit_b⟩
        · have hvf_act := hvf_all v_act hv_act_lt
          have hbnd_i :
              ((variants[v_act]'hv_act_lt)[i]'hi_act).offset.bytes.toNat +
                ((variants[v_act]'hv_act_lt)[i]'hi_act).fieldLayout.size.bytes.toNat ≤
                localAlloc.allocation.byteSize.bytes.toNat := by
            rw [hbs]; exact hvf_act.fields_in_bounds i hi_act
          have hafter_i := hvf_act.fields_after_tag i hi_act
          rcases hpayload i hi_act with
            ⟨sc, msc, hfv_i, hrel_i, hsz_i, hbool_i, hchar_i, hbits_i, hinit_i, hread_i⟩ |
            ⟨hget_none, b_u, hb_ge, hb_lt, hbit_false⟩
          · have hpos_i :
                0 < ((variants[v_act]'hv_act_lt)[i]'hi_act).fieldLayout.size.bytes.toNat := by
              rw [hsz_i, translateSizeBytes_toNat_eq hrel_i.validBytes]
              rcases hrel_i.validBytes with h | h | h | h | h <;> omega
            have hbits_i' :
                ∀ b, ((variants[v_act]'hv_act_lt)[i]'hi_act).offset.bytes.toNat ≤ b →
                  b < ((variants[v_act]'hv_act_lt)[i]'hi_act).offset.bytes.toNat +
                    ((variants[v_act]'hv_act_lt)[i]'hi_act).fieldLayout.size.bytes.toNat →
                  maskBlocksGetBit words' b = true := by
              intro b hb1 hb2
              rw [hbits' b (by omega), hbits_i b hb1 hb2, Bool.true_or]
            have hinit_i' :
                alloc'.initializationMask.isRangeInitialized
                  (Miri.Memory.allocRange ((variants[v_act]'hv_act_lt)[i]'hi_act).offset
                    ((variants[v_act]'hv_act_lt)[i]'hi_act).fieldLayout.size) = .ok (.ok ()) :=
              initMaskWordRel_isRangeInitialized hmask' hpos_i hbnd_i hbits_i'
            have hrawA_len :
                (lm22AllocRaw localAlloc.allocation).size =
                  localAlloc.allocation.byteSize.bytes.toNat := by
              have : (lm22AllocRaw localAlloc.allocation).size = localAlloc.allocation.len := by
                cases localAlloc.allocation; rfl
              rw [this, hlen]
            have hrawA'_len :
                (lm22AllocRaw alloc').size = alloc'.byteSize.bytes.toNat := by
              have : (lm22AllocRaw alloc').size = alloc'.len := by cases alloc'; rfl
              rw [this, hlen', hbs', hlen]
            have hread_i' :
                alloc'.readScalar annealTargetDataLayout
                  (Miri.Memory.allocRange ((variants[v_act]'hv_act_lt)[i]'hi_act).offset
                    ((variants[v_act]'hv_act_lt)[i]'hi_act).fieldLayout.size) false =
                .ok (.fromScalarInt msc) := by
              rw [← hread_i]
              apply alloc_readScalar_congr hrawA_len hrawA'_len hbs' hinit_i hinit_i' hbnd_i
              have hex := extract_writeBytes_disjoint (lm22AllocRaw localAlloc.allocation)
                (lm22LeBytes variantIdx (translateSizeBytes tagBytes).bytes.toNat)
                (lm22LeBytes_size _ _)
                (by rw [Nat.zero_add, hrawA_len, hbs, htb_nat]; exact hvalid_enum.size_ge_tag)
                (by rw [hrawA_len]; exact hbnd_i)
                (Or.inr (by rw [Nat.zero_add, htb_nat]; exact hafter_i))
              rw [Nat.zero_add] at hex
              rw [hraw']
              exact hex
            dsimp only
            rw [hf_eq]
            exact Or.inl ⟨sc, msc, hfv_i, hrel_i, hsz_i, hbool_i, hchar_i, hbits_i', hinit_i', hread_i'⟩
          · have hb_sz : b_u < localAlloc.allocation.byteSize.bytes.toNat := by omega
            have hnot_lt_tb : decide (b_u < tagBytes) = false := decide_eq_false (by omega)
            have hbit_false' : maskBlocksGetBit words' b_u = false := by
              rw [hbits' b_u hb_sz, hbit_false, hnot_lt_tb]; rfl
            dsimp only
            rw [hf_eq]
            exact Or.inr ⟨hget_none, b_u, hb_ge, hb_lt, hbit_false'⟩
        · have hvf_tgt := hvf_all variantIdx hv_lt
          have hbnd_tgt :
              ((variants[variantIdx]'hv_lt)[i]'hi).offset.bytes.toNat +
                ((variants[variantIdx]'hv_lt)[i]'hi).fieldLayout.size.bytes.toNat ≤
                localAlloc.allocation.byteSize.bytes.toNat := by
            rw [hbs]; exact hvf_tgt.fields_in_bounds i hi
          have hafter_tgt := hvf_tgt.fields_after_tag i hi
          have hu₀ : EnumLocalByteUninit m₀ dstIdx b_u :=
            EnumLocalByteUninit.of_cache_layout hframes huninit_b
          have hmls_d0 :
              tf₀.locals[dstIdx]? =
                some ⟨.live (.indirect mp), some (translateTy dstDecl.ty body.layouts)⟩ := by
            rw [Array.getElem?_eq_getElem hlt_d0, hind₀]
          have hold_false := hu₀ tf₀ mp _ allocId borTag localAlloc rfl hmls_d0 hprov hlive.1
          have hb_sz : b_u < localAlloc.allocation.byteSize.bytes.toNat := by omega
          rw [initMaskWordRel_get hmask hb_sz] at hold_false
          injection hold_false with hbit_old
          have hnot_lt_tb : decide (b_u < tagBytes) = false := decide_eq_false (by omega)
          have hbit_false' : maskBlocksGetBit words' b_u = false := by
            rw [hbits' b_u hb_sz, hbit_old, hnot_lt_tb]; rfl
          exact Or.inr ⟨hget_none, b_u, hb_ge, hb_lt, hbit_false'⟩
      have hmem_new :
          EnumMemRel mach' dstDecl.ty body.layouts tagBytes variants variantIdx fieldVals mp :=
        .mk allocId borTag baseAddr ⟨localAlloc.kind, alloc'⟩ words' mscTag'
          hvalid_enum hv_lt hprov hmis hmeta hlive' hbase hptr hovf hmut' halign
          (hbs'.trans hbs) (hlen'.trans (hlen.trans (by rw [hbs']))) hpmap'
          (by rw [hbs']; exact hmask') hrelTag' htag_bits' hinit' hread' hpayload'
      have hc_some :
          ∀ l ∈ (some (translateTy dstDecl.ty body.layouts)),
            l = translateTy dstDecl.ty body.layouts :=
        fun _ hl => (Option.some.inj (Option.mem_def.mp hl)).symm
      have hloc_new :
          LocalRelLM2_3 env mach' dstDecl body.layouts
            (.init (.aggregate variantIdx fieldVals)) (tf₀.locals[dstIdx]'hlt_d0) := by
        rw [hind₀]
        exact .enumInd tagBytes variants variantIdx fieldVals mp _ henv_dst hc_some hmem_new
      have hfr_mach' :
          FrameRelLM2_3 body env mach'
            { s.frame with locals := s.frame.locals.set dstIdx (.init (.aggregate variantIdx fieldVals)) }
            tf₀ := by
        refine ⟨hframe₀.body_eq, hframe₀.location_eq, ?_, hframe₀.mf_locals_size, ?_⟩
        · unfold length; rw [List.length_set]; exact hframe₀.af_locals_len
        · intro j d sl mls hd hs hm
          dsimp only at hs
          by_cases hj : dstIdx = j
          · subst hj
            rw [hdst_decl] at hd; injection hd with hd_eq; subst hd_eq
            unfold get? at hs; rw [List.getElem?_set_self hlt_af] at hs
            injection hs with hs_eq; subst hs_eq
            rw [Array.getElem?_eq_getElem hlt_d0] at hm; injection hm with hm_eq; subst hm_eq
            exact hloc_new
          · unfold get? at hs; simp only [List.getElem?_set, hj, ↓reduceIte] at hs
            have hrel_old := hframe₀.locals_rel j d sl mls hd hs hm
            refine hrel_old.of_updateAlloc_ne hu_lt hu_eq ?_
            intro mp' hval'
            have hmls_d0_get :
                tf₀.locals[dstIdx]? =
                  some ⟨.live (.indirect mp), some (translateTy dstDecl.ty body.layouts)⟩ := by
              rw [Array.getElem?_eq_getElem hlt_d0, hind₀]
            have hmls_j_get : tf₀.locals[j]? = some ⟨.live (.indirect mp'), mls.layout⟩ := by
              rw [hm]; cases mls; dsimp at hval' ⊢; subst hval'; rfl
            have hdisj_ne := hdisj₀ j dstIdx mp' mp mls.layout _ (Ne.symm hj) hmls_j_get hmls_d0_get
            rwa [hprov] at hdisj_ne
      exact StateRelLM2_3.mk
        { tf₀ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
        rfl hretCont ⟨retLay, hretPlace⟩
        hfr_mach'.step_pc
        (halloc.of_updateAlloc hu_lt hu_eq)
        hcal hstack hbor hprot hcaller hdisj₀
    · -- Preserve `EnumLocalByteUninit` outside `[0, tagBytes)` of `dstIdx`.
      intro enumId b hcond hu
      have hu₀ : EnumLocalByteUninit m₀ enumId b :=
        EnumLocalByteUninit.of_cache_layout hframes hu
      apply EnumLocalByteUninit.of_set_location
        (m := { stack := ⟨#[tf₀]⟩, machine := mach' }) rfl
      intro tf' mp' c' id' bt' la' hf' hloc' hprov' hfind'
      injection hf' with hf_arr; injection hf_arr with htf_eq; subst htf_eq
      by_cases heq_id : enumId = dstIdx
      · subst heq_id
        rcases hcond with hne | ⟨hb_ge, hb_lt⟩
        · exact False.elim (hne rfl)
        rw [Array.getElem?_eq_getElem hlt_d0, hind₀] at hloc'
        injection hloc' with hls_eq
        have hmp_eq : mp = mp' := by
          injection hls_eq with hv_eq; injection hv_eq with ho_eq
          injection ho_eq
        cases hmp_eq
        rw [hprov] at hprov'; injection hprov' with hp_eq; injection hp_eq with hid_eq _
        subst hid_eq
        have hlive_find' :
            mach'.memory.live.find? (fun (k, _) => k == allocId) =
              some (allocId, ⟨localAlloc.kind, alloc'⟩) := hlive'.1
        rw [hlive_find'] at hfind'
        injection hfind' with hpair_eq; injection hpair_eq with _ hla_eq; subst hla_eq
        have hmls_d0 :
            tf₀.locals[enumId]? =
              some ⟨.live (.indirect mp), some (translateTy dstDecl.ty body.layouts)⟩ := by
          rw [Array.getElem?_eq_getElem hlt_d0, hind₀]
        have hold_false := hu₀ tf₀ mp _ allocId borTag localAlloc rfl hmls_d0 hprov hlive.1
        have hb_sz : b < localAlloc.allocation.byteSize.bytes.toNat := by rw [hbs]; exact hb_lt
        rw [initMaskWordRel_get hmask hb_sz] at hold_false
        injection hold_false with hbit_old
        have hnot_lt_tb : decide (b < tagBytes) = false :=
          decide_eq_false (by omega)
        dsimp only
        rw [initMaskWordRel_get hmask' hb_sz]
        congr 1
        rw [hbits' b hb_sz, hbit_old, hnot_lt_tb]
        rfl
      · -- `enumId ≠ dstIdx`: `id' ≠ allocId` by `MemoryAllocDisjoint`.
        have hmls_d0 :
            tf₀.locals[dstIdx]? =
              some ⟨.live (.indirect mp), some (translateTy dstDecl.ty body.layouts)⟩ := by
          rw [Array.getElem?_eq_getElem hlt_d0, hind₀]
        have hdisj_ne := hdisj₀ enumId dstIdx mp' mp c' _ heq_id hloc' hmls_d0
        have hid_ne : id' ≠ allocId := by
          intro hid_eq; apply hdisj_ne; rw [hprov', hprov, hid_eq]; rfl
        have hfind_old :
            m.machine.memory.live.find? (fun (k, _) => k == id') = some (id', la') := by
          dsimp [mach', updateAllocMachine] at hfind'
          obtain ⟨hbeq_id, idx_f, hlt_f, hget_f, hnot_before⟩ :=
            Array.find?_eq_some_iff_getElem.mp hfind'
          have hlt_orig : idx_f < m.machine.memory.live.size := by
            rwa [Array.size_setIfInBounds] at hlt_f
          have hne_u : idx_f ≠ u := by
            intro rfl
            rw [Array.getElem_setIfInBounds_self] at hget_f
            injection hget_f with hk_eq
            exact hid_ne hk_eq.symm
          rw [Array.getElem_setIfInBounds_ne hlt_orig (Ne.symm hne_u)] at hget_f
          rw [Array.find?_eq_some_iff_getElem]
          refine ⟨hbeq_id, idx_f, hlt_orig, hget_f, ?_⟩
          intro j hj
          by_cases hju : j = u
          · subst hju
            rw [hu_eq]
            simp [Ne.symm hid_ne]
          · have hprev := hnot_before j hj
            rwa [Array.getElem_setIfInBounds_ne (Nat.lt_trans hj hlt_orig) (Ne.symm hju)] at hprev
        exact hu₀ tf₀ mp' c' id' bt' la' rfl hloc' hprov' hfind_old
    · intro j hj
      have hj₀ : IsImmediateFrameLocal tf₀ j :=
        (hj topFrame hframes).cache_layout hlt_d (translateTy dstDecl.ty body.layouts)
      exact IsImmediateStepLocal.of_set_location
        (m := { stack := ⟨#[tf₀]⟩, machine := mach' }) rfl
        (fun tf' hf' => by injection hf' with ha; injection ha with ht; subst ht; exact hj₀)

/-- **`step_setDiscriminant_uninit_divergence`**: `SetDiscriminant(_dst,
variantIdx)` on an `.uninit` enum local is where Anneal and lean-miri disagree.

Anneal's `evalStmt` requires the local to hold an initialized aggregate already
and otherwise reports UB. Vendored `Discriminant.writeDiscriminant`, like
rustc's `write_discriminant` for a direct tag, never reads the destination: it
forces the local into memory if needed and writes the tag, so lean-miri
completes the step. Anneal is therefore stricter than Miri here. That is
conservative for verification, because Anneal rejects a program that Miri
accepts rather than the reverse, but it is not lockstep simulation, so
`step_setDiscriminant_simulation` excludes this case. -/
theorem step_setDiscriminant_uninit_divergence
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_3 body env (allocBudget + 1) s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    (henv_valid : ∀ t tb vs, env t = some (tb, vs) → ValidEnumLayout t body.layouts tb vs)
    {bb : BasicBlockData} {stmt : Statement}
    {dstIdx : Local} {dstDecl : LocalDecl} {variantIdx : Nat}
    {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hkind : stmt.kind = .setDiscriminant ⟨dstIdx, .nil⟩ variantIdx)
    (hdst_decl : get? body.localDecls dstIdx = some dstDecl)
    (henv_dst : env dstDecl.ty = some (tagBytes, variants))
    (hv_lt : variantIdx < variants.length)
    (huninit : get? s.frame.locals dstIdx = some .uninit) :
    stepMirFn body s = .fail .ub ∧
    ∃ m', Miri.Interpreter.Step.step
      (annealStepHooksLM2_3 body.localDecls body.layouts) () m = (m', .ok true) := by
  rcases hstate with
    ⟨topFrame, hframes, _, _, hframe, halloc, hcal, _, _, _, _, _⟩
  have hvalid_enum := henv_valid dstDecl.ty tagBytes variants henv_dst
  obtain ⟨slot_d, mls_d, hlt_d, hslot_d, hmls_d_eq, hloc_d⟩ := hframe.lookup_local hdst_decl
  rw [huninit] at hslot_d
  injection hslot_d with hslot_eq
  subst hslot_eq
  have ha_ub : stepMirFn body s = .fail .ub := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt; rw [hkind]; simp [huninit]
  refine ⟨ha_ub, ?_⟩
  have hcache_d : ∀ l, (topFrame.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.layout_eq
  let tf₀ := cacheFrameLocalLayout topFrame dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  let m₀ : AnnealStepState := { m with stack := ⟨#[tf₀]⟩ }
  have heval_dst := annealEvalPlace_unprojected hframes hlt_d hdst_decl hcache_d
  have hlt_d0 : dstIdx < tf₀.locals.size := by
    dsimp [tf₀, cacheFrameLocalLayout]; rw [Array.size_set]; exact hlt_d
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
  have hm_base :
      Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_3 body.localDecls body.layouts) () (translateStmt stmt) m =
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.Discriminant.writeDiscriminant
          (annealDiscriminantHooksLM2_3 body.localDecls body.layouts) () variantIdx destPlace)
        m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    rw [hkind]
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
      annealStepHooksLM2_3, annealStepHooksLM2_2, annealStepHooks]
    unfold Miri.Interpreter.runRvalue
    rw [heval_dst]
  -- Both `.uninit` representations accept the tag write and keep a single
  -- frame at the same location.
  have hw : ∃ m', Miri.Interpreter.Discriminant.writeDiscriminant
        (annealDiscriminantHooksLM2_3 body.localDecls body.layouts) () variantIdx
        destPlace m₀ = .ok () m' ∧
      ∃ tf', m'.stack.frames = #[tf'] ∧ tf'.location = tf₀.location := by
    cases hloc_d with
    | base _ _ hnone _ =>
      rw [henv_dst] at hnone; cases hnone
    | enumUninitImm _ _ _ _ _ _ =>
      have himm₀ : tf₀.locals[dstIdx]'hlt_d0 =
          ⟨.live (.immediate .uninit), some (translateTy dstDecl.ty body.layouts)⟩ := by
        dsimp [tf₀, cacheFrameLocalLayout]
        simp only [Array.getElem_set, ↓reduceIte, hmls_d_eq]
      exact writeDiscriminant_uninit_imm_local_ok body.localDecls (m := m₀) (tf := tf₀)
        rfl hlt_d0 himm₀ hvalid_enum hv_lt halloc
    | enumUninitInd tb' vs' mp _ henv' _ hmem_u =>
      rw [henv_dst] at henv'; injection henv' with heq_p; rcases heq_p with ⟨rfl, rfl⟩
      rcases hmem_u with ⟨allocId, borTag, baseAddr, localAlloc, _, hprov, _, hmeta,
        hlive, hbase, hptr, _, hmut, _, hbs, hlen, hpmap, hmask_u⟩
      have hind₀ : tf₀.locals[dstIdx]'hlt_d0 =
          ⟨.live (.indirect mp), some (translateTy dstDecl.ty body.layouts)⟩ := by
        dsimp [tf₀, cacheFrameLocalLayout]
        simp only [Array.getElem_set, ↓reduceIte, hmls_d_eq]
      have hmask₀ : InitMaskWordRel localAlloc.allocation.initializationMask
          localAlloc.allocation.byteSize
          (initWordsFalse (translateTy dstDecl.ty body.layouts).layout.size) := by
        rw [hmask_u, hbs]
        exact initMaskWordRel_new_false
      obtain ⟨_, _, _, _, _, _, hw_disc, _⟩ :=
        writeDiscriminant_indirect_local_ok body.localDecls (m := m₀) (tf := tf₀)
          (iden := topFrame.localsIdentity) rfl hlt_d0 hind₀ hvalid_enum hv_lt
          hprov hmeta hlive hbase hptr hbs hlen hmut hpmap hmask₀
      exact ⟨_, hw_disc, tf₀, rfl, rfl⟩
  obtain ⟨m', hw_ok, tf', hframes', hloc'⟩ := hw
  have hm_ok :
      Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_3 body.localDecls body.layouts) () (translateStmt stmt) m =
      (m', .ok ()) := by
    rw [hm_base]
    unfold Miri.Interpreter.runRvalue
    rw [hw_ok]
  have hloc₀ : tf₀.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ :=
    (hframe.cache_local_layout hdst_decl hlt_d).location_eq
  exact ⟨_, miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq hbb hstmt
    hm_ok hframes' (hloc'.trans hloc₀)⟩

/-! ## 6. Multi-Variant Enum Construction (`LM-2.3` Deliverable 1) -/

private theorem IsPrimScalarTy.isSized_lm2_3 {ty : Ty} (h : IsPrimScalarTy ty)
    (layouts : LayoutTable) :
    (translateTy ty layouts).layout.isSized = true := by
  rcases ty with ⟨kind, lIdx⟩
  rcases h with hk | hk | ⟨k, hk⟩ | ⟨k, hk⟩ <;> dsimp only at hk <;> subst hk
  · rfl
  · rfl
  · cases k <;> rfl
  · cases k <;> rfl

private theorem IsPrimScalarTy.usesStructMemCopyDest_false_lm2_3 {ty : Ty}
    (h : IsPrimScalarTy ty) (layouts : LayoutTable)
    (ref : Miri.Interpreter.RuntimePlaceRef AnnealProv) :
    usesStructMemCopyDest ⟨ref, translateTy ty layouts⟩ = false := by
  rcases ty with ⟨kind, lIdx⟩
  rcases h with hk | hk | ⟨k, hk⟩ | ⟨k, hk⟩ <;> dsimp only at hk <;> subst hk
  · rfl
  · rfl
  · cases k <;> rfl
  · cases k <;> rfl

private theorem translateSizeBytes_pos_lm2_3 {n : Nat} (h : ValidScalarBytes n) :
    0 < (translateSizeBytes n).bytes.toNat := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

/-- `FrameRelLM2_3` with a single local `excl` temporarily excluded while its
backing enum stack allocation is being populated field-by-field. -/
private structure FrameRelLM2_3Except
    (body : CapturedMir)
    (env : EnumTypeEnv)
    (excl : Local)
    (mach : AnnealMachine)
    (af : StackFrame)
    (mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    Prop where
  body_eq : mf.body = translateBody body
  location_eq : mf.location = .mir ⟨af.blockIdx, af.stmtIdx⟩
  af_locals_len : length af.locals = length body.localDecls
  mf_locals_size : mf.locals.size = length body.localDecls
  locals_rel :
    ∀ (idx : Nat) (decl : LocalDecl) (slot : LocalSlot)
      (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout),
      idx ≠ excl →
      get? body.localDecls idx = some decl →
      get? af.locals idx = some slot →
      mf.locals[idx]? = some mls →
      LocalRelLM2_3 env mach decl body.layouts slot mls

namespace FrameRelLM2_3Except

private theorem of_frameRel {body : CapturedMir} {env : EnumTypeEnv}
    {excl : Local} {mach : AnnealMachine} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM2_3 body env mach af mf) :
    FrameRelLM2_3Except body env excl mach af mf :=
  ⟨h.body_eq, h.location_eq, h.af_locals_len, h.mf_locals_size,
    fun idx d sl ml _ hd hs hm => h.locals_rel idx d sl ml hd hs hm⟩

private theorem lookup_local {body : CapturedMir} {env : EnumTypeEnv}
    {excl : Local} {mach : AnnealMachine} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM2_3Except body env excl mach af mf)
    {idx : Nat} {decl : LocalDecl}
    (hne : idx ≠ excl)
    (hdecl : get? body.localDecls idx = some decl) :
    ∃ (slot : LocalSlot)
      (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)
      (hlt : idx < mf.locals.size),
      get? af.locals idx = some slot ∧
      mf.locals[idx]'hlt = mls ∧
      LocalRelLM2_3 env mach decl body.layouts slot mls := by
  have hidx_decls : idx < length body.localDecls := by
    unfold get? at hdecl; unfold length
    exact (List.getElem?_eq_some_iff.mp hdecl).1
  have hidx_af : idx < af.locals.length := by
    have hlen := h.af_locals_len
    unfold length at hlen hidx_decls
    omega
  have hlt : idx < mf.locals.size := by
    rw [h.mf_locals_size]; exact hidx_decls
  have haf_get : get? af.locals idx = some (af.locals[idx]'hidx_af) := by
    unfold get?; exact List.getElem?_eq_getElem hidx_af
  have hmf_get : mf.locals[idx]? = some (mf.locals[idx]'hlt) :=
    Array.getElem?_eq_getElem hlt
  exact ⟨af.locals[idx]'hidx_af, mf.locals[idx]'hlt, hlt, haf_get, rfl,
    h.locals_rel idx decl _ _ hne hdecl haf_get hmf_get⟩

private theorem cache_local_layout {body : CapturedMir} {env : EnumTypeEnv}
    {excl : Local} {mach : AnnealMachine} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM2_3Except body env excl mach af mf)
    {idx : Nat} {decl : LocalDecl}
    (hne : idx ≠ excl)
    (hdecl : get? body.localDecls idx = some decl)
    (hlt : idx < mf.locals.size) :
    FrameRelLM2_3Except body env excl mach af
      (cacheFrameLocalLayout mf idx hlt (translateTy decl.ty body.layouts)) := by
  refine ⟨h.body_eq, h.location_eq, h.af_locals_len, ?_, ?_⟩
  · dsimp [cacheFrameLocalLayout]; rw [Array.size_set]; exact h.mf_locals_size
  · intro j d s mls hj_ne hd hs hm
    dsimp [cacheFrameLocalLayout] at hm
    by_cases hij : idx = j
    · subst hij
      rw [hdecl] at hd
      injection hd with hd_eq; subst hd_eq
      rw [Array.getElem?_set_self hlt] at hm
      injection hm with hm_eq; subst hm_eq
      have hmf_old : mf.locals[idx]? = some (mf.locals[idx]'hlt) :=
        Array.getElem?_eq_getElem hlt
      exact (h.locals_rel idx decl s _ hne hdecl hs hmf_old).cache_layout
    · simp only [Array.getElem?_set, hij, ↓reduceIte] at hm
      exact h.locals_rel j d s mls hj_ne hd hs hm

private theorem of_stackAlloc_set_excl {body : CapturedMir} {env : EnumTypeEnv}
    {dstIdx : Local} {mach : AnnealMachine} {mem' : AnnealMemory}
    {newId : Miri.Memory.AllocId}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM2_3Except body env dstIdx mach af mf)
    (hres : mach.memory.reserveAllocId = (mem', .ok newId))
    {hlt : dstIdx < mf.locals.size}
    (mls' : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
    FrameRelLM2_3Except body env dstIdx (stackAllocMachine mach mem' newId alloc) af
      { mf with locals := mf.locals.set dstIdx mls' hlt } := by
  refine ⟨h.body_eq, h.location_eq, h.af_locals_len, by simp [h.mf_locals_size], ?_⟩
  intro i d sl ml hne hd hs hm
  rw [Array.getElem?_set_ne _ (Ne.symm hne)] at hm
  exact (h.locals_rel i d sl ml hne hd hs hm).of_stackAlloc_other hres

private theorem of_updateAlloc_excl {body : CapturedMir} {env : EnumTypeEnv}
    {dstIdx : Local} {mach : AnnealMachine} {u : Nat}
    {allocId : Miri.Memory.AllocId} {oldLa : AnnealLocalAlloc}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {c : Option Miri.Interpreter.LocalLayout}
    {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM2_3Except body env dstIdx mach af mf)
    (hdisj : MemoryAllocDisjoint mf)
    {hlt : dstIdx < mf.locals.size}
    (hdst : mf.locals[dstIdx]'hlt = ⟨.live (.indirect mp), c⟩)
    {borTag : Miri.Memory.BorTag}
    (hprov : mp.ptr.provenance = some (.concrete allocId borTag))
    (hu_lt : u < mach.memory.live.size)
    (hu_eq : mach.memory.live[u]'hu_lt = (allocId, oldLa)) :
    FrameRelLM2_3Except body env dstIdx (updateAllocMachine mach u allocId kind alloc') af mf := by
  refine ⟨h.body_eq, h.location_eq, h.af_locals_len, h.mf_locals_size, ?_⟩
  intro i d sl ml hne hd hs hm
  apply (h.locals_rel i d sl ml hne hd hs hm).of_updateAlloc_ne hu_lt hu_eq
  intro mp' hv
  have hml_eq : ml = ⟨.live (.indirect mp'), ml.layout⟩ := by
    cases ml; dsimp at hv ⊢; rw [hv]
  rw [hml_eq] at hm
  have hdst_get : mf.locals[dstIdx]? = some ⟨.live (.indirect mp), c⟩ := by
    rw [Array.getElem?_eq_getElem hlt, hdst]
  have hd_ids := hdisj i dstIdx mp' mp ml.layout c hne hm hdst_get
  have hmp_id : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some allocId := by
    rw [hprov]; rfl
  rwa [hmp_id] at hd_ids

private theorem finish_dst {body : CapturedMir} {env : EnumTypeEnv}
    {dstIdx : Local} {dstDecl : LocalDecl} {mach : AnnealMachine}
    {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {newSlot : LocalSlot}
    {newMls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    {locals' : List LocalSlot}
    (h : FrameRelLM2_3Except body env dstIdx mach af mf)
    (hdecl : get? body.localDecls dstIdx = some dstDecl)
    (hset : set? af.locals dstIdx newSlot = some locals')
    (hmf_dst : mf.locals[dstIdx]? = some newMls)
    (hnew : LocalRelLM2_3 env mach dstDecl body.layouts newSlot newMls) :
    FrameRelLM2_3 body env mach { af with locals := locals' } mf := by
  unfold set? at hset
  split at hset
  case isFalse => cases hset
  case isTrue hidx_af =>
    injection hset with hlocals_eq
    subst hlocals_eq
    refine ⟨h.body_eq, h.location_eq, ?_, h.mf_locals_size, ?_⟩
    · unfold length at *; rw [List.length_set]; exact h.af_locals_len
    · intro j d s mls hd hs hm
      dsimp only at hs
      by_cases hij : dstIdx = j
      · subst hij
        rw [hdecl] at hd; injection hd with hd_eq; subst hd_eq
        unfold get? at hs
        rw [List.getElem?_set_self hidx_af] at hs
        injection hs with hs_eq; subst hs_eq
        rw [hmf_dst] at hm; injection hm with hm_eq; subst hm_eq
        exact hnew
      · unfold get? at hs
        simp only [List.getElem?_set, hij, ↓reduceIte] at hs
        exact h.locals_rel j d s mls (Ne.symm hij) hd hs hm

end FrameRelLM2_3Except

private theorem MemoryAllocDisjoint_set_fresh_stackAlloc_lm2_3
    {body : CapturedMir} {env : EnumTypeEnv} {dstIdx : Local}
    {mach : AnnealMachine} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {id : Miri.Memory.AllocId}
    {lay : Option Miri.Interpreter.LocalLayout}
    (hfr : FrameRelLM2_3Except body env dstIdx mach af mf)
    (hdisj : MemoryAllocDisjoint mf)
    (hfresh : mach.memory.live.any (fun entry => entry.1 == id) = false)
    (hlt : dstIdx < mf.locals.size) :
    MemoryAllocDisjoint
      { mf with
        locals := mf.locals.set dstIdx
          ⟨.live (.indirect (stackAllocPlace id)), lay⟩ hlt } := by
  have helper : ∀ k mp_k lk, k ≠ dstIdx →
      mf.locals[k]? = some ⟨.live (.indirect mp_k), lk⟩ →
      mp_k.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id := by
    intro k mp_k lk hne hk_get heq
    obtain ⟨hlt_k, _⟩ := Array.getElem?_eq_some_iff.mp hk_get
    have hlt_d : k < body.localDecls.length := by
      have h1 : k < length body.localDecls := hfr.mf_locals_size ▸ hlt_k; exact h1
    have hlt_af : k < af.locals.length := by
      have h1 : k < length body.localDecls := hfr.mf_locals_size ▸ hlt_k
      have h2 : k < length af.locals := hfr.af_locals_len ▸ h1; exact h2
    have hdecl_k : get? body.localDecls k = some (body.localDecls[k]'hlt_d) := by
      unfold get?; exact List.getElem?_eq_getElem hlt_d
    have hsl_k : get? af.locals k = some (af.locals[k]'hlt_af) := by
      unfold get?; exact List.getElem?_eq_getElem hlt_af
    have hloc_k := hfr.locals_rel k _ _ _ hne hdecl_k hsl_k hk_get
    obtain ⟨id_k, hid_k, hany_k⟩ := hloc_k.allocLive mp_k rfl
    rw [heq] at hid_k
    injection hid_k with hid_eq; subst hid_eq
    rw [hfresh] at hany_k; cases hany_k
  intro i j mp₁ mp₂ l₁ l₂ hne hi hj
  by_cases hi_d : i = dstIdx
  · subst hi_d
    have hj_ne : j ≠ i := Ne.symm hne
    rw [Array.getElem?_set_self hlt] at hi
    injection hi with hi'; injection hi' with hmp1 _
    injection hmp1 with hmp1'; injection hmp1' with hmp1''; subst hmp1''
    rw [Array.getElem?_set_ne _ (Ne.symm hj_ne)] at hj
    have hid1 : (stackAllocPlace id).ptr.provenance.bind Miri.Memory.Provenance.getAllocId =
        some id := rfl
    rw [hid1]
    exact Ne.symm (helper j mp₂ l₂ hj_ne hj)
  · by_cases hj_d : j = dstIdx
    · subst hj_d
      rw [Array.getElem?_set_self hlt] at hj
      injection hj with hj'; injection hj' with hmp2 _
      injection hmp2 with hmp2'; injection hmp2' with hmp2''; subst hmp2''
      rw [Array.getElem?_set_ne _ (Ne.symm hi_d)] at hi
      have hid2 : (stackAllocPlace id).ptr.provenance.bind Miri.Memory.Provenance.getAllocId =
          some id := rfl
      rw [hid2]
      exact helper i mp₁ l₁ hi_d hi
    · rw [Array.getElem?_set_ne _ (Ne.symm hi_d)] at hi
      rw [Array.getElem?_set_ne _ (Ne.symm hj_d)] at hj
      exact hdisj i j mp₁ mp₂ l₁ l₂ hne hi hj

/-- Evaluating a `WellTypedEnumScalarOp` on a `FrameRelLM2_3Except` frame
(where `dstIdx` has an enum type in `env`) automatically avoids `dstIdx` by
disjointness of primitive scalar types and enum types, leaving
`tf.locals[dstIdx]?` unchanged. -/
private theorem evalEnumScalarOp_except_dst
    {body : CapturedMir} {env : EnumTypeEnv} {dstIdx : Local} {dstDecl : LocalDecl}
    {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    {af : StackFrame}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {m : AnnealStepState} {op : MirAst.Operand} {ty : Ty}
    (henv_valid : ∀ t tb vs, env t = some (tb, vs) → ValidEnumLayout t body.layouts tb vs)
    (hdst_decl : get? body.localDecls dstIdx = some dstDecl)
    (henv_dst : env dstDecl.ty = some (tagBytes, variants))
    (hframes : m.stack.frames = #[topFrame])
    (hframe : FrameRelLM2_3Except body env dstIdx m.machine af topFrame)
    (hop : WellTypedEnumScalarOp body topFrame op ty)
    (globals : List CapturedAllocation)
    (known : Option Miri.Interpreter.LocalLayout) :
    (∃ (sc : MirAst.ScalarInt) (msc : Miri.Memory.ScalarInt)
        (topFrame' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      evalOperand af.locals op .nil globals body.layouts .nil body.localDecls =
        .ok (.scalar sc) af.locals ∧
      validateLoadedValue body.layouts body.localDecls op (.scalar sc) = true ∧
      (annealEvalOperandLM2_3 body.localDecls body.layouts (translateOperand op) known >>=
        annealReadImmediateLM2_2) m =
        .ok ⟨.scalar (.fromScalarInt msc), translateTy ty body.layouts⟩
          { m with stack := ⟨#[topFrame']⟩ } ∧
      ScalarRel sc msc ∧
      (translateTy ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes ∧
      (ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) ∧
      (ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) ∧
      FrameRelLM2_3Except body env dstIdx m.machine af topFrame' ∧
      topFrame' = { topFrame with locals := topFrame'.locals } ∧
      topFrame'.locals.size = topFrame.locals.size ∧
      topFrame'.locals[dstIdx]? = topFrame.locals[dstIdx]? ∧
      (∀ (j : Nat), IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame' j) ∧
      (MemoryAllocDisjoint topFrame → MemoryAllocDisjoint topFrame') ∧
      (∀ localId b, EnumLocalByteUninit m localId b →
        EnumLocalByteUninit { m with stack := ⟨#[topFrame']⟩ } localId b)) ∨
    (∃ m' msg,
      evalOperand af.locals op .nil globals body.layouts .nil body.localDecls = .ub ∧
      (annealEvalOperandLM2_3 body.localDecls body.layouts (translateOperand op) known >>=
        annealReadImmediateLM2_2) m = .error (.undefinedBehavior msg) m') := by
  have hsame : { m with stack := ⟨#[topFrame]⟩ } = m :=
    stepState_with_same_singleton m topFrame hframes
  cases hop with
  | constScalar c sc hval hprim hsz hcan hlaysz hbool hchar =>
    obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hsz hcan
    have heval_a : evalOperand af.locals (.constant c) .nil globals body.layouts .nil body.localDecls =
        .ok (.scalar sc) af.locals := by
      unfold evalOperand; dsimp only; rw [hval]; rfl
    have heval_m :
        annealEvalOperandLM2_3 body.localDecls body.layouts
          (translateOperand (.constant c)) known m =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩ m := by
      with_unfolding_all
        unfold annealEvalOperandLM2_3 translateOperand translateConstOperand
          annealEvalOperand evalMirConstImmediate
        dsimp only
        rw [hval]
        simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
          EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
          stack_currentFrame?_singleton m.stack topFrame hframes, Option.isNone_some,
          Bool.false_eq_true, ↓reduceIte, htry, hprim.layoutOfEncoded]
    left
    refine ⟨sc, msc, topFrame, heval_a, rfl, ?_, hrel, hlaysz, hbool, hchar,
      hframe, rfl, rfl, rfl, (fun _ h => h), (fun h => h),
      (fun _ _ hu => by rw [hsame]; exact hu)⟩
    rw [EStateM.bind_eq_ok heval_m, hsame]
    rfl
  | copyLocal idx decl hdecl hprim himm =>
    have hnone := env_none_of_isPrimScalarTy henv_valid hprim
    have hne : idx ≠ dstIdx := by
      intro rfl
      rw [hdst_decl] at hdecl
      injection hdecl with hd_eq; subst hd_eq
      rw [hnone] at henv_dst; cases henv_dst
    obtain ⟨slot, mls, hlt_mf, hslot, hmls_eq, hloc⟩ := hframe.lookup_local hne hdecl
    have hloc_base := hloc.to_localRel_of_none hnone
    have hcache := hloc_base.layout_eq
    have hmls_get : topFrame.locals[idx]? = some mls := by
      rw [Array.getElem?_eq_getElem hlt_mf, hmls_eq]
    have himm' := himm mls hmls_get
    have hlm_eq :
        annealEvalOperandLM2_3 body.localDecls body.layouts
          (translateOperand (.copy ⟨idx, .nil⟩)) known =
        annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩) known := rfl
    rw [hlm_eq]
    cases hloc_base with
    | dead cachedLayout _ =>
      right
      have herr := rvalueM_bind_err (f := annealReadImmediateLM2_2)
        (annealEvalOperand_copy_dead (known := known) hframes hlt_mf hdecl hmls_eq hcache)
      exact ⟨_, "read of dead local", by simp [evalOperand, hslot], herr⟩
    | indirect _ mp _ _ _ _ =>
      exact False.elim (himm' mp rfl)
    | immediate _ imm cachedLayout _ hval =>
      let topFrame' :=
        cacheFrameLocalLayout topFrame idx hlt_mf (translateTy decl.ty body.layouts)
      rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
      · right
        have herr :
            (annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩) known >>=
              annealReadImmediateLM2_2) m =
            .error (.undefinedBehavior "read of uninitialized local")
              { m with stack := ⟨#[topFrame']⟩ } := by
          rw [EStateM.bind_eq_ok
            (annealEvalOperand_copy_live hframes hlt_mf hdecl hmls_eq hcache)]
          rfl
        exact ⟨_, "read of uninitialized local", by simp [evalOperand, hslot], herr⟩
      · obtain ⟨sc, msc, rfl, rfl, hrel, hlaysz, hbool, hchar⟩ :=
          himmRel.of_primitive_scalar hprim
        have hval_ok : validateLoadedValue body.layouts body.localDecls
            (.copy ⟨idx, .nil⟩) (.scalar sc) = true := by
          unfold validateLoadedValue
          dsimp only [operandTy, placeTy]
          rw [hdecl]
          dsimp only [resolveProjectedTy]
          cases hk_d : decl.ty.kind <;> try rfl
          rcases (hbool hk_d).2 with hb | hb <;> simp [hb]
        left
        refine ⟨sc, msc, topFrame', ?_, hval_ok, ?_, hrel, hlaysz, hbool, hchar,
          hframe.cache_local_layout hne hdecl hlt_mf, rfl,
          by dsimp [topFrame', cacheFrameLocalLayout]; rw [Array.size_set],
          by dsimp [topFrame', cacheFrameLocalLayout]; exact Array.getElem?_set_ne _ hne,
          (fun j hj => hj.cache_layout hlt_mf (translateTy decl.ty body.layouts)),
          (fun hd => MemoryAllocDisjoint_cacheFrameLocalLayout hd hlt_mf _),
          (fun _ _ hu => EnumLocalByteUninit.of_cache_layout hframes hu)⟩
        · simp [evalOperand, hslot, readProjectedValue]
        · rw [EStateM.bind_eq_ok
            (annealEvalOperand_copy_live hframes hlt_mf hdecl hmls_eq hcache)]
          rfl

/-- For a list of `WellTypedEnumScalarOp` operands, Anneal's `evalOperands`
never returns `.unsupported`, and whenever it succeeds it preserves `locals`
unchanged. -/
private theorem evalOperands_enumScalarOps_shape
    {body : CapturedMir}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (locals : List LocalSlot) (globals : List CapturedAllocation)
    (hlocals_len : length locals = length body.localDecls) :
    ∀ (ops : List MirAst.Operand),
      (∀ k (hk : k < ops.length), ∃ ty, WellTypedEnumScalarOp body tf (ops[k]'hk) ty) →
      evalOperands locals ops .nil globals body.layouts .nil body.localDecls = .ub ∨
        ∃ vals, evalOperands locals ops .nil globals body.layouts .nil body.localDecls = .ok vals locals
  | [], _ => Or.inr ⟨[], rfl⟩
  | op :: rest, hops => by
    obtain ⟨ty0, hop0⟩ := hops 0 (Nat.zero_lt_succ _)
    have hfirst : evalOperand locals op .nil globals body.layouts .nil body.localDecls = .ub ∨
        ∃ v, evalOperand locals op .nil globals body.layouts .nil body.localDecls = .ok v locals := by
      cases hop0 with
      | constScalar c sc hv _ _ _ _ _ _ =>
        exact Or.inr ⟨.scalar sc, by unfold evalOperand; dsimp only; rw [hv]; rfl⟩
      | copyLocal idx decl hdecl _ _ =>
        have hlt_d : idx < body.localDecls.length := by
          unfold get? at hdecl
          exact (List.getElem?_eq_some_iff.mp hdecl).1
        have hlt_l : idx < locals.length := by
          have h1 : idx < length body.localDecls := hlt_d
          have h2 : idx < length locals := hlocals_len ▸ h1; exact h2
        have hget : get? locals idx = some (locals[idx]'hlt_l) := by
          unfold get?; exact List.getElem?_eq_getElem hlt_l
        cases hsl : locals[idx]'hlt_l with
        | dead | uninit =>
          exact Or.inl (by simp [evalOperand, hget, hsl])
        | init val =>
          exact Or.inr ⟨val, by simp [evalOperand, hget, hsl, readProjectedValue]⟩
    have hrest := evalOperands_enumScalarOps_shape locals globals hlocals_len rest (fun k hk =>
      hops (k + 1) (Nat.succ_lt_succ hk))
    rcases hfirst with hub0 | ⟨v0, hok0⟩
    · exact Or.inl (by dsimp [evalOperands]; rw [hub0])
    · rcases hrest with hub_r | ⟨vs, hok_r⟩
      · exact Or.inl (by dsimp [evalOperands]; rw [hok0]; dsimp only; rw [hub_r])
      · exact Or.inr ⟨v0 :: vs, by dsimp [evalOperands]; rw [hok0]; dsimp only; rw [hok_r]⟩

/-- Parametric field-writing loop matching `Miri.Interpreter.writeAggregate`
over a list of translated MIR operands starting at field index `start`. -/
private def lm23WriteAggregateFieldsAux
    (h : Miri.Interpreter.AggregateHooks AnnealProv AnnealStepState Unit
      (Miri.Interpreter.RuntimePlace AnnealProv))
    (variantDest : Miri.Interpreter.RuntimePlace AnnealProv)
    (start : Nat) : List Miri.MIR.Operand → Miri.Interpreter.RvalueM AnnealStepState Unit
  | [] => pure ()
  | op :: rest => do
      let field ← h.projectField () variantDest start
      let v ← h.evalOperandAt () (Miri.Interpreter.OperandPath.aggregate start) op
        (some (h.placeLayout field))
      h.copyOpNoValidate () v field false
      lm23WriteAggregateFieldsAux h variantDest (start + 1) rest

private theorem lm23_forIn_range'_writeAggregate_eq
    (h : Miri.Interpreter.AggregateHooks AnnealProv AnnealStepState Unit
      (Miri.Interpreter.RuntimePlace AnnealProv))
    (operands : Array Miri.MIR.Operand)
    (variantDest : Miri.Interpreter.RuntimePlace AnnealProv) :
    ∀ (rest : List Miri.MIR.Operand) (start : Nat),
      (∀ k (hk : k < rest.length), operands[start + k]? = some (rest[k]'hk)) →
      (do
        for index in List.range' start rest.length 1 do
          let some operand := operands[index]?
            | throw (.invalidProgram "aggregate operand index")
          let field ← h.projectField () variantDest index
          let operand ← h.evalOperandAt ()
            (Miri.Interpreter.OperandPath.aggregate index) operand
            (some (h.placeLayout field))
          h.copyOpNoValidate () operand field false) =
        lm23WriteAggregateFieldsAux h variantDest start rest
  | [], _, _ => rfl
  | op :: tl, start, hget => by
    have h0 : operands[start]? = some op := by
      simpa using hget 0 (Nat.zero_lt_succ _)
    have htl : ∀ k (hk : k < tl.length), operands[(start + 1) + k]? = some (tl[k]'hk) := by
      intro k hk
      have := hget (k + 1) (Nat.succ_lt_succ hk)
      have hadd : start + (k + 1) = (start + 1) + k := by omega
      rw [← hadd]
      exact this
    have ih := lm23_forIn_range'_writeAggregate_eq h operands variantDest tl (start + 1) htl
    funext s
    simp only [List.length_cons, List.range', forIn, List.forIn'_cons,
      lm23WriteAggregateFieldsAux, h0,
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
    cases h.projectField () variantDest start s with
    | error _ _ => rfl
    | ok field s1 =>
      dsimp only
      cases h.evalOperandAt () (Miri.Interpreter.OperandPath.aggregate start) op
          (some (h.placeLayout field)) s1 with
      | error _ _ => rfl
      | ok v s2 =>
        dsimp only
        cases h.copyOpNoValidate () v field false s2 with
        | error _ _ => rfl
        | ok _ s3 => exact congrFun ih s3

/-- Unfold `Miri.Interpreter.writeAggregate` on multi-variant enum
`.Adt 0 variantIdx #[] none none` into `projectDowncast`,
`lm23WriteAggregateFieldsAux`, and `writeDiscriminant`. -/
private theorem writeAggregate_enum_eq
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (variantIdx : Nat) (mops : List Miri.MIR.Operand)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) :
    let h := annealAggregateHooksLM2_3 localDecls layouts mops.toArray
    Miri.Interpreter.writeAggregate h () (.Adt 0 variantIdx #[] none none) mops.toArray dest =
      (do
        let variantDest ← h.projectDowncast () dest variantIdx
        lm23WriteAggregateFieldsAux h variantDest 0 mops
        h.writeDiscriminant () variantIdx dest) := by
  intro h
  have henf : h.enforceValidity () (h.placeLayout dest) = pure true := rfl
  have hval : h.validate () dest = pure () := rfl
  funext s
  have hstep :
      Miri.Interpreter.writeAggregate h () (.Adt 0 variantIdx #[] none none) mops.toArray dest =
      (do
        let variantDest ← h.projectDowncast () dest variantIdx
        lm23WriteAggregateFieldsAux h variantDest 0 mops
        h.writeDiscriminant () variantIdx dest
        if ← h.enforceValidity () (h.placeLayout dest) then
          h.validate () dest) := by
    simp [Miri.Interpreter.writeAggregate]
    congr 1; funext variantDest
    have hloop := lm23_forIn_range'_writeAggregate_eq h mops.toArray variantDest mops 0
      (fun k hk => by simp [hk])
    simp at hloop
    exact congrArg (· >>= _) hloop
  rw [hstep]
  dsimp only [Bind.bind, EStateM.bind]
  cases h.projectDowncast () dest variantIdx s with
  | error _ _ => rfl
  | ok variantDest s1 =>
    dsimp only
    cases lm23WriteAggregateFieldsAux h variantDest 0 mops s1 with
    | error _ _ => rfl
    | ok u s2 =>
      cases u
      dsimp only
      cases h.writeDiscriminant () variantIdx dest s2 with
      | error _ _ => rfl
      | ok u2 s3 =>
        cases u2
        simp [henf, hval, Pure.pure, EStateM.pure]

/-- Allocation invariant after writing the first `k ≤ fields.length`
active-variant payload scalars (`doneVals`, `doneVals.length = k`) into an enum
backing allocation whose pre-loop initialization words were `words₀`. -/
private structure PartialEnumPayloadState
    (layouts : LayoutTable) (enumTy : Ty) (tagBytes : Nat)
    (vl : Miri.ABI.VariantLayout) (fields : List StructFieldDesc)
    (words₀ : Array UInt64)
    (k : Nat) (doneVals : List Value)
    (alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
    (words : Array UInt64) : Prop where
  valid_fields :
    ValidEnumVariantFields layouts tagBytes
      (translateTy enumTy layouts).layout.size.bytes.toNat vl fields
  hk_le : k ≤ fields.length
  done_len : doneVals.length = k
  mut_alloc : alloc.mutability = .Mut
  byteSize_eq : alloc.byteSize = (translateTy enumTy layouts).layout.size
  alloc_len_eq : alloc.len = alloc.byteSize.bytes.toNat
  prov_empty : alloc.provenanceMap = Miri.Memory.ProvenanceMap.new
  mask_rel : InitMaskWordRel alloc.initializationMask alloc.byteSize words
  bits_eq :
    ∀ b < (translateTy enumTy layouts).layout.size.bytes.toNat,
      maskBlocksGetBit words b =
        (maskBlocksGetBit words₀ b ||
          decide (∃ j, ∃ (hj : j < k),
            (fields[j]'(Nat.lt_of_lt_of_le hj hk_le)).offset.bytes.toNat ≤ b ∧
            b < (fields[j]'(Nat.lt_of_lt_of_le hj hk_le)).offset.bytes.toNat +
              (fields[j]'(Nat.lt_of_lt_of_le hj hk_le)).fieldLayout.size.bytes.toNat))
  fields_rel :
    ∀ j (hj : j < k),
      let hj_f : j < fields.length := Nat.lt_of_lt_of_le hj hk_le
      let f := fields[j]'hj_f
      ∃ sc msc,
        get? doneVals j = some (.scalar sc) ∧
        ScalarRel sc msc ∧
        f.fieldLayout.size = translateSizeBytes sc.sizeBytes ∧
        (f.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) ∧
        (f.ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) ∧
        alloc.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange f.offset f.fieldLayout.size) = .ok (.ok ()) ∧
        alloc.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange f.offset f.fieldLayout.size) false =
          .ok (.fromScalarInt msc)

private theorem PartialEnumPayloadState.init
    {layouts : LayoutTable} {enumTy : Ty} {tagBytes : Nat}
    {vl : Miri.ABI.VariantLayout} {fields : List StructFieldDesc}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {words₀ : Array UInt64}
    (hvf : ValidEnumVariantFields layouts tagBytes
      (translateTy enumTy layouts).layout.size.bytes.toNat vl fields)
    (hmut : alloc.mutability = .Mut)
    (hbs : alloc.byteSize = (translateTy enumTy layouts).layout.size)
    (hlen : alloc.len = alloc.byteSize.bytes.toNat)
    (hpmap : alloc.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask : InitMaskWordRel alloc.initializationMask alloc.byteSize words₀) :
    PartialEnumPayloadState layouts enumTy tagBytes vl fields words₀ 0 [] alloc words₀ where
  valid_fields := hvf
  hk_le := Nat.zero_le _
  done_len := rfl
  mut_alloc := hmut
  byteSize_eq := hbs
  alloc_len_eq := hlen
  prov_empty := hpmap
  mask_rel := hmask
  bits_eq := fun b _ => by simp
  fields_rel := fun _ hj => by cases hj

private theorem PartialEnumPayloadState.step_field
    {layouts : LayoutTable} {enumTy : Ty} {tagBytes : Nat}
    {vl : Miri.ABI.VariantLayout} {fields : List StructFieldDesc}
    {words₀ : Array UInt64} {k : Nat} {doneVals : List Value}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {words : Array UInt64}
    (h : PartialEnumPayloadState layouts enumTy tagBytes vl fields words₀ k doneVals alloc words)
    (hk : k < fields.length)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc)
    (hsz : (fields[k]'hk).fieldLayout.size = translateSizeBytes sc.sizeBytes)
    (hbool : (fields[k]'hk).ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1))
    (hchar : (fields[k]'hk).ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) :
    ∃ alloc' words',
      Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange (fields[k]'hk).offset msc.size)
        (.fromScalarInt msc) alloc = .ok () alloc' ∧
      PartialEnumPayloadState layouts enumTy tagBytes vl fields words₀ (k + 1)
        (doneVals ++ [.scalar sc]) alloc' words' := by
  have hbnd_k :
      (fields[k]'hk).offset.bytes.toNat +
        (translateSizeBytes sc.sizeBytes).bytes.toNat ≤
        alloc.byteSize.bytes.toNat := by
    rw [← hsz, h.byteSize_eq]
    exact h.valid_fields.fields_in_bounds k hk
  obtain ⟨alloc', words', hw, hbs', hlen', hmut', hpmap', hmask', hbits',
      hraw', hinit_k, hread_k⟩ :=
    alloc_writeScalar_at_offset_mask hrel h.alloc_len_eq h.mut_alloc
      h.prov_empty h.mask_rel hbnd_k
  rw [← hsz] at hinit_k hread_k hbits' hraw'
  have hrawA_len : (lm22AllocRaw alloc).size = alloc.byteSize.bytes.toNat := by
    have : (lm22AllocRaw alloc).size = alloc.len := by cases alloc; rfl
    rw [this, h.alloc_len_eq]
  have hrawA'_len : (lm22AllocRaw alloc').size = alloc'.byteSize.bytes.toNat := by
    have : (lm22AllocRaw alloc').size = alloc'.len := by cases alloc'; rfl
    rw [this, hlen', hbs', h.alloc_len_eq]
  refine ⟨alloc', words', hw, h.valid_fields, Nat.succ_le_of_lt hk,
    by rw [List.length_append, List.length_singleton, h.done_len],
    hmut', hbs'.trans h.byteSize_eq,
    hlen'.trans (h.alloc_len_eq.trans (by rw [hbs'])),
    hpmap', by rw [hbs']; exact hmask', ?_, ?_⟩
  · intro b hb
    have hb_a : b < alloc.byteSize.bytes.toNat := by rw [h.byteSize_eq]; exact hb
    rw [hbits' b hb_a, h.bits_eq b hb, Bool.or_assoc]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨j, hj, hlo, hhi⟩ | ⟨hlo, hhi⟩)
      · exact ⟨j, Nat.lt_succ_of_lt hj, hlo, hhi⟩
      · exact ⟨k, Nat.lt_succ_self k, hlo, hhi⟩
    · rintro ⟨j, hj1, hlo, hhi⟩
      by_cases hjk : j = k
      · subst hjk; exact Or.inr ⟨hlo, hhi⟩
      · exact Or.inl ⟨j, by omega, hlo, hhi⟩
  · intro j hj1
    by_cases hjk : j = k
    · subst hjk
      refine ⟨sc, msc, ?_, hrel, hsz, hbool, hchar, hinit_k, hread_k⟩
      unfold get?
      rw [List.getElem?_append_right (by rw [h.done_len]; exact Nat.le_refl _),
        h.done_len, Nat.sub_self]
      rfl
    · have hj_lt : j < k := by omega
      have hj_f : j < fields.length := Nat.lt_of_lt_of_le hj_lt h.hk_le
      obtain ⟨sc_j, msc_j, hget_j, hrel_j, hsz_j, hbool_j, hchar_j, hinit_j, hread_j⟩ :=
        h.fields_rel j hj_lt
      have hget_app : get? (doneVals ++ [.scalar sc]) j = some (.scalar sc_j) := by
        unfold get? at hget_j ⊢
        rw [List.getElem?_append_left (by rw [h.done_len]; exact hj_lt)]
        exact hget_j
      have hbnd_j :
          (fields[j]'hj_f).offset.bytes.toNat +
            (fields[j]'hj_f).fieldLayout.size.bytes.toNat ≤
            alloc.byteSize.bytes.toNat := by
        rw [h.byteSize_eq]
        exact h.valid_fields.fields_in_bounds j hj_f
      have hj_pos : 0 < (fields[j]'hj_f).fieldLayout.size.bytes.toNat := by
        rw [hsz_j]; exact translateSizeBytes_pos_lm2_3 hrel_j.validBytes
      have hinit'_j :
          alloc'.initializationMask.isRangeInitialized
            (Miri.Memory.allocRange (fields[j]'hj_f).offset
              (fields[j]'hj_f).fieldLayout.size) = .ok (.ok ()) := by
        apply initMaskWordRel_isRangeInitialized hmask' hj_pos hbnd_j
        intro b hlo hhi
        have hb_enum : b < (translateTy enumTy layouts).layout.size.bytes.toNat := by
          rw [← h.byteSize_eq]; omega
        rw [hbits' b (by rw [h.byteSize_eq]; exact hb_enum), h.bits_eq b hb_enum]
        have hex : ∃ j', ∃ (hj' : j' < k),
            (fields[j']'(Nat.lt_of_lt_of_le hj' h.hk_le)).offset.bytes.toNat ≤ b ∧
            b < (fields[j']'(Nat.lt_of_lt_of_le hj' h.hk_le)).offset.bytes.toNat +
              (fields[j']'(Nat.lt_of_lt_of_le hj' h.hk_le)).fieldLayout.size.bytes.toNat :=
          ⟨j, hj_lt, hlo, hhi⟩
        simp [hex]
      have hdisj := h.valid_fields.fields_disjoint j k hj_f hk hjk
      have hread'_j :
          alloc'.readScalar annealTargetDataLayout
            (Miri.Memory.allocRange (fields[j]'hj_f).offset
              (fields[j]'hj_f).fieldLayout.size) false =
          .ok (.fromScalarInt msc_j) := by
        rw [alloc_readScalar_congr hrawA_len hrawA'_len hbs' hinit_j hinit'_j hbnd_j ?_]
        · exact hread_j
        · rw [hraw']
          exact extract_writeBytes_disjoint (lm22AllocRaw alloc)
            (lm22LeBytes sc.bits (fields[k]'hk).fieldLayout.size.bytes.toNat)
            (lm22LeBytes_size _ _)
            (by rw [hrawA_len, hsz]; exact hbnd_k)
            (by rw [hrawA_len]; exact hbnd_j)
            hdisj
      exact ⟨sc_j, msc_j, hget_app, hrel_j, hsz_j, hbool_j, hchar_j, hinit'_j, hread'_j⟩

private theorem rvalueM_bind_congr_left {α β : Type}
    {x y : Miri.Interpreter.RvalueM AnnealStepState α}
    {f : α → Miri.Interpreter.RvalueM AnnealStepState β}
    {s₁ s₂ : AnnealStepState}
    (h : x s₁ = y s₂) :
    (x >>= f) s₁ = (y >>= f) s₂ := by
  dsimp only [Bind.bind, EStateM.bind]
  cases hx : x s₁ <;> cases hy : y s₂ <;> rw [hx, hy] at h <;> cases h <;> rfl

private theorem rvalueM_bind_of_error {α β : Type}
    {x : Miri.Interpreter.RvalueM AnnealStepState α}
    {f : α → Miri.Interpreter.RvalueM AnnealStepState β}
    {s s' : AnnealStepState} {e : Miri.Interpreter.StepError}
    (h : x s = .error e s') :
    (x >>= f) s = .error e s' := by
  dsimp only [Bind.bind, EStateM.bind]
  cases hx : x s <;> rw [hx] at h <;> cases h <;> rfl

/-- Inductive payload-field writing loop for `lm23WriteAggregateFieldsAux` on
`variantDest = ⟨.memory mp, varLay⟩`: either both Anneal's `evalOperands` and
`lean-miri`'s field loop followed by any continuation `cont` fail with `.ub`, or
all remaining payload scalars are written into `mp`'s stack allocation while
maintaining `PartialEnumPayloadState`, `FrameRelLM2_3Except`, and
`EnumLocalByteUninit` on all `localId ≠ dstIdx`. -/
private theorem lm23_writeEnumFields_loop
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {dstIdx : Local} {dstDecl : LocalDecl} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)} {variantIdx : Nat}
    {hv : variantIdx < variants.length}
    {vl : Miri.ABI.VariantLayout}
    {varLay : Miri.Interpreter.LocalLayout}
    {fullOps : List MirAst.Operand}
    {words₀ : Array UInt64}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {allocId : Miri.Memory.AllocId} {borTag : Miri.Memory.BorTag}
    {baseAddr : UInt64}
    (henv_valid : ∀ t tb vs, env t = some (tb, vs) → ValidEnumLayout t body.layouts tb vs)
    (hdst_decl : get? body.localDecls dstIdx = some dstDecl)
    (henv_dst : env dstDecl.ty = some (tagBytes, variants))
    (hoff_var : ∀ i (hi : i < (variants[variantIdx]'hv).length),
      varLay.layout.fields.offset i = .ok ((variants[variantIdx]'hv)[i]'hi).offset)
    (hfull_len : fullOps.length = (variants[variantIdx]'hv).length)
    (hprov : mp.ptr.provenance = some (.concrete allocId borTag))
    (hmis : mp.misaligned = none)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
    (hovf : baseAddr.toNat +
      (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat < 2 ^ 64)
    (globals : List CapturedAllocation)
    (cont : Unit → Miri.Interpreter.RvalueM AnnealStepState Unit) :
    ∀ (remOps : List MirAst.Operand) (k : Nat)
      (hk_sum : k + remOps.length = (variants[variantIdx]'hv).length)
      (_hslice : ∀ j (hj : j < remOps.length),
        fullOps[k + j]? = some (remOps[j]'hj))
      (doneVals : List Value)
      (af : StackFrame)
      (m : AnnealStepState)
      (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (localAlloc : AnnealLocalAlloc)
      (words : Array UInt64)
      (_hframes : m.stack.frames = #[tf])
      (hlt : dstIdx < tf.locals.size)
      (_hdst_ind : tf.locals[dstIdx]'hlt =
        ⟨.live (.indirect mp), some (translateTy dstDecl.ty body.layouts)⟩)
      (_hfr : FrameRelLM2_3Except body env dstIdx m.machine af tf)
      (_hdisj : MemoryAllocDisjoint tf)
      (_hsupply : AllocIdSupplyValid allocBudget m.machine.memory)
      (_hlive : LiveAllocEntry m.machine.memory.live allocId localAlloc)
      (_hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
      (_hpart : PartialEnumPayloadState body.layouts dstDecl.ty tagBytes vl
        (variants[variantIdx]'hv) words₀ k doneVals localAlloc.allocation words)
      (_hops : ∀ j (hj : j < remOps.length),
        WellTypedEnumScalarOp body tf (remOps[j]'hj)
          ((variants[variantIdx]'hv)[k + j]'(by omega)).ty),
      (evalOperands af.locals remOps .nil globals body.layouts .nil body.localDecls = .ub ∧
        ∃ m_err msg,
          (lm23WriteAggregateFieldsAux
            (annealAggregateHooksLM2_3 body.localDecls body.layouts
              (fullOps.map translateOperand).toArray)
            ⟨.memory mp, varLay⟩ k (remOps.map translateOperand) >>= cont) m =
          .error (.undefinedBehavior msg) m_err) ∨
      (∃ (tailVals : List Value) (m_end : AnnealStepState)
          (tf_end : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
          (la_end : AnnealLocalAlloc) (words_end : Array UInt64)
          (hlt_end : dstIdx < tf_end.locals.size),
        evalOperands af.locals remOps .nil globals body.layouts .nil body.localDecls =
          .ok tailVals af.locals ∧
        lm23WriteAggregateFieldsAux
          (annealAggregateHooksLM2_3 body.localDecls body.layouts
            (fullOps.map translateOperand).toArray)
          ⟨.memory mp, varLay⟩ k (remOps.map translateOperand) m =
          .ok () m_end ∧
        m_end.stack.frames = #[tf_end] ∧
        tf_end.localsIdentity = tf.localsIdentity ∧
        tf_end.returnContinuation = tf.returnContinuation ∧
        tf_end.returnPlace = tf.returnPlace ∧
        tf_end.locals[dstIdx]'hlt_end =
          ⟨.live (.indirect mp), some (translateTy dstDecl.ty body.layouts)⟩ ∧
        FrameRelLM2_3Except body env dstIdx m_end.machine af tf_end ∧
        MemoryAllocDisjoint tf_end ∧
        AllocIdSupplyValid allocBudget m_end.machine.memory ∧
        LiveAllocEntry m_end.machine.memory.live allocId la_end ∧
        m_end.machine.lookupBaseAddr allocId = some baseAddr ∧
        PartialEnumPayloadState body.layouts dstDecl.ty tagBytes vl
          (variants[variantIdx]'hv) words₀ (variants[variantIdx]'hv).length
          (doneVals ++ tailVals) la_end.allocation words_end ∧
        (∀ localId b, localId ≠ dstIdx →
          EnumLocalByteUninit m localId b →
          EnumLocalByteUninit m_end localId b) ∧
        (∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf_end j))
  | [], k, hk_sum, _, doneVals, af, m, tf, localAlloc, words,
      hframes, hlt, hdst_ind, hfr, hdisj, hsupply, hlive, hbase, hpart, _ => by
    right
    have hk_eq : k = (variants[variantIdx]'hv).length := by simpa using hk_sum
    subst hk_eq
    exact ⟨[], m, tf, localAlloc, words, hlt, rfl, rfl, hframes, rfl, rfl, rfl,
      hdst_ind, hfr, hdisj, hsupply, hlive, hbase,
      by rw [List.append_nil]; exact hpart, (fun _ _ _ hu => hu), (fun _ hj => hj)⟩
  | op :: rest, k, hk_sum, hslice, doneVals, af, m, tf, localAlloc, words,
      hframes, hlt, hdst_ind, hfr, hdisj, hsupply, hlive, hbase, hpart, hops => by
    have hk_lt : k < (variants[variantIdx]'hv).length := by
      dsimp at hk_sum; omega
    let f_k := (variants[variantIdx]'hv)[k]'hk_lt
    have hop_k : WellTypedEnumScalarOp body tf op f_k.ty := by
      simpa [f_k] using hops 0 (Nat.zero_lt_succ _)
    obtain ⟨hprim_k, hfl_k⟩ := hpart.valid_fields.fields_prim k hk_lt
    have hfl_sized : (translateTy f_k.ty body.layouts).layout.isSized = true :=
      hprim_k.isSized_lm2_3 body.layouts
    have hmiri_op_at :
        ((fullOps.map translateOperand).toArray[k]? >>=
          miriOperandLayout body.localDecls body.layouts) =
        some (translateTy f_k.ty body.layouts) := by
      have hfull_k : fullOps[k]? = some op := by
        simpa using hslice 0 (Nat.zero_lt_succ _)
      have hk_full : k < fullOps.length := by omega
      have hget_arr : (fullOps.map translateOperand).toArray[k]? = some (translateOperand op) := by
        rw [List.getElem?_toArray, List.getElem?_map, hfull_k]; rfl
      rw [hget_arr]
      exact hop_k.miriOperandLayout_eq
    have hk_in_bounds := hpart.valid_fields.fields_in_bounds k hk_lt
    have hf_ovf : mp.ptr.offset.bytes.toNat + f_k.offset.bytes.toNat < 2 ^ 64 := by
      rw [hptr]
      have hb_nat : (Miri.ABI.Size.ofBytes baseAddr).bytes.toNat = baseAddr.toNat := rfl
      rw [hb_nat]
      dsimp only [f_k]
      omega
    let fieldMp : Miri.Interpreter.MemPlace AnnealProv :=
      ⟨⟨Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + f_k.offset.bytes), mp.ptr.provenance⟩,
        .none, mp.misaligned⟩
    have hproj_k :
        (annealAggregateHooksLM2_3 body.localDecls body.layouts
          (fullOps.map translateOperand).toArray).projectField ()
          ⟨.memory mp, varLay⟩ k m =
        .ok ⟨.memory fieldMp, translateTy f_k.ty body.layouts⟩ m := by
      unfold annealAggregateHooksLM2_3
      dsimp only
      rw [hmiri_op_at]
      dsimp only
      rw [projectField_fixed_offset (hoff_var k hk_lt) hfl_sized hf_ovf]
      rfl
    have hmem_false :
        usesStructMemCopyDest ⟨.memory fieldMp, translateTy f_k.ty body.layouts⟩ = false :=
      hprim_k.usesStructMemCopyDest_false_lm2_3 body.layouts (.memory fieldMp)
    have hstep_head :
        lm23WriteAggregateFieldsAux
          (annealAggregateHooksLM2_3 body.localDecls body.layouts
            (fullOps.map translateOperand).toArray)
          ⟨.memory mp, varLay⟩ k (translateOperand op :: rest.map translateOperand) m =
        (((annealEvalOperandLM2_3 body.localDecls body.layouts (translateOperand op)
            (some (translateTy f_k.ty body.layouts)) >>= annealReadImmediateLM2_2) >>=
          fun r => annealWriteImmediateLM2_2 r.imm
            ⟨.memory fieldMp, translateTy f_k.ty body.layouts⟩) >>=
          fun _ =>
            lm23WriteAggregateFieldsAux
              (annealAggregateHooksLM2_3 body.localDecls body.layouts
                (fullOps.map translateOperand).toArray)
              ⟨.memory mp, varLay⟩ (k + 1) (rest.map translateOperand)) m := by
      dsimp only [lm23WriteAggregateFieldsAux, Bind.bind, EStateM.bind]
      rw [hproj_k]
      dsimp only [annealAggregateHooksLM2_3, annealAggregateHooksLM2_2]
      cases hev : annealEvalOperandLM2_3 body.localDecls body.layouts (translateOperand op)
          (some (translateTy f_k.ty body.layouts)) m with
      | error _ _ => rfl
      | ok src s1 =>
        dsimp only
        rw [hmem_false, Bool.and_false]
        simp only [Bool.false_eq_true, ↓reduceIte, Bind.bind, EStateM.bind]
    rcases evalEnumScalarOp_except_dst henv_valid hdst_decl henv_dst hframes hfr hop_k
        globals (some (translateTy f_k.ty body.layouts)) with
      ⟨sc, msc, tf₁, ha_op, _, hm_op, hrel, hlaysz, hbool, hchar, hfr₁, htf₁_eq,
        hsz₁, hdst_eq₁, himm_mono₁, hdisj_fn₁, hu_pres₁⟩ |
      ⟨m_err, msg, ha_err, hm_err⟩
    · have hlt₁ : dstIdx < tf₁.locals.size := by rw [hsz₁]; exact hlt
      have hdst₁ : tf₁.locals[dstIdx]'hlt₁ =
          ⟨.live (.indirect mp), some (translateTy dstDecl.ty body.layouts)⟩ := by
        have hg := hdst_eq₁
        rw [Array.getElem?_eq_getElem hlt₁, Array.getElem?_eq_getElem hlt, hdst_ind] at hg
        exact Option.some.inj hg
      have hf_sz : f_k.fieldLayout.size = translateSizeBytes sc.sizeBytes := by
        rw [hfl_k, hlaysz]
      obtain ⟨alloc₁, words₁, hw_sc, hpart₁⟩ :=
        hpart.step_field hk_lt hrel hf_sz hbool hchar
      obtain ⟨hfind_live, u, hu_lt, hfidx, hget_u⟩ := hlive
      let m₁ : AnnealStepState :=
        { stack := ⟨#[tf₁]⟩
          machine := updateAllocMachine m.machine u allocId localAlloc.kind alloc₁ }
      have hfield_ptr :
          fieldMp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + f_k.offset.bytes) := by
        dsimp [fieldMp]
        rw [hptr]
        rfl
      have hw_range_eq :
          Miri.ABI.Size.ofBytes (f_k.offset.bytes + Miri.ABI.Size.ZERO.bytes) = f_k.offset := by
        dsimp [Miri.ABI.Size.ZERO]
        rw [UInt64.add_zero]
        cases f_k.offset; rfl
      have hw_imm :
          annealWriteImmediateLM2_2 (.scalar (.fromScalarInt msc))
            ⟨.memory fieldMp, translateTy f_k.ty body.layouts⟩
            { m with stack := ⟨#[tf₁]⟩ } = .ok () m₁ := by
        unfold annealWriteImmediateLM2_2
        dsimp only [bind, Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]
        rw [stack_currentFrame?_singleton _ tf₁ rfl]
        exact annealWriteIndirectImmediate_scalar_ok
          (m := { m with stack := ⟨#[tf₁]⟩ }) (mpOff := f_k.offset)
          hprov hbase hfield_ptr hu_lt hfidx hget_u
          (by rw [hw_range_eq]; exact hw_sc)
      have hdisj₁ := hdisj_fn₁ hdisj
      have hfr_m₁ : FrameRelLM2_3Except body env dstIdx m₁.machine af tf₁ :=
        hfr₁.of_updateAlloc_excl hdisj₁ hdst₁ hprov hu_lt hget_u
      have hlive₁ : LiveAllocEntry m₁.machine.memory.live allocId
          ⟨localAlloc.kind, alloc₁⟩ :=
        LiveAllocEntry.of_set!_self ⟨hfind_live, u, hu_lt, hfidx, hget_u⟩ hu_lt hfidx _
      have hsupply₁ : AllocIdSupplyValid allocBudget m₁.machine.memory :=
        hsupply.of_updateAlloc hu_lt hget_u
      have hu_m₁ : ∀ localId b, localId ≠ dstIdx →
          EnumLocalByteUninit m localId b → EnumLocalByteUninit m₁ localId b := by
        intro localId b hne_id hu₀
        have hu_tf₁ := hu_pres₁ localId b hu₀
        intro tf' mp' c' id' bt' la' hf' hloc' hprov' hfind'
        injection hf' with hf_arr; injection hf_arr with htf_eq; subst htf_eq
        have hdst_get₁ : tf₁.locals[dstIdx]? =
            some ⟨.live (.indirect mp), some (translateTy dstDecl.ty body.layouts)⟩ := by
          rw [Array.getElem?_eq_getElem hlt₁, hdst₁]
        have hd_ne := hdisj₁ localId dstIdx mp' mp c' _ hne_id hloc' hdst_get₁
        have hid_ne : id' ≠ allocId := by
          intro hid_eq; apply hd_ne; rw [hprov', hprov, hid_eq]; rfl
        have hfind_old :
            m.machine.memory.live.find? (fun (k0, _) => k0 == id') = some (id', la') := by
          dsimp [m₁, updateAllocMachine] at hfind'
          obtain ⟨hbeq_id, idx_f, hlt_f, hget_f, hnot_before⟩ :=
            Array.find?_eq_some_iff_getElem.mp hfind'
          have hlt_orig : idx_f < m.machine.memory.live.size := by
            rwa [Array.size_setIfInBounds] at hlt_f
          have hne_u : idx_f ≠ u := by
            intro rfl
            rw [Array.getElem_setIfInBounds_self] at hget_f
            injection hget_f with hk_eq
            exact hid_ne hk_eq.symm
          rw [Array.getElem_setIfInBounds_ne hlt_orig (Ne.symm hne_u)] at hget_f
          rw [Array.find?_eq_some_iff_getElem]
          refine ⟨hbeq_id, idx_f, hlt_orig, hget_f, ?_⟩
          intro j hj
          by_cases hju : j = u
          · subst hju; rw [hget_u]; simp [Ne.symm hid_ne]
          · have hprev := hnot_before j hj
            rwa [Array.getElem_setIfInBounds_ne (Nat.lt_trans hj hlt_orig) (Ne.symm hju)] at hprev
        exact hu_tf₁ tf₁ mp' c' id' bt' la' rfl hloc' hprov' hfind_old
      have hk_rest : (k + 1) + rest.length = (variants[variantIdx]'hv).length := by
        dsimp at hk_sum; omega
      have hslice_rest : ∀ j (hj : j < rest.length),
          fullOps[(k + 1) + j]? = some (rest[j]'hj) := by
        intro j hj
        have hadd : (k + 1) + j = k + (j + 1) := by omega
        rw [hadd]
        exact hslice (j + 1) (Nat.succ_lt_succ hj)
      have hops_rest : ∀ j (hj : j < rest.length),
          WellTypedEnumScalarOp body tf₁ (rest[j]'hj)
            ((variants[variantIdx]'hv)[(k + 1) + j]'(by omega)).ty := by
        intro j hj
        have hadd : (k + 1) + j = k + (j + 1) := by omega
        have hop_j := (hops (j + 1) (Nat.succ_lt_succ hj)).mono_immediate himm_mono₁
        simpa [hadd] using hop_j
      rcases lm23_writeEnumFields_loop henv_valid hdst_decl henv_dst hoff_var hfull_len
          hprov hmis hptr hovf globals cont rest (k + 1) hk_rest hslice_rest
          (doneVals ++ [.scalar sc]) af m₁ tf₁ ⟨localAlloc.kind, alloc₁⟩ words₁
          rfl hlt₁ hdst₁ hfr_m₁ hdisj₁ hsupply₁ hlive₁ hbase hpart₁ hops_rest with
        ⟨hub_rest, m_err, msg, hm_err_rest⟩ |
        ⟨tailVals, m_end, tf_end, la_end, words_end, hlt_end, hok_rest, hm_ok_rest,
          hf_end, hid_end, hrc_end, hrp_end, hdst_end, hfr_end, hdisj_end, hsup_end,
          hlive_end, hbase_end, hpart_end, hu_end, himm_end⟩
      · left
        refine ⟨by dsimp [evalOperands]; rw [ha_op]; dsimp only; rw [hub_rest], m_err, msg, ?_⟩
        dsimp only [List.map]
        have h1 :
            (((annealEvalOperandLM2_3 body.localDecls body.layouts (translateOperand op)
                (some (translateTy f_k.ty body.layouts)) >>= annealReadImmediateLM2_2) >>=
              fun r => annealWriteImmediateLM2_2 r.imm
                ⟨.memory fieldMp, translateTy f_k.ty body.layouts⟩) >>=
              fun _ =>
                lm23WriteAggregateFieldsAux
                  (annealAggregateHooksLM2_3 body.localDecls body.layouts
                    (fullOps.map translateOperand).toArray)
                  ⟨.memory mp, varLay⟩ (k + 1) (rest.map translateOperand)) m =
            lm23WriteAggregateFieldsAux
              (annealAggregateHooksLM2_3 body.localDecls body.layouts
                (fullOps.map translateOperand).toArray)
              ⟨.memory mp, varLay⟩ (k + 1) (rest.map translateOperand) m₁ := by
          rw [EStateM.bind_eq_ok (by rw [EStateM.bind_eq_ok hm_op]; exact hw_imm)]
        rw [rvalueM_bind_congr_left (hstep_head.trans h1)]
        exact hm_err_rest
      · right
        have happ : (doneVals ++ [.scalar sc]) ++ tailVals = doneVals ++ (.scalar sc :: tailVals) := by
          rw [List.append_assoc]; rfl
        rw [happ] at hpart_end
        refine ⟨.scalar sc :: tailVals, m_end, tf_end, la_end, words_end, hlt_end,
          by dsimp [evalOperands]; rw [ha_op]; dsimp only; rw [hok_rest],
          ?_, hf_end,
          hid_end.trans (by rw [htf₁_eq]),
          hrc_end.trans (by rw [htf₁_eq]),
          hrp_end.trans (by rw [htf₁_eq]),
          hdst_end, hfr_end, hdisj_end, hsup_end, hlive_end, hbase_end, hpart_end,
          (fun localId b hne hu₀ => hu_end localId b hne (hu_m₁ localId b hne hu₀)),
          (fun j hj => himm_end j (himm_mono₁ j hj))⟩
        dsimp only [List.map]
        rw [hstep_head, EStateM.bind_eq_ok (by rw [EStateM.bind_eq_ok hm_op]; exact hw_imm)]
        exact hm_ok_rest
    · left
      refine ⟨by dsimp [evalOperands]; rw [ha_err], m_err, msg, ?_⟩
      dsimp only [List.map]
      exact rvalueM_bind_of_error
        (hstep_head.trans (EStateM.bind_eq_error (EStateM.bind_eq_error hm_err)))

/-- Shared completion after `projectDowncast` has forced `dstIdx` into stack
memory at `mp`: runs `lm23_writeEnumFields_loop` followed by
`writeDiscriminant_indirect_local_ok` to assemble `EnumMemRel` and establish
`EnumLocalByteUninit` on all non-payload bytes whenever
`words₀ = initWordsFalse`. -/
private theorem finish_aggregate_enum_from_indirect
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {s : MachineState} {m₀ m_down : AnnealStepState}
    {tf₀ tf_down : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {bb : BasicBlockData} {stmt : Statement}
    {dstIdx : Local} {dstDecl : LocalDecl}
    {adtDefId : String} {variantIdx : Nat} {ops : List MirAst.Operand}
    {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    {hv : variantIdx < variants.length}
    {vl : Miri.ABI.VariantLayout} {varLay : Miri.Interpreter.LocalLayout}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {allocId : Miri.Memory.AllocId} {borTag : Miri.Memory.BorTag}
    {baseAddr : UInt64} {la_down : AnnealLocalAlloc} {words₀ : Array UInt64}
    {slot_dst : LocalSlot} {retLay : Miri.Interpreter.LocalLayout}
    (henv_valid : ∀ t tb vs, env t = some (tb, vs) → ValidEnumLayout t body.layouts tb vs)
    (hframes₀ : m₀.stack.frames = #[tf₀])
    (hbody₀ : tf₀.body = translateBody body)
    (hloc₀ : tf₀.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hcal : s.memory.activeCallee = none)
    (hstack : s.memory.callStack = .nil)
    (hbor : s.memory.borrows = .nil)
    (hprot : s.memory.activeProtectors = .nil)
    (hcaller : s.memory.callerLocals = .nil)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hkind : stmt.kind = .assign ⟨dstIdx, .nil⟩ (.aggregate (.adt adtDefId variantIdx .none) ops))
    (hdst_decl : get? body.localDecls dstIdx = some dstDecl)
    (henv_dst : env dstDecl.ty = some (tagBytes, variants))
    (hvalid : ValidEnumLayout dstDecl.ty body.layouts tagBytes variants)
    (hvf : ValidEnumVariantFields body.layouts tagBytes
      (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat vl
      (variants[variantIdx]'hv))
    (hoff_var : ∀ i (hi : i < (variants[variantIdx]'hv).length),
      varLay.layout.fields.offset i = .ok ((variants[variantIdx]'hv)[i]'hi).offset)
    (hops_len : ops.length = (variants[variantIdx]'hv).length)
    (hops_wt : ∀ i (hi : i < ops.length),
      WellTypedEnumScalarOp body tf_down (ops[i]'hi)
        ((variants[variantIdx]'hv)[i]'(by omega)).ty)
    (hdst_slot : get? s.frame.locals dstIdx = some slot_dst)
    (hnot_dead : slot_dst ≠ .dead)
    (heval_down :
      Miri.Interpreter.Step.evalStatement (annealStepHooksLM2_3 body.localDecls body.layouts) ()
        (translateStmt stmt) m₀ =
      Miri.Interpreter.runRvalue
        (do
          lm23WriteAggregateFieldsAux
            (annealAggregateHooksLM2_3 body.localDecls body.layouts
              (ops.map translateOperand).toArray)
            ⟨.memory mp, varLay⟩ 0 (ops.map translateOperand)
          (annealAggregateHooksLM2_3 body.localDecls body.layouts
            (ops.map translateOperand).toArray).writeDiscriminant () variantIdx
            ⟨.local 0 dstIdx none tf₀.localsIdentity,
              translateTy dstDecl.ty body.layouts⟩)
        m_down)
    (hframes_down : m_down.stack.frames = #[tf_down])
    (hrc_down : tf_down.returnContinuation = .stop false)
    (hrp_down : tf_down.returnPlace = .frameLocal 0 0 none retLay tf_down.localsIdentity)
    (hlt_down : dstIdx < tf_down.locals.size)
    (hdst_down : tf_down.locals[dstIdx]'hlt_down =
      ⟨.live (.indirect mp), some (translateTy dstDecl.ty body.layouts)⟩)
    (hfr_down : FrameRelLM2_3Except body env dstIdx m_down.machine s.frame tf_down)
    (hdisj_down : MemoryAllocDisjoint tf_down)
    (hsup_down : AllocIdSupplyValid allocBudget m_down.machine.memory)
    (hprov : mp.ptr.provenance = some (.concrete allocId borTag))
    (hmis : mp.misaligned = none)
    (hmeta : mp.metadata = .none)
    (hlive_down : LiveAllocEntry m_down.machine.memory.live allocId la_down)
    (hbase_down : m_down.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
    (hovf : baseAddr.toNat +
      (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat < 2 ^ 64)
    (halign : mp.ptr.offset.isAligned
      (translateTy dstDecl.ty body.layouts).layout.align.abi = .ok true)
    (hmut₀ : la_down.allocation.mutability = .Mut)
    (hbs₀ : la_down.allocation.byteSize = (translateTy dstDecl.ty body.layouts).layout.size)
    (hlen₀ : la_down.allocation.len = la_down.allocation.byteSize.bytes.toNat)
    (hpmap₀ : la_down.allocation.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask₀ : InitMaskWordRel la_down.allocation.initializationMask
      la_down.allocation.byteSize words₀)
    (hu_down : ∀ localId b, localId ≠ dstIdx →
      EnumLocalByteUninit m₀ localId b → EnumLocalByteUninit m_down localId b)
    (himm_down : ∀ j, j ≠ dstIdx →
      IsImmediateStepLocal m₀ j → IsImmediateFrameLocal tf_down j) :
    let mRes := Miri.Interpreter.Step.step (annealStepHooksLM2_3 body.localDecls body.layouts) () m₀
    StepRelLM2_3 body env allocBudget m₀ (evalStmt s stmt body.localDecls body.layouts) mRes ∧
    ((∀ msg, mRes.2 ≠ .error (.undefinedBehavior msg)) →
      (words₀ = initWordsFalse (translateTy dstDecl.ty body.layouts).layout.size →
        ∀ b, tagBytes ≤ b →
          b < (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat →
          (∀ j (hj : j < (variants[variantIdx]'hv).length),
            b < ((variants[variantIdx]'hv)[j]'hj).offset.bytes.toNat ∨
              ((variants[variantIdx]'hv)[j]'hj).offset.bytes.toNat +
                ((variants[variantIdx]'hv)[j]'hj).fieldLayout.size.bytes.toNat ≤ b) →
          EnumLocalByteUninit mRes.1 dstIdx b) ∧
      (∀ localId b, localId ≠ dstIdx →
        EnumLocalByteUninit m₀ localId b → EnumLocalByteUninit mRes.1 localId b) ∧
      (∀ j, j ≠ dstIdx →
        IsImmediateStepLocal m₀ j → IsImmediateStepLocal mRes.1 j)) := by
  intro mRes
  have hpart₀ := PartialEnumPayloadState.init hvf hmut₀ hbs₀ hlen₀ hpmap₀ hmask₀
  let cont : Unit → Miri.Interpreter.RvalueM AnnealStepState Unit := fun _ =>
    (annealAggregateHooksLM2_3 body.localDecls body.layouts
      (ops.map translateOperand).toArray).writeDiscriminant () variantIdx
      ⟨.local 0 dstIdx none tf₀.localsIdentity, translateTy dstDecl.ty body.layouts⟩
  rcases lm23_writeEnumFields_loop henv_valid hdst_decl henv_dst hoff_var hops_len
      hprov hmis hptr hovf s.memory.globals cont ops 0 (by omega)
      (fun j hj => by simp [List.getElem?_eq_getElem hj]) [] s.frame m_down tf_down
      la_down words₀ hframes_down hlt_down hdst_down hfr_down hdisj_down hsup_down
      hlive_down hbase_down hpart₀
      (fun j hj => by simpa using hops_wt j hj) with
    ⟨hub_ops, m_err, msg, hm_err⟩ |
    ⟨vals, m_end, tf_end, la_end, words_end, hlt_end, hok_ops, hm_ok_ops,
      hf_end, hid_end, hrc_end, hrp_end, hdst_end, hfr_end, hdisj_end, hsup_end,
      hlive_end, hbase_end, hpart_end, hu_end, himm_end⟩
  · have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; rw [hkind]; dsimp only [evalRvalue, evalAggregateAdt]
      rw [hbor, hcaller, hub_ops]
    have hm_ub :
        Miri.Interpreter.Step.evalStatement (annealStepHooksLM2_3 body.localDecls body.layouts) ()
          (translateStmt stmt) m₀ = (m_err, .error (.undefinedBehavior msg)) := by
      rw [heval_down]; unfold Miri.Interpreter.runRvalue
      have hdo :
          (do
            lm23WriteAggregateFieldsAux
              (annealAggregateHooksLM2_3 body.localDecls body.layouts
                (ops.map translateOperand).toArray)
              ⟨.memory mp, varLay⟩ 0 (ops.map translateOperand)
            (annealAggregateHooksLM2_3 body.localDecls body.layouts
              (ops.map translateOperand).toArray).writeDiscriminant () variantIdx
              ⟨.local 0 dstIdx none tf₀.localsIdentity,
                translateTy dstDecl.ty body.layouts⟩) m_down =
          EStateM.Result.error (.undefinedBehavior msg) m_err := hm_err
      rw [hdo]
    have hstep_err :=
      miri_step_at_statement_error (annealStepHooksLM2_3 body.localDecls body.layouts)
        hframes₀ hbody₀ hloc₀ hbb hstmt hm_ub
    dsimp only [mRes]
    rw [ha_ub, hstep_err]
    exact ⟨.ub _ _, fun hno => False.elim (hno msg rfl)⟩
  · dsimp only [List.nil_append] at hpart_end
    obtain ⟨_, _, _, _, _, _, _, _, _, vars, _, hvars_eq, _⟩ := hvalid.table_entry
    have hwd_hook :
        (annealAggregateHooksLM2_3 body.localDecls body.layouts
          (ops.map translateOperand).toArray).writeDiscriminant () variantIdx
          ⟨.local 0 dstIdx none tf₀.localsIdentity,
            translateTy dstDecl.ty body.layouts⟩ =
        Miri.Interpreter.Discriminant.writeDiscriminant
          (annealDiscriminantHooksLM2_3 body.localDecls body.layouts) () variantIdx
          ⟨.local 0 dstIdx none tf₀.localsIdentity,
            translateTy dstDecl.ty body.layouts⟩ := by
      unfold annealAggregateHooksLM2_3
      dsimp only
      rw [hvars_eq]
    obtain ⟨u, hu_lt, alloc_final, words_final, mscTag, hu_eq, hwd_ok, hlive_final,
        hrelTag, hbs_f, hlen_f, hmut_f, hpmap_f, hmask_f, hbits_f, hraw_f,
        htag_init_f, htag_read_f⟩ :=
      writeDiscriminant_indirect_local_ok body.localDecls (iden := tf₀.localsIdentity)
        hf_end hlt_end hdst_end hvalid hv hprov hmeta hlive_end hbase_end hptr
        hpart_end.byteSize_eq hpart_end.alloc_len_eq hpart_end.mut_alloc
        hpart_end.prov_empty hpart_end.mask_rel
    let m_final : AnnealStepState :=
      { m_end with
        machine := updateAllocMachine m_end.machine u allocId la_end.kind alloc_final }
    have hm_ok :
        Miri.Interpreter.Step.evalStatement (annealStepHooksLM2_3 body.localDecls body.layouts) ()
          (translateStmt stmt) m₀ = (m_final, .ok ()) := by
      rw [heval_down]
      unfold Miri.Interpreter.runRvalue
      dsimp only [Bind.bind, EStateM.bind]
      rw [hm_ok_ops]
      dsimp only
      rw [hwd_hook, hwd_ok]
    have hlt_af : dstIdx < s.frame.locals.length := by
      unfold get? at hdst_slot
      exact (List.getElem?_eq_some_iff.mp hdst_slot).1
    have hset_af :
        set? s.frame.locals dstIdx (.init (.aggregate variantIdx vals)) =
          some (s.frame.locals.set dstIdx (.init (.aggregate variantIdx vals))) := by
      unfold set?; simp [hlt_af]
    have ha_ok :
        evalStmt s stmt body.localDecls body.layouts =
          MirStepNode.step (advanceStmt s
            (s.frame.locals.set dstIdx (.init (.aggregate variantIdx vals))) s.memory) := by
      unfold evalStmt; rw [hkind]; dsimp only [evalRvalue, evalAggregateAdt]
      rw [hbor, hcaller, hok_ops]
      dsimp only
      rw [hdst_slot]
      cases slot_dst with
      | dead => exact absurd rfl hnot_dead
      | uninit | init _ =>
        dsimp only
        rw [hset_af, hprot, hbor]
        dsimp only [invalidateConflictingBorrows]
        apply congrArg MirStepNode.step
        apply congrArg (fun mem' =>
          advanceStmt s (s.frame.locals.set dstIdx (.init (.aggregate variantIdx vals))) mem')
        cases hm : s.memory; simp_all
    have hstep_ok :=
      miri_step_at_statement_ok (annealStepHooksLM2_3 body.localDecls body.layouts)
        hframes₀ hbody₀ hloc₀ hbb hstmt hm_ok hf_end hfr_end.location_eq
    dsimp only [mRes]
    rw [ha_ok, hstep_ok]
    have htb_nat : (translateSizeBytes tagBytes).bytes.toNat = tagBytes := by
      rcases hvalid.tagBytes_valid with rfl | rfl | rfl | rfl <;> rfl
    have hrawEnd_len : (lm22AllocRaw la_end.allocation).size =
        la_end.allocation.byteSize.bytes.toNat := by
      have : (lm22AllocRaw la_end.allocation).size = la_end.allocation.len := by
        cases la_end.allocation; rfl
      rw [this, hpart_end.alloc_len_eq]
    have hrawFin_len : (lm22AllocRaw alloc_final).size =
        alloc_final.byteSize.bytes.toNat := by
      have : (lm22AllocRaw alloc_final).size = alloc_final.len := by
        cases alloc_final; rfl
      rw [this, hlen_f, hbs_f, hpart_end.alloc_len_eq]
    have henum_final : EnumMemRel m_final.machine dstDecl.ty body.layouts tagBytes variants
        variantIdx vals mp := by
      refine .mk allocId borTag baseAddr ⟨la_end.kind, alloc_final⟩ words_final mscTag
        hvalid hv hprov hmis hmeta hlive_final hbase_end hptr hovf hmut_f halign
        (hbs_f.trans hpart_end.byteSize_eq)
        (hlen_f.trans (hpart_end.alloc_len_eq.trans (by rw [hbs_f])))
        hpmap_f (by rw [hbs_f]; exact hmask_f) hrelTag ?_ htag_init_f htag_read_f ?_
      · intro b hb_tag
        have hb_sz : b < la_end.allocation.byteSize.bytes.toNat := by
          rw [hpart_end.byteSize_eq]; have := hvalid.size_ge_tag; omega
        rw [hbits_f b hb_sz]
        simp [hb_tag]
      · intro i hi
        obtain ⟨sc_i, msc_i, hget_i, hrel_i, hsz_i, hbool_i, hchar_i, hinit_i, hread_i⟩ :=
          hpart_end.fields_rel i hi
        let f_i := (variants[variantIdx]'hv)[i]'hi
        have hafter_i : tagBytes ≤ f_i.offset.bytes.toNat :=
          hvf.fields_after_tag i hi
        have hbnd_i :
            f_i.offset.bytes.toNat + f_i.fieldLayout.size.bytes.toNat ≤
              la_end.allocation.byteSize.bytes.toNat := by
          rw [hpart_end.byteSize_eq]; exact hvf.fields_in_bounds i hi
        have hpos_i : 0 < f_i.fieldLayout.size.bytes.toNat := by
          rw [hsz_i]; exact translateSizeBytes_pos_lm2_3 hrel_i.validBytes
        have hbits_i : ∀ b, f_i.offset.bytes.toNat ≤ b →
            b < f_i.offset.bytes.toNat + f_i.fieldLayout.size.bytes.toNat →
            maskBlocksGetBit words_final b = true := by
          intro b hlo hhi
          have hb_sz : b < la_end.allocation.byteSize.bytes.toNat := by omega
          have hb_enum : b < (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat := by
            rw [← hpart_end.byteSize_eq]; exact hb_sz
          rw [hbits_f b hb_sz, hpart_end.bits_eq b hb_enum]
          have hex : ∃ j, ∃ (hj : j < (variants[variantIdx]'hv).length),
              ((variants[variantIdx]'hv)[j]'hj).offset.bytes.toNat ≤ b ∧
              b < ((variants[variantIdx]'hv)[j]'hj).offset.bytes.toNat +
                ((variants[variantIdx]'hv)[j]'hj).fieldLayout.size.bytes.toNat :=
            ⟨i, hi, hlo, hhi⟩
          simp [hex]
        have hinit'_i :
            alloc_final.initializationMask.isRangeInitialized
              (Miri.Memory.allocRange f_i.offset f_i.fieldLayout.size) = .ok (.ok ()) :=
          initMaskWordRel_isRangeInitialized hmask_f hpos_i hbnd_i hbits_i
        have hread'_i :
            alloc_final.readScalar annealTargetDataLayout
              (Miri.Memory.allocRange f_i.offset f_i.fieldLayout.size) false =
            .ok (.fromScalarInt msc_i) := by
          rw [alloc_readScalar_congr hrawEnd_len hrawFin_len hbs_f hinit_i hinit'_i hbnd_i ?_]
          · exact hread_i
          · rw [hraw_f]
            have hex := extract_writeBytes_disjoint (s := 0) (lm22AllocRaw la_end.allocation)
              (lm22LeBytes variantIdx (translateSizeBytes tagBytes).bytes.toNat)
              (lm22LeBytes_size _ _)
              (by rw [Nat.zero_add, hrawEnd_len, hpart_end.byteSize_eq, htb_nat]; exact hvalid.size_ge_tag)
              (by rw [hrawEnd_len]; exact hbnd_i)
              (Or.inr (by rw [Nat.zero_add, htb_nat]; exact hafter_i))
            rw [Nat.zero_add] at hex
            exact hex
        exact Or.inl ⟨sc_i, msc_i, hget_i, hrel_i, hsz_i, hbool_i, hchar_i,
          hbits_i, hinit'_i, hread'_i⟩
    have hfr_final_ex : FrameRelLM2_3Except body env dstIdx m_final.machine s.frame tf_end :=
      hfr_end.of_updateAlloc_excl hdisj_end hdst_end hprov hu_lt hu_eq
    have hloc_dst_final : LocalRelLM2_3 env m_final.machine dstDecl body.layouts
        (.init (.aggregate variantIdx vals))
        ⟨.live (.indirect mp), some (translateTy dstDecl.ty body.layouts)⟩ :=
      .enumInd tagBytes variants variantIdx vals mp
        (some (translateTy dstDecl.ty body.layouts)) henv_dst
        (fun _ hl => (Option.some.inj (Option.mem_def.mp hl)).symm)
        henum_final
    have hmf_dst_end : tf_end.locals[dstIdx]? =
        some ⟨.live (.indirect mp), some (translateTy dstDecl.ty body.layouts)⟩ := by
      rw [Array.getElem?_eq_getElem hlt_end, hdst_end]
    have hfr_done : FrameRelLM2_3 body env m_final.machine
        { s.frame with locals := s.frame.locals.set dstIdx (.init (.aggregate variantIdx vals)) }
        tf_end :=
      hfr_final_ex.finish_dst hdst_decl hset_af hmf_dst_end hloc_dst_final
    have hsup_final : AllocIdSupplyValid allocBudget m_final.machine.memory :=
      hsup_end.of_updateAlloc hu_lt hu_eq
    refine ⟨.step _ _ ?_, fun _ => ⟨?_, ?_, ?_⟩⟩
    · exact .mk
        { tf_end with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
        rfl (hrc_end.trans hrc_down)
        ⟨retLay, (hrp_end.trans hrp_down).trans (by rw [hid_end])⟩
        hfr_done.step_pc hsup_final
        hcal hstack hbor hprot hcaller hdisj_end
    · intro hw0 b hb_ge hb_lt hnot_in
      subst hw0
      intro tf' mp' c' id' bt' la' hf' hloc' hprov' hfind'
      injection hf' with hf_arr; injection hf_arr with htf_eq; subst htf_eq
      dsimp at hloc'
      rw [hmf_dst_end] at hloc'
      injection hloc' with hls_eq
      have hmp_eq : mp = mp' := by
        injection hls_eq with hv_eq; injection hv_eq with ho_eq; injection ho_eq
      cases hmp_eq
      rw [hprov] at hprov'; injection hprov' with hp_eq; injection hp_eq with hid_eq _
      subst hid_eq
      have hlive_find' :
          m_final.machine.memory.live.find? (fun (k0, _) => k0 == allocId) =
            some (allocId, ⟨la_end.kind, alloc_final⟩) := hlive_final.1
      rw [hlive_find'] at hfind'
      injection hfind' with hpair_eq; injection hpair_eq with _ hla_eq; subst hla_eq
      have hb_sz : b < la_end.allocation.byteSize.bytes.toNat := by
        rw [hpart_end.byteSize_eq]; exact hb_lt
      dsimp only
      rw [initMaskWordRel_get hmask_f hb_sz]
      congr 1
      rw [hbits_f b hb_sz, hpart_end.bits_eq b hb_lt, maskBlocksGetBit_initWordsFalse]
      have hnot_tag : decide (b < tagBytes) = false := decide_eq_false (by omega)
      have hnot_ex :
          decide (∃ j, ∃ (hj : j < (variants[variantIdx]'hv).length),
            ((variants[variantIdx]'hv)[j]'hj).offset.bytes.toNat ≤ b ∧
            b < ((variants[variantIdx]'hv)[j]'hj).offset.bytes.toNat +
              ((variants[variantIdx]'hv)[j]'hj).fieldLayout.size.bytes.toNat) = false := by
        apply decide_eq_false
        rintro ⟨j, hj, hlo, hhi⟩
        rcases hnot_in j hj with h1 | h2 <;> omega
      rw [hnot_ex, hnot_tag]
      rfl
    · intro localId b hne_id hu₀
      have hu_e := hu_end localId b hne_id (hu_down localId b hne_id hu₀)
      intro tf' mp' c' id' bt' la' hf' hloc' hprov' hfind'
      injection hf' with hf_arr; injection hf_arr with htf_eq; subst htf_eq
      dsimp at hloc'
      have hd_ne := hdisj_end localId dstIdx mp' mp c' _ hne_id hloc' hmf_dst_end
      have hid_ne : id' ≠ allocId := by
        intro hid_eq; apply hd_ne; rw [hprov', hprov, hid_eq]; rfl
      have hfind_old :
          m_end.machine.memory.live.find? (fun (k0, _) => k0 == id') = some (id', la') := by
        dsimp [m_final, updateAllocMachine] at hfind'
        obtain ⟨hbeq_id, idx_f, hlt_f, hget_f, hnot_before⟩ :=
          Array.find?_eq_some_iff_getElem.mp hfind'
        have hlt_orig : idx_f < m_end.machine.memory.live.size := by
          rwa [Array.size_setIfInBounds] at hlt_f
        have hne_u : idx_f ≠ u := by
          intro rfl
          rw [Array.getElem_setIfInBounds_self] at hget_f
          injection hget_f with hk_eq
          exact hid_ne hk_eq.symm
        rw [Array.getElem_setIfInBounds_ne hlt_orig (Ne.symm hne_u)] at hget_f
        rw [Array.find?_eq_some_iff_getElem]
        refine ⟨hbeq_id, idx_f, hlt_orig, hget_f, ?_⟩
        intro j hj
        by_cases hju : j = u
        · subst hju; rw [hu_eq]; simp [Ne.symm hid_ne]
        · have hprev := hnot_before j hj
          rwa [Array.getElem_setIfInBounds_ne (Nat.lt_trans hj hlt_orig) (Ne.symm hju)] at hprev
      exact hu_e tf_end mp' c' id' bt' la' hf_end hloc' hprov' hfind_old
    · intro j hne hj₀ tf' hf'
      injection hf' with ha; injection ha with ht; subst ht
      exact himm_end j (himm_down j hne hj₀)

/-- **Deliverable 1 (`evalRvalue_aggregate_enum_simulation`)**:
Constructing a multi-variant direct-tagged enum (`AggregateKind.Adt adtDefId
variantIdx none`) into `dstIdx` steps Anneal's `stepMirFn` and `lean-miri`'s
`Miri.Interpreter.Step.step (annealStepHooksLM2_3 ...)` (which executes vendored
`Miri.Interpreter.writeAggregate` +
`Miri.Interpreter.Discriminant.writeDiscriminant`) in lockstep:
* When `dstIdx` is `.dead`, both machines diagnose `"write to dead local"` UB.
* When any payload operand is `.dead` or `.uninit`, both machines diagnose UB.
* When `dstIdx` is live (`.uninit` immediate, `.uninit` indirect, or an
  already-initialized variant) and all payload operands evaluate to scalars,
  both machines step to `StateRelLM2_3`-related states storing
  `Value.aggregate variantIdx fieldVals` with tag `⟨variantIdx, tagBytes⟩`
  at `[0, tagBytes)` and active-variant payload scalars at their per-variant
  offsets; moreover, when `dstIdx` started `.uninit`, every non-payload byte
  `b ≥ tagBytes` of `dstIdx` satisfies `EnumLocalByteUninit` (enabling
  subsequent inactive-variant `Downcast` + `Field` reads to diagnose UB in
  lockstep). -/
theorem evalRvalue_aggregate_enum_simulation
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_3 body env (allocBudget + 1) s m)
    (henv_valid : ∀ ty tb vs, env ty = some (tb, vs) →
      ValidEnumLayout ty body.layouts tb vs)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    {dstIdx : Local} {dstDecl : LocalDecl}
    {adtDefId : String} {variantIdx : Nat} {ops : List MirAst.Operand}
    {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hkind : stmt.kind = .assign ⟨dstIdx, .nil⟩ (.aggregate (.adt adtDefId variantIdx .none) ops))
    (hdst_decl : get? body.localDecls dstIdx = some dstDecl)
    (henv_dst : env dstDecl.ty = some (tagBytes, variants))
    (hv : variantIdx < variants.length)
    (hops_len : ops.length = (variants[variantIdx]'hv).length)
    (hops_wt : ∀ topFrame (i : Nat) (hi : i < ops.length),
      m.stack.frames = #[topFrame] →
      WellTypedEnumScalarOp body topFrame (ops[i]'hi)
        ((variants[variantIdx]'hv)[i]'(by omega)).ty) :
    let mRes := Miri.Interpreter.Step.step (annealStepHooksLM2_3 body.localDecls body.layouts) () m
    StepRelLM2_3 body env allocBudget m (stepMirFn body s) mRes ∧
    ((∀ msg, mRes.2 ≠ .error (.undefinedBehavior msg)) →
      (get? s.frame.locals dstIdx = some .uninit →
        ∀ b, tagBytes ≤ b →
          b < (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat →
          (∀ j (hj : j < (variants[variantIdx]'hv).length),
            b < ((variants[variantIdx]'hv)[j]'hj).offset.bytes.toNat ∨
              ((variants[variantIdx]'hv)[j]'hj).offset.bytes.toNat +
                ((variants[variantIdx]'hv)[j]'hj).fieldLayout.size.bytes.toNat ≤ b) →
          EnumLocalByteUninit mRes.1 dstIdx b) ∧
      (∀ localId b, localId ≠ dstIdx →
        EnumLocalByteUninit m localId b → EnumLocalByteUninit mRes.1 localId b) ∧
      (∀ j, j ≠ dstIdx →
        IsImmediateStepLocal m j → IsImmediateStepLocal mRes.1 j)) := by
  intro mRes
  rcases hstate with ⟨tf₀, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
    halloc, hcal, hstack, hbor, hprot, hcaller, hdisj₀⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  obtain ⟨slot_dst, mls_dst, hlt_d0, hslot_dst, hmls_dst_eq, hloc_dst⟩ :=
    hframe.lookup_local hdst_decl
  have hvalid := henv_valid dstDecl.ty tagBytes variants henv_dst
  obtain ⟨_, _, _, _, _, _, _, _, _, vars, hvars_sz, hvars_eq, hvf_all⟩ :=
    hvalid.table_entry
  have hvf := hvf_all variantIdx hv
  obtain ⟨varLay, hdown_ok, _, _, _, _, _, hoff_var⟩ := downcastEnumLayout_ok hvalid hv
  have his_enum_loc : isEnumLocal body.localDecls body.layouts dstIdx = true := by
    unfold isEnumLocal lookupLocalDeclLayout
    simp [hdst_decl, hvalid.isEnumLayout_true]
  have hlm_assign :
      lm23Assign body.localDecls body.layouts ⟨dstIdx, #[]⟩
        (.Aggregate (.Adt 0 variantIdx #[] none none)
          (ops.map translateOperand).toArray) = true := by
    unfold lm23Assign
    simp [his_enum_loc]
  have htrans_stmt :
      translateStmt stmt =
        { sourceInfo := defaultSourceInfo
          kind := .Assign ⟨dstIdx, #[]⟩
            (.Aggregate (.Adt 0 variantIdx #[] none none)
              (ops.map translateOperand).toArray) } := by
    rcases stmt with ⟨sk, sspan⟩
    dsimp only at hkind; subst hkind; rfl
  have hcache_d : ∀ l, (tf₀.locals[dstIdx]'hlt_d0).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_dst_eq]; exact hloc_dst.layout_eq
  let tf_c := cacheFrameLocalLayout tf₀ dstIdx hlt_d0 (translateTy dstDecl.ty body.layouts)
  have heval_p := annealEvalPlace_unprojected hframes hlt_d0 hdst_decl hcache_d
  have heval_stmt_m :
      Miri.Interpreter.Step.evalStatement (annealStepHooksLM2_3 body.localDecls body.layouts) ()
        (translateStmt stmt) m =
      Miri.Interpreter.runRvalue
        (do
          let dest ← annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩
          Miri.Interpreter.writeAggregate
            (annealAggregateHooksLM2_3 body.localDecls body.layouts
              (ops.map translateOperand).toArray) ()
            (.Adt 0 variantIdx #[] none none)
            (ops.map translateOperand).toArray dest) m := by
    rw [htrans_stmt]
    unfold Miri.Interpreter.Step.evalStatement annealStepHooksLM2_3
    dsimp only
    rw [hlm_assign]
    rfl
  cases hloc_dst with
  | base _ _ hnone _ =>
    rw [henv_dst] at hnone; cases hnone
  | enumDead _ _ cd _ _ hc_d =>
    have hdead_d : tf₀.locals[dstIdx]'hlt_d0 = ⟨.dead, cd⟩ := hmls_dst_eq
    have hlt_c : dstIdx < tf_c.locals.size := by
      dsimp [tf_c, cacheFrameLocalLayout]; rw [Array.size_set]; exact hlt_d0
    have hdead_c : tf_c.locals[dstIdx]'hlt_c =
        ⟨.dead, some (translateTy dstDecl.ty body.layouts)⟩ := by
      dsimp [tf_c, cacheFrameLocalLayout]
      simp only [Array.getElem_set, ↓reduceIte, hdead_d]
    have hfa_err :
        annealForceEnumAllocation body.localDecls body.layouts
          ⟨.local 0 dstIdx none tf₀.localsIdentity,
            translateTy dstDecl.ty body.layouts⟩
          { m with stack := ⟨#[tf_c]⟩ } =
        .error (.undefinedBehavior "write to dead local")
          { m with stack := ⟨#[tf_c]⟩ } := by
      unfold annealForceEnumAllocation
      rw [forceAllocation_dead_err (m := { m with stack := ⟨#[tf_c]⟩ }) rfl hlt_c hdead_c]
    have hm_err :
        Miri.Interpreter.Step.evalStatement (annealStepHooksLM2_3 body.localDecls body.layouts) ()
          (translateStmt stmt) m =
        ({ m with stack := ⟨#[tf_c]⟩ }, .error (.undefinedBehavior "write to dead local")) := by
      rw [heval_stmt_m]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok heval_p, writeAggregate_enum_eq]
      dsimp only [annealAggregateHooksLM2_3, Bind.bind, EStateM.bind]
      rw [hvars_eq]
      dsimp only [Bind.bind, EStateM.bind]
      rw [hfa_err]
    have hops_shape :=
      evalOperands_enumScalarOps_shape s.frame.locals s.memory.globals hframe.af_locals_len ops
        (fun k hk => ⟨_, hops_wt tf₀ k hk hframes⟩)
    have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; rw [hkind]; dsimp only [evalRvalue, evalAggregateAdt]
      rw [hbor, hcaller]
      rcases hops_shape with hub_o | ⟨vals, hok_o⟩
      · rw [hub_o]
      · rw [hok_o]; dsimp only; rw [hslot_dst]
    have hstep_err :=
      miri_step_at_statement_error (annealStepHooksLM2_3 body.localDecls body.layouts)
        hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err
    dsimp only [mRes]
    rw [ha_ub, hstep_err]
    exact ⟨.ub _ _, fun hno => False.elim (hno "write to dead local" rfl)⟩
  | enumUninitImm _ _ cd _ _ _ =>
    have hlt_c : dstIdx < tf_c.locals.size := by
      dsimp [tf_c, cacheFrameLocalLayout]; rw [Array.size_set]; exact hlt_d0
    have himm_c : tf_c.locals[dstIdx]'hlt_c =
        ⟨.live (.immediate .uninit), some (translateTy dstDecl.ty body.layouts)⟩ := by
      dsimp [tf_c, cacheFrameLocalLayout]
      simp only [Array.getElem_set, ↓reduceIte, hmls_dst_eq]
    obtain ⟨rawAlloc, htry, hbs0, hlen0, hmut0, hpmap0, hmask0⟩ :=
      tryNew_uninit_of_pow2_le_29 (translateTy dstDecl.ty body.layouts).layout.size
        (translateTy dstDecl.ty body.layouts).layout.align.abi hvalid.align_pow2_le
    obtain ⟨mem', newId, hres, _, hlive_eq, hfresh, hwm_next, hovf_all⟩ :=
      halloc.of_succ.reserve_step
    let a0 := rawAlloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree)
    let tf_down :=
      { tf_c with
        locals := tf_c.locals.set dstIdx
          ⟨.live (.indirect (stackAllocPlace newId)),
            some (translateTy dstDecl.ty body.layouts)⟩ hlt_c }
    let m_down : AnnealStepState :=
      ⟨⟨#[tf_down]⟩, stackAllocMachine m.machine mem' newId a0⟩
    have hfa_ok :
        annealForceEnumAllocation body.localDecls body.layouts
          ⟨.local 0 dstIdx none tf₀.localsIdentity,
            translateTy dstDecl.ty body.layouts⟩
          { m with stack := ⟨#[tf_c]⟩ } =
        .ok ⟨stackAllocPlace newId, translateTy dstDecl.ty body.layouts⟩ m_down := by
      unfold annealForceEnumAllocation
      rw [forceAllocation_uninit_none_ok (m := { m with stack := ⟨#[tf_c]⟩ })
        rfl hlt_c himm_c hvalid.isSized_true htry hres]
    have heval_down :
        Miri.Interpreter.Step.evalStatement (annealStepHooksLM2_3 body.localDecls body.layouts) ()
          (translateStmt stmt) m =
        Miri.Interpreter.runRvalue
          (do
            lm23WriteAggregateFieldsAux
              (annealAggregateHooksLM2_3 body.localDecls body.layouts
                (ops.map translateOperand).toArray)
              ⟨.memory (stackAllocPlace newId), varLay⟩ 0 (ops.map translateOperand)
            (annealAggregateHooksLM2_3 body.localDecls body.layouts
              (ops.map translateOperand).toArray).writeDiscriminant () variantIdx
              ⟨.local 0 dstIdx none tf₀.localsIdentity,
                translateTy dstDecl.ty body.layouts⟩) m_down := by
      rw [heval_stmt_m]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok heval_p, writeAggregate_enum_eq]
      dsimp only [annealAggregateHooksLM2_3, Bind.bind, EStateM.bind]
      rw [hvars_eq]
      dsimp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
      rw [hfa_ok]
      dsimp only
      rw [hdown_ok]
      rfl
    have hfr_c_ex := (FrameRelLM2_3Except.of_frameRel (excl := dstIdx)
      (hframe.cache_local_layout hdst_decl hlt_d0))
    have hdisj_c := MemoryAllocDisjoint_cacheFrameLocalLayout hdisj₀ hlt_d0
      (translateTy dstDecl.ty body.layouts)
    have hfr_down : FrameRelLM2_3Except body env dstIdx m_down.machine s.frame tf_down :=
      hfr_c_ex.of_stackAlloc_set_excl (alloc := a0) hres (hlt := hlt_c)
        ⟨.live (.indirect (stackAllocPlace newId)),
          some (translateTy dstDecl.ty body.layouts)⟩
    have hdisj_down := MemoryAllocDisjoint_set_fresh_stackAlloc_lm2_3
      (lay := some (translateTy dstDecl.ty body.layouts)) hfr_c_ex hdisj_c hfresh hlt_c
    have hfresh' : mem'.live.any (fun entry => entry.1 == newId) = false := by
      rw [hlive_eq]; exact hfresh
    have hlt_down : dstIdx < tf_down.locals.size := by
      dsimp [tf_down]; rw [Array.size_set]; exact hlt_c
    have hdst_down : tf_down.locals[dstIdx]'hlt_down =
        ⟨.live (.indirect (stackAllocPlace newId)),
          some (translateTy dstDecl.ty body.layouts)⟩ := by
      dsimp [tf_down]; rw [Array.getElem_set_self]
    have hops_wt_down : ∀ i (hi : i < ops.length),
        WellTypedEnumScalarOp body tf_down (ops[i]'hi)
          ((variants[variantIdx]'hv)[i]'(by omega)).ty := by
      intro i hi
      have hwt0 := hops_wt tf₀ i hi hframes
      generalize ops[i]'hi = op_i at hwt0 ⊢
      generalize ((variants[variantIdx]'hv)[i]'(by omega)).ty = fty at hwt0 ⊢
      cases hwt0 with
      | constScalar c sc h1 h2 h3 h4 h5 h6 h7 =>
        exact .constScalar c sc h1 h2 h3 h4 h5 h6 h7
      | copyLocal idx decl hd hp himm =>
        have hnone := env_none_of_isPrimScalarTy henv_valid hp
        have hne_idx : idx ≠ dstIdx := by
          intro rfl; rw [hdst_decl] at hd; injection hd with he; subst he
          rw [hnone] at henv_dst; cases henv_dst
        refine .copyLocal idx decl hd hp (fun mls hget => ?_)
        dsimp [tf_down] at hget
        rw [Array.getElem?_set_ne _ (Ne.symm hne_idx)] at hget
        dsimp [tf_c, cacheFrameLocalLayout] at hget
        rw [Array.getElem?_set_ne _ (Ne.symm hne_idx)] at hget
        exact himm mls hget
    have hmask_a0 : InitMaskWordRel a0.initializationMask a0.byteSize
        (initWordsFalse (translateTy dstDecl.ty body.layouts).layout.size) := by
      dsimp [a0]
      rw [hmask0, hbs0]
      exact initMaskWordRel_new_false
    have hu_down : ∀ localId b, localId ≠ dstIdx →
        EnumLocalByteUninit m localId b → EnumLocalByteUninit m_down localId b := by
      intro localId b hne_id hu₀
      intro tf' mp' c' id' bt' la' hf' hloc' hprov' hfind'
      injection hf' with hf_arr; injection hf_arr with htf_eq; subst htf_eq
      dsimp [tf_down] at hloc'
      rw [Array.getElem?_set_ne _ (Ne.symm hne_id)] at hloc'
      dsimp [tf_c, cacheFrameLocalLayout] at hloc'
      rw [Array.getElem?_set_ne _ (Ne.symm hne_id)] at hloc'
      have hid_ne : id' ≠ newId := by
        intro rfl
        obtain ⟨hlt_l, _⟩ := Array.getElem?_eq_some_iff.mp hloc'
        have hlt_d : localId < body.localDecls.length := by
          have h1 : localId < length body.localDecls := hframe.mf_locals_size ▸ hlt_l; exact h1
        have hlt_af : localId < s.frame.locals.length := by
          have h1 : localId < length body.localDecls := hframe.mf_locals_size ▸ hlt_l
          have h2 : localId < length s.frame.locals := hframe.af_locals_len ▸ h1; exact h2
        have hdecl_l : get? body.localDecls localId = some (body.localDecls[localId]'hlt_d) := by
          unfold get?; exact List.getElem?_eq_getElem hlt_d
        have hsl_l : get? s.frame.locals localId = some (s.frame.locals[localId]'hlt_af) := by
          unfold get?; exact List.getElem?_eq_getElem hlt_af
        have hloc_l := hframe.locals_rel localId _ _ _ hdecl_l hsl_l hloc'
        obtain ⟨id_k, hid_k, hany_k⟩ := hloc_l.allocLive mp' rfl
        rw [hprov'] at hid_k; dsimp [Miri.Memory.Provenance.getAllocId] at hid_k
        injection hid_k with hid_eq; subst hid_eq
        rw [hfresh] at hany_k; cases hany_k
      have hfind_old :
          m.machine.memory.live.find? (fun (k0, _) => k0 == id') = some (id', la') := by
        dsimp [m_down, stackAllocMachine] at hfind'
        rw [hlive_eq, Array.find?_push] at hfind'
        have hbeq_f : ((newId, ({ kind := .stack, allocation := a0 } : AnnealLocalAlloc)).1 == id') = false :=
          beq_eq_false_iff_ne.mpr (Ne.symm hid_ne)
        dsimp at hbeq_f
        simp [hbeq_f] at hfind'
        exact hfind'
      exact hu₀ tf₀ mp' c' id' bt' la' hframes hloc' hprov' hfind_old
    have himm_down : ∀ j, j ≠ dstIdx →
        IsImmediateStepLocal m j → IsImmediateFrameLocal tf_down j := by
      intro j hne hj₀ mls hmls
      dsimp [tf_down] at hmls
      rw [Array.getElem?_set_ne _ (Ne.symm hne)] at hmls
      dsimp [tf_c, cacheFrameLocalLayout] at hmls
      rw [Array.getElem?_set_ne _ (Ne.symm hne)] at hmls
      exact hj₀ tf₀ hframes mls hmls
    obtain ⟨hstep_rel, hpost⟩ :=
      finish_aggregate_enum_from_indirect henv_valid hframes hframe.body_eq
        hframe.location_eq hcal hstack hbor hprot hcaller hbb hstmt hkind
        hdst_decl henv_dst hvalid hvf hoff_var hops_len hops_wt_down
        hslot_dst nofun heval_down rfl hretCont hretPlace hlt_down hdst_down
        hfr_down hdisj_down (Or.inr (hwm_next a0)) rfl rfl rfl
        (LiveAllocEntry.of_push_fresh_self _ hfresh')
        (lookupBaseAddr_stackAllocMachine_self _ _ _ _)
        rfl (hovf_all _ hvalid.size_lt_4gib)
        (annealStackBaseAddr_isAligned newId _ hvalid.align_pow2_le)
        hmut0 hbs0 (by dsimp [a0]; rw [hlen0, hbs0]) hpmap0 hmask_a0 hu_down
        himm_down
    exact ⟨hstep_rel, fun hno => ⟨fun _ => (hpost hno).1 rfl, (hpost hno).2⟩⟩
  | enumUninitInd _ _ mp cd _ _ hmp =>
    rcases hmp with ⟨allocId, borTag, baseAddr, localAlloc, _, hprov, hmis, hmeta,
      hlive, hbase, hptr, hovf, hmut, halign, hbs, hlen, hpmap, hmask_u⟩
    have hlt_c : dstIdx < tf_c.locals.size := by
      dsimp [tf_c, cacheFrameLocalLayout]; rw [Array.size_set]; exact hlt_d0
    have hind_c : tf_c.locals[dstIdx]'hlt_c =
        ⟨.live (.indirect mp), some (translateTy dstDecl.ty body.layouts)⟩ := by
      dsimp [tf_c, cacheFrameLocalLayout]
      simp only [Array.getElem_set, ↓reduceIte, hmls_dst_eq]
    have hfa_ok :
        annealForceEnumAllocation body.localDecls body.layouts
          ⟨.local 0 dstIdx none tf₀.localsIdentity,
            translateTy dstDecl.ty body.layouts⟩
          { m with stack := ⟨#[tf_c]⟩ } =
        .ok ⟨mp, translateTy dstDecl.ty body.layouts⟩
          { m with stack := ⟨#[tf_c]⟩ } := by
      unfold annealForceEnumAllocation
      rw [forceAllocation_indirect_none_ok (m := { m with stack := ⟨#[tf_c]⟩ }) rfl hlt_c hind_c]
    have heval_down :
        Miri.Interpreter.Step.evalStatement (annealStepHooksLM2_3 body.localDecls body.layouts) ()
          (translateStmt stmt) m =
        Miri.Interpreter.runRvalue
          (do
            lm23WriteAggregateFieldsAux
              (annealAggregateHooksLM2_3 body.localDecls body.layouts
                (ops.map translateOperand).toArray)
              ⟨.memory mp, varLay⟩ 0 (ops.map translateOperand)
            (annealAggregateHooksLM2_3 body.localDecls body.layouts
              (ops.map translateOperand).toArray).writeDiscriminant () variantIdx
              ⟨.local 0 dstIdx none tf₀.localsIdentity,
                translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[tf_c]⟩ } := by
      rw [heval_stmt_m]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok heval_p, writeAggregate_enum_eq]
      dsimp only [annealAggregateHooksLM2_3, Bind.bind, EStateM.bind]
      rw [hvars_eq]
      dsimp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
      rw [hfa_ok]
      dsimp only
      rw [hdown_ok]
      rfl
    have hops_wt_c : ∀ i (hi : i < ops.length),
        WellTypedEnumScalarOp body tf_c (ops[i]'hi)
          ((variants[variantIdx]'hv)[i]'(by omega)).ty :=
      fun i hi => (hops_wt tf₀ i hi hframes).mono_immediate
        (fun _ hj => hj.cache_layout hlt_d0 _)
    have hmask₀ : InitMaskWordRel localAlloc.allocation.initializationMask
        localAlloc.allocation.byteSize
        (initWordsFalse (translateTy dstDecl.ty body.layouts).layout.size) := by
      rw [hmask_u, hbs]
      exact initMaskWordRel_new_false
    obtain ⟨hstep_rel, hpost⟩ :=
      finish_aggregate_enum_from_indirect henv_valid hframes hframe.body_eq
        hframe.location_eq hcal hstack hbor hprot hcaller hbb hstmt hkind
        hdst_decl henv_dst hvalid hvf hoff_var hops_len hops_wt_c
        hslot_dst nofun heval_down rfl hretCont hretPlace hlt_c hind_c
        (FrameRelLM2_3Except.of_frameRel (hframe.cache_local_layout hdst_decl hlt_d0))
        (MemoryAllocDisjoint_cacheFrameLocalLayout hdisj₀ hlt_d0 _)
        (halloc.mono (Nat.le_succ allocBudget))
        hprov hmis hmeta hlive hbase hptr hovf halign hmut hbs hlen hpmap hmask₀
        (fun _ _ _ hu => EnumLocalByteUninit.of_cache_layout hframes hu)
        (fun j _ hj₀ => (hj₀ tf₀ hframes).cache_layout hlt_d0 _)
    exact ⟨hstep_rel, fun hno => ⟨fun _ => (hpost hno).1 rfl, (hpost hno).2⟩⟩
  | enumInd _ _ v_old fv_old mp cd _ _ hmp =>
    rcases hmp with ⟨allocId, borTag, baseAddr, localAlloc, words_old, _,
      _, _, hprov, hmis, hmeta, hlive, hbase, hptr, hovf, hmut, halign,
      hbs, hlen, hpmap, hmask_old, _, _, _, _, _⟩
    have hlt_c : dstIdx < tf_c.locals.size := by
      dsimp [tf_c, cacheFrameLocalLayout]; rw [Array.size_set]; exact hlt_d0
    have hind_c : tf_c.locals[dstIdx]'hlt_c =
        ⟨.live (.indirect mp), some (translateTy dstDecl.ty body.layouts)⟩ := by
      dsimp [tf_c, cacheFrameLocalLayout]
      simp only [Array.getElem_set, ↓reduceIte, hmls_dst_eq]
    have hfa_ok :
        annealForceEnumAllocation body.localDecls body.layouts
          ⟨.local 0 dstIdx none tf₀.localsIdentity,
            translateTy dstDecl.ty body.layouts⟩
          { m with stack := ⟨#[tf_c]⟩ } =
        .ok ⟨mp, translateTy dstDecl.ty body.layouts⟩
          { m with stack := ⟨#[tf_c]⟩ } := by
      unfold annealForceEnumAllocation
      rw [forceAllocation_indirect_none_ok (m := { m with stack := ⟨#[tf_c]⟩ }) rfl hlt_c hind_c]
    have heval_down :
        Miri.Interpreter.Step.evalStatement (annealStepHooksLM2_3 body.localDecls body.layouts) ()
          (translateStmt stmt) m =
        Miri.Interpreter.runRvalue
          (do
            lm23WriteAggregateFieldsAux
              (annealAggregateHooksLM2_3 body.localDecls body.layouts
                (ops.map translateOperand).toArray)
              ⟨.memory mp, varLay⟩ 0 (ops.map translateOperand)
            (annealAggregateHooksLM2_3 body.localDecls body.layouts
              (ops.map translateOperand).toArray).writeDiscriminant () variantIdx
              ⟨.local 0 dstIdx none tf₀.localsIdentity,
                translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[tf_c]⟩ } := by
      rw [heval_stmt_m]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok heval_p, writeAggregate_enum_eq]
      dsimp only [annealAggregateHooksLM2_3, Bind.bind, EStateM.bind]
      rw [hvars_eq]
      dsimp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
      rw [hfa_ok]
      dsimp only
      rw [hdown_ok]
      rfl
    have hops_wt_c : ∀ i (hi : i < ops.length),
        WellTypedEnumScalarOp body tf_c (ops[i]'hi)
          ((variants[variantIdx]'hv)[i]'(by omega)).ty :=
      fun i hi => (hops_wt tf₀ i hi hframes).mono_immediate
        (fun _ hj => hj.cache_layout hlt_d0 _)
    obtain ⟨hstep_rel, hpost⟩ :=
      finish_aggregate_enum_from_indirect henv_valid hframes hframe.body_eq
        hframe.location_eq hcal hstack hbor hprot hcaller hbb hstmt hkind
        hdst_decl henv_dst hvalid hvf hoff_var hops_len hops_wt_c
        hslot_dst nofun heval_down rfl hretCont hretPlace hlt_c hind_c
        (FrameRelLM2_3Except.of_frameRel (hframe.cache_local_layout hdst_decl hlt_d0))
        (MemoryAllocDisjoint_cacheFrameLocalLayout hdisj₀ hlt_d0 _)
        (halloc.mono (Nat.le_succ allocBudget))
        hprov hmis hmeta hlive hbase hptr hovf halign hmut hbs hlen hpmap hmask_old
        (fun _ _ _ hu => EnumLocalByteUninit.of_cache_layout hframes hu)
        (fun j _ hj₀ => (hj₀ tf₀ hframes).cache_layout hlt_d0 _)
    exact ⟨hstep_rel, fun hno =>
      ⟨fun huninit => (by rw [hslot_dst] at huninit; cases huninit), (hpost hno).2⟩⟩

/-! ## 7. `Terminator.SwitchInt` Match Dispatch & Control Helpers (`LM-2.3`) -/

/-- `Miri.Interpreter.Step.step` under `annealStepHooksLM2_3` coincides with
`annealStepHooksLM2_2` whenever the active frame is positioned at a block terminator,
since `annealStepHooksLM2_3` leaves `beforeTerminator`, `terminator`, and
`returnFromCurrentFrame` identical to `annealStepHooksLM2_2`. -/
private theorem miri_step_LM2_3_eq_at_terminator
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[topFrame])
    (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none) :
    Miri.Interpreter.Step.step (annealStepHooksLM2_3 body.localDecls body.layouts) () m =
      Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m := by
  unfold Miri.Interpreter.Step.step
  rw [stack_currentFrame?_singleton m.stack topFrame hframes]
  dsimp only
  rw [hloc, hbody]
  dsimp only
  rw [translateBody_basicBlocks_getElem?, hbb]
  dsimp only [Option.map]
  rw [translateBasicBlockData_statements_getElem?, hstmt_none]
  rfl

/-- **Deliverable 5 (`enum_match_switchInt_simulation`)**:
Executing `Terminator.SwitchInt` on an enum discriminant scalar (or any
`WellTypedEnumScalarOp` of `bool` / `int` / `uint` type) steps Anneal's
`stepMirFn` and `lean-miri`'s `Miri.Interpreter.Step.step` under
`annealStepHooksLM2_3` (via vendored
`Miri.Interpreter.ControlFlow.evalTerminator`) in lockstep:
* When the discriminant operand is `.dead` or `.uninit`, both diagnose UB.
* When the discriminant operand evaluates to `sc`, both branch to
  `lookupSwitchTarget sc.bits targets.branches targets.otherwise` (matching arm
  or `otherwise`), preserving `StateRelLM2_3` and `EnumLocalByteUninit`. -/
theorem enum_match_switchInt_simulation
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_3 body env allocBudget s m)
    (henv_valid : ∀ ty tb vs, env ty = some (tb, vs) →
      ValidEnumLayout ty body.layouts tb vs)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {discr : MirAst.Operand} {targets : SwitchTargets} {ty : Ty}
    (hterm : bb.terminator.kind = .switchInt discr targets)
    (hty : ty.kind = .bool ∨ (∃ k, ty.kind = .int k) ∨ (∃ k, ty.kind = .uint k))
    (hdiscr : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedEnumScalarOp body topFrame discr ty)
    (hcases : SwitchCasesFit ty targets) :
    let mRes := Miri.Interpreter.Step.step (annealStepHooksLM2_3 body.localDecls body.layouts) () m
    StepRelLM2_3 body env allocBudget m (stepMirFn body s) mRes ∧
    ((∀ msg, mRes.2 ≠ .error (.undefinedBehavior msg)) →
      (∀ localId b, EnumLocalByteUninit m localId b → EnumLocalByteUninit mRes.1 localId b) ∧
      (∀ j, IsImmediateStepLocal m j → IsImmediateStepLocal mRes.1 j)) := by
  intro mRes
  rcases hstate with ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
    halloc, hcal, hstack, hbor, hprot, hcaller, hd_tf⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by
    simp [hstmt_len]
  simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  have hstep_eq :=
    miri_step_LM2_3_eq_at_terminator hframes hframe.body_eq hframe.location_eq hbb hstmt_none
  have hstep_t :=
    miri_step_at_terminator_lm2_2 hframes hframe.body_eq hframe.location_eq hbb hstmt_none
  have hop_wt := hdiscr topFrame hframes
  have hlm_op_eq :
      annealEvalOperandLM2_3 body.localDecls body.layouts (translateOperand discr) none =
        annealEvalOperand body.localDecls body.layouts (translateOperand discr) none := by
    cases hop_wt <;> rfl
  have hm_term : translateTerminator bb.terminator =
      { sourceInfo := defaultSourceInfo,
        kind := .SwitchInt (translateOperand discr) (translateSwitchTargets targets) } := by
    unfold translateTerminator; rw [hterm]; rfl
  have hdisc_eq :
      (annealTerminatorHooksLM2_2 body.localDecls body.layouts).evalDiscriminant ()
        (translateOperand discr) m =
      Miri.Interpreter.runRvalue
        (annealEvalOperandLM2_3 body.localDecls body.layouts (translateOperand discr) none >>=
          annealReadImmediateLM2_2) m := by
    rw [hlm_op_eq]; rfl
  unfold evalTerminator
  rw [hterm]
  dsimp only
  rw [hbor, hcaller]
  dsimp only [mRes]
  rw [hstep_eq, hstep_t, hm_term]
  rcases evalEnumScalarOp_lm2_3 henv_valid hframes hframe hop_wt s.memory.globals none with
    ⟨sc, msc, topFrame', ha_op, hm_op, hrel, hsz, hbool, _, hframe', htf',
      _, himm_pres, hdisj_fn, hu_pres⟩ |
    ⟨m_err, msg, ha_err, hm_err⟩
  · rw [ha_op]
    have hdisc :
        (annealTerminatorHooksLM2_2 body.localDecls body.layouts).evalDiscriminant ()
          (translateOperand discr) m =
        ({ m with stack := ⟨#[topFrame']⟩ },
          .ok ⟨.scalar (.fromScalarInt msc), translateTy ty body.layouts⟩) := by
      rw [hdisc_eq]; unfold Miri.Interpreter.runRvalue; rw [hm_op]
    obtain ⟨hwsz, hwvalid⟩ := boolOrInt_translateTy_size hty body.layouts
    have hwidth : sc.sizeBytes = boolOrIntByteWidth ty :=
      translateSizeBytes_inj hrel.validBytes hwvalid (by rw [← hsz, hwsz])
    have hsz_ty : sc.sizeBytes = match ty.kind with
        | .bool => 1 | .int k => k.byteWidth 64 | .uint k => k.byteWidth 64
        | _ => sc.sizeBytes := by
      rw [hwidth]
      rcases ty with ⟨tk, tIdx⟩
      rcases hty with h | ⟨k, h⟩ | ⟨k, h⟩ <;> dsimp only at h <;> subst h <;> rfl
    have hbits : ty.kind = .bool → sc.bits = 0 ∨ sc.bits = 1 := fun h => (hbool h).2
    have hcmp : ∀ v b, (v, b) ∈ targets.branches →
        (annealTerminatorHooksLM2_2 body.localDecls body.layouts).compareSwitchCase ()
          ⟨.scalar (.fromScalarInt msc), translateTy ty body.layouts⟩ v
          { m with stack := ⟨#[topFrame']⟩ } =
        ({ m with stack := ⟨#[topFrame']⟩ }, .ok (Nat.beq sc.bits v)) := by
      intro v b hmem
      obtain ⟨hlt, hcase_bool⟩ := hcases v b hmem
      rw [← hwidth] at hlt
      exact compareSwitchCase_simulation hrel body.localDecls body.layouts ty hty hsz_ty hbits
        v hlt hcase_bool _
    rw [evalTerminator_switchInt_ok _ () _ _ _ m _ _ sc.bits hdisc hcmp]
    unfold Miri.Interpreter.ControlFlow.goToBlock Miri.Interpreter.ControlFlow.setLocation
    rw [stack_currentFrame?_singleton _ topFrame' rfl]
    dsimp only [Except.map]
    refine ⟨.emitStep _ _ _ ?_, fun _ => ⟨fun localId b hu => ?_, fun j hj => ?_⟩⟩
    · have hrc' : topFrame'.returnContinuation = .stop false := by rw [htf']; exact hretCont
      have hrp' : topFrame'.returnPlace =
          .frameLocal 0 0 none retLay topFrame'.localsIdentity := by rw [htf']; exact hretPlace
      exact StateRelLM2_3.mk
        { topFrame' with
          location := .mir ⟨lookupSwitchTarget sc.bits targets.branches targets.otherwise, 0⟩ }
        rfl hrc' ⟨retLay, hrp'⟩
        ⟨hframe'.body_eq, rfl, hframe'.af_locals_len, hframe'.mf_locals_size, hframe'.locals_rel⟩
        halloc hcal hstack hbor hprot hcaller (hdisj_fn hd_tf)
    · exact EnumLocalByteUninit.of_set_location (m := { m with stack := ⟨#[topFrame']⟩ })
        rfl (hu_pres localId b hu)
    · intro tf_s hf_s
      injection hf_s with ha; injection ha with ht; subst ht
      exact himm_pres j (hj topFrame hframes)
  · rw [ha_err]
    have hdisc :
        (annealTerminatorHooksLM2_2 body.localDecls body.layouts).evalDiscriminant ()
          (translateOperand discr) m = (m_err, .error (.undefinedBehavior msg)) := by
      rw [hdisc_eq]; unfold Miri.Interpreter.runRvalue; rw [hm_err]
    rw [evalTerminator_switchInt_error _ () _ _ _ m m_err _ hdisc]
    exact ⟨.ub _ _, fun hno => False.elim (hno msg rfl)⟩

/-- `Terminator.Goto` step simulation under `StateRelLM2_3`. -/
theorem step_goto_lm2_3_simulation
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_3 body env allocBudget s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {target : BasicBlockIdx}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : bb.terminator.kind = .goto target) :
    let mRes := Miri.Interpreter.Step.step (annealStepHooksLM2_3 body.localDecls body.layouts) () m
    StepRelLM2_3 body env allocBudget m (stepMirFn body s) mRes ∧
    (∀ localId b, EnumLocalByteUninit m localId b → EnumLocalByteUninit mRes.1 localId b) ∧
    (∀ j, IsImmediateStepLocal m j → IsImmediateStepLocal mRes.1 j) := by
  intro mRes
  rcases hstate with ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
    halloc, hcal, hstack, hbor, hprot, hcaller, hd_tf⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
  simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  dsimp only [mRes]
  rw [miri_step_LM2_3_eq_at_terminator hframes hframe.body_eq hframe.location_eq hbb hstmt_none,
    miri_step_at_terminator_lm2_2 hframes hframe.body_eq hframe.location_eq hbb hstmt_none]
  unfold evalTerminator translateTerminator
    Miri.Interpreter.ControlFlow.evalTerminator
    Miri.Interpreter.ControlFlow.goToBlock
    Miri.Interpreter.ControlFlow.setLocation
  rw [hterm, stack_currentFrame?_singleton m.stack topFrame hframes, hframes]
  dsimp only [translateTerminatorKind, Except.map, Id.run]
  refine ⟨.step _ _ ?_, (fun localId b hu => EnumLocalByteUninit.of_set_location hframes hu),
    (fun j hj => IsImmediateStepLocal.of_set_location hframes hj)⟩
  exact StateRelLM2_3.mk
    { topFrame with location := .mir ⟨target, 0⟩ }
    rfl hretCont ⟨retLay, hretPlace⟩
    ⟨hframe.body_eq, rfl, hframe.af_locals_len, hframe.mf_locals_size, hframe.locals_rel⟩
    halloc hcal hstack hbor hprot hcaller hd_tf

/-- Root-frame `Terminator.Return` step simulation for primitive scalar `_0`
under `StateRelLM2_3`. -/
theorem step_return_scalar_lm2_3_simulation
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_3 body env allocBudget s m)
    (henv_valid : ∀ ty tb vs, env ty = some (tb, vs) →
      ValidEnumLayout ty body.layouts tb vs)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {decl0 : LocalDecl}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hcleanup : bb.isCleanup = false)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : bb.terminator.kind = .return_)
    (hdecl0 : get? body.localDecls 0 = some decl0)
    (hprim0 : IsPrimScalarTy decl0.ty)
    (himm0 : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame 0) :
    StepRelLM2_3 body env allocBudget m (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_3 body.localDecls body.layouts) () m) := by
  rcases hstate with ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
    _, hcal, hstack, hbor, hprot, hcaller, _⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
  simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  rw [miri_step_LM2_3_eq_at_terminator hframes hframe.body_eq hframe.location_eq hbb hstmt_none,
    miri_step_at_terminator_lm2_2 hframes hframe.body_eq hframe.location_eq hbb hstmt_none]
  obtain ⟨slot0, mls0, hlt0, hslot0, hmls0_eq, hloc0_lm⟩ := hframe.lookup_local hdecl0
  have hmls0 : topFrame.locals[0]? = some mls0 := by
    rw [Array.getElem?_eq_getElem hlt0, hmls0_eq]
  have hget0 := frame_getLocal_of_getElem? topFrame 0 mls0 hmls0
  have himm0' := himm0 topFrame hframes mls0 hmls0
  have hloc0 := hloc0_lm.to_localRel_of_none (env_none_of_isPrimScalarTy henv_valid hprim0)
  have hctrl_eq :
      (annealTerminatorHooksLM2_2 body.localDecls body.layouts).toControlHooks = annealControlHooks := rfl
  unfold evalTerminator translateTerminator Miri.Interpreter.ControlFlow.evalTerminator
  rw [hterm, hstack, hctrl_eq, hslot0]
  dsimp only [translateTerminatorKind, Id.run, Pure.pure]
  cases hloc0 with
  | dead cachedLayout _ =>
    rw [returnFromCurrentFrame_of_error annealControlHooks hframes hframe.body_eq
      hframe.location_eq hbb hcleanup (annealControlHooks_returnOperand_dead hframes hget0)]
    exact .ub _ _
  | indirect _ mp _ _ _ _ =>
    exact False.elim (himm0' mp rfl)
  | immediate _ imm cachedLayout _ hval =>
    rcases hval with ⟨rfl, rfl⟩ | ⟨retVal, rfl, himmRel⟩
    · rw [returnFromCurrentFrame_of_error annealControlHooks hframes hframe.body_eq
        hframe.location_eq hbb hcleanup (annealControlHooks_returnOperand_uninit hframes hget0)]
      exact .ub _ _
    · obtain ⟨sc, msc, rfl, rfl, hrel, hsz_sc, hbool_sc, hchar_sc⟩ :=
        himmRel.of_primitive_scalar hprim0
      have hop0 := annealControlHooks_returnOperand_scalar hframes hget0
      rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
        hframe.location_eq hbb hcleanup hretCont hop0
        (annealControlHooks_popFrame_singleton hframes)
        (annealControlHooks_copyReturn_empty _ hretPlace)
        (annealControlHooks_cleanupFrame_eq false topFrame _)]
      exact .retRoot decl0 _ _ s.memory _ hdecl0 hop0
        (.scalar sc msc hrel hsz_sc hbool_sc hchar_sc) rfl

/-! ## 8. Storage Lifecycle, Whole-Enum Copy/Move, and Downcast Field Writes -/

/-- Extract `ValidEnumLayout` from any `LocalRelLM2_3` entry whose type is
registered in `env`. -/
private theorem LocalRelLM2_3.valid_of_some
    {env : EnumTypeEnv} {mach : AnnealMachine}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    (h : LocalRelLM2_3 env mach decl layouts slot mls)
    (henv : env decl.ty = some (tagBytes, variants)) :
    ValidEnumLayout decl.ty layouts tagBytes variants := by
  cases h with
  | base _ _ hnone _ => rw [henv] at hnone; cases hnone
  | enumDead _ _ _ henv' hv _ =>
    rw [henv] at henv'; injection henv' with hp; rcases hp with ⟨rfl, rfl⟩; exact hv
  | enumUninitImm _ _ _ henv' hv _ =>
    rw [henv] at henv'; injection henv' with hp; rcases hp with ⟨rfl, rfl⟩; exact hv
  | enumUninitInd _ _ _ _ henv' _ hmp =>
    rw [henv] at henv'; injection henv' with hp; rcases hp with ⟨rfl, rfl⟩
    cases hmp; assumption
  | enumInd _ _ _ _ _ _ henv' _ hmp =>
    rw [henv] at henv'; injection henv' with hp; rcases hp with ⟨rfl, rfl⟩
    cases hmp; assumption

/-- `StorageLive(loc)` step simulation under `StateRelLM2_3` for any declared
local (primitive scalar or multi-variant enum in `env`, whether `.dead`,
`.uninit` immediate, `.uninit` indirect, or initialized indirect): both machines
mark `loc` live and uninitialized, `lean-miri` deallocates any backing stack
allocation previously owned by `loc`, and `StateRelLM2_3`,
`IsImmediateStepLocal` on `loc` and all previously immediate locals, and
`EnumLocalByteUninit` on all `enumId ≠ loc` are preserved. -/
theorem step_storageLive_LM2_3_simulation
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_3 body env allocBudget s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageLive loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl) :
    let mRes :=
      Miri.Interpreter.Step.step
        (annealStepHooksLM2_3 body.localDecls body.layouts) () m
    StepRelLM2_3 body env allocBudget m (stepMirFn body s) mRes ∧
    IsImmediateStepLocal mRes.1 loc ∧
    (∀ enumId b, enumId ≠ loc →
      EnumLocalByteUninit m enumId b → EnumLocalByteUninit mRes.1 enumId b) ∧
    (∀ j, IsImmediateStepLocal m j → IsImmediateStepLocal mRes.1 j) := by
  intro mRes
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe, halloc,
      hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  obtain ⟨slot, mls, hlt_mf, hslot, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
  have hlt_af : loc < s.frame.locals.length := by
    unfold get? at hslot
    exact (List.getElem?_eq_some_iff.mp hslot).1
  have ha : evalStmt s ⟨.storageLive loc, span⟩ body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s (s.frame.locals.set loc .uninit)) := by
    unfold evalStmt; dsimp only
    rw [hslot, set?_eq_some_set hlt_af, hprot, hbor]
    dsimp only [disableLocalBorrows]
    apply congrArg (fun mem' => MirStepNode.step (advanceStmt s _ mem'))
    cases hm : s.memory; simp_all
  rw [ha]
  have hty : ∃ ty, topFrame.body.locals[loc]? = some ty := by
    rw [hframe.body_eq, translateBody_locals_getElem? body loc, hdecl]
    exact ⟨_, rfl⟩
  have hlive : LocalAllocLive m.machine.memory (topFrame.locals[loc]'hlt_mf).value := by
    rw [hmls_eq]; exact hloc.allocLive
  let m' : AnnealStepState :=
    { stack := ⟨#[{ topFrame with
          locals := topFrame.locals.set loc
            { topFrame.locals[loc]'hlt_mf with
              value := .live (.immediate .uninit) } hlt_mf }]⟩
      machine := { m.machine with
        memory := deallocLocalMemory m.machine.memory
          (topFrame.locals[loc]'hlt_mf).value } }
  have hm : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_3 body.localDecls body.layouts) ()
      (translateStmt ⟨.storageLive loc, span⟩) m = (m', .ok ()) := by
    simp only [Miri.Interpreter.Step.evalStatement, translateStmt,
      translateStmtKind, annealStepHooksLM2_3]
    exact annealStepHooksLM2_2_storageLive_any_eq hframes hlt_mf hty hlive
  dsimp only [mRes]
  rw [miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq
    hbb hstmt hm rfl hframe.location_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply StepRelLM2_3.step
    have hc_eq : ∀ l ∈ (topFrame.locals[loc]'hlt_mf).layout,
        l = translateTy decl.ty body.layouts := by
      rw [hmls_eq]; exact hloc.cachedLayout_eq
    have hnew : LocalRelLM2_3 env m'.machine decl body.layouts .uninit
        { topFrame.locals[loc]'hlt_mf with
          value := .live (.immediate .uninit) } := by
      cases henv : env decl.ty with
      | none =>
        refine .base _ _ henv (.immediate .uninit .uninit
          (topFrame.locals[loc]'hlt_mf).layout ?_ (Or.inl ⟨rfl, rfl⟩))
        rw [hmls_eq]; exact hloc.layout_eq
      | some pair =>
        rcases pair with ⟨tb, vs⟩
        exact .enumUninitImm tb vs (topFrame.locals[loc]'hlt_mf).layout
          henv (hloc.valid_of_some henv) hc_eq
    have hfr' := hframe.update_local_dealloc hdisj hdecl hnew
    exact StateRelLM2_3.mk _ rfl hretCont ⟨retLay, hretPlace⟩ hfr'.step_pc
      (halloc.of_dealloc _) hcal hstack hbor hprot hcaller (by
        apply MemoryAllocDisjoint.mono_immediate hdisj
        intro k
        by_cases hk : loc = k
        · subst hk
          right
          exact ⟨.uninit, (topFrame.locals[loc]'hlt_mf).layout, by
            simp only [Array.getElem?_set, ↓reduceIte]⟩
        · left
          simp only [hk, Array.getElem?_set, ↓reduceIte])
  · intro tf_s hf_s mls_s hget_s
    injection hf_s with ha_s; injection ha_s with ht_s; subst ht_s
    dsimp only at hget_s
    rw [Array.getElem?_set_self hlt_mf] at hget_s
    injection hget_s with hmls_s; subst hmls_s
    intro mp hcontr; cases hcontr
  · intro enumId b hne hu
    exact EnumLocalByteUninit.of_set_location (m := m') rfl
      (EnumLocalByteUninit.of_dealloc_other (Ne.symm hne) hframes hu)
  · intro j hj tf_s hf_s mls_s hget_s
    injection hf_s with ha_s; injection ha_s with ht_s; subst ht_s
    dsimp only at hget_s
    by_cases hlj : loc = j
    · subst hlj
      rw [Array.getElem?_set_self hlt_mf] at hget_s
      injection hget_s with hmls_s; subst hmls_s
      intro mp hcontr; cases hcontr
    · rw [Array.getElem?_set_ne _ hlj] at hget_s
      exact hj topFrame hframes mls_s hget_s

/-- `StorageDead(loc)` step simulation under `StateRelLM2_3` for any declared
non-return local `loc ≠ 0` (including an active indirect multi-variant enum
local): both machines mark `loc` `.dead`, `lean-miri` deallocates any stack
allocation owned by `loc`, and `StateRelLM2_3`, `EnumLocalByteUninit` on all
`enumId ≠ loc`, and `IsImmediateStepLocal` on all locals are preserved. -/
theorem step_storageDead_LM2_3_simulation
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_3 body env allocBudget s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageDead loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (hne : loc ≠ 0) :
    let mRes :=
      Miri.Interpreter.Step.step
        (annealStepHooksLM2_3 body.localDecls body.layouts) () m
    StepRelLM2_3 body env allocBudget m (stepMirFn body s) mRes ∧
    (∀ enumId b, enumId ≠ loc →
      EnumLocalByteUninit m enumId b → EnumLocalByteUninit mRes.1 enumId b) ∧
    (∀ j, IsImmediateStepLocal m j → IsImmediateStepLocal mRes.1 j) := by
  intro mRes
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe, halloc,
      hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  obtain ⟨slot, mls, hlt_mf, hslot, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
  have hlt_af : loc < s.frame.locals.length := by
    unfold get? at hslot
    exact (List.getElem?_eq_some_iff.mp hslot).1
  have ha : evalStmt s ⟨.storageDead loc, span⟩ body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s (s.frame.locals.set loc .dead)) := by
    unfold evalStmt; dsimp only
    rw [hslot, set?_eq_some_set hlt_af, hprot, hbor]
    dsimp only [disableLocalBorrows]
    apply congrArg (fun mem' => MirStepNode.step (advanceStmt s _ mem'))
    cases hm : s.memory; simp_all
  rw [ha]
  have hlive : LocalAllocLive m.machine.memory (topFrame.locals[loc]'hlt_mf).value := by
    rw [hmls_eq]; exact hloc.allocLive
  let m' : AnnealStepState :=
    { stack := ⟨#[{ topFrame with
          locals := topFrame.locals.set loc
            { topFrame.locals[loc]'hlt_mf with value := .dead } hlt_mf }]⟩
      machine := { m.machine with
        memory := deallocLocalMemory m.machine.memory
          (topFrame.locals[loc]'hlt_mf).value } }
  have hm : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_3 body.localDecls body.layouts) ()
      (translateStmt ⟨.storageDead loc, span⟩) m = (m', .ok ()) := by
    simp only [Miri.Interpreter.Step.evalStatement, translateStmt,
      translateStmtKind, annealStepHooksLM2_3]
    exact annealStepHooksLM2_2_storageDead_any_eq hframes hlt_mf hne hlive
  dsimp only [mRes]
  rw [miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq
    hbb hstmt hm rfl hframe.location_eq]
  refine ⟨?_, ?_, ?_⟩
  · apply StepRelLM2_3.step
    have hc_eq : ∀ l ∈ (topFrame.locals[loc]'hlt_mf).layout,
        l = translateTy decl.ty body.layouts := by
      rw [hmls_eq]; exact hloc.cachedLayout_eq
    have hnew : LocalRelLM2_3 env m'.machine decl body.layouts .dead
        { topFrame.locals[loc]'hlt_mf with value := .dead } := by
      cases henv : env decl.ty with
      | none =>
        refine .base _ _ henv (.dead (topFrame.locals[loc]'hlt_mf).layout ?_)
        rw [hmls_eq]; exact hloc.layout_eq
      | some pair =>
        rcases pair with ⟨tb, vs⟩
        exact .enumDead tb vs (topFrame.locals[loc]'hlt_mf).layout
          henv (hloc.valid_of_some henv) hc_eq
    have hfr' := hframe.update_local_dealloc hdisj hdecl hnew
    exact StateRelLM2_3.mk _ rfl hretCont ⟨retLay, hretPlace⟩ hfr'.step_pc
      (halloc.of_dealloc _) hcal hstack hbor hprot hcaller (by
        apply MemoryAllocDisjoint.mono_dead hdisj
        intro k
        by_cases hk : loc = k
        · subst hk
          right
          exact ⟨(topFrame.locals[loc]'hlt_mf).layout, by
            simp only [Array.getElem?_set, ↓reduceIte]⟩
        · left
          simp only [hk, Array.getElem?_set, ↓reduceIte])
  · intro enumId b hne_id hu
    exact EnumLocalByteUninit.of_set_location (m := m') rfl
      (EnumLocalByteUninit.of_dealloc_other (Ne.symm hne_id) hframes hu)
  · intro j hj tf_s hf_s mls_s hget_s
    injection hf_s with ha_s; injection ha_s with ht_s; subst ht_s
    dsimp only at hget_s
    by_cases hlj : loc = j
    · subst hlj
      rw [Array.getElem?_set_self hlt_mf] at hget_s
      injection hget_s with hmls_s; subst hmls_s
      intro mp hcontr; cases hcontr
    · rw [Array.getElem?_set_ne _ hlj] at hget_s
      exact hj topFrame hframes mls_s hget_s

private theorem find?_live_set!_ne
    (live : Array (Miri.Memory.AllocId × AnnealLocalAlloc))
    {u : Nat} {updId qId : Miri.Memory.AllocId}
    {oldLa newLa : AnnealLocalAlloc}
    (hu_lt : u < live.size)
    (hget_u : live[u]'hu_lt = (updId, oldLa))
    (hne : qId ≠ updId) :
    (live.set! u (updId, newLa)).find? (fun (k0, _) => k0 == qId) =
      live.find? (fun (k0, _) => k0 == qId) := by
  have hget_list : live.toList[u]? = some (updId, oldLa) := by
    rw [Array.getElem?_toList, Array.getElem?_eq_getElem hu_lt, hget_u]
  dsimp only [Array.set!]
  rw [← Array.find?_toList, ← Array.find?_toList, Array.toList_setIfInBounds]
  clear hu_lt hget_u
  generalize live.toList = ls at hget_list ⊢
  induction ls generalizing u with
  | nil => rfl
  | cons hd tl ih =>
    cases u with
    | zero =>
      dsimp only [List.getElem?_cons_zero] at hget_list
      injection hget_list with hhd; subst hhd
      have hbf : (updId == qId) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
      simp [List.set, List.find?, hbf]
    | succ u' =>
      dsimp only [List.getElem?_cons_succ, List.set] at hget_list ⊢
      cases hq : (hd.1 == qId)
      · simp [List.find?, hq, ih hget_list]
      · simp [List.find?, hq]

private theorem MemoryAllocDisjoint_deinitFrameLocal_lm2_3
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : MemoryAllocDisjoint mf) {idx : Nat} (hlt : idx < mf.locals.size) :
    MemoryAllocDisjoint (deinitFrameLocal mf idx hlt) := by
  intro i j mpi mpj ci cj hne hi hj
  dsimp [deinitFrameLocal] at hi hj
  rw [Array.getElem?_set] at hi hj
  split at hi
  · injection hi with h1; injection h1 with h2 _; cases h2
  · split at hj
    · injection hj with h1; injection h1 with h2 _; cases h2
    · exact h i j mpi mpj ci cj hne hi hj

private theorem evalRvalue_use_nil_borrows_lm2_3
    (locals : List LocalSlot) (op : MirAst.Operand) (mem : Memory)
    (hbor : mem.borrows = .nil) (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    evalRvalue locals (.use op) mem localDecls layouts =
      match evalOperand locals op .nil mem.globals layouts mem.callerLocals localDecls with
      | .ok val locals' =>
        match validateLoadedValue layouts localDecls op val with
        | false => .ub
        | true => .ok val locals' mem
      | .ub => .ub
      | .unsupported => .unsupported := by
  unfold evalRvalue; dsimp only; rw [hbor]
  generalize evalOperand locals op [] mem.globals layouts mem.callerLocals localDecls = r
  cases r with
  | ub => rfl
  | unsupported => rfl
  | ok v locals' =>
    dsimp only
    generalize validateLoadedValue layouts localDecls op v = vb
    cases vb with
    | false => rfl
    | true =>
      dsimp only
      cases op with
      | constant _ => rfl
      | move pl | copy pl =>
        rcases pl with ⟨_, projs⟩
        cases projs with
        | nil => rfl
        | cons p _ => cases p <;> rfl

private theorem evalRvalue_use_nil_borrows_ok_lm2_3
    {locals locals' : List LocalSlot} {op : MirAst.Operand} {mem : Memory}
    {localDecls : List LocalDecl} {layouts : LayoutTable} {val : Value}
    (hbor : mem.borrows = .nil)
    (hev : evalOperand locals op .nil mem.globals layouts mem.callerLocals localDecls =
      .ok val locals')
    (hval : validateLoadedValue layouts localDecls op val = true) :
    evalRvalue locals (.use op) mem localDecls layouts = .ok val locals' mem := by
  rw [evalRvalue_use_nil_borrows_lm2_3 _ _ _ hbor, hev]
  dsimp only
  rw [hval]

/-- Multi-variant enum destinations always take the memory-to-memory
`annealStructMemCopyOp` path (`usesStructMemCopyDest = true`). -/
theorem usesStructMemCopyDest_true_of_validEnum
    {layouts : LayoutTable} (dest : Miri.Interpreter.RuntimePlace AnnealProv)
    {ty : Ty} {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    (hdst : dest.layout = translateTy ty layouts)
    (hvalid : ValidEnumLayout ty layouts tagBytes variants) :
    usesStructMemCopyDest dest = true := by
  unfold usesStructMemCopyDest
  rw [hdst, hvalid.backend_memory, hvalid.outer_fields_tag0]
  dsimp only
  apply bne_iff_ne.mpr
  intro hz
  have hge := hvalid.size_ge_tag
  have htb := hvalid.tagBytes_valid
  rw [hz] at hge
  dsimp [Miri.ABI.Size.ZERO] at hge
  omega

/-- Whole-enum `Copy` / `Move` step simulation (`_dst = copy _src` and
`_dst = move _src`, `srcIdx ≠ dstIdx`) under `StateRelLM2_3`:
* `.dead` `_src` → lockstep `StepRelLM2_3.ub` (`"read of dead local"`).
* `.uninit` immediate `_src` → lockstep `StepRelLM2_3.ub`
  (`"read of uninitialized local"`).
* Initialized `.init (.aggregate v_act fieldVals)` `_src`:
  - `.dead` `_dst` → lockstep `StepRelLM2_3.ub` (`"write to dead local"`);
  - `.uninit` immediate `_dst` → allocates a fresh stack slot (`allocBudget + 1
    → allocBudget`) and copies raw bytes and `InitMask` via
    `annealStructMemCopyOp`;
  - indirect `_dst` (`enumUninitInd` or `enumInd`) → overwrites `_dst`'s
    disjoint stack allocation in place via `annealStructMemCopyOp`.
When no UB occurs, `isMove = true` leaves `_src` uninitialized immediate
(`IsImmediateStepLocal mRes.1 srcIdx`), every `EnumLocalByteUninit m srcIdx b`
transfers to `EnumLocalByteUninit mRes.1 dstIdx b`, and `EnumLocalByteUninit`
on other locals (`enumId ≠ dstIdx`, plus `enumId ≠ srcIdx` on `move`) is
preserved. -/
theorem step_enum_copy_move_simulation
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_3 body env (allocBudget + 1) s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    (henv_valid : ∀ t tb vs, env t = some (tb, vs) →
      ValidEnumLayout t body.layouts tb vs)
    {bb : BasicBlockData} {stmt : Statement}
    {dstIdx srcIdx : Local} {dstDecl srcDecl : LocalDecl}
    {isMove : Bool} {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hkind : stmt.kind = .assign ⟨dstIdx, .nil⟩
      (.use (if isMove then .move ⟨srcIdx, .nil⟩ else .copy ⟨srcIdx, .nil⟩)))
    (hne_sd : srcIdx ≠ dstIdx)
    (hsrc_decl : get? body.localDecls srcIdx = some srcDecl)
    (hdst_decl : get? body.localDecls dstIdx = some dstDecl)
    (henv_src : env srcDecl.ty = some (tagBytes, variants))
    (hdst_ty : dstDecl.ty = srcDecl.ty)
    (hsrc_uninit_imm :
      get? s.frame.locals srcIdx = some .uninit →
        IsImmediateStepLocal m srcIdx) :
    let mRes :=
      Miri.Interpreter.Step.step
        (annealStepHooksLM2_3 body.localDecls body.layouts) () m
    StepRelLM2_3 body env allocBudget m (stepMirFn body s) mRes ∧
    ((∀ msg, mRes.2 ≠ .error (.undefinedBehavior msg)) →
      (isMove = true → IsImmediateStepLocal mRes.1 srcIdx) ∧
      (∀ b, EnumLocalByteUninit m srcIdx b →
        EnumLocalByteUninit mRes.1 dstIdx b) ∧
      (∀ enumId b, enumId ≠ dstIdx → (isMove = true → enumId ≠ srcIdx) →
        EnumLocalByteUninit m enumId b →
        EnumLocalByteUninit mRes.1 enumId b) ∧
      (∀ j, j ≠ dstIdx → IsImmediateStepLocal m j →
        IsImmediateStepLocal mRes.1 j)) := by
  intro mRes
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe, halloc,
      hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hvalid := henv_valid srcDecl.ty tagBytes variants henv_src
  have henv_dst : env dstDecl.ty = some (tagBytes, variants) := by
    rw [hdst_ty]; exact henv_src
  let wholeLay := translateTy srcDecl.ty body.layouts
  have hlay_dst : translateTy dstDecl.ty body.layouts = wholeLay := by
    rw [hdst_ty]
  let op : MirAst.Operand :=
    if isMove then .move ⟨srcIdx, .nil⟩ else .copy ⟨srcIdx, .nil⟩
  have hlm23_op : lm23Operand (translateOperand op) = false := by
    cases isMove <;> rfl
  have hlm23_asgn :
      lm23Assign body.localDecls body.layouts ⟨dstIdx, #[]⟩
        (.Use (translateOperand op) .No) = false := by
    unfold lm23Assign; simp [hlm23_op]
  obtain ⟨slot_d0, mls_d0, hlt_d0, hslot_d0, hmls_d0_eq, hloc_d0⟩ :=
    hframe.lookup_local hdst_decl
  have hcache_d0 : ∀ l, (topFrame.locals[dstIdx]'hlt_d0).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d0_eq]; exact hloc_d0.layout_eq
  let tf₀ := cacheFrameLocalLayout topFrame dstIdx hlt_d0 wholeLay
  let m₀ : AnnealStepState := { m with stack := ⟨#[tf₀]⟩ }
  have heval_dst :
      annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ m =
      .ok ⟨.local 0 dstIdx none topFrame.localsIdentity, wholeLay⟩ m₀ := by
    have hp := annealEvalPlace_unprojected hframes hlt_d0 hdst_decl hcache_d0
    simpa only [hlay_dst] using hp
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 dstIdx none topFrame.localsIdentity, wholeLay⟩
  have huses_mem :
      usesStructMemCopyDest ⟨.local 0 dstIdx none topFrame.localsIdentity, wholeLay⟩ = true :=
    usesStructMemCopyDest_true_of_validEnum destPlace rfl hvalid
  have hm_eval :
      Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_3 body.localDecls body.layouts) ()
        (translateStmt stmt) m =
      Miri.Interpreter.runRvalue
        (annealEvalOperand body.localDecls body.layouts (translateOperand op)
            (some wholeLay) >>=
          fun src =>
            annealStructMemCopyOp body.localDecls body.layouts src destPlace)
        m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    rw [hkind]
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
      translateRvalue, annealStepHooksLM2_3]
    change (if lm23Assign body.localDecls body.layouts ⟨dstIdx, #[]⟩
        (.Use (translateOperand op) .No) then _ else _) = _
    rw [hlm23_asgn]
    simp only [Bool.false_eq_true, ↓reduceIte, annealStepHooksLM2_2]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooksLM2_2
    rw [EStateM.bind_eq_ok heval_dst]
    dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt, destPlace]
    simp only [huses_mem, ↓reduceIte]
    rfl
  have hfr₀ : FrameRelLM2_3 body env m.machine s.frame tf₀ := by
    simpa only [tf₀, wholeLay, ← hlay_dst] using
      hframe.cache_local_layout hdst_decl hlt_d0
  have hdisj₀ : MemoryAllocDisjoint tf₀ :=
    MemoryAllocDisjoint_cacheFrameLocalLayout hdisj hlt_d0 wholeLay
  obtain ⟨slot_s, mls_s, hlt_s0, hslot_s, hmls_s_eq, hloc_s⟩ :=
    hfr₀.lookup_local hsrc_decl
  have hcache_s : ∀ l, (tf₀.locals[srcIdx]'hlt_s0).layout = some l →
      l = translateTy srcDecl.ty body.layouts := by
    rw [hmls_s_eq]; exact hloc_s.layout_eq
  have hlt_src_af : srcIdx < s.frame.locals.length := by
    unfold get? at hslot_s
    exact (List.getElem?_eq_some_iff.mp hslot_s).1
  have hmls_s? : tf₀.locals[srcIdx]? = some mls_s := by
    rw [Array.getElem?_eq_getElem hlt_s0, hmls_s_eq]
  cases hloc_s with
  | base _ _ hnone _ =>
    rw [henv_src] at hnone; cases hnone
  | enumDead _ _ c_s _ _ _ =>
    have hc_s : ∀ l, c_s = some l → l = translateTy srcDecl.ty body.layouts :=
      fun l hl => hcache_s l (by rw [hmls_s_eq]; exact hl)
    have ha_ub : evalStmt s stmt body.localDecls body.layouts =
        MirStepNode.fail .ub := by
      unfold evalStmt; rw [hkind]
      cases isMove <;> simp [evalRvalue, evalOperand, hslot_s]
    obtain ⟨m_err, hm_op_err⟩ :
        ∃ m_err,
          annealEvalOperand body.localDecls body.layouts (translateOperand op)
            (some wholeLay) m₀ =
          .error (.undefinedBehavior "read of dead local") m_err := by
      cases isMove with
      | false =>
        exact ⟨_, annealEvalOperand_copy_dead (m := m₀) rfl hlt_s0 hsrc_decl
          hmls_s_eq hc_s⟩
      | true =>
        exact ⟨_, annealEvalOperand_move_dead (m := m₀) rfl hlt_s0 hsrc_decl
          hmls_s_eq hc_s⟩
    have hm_ub :
        Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_3 body.localDecls body.layouts) ()
          (translateStmt stmt) m =
        (m_err, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_eval]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_error hm_op_err]
    dsimp only [mRes]
    rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq
      hframe.location_eq hbb hstmt hm_ub]
    exact ⟨.ub _ _, fun hno => False.elim (hno _ rfl)⟩
  | enumUninitInd _ _ srcMp_u c_s _ _ _ =>
    have himm_s := hsrc_uninit_imm hslot_s topFrame hframes
    have hmls_top : topFrame.locals[srcIdx]? =
        some ⟨.live (.indirect srcMp_u), c_s⟩ := by
      have hg := hmls_s?
      dsimp only [tf₀, cacheFrameLocalLayout] at hg
      rw [Array.getElem?_set_ne _ (Ne.symm hne_sd)] at hg
      exact hg
    exact False.elim (himm_s _ hmls_top srcMp_u rfl)
  | enumUninitImm _ _ c_s _ _ _ =>
    have hc_s : ∀ l, c_s = some l → l = translateTy srcDecl.ty body.layouts :=
      fun l hl => hcache_s l (by rw [hmls_s_eq]; exact hl)
    have ha_ub : evalStmt s stmt body.localDecls body.layouts =
        MirStepNode.fail .ub := by
      unfold evalStmt; rw [hkind]
      cases isMove <;> simp [evalRvalue, evalOperand, hslot_s]
    obtain ⟨m_err, hm_op_ok⟩ :
        ∃ m_err,
          annealEvalOperand body.localDecls body.layouts (translateOperand op)
            (some wholeLay) m₀ =
          .ok ⟨.immediate .uninit, wholeLay⟩ m_err := by
      cases isMove with
      | false =>
        exact ⟨_, annealEvalOperand_copy_live (m := m₀) rfl hlt_s0 hsrc_decl
          hmls_s_eq hc_s⟩
      | true =>
        exact ⟨_, annealEvalOperand_move_live (m := m₀) rfl hlt_s0 hsrc_decl
          hmls_s_eq hc_s⟩
    have hm_ub :
        Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_3 body.localDecls body.layouts) ()
          (translateStmt stmt) m =
        (m_err, .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_eval]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hm_op_ok]
      rfl
    dsimp only [mRes]
    rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq
      hframe.location_eq hbb hstmt hm_ub]
    exact ⟨.ub _ _, fun hno => False.elim (hno _ rfl)⟩
  | enumInd tb_s vs_s v_act fieldVals srcMp c_s henv_s _ hemr_s =>
    have hc_s : ∀ l, c_s = some l → l = translateTy srcDecl.ty body.layouts :=
      fun l hl => hcache_s l (by rw [hmls_s_eq]; exact hl)
    rw [henv_src] at henv_s
    injection henv_s with hp_s; rcases hp_s with ⟨rfl, rfl⟩
    have hemr_copy := hemr_s
    rcases hemr_s with
      ⟨srcId, borTag_s, srcBase, srcLocal, _, _, _, _, hprov_s, _, _, hlive_s,
        hbase_s, hptr_s, _, _, _, hbs_s, _, _, _, _, _, _, _, _⟩
    let rootVal : Value := .aggregate v_act fieldVals
    have htf₀_dst : tf₀.locals[dstIdx]? = some ⟨mls_d0.value, some wholeLay⟩ := by
      dsimp only [tf₀, cacheFrameLocalLayout]
      rw [Array.getElem?_set_self hlt_d0, hmls_d0_eq]
    have hsrc_top? : topFrame.locals[srcIdx]? =
        some ⟨.live (.indirect srcMp), c_s⟩ := by
      have hg := hmls_s?
      dsimp only [tf₀, cacheFrameLocalLayout] at hg
      rw [Array.getElem?_set_ne _ (Ne.symm hne_sd)] at hg
      exact hg
    have hsrc_ne_destId :
        ∀ (destMp : Miri.Interpreter.MemPlace AnnealProv)
          (destId : Miri.Memory.AllocId),
          mls_d0.value = .live (.indirect destMp) →
          ∀ tag, destMp.ptr.provenance = some (.concrete destId tag) →
          srcId ≠ destId := by
      intro destMp destId hv_d tag_d hprov_d
      have hd_get : tf₀.locals[dstIdx]? =
          some ⟨.live (.indirect destMp), some wholeLay⟩ := by
        rw [htf₀_dst, hv_d]
      have hne_prov := hdisj₀ srcIdx dstIdx srcMp destMp c_s (some wholeLay)
        hne_sd hmls_s? hd_get
      rw [hprov_s, hprov_d] at hne_prov
      intro heq; subst heq; exact hne_prov rfl
    -- Evaluate `op` (`copy _src` or `move _src`) into `(locals₁, tf₁)`.
    obtain ⟨locals₁, tf₁, hev_op, hm_op, hfr₁, hdisj₁, hid₁, hrc₁, hrp₁, hsz₁,
        hdst_loc₁, hdst_tf₁?, hmove_src_imm, hother_tf₁, himm_tf₁⟩ :
        ∃ (locals₁ : List LocalSlot)
          (tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
          evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil =
            .ok rootVal locals₁ ∧
          annealEvalOperand body.localDecls body.layouts (translateOperand op)
            (some wholeLay) m₀ =
            .ok ⟨.indirect srcMp, wholeLay⟩ { m with stack := ⟨#[tf₁]⟩ } ∧
          FrameRelLM2_3 body env m.machine { s.frame with locals := locals₁ } tf₁ ∧
          MemoryAllocDisjoint tf₁ ∧
          tf₁.localsIdentity = topFrame.localsIdentity ∧
          tf₁.returnContinuation = topFrame.returnContinuation ∧
          tf₁.returnPlace = topFrame.returnPlace ∧
          tf₁.locals.size = topFrame.locals.size ∧
          get? locals₁ dstIdx = some slot_d0 ∧
          tf₁.locals[dstIdx]? = some ⟨mls_d0.value, some wholeLay⟩ ∧
          (isMove = true → IsImmediateFrameLocal tf₁ srcIdx) ∧
          (∀ k, k ≠ dstIdx → (isMove = true → k ≠ srcIdx) →
            (tf₁.locals[k]?).map Miri.Interpreter.LocalState.value =
              (topFrame.locals[k]?).map Miri.Interpreter.LocalState.value) ∧
          (∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal tf₁ j) := by
      cases isMove with
      | false =>
        let tf₁ := cacheFrameLocalLayout tf₀ srcIdx hlt_s0 wholeLay
        have hm_c := annealEvalOperand_copy_live (known := some wholeLay)
          (m := m₀) rfl hlt_s0 hsrc_decl hmls_s_eq hc_s
        refine ⟨s.frame.locals, tf₁,
          by change evalOperand s.frame.locals (.copy ⟨srcIdx, .nil⟩) .nil
               s.memory.globals body.layouts .nil = _
             simp [evalOperand, readProjectedValue, hslot_s, rootVal],
          hm_c, hfr₀.cache_local_layout hsrc_decl hlt_s0,
          MemoryAllocDisjoint_cacheFrameLocalLayout hdisj₀ hlt_s0 _,
          rfl, rfl, rfl,
          by dsimp [tf₁, tf₀]
             rw [cacheFrameLocalLayout_size, cacheFrameLocalLayout_size],
          hslot_d0,
          by dsimp only [tf₁, cacheFrameLocalLayout]
             rw [Array.getElem?_set_ne _ hne_sd]; exact htf₀_dst,
          (fun h => by cases h), ?_, ?_⟩
        · intro k hne_kd _
          dsimp only [tf₁, cacheFrameLocalLayout]
          by_cases hks : srcIdx = k
          · subst hks
            rw [Array.getElem?_set_self hlt_s0, hmls_s_eq, hsrc_top?]
            rfl
          · rw [Array.getElem?_set_ne _ hks]
            dsimp only [tf₀, cacheFrameLocalLayout]
            rw [Array.getElem?_set_ne _ (Ne.symm hne_kd)]
        · intro j hj
          exact (hj.cache_layout hlt_d0 wholeLay).cache_layout hlt_s0 wholeLay
      | true =>
        let tf_c := cacheFrameLocalLayout tf₀ srcIdx hlt_s0 wholeLay
        have hlt_c : srcIdx < tf_c.locals.size := by
          dsimp [tf_c]; rw [cacheFrameLocalLayout_size]; exact hlt_s0
        let tf₁ := deinitFrameLocal tf_c srcIdx hlt_c
        have hm_m := annealEvalOperand_move_live (known := some wholeLay)
          (m := m₀) rfl hlt_s0 hsrc_decl hmls_s_eq hc_s
        have hc_some : ∀ l ∈ (tf_c.locals[srcIdx]'hlt_c).layout,
            l = wholeLay := by
          intro l hl
          have hget_c : tf_c.locals[srcIdx]? = some (tf_c.locals[srcIdx]'hlt_c) :=
            Array.getElem?_eq_getElem hlt_c
          have hc_eq : tf_c.locals[srcIdx]? =
              some ⟨.live (.indirect srcMp), some wholeLay⟩ := by
            dsimp only [tf_c, cacheFrameLocalLayout]
            rw [Array.getElem?_set_self hlt_s0, hmls_s_eq]
          rw [hget_c] at hc_eq; injection hc_eq with heq_ls
          rw [heq_ls] at hl
          exact (Option.some.inj (Option.mem_def.mp hl)).symm
        have hfr₁_mv : FrameRelLM2_3 body env m.machine
            { s.frame with locals := s.frame.locals.set srcIdx .uninit } tf₁ :=
          (hfr₀.cache_local_layout hsrc_decl hlt_s0).update_local hsrc_decl
            (set?_eq_some_set hlt_src_af .uninit) hlt_c
            (.enumUninitImm tagBytes variants _ henv_src hvalid hc_some)
        refine ⟨s.frame.locals.set srcIdx .uninit, tf₁,
          by change evalOperand s.frame.locals (.move ⟨srcIdx, .nil⟩) .nil
               s.memory.globals body.layouts .nil = _
             unfold evalOperand; dsimp only; rw [hslot_s]; dsimp only
             rw [set?_eq_some_set hlt_src_af .uninit],
          hm_m, hfr₁_mv,
          MemoryAllocDisjoint_deinitFrameLocal_lm2_3
            (MemoryAllocDisjoint_cacheFrameLocalLayout hdisj₀ hlt_s0 _) hlt_c,
          rfl, rfl, rfl,
          by dsimp [tf₁, deinitFrameLocal, tf_c, tf₀]
             rw [Array.size_set, cacheFrameLocalLayout_size,
               cacheFrameLocalLayout_size],
          by unfold get?; rw [List.getElem?_set_ne hne_sd]; exact hslot_d0,
          by dsimp only [tf₁, deinitFrameLocal]
             rw [Array.getElem?_set_ne _ hne_sd]
             dsimp only [tf_c, cacheFrameLocalLayout]
             rw [Array.getElem?_set_ne _ hne_sd]; exact htf₀_dst,
          ?_, ?_, ?_⟩
        · intro _ mls_x hget_x mp_x hcontr
          dsimp only [tf₁, deinitFrameLocal] at hget_x
          rw [Array.getElem?_set_self hlt_c] at hget_x
          injection hget_x with hx; subst hx; cases hcontr
        · intro k hne_kd hne_ks_fn
          have hne_ks := hne_ks_fn rfl
          dsimp only [tf₁, deinitFrameLocal]
          rw [Array.getElem?_set_ne _ (Ne.symm hne_ks)]
          dsimp only [tf_c, cacheFrameLocalLayout]
          rw [Array.getElem?_set_ne _ (Ne.symm hne_ks)]
          dsimp only [tf₀, cacheFrameLocalLayout]
          rw [Array.getElem?_set_ne _ (Ne.symm hne_kd)]
        · intro j hj mls_j hget_j
          by_cases hjs : srcIdx = j
          · subst hjs
            dsimp only [tf₁, deinitFrameLocal] at hget_j
            rw [Array.getElem?_set_self hlt_c] at hget_j
            injection hget_j with hj_eq; subst hj_eq
            intro _ hcontr; cases hcontr
          · dsimp only [tf₁, deinitFrameLocal] at hget_j
            rw [Array.getElem?_set_ne _ hjs] at hget_j
            exact ((hj.cache_layout hlt_d0 wholeLay).cache_layout hlt_s0
              wholeLay) mls_j hget_j
    have hlt_dst1 : dstIdx < tf₁.locals.size := by rw [hsz₁]; exact hlt_d0
    have hdst_tf₁ : tf₁.locals[dstIdx]'hlt_dst1 = ⟨mls_d0.value, some wholeLay⟩ := by
      rw [Array.getElem?_eq_getElem hlt_dst1] at hdst_tf₁?
      exact Option.some.inj hdst_tf₁?
    have hlt_af₁ : dstIdx < locals₁.length := by
      unfold get? at hdst_loc₁
      exact (List.getElem?_eq_some_iff.mp hdst_loc₁).1
    have hfr₁_excl : FrameRelLM2_3Except body env dstIdx m.machine
        { s.frame with locals := locals₁ } tf₁ :=
      FrameRelLM2_3Except.of_frameRel hfr₁
    have hkind_op : stmt.kind = .assign ⟨dstIdx, .nil⟩ (.use op) := hkind
    have hev_op_ld :
        evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil
          body.localDecls = .ok rootVal locals₁ := by
      have : evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil
          body.localDecls =
        evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil .nil := by
        cases isMove <;> rfl
      rw [this]; exact hev_op
    have hval_root :
        validateLoadedValue body.layouts body.localDecls op rootVal = true := by
      apply hvalid.validateLoadedValue_unproj hsrc_decl
      cases isMove
      · exact Or.inl rfl
      · exact Or.inr rfl
    have ha_ok_of : slot_d0 ≠ .dead →
        evalStmt s stmt body.localDecls body.layouts =
        MirStepNode.step (advanceStmt s (locals₁.set dstIdx (.init rootVal))
          s.memory) := by
      intro hnot_dead
      unfold evalStmt; rw [hkind_op]; dsimp only
      rw [evalRvalue_use_nil_borrows_ok_lm2_3 hbor (by rw [hcaller]; exact hev_op_ld) hval_root]
      simp only [hprot, hbor, invalidateConflictingBorrows, hdst_loc₁]
      cases slot_d0 with
      | dead => exact absurd rfl hnot_dead
      | uninit | init _ =>
        rw [set?_eq_some_set hlt_af₁ (.init rootVal)]
        apply congrArg (fun mem =>
          MirStepNode.step (advanceStmt s (locals₁.set dstIdx (.init rootVal)) mem))
        rcases hm : s.memory with ⟨_, _, bor, _, _, _, _, prot, _, _⟩
        rw [hm] at hbor hprot
        dsimp only at hbor hprot
        subst hbor hprot
        rfl
    have hdst_cases :
        (slot_d0 = .dead ∧ mls_d0.value = .dead) ∨
        (slot_d0 = .uninit ∧ mls_d0.value = .live (.immediate .uninit)) ∨
        (slot_d0 ≠ .dead ∧
          ∃ (tag_d : Miri.Memory.BorTag)
            (destMp : Miri.Interpreter.MemPlace AnnealProv)
            (destId : Miri.Memory.AllocId) (destBase : UInt64)
            (destLocal : AnnealLocalAlloc) (u : Nat)
            (hu_lt : u < m.machine.memory.live.size),
            mls_d0.value = .live (.indirect destMp) ∧
            destMp.ptr.provenance = some (.concrete destId tag_d) ∧
            destMp.misaligned = none ∧
            destMp.metadata = .none ∧
            LiveAllocEntry m.machine.memory.live destId destLocal ∧
            m.machine.memory.live.findIdx? (fun (k, _) => k == destId) = some u ∧
            m.machine.memory.live[u]'hu_lt = (destId, destLocal) ∧
            m.machine.lookupBaseAddr destId = some destBase ∧
            destMp.ptr.offset = Miri.ABI.Size.ofBytes destBase ∧
            destBase.toNat + wholeLay.layout.size.bytes.toNat < 2 ^ 64 ∧
            destLocal.allocation.mutability = .Mut ∧
            destLocal.allocation.byteSize = wholeLay.layout.size ∧
            destMp.ptr.offset.isAligned wholeLay.layout.align.abi = .ok true) := by
      cases hloc_d0 with
      | base _ _ hnone _ => rw [henv_dst] at hnone; cases hnone
      | enumDead _ _ _ _ _ _ => exact Or.inl ⟨rfl, rfl⟩
      | enumUninitImm _ _ _ _ _ _ => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      | enumUninitInd _ _ destMp _ _ _ humpr =>
        rcases humpr with ⟨destId, tag_d, destBase, destLocal, _, hprov_d,
          hmis_d, hmeta_d, hlive_d, hbase_d, hptr_d, hovf_d, hmut_d, halign_d,
          hbs_d, _, _, _⟩
        obtain ⟨hfind_d, u, hu_lt, hfidx_d, hget_d⟩ := hlive_d
        exact Or.inr (Or.inr ⟨by nofun, tag_d, destMp, destId, destBase,
          destLocal, u, hu_lt, rfl, hprov_d, hmis_d, hmeta_d,
          ⟨hfind_d, u, hu_lt, hfidx_d, hget_d⟩, hfidx_d, hget_d, hbase_d,
          hptr_d, by simpa only [hlay_dst] using hovf_d, hmut_d,
          by simpa only [hlay_dst] using hbs_d,
          by simpa only [hlay_dst] using halign_d⟩)
      | enumInd _ _ _ _ destMp _ _ _ hemr_d =>
        rcases hemr_d with ⟨destId, tag_d, destBase, destLocal, _, _, _, _,
          hprov_d, hmis_d, hmeta_d, hlive_d, hbase_d, hptr_d, hovf_d, hmut_d,
          halign_d, hbs_d, _, _, _, _, _, _, _, _⟩
        obtain ⟨hfind_d, u, hu_lt, hfidx_d, hget_d⟩ := hlive_d
        exact Or.inr (Or.inr ⟨by nofun, tag_d, destMp, destId, destBase,
          destLocal, u, hu_lt, rfl, hprov_d, hmis_d, hmeta_d,
          ⟨hfind_d, u, hu_lt, hfidx_d, hget_d⟩, hfidx_d, hget_d, hbase_d,
          hptr_d, by simpa only [hlay_dst] using hovf_d, hmut_d,
          by simpa only [hlay_dst] using hbs_d,
          by simpa only [hlay_dst] using halign_d⟩)
    rcases hdst_cases with
      ⟨hslot_dead, hv_dead⟩ | ⟨hslot_uninit, hv_uninit⟩ |
      ⟨hnot_dead, tag_d, destMp, destId, destBase, destLocal, u, hu_lt,
        hv_ind, hprov_d, hmis_d, hmeta_d, hlive_d, hfidx_d, hget_d,
        hbase_d, hptr_d, hovf_d, hmut_d, hbs_d, halign_d⟩
    · -- Dead destination: lockstep UB.
      have ha_ub : evalStmt s stmt body.localDecls body.layouts =
          MirStepNode.fail .ub := by
        unfold evalStmt; rw [hkind_op]; dsimp only
        rw [evalRvalue_use_nil_borrows_ok_lm2_3 hbor (by rw [hcaller]; exact hev_op_ld) hval_root]
        simp only [hdst_loc₁, hslot_dead]
      rw [hv_dead] at hdst_tf₁
      have hcp_dead := annealStructMemCopyOp_dead_ub
        (ld := body.localDecls) (ly := body.layouts)
        (srcMp := srcMp) (srcLay := wholeLay) (wholeLay := wholeLay)
        (iden := topFrame.localsIdentity)
        (m := { m with stack := ⟨#[tf₁]⟩ }) rfl hlt_dst1 hdst_tf₁
      have hm_ub :
          Miri.Interpreter.Step.evalStatement
            (annealStepHooksLM2_3 body.localDecls body.layouts) ()
            (translateStmt stmt) m =
          ({ m with stack := ⟨#[tf₁]⟩ },
            .error (.undefinedBehavior "write to dead local")) := by
        rw [hm_eval]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hm_op]; simp only [destPlace, hcp_dead]
      dsimp only [mRes]
      rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq
        hframe.location_eq hbb hstmt hm_ub]
      exact ⟨.ub _ _, fun hno => False.elim (hno _ rfl)⟩
    · -- Uninitialized immediate destination: fresh stack allocation + copy.
      rw [hv_uninit] at hdst_tf₁
      have hsized_w : wholeLay.layout.isSized = true := hvalid.isSized_true
      obtain ⟨rawAlloc, htry, hbs0, _, hmut0, _, _⟩ :=
        tryNew_uninit_of_pow2_le_29 wholeLay.layout.size
          wholeLay.layout.align.abi hvalid.align_pow2_le
      obtain ⟨mem', newId, hres, _, hlive_eq, hfresh_old, hwm_next, hovf_all⟩ :=
        (halloc.of_succ).reserve_step
      have hfresh : mem'.live.any (fun entry => entry.1 == newId) = false := by
        rw [hlive_eq]; exact hfresh_old
      have hcp_ok := annealStructMemCopyOp_uninitImm_ok
        (ld := body.localDecls) (ly := body.layouts)
        (srcLay := wholeLay) (iden := topFrame.localsIdentity)
        (m := { m with stack := ⟨#[tf₁]⟩ })
        rfl hlt_dst1 hdst_tf₁ hsized_w htry hbs0 hmut0 hres hfresh
        hprov_s hbase_s hptr_s hlive_s hbs_s
      have hemr_new : EnumMemRel
          (stackAllocMachine m.machine mem' newId
            (copyWholeStructAllocation srcLocal.allocation none))
          dstDecl.ty body.layouts tagBytes variants v_act fieldVals
          (stackAllocPlace newId) := by
        rw [hdst_ty]
        exact hemr_copy.of_copy_fresh hprov_s hlive_s hfresh
          (hovf_all _ hvalid.size_lt_4gib)
      let tf_end :=
        { tf₁ with
          locals := tf₁.locals.set dstIdx
            ⟨.live (.indirect (stackAllocPlace newId)), some wholeLay⟩ hlt_dst1 }
      let m_end : AnnealStepState :=
        ⟨⟨#[tf_end]⟩,
          stackAllocMachine m.machine mem' newId
            (copyWholeStructAllocation srcLocal.allocation none)⟩
      have hm_ok :
          Miri.Interpreter.Step.evalStatement
            (annealStepHooksLM2_3 body.localDecls body.layouts) ()
            (translateStmt stmt) m = (m_end, .ok ()) := by
        rw [hm_eval]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hm_op, hcp_ok]
      have hfr_end : FrameRelLM2_3 body env m_end.machine
          { s.frame with locals := locals₁.set dstIdx (.init rootVal) } tf_end := by
        have hex := hfr₁_excl.of_stackAlloc_set_excl
          (alloc := copyWholeStructAllocation srcLocal.allocation none)
          (hlt := hlt_dst1) hres
          ⟨.live (.indirect (stackAllocPlace newId)), some wholeLay⟩
        exact hex.finish_dst hdst_decl (set?_eq_some_set hlt_af₁ (.init rootVal))
          (Array.getElem?_set_self hlt_dst1)
          (.enumInd tagBytes variants v_act fieldVals (stackAllocPlace newId)
            (some wholeLay) henv_dst
            (fun _ hl => by
              rw [hlay_dst]
              exact (Option.some.inj (Option.mem_def.mp hl)).symm)
            hemr_new)
      dsimp only [mRes]
      rw [ha_ok_of (by rw [hslot_uninit]; nofun),
        miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq
          hbb hstmt hm_ok rfl hfr_end.location_eq]
      refine ⟨.step _ _ ?_, fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
      · exact .mk _ rfl (hrc₁.trans hretCont)
          ⟨retLay, by dsimp; rw [hrp₁, hretPlace, hid₁]⟩
          hfr_end.step_pc (Or.inr (hwm_next _))
          hcal hstack hbor hprot hcaller
          (MemoryAllocDisjoint_set_fresh_stackAlloc_lm2_3 hfr₁_excl hdisj₁
            hfresh_old hlt_dst1)
      · intro hmv tf_s hf_s mls_s hget_s
        injection hf_s with ha_s; injection ha_s with ht_s; subst ht_s
        dsimp only [tf_end] at hget_s
        rw [Array.getElem?_set_ne _ (Ne.symm hne_sd)] at hget_s
        exact hmove_src_imm hmv mls_s hget_s
      · intro b hu_src tf_s mp_d c_d id_d bt_d la_d hf_s hloc_d hprov_d' hfind_d
        injection hf_s with ha_s; injection ha_s with ht_s; subst ht_s
        dsimp only [tf_end] at hloc_d
        rw [Array.getElem?_set_self hlt_dst1] at hloc_d
        injection hloc_d with hls_eq
        injection hls_eq with hv_eq _
        injection hv_eq with hop_eq
        injection hop_eq with hmp_eq
        subst hmp_eq
        change some (Miri.Memory.Provenance.concrete newId Miri.Memory.BorTag.one) =
          some (Miri.Memory.Provenance.concrete id_d bt_d) at hprov_d'
        injection hprov_d' with hp_eq; injection hp_eq with hid_eq _; subst hid_eq
        have hself := (LiveAllocEntry.of_push_fresh_self
          (la := ⟨.stack, copyWholeStructAllocation srcLocal.allocation none⟩)
          hfresh).1
        dsimp only [m_end, stackAllocMachine] at hfind_d
        rw [hself] at hfind_d
        injection hfind_d with hpair_eq
        have hla_eq : la_d =
            ⟨.stack, copyWholeStructAllocation srcLocal.allocation none⟩ :=
          (Prod.mk.inj hpair_eq).2.symm
        subst hla_eq
        obtain ⟨_, _, _, _, hmask_eq, _⟩ :=
          copyWholeStructAllocation_props srcLocal.allocation none
        dsimp only
        rw [hmask_eq]
        exact hu_src topFrame srcMp c_s srcId borTag_s srcLocal
          hframes hsrc_top? hprov_s hlive_s.1
      · intro enumId b hne_ed hne_es hu_e tf_s mp_e c_e id_e bt_e la_e
            hf_s hloc_e hprov_e hfind_e
        injection hf_s with ha_s; injection ha_s with ht_s; subst ht_s
        dsimp only [tf_end] at hloc_e
        rw [Array.getElem?_set_ne _ (Ne.symm hne_ed)] at hloc_e
        have hval_map := hother_tf₁ enumId hne_ed hne_es
        rw [hloc_e] at hval_map
        dsimp only [Option.map] at hval_map
        cases htop_e : topFrame.locals[enumId]? with
        | none => rw [htop_e] at hval_map; cases hval_map
        | some mls_top =>
          rw [htop_e] at hval_map
          dsimp only [Option.map] at hval_map
          injection hval_map with hv_top
          have htop_e' : topFrame.locals[enumId]? =
              some ⟨.live (.indirect mp_e), mls_top.layout⟩ := by
            cases mls_top; dsimp at hv_top ⊢; rw [hv_top]; exact htop_e
          have hid_ne : id_e ≠ newId := by
            intro rfl
            obtain ⟨hlt_k, _⟩ := Array.getElem?_eq_some_iff.mp htop_e'
            have hlt_dk : enumId < length body.localDecls :=
              hframe.mf_locals_size ▸ hlt_k
            have hlt_afk : enumId < length s.frame.locals :=
              hframe.af_locals_len.symm ▸ hlt_dk
            unfold length at hlt_dk hlt_afk
            have hloc_k := hframe.locals_rel enumId _ _ _
              (by unfold get?; exact List.getElem?_eq_getElem hlt_dk)
              (by unfold get?; exact List.getElem?_eq_getElem hlt_afk)
              htop_e'
            obtain ⟨id_k, hid_k, hany_k⟩ := hloc_k.allocLive mp_e rfl
            rw [hprov_e] at hid_k
            injection hid_k with hid_eq; subst hid_eq
            rw [hfresh_old] at hany_k; cases hany_k
          let newEntry : AnnealLocalAlloc :=
            { kind := .stack
              allocation := copyWholeStructAllocation srcLocal.allocation none }
          have hfind_old :
              m.machine.memory.live.find? (fun (k0, _) => k0 == id_e) =
                some (id_e, la_e) := by
            dsimp only [m_end, stackAllocMachine] at hfind_e
            rw [hlive_eq, Array.find?_push] at hfind_e
            have hbeq_f : ((newId, newEntry).1 == id_e) = false :=
              beq_eq_false_iff_ne.mpr (Ne.symm hid_ne)
            dsimp at hbeq_f
            simp [hbeq_f] at hfind_e
            exact hfind_e
          exact hu_e topFrame mp_e mls_top.layout id_e bt_e la_e
            hframes htop_e' hprov_e hfind_old
      · intro j hne_jd hj tf_s hf_s mls_j hget_j
        injection hf_s with ha_s; injection ha_s with ht_s; subst ht_s
        dsimp only [tf_end] at hget_j
        rw [Array.getElem?_set_ne _ (Ne.symm hne_jd)] at hget_j
        exact himm_tf₁ j (hj topFrame hframes) mls_j hget_j
    · -- Indirect destination: overwrite disjoint stack allocation in place.
      rw [hv_ind] at hdst_tf₁
      have hne_id := hsrc_ne_destId destMp destId hv_ind tag_d hprov_d
      have hcp_ok := annealStructMemCopyOp_indirect_ok
        (ld := body.localDecls) (ly := body.layouts)
        (srcLay := wholeLay) (iden := topFrame.localsIdentity)
        (m := { m with stack := ⟨#[tf₁]⟩ })
        rfl hlt_dst1 hdst_tf₁ hne_id
        hprov_s hbase_s hptr_s hlive_s hbs_s
        hprov_d hbase_d hptr_d hu_lt hfidx_d hget_d hbs_d hmut_d
      have hemr_new : EnumMemRel
          (updateAllocMachine m.machine u destId destLocal.kind
            (copyWholeStructAllocation srcLocal.allocation
              destLocal.allocation.extra))
          dstDecl.ty body.layouts tagBytes variants v_act fieldVals destMp := by
        rw [hdst_ty]
        exact hemr_copy.of_copy_overwrite hprov_s hlive_s
          hprov_d hmis_d hmeta_d hlive_d hu_lt hfidx_d hbase_d hptr_d
          hovf_d halign_d
      let alloc_upd :=
        copyWholeStructAllocation srcLocal.allocation destLocal.allocation.extra
      let m_end : AnnealStepState :=
        ⟨⟨#[tf₁]⟩,
          updateAllocMachine m.machine u destId destLocal.kind alloc_upd⟩
      have hm_ok :
          Miri.Interpreter.Step.evalStatement
            (annealStepHooksLM2_3 body.localDecls body.layouts) ()
            (translateStmt stmt) m = (m_end, .ok ()) := by
        rw [hm_eval]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hm_op, hcp_ok]
      have hfr_end : FrameRelLM2_3 body env m_end.machine
          { s.frame with locals := locals₁.set dstIdx (.init rootVal) } tf₁ := by
        have hex := hfr₁_excl.of_updateAlloc_excl (kind := destLocal.kind)
          (alloc' := alloc_upd) hdisj₁ hdst_tf₁ hprov_d hu_lt hget_d
        exact hex.finish_dst hdst_decl (set?_eq_some_set hlt_af₁ (.init rootVal))
          (by rw [Array.getElem?_eq_getElem hlt_dst1, hdst_tf₁])
          (.enumInd tagBytes variants v_act fieldVals destMp (some wholeLay)
            henv_dst
            (fun _ hl => by
              rw [hlay_dst]
              exact (Option.some.inj (Option.mem_def.mp hl)).symm)
            hemr_new)
      dsimp only [mRes]
      rw [ha_ok_of hnot_dead,
        miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq
          hbb hstmt hm_ok rfl hfr_end.location_eq]
      refine ⟨.step _ _ ?_, fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
      · exact .mk _ rfl (hrc₁.trans hretCont)
          ⟨retLay, by dsimp; rw [hrp₁, hretPlace, hid₁]⟩
          hfr_end.step_pc
          ((halloc.mono (Nat.le_succ allocBudget)).of_updateAlloc hu_lt hget_d)
          hcal hstack hbor hprot hcaller hdisj₁
      · intro hmv tf_s hf_s mls_s hget_s
        injection hf_s with ha_s; injection ha_s with ht_s; subst ht_s
        exact hmove_src_imm hmv mls_s hget_s
      · intro b hu_src tf_s mp_d c_d id_d bt_d la_d hf_s hloc_d hprov_d' hfind_d
        injection hf_s with ha_s; injection ha_s with ht_s; subst ht_s
        dsimp only at hloc_d
        rw [hdst_tf₁?] at hloc_d
        injection hloc_d with hls_eq
        rw [hv_ind] at hls_eq
        injection hls_eq with hv_eq _
        injection hv_eq with hop_eq
        injection hop_eq with hmp_eq
        subst hmp_eq
        rw [hprov_d] at hprov_d'
        injection hprov_d' with hp_eq; injection hp_eq with hid_eq _; subst hid_eq
        have hself := (hlive_d.of_set!_self hu_lt hfidx_d
          ⟨destLocal.kind, alloc_upd⟩).1
        dsimp only [m_end, updateAllocMachine] at hfind_d
        rw [hself] at hfind_d
        injection hfind_d with hpair_eq
        have hla_eq : la_d = ⟨destLocal.kind, alloc_upd⟩ :=
          (Prod.mk.inj hpair_eq).2.symm
        subst hla_eq
        obtain ⟨_, _, _, _, hmask_eq, _⟩ :=
          copyWholeStructAllocation_props srcLocal.allocation
            destLocal.allocation.extra
        dsimp only [alloc_upd]
        rw [hmask_eq]
        exact hu_src topFrame srcMp c_s srcId borTag_s srcLocal
          hframes hsrc_top? hprov_s hlive_s.1
      · intro enumId b hne_ed hne_es hu_e tf_s mp_e c_e id_e bt_e la_e
            hf_s hloc_e hprov_e hfind_e
        injection hf_s with ha_s; injection ha_s with ht_s; subst ht_s
        dsimp only at hloc_e
        have hval_map := hother_tf₁ enumId hne_ed hne_es
        rw [hloc_e] at hval_map
        dsimp only [Option.map] at hval_map
        cases htop_e : topFrame.locals[enumId]? with
        | none => rw [htop_e] at hval_map; cases hval_map
        | some mls_top =>
          rw [htop_e] at hval_map
          dsimp only [Option.map] at hval_map
          injection hval_map with hv_top
          have htop_e' : topFrame.locals[enumId]? =
              some ⟨.live (.indirect mp_e), mls_top.layout⟩ := by
            cases mls_top; dsimp at hv_top ⊢; rw [hv_top]; exact htop_e
          have hid_ne : id_e ≠ destId := by
            have hd_top : topFrame.locals[dstIdx]? =
                some ⟨.live (.indirect destMp), mls_d0.layout⟩ := by
              rw [Array.getElem?_eq_getElem hlt_d0, hmls_d0_eq]
              cases mls_d0; dsimp at hv_ind ⊢; rw [hv_ind]
            have hne_p := hdisj enumId dstIdx mp_e destMp mls_top.layout
              mls_d0.layout hne_ed htop_e' hd_top
            rw [hprov_e, hprov_d] at hne_p
            intro rfl; exact hne_p rfl
          have hfind_old :
              m.machine.memory.live.find? (fun (k0, _) => k0 == id_e) =
                some (id_e, la_e) := by
            dsimp only [m_end, updateAllocMachine] at hfind_e
            rw [find?_live_set!_ne _ hu_lt hget_d hid_ne] at hfind_e
            exact hfind_e
          exact hu_e topFrame mp_e mls_top.layout id_e bt_e la_e
            hframes htop_e' hprov_e hfind_old
      · intro j hne_jd hj tf_s hf_s mls_j hget_j
        injection hf_s with ha_s; injection ha_s with ht_s; subst ht_s
        exact himm_tf₁ j (hj topFrame hframes) mls_j hget_j

/-! ### 8C. Downcast-Field Write Simulation & Inactive-Variant Divergence -/

private theorem size_zero_add_eq_of_lt {sz : Miri.ABI.Size}
    (hlt : sz.bytes.toNat < 2 ^ 64) :
    Miri.ABI.Size.ZERO.add sz = .ok sz := by
  have h := (size_add_of_no_overflow (a := Miri.ABI.Size.ZERO) (b := sz)
    (by dsimp [Miri.ABI.Size.ZERO]; omega)).1
  rw [h]
  dsimp [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes]
  rw [UInt64.zero_add]

private theorem size_add_eq_of_lt {a b : Miri.ABI.Size}
    (hlt : a.bytes.toNat + b.bytes.toNat < 2 ^ 64) :
    a.add b = .ok (Miri.ABI.Size.ofBytes (a.bytes + b.bytes)) :=
  (size_add_of_no_overflow hlt).1

/-- `annealEvalPlaceLM2_3` on `((_dst as v).i : fty)` caches `dstIdx`'s enum
layout in the top frame (`tf₀`) and projects to `.local 0 dstIdx (some f.offset)
topFrame.localsIdentity` with layout `translateTy fty body.layouts`. -/
theorem annealEvalPlaceLM2_3_downcast_field_ok
    {body : CapturedMir}
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Local} {dstDecl : LocalDecl}
    {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    {vName : Option String} {v i : Nat} {fty : Ty}
    (hframes : m.stack.frames = #[topFrame])
    (hlt : dstIdx < topFrame.locals.size)
    (hdst_decl : get? body.localDecls dstIdx = some dstDecl)
    (hcache : ∀ l, (topFrame.locals[dstIdx]'hlt).layout = some l →
      l = translateTy dstDecl.ty body.layouts)
    (hvalid : ValidEnumLayout dstDecl.ty body.layouts tagBytes variants)
    (hv : v < variants.length)
    (hi : i < (variants[v]'hv).length)
    (hfty : fty = ((variants[v]'hv)[i]'hi).ty) :
    annealEvalPlaceLM2_3 body.localDecls body.layouts
        ⟨dstIdx, #[.Downcast vName v, .Field i (encodeTyId fty)]⟩ m =
      .ok ⟨.local 0 dstIdx (some ((variants[v]'hv)[i]'hi).offset)
            topFrame.localsIdentity,
          translateTy fty body.layouts⟩
        { m with
          stack := ⟨#[cacheFrameLocalLayout topFrame dstIdx hlt
            (translateTy dstDecl.ty body.layouts)]⟩ } := by
  let enumLay := translateTy dstDecl.ty body.layouts
  let tf₀ := cacheFrameLocalLayout topFrame dstIdx hlt enumLay
  let m₀ : AnnealStepState := { m with stack := ⟨#[tf₀]⟩ }
  have hres :
      annealResolveAndCacheLocalLayout body.localDecls body.layouts dstIdx none m =
        .ok (tf₀, enumLay) m₀ :=
    annealResolveAndCacheLocalLayout_eq (known := none) hframes hlt hdst_decl hcache
  obtain ⟨varLay, hdown, _, hsz_var, hsized_var, _, _, hoff_all⟩ :=
    downcastEnumLayout_ok hvalid hv
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hvf_all⟩ := hvalid.table_entry
  have hvf := hvf_all v hv
  obtain ⟨hprim_f, hfl_f⟩ := hvf.fields_prim i hi
  rw [← hfty] at hprim_f
  obtain ⟨hrt_f, hsized_f, _⟩ := hprim_f.layout_props (layouts := body.layouts)
  have hbnd_f :
      ((variants[v]'hv)[i]'hi).offset.bytes.toNat +
        (translateTy fty body.layouts).layout.size.bytes.toNat ≤
        enumLay.layout.size.bytes.toNat := by
    rw [hfty, ← hfl_f]
    exact hvf.fields_in_bounds i hi
  have henum_lt64 : enumLay.layout.size.bytes.toNat < 2 ^ 64 := by
    dsimp only [enumLay]
    have h4g := hvalid.size_lt_4gib
    omega
  have hvar_lt64 : varLay.layout.size.bytes.toNat < 2 ^ 64 := by
    rw [hsz_var]; exact henum_lt64
  let carrier : Miri.Interpreter.MemPlace AnnealProv :=
    ⟨⟨Miri.ABI.Size.ZERO, none⟩, .none, none⟩
  have hp1 :
      Miri.Interpreter.project (annealEnumProjectionCx body.layouts none)
        ⟨.indirect carrier, enumLay⟩ (.Downcast vName v) =
      .ok ⟨.indirect carrier, varLay⟩ := by
    unfold Miri.Interpreter.project
    exact projectDowncast_enum_indirect_ok (mp := carrier) rfl hdown hsized_var
  have hp2 :
      Miri.Interpreter.project
        (annealEnumProjectionCx body.layouts (some (encodeTyId fty)))
        ⟨.indirect carrier, varLay⟩ (.Field i (encodeTyId fty)) =
      .ok ⟨.indirect
            ⟨⟨Miri.ABI.Size.ofBytes
                (Miri.ABI.Size.ZERO.bytes +
                  ((variants[v]'hv)[i]'hi).offset.bytes),
              none⟩, .none, none⟩,
          translateTy fty body.layouts⟩ := by
    have hpf := projectField_indirect_eq (layouts := body.layouts)
      (baseLay := varLay) (mp := carrier) (idx := i) (fty := fty)
      (off := ((variants[v]'hv)[i]'hi).offset)
      hrt_f (hoff_all i hi) hsized_f (by dsimp [carrier, Miri.ABI.Size.ZERO]; omega)
    unfold Miri.Interpreter.project Miri.Interpreter.projectField
      Miri.Interpreter.OpTy.offsetWithMeta annealEnumProjectionCx at *
    exact hpf
  have hoff_simp :
      Miri.ABI.Size.ofBytes
        (Miri.ABI.Size.ZERO.bytes + ((variants[v]'hv)[i]'hi).offset.bytes) =
      ((variants[v]'hv)[i]'hi).offset := by
    dsimp [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes]
    rw [UInt64.zero_add]
  have hadd_enum := size_zero_add_eq_of_lt henum_lt64
  have hadd_var := size_zero_add_eq_of_lt hvar_lt64
  have hadd_fld_pair := size_add_of_no_overflow
    (a := ((variants[v]'hv)[i]'hi).offset)
    (b := (translateTy fty body.layouts).layout.size)
    (by omega)
  have hadd_fld := hadd_fld_pair.1
  have hnot_lt_z : ∀ u : UInt64, ¬(u < Miri.ABI.Size.ZERO.bytes) := by
    intro u; dsimp [Miri.ABI.Size.ZERO]; simp [UInt64.lt_iff_toNat_lt]
  have hnot_gt_v : ¬(varLay.layout.size.bytes > enumLay.layout.size.bytes) := by
    dsimp only [enumLay]; rw [hsz_var]; simp [GT.gt]
  have hnot_gt_f :
      ¬(((variants[v]'hv)[i]'hi).offset.bytes +
        (translateTy fty body.layouts).layout.size.bytes >
        varLay.layout.size.bytes) := by
    rw [hsz_var, GT.gt, UInt64.lt_iff_toNat_lt, hadd_fld_pair.2]
    dsimp only [enumLay] at hbnd_f
    omega
  have helem1 :
      annealProjectEnumPlaceElem body.layouts
        ⟨.local 0 dstIdx none topFrame.localsIdentity, enumLay⟩
        (.Downcast vName v) =
      .ok ⟨.local 0 dstIdx (some Miri.ABI.Size.ZERO) topFrame.localsIdentity,
        varLay⟩ := by
    unfold annealProjectEnumPlaceElem
    dsimp only [Option.getD]
    rw [hvalid.isSized_true, hp1]
    simp only [hsized_var, Bool.not_true, Miri.Interpreter.MemPlaceMeta.hasMeta,
      carrier, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
      Bind.bind, Except.bind, Pure.pure, Except.pure,
      hadd_var, hadd_enum, hnot_lt_z, hnot_gt_v, decide_false]
  have helem2 :
      annealProjectEnumPlaceElem body.layouts
        ⟨.local 0 dstIdx (some Miri.ABI.Size.ZERO) topFrame.localsIdentity, varLay⟩
        (.Field i (encodeTyId fty)) =
      .ok ⟨.local 0 dstIdx (some ((variants[v]'hv)[i]'hi).offset)
            topFrame.localsIdentity,
          translateTy fty body.layouts⟩ := by
    unfold annealProjectEnumPlaceElem
    dsimp only [Option.getD]
    rw [hsized_var, hp2, hoff_simp]
    simp only [hsized_f, Bool.not_true, Miri.Interpreter.MemPlaceMeta.hasMeta,
      Bool.or_self, Bool.false_eq_true, ↓reduceIte,
      Bind.bind, Except.bind, Pure.pure, Except.pure,
      hadd_fld, hadd_var, Miri.ABI.Size.ofBytes, hnot_lt_z, hnot_gt_f, decide_false]
  have hlist :
      annealProjectEnumPlaceList body.layouts
        ⟨.local 0 dstIdx none topFrame.localsIdentity, enumLay⟩
        [.Downcast vName v, .Field i (encodeTyId fty)] =
      .ok ⟨.local 0 dstIdx (some ((variants[v]'hv)[i]'hi).offset)
            topFrame.localsIdentity,
          translateTy fty body.layouts⟩ := by
    unfold annealProjectEnumPlaceList
    rw [helem1]
    dsimp only [Bind.bind, Except.bind]
    unfold annealProjectEnumPlaceList
    rw [helem2]
    rfl
  have hid₀ : tf₀.localsIdentity = topFrame.localsIdentity := rfl
  unfold annealEvalPlaceLM2_3 annealEvalEnumProjectedPlace
  have hany :
      ((#[Miri.MIR.ProjectionElem.Downcast vName v,
          .Field i (encodeTyId fty)]).toList.any isDowncastElem) = true := rfl
  simp only [hany, ↓reduceIte,
    get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
    stack_currentFrame?_singleton m.stack topFrame hframes, Option.isNone_some,
    Bool.false_eq_true, hframes, Array.size, List.length_singleton, Nat.sub_self,
    hres, hid₀, hlist]
  rfl

private theorem setOrExtendFields_get?_self :
    ∀ (vs : List Value) (idx : Nat) (v : Value),
      get? (setOrExtendFields vs idx v) idx = some v
  | [], 0, _ => rfl
  | [], n + 1, v => setOrExtendFields_get?_self [] n v
  | _ :: _, 0, _ => rfl
  | _ :: tl, n + 1, v => setOrExtendFields_get?_self tl n v

private theorem setOrExtendFields_get?_ne :
    ∀ (vs : List Value) (idx i : Nat) (v : Value),
      idx ≤ vs.length → i ≠ idx →
      get? (setOrExtendFields vs idx v) i = get? vs i
  | vs, 0, 0, _, _, hne => absurd rfl hne
  | [], 0, _ + 1, _, _, _ => rfl
  | _ :: _, 0, _ + 1, _, _, _ => rfl
  | [], _ + 1, _, _, hle, _ => by cases hle
  | _ :: _, _ + 1, 0, _, _, _ => rfl
  | _ :: tl, idx + 1, i + 1, v, hle, hne =>
      setOrExtendFields_get?_ne tl idx i v (Nat.le_of_succ_le_succ hle)
        (fun h => hne (congrArg Nat.succ h))

private theorem set?_eq_setOrExtendFields_of_lt :
    ∀ (vs : List Value) (idx : Nat) (v : Value),
      idx < vs.length → set? vs idx v = some (setOrExtendFields vs idx v)
  | [], _, _, hlt => by cases hlt
  | _ :: _, 0, _, _ => by
      unfold set?; simp [setOrExtendFields]
  | _ :: tl, idx + 1, v, hlt => by
      have hlt' : idx < tl.length := Nat.lt_of_succ_lt_succ hlt
      have ih := set?_eq_setOrExtendFields_of_lt tl idx v hlt'
      unfold set? at ih ⊢
      simp [hlt', setOrExtendFields] at ih ⊢
      exact ih

private theorem writeProjectedValue_downcast_field_active_eq
    (locals : List LocalSlot) (v_act : Nat) (fieldVals : List Value)
    (vName : Option String) (fieldIdx : Nat) (fieldTy : Ty) (val : Value)
    (hle : fieldIdx ≤ fieldVals.length) :
    writeProjectedValue locals (.aggregate v_act fieldVals)
        [.downcast vName v_act, .field fieldIdx fieldTy] val =
      .ok (.aggregate v_act (setOrExtendFields fieldVals fieldIdx val)) := by
  have hbeq : Nat.beq v_act v_act = true := by simp
  dsimp only [writeProjectedValue]
  rw [hbeq]
  dsimp only [writeProjectedValue]
  by_cases hlt : fieldIdx < fieldVals.length
  · have hget : get? fieldVals fieldIdx = some (fieldVals[fieldIdx]'hlt) := by
      unfold get?; exact List.getElem?_eq_getElem hlt
    rw [hget]
    dsimp only [writeProjectedValue]
    rw [set?_eq_setOrExtendFields_of_lt fieldVals fieldIdx val hlt]
  · have heq : fieldIdx = fieldVals.length := by omega
    subst heq
    have hget : get? fieldVals fieldVals.length = none := by
      unfold get?; exact List.getElem?_eq_none (Nat.le_refl _)
    rw [hget]

/-- Active-variant scalar field write simulation
(`((_dst as variantIdx).fieldIdx : fieldTy) = use op`) under `StateRelLM2_3`:
* When `op` diagnoses `.ub` (`dead` or `uninit`), both Anneal and `lean-miri`
  step to `StepRelLM2_3.ub`.
* When `_dst` is `.dead` and `op` yields scalar `sc`, both Anneal and
  `lean-miri` step to `StepRelLM2_3.ub` (`"write to dead local"`).
* When `_dst` holds `.init (.aggregate variantIdx fieldVals)` with
  `fieldIdx ≤ fieldVals.length` (covering both in-place active-field mutation
  `fieldIdx < fieldVals.length` and sequential trailing-field initialization
  `fieldIdx = fieldVals.length` after a wider-variant `SetDiscriminant`),
  both machines write `sc` into `(variants[variantIdx])[fieldIdx]` at its ABI
  offset, preserving `StateRelLM2_3`, `IsImmediateStepLocal`, and
  `EnumLocalByteUninit` on all `enumId ≠ dstIdx` as well as on `dstIdx` outside
  the written field's byte range `[f.offset, f.offset + f.fieldLayout.size)`. -/
theorem step_downcast_field_write_simulation
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_3 body env allocBudget s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    (henv_valid : ∀ t tb vs, env t = some (tb, vs) →
      ValidEnumLayout t body.layouts tb vs)
    {bb : BasicBlockData} {stmt : Statement}
    {dstIdx : Local} {dstDecl : LocalDecl}
    {vName : Option String} {variantIdx fieldIdx : Nat} {fieldTy : Ty}
    {op : MirAst.Operand}
    {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hkind : stmt.kind = .assign
      ⟨dstIdx, [.downcast vName variantIdx, .field fieldIdx fieldTy]⟩
      (.use op))
    (hdst_decl : get? body.localDecls dstIdx = some dstDecl)
    (henv_dst : env dstDecl.ty = some (tagBytes, variants))
    (hv_lt : variantIdx < variants.length)
    (hf_lt : fieldIdx < (variants[variantIdx]'hv_lt).length)
    (hfty_eq : fieldTy = ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).ty)
    (hop : ∀ tf, m.stack.frames = #[tf] →
      WellTypedEnumScalarOp body tf op fieldTy)
    (hdst_active :
      get? s.frame.locals dstIdx = some .dead ∨
      ∃ fieldVals,
        get? s.frame.locals dstIdx =
          some (.init (.aggregate variantIdx fieldVals)) ∧
        fieldIdx ≤ fieldVals.length) :
    let mRes :=
      Miri.Interpreter.Step.step
        (annealStepHooksLM2_3 body.localDecls body.layouts) () m
    StepRelLM2_3 body env allocBudget m (stepMirFn body s) mRes ∧
    ((∀ msg, mRes.2 ≠ .error (.undefinedBehavior msg)) →
      (∀ enumId b,
        (enumId ≠ dstIdx ∨
          ((b < ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).offset.bytes.toNat ∨
            ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).offset.bytes.toNat +
              ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).fieldLayout.size.bytes.toNat ≤
              b) ∧
            b < (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat)) →
        EnumLocalByteUninit m enumId b →
        EnumLocalByteUninit mRes.1 enumId b) ∧
      (∀ j, IsImmediateStepLocal m j → IsImmediateStepLocal mRes.1 j)) := by
  intro mRes
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe, halloc,
      hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hvalid := henv_valid dstDecl.ty tagBytes variants henv_dst
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hvf_all⟩ := hvalid.table_entry
  have hvf := hvf_all variantIdx hv_lt
  let fDesc := (variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt
  obtain ⟨hprim_f, hfl_f⟩ := hvf.fields_prim fieldIdx hf_lt
  have hprim_fty : IsPrimScalarTy fieldTy := by rw [hfty_eq]; exact hprim_f
  have hfl_eq : (translateTy fieldTy body.layouts).layout = fDesc.fieldLayout := by
    rw [hfty_eq]; exact hfl_f.symm
  have hsized_fty : (translateTy fieldTy body.layouts).layout.isSized = true :=
    hprim_fty.isSized_lm2_3 body.layouts
  obtain ⟨slot_d0, mls_d0, hlt_d0, hslot_d0, hmls_d0_eq, hloc_d0⟩ :=
    hframe.lookup_local hdst_decl
  have hcache_d0 : ∀ l, (topFrame.locals[dstIdx]'hlt_d0).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d0_eq]; exact hloc_d0.layout_eq
  let tf₀ := cacheFrameLocalLayout topFrame dstIdx hlt_d0
    (translateTy dstDecl.ty body.layouts)
  let m₀ : AnnealStepState := { m with stack := ⟨#[tf₀]⟩ }
  have heval_dst := annealEvalPlaceLM2_3_downcast_field_ok
    (vName := vName) hframes hlt_d0 hdst_decl hcache_d0 hvalid hv_lt hf_lt hfty_eq
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 dstIdx (some fDesc.offset) topFrame.localsIdentity,
      translateTy fieldTy body.layouts⟩
  have hnot_mem :
      usesStructMemCopyDest
        ⟨.local 0 dstIdx (some fDesc.offset) topFrame.localsIdentity,
          translateTy fieldTy body.layouts⟩ = false :=
    usesStructMemCopyDest_false_of_primScalar destPlace rfl hprim_fty
  have hm_eval :
      Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_3 body.localDecls body.layouts) ()
        (translateStmt stmt) m =
      Miri.Interpreter.runRvalue
        ((annealEvalOperandLM2_3 body.localDecls body.layouts
            (translateOperand op) (some (translateTy fieldTy body.layouts)) >>=
          annealReadImmediateLM2_2) >>=
          fun imm => annealWriteImmediateLM2_2 imm.imm destPlace)
        m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    rw [hkind]
    have hlm23_asgn :
        lm23Assign body.localDecls body.layouts
          ⟨dstIdx, #[.Downcast vName variantIdx, .Field fieldIdx (encodeTyId fieldTy)]⟩
          (.Use (translateOperand op) .No) = true := rfl
    dsimp only [translateStmtKind, translatePlace, translateProjectionElem,
      List.map, List.toArray, translateRvalue, annealStepHooksLM2_3]
    change (if lm23Assign body.localDecls body.layouts
        ⟨dstIdx, #[.Downcast vName variantIdx, .Field fieldIdx (encodeTyId fieldTy)]⟩
        (.Use (translateOperand op) .No) then _ else _) = _
    rw [hlm23_asgn]
    simp only [↓reduceIte]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooksLM2_3
    dsimp only [annealRvalueHooksLM2_2]
    rw [EStateM.bind_eq_ok heval_dst]
    dsimp only [destPlace]
    exact bind_copyOp_eq_of_not_usesStructMemCopyDest hnot_mem m₀
  have hfr₀_excl : FrameRelLM2_3Except body env dstIdx m.machine s.frame tf₀ :=
    FrameRelLM2_3Except.of_frameRel (hframe.cache_local_layout hdst_decl hlt_d0)
  have hdisj₀ : MemoryAllocDisjoint tf₀ :=
    MemoryAllocDisjoint_cacheFrameLocalLayout hdisj hlt_d0 _
  have hop₀ : WellTypedEnumScalarOp body tf₀ op fieldTy :=
    (hop topFrame hframes).mono_immediate
      (fun _ hj => hj.cache_layout hlt_d0 _)
  have huninit_m₀ : ∀ enumId b,
      EnumLocalByteUninit m enumId b → EnumLocalByteUninit m₀ enumId b :=
    fun _ _ hu => EnumLocalByteUninit.of_cache_layout hframes hu
  have himm_m₀ : ∀ j, IsImmediateStepLocal m j → IsImmediateStepLocal m₀ j :=
    fun _ hj => IsImmediateStepLocal.of_cache_layout hframes hj
  have htf₀_dst :
      tf₀.locals[dstIdx]? =
        some ⟨mls_d0.value, some (translateTy dstDecl.ty body.layouts)⟩ := by
    dsimp only [tf₀, cacheFrameLocalLayout]
    rw [Array.getElem?_set_self hlt_d0, hmls_d0_eq]
  rcases evalEnumScalarOp_except_dst henv_valid hdst_decl henv_dst
      (m := m₀) rfl hfr₀_excl hop₀ s.memory.globals
      (some (translateTy fieldTy body.layouts)) with
    ⟨sc, msc, tf₁, hev_op, hval_op, hm_op, hrel_sc, hlaysz_sc, hbool_sc, hchar_sc,
      hfr₁_excl, htf₁_eta, hsz₁, hdst_tf₁?, himm_tf₁, hdisj_fn₁, huninit_m₁⟩ |
    ⟨m_err, msg, ha_op_ub, hm_op_err⟩
  · have hdisj₁ := hdisj_fn₁ hdisj₀
    have hlt_dst1 : dstIdx < tf₁.locals.size := by
      rw [hsz₁]; dsimp [tf₀]; rw [cacheFrameLocalLayout_size]; exact hlt_d0
    have hdst_tf₁ :
        tf₁.locals[dstIdx]'hlt_dst1 =
          ⟨mls_d0.value, some (translateTy dstDecl.ty body.layouts)⟩ := by
      have hg := hdst_tf₁?
      rw [htf₀_dst, Array.getElem?_eq_getElem hlt_dst1] at hg
      exact Option.some.inj hg
    have hid₁ : tf₁.localsIdentity = topFrame.localsIdentity := by
      rw [htf₁_eta]; rfl
    have hrc₁ : tf₁.returnContinuation = topFrame.returnContinuation := by
      rw [htf₁_eta]; rfl
    have hrp₁ : tf₁.returnPlace = topFrame.returnPlace := by
      rw [htf₁_eta]; rfl
    let m₁ : AnnealStepState := { m with stack := ⟨#[tf₁]⟩ }
    have hwrite_eq :
        annealWriteImmediateLM2_2 (.scalar (.fromScalarInt msc)) destPlace m₁ =
        annealWriteProjectedLocalImmediate (.scalar (.fromScalarInt msc))
          destPlace .nil emptyLayoutTable m₁ := by
      unfold annealWriteImmediateLM2_2
      simp [get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
        stack_currentFrame?_singleton m₁.stack tf₁ rfl, destPlace]
    rcases hdst_active with hdead_slot | ⟨fieldVals, hinit_slot, hfle⟩
    · -- Dead `_dst`: lockstep UB (`"write to dead local"`).
      rw [hslot_d0] at hdead_slot
      injection hdead_slot with hsl_eq; subst hsl_eq
      have hv_dead : mls_d0.value = .dead := by
        cases hloc_d0 with
        | base _ _ hn _ => rw [henv_dst] at hn; cases hn
        | enumDead _ _ _ _ _ _ => rfl
      rw [hv_dead] at hdst_tf₁
      have ha_ub : evalStmt s stmt body.localDecls body.layouts =
          MirStepNode.fail .ub := by
        unfold evalStmt; rw [hkind]; dsimp only
        rw [evalRvalue_use_nil_borrows_ok_lm2_3 hbor (by rw [hcaller]; exact hev_op) hval_op]
        dsimp only
        rw [hslot_d0]
      have hw_dead := annealWriteProjectedLocalImmediate_dead_ub
        (localDecls := .nil) (layouts := emptyLayoutTable)
        (val := .scalar (.fromScalarInt msc)) (m := m₁)
        (relOff := fDesc.offset) (iden := topFrame.localsIdentity)
        hsized_fty rfl hlt_dst1 hdst_tf₁
      have hm_ub :
          Miri.Interpreter.Step.evalStatement
            (annealStepHooksLM2_3 body.localDecls body.layouts) ()
            (translateStmt stmt) m =
          (m₁, .error (.undefinedBehavior "write to dead local")) := by
        rw [hm_eval]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hm_op]; dsimp only [m₀]
        rw [hwrite_eq]; simp only [destPlace, hw_dead]
      dsimp only [mRes]
      rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq
        hframe.location_eq hbb hstmt hm_ub]
      exact ⟨.ub _ _, fun hno => False.elim (hno _ rfl)⟩
    · -- Active-variant `_dst`: write scalar at `fDesc.offset`.
      rw [hslot_d0] at hinit_slot
      injection hinit_slot with hsl_eq; subst hsl_eq
      have hlt_af : dstIdx < s.frame.locals.length := by
        unfold get? at hslot_d0
        exact (List.getElem?_eq_some_iff.mp hslot_d0).1
      cases hloc_d0 with
      | base _ _ hn _ => rw [henv_dst] at hn; cases hn
      | enumInd tb_d vs_d v_act fv_d mp c_d henv_d _ hemr =>
        rw [henv_dst] at henv_d
        injection henv_d with hp_d; rcases hp_d with ⟨rfl, rfl⟩
        rcases hemr with
          ⟨allocId, borTag, baseAddr, localAlloc, words, msc_tag,
            _, hv_act_lt, hprov, hmis, hmeta, hlive, hbase, hptr, hovf,
            hmut, halign, hbs, hlen, hpmap, hmask, htag_rel, htag_bits,
            htag_init, htag_read, hpayload⟩
        obtain ⟨hfind_live, u, hu_lt, hfidx, hget_u⟩ := hlive
        have hsz_f : fDesc.fieldLayout.size = translateSizeBytes sc.sizeBytes := by
          rw [← hfl_eq]; exact hlaysz_sc
        have hbnd_f :
            fDesc.offset.bytes.toNat +
              (translateSizeBytes sc.sizeBytes).bytes.toNat ≤
              localAlloc.allocation.byteSize.bytes.toNat := by
          rw [← hsz_f, hbs]
          exact hvf.fields_in_bounds fieldIdx hf_lt
        obtain ⟨alloc', words', hw, hbs', hlen', hmut', hpmap', hmask',
            hbits', hraw', hinit_f, hread_f⟩ :=
          alloc_writeScalar_at_offset_mask hrel_sc hlen hmut hpmap hmask hbnd_f
        rw [← hsz_f] at hinit_f hread_f hbits' hraw'
        have hovf_off : baseAddr.toNat + fDesc.offset.bytes.toNat < 2 ^ 64 := by
          have hpos_f : 0 < fDesc.fieldLayout.size.bytes.toNat := by
            rw [hsz_f]; exact translateSizeBytes_pos_lm2_3 hrel_sc.validBytes
          dsimp only [fDesc] at hpos_f ⊢
          have hb_enum := hvf.fields_in_bounds fieldIdx hf_lt
          omega
        have hw_proj := annealWriteProjectedLocalImmediate_indirect_scalar_ok
          (localDecls := .nil) (layouts := emptyLayoutTable)
          (s := .fromScalarInt msc) (m := m₁) (tf := tf₁)
          (localId := dstIdx) (relOff := fDesc.offset)
          (iden := topFrame.localsIdentity)
          (fieldLay := translateTy fieldTy body.layouts)
          hsized_fty rfl hlt_dst1 hdst_tf₁ hprov hbase hptr hovf_off
          hu_lt hfidx hget_u hw
        let mach' := updateAllocMachine m.machine u allocId localAlloc.kind alloc'
        let m_end : AnnealStepState := ⟨⟨#[tf₁]⟩, mach'⟩
        have hm_ok :
            Miri.Interpreter.Step.evalStatement
              (annealStepHooksLM2_3 body.localDecls body.layouts) ()
              (translateStmt stmt) m = (m_end, .ok ()) := by
          rw [hm_eval]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hm_op]; dsimp only [m₀]
          rw [hwrite_eq]; dsimp only [destPlace]; rw [hw_proj]
        let newFields := setOrExtendFields fieldVals fieldIdx (.scalar sc)
        have ha_ok :
            evalStmt s stmt body.localDecls body.layouts =
            MirStepNode.step
              (advanceStmt s
                (s.frame.locals.set dstIdx (.init (.aggregate variantIdx newFields)))
                s.memory) := by
          unfold evalStmt; rw [hkind]; dsimp only
          rw [evalRvalue_use_nil_borrows_ok_lm2_3 hbor (by rw [hcaller]; exact hev_op) hval_op]
          dsimp only
          rw [hslot_d0]
          dsimp only [ensureNestedFieldShells, writeProjectedForLocal]
          rw [hvalid.placeTouchesUnion_downcast_field hdst_decl]
          dsimp only
          rw [writeProjectedValue_downcast_field_active_eq _ _ _ _ _ _ _ hfle]
          dsimp only [newFields]
          rw [set?_eq_some_set hlt_af
            (.init (.aggregate variantIdx (setOrExtendFields fieldVals fieldIdx (.scalar sc)))),
            hprot, hbor]
          dsimp only [invalidateConflictingBorrowsAtProj]
          apply congrArg (fun mem =>
            MirStepNode.step
              (advanceStmt s
                (s.frame.locals.set dstIdx
                  (.init (.aggregate variantIdx (setOrExtendFields fieldVals fieldIdx (.scalar sc)))))
                mem))
          rcases hm_s : s.memory with ⟨_, _, bor, _, _, _, _, prot, _, _⟩
          rw [hm_s] at hbor hprot
          dsimp only at hbor hprot
          subst hbor hprot
          rfl
        -- Re-establish `EnumMemRel` on `mach'` with `newFields`.
        have hrawA_len :
            (lm22AllocRaw localAlloc.allocation).size =
              localAlloc.allocation.byteSize.bytes.toNat := by
          have : (lm22AllocRaw localAlloc.allocation).size =
              localAlloc.allocation.len := by cases localAlloc.allocation; rfl
          rw [this, hlen]
        have hrawA'_len :
            (lm22AllocRaw alloc').size = alloc'.byteSize.bytes.toNat := by
          have : (lm22AllocRaw alloc').size = alloc'.len := by cases alloc'; rfl
          rw [this, hlen', hbs', hlen]
        have hlive' :
            LiveAllocEntry mach'.memory.live allocId ⟨localAlloc.kind, alloc'⟩ :=
          LiveAllocEntry.of_set!_self ⟨hfind_live, u, hu_lt, hfidx, hget_u⟩
            hu_lt hfidx ⟨localAlloc.kind, alloc'⟩
        have hafter_tag := hvf.fields_after_tag fieldIdx hf_lt
        have htb_vsb := validScalarBytes_of_tagBytes hvalid.tagBytes_valid
        have htb_pos : 0 < (translateSizeBytes tagBytes).bytes.toNat :=
          translateSizeBytes_pos_lm2_3 htb_vsb
        have htb_sz : (translateSizeBytes tagBytes).bytes.toNat = tagBytes :=
          translateSizeBytes_toNat_eq htb_vsb
        have htb_bnd :
            Miri.ABI.Size.ZERO.bytes.toNat +
              (translateSizeBytes tagBytes).bytes.toNat ≤
              localAlloc.allocation.byteSize.bytes.toNat := by
          dsimp [Miri.ABI.Size.ZERO]
          rw [Nat.zero_add, htb_sz, hbs]
          exact hvalid.size_ge_tag
        have htag_bits' : ∀ b, b < tagBytes → maskBlocksGetBit words' b = true := by
          intro b hb
          have hb_sz : b < localAlloc.allocation.byteSize.bytes.toNat := by
            rw [hbs]; have hge := hvalid.size_ge_tag; omega
          rw [hbits' b hb_sz, htag_bits b hb, Bool.true_or]
        have htag_init' :
            alloc'.initializationMask.isRangeInitialized
              (Miri.Memory.allocRange Miri.ABI.Size.ZERO
                (translateSizeBytes tagBytes)) = .ok (.ok ()) := by
          apply initMaskWordRel_isRangeInitialized hmask' htb_pos htb_bnd
          intro b _ hb_hi
          dsimp [Miri.ABI.Size.ZERO] at hb_hi
          rw [Nat.zero_add, htb_sz] at hb_hi
          exact htag_bits' b hb_hi
        have htag_read' :
            alloc'.readScalar annealTargetDataLayout
              (Miri.Memory.allocRange Miri.ABI.Size.ZERO
                (translateSizeBytes tagBytes)) false =
              .ok (.fromScalarInt msc_tag) := by
          rw [alloc_readScalar_congr hrawA_len hrawA'_len hbs' htag_init
            htag_init' htb_bnd ?_]
          · exact htag_read
          · rw [hraw']
            exact extract_writeBytes_disjoint
              (lm22AllocRaw localAlloc.allocation)
              (lm22LeBytes sc.bits fDesc.fieldLayout.size.bytes.toNat)
              (lm22LeBytes_size _ _)
              (by rw [hrawA_len, hsz_f]; exact hbnd_f)
              (by rw [hrawA_len]; exact htb_bnd)
              (Or.inl (by dsimp [Miri.ABI.Size.ZERO]; rw [Nat.zero_add, htb_sz]; exact hafter_tag))
        have hpayload' :
            ∀ (i : Nat) (hi : i < (variants[variantIdx]'hv_lt).length),
              let f_i := (variants[variantIdx]'hv_lt)[i]'hi
              (∃ sc_i msc_i,
                get? newFields i = some (.scalar sc_i) ∧
                ScalarRel sc_i msc_i ∧
                f_i.fieldLayout.size = translateSizeBytes sc_i.sizeBytes ∧
                (f_i.ty.kind = .bool →
                  sc_i.sizeBytes = 1 ∧ (sc_i.bits = 0 ∨ sc_i.bits = 1)) ∧
                (f_i.ty.kind = .char →
                  sc_i.sizeBytes = 4 ∧ isValidCharCode sc_i.bits = true) ∧
                (∀ b, f_i.offset.bytes.toNat ≤ b →
                  b < f_i.offset.bytes.toNat + f_i.fieldLayout.size.bytes.toNat →
                  maskBlocksGetBit words' b = true) ∧
                alloc'.initializationMask.isRangeInitialized
                  (Miri.Memory.allocRange f_i.offset f_i.fieldLayout.size) =
                  .ok (.ok ()) ∧
                alloc'.readScalar annealTargetDataLayout
                  (Miri.Memory.allocRange f_i.offset f_i.fieldLayout.size) false =
                  .ok (.fromScalarInt msc_i)) ∨
              (get? newFields i = none ∧
                ∃ b,
                  f_i.offset.bytes.toNat ≤ b ∧
                  b < f_i.offset.bytes.toNat + f_i.fieldLayout.size.bytes.toNat ∧
                  maskBlocksGetBit words' b = false) := by
          intro i hi
          by_cases hif : i = fieldIdx
          · subst hif
            left
            refine ⟨sc, msc, setOrExtendFields_get?_self _ _ _, hrel_sc, hsz_f,
              (by rw [← hfty_eq]; exact hbool_sc),
              (by rw [← hfty_eq]; exact hchar_sc), ?_, hinit_f, hread_f⟩
            intro b hlo hhi
            have hb_sz : b < localAlloc.allocation.byteSize.bytes.toNat := by
              have hb_e := hvf.fields_in_bounds i hi; rw [hbs]; omega
            rw [hbits' b hb_sz]
            have hdec : decide (fDesc.offset.bytes.toNat ≤ b ∧
                b < fDesc.offset.bytes.toNat + fDesc.fieldLayout.size.bytes.toNat) = true :=
              decide_eq_true ⟨hlo, hhi⟩
            rw [hdec, Bool.or_true]
          · have hdisj_fi := hvf.fields_disjoint i fieldIdx hi hf_lt hif
            have hbnd_i :
                ((variants[variantIdx]'hv_lt)[i]'hi).offset.bytes.toNat +
                  ((variants[variantIdx]'hv_lt)[i]'hi).fieldLayout.size.bytes.toNat ≤
                  localAlloc.allocation.byteSize.bytes.toNat := by
              rw [hbs]; exact hvf.fields_in_bounds i hi
            rcases hpayload i hi with
              ⟨sc_i, msc_i, hfv_i, hrel_i, hsz_i, hb_i, hc_i, hbits_i,
                hinit_i, hread_i⟩ |
              ⟨hnone_i, b_u, hlo_u, hhi_u, hfalse_u⟩
            · left
              have hbits'_i :
                  ∀ b, ((variants[variantIdx]'hv_lt)[i]'hi).offset.bytes.toNat ≤ b →
                    b < ((variants[variantIdx]'hv_lt)[i]'hi).offset.bytes.toNat +
                      ((variants[variantIdx]'hv_lt)[i]'hi).fieldLayout.size.bytes.toNat →
                    maskBlocksGetBit words' b = true := by
                intro b hlo hhi
                have hb_sz : b < localAlloc.allocation.byteSize.bytes.toNat := by omega
                rw [hbits' b hb_sz, hbits_i b hlo hhi, Bool.true_or]
              have hpos_i :
                  0 < ((variants[variantIdx]'hv_lt)[i]'hi).fieldLayout.size.bytes.toNat := by
                rw [hsz_i]; exact translateSizeBytes_pos_lm2_3 hrel_i.validBytes
              have hinit'_i :
                  alloc'.initializationMask.isRangeInitialized
                    (Miri.Memory.allocRange
                      ((variants[variantIdx]'hv_lt)[i]'hi).offset
                      ((variants[variantIdx]'hv_lt)[i]'hi).fieldLayout.size) =
                    .ok (.ok ()) :=
                initMaskWordRel_isRangeInitialized hmask' hpos_i hbnd_i hbits'_i
              have hread'_i :
                  alloc'.readScalar annealTargetDataLayout
                    (Miri.Memory.allocRange
                      ((variants[variantIdx]'hv_lt)[i]'hi).offset
                      ((variants[variantIdx]'hv_lt)[i]'hi).fieldLayout.size) false =
                    .ok (.fromScalarInt msc_i) := by
                rw [alloc_readScalar_congr hrawA_len hrawA'_len hbs' hinit_i
                  hinit'_i hbnd_i ?_]
                · exact hread_i
                · rw [hraw']
                  exact extract_writeBytes_disjoint
                    (lm22AllocRaw localAlloc.allocation)
                    (lm22LeBytes sc.bits fDesc.fieldLayout.size.bytes.toNat)
                    (lm22LeBytes_size _ _)
                    (by rw [hrawA_len, hsz_f]; exact hbnd_f)
                    (by rw [hrawA_len]; exact hbnd_i)
                    hdisj_fi
              exact ⟨sc_i, msc_i,
                (setOrExtendFields_get?_ne _ _ _ _ hfle hif).trans hfv_i,
                hrel_i, hsz_i, hb_i, hc_i, hbits'_i, hinit'_i, hread'_i⟩
            · right
              refine ⟨(setOrExtendFields_get?_ne _ _ _ _ hfle hif).trans hnone_i,
                b_u, hlo_u, hhi_u, ?_⟩
              have hb_sz : b_u < localAlloc.allocation.byteSize.bytes.toNat := by omega
              have hdec_f :
                  decide (fDesc.offset.bytes.toNat ≤ b_u ∧
                    b_u < fDesc.offset.bytes.toNat +
                      fDesc.fieldLayout.size.bytes.toNat) = false :=
                decide_eq_false (by dsimp only [fDesc]; rcases hdisj_fi with h1 | h2 <;> omega)
              rw [hbits' b_u hb_sz, hfalse_u, hdec_f]; rfl
        have hemr_new :
            EnumMemRel mach' dstDecl.ty body.layouts tagBytes variants
              variantIdx newFields mp :=
          .mk allocId borTag baseAddr ⟨localAlloc.kind, alloc'⟩ words' msc_tag
            hvalid hv_lt hprov hmis hmeta hlive' hbase hptr hovf hmut' halign
            (hbs'.trans hbs) (hlen'.trans (hlen.trans (by rw [hbs']))) hpmap'
            (by rw [hbs']; exact hmask') htag_rel htag_bits' htag_init'
            htag_read' hpayload'
        have hfr_end :
            FrameRelLM2_3 body env mach'
              { s.frame with
                locals := s.frame.locals.set dstIdx
                  (.init (.aggregate variantIdx newFields)) }
              tf₁ := by
          have hex := hfr₁_excl.of_updateAlloc_excl (kind := localAlloc.kind)
            (alloc' := alloc') hdisj₁ hdst_tf₁ hprov hu_lt hget_u
          exact hex.finish_dst hdst_decl
            (set?_eq_some_set hlt_af (.init (.aggregate variantIdx newFields)))
            (by rw [Array.getElem?_eq_getElem hlt_dst1, hdst_tf₁])
            (.enumInd tagBytes variants variantIdx newFields mp
              (some (translateTy dstDecl.ty body.layouts)) henv_dst
              (fun _ hl => (Option.some.inj (Option.mem_def.mp hl)).symm)
              hemr_new)
        dsimp only [mRes]
        rw [ha_ok,
          miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq
            hbb hstmt hm_ok rfl hfr_end.location_eq]
        refine ⟨.step _ _ ?_, fun _ => ⟨?_, ?_⟩⟩
        · exact .mk _ rfl (hrc₁.trans hretCont)
            ⟨retLay, by dsimp; rw [hrp₁, hretPlace, hid₁]⟩
            hfr_end.step_pc
            (halloc.of_updateAlloc hu_lt hget_u)
            hcal hstack hbor hprot hcaller hdisj₁
        · intro enumId b hcond hu
          have hu₁ : EnumLocalByteUninit m₁ enumId b :=
            huninit_m₁ enumId b (huninit_m₀ enumId b hu)
          apply EnumLocalByteUninit.of_set_location
            (m := m_end) rfl
          intro tf' mp' c' id' bt' la' hf' hloc' hprov' hfind'
          injection hf' with ha; injection ha with ht; subst ht
          by_cases heq_id : enumId = dstIdx
          · subst heq_id
            rcases hcond with hne | ⟨hb_out, hb_lt_enum⟩
            · exact False.elim (hne rfl)
            have htf₁_d : tf₁.locals[enumId]? =
                some ⟨.live (.indirect mp),
                  some (translateTy dstDecl.ty body.layouts)⟩ := by
              rw [Array.getElem?_eq_getElem hlt_dst1, hdst_tf₁]
            rw [htf₁_d] at hloc'
            injection hloc' with hls_eq
            injection hls_eq with hv_eq _
            injection hv_eq with hop_eq
            injection hop_eq with hmp_eq
            subst hmp_eq
            rw [hprov] at hprov'
            injection hprov' with hp_eq; injection hp_eq with hid_eq _
            subst hid_eq
            dsimp only [m_end] at hfind'
            rw [hlive'.1] at hfind'
            injection hfind' with hpair_eq
            have hla_eq : la' = ⟨localAlloc.kind, alloc'⟩ :=
              (Prod.mk.inj hpair_eq).2.symm
            subst hla_eq
            have hold_f := hu₁ tf₁ mp _ allocId borTag localAlloc
              rfl htf₁_d hprov hfind_live
            have hb_lt_sz : b < localAlloc.allocation.byteSize.bytes.toNat := by
              rw [hbs]; exact hb_lt_enum
            rw [initMaskWordRel_get hmask hb_lt_sz] at hold_f
            injection hold_f with hbit_old
            dsimp only
            rw [initMaskWordRel_get hmask' hb_lt_sz]
            congr 1
            have hdec_f :
                decide (fDesc.offset.bytes.toNat ≤ b ∧
                  b < fDesc.offset.bytes.toNat +
                    fDesc.fieldLayout.size.bytes.toNat) = false :=
              decide_eq_false (by dsimp only [fDesc]; rcases hb_out with h1 | h2 <;> omega)
            rw [hbits' b hb_lt_sz, hbit_old, hdec_f]; rfl
          · have hid_ne : id' ≠ allocId := by
              have htf₁_d : tf₁.locals[dstIdx]? =
                  some ⟨.live (.indirect mp),
                    some (translateTy dstDecl.ty body.layouts)⟩ := by
                rw [Array.getElem?_eq_getElem hlt_dst1, hdst_tf₁]
              have hne_p := hdisj₁ enumId dstIdx mp' mp c' _ heq_id hloc' htf₁_d
              rw [hprov', hprov] at hne_p
              intro rfl; exact hne_p rfl
            have hfind_old :
                m.machine.memory.live.find? (fun (k0, _) => k0 == id') =
                  some (id', la') := by
              dsimp only [m_end, mach', updateAllocMachine] at hfind'
              rw [find?_live_set!_ne _ hu_lt hget_u hid_ne] at hfind'
              exact hfind'
            exact hu₁ tf₁ mp' c' id' bt' la' rfl hloc' hprov' hfind_old
        · intro j hj tf' hf'
          injection hf' with ha; injection ha with ht; subst ht
          exact himm_tf₁ j (himm_m₀ j hj tf₀ rfl)
  · -- Operand `op` failed with `.ub` in both Anneal and `lean-miri`.
    have ha_ub : evalStmt s stmt body.localDecls body.layouts =
        MirStepNode.fail .ub := by
      unfold evalStmt; rw [hkind]; dsimp only
      rw [evalRvalue_use_nil_borrows_lm2_3 _ _ _ hbor, hcaller, ha_op_ub]
    have hm_ub :
        Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_3 body.localDecls body.layouts) ()
          (translateStmt stmt) m =
        (m_err, .error (.undefinedBehavior msg)) := by
      rw [hm_eval]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_error hm_op_err]
    dsimp only [mRes]
    rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq
      hframe.location_eq hbb hstmt hm_ub]
    exact ⟨.ub _ _, fun hno => False.elim (hno _ rfl)⟩

/-- Inactive-variant downcast-field write divergence
(`((_dst as variantIdx).fieldIdx : fieldTy) = use op` when `_dst` holds
`.init (.aggregate v_act fieldVals)` with `variantIdx ≠ v_act` and `op`
evaluates without UB):
* Anneal's value-tree `writeProjectedValue` checks `Nat.beq v_act variantIdx`
  on `.downcast` and fails with `MirStepNode.fail .ub`.
* Vendored `lean-miri`'s byte-offset `projectDowncast` + `projectField`
  computes `.local 0 dstIdx (some f.offset) ...` without reading the
  discriminant tag, and `writePlaceImmediateNoValidate` writes the scalar
  bytes into `[f.offset, f.offset + f.fieldLayout.size)` (`(m', .ok true)`).
This formally witnesses why `step_downcast_field_write_simulation` requires
`_dst` to be either `.dead` or active at `variantIdx` (just as Rustc MIR
forbids writing through an inactive enum downcast before `SetDiscriminant`). -/
theorem step_downcast_field_write_inactive_divergence
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_3 body env allocBudget s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    (henv_valid : ∀ t tb vs, env t = some (tb, vs) →
      ValidEnumLayout t body.layouts tb vs)
    {bb : BasicBlockData} {stmt : Statement}
    {dstIdx : Local} {dstDecl : LocalDecl}
    {vName : Option String} {variantIdx v_act fieldIdx : Nat} {fieldTy : Ty}
    {fieldVals : List Value} {op : MirAst.Operand}
    {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hkind : stmt.kind = .assign
      ⟨dstIdx, [.downcast vName variantIdx, .field fieldIdx fieldTy]⟩
      (.use op))
    (hdst_decl : get? body.localDecls dstIdx = some dstDecl)
    (henv_dst : env dstDecl.ty = some (tagBytes, variants))
    (hv_lt : variantIdx < variants.length)
    (hf_lt : fieldIdx < (variants[variantIdx]'hv_lt).length)
    (hfty_eq : fieldTy = ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).ty)
    (hop : ∀ tf, m.stack.frames = #[tf] →
      WellTypedEnumScalarOp body tf op fieldTy)
    (hop_ok :
      evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil ≠ .ub)
    (hdst_slot :
      get? s.frame.locals dstIdx = some (.init (.aggregate v_act fieldVals)))
    (hne_var : variantIdx ≠ v_act) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step
        (annealStepHooksLM2_3 body.localDecls body.layouts) () m =
      (m', .ok true) := by
  rcases hstate with
    ⟨topFrame, hframes, _, _, hframe, _, hcal, _, hbor, _, hcaller, _⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hvalid := henv_valid dstDecl.ty tagBytes variants henv_dst
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hvf_all⟩ := hvalid.table_entry
  have hvf := hvf_all variantIdx hv_lt
  let fDesc := (variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt
  obtain ⟨hprim_f, hfl_f⟩ := hvf.fields_prim fieldIdx hf_lt
  have hprim_fty : IsPrimScalarTy fieldTy := by rw [hfty_eq]; exact hprim_f
  have hfl_eq : (translateTy fieldTy body.layouts).layout = fDesc.fieldLayout := by
    rw [hfty_eq]; exact hfl_f.symm
  have hsized_fty : (translateTy fieldTy body.layouts).layout.isSized = true :=
    hprim_fty.isSized_lm2_3 body.layouts
  obtain ⟨slot_d0, mls_d0, hlt_d0, hslot_d0, hmls_d0_eq, hloc_d0⟩ :=
    hframe.lookup_local hdst_decl
  have hcache_d0 : ∀ l, (topFrame.locals[dstIdx]'hlt_d0).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d0_eq]; exact hloc_d0.layout_eq
  let tf₀ := cacheFrameLocalLayout topFrame dstIdx hlt_d0
    (translateTy dstDecl.ty body.layouts)
  let m₀ : AnnealStepState := { m with stack := ⟨#[tf₀]⟩ }
  have heval_dst := annealEvalPlaceLM2_3_downcast_field_ok
    (vName := vName) hframes hlt_d0 hdst_decl hcache_d0 hvalid hv_lt hf_lt hfty_eq
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 dstIdx (some fDesc.offset) topFrame.localsIdentity,
      translateTy fieldTy body.layouts⟩
  have hnot_mem :
      usesStructMemCopyDest
        ⟨.local 0 dstIdx (some fDesc.offset) topFrame.localsIdentity,
          translateTy fieldTy body.layouts⟩ = false :=
    usesStructMemCopyDest_false_of_primScalar destPlace rfl hprim_fty
  have hm_eval :
      Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_3 body.localDecls body.layouts) ()
        (translateStmt stmt) m =
      Miri.Interpreter.runRvalue
        ((annealEvalOperandLM2_3 body.localDecls body.layouts
            (translateOperand op) (some (translateTy fieldTy body.layouts)) >>=
          annealReadImmediateLM2_2) >>=
          fun imm => annealWriteImmediateLM2_2 imm.imm destPlace)
        m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    rw [hkind]
    have hlm23_asgn :
        lm23Assign body.localDecls body.layouts
          ⟨dstIdx, #[.Downcast vName variantIdx, .Field fieldIdx (encodeTyId fieldTy)]⟩
          (.Use (translateOperand op) .No) = true := rfl
    dsimp only [translateStmtKind, translatePlace, translateProjectionElem,
      List.map, List.toArray, translateRvalue, annealStepHooksLM2_3]
    change (if lm23Assign body.localDecls body.layouts
        ⟨dstIdx, #[.Downcast vName variantIdx, .Field fieldIdx (encodeTyId fieldTy)]⟩
        (.Use (translateOperand op) .No) then _ else _) = _
    rw [hlm23_asgn]
    simp only [↓reduceIte]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooksLM2_3
    dsimp only [annealRvalueHooksLM2_2]
    rw [EStateM.bind_eq_ok heval_dst]
    dsimp only [destPlace]
    exact bind_copyOp_eq_of_not_usesStructMemCopyDest hnot_mem m₀
  have hfr₀_excl : FrameRelLM2_3Except body env dstIdx m.machine s.frame tf₀ :=
    FrameRelLM2_3Except.of_frameRel (hframe.cache_local_layout hdst_decl hlt_d0)
  have hop₀ : WellTypedEnumScalarOp body tf₀ op fieldTy :=
    (hop topFrame hframes).mono_immediate
      (fun _ hj => hj.cache_layout hlt_d0 _)
  have htf₀_dst :
      tf₀.locals[dstIdx]? =
        some ⟨mls_d0.value, some (translateTy dstDecl.ty body.layouts)⟩ := by
    dsimp only [tf₀, cacheFrameLocalLayout]
    rw [Array.getElem?_set_self hlt_d0, hmls_d0_eq]
  rcases evalEnumScalarOp_except_dst henv_valid hdst_decl henv_dst
      (m := m₀) rfl hfr₀_excl hop₀ s.memory.globals
      (some (translateTy fieldTy body.layouts)) with
    ⟨sc, msc, tf₁, hev_op, hval_op, hm_op, hrel_sc, hlaysz_sc, _, _, _, htf₁_eta,
      hsz₁, hdst_tf₁?, _, _, _⟩ |
    ⟨_, _, ha_op_ub, _⟩
  · -- Anneal fails `.ub` on inactive `.downcast`:
    have hbeq_f : Nat.beq v_act variantIdx = false := by
      cases hb : Nat.beq v_act variantIdx
      · rfl
      · rw [Nat.beq_eq] at hb; exact absurd hb (Ne.symm hne_var)
    have ha_ub : evalStmt s stmt body.localDecls body.layouts =
        MirStepNode.fail .ub := by
      unfold evalStmt; rw [hkind]; dsimp only
      rw [evalRvalue_use_nil_borrows_ok_lm2_3 hbor (by rw [hcaller]; exact hev_op) hval_op]
      dsimp only
      rw [hdst_slot]
      dsimp only [ensureNestedFieldShells, writeProjectedForLocal]
      rw [hvalid.placeTouchesUnion_downcast_field hdst_decl]
      dsimp only [writeProjectedValue]
      rw [hbeq_f]
    -- `lean-miri` writes `msc` into `dstIdx` and steps `.ok true`:
    rw [hslot_d0] at hdst_slot
    injection hdst_slot with hsl_eq; subst hsl_eq
    have hlt_dst1 : dstIdx < tf₁.locals.size := by
      rw [hsz₁]; dsimp [tf₀]; rw [cacheFrameLocalLayout_size]; exact hlt_d0
    have hdst_tf₁ :
        tf₁.locals[dstIdx]'hlt_dst1 =
          ⟨mls_d0.value, some (translateTy dstDecl.ty body.layouts)⟩ := by
      have hg := hdst_tf₁?
      rw [htf₀_dst, Array.getElem?_eq_getElem hlt_dst1] at hg
      exact Option.some.inj hg
    cases hloc_d0 with
    | base _ _ hn _ => rw [henv_dst] at hn; cases hn
    | enumInd tb_d vs_d _ _ mp _ henv_d _ hemr =>
      rw [henv_dst] at henv_d
      injection henv_d with hp_d; rcases hp_d with ⟨rfl, rfl⟩
      rcases hemr with
        ⟨allocId, borTag, baseAddr, localAlloc, words, _, _, _, hprov, _, _,
          hlive, hbase, hptr, hovf, hmut, _, hbs, hlen, hpmap, hmask,
          _, _, _, _, _⟩
      obtain ⟨_, u, hu_lt, hfidx, hget_u⟩ := hlive
      have hsz_f : fDesc.fieldLayout.size = translateSizeBytes sc.sizeBytes := by
        rw [← hfl_eq]; exact hlaysz_sc
      have hbnd_f :
          fDesc.offset.bytes.toNat +
            (translateSizeBytes sc.sizeBytes).bytes.toNat ≤
            localAlloc.allocation.byteSize.bytes.toNat := by
        rw [← hsz_f, hbs]
        exact hvf.fields_in_bounds fieldIdx hf_lt
      obtain ⟨alloc', _, hw, _, _, _, _, _, _, _, _, _⟩ :=
        alloc_writeScalar_at_offset_mask hrel_sc hlen hmut hpmap hmask hbnd_f
      have hovf_off : baseAddr.toNat + fDesc.offset.bytes.toNat < 2 ^ 64 := by
        have hpos_f : 0 < fDesc.fieldLayout.size.bytes.toNat := by
          rw [hsz_f]; exact translateSizeBytes_pos_lm2_3 hrel_sc.validBytes
        dsimp only [fDesc] at hpos_f ⊢
        have hb_enum := hvf.fields_in_bounds fieldIdx hf_lt
        omega
      let m₁ : AnnealStepState := { m with stack := ⟨#[tf₁]⟩ }
      have hwrite_eq :
          annealWriteImmediateLM2_2 (.scalar (.fromScalarInt msc)) destPlace m₁ =
          annealWriteProjectedLocalImmediate (.scalar (.fromScalarInt msc))
            destPlace .nil emptyLayoutTable m₁ := by
        unfold annealWriteImmediateLM2_2
        simp [get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
          stack_currentFrame?_singleton m₁.stack tf₁ rfl, destPlace]
      have hw_proj := annealWriteProjectedLocalImmediate_indirect_scalar_ok
        (localDecls := .nil) (layouts := emptyLayoutTable)
        (s := .fromScalarInt msc) (m := m₁) (tf := tf₁)
        (localId := dstIdx) (relOff := fDesc.offset)
        (iden := topFrame.localsIdentity)
        (fieldLay := translateTy fieldTy body.layouts)
        hsized_fty rfl hlt_dst1 hdst_tf₁ hprov hbase hptr hovf_off
        hu_lt hfidx hget_u hw
      let mach' := updateAllocMachine m.machine u allocId localAlloc.kind alloc'
      let m_end : AnnealStepState := ⟨⟨#[tf₁]⟩, mach'⟩
      have hm_ok :
          Miri.Interpreter.Step.evalStatement
            (annealStepHooksLM2_3 body.localDecls body.layouts) ()
            (translateStmt stmt) m = (m_end, .ok ()) := by
        rw [hm_eval]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hm_op]; dsimp only [m₀]
        rw [hwrite_eq]; dsimp only [destPlace]; rw [hw_proj]
      have hloc_tf₁ : tf₁.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by
        rw [htf₁_eta]; exact (hframe.cache_local_layout hdst_decl hlt_d0).location_eq
      exact ⟨ha_ub, _, miri_step_at_statement_ok _ hframes hframe.body_eq
        hframe.location_eq hbb hstmt hm_ok rfl hloc_tf₁⟩
  · cases hop₀ <;> exact absurd ha_op_ub hop_ok

/-- Uninitialized downcast-field write divergence
(`((_dst as variantIdx).fieldIdx : fieldTy) = use op` when `_dst` holds
`.uninit` — either `LocalRelLM2_3.enumUninitImm` or
`LocalRelLM2_3.enumUninitInd` — and `op` evaluates without UB):
* Anneal's value-tree `evalStmt` requires any projected assignment
  (`projs ≠ []`) to find `get? s.frame.locals dstIdx = some (.init oldVal)` and
  fails with `MirStepNode.fail .ub` when `_dst` is `.uninit`.
* Vendored `lean-miri`'s byte-offset `projectDowncast` + `projectField`
  computes `.local 0 dstIdx (some f.offset) ...`, and
  `writePlaceImmediateNoValidate` either forces a fresh `.Uninit` stack
  allocation (`enumUninitImm`, consuming 1 allocation from `allocBudget + 1`)
  or reuses the existing uninitialized stack allocation (`enumUninitInd`) and
  writes the scalar bytes into `[f.offset, f.offset + f.fieldLayout.size)`
  (`(m', .ok true)`).
Together with `step_downcast_field_write_simulation` (`.dead` and active
`.init`) and `step_downcast_field_write_inactive_divergence` (inactive `.init`),
this completes the exhaustive `LocalSlot` characterization for downcast-field
writes. -/
theorem step_downcast_field_write_uninit_divergence
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_3 body env (allocBudget + 1) s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    (henv_valid : ∀ t tb vs, env t = some (tb, vs) →
      ValidEnumLayout t body.layouts tb vs)
    {bb : BasicBlockData} {stmt : Statement}
    {dstIdx : Local} {dstDecl : LocalDecl}
    {vName : Option String} {variantIdx fieldIdx : Nat} {fieldTy : Ty}
    {op : MirAst.Operand}
    {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hkind : stmt.kind = .assign
      ⟨dstIdx, [.downcast vName variantIdx, .field fieldIdx fieldTy]⟩
      (.use op))
    (hdst_decl : get? body.localDecls dstIdx = some dstDecl)
    (henv_dst : env dstDecl.ty = some (tagBytes, variants))
    (hv_lt : variantIdx < variants.length)
    (hf_lt : fieldIdx < (variants[variantIdx]'hv_lt).length)
    (hfty_eq : fieldTy = ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).ty)
    (hop : ∀ tf, m.stack.frames = #[tf] →
      WellTypedEnumScalarOp body tf op fieldTy)
    (hop_ok :
      evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil ≠ .ub)
    (hdst_uninit : get? s.frame.locals dstIdx = some .uninit) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step
        (annealStepHooksLM2_3 body.localDecls body.layouts) () m =
      (m', .ok true) := by
  rcases hstate with
    ⟨topFrame, hframes, _, _, hframe, halloc, hcal, _, hbor, _, hcaller, _⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hvalid := henv_valid dstDecl.ty tagBytes variants henv_dst
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hvf_all⟩ := hvalid.table_entry
  have hvf := hvf_all variantIdx hv_lt
  let fDesc := (variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt
  obtain ⟨hprim_f, hfl_f⟩ := hvf.fields_prim fieldIdx hf_lt
  have hprim_fty : IsPrimScalarTy fieldTy := by rw [hfty_eq]; exact hprim_f
  have hfl_eq : (translateTy fieldTy body.layouts).layout = fDesc.fieldLayout := by
    rw [hfty_eq]; exact hfl_f.symm
  have hsized_fty : (translateTy fieldTy body.layouts).layout.isSized = true :=
    hprim_fty.isSized_lm2_3 body.layouts
  obtain ⟨slot_d0, mls_d0, hlt_d0, hslot_d0, hmls_d0_eq, hloc_d0⟩ :=
    hframe.lookup_local hdst_decl
  have hcache_d0 : ∀ l, (topFrame.locals[dstIdx]'hlt_d0).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d0_eq]; exact hloc_d0.layout_eq
  let tf₀ := cacheFrameLocalLayout topFrame dstIdx hlt_d0
    (translateTy dstDecl.ty body.layouts)
  let m₀ : AnnealStepState := { m with stack := ⟨#[tf₀]⟩ }
  have heval_dst := annealEvalPlaceLM2_3_downcast_field_ok
    (vName := vName) hframes hlt_d0 hdst_decl hcache_d0 hvalid hv_lt hf_lt hfty_eq
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 dstIdx (some fDesc.offset) topFrame.localsIdentity,
      translateTy fieldTy body.layouts⟩
  have hnot_mem :
      usesStructMemCopyDest
        ⟨.local 0 dstIdx (some fDesc.offset) topFrame.localsIdentity,
          translateTy fieldTy body.layouts⟩ = false :=
    usesStructMemCopyDest_false_of_primScalar destPlace rfl hprim_fty
  have hm_eval :
      Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_3 body.localDecls body.layouts) ()
        (translateStmt stmt) m =
      Miri.Interpreter.runRvalue
        ((annealEvalOperandLM2_3 body.localDecls body.layouts
            (translateOperand op) (some (translateTy fieldTy body.layouts)) >>=
          annealReadImmediateLM2_2) >>=
          fun imm => annealWriteImmediateLM2_2 imm.imm destPlace)
        m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    rw [hkind]
    have hlm23_asgn :
        lm23Assign body.localDecls body.layouts
          ⟨dstIdx, #[.Downcast vName variantIdx, .Field fieldIdx (encodeTyId fieldTy)]⟩
          (.Use (translateOperand op) .No) = true := rfl
    dsimp only [translateStmtKind, translatePlace, translateProjectionElem,
      List.map, List.toArray, translateRvalue, annealStepHooksLM2_3]
    change (if lm23Assign body.localDecls body.layouts
        ⟨dstIdx, #[.Downcast vName variantIdx, .Field fieldIdx (encodeTyId fieldTy)]⟩
        (.Use (translateOperand op) .No) then _ else _) = _
    rw [hlm23_asgn]
    simp only [↓reduceIte]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooksLM2_3
    dsimp only [annealRvalueHooksLM2_2]
    rw [EStateM.bind_eq_ok heval_dst]
    dsimp only [destPlace]
    exact bind_copyOp_eq_of_not_usesStructMemCopyDest hnot_mem m₀
  have hfr₀_excl : FrameRelLM2_3Except body env dstIdx m.machine s.frame tf₀ :=
    FrameRelLM2_3Except.of_frameRel (hframe.cache_local_layout hdst_decl hlt_d0)
  have hop₀ : WellTypedEnumScalarOp body tf₀ op fieldTy :=
    (hop topFrame hframes).mono_immediate
      (fun _ hj => hj.cache_layout hlt_d0 _)
  have htf₀_dst :
      tf₀.locals[dstIdx]? =
        some ⟨mls_d0.value, some (translateTy dstDecl.ty body.layouts)⟩ := by
    dsimp only [tf₀, cacheFrameLocalLayout]
    rw [Array.getElem?_set_self hlt_d0, hmls_d0_eq]
  rcases evalEnumScalarOp_except_dst henv_valid hdst_decl henv_dst
      (m := m₀) rfl hfr₀_excl hop₀ s.memory.globals
      (some (translateTy fieldTy body.layouts)) with
    ⟨sc, msc, tf₁, hev_op, hval_op, hm_op, hrel_sc, hlaysz_sc, _, _, _, htf₁_eta,
      hsz₁, hdst_tf₁?, _, _, _⟩ |
    ⟨_, _, ha_op_ub, _⟩
  · -- Anneal fails `.ub` on `.uninit` `_dst` with non-empty projection:
    have ha_ub : evalStmt s stmt body.localDecls body.layouts =
        MirStepNode.fail .ub := by
      unfold evalStmt; rw [hkind]; dsimp only
      rw [evalRvalue_use_nil_borrows_ok_lm2_3 hbor (by rw [hcaller]; exact hev_op) hval_op]
      dsimp only
      rw [hdst_uninit]
      dsimp only [uninitFieldWriteShell?]
    rw [hslot_d0] at hdst_uninit
    injection hdst_uninit with hsl_eq; subst hsl_eq
    have hlt_dst1 : dstIdx < tf₁.locals.size := by
      rw [hsz₁]; dsimp [tf₀]; rw [cacheFrameLocalLayout_size]; exact hlt_d0
    have hdst_tf₁ :
        tf₁.locals[dstIdx]'hlt_dst1 =
          ⟨mls_d0.value, some (translateTy dstDecl.ty body.layouts)⟩ := by
      have hg := hdst_tf₁?
      rw [htf₀_dst, Array.getElem?_eq_getElem hlt_dst1] at hg
      exact Option.some.inj hg
    let m₁ : AnnealStepState := { m with stack := ⟨#[tf₁]⟩ }
    have hwrite_eq :
        annealWriteImmediateLM2_2 (.scalar (.fromScalarInt msc)) destPlace m₁ =
        annealWriteProjectedLocalImmediate (.scalar (.fromScalarInt msc))
          destPlace .nil emptyLayoutTable m₁ := by
      unfold annealWriteImmediateLM2_2
      simp [get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
        stack_currentFrame?_singleton m₁.stack tf₁ rfl, destPlace]
    have hsz_f : fDesc.fieldLayout.size = translateSizeBytes sc.sizeBytes := by
      rw [← hfl_eq]; exact hlaysz_sc
    have hloc_tf₁ : tf₁.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by
      rw [htf₁_eta]; exact (hframe.cache_local_layout hdst_decl hlt_d0).location_eq
    cases hloc_d0 with
    | base _ _ hn _ => rw [henv_dst] at hn; cases hn
    | enumUninitImm _ _ _ _ _ _ =>
      obtain ⟨rawAlloc, htry, hbs0, hlen0, hmut0, hpmap0, hmask0⟩ :=
        tryNew_uninit_of_pow2_le_29 (translateTy dstDecl.ty body.layouts).layout.size
          (translateTy dstDecl.ty body.layouts).layout.align.abi hvalid.align_pow2_le
      obtain ⟨mem', newId, hres, _, hlive_eq, hfresh_old, _, hovf_all⟩ :=
        halloc.of_succ.reserve_step
      have hfresh : mem'.live.any (fun entry => entry.1 == newId) = false := by
        rw [hlive_eq]; exact hfresh_old
      let a0 := rawAlloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree)
      have hmask_a0 : InitMaskWordRel a0.initializationMask a0.byteSize
          (initWordsFalse (translateTy dstDecl.ty body.layouts).layout.size) := by
        dsimp [a0]; rw [hmask0, hbs0]; exact initMaskWordRel_new_false
      have hlen_a0 : a0.len = a0.byteSize.bytes.toNat := by
        dsimp [a0]; rw [hlen0, hbs0]
      have hbnd_f :
          fDesc.offset.bytes.toNat +
            (translateSizeBytes sc.sizeBytes).bytes.toNat ≤
            a0.byteSize.bytes.toNat := by
        dsimp [a0]; rw [← hsz_f, hbs0]
        exact hvf.fields_in_bounds fieldIdx hf_lt
      obtain ⟨alloc', _, hw, _, _, _, _, _, _, _, _, _⟩ :=
        alloc_writeScalar_at_offset_mask hrel_sc hlen_a0 hmut0 hpmap0 hmask_a0 hbnd_f
      have hovf_off : (annealStackBaseAddr newId).toNat + fDesc.offset.bytes.toNat < 2 ^ 64 := by
        have hovf_enum := hovf_all _ hvalid.size_lt_4gib
        have hpos_f : 0 < fDesc.fieldLayout.size.bytes.toNat := by
          rw [hsz_f]; exact translateSizeBytes_pos_lm2_3 hrel_sc.validBytes
        dsimp only [fDesc] at hpos_f ⊢
        have hb_enum := hvf.fields_in_bounds fieldIdx hf_lt
        omega
      have hw_proj := annealWriteProjectedLocalImmediate_immediate_scalar_ok
        (localDecls := .nil) (layouts := emptyLayoutTable)
        (s := .fromScalarInt msc) (m := m₁) (tf := tf₁)
        (localId := dstIdx) (relOff := fDesc.offset)
        (iden := topFrame.localsIdentity)
        (fieldLay := translateTy fieldTy body.layouts)
        (wholeLay := translateTy dstDecl.ty body.layouts)
        (oldImm := .uninit) (rawAlloc := rawAlloc) (mem' := mem') (id := newId)
        (alloc_init := a0) (alloc_final := alloc')
        hsized_fty hvalid.isSized_true rfl hlt_dst1 hdst_tf₁ htry hres hfresh
        rfl hovf_off hw
      let tf_end :=
        { tf₁ with
          locals := tf₁.locals.set dstIdx
            ⟨.live (.indirect (stackAllocPlace newId)),
              some (translateTy dstDecl.ty body.layouts)⟩ hlt_dst1 }
      let m_end : AnnealStepState :=
        ⟨⟨#[tf_end]⟩, stackAllocMachine m.machine mem' newId alloc'⟩
      have hm_ok :
          Miri.Interpreter.Step.evalStatement
            (annealStepHooksLM2_3 body.localDecls body.layouts) ()
            (translateStmt stmt) m = (m_end, .ok ()) := by
        rw [hm_eval]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hm_op]; dsimp only [m₀]
        rw [hwrite_eq]; dsimp only [destPlace]; rw [hw_proj]
      exact ⟨ha_ub, _, miri_step_at_statement_ok _ hframes hframe.body_eq
        hframe.location_eq hbb hstmt hm_ok rfl hloc_tf₁⟩
    | enumUninitInd tb_d vs_d mp _ henv_d _ humpr =>
      rw [henv_dst] at henv_d
      injection henv_d with hp_d; rcases hp_d with ⟨rfl, rfl⟩
      rcases humpr with
        ⟨allocId, _, baseAddr, localAlloc, _, hprov, _, _,
          hlive, hbase, hptr, hovf, hmut, _, hbs, hlen, hpmap, hmask_u⟩
      obtain ⟨_, u, hu_lt, hfidx, hget_u⟩ := hlive
      have hmask₀ : InitMaskWordRel localAlloc.allocation.initializationMask
          localAlloc.allocation.byteSize
          (initWordsFalse (translateTy dstDecl.ty body.layouts).layout.size) := by
        rw [hmask_u, hbs]; exact initMaskWordRel_new_false
      have hbnd_f :
          fDesc.offset.bytes.toNat +
            (translateSizeBytes sc.sizeBytes).bytes.toNat ≤
            localAlloc.allocation.byteSize.bytes.toNat := by
        rw [← hsz_f, hbs]
        exact hvf.fields_in_bounds fieldIdx hf_lt
      obtain ⟨alloc', _, hw, _, _, _, _, _, _, _, _, _⟩ :=
        alloc_writeScalar_at_offset_mask hrel_sc hlen hmut hpmap hmask₀ hbnd_f
      have hovf_off : baseAddr.toNat + fDesc.offset.bytes.toNat < 2 ^ 64 := by
        have hpos_f : 0 < fDesc.fieldLayout.size.bytes.toNat := by
          rw [hsz_f]; exact translateSizeBytes_pos_lm2_3 hrel_sc.validBytes
        dsimp only [fDesc] at hpos_f ⊢
        have hb_enum := hvf.fields_in_bounds fieldIdx hf_lt
        omega
      have hw_proj := annealWriteProjectedLocalImmediate_indirect_scalar_ok
        (localDecls := .nil) (layouts := emptyLayoutTable)
        (s := .fromScalarInt msc) (m := m₁) (tf := tf₁)
        (localId := dstIdx) (relOff := fDesc.offset)
        (iden := topFrame.localsIdentity)
        (fieldLay := translateTy fieldTy body.layouts)
        hsized_fty rfl hlt_dst1 hdst_tf₁ hprov hbase hptr hovf_off
        hu_lt hfidx hget_u hw
      let mach' := updateAllocMachine m.machine u allocId localAlloc.kind alloc'
      let m_end : AnnealStepState := ⟨⟨#[tf₁]⟩, mach'⟩
      have hm_ok :
          Miri.Interpreter.Step.evalStatement
            (annealStepHooksLM2_3 body.localDecls body.layouts) ()
            (translateStmt stmt) m = (m_end, .ok ()) := by
        rw [hm_eval]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hm_op]; dsimp only [m₀]
        rw [hwrite_eq]; dsimp only [destPlace]; rw [hw_proj]
      exact ⟨ha_ub, _, miri_step_at_statement_ok _ hframes hframe.body_eq
        hframe.location_eq hbb hstmt hm_ok rfl hloc_tf₁⟩
  · cases hop₀ <;> exact absurd ha_op_ub hop_ok

/-- Whole-enum self-move simulation (`_idx = Rvalue.Use(move _idx)` on a
multi-variant enum local `idx`):
* When `idx` is `.dead`, both machines diagnose `"read of dead local"` UB.
* When `idx` is `.uninit` and immediate (`IsImmediateStepLocal m idx`), both
  machines diagnose `"read of uninitialized local"` UB.
* When `idx` holds `.init (.aggregate v_act fieldVals)`, `annealEvalOperand`
  reads `⟨.indirect srcMp, wholeLay⟩` and resets `tf₁.locals[idx]` to
  `.live (.immediate .uninit)` (`deinitFrameLocal`) BEFORE
  `annealStructMemCopyOp` runs; `annealStructMemCopyOp` then forces a fresh
  stack allocation `newId` (`newId ≠ srcId`, consuming 1 allocation from
  `allocBudget + 1`) and copies `srcLocal.allocation` (including raw bytes and
  `InitMask`) into `newId`, so both Anneal and `lean-miri` step in lockstep
  (`StepRelLM2_3.step`)! -/
theorem step_enum_self_move_simulation
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_3 body env (allocBudget + 1) s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    (henv_valid : ∀ t tb vs, env t = some (tb, vs) →
      ValidEnumLayout t body.layouts tb vs)
    {bb : BasicBlockData} {stmt : Statement}
    {idx : Local} {decl : LocalDecl}
    {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hkind : stmt.kind = .assign ⟨idx, .nil⟩ (.use (.move ⟨idx, .nil⟩)))
    (hdecl : get? body.localDecls idx = some decl)
    (henv_idx : env decl.ty = some (tagBytes, variants))
    (huninit_imm :
      get? s.frame.locals idx = some .uninit →
        IsImmediateStepLocal m idx) :
    let mRes :=
      Miri.Interpreter.Step.step
        (annealStepHooksLM2_3 body.localDecls body.layouts) () m
    StepRelLM2_3 body env allocBudget m (stepMirFn body s) mRes ∧
    ((∀ msg, mRes.2 ≠ .error (.undefinedBehavior msg)) →
      (∀ enumId b,
        EnumLocalByteUninit m enumId b →
        EnumLocalByteUninit mRes.1 enumId b) ∧
      (∀ j, j ≠ idx → IsImmediateStepLocal m j →
        IsImmediateStepLocal mRes.1 j)) := by
  intro mRes
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe, halloc,
      hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hvalid := henv_valid decl.ty tagBytes variants henv_idx
  let wholeLay := translateTy decl.ty body.layouts
  obtain ⟨slot0, mls0, hlt0, hslot0, hmls0_eq, hloc0⟩ :=
    hframe.lookup_local hdecl
  have hcache0 : ∀ l, (topFrame.locals[idx]'hlt0).layout = some l →
      l = wholeLay := by
    rw [hmls0_eq]; exact hloc0.layout_eq
  let tf₀ := cacheFrameLocalLayout topFrame idx hlt0 wholeLay
  let m₀ : AnnealStepState := { m with stack := ⟨#[tf₀]⟩ }
  have heval_dst :
      annealEvalPlace body.localDecls body.layouts ⟨idx, #[]⟩ m =
      .ok ⟨.local 0 idx none topFrame.localsIdentity, wholeLay⟩ m₀ :=
    annealEvalPlace_unprojected hframes hlt0 hdecl hcache0
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 idx none topFrame.localsIdentity, wholeLay⟩
  have huses_mem :
      usesStructMemCopyDest ⟨.local 0 idx none topFrame.localsIdentity, wholeLay⟩ = true :=
    usesStructMemCopyDest_true_of_validEnum destPlace rfl hvalid
  have hm_eval :
      Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_3 body.localDecls body.layouts) ()
        (translateStmt stmt) m =
      Miri.Interpreter.runRvalue
        (annealEvalOperand body.localDecls body.layouts (.Move ⟨idx, #[]⟩)
            (some wholeLay) >>=
          fun src =>
            annealStructMemCopyOp body.localDecls body.layouts src destPlace)
        m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    rw [hkind]
    have hlm23_asgn :
        lm23Assign body.localDecls body.layouts ⟨idx, #[]⟩
          (.Use (.Move ⟨idx, #[]⟩) .No) = false := rfl
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
      translateRvalue, translateOperand, annealStepHooksLM2_3]
    change (if lm23Assign body.localDecls body.layouts ⟨idx, #[]⟩
        (.Use (.Move ⟨idx, #[]⟩) .No) then _ else _) = _
    rw [hlm23_asgn]
    simp only [Bool.false_eq_true, ↓reduceIte, annealStepHooksLM2_2]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooksLM2_2
    rw [EStateM.bind_eq_ok heval_dst]
    dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt, destPlace]
    simp only [huses_mem, ↓reduceIte]
  have hlt_tf₀ : idx < tf₀.locals.size := by
    dsimp [tf₀]; rw [cacheFrameLocalLayout_size]; exact hlt0
  have htf₀_self : tf₀.locals[idx]'hlt_tf₀ = ⟨mls0.value, some wholeLay⟩ := by
    have h? : tf₀.locals[idx]? = some ⟨mls0.value, some wholeLay⟩ := by
      dsimp only [tf₀, cacheFrameLocalLayout]
      rw [Array.getElem?_set_self hlt0, hmls0_eq]
    rw [Array.getElem?_eq_getElem hlt_tf₀] at h?
    exact Option.some.inj h?
  have hcache_tf₀ : ∀ l, (some wholeLay : Option Miri.Interpreter.LocalLayout) = some l →
      l = wholeLay := fun _ h => (Option.some.inj h).symm
  have hlt_af0 : idx < s.frame.locals.length := by
    unfold get? at hslot0
    exact (List.getElem?_eq_some_iff.mp hslot0).1
  cases hloc0 with
  | base _ _ hnone _ => rw [henv_idx] at hnone; cases hnone
  | enumDead _ _ _ _ _ _ =>
    have ha_ub : evalStmt s stmt body.localDecls body.layouts =
        MirStepNode.fail .ub := by
      unfold evalStmt; rw [hkind]; simp [evalRvalue, evalOperand, hslot0]
    obtain ⟨m_err, hm_op_err⟩ :
        ∃ m_err,
          annealEvalOperand body.localDecls body.layouts (.Move ⟨idx, #[]⟩)
            (some wholeLay) m₀ =
          .error (.undefinedBehavior "read of dead local") m_err :=
      ⟨_, annealEvalOperand_move_dead (known := some wholeLay)
        (m := m₀) rfl hlt_tf₀ hdecl htf₀_self hcache_tf₀⟩
    have hm_ub :
        Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_3 body.localDecls body.layouts) ()
          (translateStmt stmt) m =
        (m_err, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_eval]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_error hm_op_err]
    dsimp only [mRes]
    rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq
      hframe.location_eq hbb hstmt hm_ub]
    exact ⟨.ub _ _, fun hno => False.elim (hno _ rfl)⟩
  | enumUninitInd _ _ srcMp_u c_s _ _ _ =>
    have himm_s := huninit_imm hslot0 topFrame hframes
    have hmls_top : topFrame.locals[idx]? =
        some ⟨.live (.indirect srcMp_u), c_s⟩ := by
      rw [Array.getElem?_eq_getElem hlt0, hmls0_eq]
    exact False.elim (himm_s _ hmls_top srcMp_u rfl)
  | enumUninitImm _ _ _ _ _ _ =>
    have ha_ub : evalStmt s stmt body.localDecls body.layouts =
        MirStepNode.fail .ub := by
      unfold evalStmt; rw [hkind]; simp [evalRvalue, evalOperand, hslot0]
    obtain ⟨m_err, hm_op_ok⟩ :
        ∃ m_err,
          annealEvalOperand body.localDecls body.layouts (.Move ⟨idx, #[]⟩)
            (some wholeLay) m₀ =
          .ok ⟨.immediate .uninit, wholeLay⟩ m_err :=
      ⟨_, annealEvalOperand_move_live (known := some wholeLay)
        (m := m₀) rfl hlt_tf₀ hdecl htf₀_self hcache_tf₀⟩
    have hm_ub :
        Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_3 body.localDecls body.layouts) ()
          (translateStmt stmt) m =
        (m_err, .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_eval]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hm_op_ok]; rfl
    dsimp only [mRes]
    rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq
      hframe.location_eq hbb hstmt hm_ub]
    exact ⟨.ub _ _, fun hno => False.elim (hno _ rfl)⟩
  | enumInd tb_s vs_s v_act fieldVals srcMp c_s henv_s _ hemr_s =>
    rw [henv_idx] at henv_s
    injection henv_s with hp_s; rcases hp_s with ⟨rfl, rfl⟩
    have hemr_copy := hemr_s
    rcases hemr_s with
      ⟨srcId, borTag_s, srcBase, srcLocal, _, _, _, _, hprov_s, _, _, hlive_s,
        hbase_s, hptr_s, _, _, _, hbs_s, _, _, _, _, _, _, _, _⟩
    let rootVal : Value := .aggregate v_act fieldVals
    let tf_c := cacheFrameLocalLayout tf₀ idx hlt_tf₀ wholeLay
    have hlt_c : idx < tf_c.locals.size := by
      dsimp [tf_c]; rw [cacheFrameLocalLayout_size]; exact hlt_tf₀
    let tf₁ := deinitFrameLocal tf_c idx hlt_c
    have hm_op := annealEvalOperand_move_live (known := some wholeLay)
      (m := m₀) rfl hlt_tf₀ hdecl htf₀_self hcache_tf₀
    have hc_some : ∀ l ∈ (tf_c.locals[idx]'hlt_c).layout, l = wholeLay := by
      intro l hl
      have hget_c : tf_c.locals[idx]? = some (tf_c.locals[idx]'hlt_c) :=
        Array.getElem?_eq_getElem hlt_c
      have hc_eq : tf_c.locals[idx]? =
          some ⟨.live (.indirect srcMp), some wholeLay⟩ := by
        dsimp only [tf_c, cacheFrameLocalLayout]
        rw [Array.getElem?_set_self hlt_tf₀, htf₀_self]
      rw [hget_c] at hc_eq; injection hc_eq with heq_ls
      rw [heq_ls] at hl
      exact (Option.some.inj (Option.mem_def.mp hl)).symm
    let locals₁ := s.frame.locals.set idx .uninit
    have hfr₁ : FrameRelLM2_3 body env m.machine
        { s.frame with locals := locals₁ } tf₁ :=
      ((hframe.cache_local_layout hdecl hlt0).cache_local_layout hdecl hlt_tf₀).update_local
        hdecl (set?_eq_some_set hlt_af0 .uninit) hlt_c
        (.enumUninitImm tagBytes variants _ henv_idx hvalid hc_some)
    have hdisj₁ : MemoryAllocDisjoint tf₁ :=
      MemoryAllocDisjoint_deinitFrameLocal_lm2_3
        (MemoryAllocDisjoint_cacheFrameLocalLayout
          (MemoryAllocDisjoint_cacheFrameLocalLayout hdisj hlt0 _) hlt_tf₀ _) hlt_c
    have hlt_dst1 : idx < tf₁.locals.size := by
      dsimp [tf₁, deinitFrameLocal]; rw [Array.size_set]; exact hlt_c
    have hdst_tf₁ : tf₁.locals[idx]'hlt_dst1 = ⟨.live (.immediate .uninit), some wholeLay⟩ := by
      have h? : tf₁.locals[idx]? = some ⟨.live (.immediate .uninit), some wholeLay⟩ := by
        dsimp only [tf₁, deinitFrameLocal]
        rw [Array.getElem?_set_self hlt_c]
        have hc_eq : tf_c.locals[idx]? = some ⟨.live (.indirect srcMp), some wholeLay⟩ := by
          dsimp only [tf_c, cacheFrameLocalLayout]
          rw [Array.getElem?_set_self hlt_tf₀, htf₀_self]
        rw [Array.getElem?_eq_getElem hlt_c] at hc_eq
        rw [Option.some.inj hc_eq]
      rw [Array.getElem?_eq_getElem hlt_dst1] at h?
      exact Option.some.inj h?
    have hlt_af₁ : idx < locals₁.length := by
      dsimp [locals₁]; rw [List.length_set]; exact hlt_af0
    have hfr₁_excl : FrameRelLM2_3Except body env idx m.machine
        { s.frame with locals := locals₁ } tf₁ :=
      FrameRelLM2_3Except.of_frameRel hfr₁
    obtain ⟨rawAlloc, htry, hbs0, _, hmut0, _, _⟩ :=
      tryNew_uninit_of_pow2_le_29 wholeLay.layout.size
        wholeLay.layout.align.abi hvalid.align_pow2_le
    obtain ⟨mem', newId, hres, _, hlive_eq, hfresh_old, hwm_next, hovf_all⟩ :=
      (halloc.of_succ).reserve_step
    have hfresh : mem'.live.any (fun entry => entry.1 == newId) = false := by
      rw [hlive_eq]; exact hfresh_old
    have hcp_ok := annealStructMemCopyOp_uninitImm_ok
      (ld := body.localDecls) (ly := body.layouts)
      (srcLay := wholeLay) (iden := topFrame.localsIdentity)
      (m := { m with stack := ⟨#[tf₁]⟩ })
      rfl hlt_dst1 hdst_tf₁ hvalid.isSized_true htry hbs0 hmut0 hres hfresh
      hprov_s hbase_s hptr_s hlive_s hbs_s
    have hemr_new : EnumMemRel
        (stackAllocMachine m.machine mem' newId
          (copyWholeStructAllocation srcLocal.allocation none))
        decl.ty body.layouts tagBytes variants v_act fieldVals
        (stackAllocPlace newId) :=
      hemr_copy.of_copy_fresh hprov_s hlive_s hfresh
        (hovf_all _ hvalid.size_lt_4gib)
    let tf_end :=
      { tf₁ with
        locals := tf₁.locals.set idx
          ⟨.live (.indirect (stackAllocPlace newId)), some wholeLay⟩ hlt_dst1 }
    let m_end : AnnealStepState :=
      ⟨⟨#[tf_end]⟩,
        stackAllocMachine m.machine mem' newId
          (copyWholeStructAllocation srcLocal.allocation none)⟩
    have hm_ok :
        Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_3 body.localDecls body.layouts) ()
          (translateStmt stmt) m = (m_end, .ok ()) := by
      rw [hm_eval]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hm_op]; dsimp only [m₀]; rw [hcp_ok]
    have ha_ok :
        evalStmt s stmt body.localDecls body.layouts =
        MirStepNode.step (advanceStmt s (locals₁.set idx (.init rootVal)) s.memory) := by
      unfold evalStmt; rw [hkind]; dsimp only
      rw [evalRvalue_use_nil_borrows_lm2_3 _ _ _ hbor, hcaller]
      have hev_op :
          evalOperand s.frame.locals (.move ⟨idx, .nil⟩) .nil s.memory.globals
            body.layouts .nil body.localDecls = .ok rootVal locals₁ := by
        unfold evalOperand; dsimp only; rw [hslot0]; dsimp only
        rw [set?_eq_some_set hlt_af0 .uninit]
      rw [hev_op]; dsimp only
      rw [hvalid.validateLoadedValue_unproj hdecl (Or.inr rfl)]; dsimp only
      have hloc₁_get : get? locals₁ idx = some .uninit := by
        unfold get?; dsimp [locals₁]; exact List.getElem?_set_self hlt_af0
      rw [hprot, hbor, hloc₁_get]; dsimp only [invalidateConflictingBorrows]
      rw [set?_eq_some_set hlt_af₁ (.init rootVal)]
      apply congrArg (fun mem =>
        MirStepNode.step (advanceStmt s (locals₁.set idx (.init rootVal)) mem))
      rcases hm_s : s.memory with ⟨_, _, bor, _, _, _, _, prot, _, _⟩
      rw [hm_s] at hbor hprot; dsimp only at hbor hprot; subst hbor hprot; rfl
    have hfr_end : FrameRelLM2_3 body env m_end.machine
        { s.frame with locals := locals₁.set idx (.init rootVal) } tf_end := by
      have hex := hfr₁_excl.of_stackAlloc_set_excl
        (alloc := copyWholeStructAllocation srcLocal.allocation none)
        (hlt := hlt_dst1) hres
        ⟨.live (.indirect (stackAllocPlace newId)), some wholeLay⟩
      exact hex.finish_dst hdecl (set?_eq_some_set hlt_af₁ (.init rootVal))
        (Array.getElem?_set_self hlt_dst1)
        (.enumInd tagBytes variants v_act fieldVals (stackAllocPlace newId)
          (some wholeLay) henv_idx
          (fun _ hl => (Option.some.inj (Option.mem_def.mp hl)).symm)
          hemr_new)
    dsimp only [mRes]
    rw [ha_ok,
      miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq
        hbb hstmt hm_ok rfl hfr_end.location_eq]
    refine ⟨.step _ _ ?_, fun _ => ⟨?_, ?_⟩⟩
    · exact .mk _ rfl hretCont ⟨retLay, hretPlace⟩
        hfr_end.step_pc (Or.inr (hwm_next _))
        hcal hstack hbor hprot hcaller
        (MemoryAllocDisjoint_set_fresh_stackAlloc_lm2_3 hfr₁_excl hdisj₁
          hfresh_old hlt_dst1)
    · intro enumId b hu_e tf_s mp_e c_e id_e bt_e la_e hf_s hloc_e hprov_e hfind_e
      injection hf_s with ha_s; injection ha_s with ht_s; subst ht_s
      dsimp only [tf_end] at hloc_e
      by_cases heq_id : idx = enumId
      · subst heq_id
        rw [Array.getElem?_set_self hlt_dst1] at hloc_e
        injection hloc_e with hls_eq
        injection hls_eq with hv_eq _
        injection hv_eq with hop_eq
        injection hop_eq with hmp_eq
        subst hmp_eq
        change some (Miri.Memory.Provenance.concrete newId Miri.Memory.BorTag.one) =
          some (Miri.Memory.Provenance.concrete id_e bt_e) at hprov_e
        injection hprov_e with hp_eq; injection hp_eq with hid_eq _; subst hid_eq
        have hself := (LiveAllocEntry.of_push_fresh_self
          (la := ⟨.stack, copyWholeStructAllocation srcLocal.allocation none⟩)
          hfresh).1
        dsimp only [m_end, stackAllocMachine] at hfind_e
        rw [hself] at hfind_e
        injection hfind_e with hpair_eq
        have hla_eq : la_e =
            ⟨.stack, copyWholeStructAllocation srcLocal.allocation none⟩ :=
          (Prod.mk.inj hpair_eq).2.symm
        subst hla_eq
        obtain ⟨_, _, _, _, hmask_eq, _⟩ :=
          copyWholeStructAllocation_props srcLocal.allocation none
        dsimp only
        rw [hmask_eq]
        have hsrc_top? : topFrame.locals[idx]? =
            some ⟨.live (.indirect srcMp), c_s⟩ := by
          rw [Array.getElem?_eq_getElem hlt0, hmls0_eq]
        exact hu_e topFrame srcMp c_s srcId borTag_s srcLocal
          hframes hsrc_top? hprov_s hlive_s.1
      · rw [Array.getElem?_set_ne _ heq_id] at hloc_e
        dsimp only [tf₁, deinitFrameLocal] at hloc_e
        rw [Array.getElem?_set_ne _ heq_id] at hloc_e
        dsimp only [tf_c, cacheFrameLocalLayout] at hloc_e
        rw [Array.getElem?_set_ne _ heq_id] at hloc_e
        dsimp only [tf₀, cacheFrameLocalLayout] at hloc_e
        rw [Array.getElem?_set_ne _ heq_id] at hloc_e
        have hid_ne : id_e ≠ newId := by
          intro rfl
          obtain ⟨hlt_k, _⟩ := Array.getElem?_eq_some_iff.mp hloc_e
          have hlt_dk : enumId < length body.localDecls :=
            hframe.mf_locals_size ▸ hlt_k
          have hlt_afk : enumId < length s.frame.locals :=
            hframe.af_locals_len.symm ▸ hlt_dk
          unfold length at hlt_dk hlt_afk
          have hloc_k := hframe.locals_rel enumId _ _ _
            (by unfold get?; exact List.getElem?_eq_getElem hlt_dk)
            (by unfold get?; exact List.getElem?_eq_getElem hlt_afk)
            hloc_e
          obtain ⟨id_k, hid_k, hany_k⟩ := hloc_k.allocLive mp_e rfl
          rw [hprov_e] at hid_k
          injection hid_k with hid_eq; subst hid_eq
          rw [hfresh_old] at hany_k; cases hany_k
        let newEntry : AnnealLocalAlloc :=
          { kind := .stack
            allocation := copyWholeStructAllocation srcLocal.allocation none }
        have hfind_old :
            m.machine.memory.live.find? (fun (k0, _) => k0 == id_e) =
              some (id_e, la_e) := by
          dsimp only [m_end, stackAllocMachine] at hfind_e
          rw [hlive_eq, Array.find?_push] at hfind_e
          have hbeq_f : ((newId, newEntry).1 == id_e) = false :=
            beq_eq_false_iff_ne.mpr (Ne.symm hid_ne)
          dsimp at hbeq_f
          simp [hbeq_f] at hfind_e
          exact hfind_e
        exact hu_e topFrame mp_e c_e id_e bt_e la_e
          hframes hloc_e hprov_e hfind_old
    · intro j hne_ji hj tf_s hf_s mls_j hget_j
      injection hf_s with ha_s; injection ha_s with ht_s; subst ht_s
      dsimp only [tf_end] at hget_j
      rw [Array.getElem?_set_ne _ (Ne.symm hne_ji)] at hget_j
      dsimp only [tf₁, deinitFrameLocal] at hget_j
      rw [Array.getElem?_set_ne _ (Ne.symm hne_ji)] at hget_j
      dsimp only [tf_c, cacheFrameLocalLayout] at hget_j
      rw [Array.getElem?_set_ne _ (Ne.symm hne_ji)] at hget_j
      dsimp only [tf₀, cacheFrameLocalLayout] at hget_j
      rw [Array.getElem?_set_ne _ (Ne.symm hne_ji)] at hget_j
      exact hj topFrame hframes mls_j hget_j

/-! ## 11. Whole-Enum Self-Copy and Indirect-Uninit Copy/Move Boundaries -/

private def lm23RangeEntries {α : Type} (values : Array (Miri.ABI.Size × α))
    (start finish : Miri.ABI.Size) : Array (Miri.ABI.Size × α) :=
  values.filter fun entry =>
    start.bytes ≤ entry.1.bytes && entry.1.bytes < finish.bytes

private def lm23AdjustedStart (range : Miri.Memory.AllocRange)
    (pointerSize : Miri.ABI.Size) :
    Except Miri.Memory.ProvenanceMapError Miri.ABI.Size :=
  if pointerSize.bytes == 0 then .error .pointerSizeZero
  else .ok (Miri.ABI.Size.ofBytes
    (UInt64.ofNat (range.start.bytes.toNat - (pointerSize.bytes.toNat - 1))))

private def lm23RangeEnd (range : Miri.Memory.AllocRange) :
    Except Miri.Memory.ProvenanceMapError Miri.ABI.Size :=
  range.endExclusive.mapError .memory

private def lm23RangePtrs {Prov : Type} (self : Miri.Memory.ProvenanceMap Prov)
    (range : Miri.Memory.AllocRange) (pointerSize : Miri.ABI.Size) :
    Except Miri.Memory.ProvenanceMapError (Array (Miri.ABI.Size × Prov)) := do
  let start ← lm23AdjustedStart range pointerSize
  let finish ← lm23RangeEnd range
  return lm23RangeEntries self.ptrs start finish

private def lm23RangeBytes {Prov : Type} (self : Miri.Memory.ProvenanceMap Prov)
    (range : Miri.Memory.AllocRange) :
    Except Miri.Memory.ProvenanceMapError
      (Array (Miri.ABI.Size × Miri.Memory.PointerFrag Prov)) := do
  let finish ← lm23RangeEnd range
  return lm23RangeEntries (self.byteFragments.getD #[]) range.start finish

private def lm23SubtractSize (left right : Miri.ABI.Size) :
    Except Miri.Memory.ProvenanceMapError Miri.ABI.Size :=
  (Miri.ABI.Size.sub left right).mapError
    (Miri.Memory.ProvenanceMapError.memory ∘ Miri.Memory.MemoryError.sizeError)

private def lm23PtrFragments {Prov : Type} (inRange : Miri.ABI.Size → Bool)
    (position : Miri.ABI.Size) (prov : Prov) (data : Array UInt8)
    (pointerSize : Miri.ABI.Size) :
    Except Miri.Memory.ProvenanceMapError
      (Array (Miri.ABI.Size × Miri.Memory.PointerFrag Prov)) := do
  if pointerSize.bytes > 8 then
    throw (.pointerSizeExceedsFragmentStorage pointerSize.bytes)
  let _finish ← (Miri.ABI.Size.add position pointerSize).mapError
    (Miri.Memory.ProvenanceMapError.memory ∘ Miri.Memory.MemoryError.sizeError)
  if h : position.bytes.toNat + pointerSize.bytes.toNat ≤ data.size then
    let bytes : Vector UInt8 8 := Vector.ofFn fun index =>
      if hi : index.val < pointerSize.bytes.toNat then
        data[position.bytes.toNat + index.val]'(by omega)
      else 0
    let mut fragments := #[]
    for index in [:pointerSize.bytes.toNat] do
      let pos := Miri.ABI.Size.ofBytes (position.bytes + UInt64.ofNat index)
      if inRange pos then
        fragments := fragments.push (pos, ⟨UInt8.ofNat index, prov, bytes⟩)
    return fragments
  else throw (.fragmentSliceOutOfBounds position pointerSize data.size)

private def lm23PrepareCopy {Prov : Type} (self : Miri.Memory.ProvenanceMap Prov)
    (range : Miri.Memory.AllocRange) (data : Array UInt8)
    (pointerSize : Miri.ABI.Size) :
    Except Miri.Memory.ProvenanceMapError
      (Miri.Memory.ProvenanceCopy Prov) := do
  if pointerSize.bytes == 0 then throw .pointerSizeZero
  let finish ← lm23RangeEnd range
  let mut ptrs := #[]
  if range.size.bytes ≥ pointerSize.bytes then
    let adjustedEnd ← lm23SubtractSize finish
      (Miri.ABI.Size.ofBytes (pointerSize.bytes - 1))
    for (offset, prov) in lm23RangeEntries self.ptrs range.start adjustedEnd do
      ptrs := ptrs.push (← lm23SubtractSize offset range.start, prov)
  let beginOverlap := (← lm23RangePtrs self
    (Miri.Memory.allocRange range.start Miri.ABI.Size.ZERO) pointerSize)[0]?
  let endOverlap := (← lm23RangePtrs self
    (Miri.Memory.allocRange finish Miri.ABI.Size.ZERO) pointerSize)[0]?
  let mut bytes := #[]
  if beginOverlap.isSome || endOverlap.isSome || self.byteFragments.isSome then
    if let some (position, prov) := beginOverlap then
      let ptrEnd ← (Miri.ABI.Size.add position pointerSize).mapError
        (Miri.Memory.ProvenanceMapError.memory ∘
          Miri.Memory.MemoryError.sizeError)
      let fragmentEnd := if ptrEnd.bytes < finish.bytes then ptrEnd else finish
      if range.start.bytes < fragmentEnd.bytes then
        let fragments ← lm23PtrFragments
          (fun pos => range.start.bytes ≤ pos.bytes &&
            pos.bytes < fragmentEnd.bytes)
          position prov data pointerSize
        for (pos, frag) in fragments do
          bytes := bytes.push (← lm23SubtractSize pos range.start, frag)
    for (offset, frag) in (← lm23RangeBytes self range) do
      bytes := bytes.push (← lm23SubtractSize offset range.start, frag)
    if let some (position, prov) := endOverlap then
      if (beginOverlap.map fun (begin, _) =>
          begin.bytes != position.bytes).getD true then
        if position.bytes < range.start.bytes then
          throw .unsortedOrDuplicateKeys
        if position.bytes < finish.bytes then
          let fragments ← lm23PtrFragments
            (fun pos => position.bytes ≤ pos.bytes && pos.bytes < finish.bytes)
            position prov data pointerSize
          for (pos, frag) in fragments do
            let shifted ← lm23SubtractSize pos range.start
            if !((bytes.back?.map fun last =>
                decide (last.1.bytes < shifted.bytes)).getD true) then
              throw .unsortedOrDuplicateKeys
            bytes := bytes.push (shifted, frag)
  return ⟨ptrs, bytes⟩

private theorem lm23_prepareCopy_eq {Prov : Type} :
    @Miri.Memory.ProvenanceMap.prepareCopy Prov = lm23PrepareCopy := rfl

private theorem lm23RangeEntries_new (start finish : Miri.ABI.Size) :
    lm23RangeEntries
      (Miri.Memory.ProvenanceMap.new (Prov := AnnealProv)).ptrs start finish =
      #[] := rfl

private theorem lm23_array_forIn_empty {α β : Type} {m : Type → Type} [Monad m]
    (b : β) (f : α → β → m (ForInStep β)) :
    forIn (#[] : Array α) b f = pure b := rfl

private theorem lm23_allocRange_endExclusive_of_lt {off sz : Miri.ABI.Size}
    (hlt : off.bytes.toNat + sz.bytes.toNat < 2 ^ 64) :
    (Miri.Memory.allocRange off sz).endExclusive =
      .ok (Miri.ABI.Size.ofBytes (off.bytes + sz.bytes)) := by
  unfold Miri.Memory.AllocRange.endExclusive Miri.Memory.AllocRange.end
    Miri.Memory.allocRange
  have hadd : (off.bytes + sz.bytes).toNat =
      off.bytes.toNat + sz.bytes.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt hlt
  have hno_wrap : ¬ (off.bytes + sz.bytes) < off.bytes := by
    rw [UInt64.lt_iff_toNat_lt, hadd]; omega
  simp [Miri.ABI.Size.add, hno_wrap, Except.mapError]

private theorem lm23_provenanceMap_prepareCopy_new (sz : Miri.ABI.Size)
    (data : Array UInt8) :
    (Miri.Memory.ProvenanceMap.new (Prov := AnnealProv)).prepareCopy
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz) data
      (Miri.ABI.Size.ofBytes 8) = .ok ⟨#[], #[]⟩ := by
  have hlt : Miri.ABI.Size.ZERO.bytes.toNat + sz.bytes.toNat < 2 ^ 64 := by
    simp [Miri.ABI.Size.ZERO]; exact UInt64.toNat_lt _
  have hend := lm23_allocRange_endExclusive_of_lt hlt
  have hfin : (Miri.ABI.Size.ofBytes
      (Miri.ABI.Size.ZERO.bytes + sz.bytes)).bytes.toNat = sz.bytes.toNat := by
    simp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]
  have hend0_s := lm23_allocRange_endExclusive_of_lt
    (off := Miri.ABI.Size.ZERO) (sz := Miri.ABI.Size.ZERO) (by decide)
  have hend0_f := lm23_allocRange_endExclusive_of_lt
    (off := Miri.ABI.Size.ofBytes (Miri.ABI.Size.ZERO.bytes + sz.bytes))
    (sz := Miri.ABI.Size.ZERO)
    (by simp [Miri.ABI.Size.ZERO]; exact UInt64.toNat_lt _)
  rw [lm23_prepareCopy_eq]
  unfold lm23PrepareCopy lm23RangePtrs lm23RangeBytes lm23AdjustedStart
    lm23RangeEnd lm23SubtractSize
  have hpz : ((Miri.ABI.Size.ofBytes 8).bytes == 0) = false := rfl
  have hstart_eq :
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz).start =
        Miri.ABI.Size.ZERO := rfl
  simp only [hpz, Bool.false_eq_true, ↓reduceIte, hstart_eq, hend, hend0_s,
    hend0_f, Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure,
    Except.pure, lm23RangeEntries_new, lm23_array_forIn_empty]
  by_cases hge : (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz).size.bytes ≥
      (Miri.ABI.Size.ofBytes 8).bytes
  · have hsub_ok : ¬ (Miri.ABI.Size.ofBytes
        (Miri.ABI.Size.ZERO.bytes + sz.bytes)).bytes <
        (Miri.ABI.Size.ofBytes ((Miri.ABI.Size.ofBytes 8).bytes - 1)).bytes := by
      rw [UInt64.lt_iff_toNat_lt, hfin]
      have hge' : 8 ≤ sz.bytes.toNat := by
        simpa [GE.ge, UInt64.le_iff_toNat_le, Miri.Memory.allocRange,
          Miri.ABI.Size.ofBytes] using hge
      have h7 : (Miri.ABI.Size.ofBytes
          ((Miri.ABI.Size.ofBytes 8).bytes - 1)).bytes.toNat = 7 := rfl
      omega
    simp only [hge, ↓reduceIte, Miri.ABI.Size.sub, hsub_ok]
    rfl
  · simp only [hge, ↓reduceIte]
    rfl

private theorem lm23_initMask_setRange_full (mask : Miri.Memory.InitMask)
    (range : Miri.Memory.AllocRange) (finish : Miri.ABI.Size) (newState : Bool)
    (hend : range.endExclusive = .ok finish)
    (hstart : range.start.bytes = 0)
    (hlen : mask.len.bytes ≤ finish.bytes) :
    mask.setRange range newState = .ok ⟨.Lazy newState, finish⟩ := by
  cases mask with
  | mk blocks len =>
    cases blocks <;>
      simp [Miri.Memory.InitMask.setRange, hend, hstart, hlen,
        Pure.pure, Except.pure, Bind.bind, Except.bind]

private theorem lm23SearchBlock_bit (words : Array UInt64)
    {block startBit : Nat} (isInit : Bool)
    (hblk_sz : block < words.size)
    (hblk : block * 64 + 64 ≤ 2 ^ 64)
    {idx : Miri.ABI.Size}
    (hsearch : lm23SearchBlock (words[block]'hblk_sz) block startBit isInit =
      .ok (some idx)) :
    maskBlocksGetBit words idx.bytes.toNat = isInit := by
  let word := words[block]'hblk_sz
  let bits := if isInit then word.toNat else lm23WordMask - word.toNat
  unfold lm23SearchBlock lm23FirstSetBit at hsearch
  cases hopt : (List.range (64 - startBit)).find?
      (fun offset => lm23BitAt bits (startBit + offset)) with
  | none =>
    simp [word, bits, hopt, pure, Except.pure] at hsearch
  | some offset =>
    have hmem : offset ∈ List.range (64 - startBit) :=
      List.mem_of_find?_eq_some hopt
    have hbit_true : lm23BitAt bits (startBit + offset) = true :=
      @List.find?_some _ (fun offset => lm23BitAt bits (startBit + offset)) _
        _ hopt
    have hoff_lt64 : offset + startBit < 64 := by
      have := List.mem_range.mp hmem; omega
    have hoff_le_max :
        block * lm23BlockSize + (offset + startBit) ≤ lm23MaxSizeBytes := by
      unfold lm23BlockSize lm23MaxSizeBytes; omega
    simp only [word, bits, hopt, Option.map, lm23SizeFromNat, hoff_le_max,
      ↓reduceIte, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq, Option.some.injEq] at hsearch
    subst hsearch
    have hoff_u64 :
        (UInt64.ofNat (block * lm23BlockSize + (offset + startBit))).toNat =
          block * 64 + (startBit + offset) := by
      rw [UInt64.toNat_ofNat']
      unfold lm23BlockSize at *
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have hdiv : (block * 64 + (startBit + offset)) / 64 = block := by omega
    have hmod : (block * 64 + (startBit + offset)) % 64 = startBit + offset := by
      omega
    unfold maskBlocksGetBit
    simp only [Miri.ABI.Size.ofBytes, hoff_u64, hdiv, hmod,
      Array.getElem?_eq_getElem hblk_sz]
    unfold lm23BitAt at hbit_true
    cases isInit
    · dsimp [bits] at hbit_true
      rw [lm23_testBit_wordMask_sub word (by omega)] at hbit_true
      cases hb : Nat.testBit word.toNat (startBit + offset) <;>
        simp [hb] at hbit_true ⊢
    · dsimp [bits] at hbit_true
      exact hbit_true

private theorem lm23FindBitStep_loop_bit
    (words : Array UInt64) {finishBytes : Nat} (isInit : Bool)
    (hfin_blk : ((finishBytes - 1) / 64) * 64 + 64 ≤ 2 ^ 64)
    (hbp_sz : (finishBytes - 1) / 64 < words.size) :
    ∀ m k, k + m ≤ (finishBytes - 1) / 64 + 1 →
      ∀ idx,
        forIn (List.range' k m) (none, ())
          (lm23FindBitStep ⟨words⟩ finishBytes isInit) =
            .ok (some (some idx), ()) →
        maskBlocksGetBit words idx.bytes.toNat = isInit := by
  intro m
  induction m with
  | zero =>
    intro _ _ _ h
    cases h
  | succ m ih =>
    intro k hkm idx hfor
    rw [List.range'_succ, List.forIn_cons] at hfor
    have hk_sz : k < words.size := by omega
    have hk_blk : k * 64 + 64 ≤ 2 ^ 64 := by omega
    have hget_k : lm23GetBlock ⟨words⟩ k = .ok (words[k]'hk_sz) := by
      simp [lm23GetBlock, hk_sz]
    obtain ⟨optK, hsearchK, _⟩ :=
      lm23SearchBlock_ok (words[k]'hk_sz) isInit hk_blk (startBit := 0)
    cases optK with
    | none =>
      have hstep_k :
          lm23FindBitStep ⟨words⟩ finishBytes isInit k (none, ()) =
            .ok (.yield (none, ())) := by
        unfold lm23FindBitStep
        simp [hget_k, hsearchK, bind, Except.bind, pure, Except.pure]
      rw [hstep_k] at hfor
      exact ih (k + 1) (by omega) idx hfor
    | some idxK =>
      by_cases hlt_fin : lm23SizeBytes idxK < finishBytes
      · have hstep_k :
            lm23FindBitStep ⟨words⟩ finishBytes isInit k (none, ()) =
              .ok (.done (some (some idxK), ())) := by
          unfold lm23FindBitStep
          simp [hget_k, hsearchK, hlt_fin, bind, Except.bind, pure, Except.pure]
        rw [hstep_k] at hfor
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq,
          Prod.mk.injEq, Option.some.injEq] at hfor
        rcases hfor with ⟨rfl, _⟩
        exact lm23SearchBlock_bit words isInit hk_sz hk_blk hsearchK
      · have hstep_k :
            lm23FindBitStep ⟨words⟩ finishBytes isInit k (none, ()) =
              .ok (.done (some none, ())) := by
          unfold lm23FindBitStep
          simp [hget_k, hsearchK, hlt_fin, bind, Except.bind, pure, Except.pure]
        rw [hstep_k] at hfor
        simp [bind, Except.bind, pure, Except.pure] at hfor

private theorem lm23FindBitFast_bit (words : Array UInt64)
    {start finish : Miri.ABI.Size} (isInit : Bool)
    (hfin_blk : ((finish.bytes.toNat - 1) / 64) * 64 + 64 ≤ 2 ^ 64)
    (hsz : (finish.bytes.toNat - 1) / 64 < words.size)
    {idx : Miri.ABI.Size}
    (hfind : lm23FindBitFast ⟨words⟩ start finish isInit = .ok (some idx)) :
    maskBlocksGetBit words idx.bytes.toNat = isInit := by
  by_cases hge : lm23SizeBytes start ≥ lm23SizeBytes finish
  · unfold lm23FindBitFast at hfind
    simp [hge, pure, Except.pure] at hfind
  · have hlt : start.bytes.toNat < finish.bytes.toNat := by
      unfold lm23SizeBytes at hge; omega
    have hsub1_le : finish.bytes.toNat - 1 ≤ lm23MaxSizeBytes := by
      unfold lm23MaxSizeBytes; omega
    have hsub1_u64 :
        (UInt64.ofNat (finish.bytes.toNat - 1)).toNat =
          finish.bytes.toNat - 1 := by
      rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
    let startBlock := start.bytes.toNat / 64
    let startBit := start.bytes.toNat % 64
    let endBlock := (finish.bytes.toNat - 1) / 64
    have hstart_sz : startBlock < words.size := by omega
    have hstart_blk : startBlock * 64 + 64 ≤ 2 ^ 64 := by omega
    have hget_start :
        lm23GetBlock ⟨words⟩ startBlock = .ok (words[startBlock]'hstart_sz) := by
      simp [lm23GetBlock, hstart_sz]
    have hbit_start : lm23BitIndex start = (startBlock, startBit) := rfl
    have hsz_end : lm23SizeFromNat (lm23SizeBytes finish - 1) =
        .ok (Miri.ABI.Size.ofBytes (UInt64.ofNat (finish.bytes.toNat - 1))) := by
      simp [lm23SizeFromNat, lm23SizeBytes, hsub1_le]
    have hbit_end :
        (lm23BitIndex
          (Miri.ABI.Size.ofBytes (UInt64.ofNat (finish.bytes.toNat - 1)))).1 =
          endBlock := by
      simp [lm23BitIndex, lm23SizeBytes, lm23BlockSize, Miri.ABI.Size.ofBytes,
        hsub1_u64, endBlock]
    obtain ⟨first, hsearch_ok, _⟩ :=
      lm23SearchBlock_ok (words[startBlock]'hstart_sz) isInit hstart_blk
        (startBit := startBit)
    unfold lm23FindBitFast at hfind
    simp only [hge, ↓reduceIte, hbit_start, hsz_end, bind, Except.bind,
      hbit_end, hget_start, hsearch_ok] at hfind
    cases first with
    | some idx0 =>
      by_cases hlt0 : lm23SizeBytes idx0 < lm23SizeBytes finish
      · simp only [hlt0, ↓reduceIte, pure, Except.pure, Except.ok.injEq,
          Option.some.injEq] at hfind
        subst hfind
        exact lm23SearchBlock_bit words isInit hstart_sz hstart_blk hsearch_ok
      · simp [hlt0, pure, Except.pure] at hfind
    | none =>
      by_cases hlt_blk : startBlock < endBlock
      · obtain ⟨res, hloop, _⟩ :=
          lm23FindBitStep_loop_ok words (finishBytes := lm23SizeBytes finish)
            isInit
            (by unfold lm23SizeBytes; exact hfin_blk)
            (by unfold lm23SizeBytes; exact hsz)
            (endBlock + 1 - (startBlock + 1)) (startBlock + 1)
            (by unfold lm23SizeBytes; omega)
        simp only [hlt_blk, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range',
          Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one] at hfind
        have hloop' := hloop
        unfold lm23FindBitStep at hloop'
        dsimp only [bind, Except.bind] at hloop'
        rw [hloop'] at hfind
        cases res with
        | none => simp [pure, Except.pure] at hfind
        | some opt =>
          simp only [pure, Except.pure, Except.ok.injEq] at hfind
          subst hfind
          exact lm23FindBitStep_loop_bit words isInit
            (by unfold lm23SizeBytes; exact hfin_blk)
            (by unfold lm23SizeBytes; exact hsz)
            (endBlock + 1 - (startBlock + 1)) (startBlock + 1)
            (by unfold lm23SizeBytes; omega) idx hloop
      · simp [hlt_blk, pure, Except.pure] at hfind

private def lm23IterNext? (iter : Miri.Memory.InitChunkIter) :
    Except Miri.Memory.InitMaskError
      (Option (Miri.Memory.InitChunk × Miri.Memory.InitChunkIter)) := do
  if iter.start.bytes > iter.finish.bytes ||
      iter.finish.bytes > iter.initMask.len.bytes then
    throw (.invalidChunkIterator iter.start iter.finish)
  if lm23SizeBytes iter.start ≥ lm23SizeBytes iter.finish then return none
  match iter.initMask.blocks with
  | .Lazy state =>
    if state != iter.isInit then
      throw (.invalidChunkIterator iter.start iter.finish)
  | .Materialized _ => pure ()
  let chunkEnd ← do
    match iter.initMask.blocks with
    | .Lazy _ => pure iter.finish
    | .Materialized blocks => do
      let found ← lm23FindBitFast blocks iter.start iter.finish (!iter.isInit)
      pure (found.getD iter.finish)
  if chunkEnd.bytes ≤ iter.start.bytes then
    throw (.invalidChunkIterator iter.start iter.finish)
  let chunk := if iter.isInit then Miri.Memory.InitChunk.Init iter.start chunkEnd
    else Miri.Memory.InitChunk.Uninit iter.start chunkEnd
  return some (chunk, { iter with isInit := !iter.isInit, start := chunkEnd })

private theorem lm23_iterNext?_eq (iter : Miri.Memory.InitChunkIter) :
    iter.next? = lm23IterNext? iter := rfl

private theorem lm23_fromEndpoints_ok {s f : Miri.ABI.Size}
    (hle : s.bytes.toNat ≤ f.bytes.toNat) :
    ∃ r, Miri.Memory.AllocRange.fromEndpoints s f = .ok r := by
  unfold Miri.Memory.AllocRange.fromEndpoints Miri.ABI.Size.sub
  have hnot_lt : ¬ f.bytes < s.bytes := by
    rw [UInt64.lt_iff_toNat_lt]; omega
  simp [hnot_lt, Except.mapError, bind, Except.bind, pure, Except.pure]

private theorem lm23_iterNext?_step
    {mask : Miri.Memory.InitMask} {sz cur : Miri.ABI.Size}
    {words : Array UInt64} {isInit : Bool}
    (hrel : InitMaskWordRel mask sz words)
    (hcur_lt : cur.bytes.toNat < sz.bytes.toNat)
    (hcur_bit : maskBlocksGetBit words cur.bytes.toNat = isInit) :
    ∃ (chunk : Miri.Memory.InitChunk) (chunkEnd : Miri.ABI.Size),
      (Miri.Memory.InitChunkIter.mk mask isInit cur sz).next? =
        .ok (some (chunk, ⟨mask, !isInit, chunkEnd, sz⟩)) ∧
      chunk.isInit = isInit ∧
      (∃ r, chunk.range = .ok r) ∧
      cur.bytes.toNat < chunkEnd.bytes.toNat ∧
      chunkEnd.bytes.toNat ≤ sz.bytes.toNat ∧
      (chunkEnd.bytes.toNat < sz.bytes.toNat →
        maskBlocksGetBit words chunkEnd.bytes.toNat = !isInit) := by
  obtain ⟨hlen, hsize, hblocks⟩ := hrel
  have hnot_gt_sf : ¬ cur.bytes > sz.bytes := by
    rw [GT.gt, UInt64.lt_iff_toNat_lt]; omega
  have hnot_gt_len : ¬ sz.bytes > mask.len.bytes := by
    rw [hlen]; simp [GT.gt]
  have hnot_ge : ¬ lm23SizeBytes cur ≥ lm23SizeBytes sz := by
    unfold lm23SizeBytes; omega
  rw [lm23_iterNext?_eq]
  unfold lm23IterNext?
  dsimp only
  simp only [hnot_gt_sf, hnot_gt_len, Bool.or_self, decide_false,
    Bool.false_eq_true, ↓reduceIte, hnot_ge, bind, Bind.bind, Except.bind,
    pure, Pure.pure, Except.pure]
  rcases hblocks with ⟨hb, rfl⟩ | ⟨hb, rfl⟩ | hb
  · have his : isInit = false := by
      rw [← hcur_bit, maskBlocksGetBit_initWordsFalse]
    subst his
    have hnot_le : ¬ sz.bytes ≤ cur.bytes := by
      rw [UInt64.le_iff_toNat_le]; omega
    simp only [hb, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hnot_le]
    obtain ⟨r, hr⟩ := lm23_fromEndpoints_ok (Nat.le_of_lt hcur_lt)
    exact ⟨.Uninit cur sz, sz, rfl, rfl, ⟨r, hr⟩, hcur_lt, Nat.le_refl _,
      fun h => absurd h (Nat.lt_irrefl _)⟩
  · have his : isInit = true := by
      rw [← hcur_bit, maskBlocksGetBit_initWordsTrue hcur_lt]
    subst his
    have hnot_le : ¬ sz.bytes ≤ cur.bytes := by
      rw [UInt64.le_iff_toNat_le]; omega
    simp only [hb, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hnot_le]
    obtain ⟨r, hr⟩ := lm23_fromEndpoints_ok (Nat.le_of_lt hcur_lt)
    exact ⟨.Init cur sz, sz, rfl, rfl, ⟨r, hr⟩, hcur_lt, Nat.le_refl _,
      fun h => absurd h (Nat.lt_irrefl _)⟩
  · simp only [hb]
    have hsz_lt64 : sz.bytes.toNat < 2 ^ 64 := UInt64.toNat_lt _
    have hfin_blk : ((sz.bytes.toNat - 1) / 64) * 64 + 64 ≤ 2 ^ 64 := by omega
    have hwords_sz : (sz.bytes.toNat - 1) / 64 < words.size := by
      rw [hsize]; omega
    obtain ⟨opt, hfind, hbounds⟩ :=
      lm23FindBitFast_ok words (start := cur) (finish := sz) (!isInit)
        hfin_blk hwords_sz
    rw [hfind]
    dsimp only
    let chunkEnd := opt.getD sz
    have hce_prop :
        cur.bytes.toNat < chunkEnd.bytes.toNat ∧
        chunkEnd.bytes.toNat ≤ sz.bytes.toNat ∧
        (chunkEnd.bytes.toNat < sz.bytes.toNat →
          maskBlocksGetBit words chunkEnd.bytes.toNat = !isInit) := by
      cases opt with
      | none =>
        exact ⟨hcur_lt, Nat.le_refl _, fun h => absurd h (Nat.lt_irrefl _)⟩
      | some idx =>
        obtain ⟨hlo, hhi⟩ := hbounds idx rfl
        have hbit_idx :=
          lm23FindBitFast_bit words (!isInit) hfin_blk hwords_sz hfind
        have hne : cur.bytes.toNat ≠ idx.bytes.toNat := by
          intro heq
          rw [heq, hbit_idx] at hcur_bit
          cases isInit <;> cases hcur_bit
        exact ⟨by dsimp [chunkEnd]; omega,
          by dsimp [chunkEnd]; omega,
          fun _ => hbit_idx⟩
    have hnot_le : ¬ chunkEnd.bytes ≤ cur.bytes := by
      rw [UInt64.le_iff_toNat_le]; omega
    simp only [chunkEnd, hnot_le, ↓reduceIte]
    obtain ⟨r, hr⟩ := lm23_fromEndpoints_ok (Nat.le_of_lt hce_prop.1)
    cases isInit <;>
      exact ⟨_, chunkEnd, rfl, rfl, ⟨r, hr⟩, hce_prop.1, hce_prop.2.1,
        hce_prop.2.2⟩

private theorem lm23_forIn_push_ranges :
    ∀ (cs : List Miri.Memory.InitChunk) (acc : Array UInt64),
      (∀ c ∈ cs, ∃ r, c.range = .ok r) →
      ∃ runs : Array UInt64,
        (forIn cs acc
          (fun (chunk : Miri.Memory.InitChunk) (runs : Array UInt64) => do
            let chunkRange ← chunk.range
            pure (ForInStep.yield (runs.push chunkRange.size.bytes))) :
          Except Miri.Memory.InitMaskError (Array UInt64)) =
          .ok runs
  | [], acc, _ => ⟨acc, rfl⟩
  | c :: cs, acc, hall => by
    obtain ⟨r, hr⟩ := hall c (List.mem_cons_self ..)
    rw [List.forIn_cons]
    simp only [hr, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
    exact lm23_forIn_push_ranges cs (acc.push r.size.bytes)
      (fun x hx => hall x (List.mem_cons_of_mem c hx))

private theorem initMaskWordRel_prepareCopy_init0
    {mask : Miri.Memory.InitMask} {sz : Miri.ABI.Size} {words : Array UInt64}
    (hrel : InitMaskWordRel mask sz words)
    (hpos : 0 < sz.bytes.toNat)
    (hbit0 : maskBlocksGetBit words 0 = true) :
    ∃ defined : Miri.Memory.InitCopy,
      mask.prepareCopy (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz) =
        .ok defined ∧
      defined.noBytesInit = false := by
  have haux : ∃ aux : Miri.Memory.InitChunkIter → Nat →
      Except Miri.Memory.InitMaskError (Array Miri.Memory.InitChunk),
      (∀ it, Miri.Memory.InitMask.collectChunks it =
        aux it (it.finish.bytes.toNat - it.start.bytes.toNat + 1)) ∧
      (∀ it n, aux it (n + 1) = (do
        match ← it.next? with
        | none => return #[]
        | some (chunk, next) => return #[chunk] ++ (← aux next n))) := by
    refine ⟨fun it k => WellFounded.Nat.fix
        (α := (_ : Miri.Memory.InitChunkIter) ×' Nat)
        (motive := fun _ =>
          Except Miri.Memory.InitMaskError (Array Miri.Memory.InitChunk))
        (fun x => PSigma.casesOn x fun _ fuel => fuel) _ ⟨it, k⟩,
      fun _ => by with_unfolding_all rfl,
      fun it n => ?_⟩
    dsimp only
    rw [WellFounded.Nat.fix_eq]
    with_unfolding_all rfl
  rcases haux with ⟨aux, hcol_eq, haux_step⟩
  have hloop :
      ∀ fuel (cur : Miri.ABI.Size) (isInit : Bool),
        cur.bytes.toNat ≤ sz.bytes.toNat →
        sz.bytes.toNat - cur.bytes.toNat < fuel →
        (cur.bytes.toNat < sz.bytes.toNat →
          maskBlocksGetBit words cur.bytes.toNat = isInit) →
        ∃ chunks : Array Miri.Memory.InitChunk,
          aux ⟨mask, isInit, cur, sz⟩ fuel = .ok chunks ∧
          (∀ c ∈ chunks.toList, ∃ r, c.range = .ok r) ∧
          (cur.bytes.toNat < sz.bytes.toNat →
            ∃ first, chunks[0]? = some first ∧ first.isInit = isInit) := by
    intro fuel
    induction fuel with
    | zero => intro _ _ _ hlt _; omega
    | succ fuel ih =>
      intro cur isInit hle hfuel hbit
      rw [haux_step]
      by_cases hlt : cur.bytes.toNat < sz.bytes.toNat
      · obtain ⟨chunk, chunkEnd, hnext, hc_init, hc_rng, hgt, hce_le, hce_bit⟩ :=
          lm23_iterNext?_step hrel hlt (hbit hlt)
        rw [hnext]
        dsimp only [bind, Bind.bind, Except.bind]
        obtain ⟨rest, hrest, hrest_rng, _⟩ :=
          ih chunkEnd (!isInit) hce_le (by omega) hce_bit
        rw [hrest]
        dsimp only [pure, Pure.pure, Except.pure]
        refine ⟨#[chunk] ++ rest, rfl, ?_, fun _ => ⟨chunk, ?_, hc_init⟩⟩
        · intro c hc
          rw [Array.toList_append] at hc
          rcases List.mem_append.mp hc with h1 | h2
          · rcases List.mem_singleton.mp h1 with rfl
            exact hc_rng
          · exact hrest_rng c h2
        · simp [Array.getElem?_append]
      · have heq_b : cur.bytes = sz.bytes := by
          have h1 : ¬ cur.bytes < sz.bytes := by
            rw [UInt64.lt_iff_toNat_lt]; omega
          have h2 : ¬ sz.bytes < cur.bytes := by
            rw [UInt64.lt_iff_toNat_lt]; omega
          exact UInt64.le_antisymm (UInt64.not_lt.mp h2) (UInt64.not_lt.mp h1)
        have hnext_none :
            (Miri.Memory.InitChunkIter.mk mask isInit cur sz).next? =
              .ok none := by
          rw [lm23_iterNext?_eq]
          unfold lm23IterNext?
          have h1 : ¬ cur.bytes > sz.bytes := by rw [heq_b]; simp [GT.gt]
          have h2 : ¬ sz.bytes > mask.len.bytes := by
            rw [hrel.1]; simp [GT.gt]
          have h3 : lm23SizeBytes cur ≥ lm23SizeBytes sz := by
            unfold lm23SizeBytes; omega
          simp [h1, h2, h3, pure, Except.pure]
        rw [hnext_none]
        exact ⟨#[], rfl, (fun _ h => by simp at h), (fun h => absurd h hlt)⟩
  have hlt0 : Miri.ABI.Size.ZERO.bytes.toNat + sz.bytes.toNat < 2 ^ 64 := by
    simp [Miri.ABI.Size.ZERO]; exact UInt64.toNat_lt _
  have hend := lm23_allocRange_endExclusive_of_lt hlt0
  have hfin_eq :
      Miri.ABI.Size.ofBytes (Miri.ABI.Size.ZERO.bytes + sz.bytes) = sz := by
    cases sz; simp [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes]
  rw [hfin_eq] at hend
  have hnz : ((Miri.Memory.allocRange Miri.ABI.Size.ZERO sz).size.bytes == 0) =
      false := by
    cases h : ((Miri.Memory.allocRange Miri.ABI.Size.ZERO sz).size.bytes == 0)
    · rfl
    · have hz := eq_of_beq h
      dsimp [Miri.Memory.allocRange] at hz
      rw [hz] at hpos; simp at hpos
  have hget0 : mask.get Miri.ABI.Size.ZERO = .ok true := by
    have hg := initMaskWordRel_get hrel hpos
    simpa [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes, hbit0] using hg
  have hrange :
      mask.rangeAsInitChunks (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz) =
        .ok ⟨mask, true, Miri.ABI.Size.ZERO, sz⟩ := by
    unfold Miri.Memory.InitMask.rangeAsInitChunks
    rw [hend]
    have hnot_gt : ¬ sz.bytes > mask.len.bytes := by
      rw [hrel.1]; simp [GT.gt]
    have hlt_b : Miri.ABI.Size.ZERO.bytes < sz.bytes := by
      rw [UInt64.lt_iff_toNat_lt]; simpa [Miri.ABI.Size.ZERO] using hpos
    simp [hnot_gt, hlt_b, Miri.Memory.allocRange, hget0,
      bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  obtain ⟨chunks, hchunks_aux, hrng_all, hfirst_ex⟩ :=
    hloop (sz.bytes.toNat - 0 + 1) Miri.ABI.Size.ZERO true
      (by simp [Miri.ABI.Size.ZERO])
      (by simp [Miri.ABI.Size.ZERO])
      (fun _ => by simpa [Miri.ABI.Size.ZERO] using hbit0)
  obtain ⟨first, hfirst0, hfirst_true⟩ :=
    hfirst_ex (by simpa [Miri.ABI.Size.ZERO] using hpos)
  have hcol : Miri.Memory.InitMask.collectChunks
      ⟨mask, true, Miri.ABI.Size.ZERO, sz⟩ = .ok chunks := by
    rw [hcol_eq]; simpa [Miri.ABI.Size.ZERO] using hchunks_aux
  obtain ⟨runs, hfor⟩ := lm23_forIn_push_ranges chunks.toList #[] hrng_all
  rw [Array.forIn_toList] at hfor
  unfold Miri.Memory.InitMask.prepareCopy
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte, hrange, bind, Bind.bind,
    Except.bind, hcol, hfirst0]
  simp only [bind, Bind.bind, Except.bind] at hfor
  rw [hfor]
  refine ⟨⟨first.isInit, runs⟩, rfl, ?_⟩
  simp [Miri.Memory.InitCopy.noBytesInit, hfirst_true]

private def lm23CheckedSlice {P E : Type}
    (allocation : Miri.Memory.Allocation P E)
    (range : Miri.Memory.AllocRange) :
    Except Miri.Memory.AllocError (Array UInt8) := do
  if (lm22AllocRaw allocation).size != allocation.byteSize.bytes.toNat then
    throw (.storageLengthMismatch allocation.byteSize
      (lm22AllocRaw allocation).size)
  let finish ← range.endExclusive |>.mapError Miri.Memory.AllocError.memory
  if range.start.bytes > finish.bytes ||
      finish.bytes > allocation.byteSize.bytes then
    throw (.outOfBounds range allocation.byteSize)
  return (lm22AllocRaw allocation).extract
    range.start.bytes.toNat finish.bytes.toNat

private theorem lm23_getBytesUnchecked_eq {P E : Type}
    (allocation : Miri.Memory.Allocation P E)
    (range : Miri.Memory.AllocRange) :
    Miri.Memory.Allocation.getBytesUnchecked allocation range =
      lm23CheckedSlice allocation range := rfl

private theorem lm23_checkedSlice_full {P E : Type}
    {a : Miri.Memory.Allocation P E} {sz : Miri.ABI.Size}
    (hlen : a.len = sz.bytes.toNat) (hsz : a.byteSize = sz) :
    Miri.Memory.Allocation.getBytesUnchecked a
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz) =
      .ok ((lm22AllocRaw a).extract 0 sz.bytes.toNat) := by
  rw [lm23_getBytesUnchecked_eq]
  have hlt0 : Miri.ABI.Size.ZERO.bytes.toNat + sz.bytes.toNat < 2 ^ 64 := by
    simp [Miri.ABI.Size.ZERO]; exact UInt64.toNat_lt _
  have hend := lm23_allocRange_endExclusive_of_lt hlt0
  have hfin_eq :
      Miri.ABI.Size.ofBytes (Miri.ABI.Size.ZERO.bytes + sz.bytes) = sz := by
    cases sz; simp [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes]
  rw [hfin_eq] at hend
  have hraw : (lm22AllocRaw a).size = a.byteSize.bytes.toNat := by
    rw [hsz]; exact hlen
  have hnot_gt1 : ¬ (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz).start.bytes >
      sz.bytes := by
    simp [GT.gt, Miri.Memory.allocRange, Miri.ABI.Size.ZERO,
      UInt64.lt_iff_toNat_lt]
  have hnot_gt2 : ¬ sz.bytes > a.byteSize.bytes := by
    rw [hsz]; simp [GT.gt]
  unfold lm23CheckedSlice
  rw [hend]
  simp only [hraw, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    Except.mapError, bind, Except.bind, hnot_gt1, hnot_gt2, Bool.or_self,
    pure, Except.pure]
  simp only [decide_false, Bool.false_eq_true, ↓reduceIte,
    Miri.Memory.allocRange, Miri.ABI.Size.ZERO, UInt64.toNat_zero]

private theorem lm23_size_mul_one (sz : Miri.ABI.Size) :
    sz.mul 1 = .ok sz := by
  cases sz with
  | mk b =>
    unfold Miri.ABI.Size.mul
    simp [UInt64.mul_one, UInt64.div_one, Miri.ABI.Size.ofBytes]

/-- Every initialized multi-variant direct-tagged enum allocation (`EnumMemRel`)
has strictly positive byte size (`0 < tagBytes ≤ size`) and an initialized tag
byte `0`, so self-copy (`sameAllocation = true`, `nonoverlapping = true`) via
`Miri.Memory.Allocation.copy` unconditionally fails with
`AllocError.copyRangesOverlap`. -/
theorem EnumMemRel.copy_self_overlap_err {mach : AnnealMachine}
    {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)} {v_act : Nat}
    {fieldVals : List Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag}
    {localAlloc : AnnealLocalAlloc}
    (h : EnumMemRel mach ty layouts tagBytes variants v_act fieldVals mp)
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hlive : LiveAllocEntry mach.memory.live allocId localAlloc) :
    ∃ alloc',
      Miri.Memory.Allocation.copy localAlloc.allocation
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO
          (translateTy ty layouts).layout.size)
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) true true
        localAlloc.allocation = .error .copyRangesOverlap alloc' := by
  rcases h with ⟨id0, _, _, la0, words, _, valid_enum, _, ptr_prov, _, _,
    live_entry, _, _, _, mut_alloc, _, byteSize_eq, alloc_len_eq, prov_empty,
    mask_rel, _, tag_bits_init, _, _, _⟩
  rw [ptr_prov] at hprov
  injection hprov with hp; injection hp with hid_eq _; subst hid_eq
  have hla_eq : localAlloc = la0 := by
    have h1 := hlive.1; rw [live_entry.1] at h1
    injection h1 with hmk; exact ((Prod.mk.inj hmk).2).symm
  subst hla_eq
  let sz := (translateTy ty layouts).layout.size
  have htb_pos : 0 < tagBytes := by
    rcases valid_enum.tagBytes_valid with rfl | rfl | rfl | rfl <;> omega
  have hsz_pos : 0 < sz.bytes.toNat :=
    Nat.lt_of_lt_of_le htb_pos valid_enum.size_ge_tag
  have hbit0 : maskBlocksGetBit words 0 = true := tag_bits_init 0 htb_pos
  have hmask_rel' :
      InitMaskWordRel localAlloc.allocation.initializationMask sz words := by
    dsimp [sz]; rw [← byteSize_eq]; exact mask_rel
  obtain ⟨defined, hprep_mask, hno_uninit⟩ :=
    initMaskWordRel_prepareCopy_init0 hmask_rel' hsz_pos hbit0
  have hlen_sz : localAlloc.allocation.len = sz.bytes.toNat := by
    rw [alloc_len_eq, byteSize_eq]
  have hslice := lm23_checkedSlice_full hlen_sz byteSize_eq
  unfold Miri.Memory.Allocation.getBytesUnchecked at hslice
  have hlt0 : Miri.ABI.Size.ZERO.bytes.toNat + sz.bytes.toNat < 2 ^ 64 := by
    simp [Miri.ABI.Size.ZERO]; exact UInt64.toNat_lt _
  have hend := lm23_allocRange_endExclusive_of_lt hlt0
  have hfin_eq :
      Miri.ABI.Size.ofBytes (Miri.ABI.Size.ZERO.bytes + sz.bytes) = sz := by
    cases sz; simp [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes]
  rw [hfin_eq] at hend
  have hnz_sz :
      ((Miri.Memory.allocRange Miri.ABI.Size.ZERO sz).size.bytes == 0) =
        false := by
    cases h : ((Miri.Memory.allocRange Miri.ABI.Size.ZERO sz).size.bytes == 0)
    · rfl
    · have hz := eq_of_beq h
      dsimp [Miri.Memory.allocRange] at hz
      rw [hz] at hsz_pos; simp at hsz_pos
  have hpos_b : Miri.ABI.Size.ZERO.bytes < sz.bytes := by
    rw [UInt64.lt_iff_toNat_lt]; simpa [Miri.ABI.Size.ZERO] using hsz_pos
  have hmul : (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz).size.mul 1 =
      .ok sz := lm23_size_mul_one sz
  have hprep_prov := lm23_provenanceMap_prepareCopy_new sz
    (lm22AllocRaw localAlloc.allocation)
  unfold lm22AllocRaw at hprep_prov
  have hmask_len := hmask_rel'.1
  rcases localAlloc with ⟨kind, src⟩
  dsimp only at mut_alloc byteSize_eq alloc_len_eq prov_empty hlen_sz hmask_len hprep_mask hslice hprep_prov ⊢
  cases src using Miri.Memory.Allocation.casesOn with
  | _ srcRaw srcSz srcProv srcMask srcAlign srcMut srcExtra srcNat =>
  change srcRaw.size = sz.bytes.toNat at hlen_sz
  change srcSz = sz at byteSize_eq
  change srcMut = .Mut at mut_alloc
  change srcProv = Miri.Memory.ProvenanceMap.new at prov_empty
  change srcMask.len = sz at hmask_len
  change srcMask.prepareCopy (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz) =
    .ok defined at hprep_mask
  change _ = Except.ok (srcRaw.extract 0 sz.bytes.toNat) at hslice
  change (Miri.Memory.ProvenanceMap.new (Prov := AnnealProv)).prepareCopy
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz)
      srcRaw (Miri.ABI.Size.ofBytes 8) = .ok ⟨#[], #[]⟩ at hprep_prov
  subst byteSize_eq mut_alloc prov_empty
  have hset_dst : srcMask.setRange
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz) true =
      .ok ⟨.Lazy true, sz⟩ :=
    lm23_initMask_setRange_full srcMask
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz)
      sz true hend rfl (by rw [hmask_len]; exact UInt64.le_refl _)
  have hclr_dst := Miri.Memory.ProvenanceMap.clear_new (P := AnnealProv)
    (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz) srcRaw
    (Miri.ABI.Size.ofBytes 8) sz (by decide) hend
  change ∃ alloc',
    Miri.Memory.Allocation.copy _
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz)
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) true true _ =
      .error .copyRangesOverlap alloc'
  unfold Miri.Memory.Allocation.copy Miri.Memory.Allocation.copyRepeatedly
  rw [hslice]
  dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
  rw [hmul]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hslice]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hprep_prov]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hprep_mask]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  split
  · rename_i _ updated₁ _
    simp only [hno_uninit, Bool.false_eq_true, ↓reduceIte, Bool.and_self,
      show (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz).size = sz from rfl,
      show (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz).start =
        Miri.ABI.Size.ZERO from rfl,
      hend, hpos_b, decide_true]
    exact ⟨updated₁, rfl⟩
  · rename_i _ _ hprep_ovw
    have hpo := hprep_ovw
    with_unfolding_all
      conv at hpo => lhs; whnf
      rw [hslice] at hpo
      dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hpo
      simp only [hnz_sz, Bool.false_eq_true, ↓reduceIte,
        bne_self_eq_false] at hpo
      conv at hpo => lhs; arg 2; whnf
      simp only [hset_dst, Except.mapError] at hpo
      dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure,
        Except.pure] at hpo
      rw [hclr_dst] at hpo
      cases hpo

private def lm23AllocResultTuple {P E : Type}
    (r : EStateM.Result Miri.Memory.AllocError (Miri.Memory.Allocation P E)
      Unit) :
    Option (Array UInt8 × Miri.ABI.Size × Miri.Memory.ProvenanceMap P ×
      Miri.Memory.InitMask × Miri.ABI.Align × Miri.Memory.Mutability × E ×
      Option Miri.Memory.NativeBufferOwnership) :=
  match r with
  | .ok () a =>
    Miri.Memory.Allocation.casesOn a
      (fun raw sz prov mask align mutab extra nat =>
        some (raw, sz, prov, mask, align, mutab, extra, nat))
  | .error _ _ => none

private theorem initMask_new_false_prepareCopy
    (sz : Miri.ABI.Size) (hpos : 0 < sz.bytes.toNat) :
    (Miri.Memory.InitMask.new sz false).prepareCopy
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz) =
      .ok ⟨false, #[sz.bytes]⟩ := by
  have haux : ∃ aux : Miri.Memory.InitChunkIter → Nat →
      Except Miri.Memory.InitMaskError (Array Miri.Memory.InitChunk),
      (∀ it, Miri.Memory.InitMask.collectChunks it =
        aux it (it.finish.bytes.toNat - it.start.bytes.toNat + 1)) ∧
      (∀ it n, aux it (n + 1) = (do
        match ← it.next? with
        | none => return #[]
        | some (chunk, next) => return #[chunk] ++ (← aux next n))) := by
    refine ⟨fun it k => WellFounded.Nat.fix
        (α := (_ : Miri.Memory.InitChunkIter) ×' Nat)
        (motive := fun _ =>
          Except Miri.Memory.InitMaskError (Array Miri.Memory.InitChunk))
        (fun x => PSigma.casesOn x fun _ fuel => fuel) _ ⟨it, k⟩,
      fun _ => by with_unfolding_all rfl,
      fun it n => ?_⟩
    dsimp only
    rw [WellFounded.Nat.fix_eq]
    with_unfolding_all rfl
  rcases haux with ⟨aux, hcol_eq, haux_step⟩
  have hlt0 : Miri.ABI.Size.ZERO.bytes.toNat + sz.bytes.toNat < 2 ^ 64 := by
    simp [Miri.ABI.Size.ZERO]; exact UInt64.toNat_lt _
  have hend := lm23_allocRange_endExclusive_of_lt hlt0
  have hfin_eq :
      Miri.ABI.Size.ofBytes (Miri.ABI.Size.ZERO.bytes + sz.bytes) = sz := by
    cases sz; simp [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes]
  rw [hfin_eq] at hend
  have hnz :
      ((Miri.Memory.allocRange Miri.ABI.Size.ZERO sz).size.bytes == 0) =
        false := by
    cases h : ((Miri.Memory.allocRange Miri.ABI.Size.ZERO sz).size.bytes == 0)
    · rfl
    · have hz := eq_of_beq h
      dsimp [Miri.Memory.allocRange] at hz
      rw [hz] at hpos; simp at hpos
  have hget0 :
      (Miri.Memory.InitMask.new sz false).get Miri.ABI.Size.ZERO =
        .ok false := rfl
  have hrange :
      (Miri.Memory.InitMask.new sz false).rangeAsInitChunks
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz) =
        .ok ⟨Miri.Memory.InitMask.new sz false, false,
          Miri.ABI.Size.ZERO, sz⟩ := by
    unfold Miri.Memory.InitMask.rangeAsInitChunks
    rw [hend]
    have hnot_gt : ¬ sz.bytes > (Miri.Memory.InitMask.new sz false).len.bytes := by
      simp [Miri.Memory.InitMask.new, GT.gt]
    have hlt_b : Miri.ABI.Size.ZERO.bytes < sz.bytes := by
      rw [UInt64.lt_iff_toNat_lt]; simp [Miri.ABI.Size.ZERO]; omega
    simp [hnot_gt, hlt_b, Miri.Memory.allocRange, hget0,
      bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  have hnext1 :
      (Miri.Memory.InitChunkIter.mk (Miri.Memory.InitMask.new sz false) false
        Miri.ABI.Size.ZERO sz).next? =
        .ok (some (.Uninit Miri.ABI.Size.ZERO sz,
          ⟨Miri.Memory.InitMask.new sz false, true, sz, sz⟩)) := by
    rw [lm23_iterNext?_eq]
    unfold lm23IterNext?
    have h1 : ¬ Miri.ABI.Size.ZERO.bytes > sz.bytes := by
      simp [GT.gt, Miri.ABI.Size.ZERO, UInt64.lt_iff_toNat_lt]
    have h3 : ¬ lm23SizeBytes Miri.ABI.Size.ZERO ≥ lm23SizeBytes sz := by
      unfold lm23SizeBytes; simp [Miri.ABI.Size.ZERO]; omega
    have h4 : ¬ sz.bytes ≤ Miri.ABI.Size.ZERO.bytes := by
      rw [UInt64.le_iff_toNat_le]; simp [Miri.ABI.Size.ZERO]; omega
    simp [Miri.Memory.InitMask.new, h1, h3, h4,
      bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  have hnext2 :
      (Miri.Memory.InitChunkIter.mk (Miri.Memory.InitMask.new sz false) true
        sz sz).next? = .ok none := by
    rw [lm23_iterNext?_eq]
    unfold lm23IterNext?
    have h1 : ¬ sz.bytes > sz.bytes := by simp [GT.gt]
    simp [Miri.Memory.InitMask.new, h1, lm23SizeBytes, pure, Except.pure]
  have hcol :
      Miri.Memory.InitMask.collectChunks
        ⟨Miri.Memory.InitMask.new sz false, false, Miri.ABI.Size.ZERO, sz⟩ =
        .ok #[.Uninit Miri.ABI.Size.ZERO sz] := by
    rw [hcol_eq]
    have hfuel :
        sz.bytes.toNat - Miri.ABI.Size.ZERO.bytes.toNat + 1 =
          (sz.bytes.toNat - 1) + 1 + 1 := by
      simp [Miri.ABI.Size.ZERO]; omega
    rw [hfuel, haux_step, hnext1]
    dsimp only [bind, Bind.bind, Except.bind]
    rw [haux_step, hnext2]
    rfl
  have hrng_u :
      (Miri.Memory.InitChunk.Uninit Miri.ABI.Size.ZERO sz).range =
        .ok (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz) := by
    unfold Miri.Memory.InitChunk.range Miri.Memory.AllocRange.fromEndpoints
      Miri.ABI.Size.sub
    have hnot_lt : ¬ sz.bytes < Miri.ABI.Size.ZERO.bytes := by
      simp [Miri.ABI.Size.ZERO, UInt64.lt_iff_toNat_lt]
    have hsub0 : Miri.ABI.Size.ofBytes (sz.bytes - Miri.ABI.Size.ZERO.bytes) =
        sz := by
      cases sz; simp [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes]
    simp [hnot_lt, hsub0, Miri.Memory.allocRange, Except.mapError,
      bind, Except.bind, pure, Except.pure]
  have hfor_one :
      (forIn #[Miri.Memory.InitChunk.Uninit Miri.ABI.Size.ZERO sz] #[]
        (fun (chunk : Miri.Memory.InitChunk) (runs : Array UInt64) => do
          let chunkRange ← chunk.range
          pure (ForInStep.yield (runs.push chunkRange.size.bytes))) :
        Except Miri.Memory.InitMaskError (Array UInt64)) =
        .ok #[sz.bytes] := by
    rw [← Array.forIn_toList]
    change (forIn [Miri.Memory.InitChunk.Uninit Miri.ABI.Size.ZERO sz] #[] _ :
      Except Miri.Memory.InitMaskError (Array UInt64)) = _
    rw [List.forIn_cons]
    simp [hrng_u, Miri.Memory.allocRange, bind, Bind.bind, Except.bind,
      pure, Pure.pure, Except.pure]
  have hc0 :
      (#[Miri.Memory.InitChunk.Uninit Miri.ABI.Size.ZERO sz])[0]? =
        some (.Uninit Miri.ABI.Size.ZERO sz) := rfl
  unfold Miri.Memory.InitMask.prepareCopy
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte, hrange, bind, Bind.bind,
    Except.bind, hcol, hc0]
  simp only [bind, Bind.bind, Except.bind] at hfor_one
  rw [hfor_one]
  rfl

/-- Conversely, for a completely uninitialized indirect enum allocation
(`UninitEnumMemRel`, where `initializationMask = InitMask.new sz false`),
vendored `Miri.Memory.Allocation.copy` (`copyRepeatedly`) sees
`initialized.noBytesInit = true` and takes the `Allocation.writeUninit` fast
path BEFORE checking `sameAllocation && nonoverlapping`, so even self-copy
(`sameAllocation = true`, `nonoverlapping = true`) succeeds with `.ok ()`! -/
theorem UninitEnumMemRel.copy_uninit_self_ok {mach : AnnealMachine}
    {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag}
    {localAlloc : AnnealLocalAlloc}
    (h : UninitEnumMemRel mach ty layouts tagBytes variants mp)
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hlive : LiveAllocEntry mach.memory.live allocId localAlloc) :
    ∃ alloc',
      Miri.Memory.Allocation.copy localAlloc.allocation
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO
          (translateTy ty layouts).layout.size)
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) true true
        localAlloc.allocation = .ok () alloc' := by
  rcases h with ⟨id0, _, _, la0, valid_enum, ptr_prov, _, _, live_entry, _, _,
    _, mut_alloc, _, byteSize_eq, alloc_len_eq, prov_empty, mask_uninit⟩
  rw [ptr_prov] at hprov
  injection hprov with hp; injection hp with hid_eq _; subst hid_eq
  have hla_eq : localAlloc = la0 := by
    have h1 := hlive.1; rw [live_entry.1] at h1
    injection h1 with hmk; exact ((Prod.mk.inj hmk).2).symm
  subst hla_eq
  let sz := (translateTy ty layouts).layout.size
  have htb_pos : 0 < tagBytes := by
    rcases valid_enum.tagBytes_valid with rfl | rfl | rfl | rfl <;> omega
  have hsz_pos : 0 < sz.bytes.toNat :=
    Nat.lt_of_lt_of_le htb_pos valid_enum.size_ge_tag
  have hprep_mask := initMask_new_false_prepareCopy sz hsz_pos
  have hlen_sz : localAlloc.allocation.len = sz.bytes.toNat := by
    rw [alloc_len_eq, byteSize_eq]
  have hslice := lm23_checkedSlice_full hlen_sz byteSize_eq
  unfold Miri.Memory.Allocation.getBytesUnchecked at hslice
  have hlt0 : Miri.ABI.Size.ZERO.bytes.toNat + sz.bytes.toNat < 2 ^ 64 := by
    simp [Miri.ABI.Size.ZERO]; exact UInt64.toNat_lt _
  have hend := lm23_allocRange_endExclusive_of_lt hlt0
  have hfin_eq :
      Miri.ABI.Size.ofBytes (Miri.ABI.Size.ZERO.bytes + sz.bytes) = sz := by
    cases sz; simp [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes]
  rw [hfin_eq] at hend
  have hnz_sz :
      ((Miri.Memory.allocRange Miri.ABI.Size.ZERO sz).size.bytes == 0) =
        false := by
    cases h : ((Miri.Memory.allocRange Miri.ABI.Size.ZERO sz).size.bytes == 0)
    · rfl
    · have hz := eq_of_beq h
      dsimp [Miri.Memory.allocRange] at hz
      rw [hz] at hsz_pos; simp at hsz_pos
  have hmul : (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz).size.mul 1 =
      .ok sz := lm23_size_mul_one sz
  have hprep_prov := lm23_provenanceMap_prepareCopy_new sz
    (lm22AllocRaw localAlloc.allocation)
  unfold lm22AllocRaw at hprep_prov
  rcases localAlloc with ⟨kind, src⟩
  dsimp only at mut_alloc byteSize_eq alloc_len_eq prov_empty mask_uninit hlen_sz hslice hprep_prov ⊢
  cases src using Miri.Memory.Allocation.casesOn with
  | _ srcRaw srcSz srcProv srcMask srcAlign srcMut srcExtra srcNat =>
  change srcRaw.size = sz.bytes.toNat at hlen_sz
  change srcSz = sz at byteSize_eq
  change srcMut = .Mut at mut_alloc
  change srcProv = Miri.Memory.ProvenanceMap.new at prov_empty
  change srcMask = Miri.Memory.InitMask.new sz false at mask_uninit
  change _ = Except.ok (srcRaw.extract 0 sz.bytes.toNat) at hslice
  change (Miri.Memory.ProvenanceMap.new (Prov := AnnealProv)).prepareCopy
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz)
      srcRaw (Miri.ABI.Size.ofBytes 8) = .ok ⟨#[], #[]⟩ at hprep_prov
  subst byteSize_eq mut_alloc prov_empty mask_uninit
  have hset_dst : (Miri.Memory.InitMask.new sz false).setRange
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz) true =
      .ok ⟨.Lazy true, sz⟩ :=
    lm23_initMask_setRange_full (Miri.Memory.InitMask.new sz false)
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz)
      sz true hend rfl (UInt64.le_refl _)
  have hclr_dst := Miri.Memory.ProvenanceMap.clear_new (P := AnnealProv)
    (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz) srcRaw
    (Miri.ABI.Size.ofBytes 8) sz (by decide) hend
  change ∃ alloc',
    Miri.Memory.Allocation.copy _
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz)
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) true true _ =
      .ok () alloc'
  unfold Miri.Memory.Allocation.copy Miri.Memory.Allocation.copyRepeatedly
  rw [hslice]
  dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
  rw [hmul]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hslice]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hprep_prov]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hprep_mask]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  split
  · rename_i _ updated₁ hprep_ovw
    have hu1 : lm23AllocResultTuple (.ok () updated₁) =
        some (srcRaw, sz, Miri.Memory.ProvenanceMap.new,
          ⟨.Lazy true, sz⟩, srcAlign, .Mut, srcExtra, srcNat) := by
      have hpo := hprep_ovw
      with_unfolding_all
        conv at hpo => lhs; whnf
        rw [hslice] at hpo
        dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hpo
        simp only [hnz_sz, Bool.false_eq_true, ↓reduceIte,
          bne_self_eq_false] at hpo
        conv at hpo => lhs; arg 2; whnf
        simp only [hset_dst, Except.mapError] at hpo
        dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure,
          Except.pure] at hpo
        rw [hclr_dst] at hpo
        cases hpo
        rfl
    have hno_init : (Miri.Memory.InitCopy.mk false #[sz.bytes]).noBytesInit =
        true := rfl
    simp only [hno_init, ↓reduceIte]
    have hlen_u1 : updated₁.len = sz.bytes.toNat := by
      cases updated₁ using Miri.Memory.Allocation.casesOn
      simp only [lm23AllocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu1
      rcases hu1 with ⟨hraw₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact hraw₁ ▸ hlen_sz
    have hsz_u1 : updated₁.byteSize = sz := by
      cases updated₁ using Miri.Memory.Allocation.casesOn
      simp only [lm23AllocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu1
      rcases hu1 with ⟨_, rfl, _⟩; rfl
    have hslice_u1 := lm23_checkedSlice_full hlen_u1 hsz_u1
    unfold Miri.Memory.Allocation.getBytesUnchecked at hslice_u1
    have hset_uninit :
        (Miri.Memory.InitMask.mk (.Lazy true) sz).setRange
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz) false =
          .ok (Miri.Memory.InitMask.new sz false) :=
      lm23_initMask_setRange_full _ _ _ false hend rfl (UInt64.le_refl _)
    split
    · rename_i _ _ hwu
      have hwu' := hwu
      cases updated₁ using Miri.Memory.Allocation.casesOn
      simp only [lm23AllocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu1
      rcases hu1 with ⟨hraw₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      cases hraw₁
      with_unfolding_all
        conv at hwu' => lhs; whnf
        rw [hslice_u1] at hwu'
        dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hwu'
        simp only [hnz_sz, Bool.false_eq_true, ↓reduceIte,
          bne_self_eq_false] at hwu'
        conv at hwu' => lhs; arg 2; whnf
        simp only [hset_uninit, Except.mapError] at hwu'
        dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure,
          Except.pure] at hwu'
        rw [hclr_dst] at hwu'
        cases hwu'
    · rename_i updated₂ _
      exact ⟨updated₂, rfl⟩
  · rename_i _ _ hprep_ovw
    have hpo := hprep_ovw
    with_unfolding_all
      conv at hpo => lhs; whnf
      rw [hslice] at hpo
      dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hpo
      simp only [hnz_sz, Bool.false_eq_true, ↓reduceIte,
        bne_self_eq_false] at hpo
      conv at hpo => lhs; arg 2; whnf
      simp only [hset_dst, Except.mapError] at hpo
      dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure,
        Except.pure] at hpo
      rw [hclr_dst] at hpo
      cases hpo

private theorem annealStructMemCopyOp_self_ok
    {ld : List LocalDecl} {ly : LayoutTable}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {srcLay wholeLay : Miri.Interpreter.LocalLayout}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx : Miri.MIR.LocalId}
    {iden : Miri.Interpreter.LocalsIdentity}
    {c : Option Miri.Interpreter.LocalLayout}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag}
    {baseAddr : UInt64}
    {localAlloc : AnnealLocalAlloc}
    {alloc' : Miri.Memory.Allocation AnnealProv
      (Option Miri.TreeBorrows.BorrowTree)}
    {u : Nat}
    (hframes : m.stack.frames = #[tf])
    (hlt : idx < tf.locals.size)
    (hind : tf.locals[idx]'hlt = ⟨.live (.indirect mp), c⟩)
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
    (hlive : LiveAllocEntry m.machine.memory.live allocId localAlloc)
    (hu_lt : u < m.machine.memory.live.size)
    (hfidx : m.machine.memory.live.findIdx? (fun (k, _) => k == allocId) =
      some u)
    (hget : m.machine.memory.live[u]'hu_lt = (allocId, localAlloc))
    (hcopy_ok : Miri.Memory.Allocation.copy localAlloc.allocation
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO wholeLay.layout.size)
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) true true
        localAlloc.allocation = .ok () alloc') :
    annealStructMemCopyOp ld ly ⟨.indirect mp, srcLay⟩
        ⟨.local 0 idx none iden, wholeLay⟩ m =
      .ok ()
        { m with
          machine := updateAllocMachine m.machine u allocId localAlloc.kind
            alloc' } := by
  have hfa := forceAllocation_indirect_none_ok (ld := ld) (ly := ly)
    (iden := iden) (lay := wholeLay) hframes hlt hind
  have hget? : m.machine.memory.live[u]? =
      some (allocId, ⟨localAlloc.kind, localAlloc.allocation⟩) := by
    rw [Array.getElem?_eq_getElem hu_lt, hget]
  have hsub : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr) =
      Miri.ABI.Size.ZERO := by
    rw [hptr]; dsimp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]
    rw [UInt64.sub_self]
  have hsame : (allocId == allocId) = true := beq_self_eq_true allocId
  have hcopy_cond :
      isWholeStructAllocationCopy localAlloc.allocation localAlloc.allocation
        Miri.ABI.Size.ZERO Miri.ABI.Size.ZERO wholeLay.layout.size true =
        false := by
    simp [isWholeStructAllocationCopy]
  unfold annealStructMemCopyOp
  simp only [bind, EStateM.bind, hfa, get, getThe, MonadStateOf.get,
    EStateM.get, set, MonadStateOf.set, EStateM.set,
    hprov, Option.bind, Miri.Memory.Provenance.getAllocId, hbase, hlive.1,
    hfidx, hget?, hsub, hsame, hcopy_cond, Bool.false_eq_true, ↓reduceIte,
    hcopy_ok]
  rfl

/-- Whole-enum self-copy simulation on `.dead` and immediate `.uninit`
(`_idx = Rvalue.Use(copy _idx)` when `idx` is not `.init` and any `.uninit`
local is immediate):
* When `idx` is `.dead`, both machines diagnose `"read of dead local"` UB.
* When `idx` is `.uninit` and immediate (`IsImmediateStepLocal m idx`), both
  machines diagnose `"read of uninitialized local"` UB.
(When `idx` holds `.init (.aggregate v_act fieldVals)`, self-copy hits the
overlapping-range boundary proved in `step_enum_self_copy_overlap_divergence`;
when `idx` is indirect `.uninit`, self-copy hits the raw-byte uninit boundary
proved in `step_enum_copy_move_uninitInd_divergence`.) -/
theorem step_enum_self_copy_dead_or_uninit_simulation
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_3 body env allocBudget s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    (henv_valid : ∀ t tb vs, env t = some (tb, vs) →
      ValidEnumLayout t body.layouts tb vs)
    {bb : BasicBlockData} {stmt : Statement}
    {idx : Local} {decl : LocalDecl}
    {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hkind : stmt.kind = .assign ⟨idx, .nil⟩ (.use (.copy ⟨idx, .nil⟩)))
    (hdecl : get? body.localDecls idx = some decl)
    (henv_idx : env decl.ty = some (tagBytes, variants))
    (hnot_init : ∀ v, get? s.frame.locals idx ≠ some (.init v))
    (huninit_imm :
      get? s.frame.locals idx = some .uninit →
        IsImmediateStepLocal m idx) :
    let mRes :=
      Miri.Interpreter.Step.step
        (annealStepHooksLM2_3 body.localDecls body.layouts) () m
    StepRelLM2_3 body env allocBudget m (stepMirFn body s) mRes ∧
    ((∀ msg, mRes.2 ≠ .error (.undefinedBehavior msg)) →
      (∀ enumId b,
        EnumLocalByteUninit m enumId b →
        EnumLocalByteUninit mRes.1 enumId b) ∧
      (∀ j, j ≠ idx → IsImmediateStepLocal m j →
        IsImmediateStepLocal mRes.1 j)) := by
  intro mRes
  rcases hstate with
    ⟨topFrame, hframes, _, _, hframe, _, hcal, _, _, _, _, _⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hvalid := henv_valid decl.ty tagBytes variants henv_idx
  let wholeLay := translateTy decl.ty body.layouts
  obtain ⟨slot0, mls0, hlt0, hslot0, hmls0_eq, hloc0⟩ :=
    hframe.lookup_local hdecl
  have hcache0 : ∀ l, (topFrame.locals[idx]'hlt0).layout = some l →
      l = wholeLay := by
    rw [hmls0_eq]; exact hloc0.layout_eq
  let tf₀ := cacheFrameLocalLayout topFrame idx hlt0 wholeLay
  let m₀ : AnnealStepState := { m with stack := ⟨#[tf₀]⟩ }
  have heval_dst :
      annealEvalPlace body.localDecls body.layouts ⟨idx, #[]⟩ m =
      .ok ⟨.local 0 idx none topFrame.localsIdentity, wholeLay⟩ m₀ :=
    annealEvalPlace_unprojected hframes hlt0 hdecl hcache0
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 idx none topFrame.localsIdentity, wholeLay⟩
  have huses_mem :
      usesStructMemCopyDest
        ⟨.local 0 idx none topFrame.localsIdentity, wholeLay⟩ = true :=
    usesStructMemCopyDest_true_of_validEnum destPlace rfl hvalid
  have hm_eval :
      Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_3 body.localDecls body.layouts) ()
        (translateStmt stmt) m =
      Miri.Interpreter.runRvalue
        (annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩)
            (some wholeLay) >>=
          fun src =>
            annealStructMemCopyOp body.localDecls body.layouts src destPlace)
        m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    rw [hkind]
    have hlm23_asgn :
        lm23Assign body.localDecls body.layouts ⟨idx, #[]⟩
          (.Use (.Copy ⟨idx, #[]⟩) .No) = false := rfl
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
      translateRvalue, translateOperand, annealStepHooksLM2_3]
    change (if lm23Assign body.localDecls body.layouts ⟨idx, #[]⟩
        (.Use (.Copy ⟨idx, #[]⟩) .No) then _ else _) = _
    rw [hlm23_asgn]
    simp only [Bool.false_eq_true, ↓reduceIte, annealStepHooksLM2_2]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooksLM2_2
    rw [EStateM.bind_eq_ok heval_dst]
    dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt, destPlace]
    simp only [huses_mem, ↓reduceIte]
  have hlt_tf₀ : idx < tf₀.locals.size := by
    dsimp [tf₀]; rw [cacheFrameLocalLayout_size]; exact hlt0
  have htf₀_self : tf₀.locals[idx]'hlt_tf₀ = ⟨mls0.value, some wholeLay⟩ := by
    have h? : tf₀.locals[idx]? = some ⟨mls0.value, some wholeLay⟩ := by
      dsimp only [tf₀, cacheFrameLocalLayout]
      rw [Array.getElem?_set_self hlt0, hmls0_eq]
    rw [Array.getElem?_eq_getElem hlt_tf₀] at h?
    exact Option.some.inj h?
  have hcache_tf₀ :
      ∀ l, (some wholeLay : Option Miri.Interpreter.LocalLayout) = some l →
        l = wholeLay := fun _ h => (Option.some.inj h).symm
  cases hloc0 with
  | base _ _ hnone _ => rw [henv_idx] at hnone; cases hnone
  | enumDead _ _ _ _ _ _ =>
    have ha_ub : evalStmt s stmt body.localDecls body.layouts =
        MirStepNode.fail .ub := by
      unfold evalStmt; rw [hkind]; simp [evalRvalue, evalOperand, hslot0]
    obtain ⟨m_err, hm_op_err⟩ :
        ∃ m_err,
          annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩)
            (some wholeLay) m₀ =
          .error (.undefinedBehavior "read of dead local") m_err :=
      ⟨_, annealEvalOperand_copy_dead (known := some wholeLay)
        (m := m₀) rfl hlt_tf₀ hdecl htf₀_self hcache_tf₀⟩
    have hm_ub :
        Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_3 body.localDecls body.layouts) ()
          (translateStmt stmt) m =
        (m_err, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_eval]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_error hm_op_err]
    dsimp only [mRes]
    rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq
      hframe.location_eq hbb hstmt hm_ub]
    exact ⟨.ub _ _, fun hno => False.elim (hno _ rfl)⟩
  | enumUninitInd _ _ srcMp_u c_s _ _ _ =>
    have himm_s := huninit_imm hslot0 topFrame hframes
    have hmls_top : topFrame.locals[idx]? =
        some ⟨.live (.indirect srcMp_u), c_s⟩ := by
      rw [Array.getElem?_eq_getElem hlt0, hmls0_eq]
    exact False.elim (himm_s _ hmls_top srcMp_u rfl)
  | enumUninitImm _ _ _ _ _ _ =>
    have ha_ub : evalStmt s stmt body.localDecls body.layouts =
        MirStepNode.fail .ub := by
      unfold evalStmt; rw [hkind]; simp [evalRvalue, evalOperand, hslot0]
    obtain ⟨m_err, hm_op_ok⟩ :
        ∃ m_err,
          annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩)
            (some wholeLay) m₀ =
          .ok ⟨.immediate .uninit, wholeLay⟩ m_err :=
      ⟨_, annealEvalOperand_copy_live (known := some wholeLay)
        (m := m₀) rfl hlt_tf₀ hdecl htf₀_self hcache_tf₀⟩
    have hm_ub :
        Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_3 body.localDecls body.layouts) ()
          (translateStmt stmt) m =
        (m_err, .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_eval]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hm_op_ok]; rfl
    dsimp only [mRes]
    rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq
      hframe.location_eq hbb hstmt hm_ub]
    exact ⟨.ub _ _, fun hno => False.elim (hno _ rfl)⟩
  | enumInd _ _ v_act fieldVals _ _ _ _ _ =>
    exact False.elim (hnot_init (.aggregate v_act fieldVals) hslot0)

/-- Whole-enum self-copy overlapping-range divergence
(`_idx = Rvalue.Use(copy _idx)` when `idx` holds `.init rootVal` on a
multi-variant enum):
* Anneal's pure value-tree semantics reads `rootVal` from `s.frame.locals[idx]`
  and writes `.init rootVal` back (`MirStepNode.step`).
* Unlike `SimLM2_2.step_assign_self_copy_memory_struct_divergence` (which takes
  an external `hcopy_err` hypothesis), `EnumMemRel.copy_self_overlap_err`
  proves unconditionally from `StateRelLM2_3` that every initialized
  multi-variant direct-tagged enum allocation has `0 < tagBytes ≤ size` and an
  initialized tag byte `0`, so vendored `lean-miri`'s nonoverlapping
  `Miri.Memory.Allocation.copy` (`sameAllocation = true`,
  `nonoverlapping = true`) ALWAYS raises
  `.error (.undefinedBehavior "whole-value copy between overlapping ranges")`.
  (Rustc MIR forbids overlapping `Operand::Copy` -> destination `Assign`.) -/
theorem step_enum_self_copy_overlap_divergence
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_3 body env allocBudget s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    (henv_valid : ∀ t tb vs, env t = some (tb, vs) →
      ValidEnumLayout t body.layouts tb vs)
    {bb : BasicBlockData} {stmt : Statement}
    {idx : Local} {decl : LocalDecl} {rootVal : Value}
    {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hkind : stmt.kind = .assign ⟨idx, .nil⟩ (.use (.copy ⟨idx, .nil⟩)))
    (hdecl : get? body.localDecls idx = some decl)
    (henv_idx : env decl.ty = some (tagBytes, variants))
    (hslot : get? s.frame.locals idx = some (.init rootVal)) :
    stepMirFn body s =
      MirStepNode.step
        (advanceStmt s (s.frame.locals.set idx (.init rootVal)) s.memory) ∧
    ∃ m_err,
      Miri.Interpreter.Step.step
        (annealStepHooksLM2_3 body.localDecls body.layouts) () m =
      (m_err,
        .error
          (.undefinedBehavior "whole-value copy between overlapping ranges")) := by
  rcases hstate with
    ⟨topFrame, hframes, _, _, hframe, _, hcal, _, hbor, hprot, hcaller, _⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hvalid := henv_valid decl.ty tagBytes variants henv_idx
  let wholeLay := translateTy decl.ty body.layouts
  obtain ⟨slot0, mls0, hlt0, hslot0, hmls0_eq, hloc0⟩ :=
    hframe.lookup_local hdecl
  have hlt_af0 : idx < s.frame.locals.length := by
    unfold get? at hslot0
    exact (List.getElem?_eq_some_iff.mp hslot0).1
  rw [hslot] at hslot0
  injection hslot0 with hsl; subst hsl
  have ha_ok :
      evalStmt s stmt body.localDecls body.layouts =
      MirStepNode.step
        (advanceStmt s (s.frame.locals.set idx (.init rootVal)) s.memory) := by
    unfold evalStmt; rw [hkind]; dsimp only
    rw [evalRvalue_use_nil_borrows_lm2_3 _ _ _ hbor, hcaller]
    have hev :
        evalOperand s.frame.locals (.copy ⟨idx, .nil⟩) .nil s.memory.globals
          body.layouts .nil body.localDecls = .ok rootVal s.frame.locals := by
      simp [evalOperand, readProjectedValue, hslot]
    rw [hev]; dsimp only
    rw [hvalid.validateLoadedValue_unproj hdecl (Or.inl rfl)]; dsimp only
    simp only [hprot, hbor, invalidateConflictingBorrows, hslot]
    rw [set?_eq_some_set hlt_af0 (.init rootVal)]
    apply congrArg (fun mem =>
      MirStepNode.step
        (advanceStmt s (s.frame.locals.set idx (.init rootVal)) mem))
    rcases hm : s.memory with ⟨_, _, bor, _, _, _, _, prot, _, _⟩
    rw [hm] at hbor hprot
    dsimp only at hbor hprot
    subst hbor hprot
    rfl
  refine ⟨ha_ok, ?_⟩
  have hcache0 : ∀ l, (topFrame.locals[idx]'hlt0).layout = some l →
      l = wholeLay := by
    rw [hmls0_eq]; exact hloc0.layout_eq
  let tf₀ := cacheFrameLocalLayout topFrame idx hlt0 wholeLay
  let m₀ : AnnealStepState := { m with stack := ⟨#[tf₀]⟩ }
  have heval_dst :
      annealEvalPlace body.localDecls body.layouts ⟨idx, #[]⟩ m =
      .ok ⟨.local 0 idx none topFrame.localsIdentity, wholeLay⟩ m₀ :=
    annealEvalPlace_unprojected hframes hlt0 hdecl hcache0
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 idx none topFrame.localsIdentity, wholeLay⟩
  have huses_mem :
      usesStructMemCopyDest
        ⟨.local 0 idx none topFrame.localsIdentity, wholeLay⟩ = true :=
    usesStructMemCopyDest_true_of_validEnum destPlace rfl hvalid
  have hm_eval :
      Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_3 body.localDecls body.layouts) ()
        (translateStmt stmt) m =
      Miri.Interpreter.runRvalue
        (annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩)
            (some wholeLay) >>=
          fun src =>
            annealStructMemCopyOp body.localDecls body.layouts src destPlace)
        m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    rw [hkind]
    have hlm23_asgn :
        lm23Assign body.localDecls body.layouts ⟨idx, #[]⟩
          (.Use (.Copy ⟨idx, #[]⟩) .No) = false := rfl
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
      translateRvalue, translateOperand, annealStepHooksLM2_3]
    change (if lm23Assign body.localDecls body.layouts ⟨idx, #[]⟩
        (.Use (.Copy ⟨idx, #[]⟩) .No) then _ else _) = _
    rw [hlm23_asgn]
    simp only [Bool.false_eq_true, ↓reduceIte, annealStepHooksLM2_2]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooksLM2_2
    rw [EStateM.bind_eq_ok heval_dst]
    dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt, destPlace]
    simp only [huses_mem, ↓reduceIte]
  cases hloc0 with
  | base _ _ hnone _ => rw [henv_idx] at hnone; cases hnone
  | enumInd tb_s vs_s v_act fieldVals mp c_s henv_s _ hemr =>
    rw [henv_idx] at henv_s
    injection henv_s with hp_s; rcases hp_s with ⟨rfl, rfl⟩
    have hemr_copy := hemr
    rcases hemr with ⟨allocId, tag_s, baseAddr, localAlloc, _, _, _, _,
      hprov, _, _, hlive, hbase, hptr, _, _, _, _, _, _, _, _, _, _, _, _⟩
    obtain ⟨hfind, u, hu_lt, hfidx, hget⟩ := hlive
    have hlive' : LiveAllocEntry m.machine.memory.live allocId localAlloc :=
      ⟨hfind, u, hu_lt, hfidx, hget⟩
    obtain ⟨alloc', herr⟩ :=
      hemr_copy.copy_self_overlap_err hprov hlive'
    have hlt_tf₀ : idx < tf₀.locals.size := by
      dsimp [tf₀]; rw [cacheFrameLocalLayout_size]; exact hlt0
    have htf₀_self :
        tf₀.locals[idx]'hlt_tf₀ = ⟨.live (.indirect mp), some wholeLay⟩ := by
      have h? : tf₀.locals[idx]? =
          some ⟨.live (.indirect mp), some wholeLay⟩ := by
        dsimp only [tf₀, cacheFrameLocalLayout]
        rw [Array.getElem?_set_self hlt0, hmls0_eq]
      rw [Array.getElem?_eq_getElem hlt_tf₀] at h?
      exact Option.some.inj h?
    let tf₁ := cacheFrameLocalLayout tf₀ idx hlt_tf₀ wholeLay
    have hm_op :
        annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩)
          (some wholeLay) m₀ =
        .ok ⟨.indirect mp, wholeLay⟩ { m with stack := ⟨#[tf₁]⟩ } :=
      annealEvalOperand_copy_live (known := some wholeLay)
        (m := m₀) rfl hlt_tf₀ hdecl htf₀_self
        (fun _ h => (Option.some.inj h).symm)
    have hlt_tf₁ : idx < tf₁.locals.size := by
      dsimp [tf₁]; rw [cacheFrameLocalLayout_size]; exact hlt_tf₀
    have htf₁_self :
        tf₁.locals[idx]'hlt_tf₁ = ⟨.live (.indirect mp), some wholeLay⟩ := by
      have h? : tf₁.locals[idx]? =
          some ⟨.live (.indirect mp), some wholeLay⟩ := by
        dsimp only [tf₁, cacheFrameLocalLayout]
        rw [Array.getElem?_set_self hlt_tf₀, htf₀_self]
      rw [Array.getElem?_eq_getElem hlt_tf₁] at h?
      exact Option.some.inj h?
    have hcp_err := annealStructMemCopyOp_overlap_ub
      (ld := body.localDecls) (ly := body.layouts)
      (srcLay := wholeLay) (wholeLay := wholeLay)
      (iden := topFrame.localsIdentity)
      (m := { m with stack := ⟨#[tf₁]⟩ })
      rfl hlt_tf₁ htf₁_self hprov hbase hptr hlive' hu_lt hfidx hget herr
    have hm_ub :
        Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_3 body.localDecls body.layouts) ()
          (translateStmt stmt) m =
        ({ m with stack := ⟨#[tf₁]⟩ },
          .error
            (.undefinedBehavior
              "whole-value copy between overlapping ranges")) := by
      rw [hm_eval]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hm_op]; simp only [destPlace, hcp_err]
    exact ⟨_, miri_step_at_statement_error _ hframes hframe.body_eq
      hframe.location_eq hbb hstmt hm_ub⟩

/-- Indirect-uninitialized whole-enum copy/move divergence
(`_dst = Rvalue.Use(copy/move _src)` when `_src` is in
`LocalRelLM2_3.enumUninitInd` — i.e., `.uninit` in Anneal and backed by an
uninitialized indirect stack allocation `¬ IsImmediateStepLocal m srcIdx` in
`lean-miri` — and `_dst` is live):
* Anneal's typed local-slot evaluator (`evalOperand`) checks
  `get? s.frame.locals srcIdx = some .uninit` and fails with
  `MirStepNode.fail .ub`.
* Vendored `lean-miri`'s untyped byte-level memory copy copies the
  uninitialized `InitMask.new sz false` bytes without reading any scalar value,
  stepping `(m', .ok true)` across **all four** combinations of
  `(srcIdx ≠ dstIdx ∨ srcIdx = dstIdx) × (isMove = false ∨ isMove = true)` —
  including self-copy (`srcIdx = dstIdx`, `isMove = false`), where
  `UninitEnumMemRel.copy_uninit_self_ok` takes `copyRepeatedly`'s
  `initialized.noBytesInit` (`Allocation.writeUninit`) fast path before the
  `copyRangesOverlap` check!
This proves that the `IsImmediateStepLocal m srcIdx` hypothesis in
`step_enum_copy_move_simulation`, `step_enum_self_move_simulation`, and
`step_enum_self_copy_dead_or_uninit_simulation` is exact and sharp. -/
theorem step_enum_copy_move_uninitInd_divergence
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_3 body env (allocBudget + 1) s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    (henv_valid : ∀ t tb vs, env t = some (tb, vs) →
      ValidEnumLayout t body.layouts tb vs)
    {bb : BasicBlockData} {stmt : Statement}
    {dstIdx srcIdx : Local} {dstDecl srcDecl : LocalDecl}
    {isMove : Bool} {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hkind : stmt.kind = .assign ⟨dstIdx, .nil⟩
      (.use (if isMove then .move ⟨srcIdx, .nil⟩ else .copy ⟨srcIdx, .nil⟩)))
    (hsrc_decl : get? body.localDecls srcIdx = some srcDecl)
    (hdst_decl : get? body.localDecls dstIdx = some dstDecl)
    (henv_src : env srcDecl.ty = some (tagBytes, variants))
    (hdst_ty : dstDecl.ty = srcDecl.ty)
    (hsrc_uninit : get? s.frame.locals srcIdx = some .uninit)
    (hsrc_not_imm : ¬ IsImmediateStepLocal m srcIdx)
    (hdst_not_dead : get? s.frame.locals dstIdx ≠ some .dead) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step
        (annealStepHooksLM2_3 body.localDecls body.layouts) () m =
      (m', .ok true) := by
  rcases hstate with
    ⟨topFrame, hframes, _, _, hframe, halloc, hcal, _, _, _, _, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have ha_ub : evalStmt s stmt body.localDecls body.layouts =
      MirStepNode.fail .ub := by
    unfold evalStmt; rw [hkind]
    cases isMove <;> simp [evalRvalue, evalOperand, hsrc_uninit]
  refine ⟨ha_ub, ?_⟩
  have hvalid := henv_valid srcDecl.ty tagBytes variants henv_src
  have henv_dst : env dstDecl.ty = some (tagBytes, variants) := by
    rw [hdst_ty]; exact henv_src
  let wholeLay := translateTy srcDecl.ty body.layouts
  have hlay_dst : translateTy dstDecl.ty body.layouts = wholeLay := by
    rw [hdst_ty]
  let op : MirAst.Operand :=
    if isMove then .move ⟨srcIdx, .nil⟩ else .copy ⟨srcIdx, .nil⟩
  have hlm23_op : lm23Operand (translateOperand op) = false := by
    cases isMove <;> rfl
  have hlm23_asgn :
      lm23Assign body.localDecls body.layouts ⟨dstIdx, #[]⟩
        (.Use (translateOperand op) .No) = false := by
    unfold lm23Assign; simp [hlm23_op]
  obtain ⟨slot_d0, mls_d0, hlt_d0, hslot_d0, hmls_d0_eq, hloc_d0⟩ :=
    hframe.lookup_local hdst_decl
  have hcache_d0 : ∀ l, (topFrame.locals[dstIdx]'hlt_d0).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d0_eq]; exact hloc_d0.layout_eq
  let tf₀ := cacheFrameLocalLayout topFrame dstIdx hlt_d0 wholeLay
  let m₀ : AnnealStepState := { m with stack := ⟨#[tf₀]⟩ }
  have heval_dst :
      annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ m =
      .ok ⟨.local 0 dstIdx none topFrame.localsIdentity, wholeLay⟩ m₀ := by
    have hp := annealEvalPlace_unprojected hframes hlt_d0 hdst_decl hcache_d0
    simpa only [hlay_dst] using hp
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 dstIdx none topFrame.localsIdentity, wholeLay⟩
  have huses_mem :
      usesStructMemCopyDest
        ⟨.local 0 dstIdx none topFrame.localsIdentity, wholeLay⟩ = true :=
    usesStructMemCopyDest_true_of_validEnum destPlace rfl hvalid
  have hm_eval :
      Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_3 body.localDecls body.layouts) ()
        (translateStmt stmt) m =
      Miri.Interpreter.runRvalue
        (annealEvalOperand body.localDecls body.layouts (translateOperand op)
            (some wholeLay) >>=
          fun src =>
            annealStructMemCopyOp body.localDecls body.layouts src destPlace)
        m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    rw [hkind]
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
      translateRvalue, annealStepHooksLM2_3]
    change (if lm23Assign body.localDecls body.layouts ⟨dstIdx, #[]⟩
        (.Use (translateOperand op) .No) then _ else _) = _
    rw [hlm23_asgn]
    simp only [Bool.false_eq_true, ↓reduceIte, annealStepHooksLM2_2]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooksLM2_2
    rw [EStateM.bind_eq_ok heval_dst]
    dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt, destPlace]
    simp only [huses_mem, ↓reduceIte]
    rfl
  obtain ⟨slot_s_top, mls_s_top, hlt_s_top, hslot_s_top, hmls_s_top_eq,
      hloc_s_top⟩ := hframe.lookup_local hsrc_decl
  rw [hsrc_uninit] at hslot_s_top
  injection hslot_s_top with hs_eq; subst hs_eq
  have hfr₀ : FrameRelLM2_3 body env m.machine s.frame tf₀ := by
    simpa only [tf₀, wholeLay, ← hlay_dst] using
      hframe.cache_local_layout hdst_decl hlt_d0
  have hdisj₀ : MemoryAllocDisjoint tf₀ :=
    MemoryAllocDisjoint_cacheFrameLocalLayout hdisj hlt_d0 wholeLay
  have hlt_s0 : srcIdx < tf₀.locals.size := by
    dsimp [tf₀]; rw [cacheFrameLocalLayout_size]; exact hlt_s_top
  cases hloc_s_top with
  | base _ _ hnone _ => rw [henv_src] at hnone; cases hnone
  | enumUninitImm _ _ c_top _ _ _ =>
    exfalso; apply hsrc_not_imm
    intro tf' hf' mls' hget' mp' hcontr
    rw [hframes] at hf'
    injection hf' with ha; injection ha with ht; subst ht
    rw [Array.getElem?_eq_getElem hlt_s_top, hmls_s_top_eq] at hget'
    injection hget' with hm_eq; subst hm_eq; cases hcontr
  | enumUninitInd tb_s vs_s srcMp c_top henv_s hc_top humpr_s =>
    rw [henv_src] at henv_s
    injection henv_s with hp_s; rcases hp_s with ⟨rfl, rfl⟩
    have humpr_copy := humpr_s
    rcases humpr_s with ⟨srcId, tag_s, srcBase, srcLocal, _, hprov_s, _, _,
      hlive_s, hbase_s, hptr_s, _, _, _, hbs_s, _, _, _⟩
    have htf₀_src :
        ∃ c_s0, tf₀.locals[srcIdx]'hlt_s0 = ⟨.live (.indirect srcMp), c_s0⟩ ∧
          (∀ l, c_s0 = some l → l = wholeLay) := by
      by_cases hsd : dstIdx = srcIdx
      · subst hsd
        have h? : tf₀.locals[dstIdx]? =
            some ⟨.live (.indirect srcMp), some wholeLay⟩ := by
          dsimp only [tf₀, cacheFrameLocalLayout]
          rw [Array.getElem?_set_self hlt_d0, hmls_s_top_eq]
        rw [Array.getElem?_eq_getElem hlt_s0] at h?
        exact ⟨some wholeLay, Option.some.inj h?,
          fun _ h => (Option.some.inj h).symm⟩
      · have h? : tf₀.locals[srcIdx]? =
            some ⟨.live (.indirect srcMp), c_top⟩ := by
          dsimp only [tf₀, cacheFrameLocalLayout]
          rw [Array.getElem?_set_ne _ hsd,
            Array.getElem?_eq_getElem hlt_s_top, hmls_s_top_eq]
        rw [Array.getElem?_eq_getElem hlt_s0] at h?
        exact ⟨c_top, Option.some.inj h?,
          fun l hl => hc_top l (Option.mem_def.mpr hl)⟩
    obtain ⟨c_s0, hmls_s0_eq, hc_s0⟩ := htf₀_src
    have htf₀_dst : tf₀.locals[dstIdx]? = some ⟨mls_d0.value, some wholeLay⟩ := by
      dsimp only [tf₀, cacheFrameLocalLayout]
      rw [Array.getElem?_set_self hlt_d0, hmls_d0_eq]
    have hmls_s0? : tf₀.locals[srcIdx]? =
        some ⟨.live (.indirect srcMp), c_s0⟩ := by
      rw [Array.getElem?_eq_getElem hlt_s0, hmls_s0_eq]
    -- Helper: run `annealStructMemCopyOp` when `tf₁.locals[dstIdx]` is
    -- `.live (.immediate .uninit)`:
    have hfinish_uninitImm :
        ∀ (tf₁ : Miri.Interpreter.Frame AnnealProv
            Miri.Interpreter.LocalLayout Unit)
          (hlt_d1 : dstIdx < tf₁.locals.size),
          annealEvalOperand body.localDecls body.layouts (translateOperand op)
            (some wholeLay) m₀ =
            .ok ⟨.indirect srcMp, wholeLay⟩ { m with stack := ⟨#[tf₁]⟩ } →
          tf₁.location = topFrame.location →
          tf₁.locals[dstIdx]'hlt_d1 =
            ⟨.live (.immediate .uninit), some wholeLay⟩ →
          ∃ m',
            Miri.Interpreter.Step.step
              (annealStepHooksLM2_3 body.localDecls body.layouts) () m =
            (m', .ok true) := by
      intro tf₁ hlt_d1 hm_op hloc₁ hd1
      have hsized_w : wholeLay.layout.isSized = true := hvalid.isSized_true
      obtain ⟨rawAlloc, htry, hbs0, _, hmut0, _, _⟩ :=
        tryNew_uninit_of_pow2_le_29 wholeLay.layout.size
          wholeLay.layout.align.abi hvalid.align_pow2_le
      obtain ⟨mem', newId, hres, _, hlive_eq, hfresh_old, _, _⟩ :=
        (halloc.of_succ).reserve_step
      have hfresh : mem'.live.any (fun entry => entry.1 == newId) = false := by
        rw [hlive_eq]; exact hfresh_old
      have hcp_ok := annealStructMemCopyOp_uninitImm_ok
        (ld := body.localDecls) (ly := body.layouts)
        (srcLay := wholeLay) (iden := topFrame.localsIdentity)
        (m := { m with stack := ⟨#[tf₁]⟩ })
        rfl hlt_d1 hd1 hsized_w htry hbs0 hmut0 hres hfresh
        hprov_s hbase_s hptr_s hlive_s hbs_s
      obtain ⟨tf_end, mach_end, hm_ok, hloc_end⟩ :
          ∃ tf_end mach_end,
            Miri.Interpreter.Step.evalStatement
              (annealStepHooksLM2_3 body.localDecls body.layouts) ()
              (translateStmt stmt) m =
              (⟨⟨#[tf_end]⟩, mach_end⟩, .ok ()) ∧
            tf_end.location = topFrame.location := by
        rw [hm_eval]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hm_op, hcp_ok]; exact ⟨_, _, rfl, hloc₁⟩
      exact ⟨_, miri_step_at_statement_ok _ hframes hframe.body_eq
        hframe.location_eq hbb hstmt hm_ok rfl
        (hloc_end.trans hframe.location_eq)⟩
    cases isMove with
    | true =>
      let tf_c := cacheFrameLocalLayout tf₀ srcIdx hlt_s0 wholeLay
      have hlt_c : srcIdx < tf_c.locals.size := by
        dsimp [tf_c]; rw [cacheFrameLocalLayout_size]; exact hlt_s0
      let tf₁ := deinitFrameLocal tf_c srcIdx hlt_c
      have hm_op :
          annealEvalOperand body.localDecls body.layouts (translateOperand op)
            (some wholeLay) m₀ =
          .ok ⟨.indirect srcMp, wholeLay⟩ { m with stack := ⟨#[tf₁]⟩ } :=
        annealEvalOperand_move_live (known := some wholeLay)
          (m := m₀) rfl hlt_s0 hsrc_decl hmls_s0_eq hc_s0
      have hlt_d1 : dstIdx < tf₁.locals.size := by
        dsimp [tf₁, deinitFrameLocal, tf_c, tf₀]
        rw [Array.size_set, cacheFrameLocalLayout_size,
          cacheFrameLocalLayout_size]
        exact hlt_d0
      by_cases hsd : srcIdx = dstIdx
      · subst hsd
        have hd1 :
            tf₁.locals[srcIdx]'hlt_d1 =
              ⟨.live (.immediate .uninit), some wholeLay⟩ := by
          have h? : tf₁.locals[srcIdx]? =
              some ⟨.live (.immediate .uninit), some wholeLay⟩ := by
            dsimp only [tf₁, deinitFrameLocal]
            rw [Array.getElem?_set_self hlt_c]
            have hc? : tf_c.locals[srcIdx]? =
                some ⟨.live (.indirect srcMp), some wholeLay⟩ := by
              dsimp only [tf_c, cacheFrameLocalLayout]
              rw [Array.getElem?_set_self hlt_s0, hmls_s0_eq]
            rw [Array.getElem?_eq_getElem hlt_c] at hc?
            rw [Option.some.inj hc?]
          rw [Array.getElem?_eq_getElem hlt_d1] at h?
          exact Option.some.inj h?
        exact hfinish_uninitImm tf₁ hlt_d1 hm_op rfl hd1
      · have hd1 : tf₁.locals[dstIdx]'hlt_d1 = ⟨mls_d0.value, some wholeLay⟩ := by
          have h? : tf₁.locals[dstIdx]? = some ⟨mls_d0.value, some wholeLay⟩ := by
            dsimp only [tf₁, deinitFrameLocal]
            rw [Array.getElem?_set_ne _ hsd]
            dsimp only [tf_c, cacheFrameLocalLayout]
            rw [Array.getElem?_set_ne _ hsd]
            exact htf₀_dst
          rw [Array.getElem?_eq_getElem hlt_d1] at h?
          exact Option.some.inj h?
        cases hloc_d0 with
        | base _ _ hn _ => rw [henv_dst] at hn; cases hn
        | enumDead _ _ _ _ _ _ => exact False.elim (hdst_not_dead hslot_d0)
        | enumUninitImm _ _ _ _ _ _ =>
          exact hfinish_uninitImm tf₁ hlt_d1 hm_op rfl hd1
        | enumUninitInd _ _ destMp _ _ _ humpr_d =>
          rcases humpr_d with ⟨destId, tag_d, destBase, destLocal, _, hprov_d,
            _, _, hlive_d, hbase_d, hptr_d, _, hmut_d, _, hbs_d, _, _, _⟩
          obtain ⟨hfind_d, u, hu_lt, hfidx_d, hget_d⟩ := hlive_d
          have hne_id : srcId ≠ destId := by
            have hne_p := hdisj₀ srcIdx dstIdx srcMp destMp c_s0 (some wholeLay)
              hsd hmls_s0? htf₀_dst
            rw [hprov_s, hprov_d] at hne_p
            intro rfl; exact hne_p rfl
          have hcp_ok := annealStructMemCopyOp_indirect_ok
            (ld := body.localDecls) (ly := body.layouts)
            (srcLay := wholeLay) (wholeLay := wholeLay)
            (iden := topFrame.localsIdentity)
            (m := { m with stack := ⟨#[tf₁]⟩ })
            rfl hlt_d1 hd1 hne_id hprov_s hbase_s hptr_s hlive_s hbs_s
            hprov_d hbase_d hptr_d hu_lt hfidx_d hget_d
            (by simpa only [hlay_dst] using hbs_d) hmut_d
          obtain ⟨tf_end, mach_end, hm_ok, hloc_end⟩ :
              ∃ tf_end mach_end,
                Miri.Interpreter.Step.evalStatement
                  (annealStepHooksLM2_3 body.localDecls body.layouts) ()
                  (translateStmt stmt) m =
                  (⟨⟨#[tf_end]⟩, mach_end⟩, .ok ()) ∧
                tf_end.location = topFrame.location := by
            rw [hm_eval]; unfold Miri.Interpreter.runRvalue
            rw [EStateM.bind_eq_ok hm_op, hcp_ok]; exact ⟨_, _, rfl, rfl⟩
          exact ⟨_, miri_step_at_statement_ok _ hframes hframe.body_eq
            hframe.location_eq hbb hstmt hm_ok rfl
            (hloc_end.trans hframe.location_eq)⟩
        | enumInd _ _ _ _ destMp _ _ _ hemr_d =>
          rcases hemr_d with ⟨destId, tag_d, destBase, destLocal, _, _, _, _,
            hprov_d, _, _, hlive_d, hbase_d, hptr_d, _, hmut_d, _, hbs_d,
            _, _, _, _, _, _, _, _⟩
          obtain ⟨hfind_d, u, hu_lt, hfidx_d, hget_d⟩ := hlive_d
          have hne_id : srcId ≠ destId := by
            have hne_p := hdisj₀ srcIdx dstIdx srcMp destMp c_s0 (some wholeLay)
              hsd hmls_s0? htf₀_dst
            rw [hprov_s, hprov_d] at hne_p
            intro rfl; exact hne_p rfl
          have hcp_ok := annealStructMemCopyOp_indirect_ok
            (ld := body.localDecls) (ly := body.layouts)
            (srcLay := wholeLay) (wholeLay := wholeLay)
            (iden := topFrame.localsIdentity)
            (m := { m with stack := ⟨#[tf₁]⟩ })
            rfl hlt_d1 hd1 hne_id hprov_s hbase_s hptr_s hlive_s hbs_s
            hprov_d hbase_d hptr_d hu_lt hfidx_d hget_d
            (by simpa only [hlay_dst] using hbs_d) hmut_d
          obtain ⟨tf_end, mach_end, hm_ok, hloc_end⟩ :
              ∃ tf_end mach_end,
                Miri.Interpreter.Step.evalStatement
                  (annealStepHooksLM2_3 body.localDecls body.layouts) ()
                  (translateStmt stmt) m =
                  (⟨⟨#[tf_end]⟩, mach_end⟩, .ok ()) ∧
                tf_end.location = topFrame.location := by
            rw [hm_eval]; unfold Miri.Interpreter.runRvalue
            rw [EStateM.bind_eq_ok hm_op, hcp_ok]; exact ⟨_, _, rfl, rfl⟩
          exact ⟨_, miri_step_at_statement_ok _ hframes hframe.body_eq
            hframe.location_eq hbb hstmt hm_ok rfl
            (hloc_end.trans hframe.location_eq)⟩
    | false =>
      let tf₁ := cacheFrameLocalLayout tf₀ srcIdx hlt_s0 wholeLay
      have hm_op :
          annealEvalOperand body.localDecls body.layouts (translateOperand op)
            (some wholeLay) m₀ =
          .ok ⟨.indirect srcMp, wholeLay⟩ { m with stack := ⟨#[tf₁]⟩ } :=
        annealEvalOperand_copy_live (known := some wholeLay)
          (m := m₀) rfl hlt_s0 hsrc_decl hmls_s0_eq hc_s0
      have hlt_d1 : dstIdx < tf₁.locals.size := by
        dsimp [tf₁, tf₀]
        rw [cacheFrameLocalLayout_size, cacheFrameLocalLayout_size]
        exact hlt_d0
      by_cases hsd : srcIdx = dstIdx
      · subst hsd
        have hd1 :
            tf₁.locals[srcIdx]'hlt_d1 =
              ⟨.live (.indirect srcMp), some wholeLay⟩ := by
          have h? : tf₁.locals[srcIdx]? =
              some ⟨.live (.indirect srcMp), some wholeLay⟩ := by
            dsimp only [tf₁, cacheFrameLocalLayout]
            rw [Array.getElem?_set_self hlt_s0, hmls_s0_eq]
          rw [Array.getElem?_eq_getElem hlt_d1] at h?
          exact Option.some.inj h?
        obtain ⟨hfind_s, u, hu_lt, hfidx_s, hget_s⟩ := hlive_s
        have hlive_s' : LiveAllocEntry m.machine.memory.live srcId srcLocal :=
          ⟨hfind_s, u, hu_lt, hfidx_s, hget_s⟩
        obtain ⟨alloc', hcopy_self⟩ :=
          humpr_copy.copy_uninit_self_ok hprov_s hlive_s'
        have hcp_ok := annealStructMemCopyOp_self_ok
          (ld := body.localDecls) (ly := body.layouts)
          (srcLay := wholeLay) (wholeLay := wholeLay)
          (iden := topFrame.localsIdentity)
          (m := { m with stack := ⟨#[tf₁]⟩ })
          rfl hlt_d1 hd1 hprov_s hbase_s hptr_s hlive_s' hu_lt hfidx_s hget_s
          hcopy_self
        obtain ⟨tf_end, mach_end, hm_ok, hloc_end⟩ :
            ∃ tf_end mach_end,
              Miri.Interpreter.Step.evalStatement
                (annealStepHooksLM2_3 body.localDecls body.layouts) ()
                (translateStmt stmt) m =
                (⟨⟨#[tf_end]⟩, mach_end⟩, .ok ()) ∧
              tf_end.location = topFrame.location := by
          rw [hm_eval]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hm_op, hcp_ok]; exact ⟨_, _, rfl, rfl⟩
        exact ⟨_, miri_step_at_statement_ok _ hframes hframe.body_eq
          hframe.location_eq hbb hstmt hm_ok rfl
          (hloc_end.trans hframe.location_eq)⟩
      · have hd1 : tf₁.locals[dstIdx]'hlt_d1 = ⟨mls_d0.value, some wholeLay⟩ := by
          have h? : tf₁.locals[dstIdx]? = some ⟨mls_d0.value, some wholeLay⟩ := by
            dsimp only [tf₁, cacheFrameLocalLayout]
            rw [Array.getElem?_set_ne _ hsd]
            exact htf₀_dst
          rw [Array.getElem?_eq_getElem hlt_d1] at h?
          exact Option.some.inj h?
        cases hloc_d0 with
        | base _ _ hn _ => rw [henv_dst] at hn; cases hn
        | enumDead _ _ _ _ _ _ => exact False.elim (hdst_not_dead hslot_d0)
        | enumUninitImm _ _ _ _ _ _ =>
          exact hfinish_uninitImm tf₁ hlt_d1 hm_op rfl hd1
        | enumUninitInd _ _ destMp _ _ _ humpr_d =>
          rcases humpr_d with ⟨destId, tag_d, destBase, destLocal, _, hprov_d,
            _, _, hlive_d, hbase_d, hptr_d, _, hmut_d, _, hbs_d, _, _, _⟩
          obtain ⟨hfind_d, u, hu_lt, hfidx_d, hget_d⟩ := hlive_d
          have hne_id : srcId ≠ destId := by
            have hne_p := hdisj₀ srcIdx dstIdx srcMp destMp c_s0 (some wholeLay)
              hsd hmls_s0? htf₀_dst
            rw [hprov_s, hprov_d] at hne_p
            intro rfl; exact hne_p rfl
          have hcp_ok := annealStructMemCopyOp_indirect_ok
            (ld := body.localDecls) (ly := body.layouts)
            (srcLay := wholeLay) (wholeLay := wholeLay)
            (iden := topFrame.localsIdentity)
            (m := { m with stack := ⟨#[tf₁]⟩ })
            rfl hlt_d1 hd1 hne_id hprov_s hbase_s hptr_s hlive_s hbs_s
            hprov_d hbase_d hptr_d hu_lt hfidx_d hget_d
            (by simpa only [hlay_dst] using hbs_d) hmut_d
          obtain ⟨tf_end, mach_end, hm_ok, hloc_end⟩ :
              ∃ tf_end mach_end,
                Miri.Interpreter.Step.evalStatement
                  (annealStepHooksLM2_3 body.localDecls body.layouts) ()
                  (translateStmt stmt) m =
                  (⟨⟨#[tf_end]⟩, mach_end⟩, .ok ()) ∧
                tf_end.location = topFrame.location := by
            rw [hm_eval]; unfold Miri.Interpreter.runRvalue
            rw [EStateM.bind_eq_ok hm_op, hcp_ok]; exact ⟨_, _, rfl, rfl⟩
          exact ⟨_, miri_step_at_statement_ok _ hframes hframe.body_eq
            hframe.location_eq hbb hstmt hm_ok rfl
            (hloc_end.trans hframe.location_eq)⟩
        | enumInd _ _ _ _ destMp _ _ _ hemr_d =>
          rcases hemr_d with ⟨destId, tag_d, destBase, destLocal, _, _, _, _,
            hprov_d, _, _, hlive_d, hbase_d, hptr_d, _, hmut_d, _, hbs_d,
            _, _, _, _, _, _, _, _⟩
          obtain ⟨hfind_d, u, hu_lt, hfidx_d, hget_d⟩ := hlive_d
          have hne_id : srcId ≠ destId := by
            have hne_p := hdisj₀ srcIdx dstIdx srcMp destMp c_s0 (some wholeLay)
              hsd hmls_s0? htf₀_dst
            rw [hprov_s, hprov_d] at hne_p
            intro rfl; exact hne_p rfl
          have hcp_ok := annealStructMemCopyOp_indirect_ok
            (ld := body.localDecls) (ly := body.layouts)
            (srcLay := wholeLay) (wholeLay := wholeLay)
            (iden := topFrame.localsIdentity)
            (m := { m with stack := ⟨#[tf₁]⟩ })
            rfl hlt_d1 hd1 hne_id hprov_s hbase_s hptr_s hlive_s hbs_s
            hprov_d hbase_d hptr_d hu_lt hfidx_d hget_d
            (by simpa only [hlay_dst] using hbs_d) hmut_d
          obtain ⟨tf_end, mach_end, hm_ok, hloc_end⟩ :
              ∃ tf_end mach_end,
                Miri.Interpreter.Step.evalStatement
                  (annealStepHooksLM2_3 body.localDecls body.layouts) ()
                  (translateStmt stmt) m =
                  (⟨⟨#[tf_end]⟩, mach_end⟩, .ok ()) ∧
                tf_end.location = topFrame.location := by
            rw [hm_eval]; unfold Miri.Interpreter.runRvalue
            rw [EStateM.bind_eq_ok hm_op, hcp_ok]; exact ⟨_, _, rfl, rfl⟩
          exact ⟨_, miri_step_at_statement_ok _ hframes hframe.body_eq
            hframe.location_eq hbb hstmt hm_ok rfl
            (hloc_end.trans hframe.location_eq)⟩

/-! ## 12. Root-Frame Enum-Returning `Terminator.Return` Simulation -/

/-- `annealControlHooks.returnOperand` extracts `.ok (.indirect mp)` when root
return local `_0` holds `.live (.indirect mp)`. -/
theorem annealControlHooks_returnOperand_indirect_lm2_3
    {m : AnnealStepState}
    {topFrame :
      Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[topFrame])
    (hget0 : topFrame.getLocal 0 = .ok ⟨.live (.indirect mp), lay⟩) :
    annealControlHooks.returnOperand () m = (m, .ok (.indirect mp)) := by
  unfold annealControlHooks
  dsimp only
  rw [stack_currentFrame?_singleton m.stack topFrame hframes]
  dsimp only
  rw [hget0]

/-- Outcome correspondence for root-frame `Terminator.Return` when `_0` is a
multi-variant enum in `env` (`env decl0.ty = some (tagBytes, variants)`):
* `retRootEnum`: Anneal returns `.retNormal (.aggregate v_act fieldVals) mem'`,
  while `lean-miri` returns `.indirect mp0` via `returnOperand`, pops the root
  frame (`m' = { m with stack := ⟨#[]⟩ }`), and preserves
  `EnumMemRel m'.machine decl0.ty body.layouts tagBytes variants v_act
  fieldVals mp0` in the post-return machine `m'`;
* `ub`: dead or immediate-uninitialized `_0` raises undefined behavior on both
  sides. -/
inductive StepRelEnumReturnLM2_3
    (body : CapturedMir)
    (env : EnumTypeEnv)
    (m : AnnealStepState) :
    MirStepNode →
    Miri.Interpreter.StepResult AnnealStepState Bool →
    Prop where
  | retRootEnum (decl0 : LocalDecl) (tagBytes : Nat)
      (variants : List (List StructFieldDesc))
      (v_act : Nat) (fieldVals : List Value)
      (mp0 : Miri.Interpreter.MemPlace AnnealProv)
      (mem' : Memory) (m' : AnnealStepState) :
      get? body.localDecls 0 = some decl0 →
      env decl0.ty = some (tagBytes, variants) →
      annealControlHooks.returnOperand () m = (m, .ok (.indirect mp0)) →
      EnumMemRel m'.machine decl0.ty body.layouts tagBytes variants
        v_act fieldVals mp0 →
      m' = { m with stack := ⟨#[]⟩ } →
      StepRelEnumReturnLM2_3 body env m
        (.retNormal (.aggregate v_act fieldVals) mem') (m', .ok true)
  | ub (m' : AnnealStepState) (msg : String) :
      StepRelEnumReturnLM2_3 body env m
        (.fail .ub) (m', .error (.undefinedBehavior msg))

/-- Root-frame `Terminator.Return` step simulation when `_0` is a multi-variant
enum in `env` (`env decl0.ty = some (tagBytes, variants)`):
* `.dead` `_0` → lockstep `StepRelEnumReturnLM2_3.ub` (`"read of dead local"`).
* `.uninit` immediate `_0` → lockstep `StepRelEnumReturnLM2_3.ub`
  (`"read of uninitialized local"`).
* `.init (.aggregate v_act fieldVals)` `_0` → lockstep
  `StepRelEnumReturnLM2_3.retRootEnum`, returning
  `.retNormal (.aggregate v_act fieldVals) s.memory` in Anneal and popping the
  root frame in `lean-miri` with `returnOperand () m = (m, .ok (.indirect mp0))`
  and `EnumMemRel` holding on `mp0` in the post-return machine. -/
theorem step_return_enum_lm2_3_simulation
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_3 body env allocBudget s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {decl0 : LocalDecl}
    {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hcleanup : bb.isCleanup = false)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : bb.terminator.kind = .return_)
    (hdecl0 : get? body.localDecls 0 = some decl0)
    (henv0 : env decl0.ty = some (tagBytes, variants))
    (huninit_imm0 : get? s.frame.locals 0 = some .uninit →
      IsImmediateStepLocal m 0) :
    StepRelEnumReturnLM2_3 body env m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM2_3 body.localDecls body.layouts) () m) := by
  rcases hstate with ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
    _, hcal, hstack, _, _, _, _⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by
    simp [hstmt_len]
  simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  rw [miri_step_LM2_3_eq_at_terminator hframes hframe.body_eq
      hframe.location_eq hbb hstmt_none,
    miri_step_at_terminator_lm2_2 hframes hframe.body_eq hframe.location_eq
      hbb hstmt_none]
  obtain ⟨slot0, mls0, hlt0, hslot0, hmls0_eq, hloc0⟩ :=
    hframe.lookup_local hdecl0
  have hmls0 : topFrame.locals[0]? = some mls0 := by
    rw [Array.getElem?_eq_getElem hlt0, hmls0_eq]
  have hget0 := frame_getLocal_of_getElem? topFrame 0 mls0 hmls0
  have hctrl_eq :
      (annealTerminatorHooksLM2_2 body.localDecls body.layouts).toControlHooks = annealControlHooks := rfl
  unfold evalTerminator translateTerminator
    Miri.Interpreter.ControlFlow.evalTerminator
  rw [hterm, hstack, hctrl_eq, hslot0]
  dsimp only [translateTerminatorKind, Id.run, Pure.pure]
  cases hloc0 with
  | base _ _ hnone _ =>
    rw [henv0] at hnone; cases hnone
  | enumDead _ _ _ _ _ _ =>
    rw [returnFromCurrentFrame_of_error annealControlHooks hframes
      hframe.body_eq hframe.location_eq hbb hcleanup
      (annealControlHooks_returnOperand_dead hframes hget0)]
    exact .ub _ _
  | enumUninitImm _ _ _ _ _ _ =>
    rw [returnFromCurrentFrame_of_error annealControlHooks hframes
      hframe.body_eq hframe.location_eq hbb hcleanup
      (annealControlHooks_returnOperand_uninit hframes hget0)]
    exact .ub _ _
  | enumUninitInd _ _ mp0 c0 _ _ _ =>
    exact False.elim
      (huninit_imm0 hslot0 topFrame hframes ⟨.live (.indirect mp0), c0⟩
        hmls0 mp0 rfl)
  | enumInd tb0 vs0 v_act fieldVals mp0 _ henv_0 _ hemr =>
    rw [henv0] at henv_0
    injection henv_0 with hp0; rcases hp0 with ⟨rfl, rfl⟩
    have hop0 := annealControlHooks_returnOperand_indirect_lm2_3 hframes hget0
    rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
      hframe.location_eq hbb hcleanup hretCont hop0
      (annealControlHooks_popFrame_singleton hframes)
      (annealControlHooks_copyReturn_empty _ hretPlace)
      (annealControlHooks_cleanupFrame_eq false topFrame _)]
    exact .retRootEnum decl0 tagBytes variants v_act fieldVals mp0 s.memory _
      hdecl0 henv0 hop0 hemr rfl

/-- Indirect-uninitialized root-frame enum return divergence
(`Terminator.Return` when `_0` is in `LocalRelLM2_3.enumUninitInd` — i.e.,
`get? s.frame.locals 0 = some .uninit` and `¬ IsImmediateStepLocal m 0`):
* Anneal's `evalTerminator` checks `get? s.frame.locals 0 = some .uninit` and
  fails with `MirStepNode.fail .ub`.
* Vendored `lean-miri`'s `returnOperand` inspects `topFrame.locals[0]`, sees
  `.live (.indirect mp0)` without checking whether `mp0`'s backing bytes are
  initialized, pops the root frame, and steps
  `({ m with stack := ⟨#[]⟩ }, .ok true)` with `UninitEnumMemRel` holding on
  `mp0`.
This proves that the `get? s.frame.locals 0 = some .uninit →
IsImmediateStepLocal m 0` hypothesis in `step_return_enum_lm2_3_simulation` is
exact and sharp. -/
theorem step_return_enum_uninitInd_divergence
    {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_3 body env allocBudget s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {decl0 : LocalDecl}
    {tagBytes : Nat} {variants : List (List StructFieldDesc)}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hcleanup : bb.isCleanup = false)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : bb.terminator.kind = .return_)
    (hdecl0 : get? body.localDecls 0 = some decl0)
    (henv0 : env decl0.ty = some (tagBytes, variants))
    (huninit0 : get? s.frame.locals 0 = some .uninit)
    (hnot_imm0 : ¬ IsImmediateStepLocal m 0) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ mp0,
      annealControlHooks.returnOperand () m = (m, .ok (.indirect mp0)) ∧
      UninitEnumMemRel m.machine decl0.ty body.layouts tagBytes variants mp0 ∧
      Miri.Interpreter.Step.step
        (annealStepHooksLM2_3 body.localDecls body.layouts) () m =
      ({ m with stack := ⟨#[]⟩ }, .ok true) := by
  rcases hstate with ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
    _, hcal, hstack, _, _, _, _⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by
    simp [hstmt_len]
  simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  rw [miri_step_LM2_3_eq_at_terminator hframes hframe.body_eq
      hframe.location_eq hbb hstmt_none,
    miri_step_at_terminator_lm2_2 hframes hframe.body_eq hframe.location_eq
      hbb hstmt_none]
  obtain ⟨slot0, mls0, hlt0, hslot0, hmls0_eq, hloc0⟩ :=
    hframe.lookup_local hdecl0
  rw [huninit0] at hslot0
  injection hslot0 with hs0; subst hs0
  have hmls0 : topFrame.locals[0]? = some mls0 := by
    rw [Array.getElem?_eq_getElem hlt0, hmls0_eq]
  have hget0 := frame_getLocal_of_getElem? topFrame 0 mls0 hmls0
  have hctrl_eq :
      (annealTerminatorHooksLM2_2 body.localDecls body.layouts).toControlHooks = annealControlHooks := rfl
  unfold evalTerminator translateTerminator
    Miri.Interpreter.ControlFlow.evalTerminator
  rw [hterm, hstack, hctrl_eq, huninit0]
  dsimp only [translateTerminatorKind, Id.run, Pure.pure]
  refine ⟨rfl, ?_⟩
  cases hloc0 with
  | base _ _ hnone _ =>
    rw [henv0] at hnone; cases hnone
  | enumUninitImm _ _ _ _ _ _ =>
    exfalso; apply hnot_imm0
    intro tf' hf' mls' hget' mp' hcontr
    rw [hframes] at hf'
    injection hf' with ha; injection ha with ht; subst ht
    rw [hmls0] at hget'
    injection hget' with hm_eq; subst hm_eq; cases hcontr
  | enumUninitInd tb0 vs0 mp0 _ henv_0 _ humpr =>
    rw [henv0] at henv_0
    injection henv_0 with hp0; rcases hp0 with ⟨rfl, rfl⟩
    have hop0 := annealControlHooks_returnOperand_indirect_lm2_3 hframes hget0
    rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
      hframe.location_eq hbb hcleanup hretCont hop0
      (annealControlHooks_popFrame_singleton hframes)
      (annealControlHooks_copyReturn_empty _ hretPlace)
      (annealControlHooks_cleanupFrame_eq false topFrame _)]
    exact ⟨mp0, hop0, humpr, rfl⟩

end LeanMiriSpec.Correspondence
