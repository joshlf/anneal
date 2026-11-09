with open("lines_to_replace.txt", "r") as f:
    content = f.read()

# Apply Fix 1
target1 = """  simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes, hlen_new,
    hnz, Bool.false_eq_true, ↓reduceIte, hnot_oob, hlt_sf, Miri.Memory.InitMask.lazy_get,
    bind, Except.bind, pure, Except.pure]
  unfold Miri.Memory.InitMask.collectChunks
  have hiter0 :"""
replace1 = """  simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes, hlen_new,
    hnz, Bool.false_eq_true, ↓reduceIte, hnot_oob, hlt_sf, Miri.Memory.InitMask.lazy_get,
    bind, Except.bind, pure, Except.pure]
  unfold Miri.Memory.InitMask.collectChunks
  have hfuel : (UInt64.ofNat (off + total)).toNat - (UInt64.ofNat off).toNat + 1 = total + 1 := by omega
  with_unfolding_all erw [hfuel]
  cases ht : total with
  | zero => rw [ht] at hpos; contradiction
  | succ t' =>
    have hiter0 :"""
content = content.replace(target1, replace1)

# Apply Fix 2 (part A)
target2 = """            have hnot_le : ¬ ((UInt64.ofNat (off + total)).toNat ≤ (UInt64.ofNat off).toNat) := by omega
            contradiction
  rw [hiter0]
  unfold Miri.Memory.collectChunksAux
  have hiter1 :"""
replace2 = """            have hnot_le : ¬ ((UInt64.ofNat (off + (t' + 1))).toNat ≤ (UInt64.ofNat off).toNat) := by
              have ht_eq : off + (t' + 1) = off + total := by rw [ht]
              rw [ht_eq]; rw [hoff_nat, hend_nat]; omega
            contradiction
    have hiter1 :"""
content = content.replace(target2, replace2)

# Fix (off + total) to (off + (t' + 1)) in hiter0 block
# Wait, I can just replace `off + total` with `off + (t' + 1)` in that block
iter0_start = content.find("have hiter0 :")
iter1_start = content.find("have hiter1 :")
iter0_block = content[iter0_start:iter1_start]
iter0_block = iter0_block.replace("off + total", "off + (t' + 1)")
iter0_block = iter0_block.replace("have hnot_ge : ¬ ((UInt64.ofNat off).toNat ≥ (UInt64.ofNat (off + (t' + 1))).toNat) := by omega", """have hnot_ge : ¬ ((UInt64.ofNat off).toNat ≥ (UInt64.ofNat (off + (t' + 1))).toNat) := by
          have ht_eq : off + (t' + 1) = off + total := by rw [ht]
          rw [ht_eq]; rw [hoff_nat, hend_nat]; omega""")
iter0_block = iter0_block.replace("have hnot_gt_sf : ¬ (UInt64.ofNat off > UInt64.ofNat (off + (t' + 1))) := by\n        rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hoff_nat, hend_nat]; omega", """have hnot_gt_sf : ¬ (UInt64.ofNat off > UInt64.ofNat (off + (t' + 1))) := by
        have ht_eq : off + (t' + 1) = off + total := by rw [ht]
        rw [ht_eq]
        rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hoff_nat, hend_nat]; omega""")
iter0_block = iter0_block.replace("exact ⟨hnot_gt_sf, hnot_oob⟩", """have hnot_oob2 : ¬ (UInt64.ofNat (off + (t' + 1)) > (translateSizeBytes n).bytes) := by
        have ht_eq : off + (t' + 1) = off + total := by rw [ht]
        rw [ht_eq]
        exact hnot_oob
      rw [Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
      exact ⟨hnot_gt_sf, hnot_oob2⟩""")
content = content[:iter0_start] + iter0_block + content[iter1_start:]

# Fix (off + total) to (off + (t' + 1)) in hiter1 block
iter1_start = content.find("have hiter1 :")
rw_hiter1 = content.find("rw [hiter1]")
iter1_block = content[iter1_start:rw_hiter1]
iter1_block = iter1_block.replace("off + total", "off + (t' + 1)")
iter1_block = iter1_block.replace("have hge : ((UInt64.ofNat (off + (t' + 1))).toNat ≥ (UInt64.ofNat (off + (t' + 1))).toNat) := by omega", "have hge : ((UInt64.ofNat (off + (t' + 1))).toNat ≥ (UInt64.ofNat (off + (t' + 1))).toNat) := by omega")
iter1_block = iter1_block.replace("exact ⟨UInt64.lt_irrefl _, hnot_oob⟩", """have hnot_oob2 : ¬ (UInt64.ofNat (off + (t' + 1)) > (translateSizeBytes n).bytes) := by
        have ht_eq : off + (t' + 1) = off + total := by rw [ht]
        rw [ht_eq]
        exact hnot_oob
      rw [Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
      exact ⟨UInt64.lt_irrefl _, hnot_oob2⟩""")
content = content[:iter1_start] + iter1_block + content[rw_hiter1:]

# Apply Fix 3: replace `rw [hiter1]` and everything after it up to `copyRepeatedly` with the final step
target3 = """  rw [hiter1]
  have hfuel : (UInt64.ofNat (off + total)).toNat - (UInt64.ofNat off).toNat + 1 = total + 1 := by
    omega
  with_unfolding_all erw [hfuel]
  match total with
  | 0 => rw [hpos] at hpos; contradiction
  | t' + 1 =>
    rfl"""
replace3 = """    unfold Miri.Memory.collectChunksAux
    simp only [hiter0, bind, Except.bind, pure, Except.pure, Array.append_empty, Id.pure, Id.bind]
    unfold Miri.Memory.collectChunksAux
    simp only [hiter1, bind, Except.bind, pure, Except.pure, Array.append_empty]
    rw [ht]
    rfl"""
content = content.replace(target3, replace3)

# Remove the `dsimp only` lines in copyRepeatedly and fix decide total == 0
target4 = """  have hz_decide : decide ((UInt64.ofNat total).toNat == 0) = false := by
    cases hb : (UInt64.ofNat total == 0)
    · rfl
    · have := eq_of_beq hb; rw [this] at htot64; have htot_nat : (UInt64.ofNat total).toNat = total := UInt64.toNat_ofNat_of_lt htot64; simp at htot_nat; omega
  simp only [hallocSize, hz_decide, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
  dsimp only
  unfold Miri.Memory.Allocation.prepareCopy
  rw [huninitS]
  rw [hmask_prep]
  dsimp only [bind, Except.bind, pure, Except.pure]
  split
  · rename_i hcond
    have hsame_eq : sameAlloc = false := by
      cases sameAlloc <;> simp at hcond <;> assumption
    rw [hsame_eq]
    dsimp only [ite_false]
    unfold Miri.Memory.Allocation.writeUninit
    dsimp only [bind, Except.bind, pure, Except.pure]"""
replace4 = """  have htot_nat : (UInt64.ofNat total).toNat = total := UInt64.toNat_ofNat_of_lt htot64
  have hz_decide : ((UInt64.ofNat total).toNat == 0) = false := by
    have h1 : total ≠ 0 := by omega
    rw [htot_nat]
    exact decide_eq_false h1
  simp only [hallocSize, bind, Except.bind, pure, Except.pure]
  unfold Miri.Memory.InitMask.prepareCopy
  rw [huninitS]
  unfold Miri.Memory.InitMask.prepareCopy at hmask_prep
  rw [hmask_prep]
  have hb1 : (false == true) = false := rfl
  have hb2 : (decide ((UInt64.ofNat total).toNat == 0)) = false := by rw [hz_decide]
  simp only [hb1, hb2, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
  split
  · rename_i hcond
    have hsame_eq : sameAlloc = false := by
      cases sameAlloc <;> simp at hcond <;> assumption
    rw [hsame_eq]
    unfold Miri.Memory.Allocation.writeUninit"""
content = content.replace(target4, replace4)

# Fix dsimp only [ite_true] and the other branches in copyRepeatedly
target5 = """    rw [hsame_eq]
    dsimp only [ite_true]
    have hdisj2 : srcStart + total ≤ dstStart ∨ dstStart + total ≤ srcStart := hdisj rfl
    have hdisj3 : decide (Miri.Memory.allocRangeOverlap (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat srcStart)) (Miri.ABI.Size.ofBytes (UInt64.ofNat total))) (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat dstStart)) (Miri.ABI.Size.ofBytes (UInt64.ofNat total)))) = false := by
      unfold Miri.Memory.allocRangeOverlap
      simp only [hallocSize, Miri.Memory.allocRange, Miri.ABI.Size.ofBytes]
      rw [Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
      have hsrc_nat : (UInt64.ofNat srcStart).toNat = srcStart := UInt64.toNat_ofNat_of_lt hltS
      have hdst_nat : (UInt64.ofNat dstStart).toNat = dstStart := UInt64.toNat_ofNat_of_lt hltD
      have htot_nat : (UInt64.ofNat total).toNat = total := UInt64.toNat_ofNat_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_left total dstStart) hltD)
      have h1 : ((UInt64.ofNat srcStart).toNat + (UInt64.ofNat total).toNat) = srcStart + total := by omega
      have h2 : ((UInt64.ofNat dstStart).toNat + (UInt64.ofNat total).toNat) = dstStart + total := by omega
      cases hdisj2 with
      | inl hle => right; omega
      | inr hle => left; omega
    split
    · rename_i h; rw [hdisj3] at h; contradiction
    · dsimp only
      unfold Miri.Memory.Allocation.writeUninit
      dsimp only [bind, Except.bind, pure, Except.pure]"""
replace5 = """    rw [hsame_eq]
    have hdisj2 : srcStart + total ≤ dstStart ∨ dstStart + total ≤ srcStart := hdisj rfl
    have hdisj3 : decide (Miri.Memory.allocRangeOverlap (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat srcStart)) (Miri.ABI.Size.ofBytes (UInt64.ofNat total))) (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat dstStart)) (Miri.ABI.Size.ofBytes (UInt64.ofNat total)))) = false := by
      unfold Miri.Memory.allocRangeOverlap
      simp only [hallocSize, Miri.Memory.allocRange, Miri.ABI.Size.ofBytes]
      rw [Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
      have hsrc_nat : (UInt64.ofNat srcStart).toNat = srcStart := UInt64.toNat_ofNat_of_lt hltS
      have hdst_nat : (UInt64.ofNat dstStart).toNat = dstStart := UInt64.toNat_ofNat_of_lt hltD
      have h1 : ((UInt64.ofNat srcStart).toNat + (UInt64.ofNat total).toNat) = srcStart + total := by rw [hsrc_nat, htot_nat]
      have h2 : ((UInt64.ofNat dstStart).toNat + (UInt64.ofNat total).toNat) = dstStart + total := by rw [hdst_nat, htot_nat]
      cases hdisj2 with
      | inl hle => right; omega
      | inr hle => left; omega
    split
    · rename_i h; rw [hdisj3] at h; contradiction
    · unfold Miri.Memory.Allocation.writeUninit"""
content = content.replace(target5, replace5)

with open("replacement.lean", "w") as f:
    f.write(content)
