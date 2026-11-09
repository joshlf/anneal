private theorem allocRange_size (start size : Miri.ABI.Size) :
  (Miri.Memory.allocRange start size).size = size := rfl

private theorem copyInitMask_prepareCopy_false_range {n off total : Nat}
    (hn : ValidScalarBytes n) (hpos : 0 < total) (hinb : off + total ≤ n) :
    (Miri.Memory.InitMask.new (translateSizeBytes n) false).prepareCopy
      (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat off))
        (Miri.ABI.Size.ofBytes (UInt64.ofNat total))) =
      .ok ⟨false, #[UInt64.ofNat total]⟩ := by
  have hn_eq : (translateSizeBytes n).bytes.toNat = n := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hn64 : n < 2 ^ 64 := by rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega
  have hlt64 : off + total < 2 ^ 64 := Nat.lt_of_le_of_lt hinb hn64
  have hoff64 : off < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_right off total) hlt64
  have htot64 : total < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_left total off) hlt64
  have hend := copyRange_endExclusive hlt64
  have hoff_nat : (UInt64.ofNat off).toNat = off := UInt64.toNat_ofNat_of_lt hoff64
  have htot_nat : (UInt64.ofNat total).toNat = total := UInt64.toNat_ofNat_of_lt htot64
  have hend_nat : (UInt64.ofNat (off + total)).toNat = off + total := UInt64.toNat_ofNat_of_lt hlt64
  have hnz : (UInt64.ofNat total == 0) = false := by
    cases hb : (UInt64.ofNat total == 0)
    · rfl
    · have := eq_of_beq hb; rw [this] at htot_nat; simp at htot_nat; omega
  have hnot_oob : ¬ (UInt64.ofNat (off + total) > (translateSizeBytes n).bytes) := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hend_nat, hn_eq]; omega
  have hlt_sf : UInt64.ofNat off < UInt64.ofNat (off + total) := by
    rw [UInt64.lt_iff_toNat_lt, hoff_nat, hend_nat]; omega
  unfold Miri.Memory.InitMask.prepareCopy Miri.Memory.InitMask.rangeAsInitChunks
  rw [hend]
  have hlen_new : (Miri.Memory.InitMask.new (translateSizeBytes n) false).len =
      translateSizeBytes n := rfl
  simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes, hlen_new,
    hnz, Bool.false_eq_true, ↓reduceIte, hnot_oob, hlt_sf, Miri.Memory.InitMask.lazy_get,
    bind, Except.bind, pure, Except.pure]
  unfold Miri.Memory.InitMask.collectChunks
  have hfuel : (UInt64.ofNat (off + total)).toNat - (UInt64.ofNat off).toNat + 1 = total + 1 := by omega
  with_unfolding_all erw [hfuel]
  cases ht : total with
  | zero => rw [ht] at hpos; contradiction
  | succ t' =>
    have hiter0 : (Miri.Memory.InitChunkIter.mk
        (Miri.Memory.InitMask.new (translateSizeBytes n) false) false
        ⟨UInt64.ofNat off⟩ ⟨UInt64.ofNat (off + (t' + 1))⟩).next? = .ok (some (.Uninit ⟨UInt64.ofNat off⟩ ⟨UInt64.ofNat (off + (t' + 1))⟩, ⟨Miri.Memory.InitMask.new (translateSizeBytes n) false, true, ⟨UInt64.ofNat (off + (t' + 1))⟩, ⟨UInt64.ofNat (off + (t' + 1))⟩⟩)) := by
      unfold Miri.Memory.InitChunkIter.next? Miri.Memory.InitMask.new
      dsimp only [bind, Except.bind, pure, Except.pure]
      have hcond1 : (decide (UInt64.ofNat off > UInt64.ofNat (off + (t' + 1))) || decide (UInt64.ofNat (off + (t' + 1)) > (translateSizeBytes n).bytes)) = false := by
        have ht_eq : off + (t' + 1) = off + total := by rw [ht]
        have hnot_gt_sf : ¬ (UInt64.ofNat off > UInt64.ofNat (off + (t' + 1))) := by
          rw [ht_eq]; rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hoff_nat, hend_nat]; omega
        have hnot_oob2 : ¬ (UInt64.ofNat (off + (t' + 1)) > (translateSizeBytes n).bytes) := by
          rw [ht_eq]; exact hnot_oob
        rw [Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
        exact ⟨hnot_gt_sf, hnot_oob2⟩
      split
      · rename_i h; rw [hcond1] at h; contradiction
      · split
        · rename_i h2
          change ((UInt64.ofNat off).toNat ≥ (UInt64.ofNat (off + (t' + 1))).toNat) at h2
          have hnot_ge : ¬ ((UInt64.ofNat off).toNat ≥ (UInt64.ofNat (off + (t' + 1))).toNat) := by
            have ht_eq : off + (t' + 1) = off + total := by rw [ht]
            rw [ht_eq]; rw [hoff_nat, hend_nat]; omega
          contradiction
        · split
          · rename_i h3
            have hff : (false != false) = false := rfl
            rw [hff] at h3; contradiction
          · split
            · rename_i h4_true
              have hnot_le : ¬ ((UInt64.ofNat (off + (t' + 1))).toNat ≤ (UInt64.ofNat off).toNat) := by
                have ht_eq : off + (t' + 1) = off + total := by rw [ht]
                rw [ht_eq]; rw [hoff_nat, hend_nat]; omega
              change ((UInt64.ofNat (off + (t' + 1))).toNat ≤ (UInt64.ofNat off).toNat) at h4_true
              contradiction
            · split
              · contradiction
              · rfl
    have hiter1 : (Miri.Memory.InitChunkIter.mk
        (Miri.Memory.InitMask.new (translateSizeBytes n) false) true
        ⟨UInt64.ofNat (off + (t' + 1))⟩ ⟨UInt64.ofNat (off + (t' + 1))⟩).next? = .ok none := by
      unfold Miri.Memory.InitChunkIter.next? Miri.Memory.InitMask.new
      dsimp only [bind, Except.bind, pure, Except.pure]
      have hcond2 : (decide (UInt64.ofNat (off + (t' + 1)) > UInt64.ofNat (off + (t' + 1))) || decide (UInt64.ofNat (off + (t' + 1)) > (translateSizeBytes n).bytes)) = false := by
        have ht_eq : off + (t' + 1) = off + total := by rw [ht]
        have hnot_oob2 : ¬ (UInt64.ofNat (off + (t' + 1)) > (translateSizeBytes n).bytes) := by
          rw [ht_eq]; exact hnot_oob
        rw [Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
        exact ⟨UInt64.lt_irrefl _, hnot_oob2⟩
      split
      · rename_i h; rw [hcond2] at h; contradiction
      · split
        · rfl
        · rename_i h
          change ¬ ((UInt64.ofNat (off + (t' + 1))).toNat ≥ (UInt64.ofNat (off + (t' + 1))).toNat) at h
          have hge : ((UInt64.ofNat (off + (t' + 1))).toNat ≥ (UInt64.ofNat (off + (t' + 1))).toNat) := by omega
          contradiction
    dsimp
    simp only [hiter0, bind, Except.bind, pure, Except.pure, Array.append_empty]
    dsimp
    simp only [hiter1, bind, Except.bind, pure, Except.pure, Array.append_empty]
    rw [ht]
    rfl

theorem StackScalarAllocShape.copyRepeatedly_range_uninit {E : Type}
    {srcBytes dstBytes : Nat}
    (hnS : ValidScalarBytes srcBytes) (hnD : ValidScalarBytes dstBytes)
    {srcStart dstStart total : Nat}
    (hpos : 0 < total) (hinS : srcStart + total ≤ srcBytes) (hinD : dstStart + total ≤ dstBytes)
    {S D : Miri.Memory.Allocation AnnealProv E}
    (hshapeS : StackScalarAllocShape (translateSizeBytes srcBytes) S)
    (huninitS : S.initializationMask = Miri.Memory.InitMask.new (translateSizeBytes srcBytes) false)
    (hshapeD : StackScalarAllocShape (translateSizeBytes dstBytes) D)
    (sameAlloc : Bool)
    (hdisj : sameAlloc = true → srcStart + total ≤ dstStart ∨ dstStart + total ≤ srcStart) :
    ∃ alloc' : Miri.Memory.Allocation AnnealProv E,
      Miri.Memory.Allocation.copyRepeatedly S
        (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat srcStart)) (Miri.ABI.Size.ofBytes (UInt64.ofNat total)))
        (Miri.ABI.Size.ofBytes (UInt64.ofNat dstStart)) 1 (Miri.ABI.Size.ofBytes 8) sameAlloc true D = .ok () alloc' := by
  have hs64 : srcBytes < 2 ^ 64 := by rcases hnS with rfl | rfl | rfl | rfl | rfl <;> omega
  have hd64 : dstBytes < 2 ^ 64 := by rcases hnD with rfl | rfl | rfl | rfl | rfl <;> omega
  have hltS : srcStart + total < 2 ^ 64 := Nat.lt_of_le_of_lt hinS hs64
  have hltD : dstStart + total < 2 ^ 64 := Nat.lt_of_le_of_lt hinD hd64
  have hmask_prep := copyInitMask_prepareCopy_false_range hnS hpos hinS
  unfold Miri.Memory.Allocation.copyRepeatedly
  have hallocSize : (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat srcStart)) (Miri.ABI.Size.ofBytes (UInt64.ofNat total))).size = (Miri.ABI.Size.ofBytes (UInt64.ofNat total)) := allocRange_size _ _
  have htot64 : total < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_left total srcStart) hltS
  have htot_nat : (UInt64.ofNat total).toNat = total := UInt64.toNat_ofNat_of_lt htot64
  have hz_decide : ((UInt64.ofNat total).toNat == 0) = false := by
    have h1 : total ≠ 0 := by omega
    rw [htot_nat]
    exact decide_eq_false h1
  simp only [hallocSize, bind, Except.bind, pure, Except.pure]
  rw [huninitS]
  unfold Miri.Memory.InitMask.prepareCopy
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
    unfold Miri.Memory.Allocation.writeUninit
    have hnot_oob : (UInt64.ofNat (dstStart + total) > (translateSizeBytes dstBytes).bytes) = false := by
      have hn_eq : (translateSizeBytes dstBytes).bytes.toNat = dstBytes := by rcases hnD with rfl | rfl | rfl | rfl | rfl <;> rfl
      have hend_nat : (UInt64.ofNat (dstStart + total)).toNat = dstStart + total := UInt64.toNat_ofNat_of_lt hltD
      rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hend_nat, hn_eq]; omega
    have hnot_oob_decide : decide (UInt64.ofNat (dstStart + total) > (translateSizeBytes dstBytes).bytes) = false := decide_eq_false (by rw [hnot_oob]; exact not_false)
    split
    · rename_i h; rw [hnot_oob_decide] at h; contradiction
    · exact ⟨_, rfl⟩
  · rename_i hcond
    have hsame_eq : sameAlloc = true := by
      cases sameAlloc <;> simp at hcond <;> rfl
    rw [hsame_eq]
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
    · unfold Miri.Memory.Allocation.writeUninit
      have hnot_oob : (UInt64.ofNat (dstStart + total) > (translateSizeBytes dstBytes).bytes) = false := by
        have hn_eq : (translateSizeBytes dstBytes).bytes.toNat = dstBytes := by rcases hnD with rfl | rfl | rfl | rfl | rfl <;> rfl
        have hend_nat : (UInt64.ofNat (dstStart + total)).toNat = dstStart + total := UInt64.toNat_ofNat_of_lt hltD
        rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hend_nat, hn_eq]; omega
      have hnot_oob_decide : decide (UInt64.ofNat (dstStart + total) > (translateSizeBytes dstBytes).bytes) = false := decide_eq_false (by rw [hnot_oob]; exact not_false)
      split
      · rename_i h; rw [hnot_oob_decide] at h; contradiction
      · exact ⟨_, rfl⟩
