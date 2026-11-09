import LeanMiriSpec.Correspondence.WriteBytesLM4_2
open Miri Miri.Memory Miri.ABI

theorem copyInitMask_prepareCopy_false_range_gen {n off total : Nat}
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
  have hoff_nat : (UInt64.ofNat off).toNat = off := UInt64.toNat_ofNat_of_lt hoff64
  have hlen_new : (Miri.Memory.InitMask.new (translateSizeBytes n) false).len = translateSizeBytes n := rfl
  have hend : (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat off)) (Miri.ABI.Size.ofBytes (UInt64.ofNat total))).endExclusive = .ok (Miri.ABI.Size.ofBytes (UInt64.ofNat (off + total))) := by
    unfold AllocRange.endExclusive AllocRange.end Size.add
    have htot_nat : (UInt64.ofNat total).toNat = total := UInt64.toNat_ofNat_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_left total off) hlt64)
    have hend_nat : (UInt64.ofNat (off + total)).toNat = off + total := UInt64.toNat_ofNat_of_lt hlt64
    have hnz : (UInt64.ofNat total == 0) = false := by
      rw [Bool.eq_false_iff, beq_iff_eq, decide_eq_false_iff_not, UInt64.eq_iff_toNat_eq, htot_nat]; omega
    have hnot_oob : ¬ (UInt64.ofNat (off + total) > (translateSizeBytes n).bytes) := by
      rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hend_nat, hn_eq]; omega
    have hlt_sf : (UInt64.ofNat off < UInt64.ofNat (off + total)) := by
      rw [UInt64.lt_iff_toNat_lt, hoff_nat, hend_nat]; omega
    simp only [hnz, hlt_sf, ite_false, Except.mapError, Except.ok.injEq, Size.mk.injEq]
    have : UInt64.ofNat off + UInt64.ofNat total = UInt64.ofNat (off + total) := by
      apply UInt64.eq_of_val_eq
      have h_size : UInt64.size = 18446744073709551616 := rfl
      simp only [UInt64.add_def, UInt64.val_ofNat]
      omega
    rw [this]
  unfold Miri.Memory.InitMask.prepareCopy
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [hlen_new, hend]
  dsimp only [bind, Except.bind, pure, Except.pure]
  have htot_nat : (UInt64.ofNat total).toNat = total := UInt64.toNat_ofNat_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_left total off) hlt64)
  have hnz : (UInt64.ofNat total == 0) = false := by
    rw [Bool.eq_false_iff, beq_iff_eq, decide_eq_false_iff_not, UInt64.eq_iff_toNat_eq, htot_nat]; omega
  rw [hnz]
  dsimp only [bind, Except.bind, pure, Except.pure]
  unfold Miri.Memory.InitMask.rangeAsInitChunks
  dsimp only [bind, Except.bind, pure, Except.pure]
  have hend_nat : (UInt64.ofNat (off + total)).toNat = off + total := UInt64.toNat_ofNat_of_lt hlt64
  have hnot_oob : ¬ (UInt64.ofNat (off + total) > (translateSizeBytes n).bytes) := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hend_nat, hn_eq]; omega
  have hcond : (UInt64.ofNat (off + total) > (translateSizeBytes n).bytes) = false := by
    rw [decide_eq_false_iff_not]; exact hnot_oob
  rw [hcond, hlen_new]
  dsimp only [bind, Except.bind, pure, Except.pure]
  have hlt_sf : (UInt64.ofNat off < UInt64.ofNat (off + total)) := by
    rw [UInt64.lt_iff_toNat_lt, hoff_nat, hend_nat]; omega
  have hlt_decide : (UInt64.ofNat off < UInt64.ofNat (off + total)) = true := decide_eq_true hlt_sf
  rw [hlt_decide]
  dsimp only [bind, Except.bind, pure, Except.pure]
  have hiter0 : (Miri.Memory.InitChunkIter.mk
      (Miri.Memory.InitMask.new (translateSizeBytes n) false) false
      ⟨UInt64.ofNat off⟩ ⟨UInt64.ofNat (off + total)⟩).next? = .ok (some (.Uninit ⟨UInt64.ofNat off⟩ ⟨UInt64.ofNat (off + total)⟩, ⟨Miri.Memory.InitMask.new (translateSizeBytes n) false, false, ⟨UInt64.ofNat (off + total)⟩, ⟨UInt64.ofNat (off + total)⟩⟩)) := by
    unfold Miri.Memory.InitChunkIter.next? Miri.Memory.InitMask.new
    dsimp only [bind, Except.bind, pure, Except.pure]
    have hcond1 :
        ((UInt64.ofNat off > UInt64.ofNat (off + total)) ||
          (UInt64.ofNat off > (translateSizeBytes n).bytes)) = false := by
      have hnot_gt_sf : ¬ (UInt64.ofNat off > UInt64.ofNat (off + total)) := by
        rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hoff_nat, hend_nat]; omega
      rw [Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
      have hoff_oob : ¬ (UInt64.ofNat off > (translateSizeBytes n).bytes) := by
        rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hoff_nat, hn_eq]; omega
      exact ⟨hnot_gt_sf, hoff_oob⟩
    split
    · rename_i h; rw [hcond1] at h; contradiction
    · split
      · rename_i h2
        have hnot_ge : (UInt64.ofNat off).toNat ≥ (UInt64.ofNat (off + total)).toNat := by
          exact h2
        omega
      · split
        · rename_i h3
          contradiction
        · split
          · rfl
          · rename_i h4; sorry
  sorry
