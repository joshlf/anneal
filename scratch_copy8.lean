import LeanMiriSpec.Correspondence.CopyLM4_2
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

private theorem copyIte_neg {P : Prop} [Decidable P] {α : Type _} {a b : α} (h : ¬ P) :
    (if P then a else b) = b := by simp [h]

private theorem copyInitMask_prepareCopy_false_range {n off total : Nat}
    (hn : ValidScalarBytes n) (hpos : 0 < total) (hinb : off + total ≤ n) :
    (Miri.Memory.InitMask.new (translateSizeBytes n) false).prepareCopy
      (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat off))
        (Miri.ABI.Size.ofBytes (UInt64.ofNat total))) =
      .ok ⟨false, #[]⟩ := by
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
  have hnot_gt_sf : ¬ (UInt64.ofNat off > UInt64.ofNat (off + total)) := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hoff_nat, hend_nat]; omega
  have hnot_le_fs : ¬ (UInt64.ofNat (off + total) ≤ UInt64.ofNat off) := by
    rw [UInt64.le_iff_toNat_le, hoff_nat, hend_nat]; omega
  have hfuel : (UInt64.ofNat (off + total)).toNat - (UInt64.ofNat off).toNat + 1 = total + 1 := by
    omega
  have hsub_u64 : UInt64.ofNat (off + total) - UInt64.ofNat off = UInt64.ofNat total := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hlt_sf), hend_nat, hoff_nat, htot_nat]
    omega
  unfold Miri.Memory.InitMask.prepareCopy Miri.Memory.InitMask.rangeAsInitChunks
  rw [hend]
  have hlen_new : (Miri.Memory.InitMask.new (translateSizeBytes n) false).len =
      translateSizeBytes n := rfl
  simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes, hlen_new,
    hnz, Bool.false_eq_true, ↓reduceIte, hnot_oob, hlt_sf, Miri.Memory.InitMask.lazy_get,
    bind, Except.bind, pure, Except.pure]
  have hcond1 :
      (decide (UInt64.ofNat off > UInt64.ofNat (off + total)) ||
        decide (UInt64.ofNat (off + total) > (translateSizeBytes n).bytes)) = false := by
    rw [Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
    exact ⟨hnot_gt_sf, hnot_oob⟩
  have hcond2 :
      (decide (UInt64.ofNat (off + total) > UInt64.ofNat (off + total)) ||
        decide (UInt64.ofNat (off + total) > (translateSizeBytes n).bytes)) = false := by
    rw [Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
    exact ⟨UInt64.lt_irrefl _, hnot_oob⟩
  have hiter0 : (Miri.Memory.InitChunkIter.mk
      (Miri.Memory.InitMask.new (translateSizeBytes n) false) false
      ⟨UInt64.ofNat off⟩ ⟨UInt64.ofNat (off + total)⟩).next? =
      .ok (some (.Uninit ⟨UInt64.ofNat off⟩ ⟨UInt64.ofNat (off + total)⟩,
        ⟨Miri.Memory.InitMask.new (translateSizeBytes n) false, true,
          ⟨UInt64.ofNat (off + total)⟩, ⟨UInt64.ofNat (off + total)⟩⟩)) := by
    unfold Miri.Memory.InitChunkIter.next? Miri.Memory.InitMask.new
    dsimp only [bind, Except.bind, pure, Except.pure]
    erw [hcond1]
    have hnot_ge : ¬ ((UInt64.ofNat off).toNat ≥ (UInt64.ofNat (off + total)).toNat) := by
      omega
    with_unfolding_all dsimp
    simp only [↓reduceIte, hnot_le_fs]
    with_unfolding_all change
      (if (UInt64.ofNat off).toNat ≥ (UInt64.ofNat (off + total)).toNat then _ else _) = _
    rw [copyIte_neg hnot_ge]
    rfl
  have hiter1 : (Miri.Memory.InitChunkIter.mk
      (Miri.Memory.InitMask.new (translateSizeBytes n) false) true
      ⟨UInt64.ofNat (off + total)⟩ ⟨UInt64.ofNat (off + total)⟩).next? = .ok none := by
    unfold Miri.Memory.InitChunkIter.next? Miri.Memory.InitMask.new
    dsimp only [bind, Except.bind, pure, Except.pure]
    erw [hcond2]
    with_unfolding_all simp
  unfold Miri.Memory.collectChunks Miri.Memory.collectChunksAux
  rw [hfuel]
  with_unfolding_all dsimp
  rw [hiter0, hiter1]
  rfl
