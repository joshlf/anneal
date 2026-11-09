with open("replacement.lean", "r") as f:
    content = f.read()

import re
iter0_start = content.find("    have hiter0 :")
iter1_start = content.find("    have hiter1 :")
iter1_end = content.find("    unfold Miri.Memory.InitMask.collectChunksAux")

hiter0_proof = """    have hiter0 : (Miri.Memory.InitChunkIter.mk
        (Miri.Memory.InitMask.new (translateSizeBytes n) false) false
        ⟨UInt64.ofNat off⟩ ⟨UInt64.ofNat (off + (t' + 1))⟩).next? = .ok (some (.Uninit ⟨UInt64.ofNat off⟩ ⟨UInt64.ofNat (off + (t' + 1))⟩, ⟨Miri.Memory.InitMask.new (translateSizeBytes n) false, false, ⟨UInt64.ofNat (off + (t' + 1))⟩, ⟨UInt64.ofNat (off + (t' + 1))⟩⟩)) := by
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
            · rfl
"""

hiter1_proof = """    have hiter1 : (Miri.Memory.InitChunkIter.mk
        (Miri.Memory.InitMask.new (translateSizeBytes n) false) false
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
"""

content = content[:iter0_start] + hiter0_proof + hiter1_proof + content[iter1_end:]

# And fix the Missing field copyRepeatedly_range_uninit.
# In my original file, did I put `theorem copyRepeatedly_range_uninit` inside `namespace StackScalarAllocShape`?
# In the original, it was `theorem StackScalarAllocShape.copyRepeatedly_range_uninit` but it failed!
# Wait, did it fail because `copyInitMask_prepareCopy_false_range` failed to compile and closed the goal, causing the whole theorem to be ignored?
# YES! The `L5526: unsolved goals` was for `copyInitMask_prepareCopy_false_range`!
# Because of that error, the rest of the file couldn't see `StackScalarAllocShape.copyRepeatedly_range_uninit`!

with open("replacement.lean", "w") as f:
    f.write(content)
