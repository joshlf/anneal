with open("replacement.lean", "r") as f:
    content = f.read()

target_iter0 = """      split
      · rename_i h; rw [hcond1] at h; contradiction
      · split
        · rename_i h2
          change ¬ ((UInt64.ofNat off).toNat ≥ (UInt64.ofNat (off + (t' + 1))).toNat) at h2
          have hnot_ge : ¬ ((UInt64.ofNat off).toNat ≥ (UInt64.ofNat (off + (t' + 1))).toNat) := by
            have ht_eq : off + (t' + 1) = off + total := by rw [ht]
            rw [ht_eq]; rw [hoff_nat, hend_nat]; omega
          contradiction
        · split
          · rename_i h3
            contradiction
          · skip
            split
            · rfl
            · rename_i h4
              change ¬ ((UInt64.ofNat (off + (t' + 1))).toNat ≤ (UInt64.ofNat off).toNat) at h4
              have hnot_le : ¬ ((UInt64.ofNat (off + (t' + 1))).toNat ≤ (UInt64.ofNat off).toNat) := by
                have ht_eq : off + (t' + 1) = off + total := by rw [ht]
                rw [ht_eq]; rw [hoff_nat, hend_nat]; omega
              contradiction"""

replacement_iter0 = """      split
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
            contradiction
          · skip
            split
            · rfl
            · rename_i h4
              have hnot_le : ¬ ((UInt64.ofNat (off + (t' + 1))).toNat ≤ (UInt64.ofNat off).toNat) := by
                have ht_eq : off + (t' + 1) = off + total := by rw [ht]
                rw [ht_eq]; rw [hoff_nat, hend_nat]; omega
              change ¬ ((UInt64.ofNat (off + (t' + 1))).toNat ≤ (UInt64.ofNat off).toNat) at h4
              contradiction"""

target_iter1 = """      split
      · rename_i h; rw [hcond2] at h; contradiction
      · split
        · rfl
        · rename_i h
          change ¬ ((UInt64.ofNat (off + (t' + 1))).toNat ≥ (UInt64.ofNat (off + (t' + 1))).toNat) at h
          have hge : ((UInt64.ofNat (off + (t' + 1))).toNat ≥ (UInt64.ofNat (off + (t' + 1))).toNat) := by omega
          contradiction"""

replacement_iter1 = """      split
      · rename_i h; rw [hcond2] at h; contradiction
      · split
        · rfl
        · rename_i h
          change ¬ ((UInt64.ofNat (off + (t' + 1))).toNat ≥ (UInt64.ofNat (off + (t' + 1))).toNat) at h
          have hge : ((UInt64.ofNat (off + (t' + 1))).toNat ≥ (UInt64.ofNat (off + (t' + 1))).toNat) := by omega
          contradiction"""

content = content.replace(target_iter0, replacement_iter0)
content = content.replace(target_iter1, replacement_iter1)

with open("replacement.lean", "w") as f:
    f.write(content)
