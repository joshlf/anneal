with open("replacement.lean", "r") as f:
    content = f.read()

replacement = """    have hiter0 : (Miri.Memory.InitChunkIter.mk
        (Miri.Memory.InitMask.new (translateSizeBytes n) false) false
        ⟨UInt64.ofNat off⟩ ⟨UInt64.ofNat (off + (t' + 1))⟩).next? = .ok (some (.Uninit ⟨UInt64.ofNat off⟩ ⟨UInt64.ofNat (off + (t' + 1))⟩, ⟨Miri.Memory.InitMask.new (translateSizeBytes n) false, false, ⟨UInt64.ofNat (off + (t' + 1))⟩, ⟨UInt64.ofNat (off + (t' + 1))⟩⟩)) := by
      unfold Miri.Memory.InitChunkIter.next? Miri.Memory.InitMask.new
      dsimp only [bind, Except.bind, pure, Except.pure]
      split
      · rename_i h
        change (UInt64.ofNat off).toNat ≥ (UInt64.ofNat (off + (t' + 1))).toNat at h
        have ht_eq : off + (t' + 1) = off + total := by rw [ht]
        rw [ht_eq] at h; rw [hoff_nat, hend_nat] at h; omega
      · split
        · rename_i h2
          change (UInt64.ofNat (off + (t' + 1))).toNat ≤ (UInt64.ofNat off).toNat at h2
          have ht_eq : off + (t' + 1) = off + total := by rw [ht]
          rw [ht_eq] at h2; rw [hoff_nat, hend_nat] at h2; omega
        · split
          · rename_i h3
            have ht_eq : off + (t' + 1) = off + total := by rw [ht]
            rw [ht_eq] at h3; rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hoff_nat, hend_nat] at h3; omega
          · split
            · rename_i h4
              have ht_eq : off + (t' + 1) = off + total := by rw [ht]
              rw [ht_eq] at h4; rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hend_nat, hn_eq] at h4; omega
            · rfl
    have hiter1 : (Miri.Memory.InitChunkIter.mk
        (Miri.Memory.InitMask.new (translateSizeBytes n) false) false
        ⟨UInt64.ofNat (off + (t' + 1))⟩ ⟨UInt64.ofNat (off + (t' + 1))⟩).next? = .ok none := by
      unfold Miri.Memory.InitChunkIter.next? Miri.Memory.InitMask.new
      dsimp only [bind, Except.bind, pure, Except.pure]
      split
      · rfl
      · rename_i h
        change (UInt64.ofNat (off + (t' + 1))).toNat ≥ (UInt64.ofNat (off + (t' + 1))).toNat at h
        omega"""

import re
content = re.sub(r'    have hiter0 : (.*?):= by sorry', replacement, content, flags=re.DOTALL)
content = re.sub(r'    have hiter1 : (.*?):= by sorry', "", content, flags=re.DOTALL)

# And remove Miri.Memory.collectChunksAux from simp because it's unfolded automatically
content = content.replace("    unfold Miri.Memory.InitMask.collectChunksAux\n", "")
content = content.replace("    simp only [hiter0, bind, Except.bind, pure, Except.pure, Array.append_empty, Id.pure, Id.bind]\n", "    simp only [hiter0, bind, Except.bind, pure, Except.pure, Array.append_empty, Id.pure, Id.bind]\n")
content = content.replace("    simp only [hiter1, bind, Except.bind, pure, Except.pure, Array.append_empty]\n", "    simp only [hiter1, bind, Except.bind, pure, Except.pure, Array.append_empty]\n")

with open("replacement.lean", "w") as f:
    f.write(content)
