with open('lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean', 'r') as f:
    text = f.read()

# Fix 1: rfl -> with_unfolding_all rfl
text = text.replace("""    match total, hpos, htot16 with
    | 1, _, _ | 2, _, _ | 3, _, _ | 4, _, _ | 5, _, _ | 6, _, _ | 7, _, _ | 8, _, _
    | 9, _, _ | 10, _, _ | 11, _, _ | 12, _, _ | 13, _, _ | 14, _, _ | 15, _, _ | 16, _, _ =>
      with_unfolding_all (conv => lhs; whnf)
      with_unfolding_all erw [hiter0]
      dsimp only [bind, Except.bind, pure, Except.pure]
      with_unfolding_all (conv => lhs; whnf)
      with_unfolding_all erw [hiter1]
      rfl
    | k + 17, _, hle => omega
  rw [hchunks]
  rfl""", """    match total, hpos, htot16 with
    | 1, _, _ | 2, _, _ | 3, _, _ | 4, _, _ | 5, _, _ | 6, _, _ | 7, _, _ | 8, _, _
    | 9, _, _ | 10, _, _ | 11, _, _ | 12, _, _ | 13, _, _ | 14, _, _ | 15, _, _ | 16, _, _ =>
      with_unfolding_all (conv => lhs; whnf)
      with_unfolding_all erw [hiter0]
      dsimp only [bind, Except.bind, pure, Except.pure]
      with_unfolding_all (conv => lhs; whnf)
      with_unfolding_all erw [hiter1]
      rfl
    | k + 17, _, hle => omega
  rw [hchunks]
  with_unfolding_all rfl""")

# Fix 2: dsimp made no progress -> remove dsimp only ...
text = text.replace("""  unfold Miri.Memory.Allocation.copyRepeatedly
  dsimp only [bind, Except.bind, pure, Except.pure]
  simp only [hsliceS, hmul, hsliceD, hshapeS.provenanceMap_eq, hprov_prep,
    huninitS, hmask_prep]
  dsimp only [bind, Except.bind, pure, Except.pure]
  simp only [Miri.Memory.InitCopy.noBytesInit, Bool.false_eq_true, ↓reduceIte]
  change ∃ alloc', (Miri.Memory.Allocation.writeUninit
    (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat dstStart))
      (Miri.ABI.Size.ofBytes (UInt64.ofNat total)))
    (Miri.ABI.Size.ofBytes 8) _) = Except.ok () alloc'""", """  unfold Miri.Memory.Allocation.copyRepeatedly
  simp only [bind, Except.bind, pure, Except.pure, hsliceS, hmul, hsliceD, hshapeS.provenanceMap_eq, hprov_prep,
    huninitS, hmask_prep]
  simp only [bind, Except.bind, pure, Except.pure]
  simp only [Miri.Memory.InitCopy.noBytesInit, Bool.false_eq_true, ↓reduceIte]
  change ∃ alloc', (Miri.Memory.Allocation.writeUninit
    (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat dstStart))
      (Miri.ABI.Size.ofBytes (UInt64.ofNat total)))
    (Miri.ABI.Size.ofBytes 8) _) = Except.ok () alloc'""")

# Fix 3: Miri.ABI.Size.ext -> rfl
text = text.replace("""  have hts : Miri.ABI.Size.ofBytes (UInt64.ofNat total) = translateSizeBytes total := by
    have _ : total < 2^64 := by rcases hnS with rfl | rfl | rfl | rfl | rfl <;> omega
    exact Miri.ABI.Size.ext rfl""", """  have hts : Miri.ABI.Size.ofBytes (UInt64.ofNat total) = translateSizeBytes total := by
    have _ : total < 2^64 := by rcases hnS with rfl | rfl | rfl | rfl | rfl <;> omega
    rfl""")

# Fix 4: srcStart < 2^32
text = text.replace("""  have heq := annealMemCopy_live_inbounds_eq (st := st) srcId srcTag srcStart srcLA dstId dstTag dstStart dstLA
    hsrc_id (by decide) hsrc_base hsrc_live hinS
    hdst_id (by decide) hdst_base hdst_live hinD hpos hle""", """  have hsrc_lt : srcStart < 2^32 := by rcases hnS with rfl | rfl | rfl | rfl | rfl <;> omega
  have hdst_lt : dstStart < 2^32 := by rcases hnD with rfl | rfl | rfl | rfl | rfl <;> omega
  have heq := annealMemCopy_live_inbounds_eq (st := st) srcId srcTag srcStart srcLA dstId dstTag dstStart dstLA
    hsrc_id hsrc_lt hsrc_base hsrc_live hinS
    hdst_id hdst_lt hdst_base hdst_live hinD hpos hle""")

with open('lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean', 'w') as f:
    f.write(text)
