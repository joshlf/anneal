with open('lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean', 'r') as f:
    text = f.read()

# Fix the simplify issue
old_simp = """  simp only [bind, Except.bind, pure, Except.pure, hsliceS, hmul, hsliceD, hshapeS.provenanceMap_eq, hprov_prep,
    huninitS, hmask_prep]
  simp only [bind, Except.bind, pure, Except.pure]
  simp only [Miri.Memory.InitCopy.noBytesInit, Bool.false_eq_true, ↓reduceIte]
  change ∃ alloc', (Miri.Memory.Allocation.writeUninit
    (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat dstStart))
      (Miri.ABI.Size.ofBytes (UInt64.ofNat total)))
    (Miri.ABI.Size.ofBytes 8) _) = Except.ok () alloc'
  have hendD := copyRange_endExclusive hltD"""
new_simp = """  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [hsliceS, hmul, hsliceD, hshapeS.provenanceMap_eq, hprov_prep, huninitS, hmask_prep]
  dsimp only [bind, Except.bind, pure, Except.pure]
  simp only [Miri.Memory.InitCopy.noBytesInit, Bool.false_eq_true, ↓reduceIte]
  have hendD := copyRange_endExclusive hltD"""
text = text.replace(old_simp, new_simp)

# Fix the inbounds expected type mismatch
old_inbounds = """  have heq := annealMemCopy_live_inbounds_eq (st := st) srcId srcTag srcStart srcLA dstId dstTag dstStart dstLA
    hsrc_id hsrc_lt hsrc_base hsrc_live hinS
    hdst_id hdst_lt hdst_base hdst_live hinD hpos hle"""
new_inbounds = """  have hinS' : srcStart + total ≤ srcLA.allocation.byteSize.bytes.toNat := by rw [hsrc_sz]; exact hinS
  have hinD' : dstStart + total ≤ dstLA.allocation.byteSize.bytes.toNat := by rw [hdst_sz]; exact hinD
  have heq := annealMemCopy_live_inbounds_eq (st := st) srcId srcTag srcStart srcLA dstId dstTag dstStart dstLA
    hsrc_id hsrc_lt hsrc_base hsrc_live hinS'
    hdst_id hdst_lt hdst_base hdst_live hinD' hpos hle"""
text = text.replace(old_inbounds, new_inbounds)

with open('lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean', 'w') as f:
    f.write(text)
