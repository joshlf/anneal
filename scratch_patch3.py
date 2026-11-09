with open('lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean', 'r') as f:
    text = f.read()

# Fix the incorrect #[] to #[UInt64.ofNat total]
text = text.replace("""    (Miri.Memory.InitMask.new (translateSizeBytes n) false).prepareCopy
      (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat off))
        (Miri.ABI.Size.ofBytes (UInt64.ofNat total))) =
      .ok ⟨false, #[]⟩""", """    (Miri.Memory.InitMask.new (translateSizeBytes n) false).prepareCopy
      (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat off))
        (Miri.ABI.Size.ofBytes (UInt64.ofNat total))) =
      .ok ⟨false, #[UInt64.ofNat total]⟩""")

# Fix the end of the proof of copyInitMask_prepareCopy_false_range
text = text.replace("""  rw [hchunks]
  with_unfolding_all rfl""", """  rw [hchunks]
  have hnot_lt_fs : ¬ (UInt64.ofNat (off + total) < UInt64.ofNat off) := hnot_gt_sf
  have hcr : (Miri.Memory.InitChunk.Uninit ⟨UInt64.ofNat off⟩ ⟨UInt64.ofNat (off + total)⟩).range =
      .ok ⟨⟨UInt64.ofNat off⟩, ⟨UInt64.ofNat total⟩⟩ := by
    unfold Miri.Memory.InitChunk.range Miri.Memory.AllocRange.fromEndpoints Miri.ABI.Size.sub
    simp only [hnot_lt_fs, ↓reduceIte, hsub_u64, Except.mapError, bind, Except.bind,
      pure, Except.pure, Miri.ABI.Size.ofBytes]
  simp only [List.forIn_toArray, List.forIn_cons, List.forIn_nil, hcr,
    Miri.Memory.InitChunk.isInit, bind, Except.bind, pure, Except.pure]
  rfl""")

with open('lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean', 'w') as f:
    f.write(text)
