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
  have hsliceS := copyCheckedSlice_range hnS hinS hshapeS.byteSize_eq hshapeS.len_eq
  have hsliceD := copyCheckedSlice_range hnD hinD hshapeD.byteSize_eq hshapeD.len_eq
  unfold Miri.Memory.Allocation.getBytesUnchecked at hsliceS hsliceD
  have hmul := copySize_mul_one (Miri.ABI.Size.ofBytes (UInt64.ofNat total))
  have hprov_prep := copyProv_prepareCopy_new_range hltS (copyAlloc_raw S)
  have hmask_prep := copyInitMask_prepareCopy_false_range hnS hpos hinS
  unfold Miri.Memory.Allocation.copyRepeatedly
  dsimp only [bind, Except.bind, pure, Except.pure]
  simp only [hsliceS, hmul, hsliceD, hshapeS.provenanceMap_eq, hprov_prep,
    huninitS, hmask_prep]
  dsimp only [bind, Except.bind, pure, Except.pure]
  simp only [Miri.Memory.InitCopy.noBytesInit, Bool.false_eq_true, ↓reduceIte]
  change ∃ alloc', (Miri.Memory.Allocation.writeUninit
    (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat dstStart))
      (Miri.ABI.Size.ofBytes (UInt64.ofNat total)))
    (Miri.ABI.Size.ofBytes 8) _) = Except.ok () alloc'
  have hendD := copyRange_endExclusive hltD
  have hclear := Miri.Memory.ProvenanceMap.clear_new (P := AnnealProv)
    (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat dstStart))
      (Miri.ABI.Size.ofBytes (UInt64.ofNat total)))
    (copyAlloc_raw D) (Miri.ABI.Size.ofBytes 8) _ (by decide) hendD
  unfold Miri.Memory.Allocation.writeUninit
  dsimp only [bind, Except.bind, pure, Except.pure]
  exact ⟨_, rfl⟩

theorem annealMemCopy_live_uninit_range_ok
    {st : AnnealStepState}
    {srcBytes dstBytes : Nat}
    (hnS : ValidScalarBytes srcBytes) (hnD : ValidScalarBytes dstBytes)
    {srcStart dstStart total : Nat}
    (hpos : 0 < total) (hinS : srcStart + total ≤ srcBytes) (hinD : dstStart + total ≤ dstBytes)
    (srcId : Miri.Memory.AllocId) (srcTag : Miri.Memory.BorTag)
    (srcLA : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind)
    (dstId : Miri.Memory.AllocId) (dstTag : Miri.Memory.BorTag)
    (dstLA : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind)
    (hdisj : srcId = dstId → srcStart + total ≤ dstStart ∨ dstStart + total ≤ srcStart)
    (hsrc_id : srcId.value.toNat < 2 ^ 32)
    (hsrc_base : st.machine.lookupBaseAddr srcId = some (annealStackBaseAddr srcId))
    (hsrc_live : st.machine.memory.live.find? (fun entry => entry.1 == srcId) = some (srcId, srcLA))
    (hsrc_shape : StackScalarAllocShape (translateSizeBytes srcBytes) srcLA.allocation)
    (hsrc_uninit : srcLA.allocation.initializationMask =
      Miri.Memory.InitMask.new (translateSizeBytes srcBytes) false)
    (hdst_id : dstId.value.toNat < 2 ^ 32)
    (hdst_base : st.machine.lookupBaseAddr dstId = some (annealStackBaseAddr dstId))
    (hdst_live : st.machine.memory.live.find? (fun entry => entry.1 == dstId) = some (dstId, dstLA))
    (hdst_shape : StackScalarAllocShape (translateSizeBytes dstBytes) dstLA.allocation) :
    ∃ mach', annealMemCopy
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr srcId + UInt64.ofNat srcStart),
        some (.concrete srcId srcTag)⟩
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr dstId + UInt64.ofNat dstStart),
        some (.concrete dstId dstTag)⟩
      (Miri.ABI.Size.ofBytes (UInt64.ofNat total)) true st = .ok () { st with machine := mach' } := by
  have hle : total ≤ isizeMaxBytes := by
    unfold isizeMaxBytes; rcases hnS with rfl | rfl | rfl | rfl | rfl <;> omega
  have hts : Miri.ABI.Size.ofBytes (UInt64.ofNat total) = translateSizeBytes total := by
    have _ : total < 2^64 := by rcases hnS with rfl | rfl | rfl | rfl | rfl <;> omega
    exact Miri.ABI.Size.ext rfl
  have hsrc_sz : srcLA.allocation.byteSize.bytes.toNat = srcBytes := by
    rw [hsrc_shape.byteSize_eq]; rcases hnS with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hdst_sz : dstLA.allocation.byteSize.bytes.toNat = dstBytes := by
    rw [hdst_shape.byteSize_eq]; rcases hnD with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hsame : (srcId == dstId) = true → srcStart + total ≤ dstStart ∨ dstStart + total ≤ srcStart := by
    intro h
    exact hdisj (eq_of_beq h)
  obtain ⟨alloc', hcopy⟩ := hsrc_shape.copyRepeatedly_range_uninit hnS hnD hpos hinS hinD
    hsrc_uninit hdst_shape (srcId == dstId) hsame
  have heq := annealMemCopy_live_inbounds_eq (st := st) srcId srcTag srcStart srcLA dstId dstTag dstStart dstLA
    hsrc_id (by decide) hsrc_base hsrc_live hinS
    hdst_id (by decide) hdst_base hdst_live hinD hpos hle
  rw [hts, hcopy] at heq
  exact ⟨_, heq⟩
