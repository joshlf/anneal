import LeanMiriSpec.Correspondence.CopyLM4_2
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

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
  sorry
