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
  rcases hshapeS with ⟨hszS, hlenS, hmutS, hprovS, _⟩
  rcases hshapeD with ⟨hszD, hlenD, hmutD, hprovD, ⟨bD, hmaskD⟩⟩
  cases S with | _ rawS szS provS maskS alignS mutS extraS nbS =>
  cases D with | _ rawD szD provD maskD alignD mutD extraD nbD =>
  change szS = _ at hszS; change rawS.size = _ at hlenS
  change mutS = _ at hmutS; change provS = _ at hprovS; change maskS = _ at huninitS
  change szD = _ at hszD; change rawD.size = _ at hlenD
  change mutD = _ at hmutD; change provD = _ at hprovD; change maskD = _ at hmaskD
  subst hszS hmutS hprovS huninitS hszD hmutD hprovD hmaskD
  have hn_eqS : (translateSizeBytes srcBytes).bytes.toNat = srcBytes := by
    rcases hnS with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hn_eqD : (translateSizeBytes dstBytes).bytes.toNat = dstBytes := by
    rcases hnD with rfl | rfl | rfl | rfl | rfl <;> rfl
  unfold Miri.Memory.Allocation.copyRepeatedly
  sorry
