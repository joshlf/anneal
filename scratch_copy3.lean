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
  sorry
