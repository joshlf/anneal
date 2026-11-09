import LeanMiriSpec
open LeanMiriSpec
open Miri.Memory

theorem copyInitMask_prepareCopy_false_range {n off total : Nat}
    (hn : ValidScalarBytes n) (hpos : 0 < total) (hinb : off + total ≤ n) :
    (Miri.Memory.InitMask.new (translateSizeBytes n) false).prepareCopy
      (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat off))
        (Miri.ABI.Size.ofBytes (UInt64.ofNat total))) =
      .ok ⟨false, #[UInt64.ofNat total]⟩ := by
  sorry
