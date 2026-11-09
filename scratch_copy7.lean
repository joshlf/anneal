import LeanMiriSpec.Correspondence.CopyLM4_2
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

private theorem copyInitMask_prepareCopy_false_range {n off total : Nat}
    (hn : ValidScalarBytes n) (hpos : 0 < total) (hin : off + total ≤ n) :
    (Miri.Memory.InitMask.new (translateSizeBytes n) false).prepareCopy
      (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat off))
        (Miri.ABI.Size.ofBytes (UInt64.ofNat total))) = .ok ⟨false, #[]⟩ := by
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · revert off total hpos hin; decide
  · revert off total hpos hin; decide
  · revert off total hpos hin; decide
  · revert off total hpos hin; decide
  · revert off total hpos hin; decide
