import LeanMiriSpec
open Miri.Memory
theorem test (total : Nat) (htot64 : total < 2^64) (h : total ≠ 0) :
  (UInt64.ofNat total == 0) = false := by
  have h1 : (UInt64.ofNat total).toNat = total := UInt64.toNat_ofNat_of_lt htot64
  have h2 : (UInt64.ofNat 0).toNat = 0 := rfl
  change ((UInt64.ofNat total).toNat == (UInt64.ofNat 0).toNat) = false
  rw [h1, h2]
  exact decide_eq_false h
