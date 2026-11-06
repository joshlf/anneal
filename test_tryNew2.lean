import Miri.Memory.Allocation

theorem tryNew_byteSize_eq {size align init f alloc} (h : Miri.Memory.Allocation.tryNew size align init f = Except.ok alloc) : alloc.byteSize = size := by
  unfold Miri.Memory.Allocation.tryNew at h
  sorry
