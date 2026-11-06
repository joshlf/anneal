import LeanMiriSpec.Correspondence.SimLM1_4

theorem tryNew_byteSize_eq {size align init f alloc} (h : Miri.Memory.Allocation.tryNew size align init f = Except.ok alloc) : alloc.byteSize = size := by
  unfold Miri.Memory.Allocation.tryNew at h
  dsimp [bind, Except.bind] at h
  split at h
  · split at h
    · split at h
      · injection h with h_eq; subst h_eq; rfl
      · contradiction
    · split at h
      · injection h with h_eq; subst h_eq; rfl
      · contradiction
  · contradiction
