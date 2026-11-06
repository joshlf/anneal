import Miri
open Miri.Memory

theorem reserveAllocId_live_eq {Prov Extra MachineKind} (state : MemoryState Prov Extra MachineKind) (mem_new : MemoryState Prov Extra MachineKind) (res : Except AllocationIdError AllocId)
  (h : state.reserveAllocId = (mem_new, res)) : mem_new.live = state.live := by
  unfold MemoryState.reserveAllocId at h
  dsimp [Id.run] at h
  split at h
  · injection h with h1 h2; subst h1; rfl
  · split at h
    · injection h with h1 h2; subst h1; rfl
    · split at h
      · injection h with h1 h2; subst h1
        cases state.sourceAllocIdWorldActive <;> rfl
      · split at h
        · injection h with h1 h2; subst h1
          cases state.sourceAllocIdWorldActive <;> rfl
        · split at h
          · injection h with h1 h2; subst h1
            cases state.sourceAllocIdWorldActive <;> rfl
          · injection h with h1 h2; subst h1
            cases state.sourceAllocIdWorldActive <;> rfl

theorem reserveAllocId_base_eq {Prov Extra MachineKind} (state : MemoryState Prov Extra MachineKind) (mem_new : MemoryState Prov Extra MachineKind) (res : Except AllocationIdError AllocId)
  (h : state.reserveAllocId = (mem_new, res)) : mem_new.globalTable = state.globalTable := by
  unfold MemoryState.reserveAllocId at h
  dsimp [Id.run] at h
  split at h
  · injection h with h1 h2; subst h1; rfl
  · split at h
    · injection h with h1 h2; subst h1; rfl
    · split at h
      · injection h with h1 h2; subst h1
        cases state.sourceAllocIdWorldActive <;> rfl
      · split at h
        · injection h with h1 h2; subst h1
          cases state.sourceAllocIdWorldActive <;> rfl
        · split at h
          · injection h with h1 h2; subst h1
            cases state.sourceAllocIdWorldActive <;> rfl
          · injection h with h1 h2; subst h1
            cases state.sourceAllocIdWorldActive <;> rfl
