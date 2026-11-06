import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "r") as f:
    content = f.read()

helpers = """
theorem reserveAllocId_live_eq {Prov Extra MachineKind} (state : Miri.Memory.MemoryState Prov Extra MachineKind) (mem_new : Miri.Memory.MemoryState Prov Extra MachineKind) (res : Except Miri.Memory.AllocationIdError Miri.Memory.AllocId)
  (h : state.reserveAllocId = (mem_new, res)) : mem_new.live = state.live := by
  unfold Miri.Memory.MemoryState.reserveAllocId at h
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

theorem StateRel_allocateStack {body s m layout allocated m'}
  (hstate : StateRel body s m)
  (h_alloc : (annealPlaceHooks body.localDecls body.layouts).allocateStack () layout m = EStateM.Result.ok allocated m') :
  StateRel body s m' ∧ m'.stack.frames = m.stack.frames ∧ True := by
  dsimp [annealPlaceHooks, Miri.Interpreter.PlaceHooks.allocateStack] at h_alloc
  cases h_alloc_new : Miri.Memory.Allocation.tryNew layout.layout.size layout.layout.align.abi Miri.Memory.InitMaskMaterialized.Uninit (fun _ _ => none) with
  | error e =>
    rw [h_alloc_new] at h_alloc
    dsimp [throw, EStateM.throw] at h_alloc
    contradiction
  | ok allocation =>
    rw [h_alloc_new] at h_alloc
    dsimp [bind, pure, EStateM.pure, get, EStateM.get, StateT.get] at h_alloc
    cases h_res : m.machine.memory.reserveAllocId with | mk mem_new res =>
    rw [h_res] at h_alloc
    dsimp only at h_alloc
    cases h_id : res with
    | error e =>
      rw [h_id] at h_alloc
      dsimp [throw, EStateM.throw] at h_alloc
      contradiction
    | ok id =>
      rw [h_id] at h_alloc
      dsimp [pure, EStateM.pure, set, EStateM.set, StateT.set] at h_alloc
      injection h_alloc with _ hm_eq
      subst hm_eq
      apply And.intro
      · cases hstate with | mk tf hframes_eq hret hret_p hfr hcal hstack hbor hprot hcaller hdisj =>
        apply StateRel.mk tf
        · exact hframes_eq
        · exact hret
        · exact hret_p
        · apply FrameRel_mono_live hfr
          · intro id' alloc' h_mem
            have h_eq_reserve := reserveAllocId_live_eq m.machine.memory mem_new (Except.ok id) h_res
            dsimp [AnnealMachine.lookupBaseAddr]
            have h_push : (id', alloc') ∈ (mem_new.live.push (id, ⟨Miri.Memory.MiriMemoryKind.stack, allocation.withExtra none⟩)).toList := by
              rw [Array.toList_push]
              apply List.mem_append_of_mem_left
              rw [h_eq_reserve]
              exact h_mem
            exact h_push
          · rfl
        · exact hcal
        · exact hstack
        · exact hbor
        · exact hprot
        · exact hcaller
        · apply MemoryAllocDisjoint_mono_live hdisj
      · apply And.intro
        · rfl
        · trivial

"""

target = """theorem StateRel_allocateStack {body s m layout allocated m'}
  (hstate : StateRel body s m)
  (h_alloc : (annealPlaceHooks body.localDecls body.layouts).allocateStack () layout m = EStateM.Result.ok allocated m') :
  StateRel body s m' ∧ m'.stack.frames = m.stack.frames ∧ True := by
  sorry"""

idx = content.find(target)
if idx != -1:
    content = content[:idx] + helpers + content[idx + len(target):]
else:
    print("NOT FOUND TARGET")

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "w") as f:
    f.write(content)
