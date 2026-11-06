import sys
path = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean"
with open(path, "r") as f:
    content = f.read()

replacement = """                · -- FrameRel
                  have h_alloc_copy := h_alloc
                  dsimp [annealPlaceHooks, Miri.Interpreter.PlaceHooks.allocateStack] at h_alloc_copy
                  cases h_alloc_new : Miri.Memory.Allocation.tryNew layout.layout.size layout.layout.align.abi Miri.Memory.InitMaskMaterialized.Uninit (fun _ _ => none) with
                  | error e =>
                    rw [h_alloc_new] at h_alloc_copy
                    dsimp [throw, EStateM.throw] at h_alloc_copy
                    contradiction
                  | ok allocation =>
                    rw [h_alloc_new] at h_alloc_copy
                    dsimp [bind, pure, EStateM.pure, get, EStateM.get, StateT.get] at h_alloc_copy
                    cases h_res : m5.machine.memory.reserveAllocId with | mk mem_new res =>
                    rw [h_res] at h_alloc_copy
                    dsimp only at h_alloc_copy
                    cases h_id : res with
                    | error e =>
                      rw [h_id] at h_alloc_copy
                      dsimp [throw, EStateM.throw] at h_alloc_copy
                      contradiction
                    | ok id =>
                      rw [h_id] at h_alloc_copy
                      dsimp [pure, EStateM.pure, set, EStateM.set, StateT.set] at h_alloc_copy
                      injection h_alloc_copy with h_allocated_eq hm6_eq
                      
                      -- now we have id and allocation!
                      have h_local_rel : LocalRel m10.machine decl body.layouts (s.frame.locals[hlt_af]'sorry) ⟨.live (.indirect allocated.mplace), none⟩ := by
                        sorry
                      sorry"""

content = content.replace(
    """                · -- FrameRel
                  -- We first assert LocalRel.indirect for the updated local
                  have h_local_rel : LocalRel m10.machine decl body.layouts (s.frame.locals.get! localId) ⟨.live (.indirect allocated.mplace), none⟩ := by
                    -- the original local was immediate uninit
                    sorry
                  sorry""",
    replacement
)

with open(path, "w") as f:
    f.write(content)
