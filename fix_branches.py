import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "r") as f:
    content = f.read()

inline_proof = """          cases hval : val with
          | uninit =>
            rw [hval] at hforce6
            dsimp only at hforce6
            have ⟨res_after, m7, h_after, hforce7⟩ := split_bind hforce6
            dsimp [annealPlaceHooks, Miri.Interpreter.PlaceHooks.afterLocalMovedToMemory, pure, EStateM.pure] at h_after
            injection h_after with _ hm7; subst m7
            
            have ⟨res_f2, m8, h_f2, hforce8⟩ := split_bind hforce7
            unfold Miri.Interpreter.PlaceHooks.getFrame at h_f2
            have ⟨state_get, m_get, h_get, h_get_rest⟩ := split_bind h_f2
            dsimp [get, EStateM.get, StateT.get] at h_get
            injection h_get with _ hm_get; subst m_get state_get
            
            have hrel6 := StateRel_allocateStack hstate5 h_alloc
            rcases hrel6 with ⟨hstate6, hframes6, _⟩
            cases hstate6 with | mk topFrame6 hframes_m6 hret6 hret_p6 hfr6 hcal6 hstack6 hbor6 hprot6 hcaller6 hdisj6 =>
            
            unfold Miri.Interpreter.Stack.currentFrame? at h_get_rest
            rw [hframes_m6] at h_get_rest
            dsimp [Array.back?] at h_get_rest
            dsimp [pure, EStateM.pure] at h_get_rest
            injection h_get_rest with hm8_frame hm8; subst m8 res_f2
            
            have ⟨res_sl, m9, h_sl, hforce9⟩ := split_bind hforce8
            cases h_set_op : (topFrame6.setLocalOperand localId (Miri.Interpreter.Operand.indirect allocated.mplace)) with
            | error e =>
              rw [h_set_op] at h_sl
              dsimp [throw, EStateM.throw] at h_sl
              contradiction
            | ok frame_new =>
              rw [h_set_op] at h_sl
              dsimp [pure, EStateM.pure] at h_sl
              injection h_sl with _ hm9; subst m9
              
              have ⟨res_sf, m10, h_sf, hforce10⟩ := split_bind hforce9
              dsimp [annealPlaceHooks, Miri.Interpreter.PlaceHooks.setFrame] at h_sf
              have ⟨state_get_sf, m_get_sf, h_get_sf, h_get_rest_sf⟩ := split_bind h_sf
              dsimp [get, EStateM.get, StateT.get] at h_get_sf
              injection h_get_sf with _ hm_get_sf; subst m_get_sf state_get_sf
              
              -- setFrame evaluates `if idx < size`
              have h_get_rest_sf' : (if h_idx : m9.stack.frames.size - 1 < m9.stack.frames.size then EStateM.set { m9 with stack := { frames := m9.stack.frames.set (m9.stack.frames.size - 1) frame_new h_idx } } else throw (Miri.Interpreter.StepError.stack Miri.Interpreter.EmptyStackError.emptyStack)) = EStateM.Result.ok () m10 := h_get_rest_sf
              
              have h_frames_m9 : m9.stack.frames = #[topFrame6] := hframes_m6
              rw [h_frames_m9] at h_get_rest_sf'
              dsimp [Array.size, List.length] at h_get_rest_sf'
              
              -- inside the if, it's set
              -- We will just apply a sorry here for the rest of uninit
              sorry

          | scalar sc =>
            sorry
          | scalarPair sc1 sc2 =>
            sorry"""

target = """          cases hval : val with
          | uninit =>
            sorry

          | scalar sc =>
            rw [hval] at hforce6
            dsimp only at hforce6
            trace_state; sorry
          | scalarPair sc1 sc2 =>
            rw [hval] at hforce6
            dsimp only at hforce6
            trace_state; sorry"""

idx = content.find(target)
if idx != -1:
    content = content[:idx] + inline_proof + content[idx + len(target):]
else:
    print("NOT FOUND")

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "w") as f:
    f.write(content)
