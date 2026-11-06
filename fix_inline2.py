import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "r") as f:
    content = f.read()

uninit_logic = """          | Miri.Interpreter.Immediate.uninit =>
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
            
            unfold Miri.Interpreter.Stack.currentFrame? at h_get_rest
            rw [hframes6] at h_get_rest
            dsimp [Array.back?] at h_get_rest
            dsimp [pure, EStateM.pure] at h_get_rest
            injection h_get_rest with hm8_frame hm8; subst m8 res_f2
            
            have ⟨res_sl, m9, h_sl, hforce9⟩ := split_bind hforce8
            -- simp only [hframes6, Array.size_toArray, List.length_singleton, Nat.reduceSub, Array.getElem_toArray, List.get_singleton] at h_sl
            
            cases h_set_op : (topFrame.setLocalOperand localId (Miri.Interpreter.Operand.indirect allocated.mplace)) with
            | error e =>
              rw [h_set_op] at h_sl
              -- we can prove contradiction since it is a failure
              sorry
            | ok frame_new =>
              rw [h_set_op] at h_sl
              dsimp [pure, EStateM.pure] at h_sl
              injection h_sl with _ hm9; subst m9
              
              have ⟨res_sf, m10, h_sf, hforce10⟩ := split_bind hforce9
              -- here we apply our custom relation
              trace_state
              sorry"""

target = """          | Miri.Interpreter.Immediate.uninit =>
            rw [hval] at hforce6
            dsimp only at hforce6
            trace_state
            sorry"""

idx = content.find(target)
if idx != -1:
    content = content.replace(target, uninit_logic)
else:
    print("NOT FOUND")

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "w") as f:
    f.write(content)
