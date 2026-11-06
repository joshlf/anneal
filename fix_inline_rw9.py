import sys
path = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean"
with open(path, "r") as f:
    content = f.read()

content = content.replace(
    """            | error e =>
              simp only [h_set_op] at h_sl
              dsimp [throw, EStateM.throw] at h_sl
              contradiction
            | ok frame_new =>
              simp only [h_set_op] at h_sl
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
              sorry""",
    """            | error e =>
              unfold Miri.Interpreter.stackLift at h_sl
              simp only [h_set_op] at h_sl
              dsimp [throw, EStateM.throw] at h_sl
              contradiction
            | ok frame_new =>
              unfold Miri.Interpreter.stackLift at h_sl
              simp only [h_set_op] at h_sl
              dsimp [pure, EStateM.pure] at h_sl
              injection h_sl with _ hm9; subst m9
              
              have ⟨res_sf, m10, h_sf, hforce10⟩ := split_bind hforce9
              dsimp [annealPlaceHooks, Miri.Interpreter.PlaceHooks.setFrame] at h_sf
              have ⟨state_get_sf, m_get_sf, h_get_sf, h_get_rest_sf⟩ := split_bind h_sf
              dsimp [get, EStateM.get, StateT.get] at h_get_sf
              injection h_get_sf with _ hm_get_sf; subst m_get_sf state_get_sf
              
              -- setFrame evaluates `if idx < size`
              have h_frames_m9 : m9.stack.frames = #[topFrame6] := hframes_m6
              rw [h_frames_m9] at h_get_rest_sf
              change (if h_idx : 1 - 1 < 1 then EStateM.set (Miri.Interpreter.State.mk m9.machine { m9.stack with frames := #[frame_new] } m9.memory m9.random m9.terminal) else throw _) m9 = EStateM.Result.ok () m10 at h_get_rest_sf
              dsimp only [set, EStateM.set] at h_get_rest_sf
              have h_idx_t : 1 - 1 < 1 := by decide
              simp only [h_idx_t, ↓reduceDIte] at h_get_rest_sf
              injection h_get_rest_sf with hm10_1 hm10; subst m10
              sorry"""
)

with open(path, "w") as f:
    f.write(content)
