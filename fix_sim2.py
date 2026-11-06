import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "r") as f:
    content = f.read()

h_frame_new_eq_replacement = """                      have h_frame_new_eq : frame_new = { topFrame6 with locals := topFrame6.locals.set localId { topFrame6.locals[localId]'hlt_mf with value := .live (.indirect allocated.mplace) } hlt_mf } := by
                        revert h_set_op
                        unfold Miri.Interpreter.Frame.setLocalOperand
                        dsimp [bind, Except.bind]
                        cases h_get : topFrame6.getLocalOperand localId with
                        | error e =>
                          intro h; contradiction
                        | ok op =>
                          intro h
                          unfold Miri.Interpreter.Frame.replaceLocalValue at h
                          rw [dite_eq_left] at h
                          dsimp [pure, Except.pure] at h
                          injection h with heq; rw [←heq]"""

h_s_frame_eq_replacement = """                      -- and s.frame.locals is NOT changed because s.frame.locals.set localId slot is a no-op!
                      have h_s_frame_eq : { s.frame with locals := s.frame.locals.set localId slot } = s.frame := by
                        cases s.frame; dsimp only; congr
                        -- we need `List.set locals localId slot = locals`
                        -- h_slot_eq: get? locals localId = some slot
                        induction locals generalizing localId with
                        | nil =>
                          cases localId
                          · contradiction
                          · contradiction
                        | cons hd tl ih =>
                          cases localId
                          · dsimp [get?] at h_slot_eq
                            injection h_slot_eq with h_eq; rw [←h_eq]
                            rfl
                          · dsimp [get?] at h_slot_eq
                            dsimp [List.set]
                            rw [ih _ h_slot_eq]"""

content = re.sub(r"(\s*)have h_frame_new_eq : frame_new = \{ topFrame6 with locals := topFrame6.locals.set localId \{ topFrame6.locals\[localId\]'hlt_mf with value := \.live \(\.indirect allocated.mplace\) \} hlt_mf \} := by\n\s*sorry", h_frame_new_eq_replacement, content)

content = re.sub(r"(\s*)-- and s.frame.locals is NOT changed because s.frame.locals.set localId slot is a no-op!\n\s*have h_s_frame_eq : \{ s.frame with locals := s.frame.locals.set localId slot \} = s.frame := by\n\s*sorry", h_s_frame_eq_replacement, content)

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "w") as f:
    f.write(content)
