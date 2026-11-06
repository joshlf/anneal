import sys
path = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean"
with open(path, "r") as f:
    content = f.read()

replacement = """                      have hlt_mf : localId < topFrame6.locals.size := by
                        have h_op_copy := h_op
                        unfold Miri.Interpreter.Frame.getLocalOperand at h_op_copy
                        unfold Miri.Interpreter.Frame.getLocal at h_op_copy
                        dsimp [get?, Array.get?] at h_op_copy
                        split at h_op_copy
                        · exact ‹localId < topFrame6.locals.size›
                        · contradiction
                      
                      have hlt_af : localId < s.frame.locals.length := by
                        rw [hfr6.af_locals_len, ← hfr6.mf_locals_size]
                        exact hlt_mf
                      
                      have h_loc_val : topFrame6.locals[localId]'hlt_mf = ⟨.live (.immediate .uninit), topFrame6.locals[localId]'hlt_mf |>.layout⟩ := by
                        have h_op_copy := h_op
                        unfold Miri.Interpreter.Frame.getLocalOperand at h_op_copy
                        unfold Miri.Interpreter.Frame.getLocal at h_op_copy
                        dsimp [get?, Array.get?, getElem] at h_op_copy
                        simp only [hlt_mf, ↓reduceDIte] at h_op_copy
                        injection h_op_copy with h_op_eq
                        -- h_op_eq is topFrame6.locals[localId].value = .live (.immediate .uninit)
                        cases h_local : topFrame6.locals[localId]'hlt_mf with | mk val lay =>
                        dsimp at h_op_eq
                        subst h_op_eq
                        rfl

                      have h_decl_eq : get? body.localDecls localId = some decl := by
                        -- wait, decl is NOT in scope! We just use body.localDecls.get?
                        sorry
                      trace_state
                      sorry"""

content = content.replace(
    """                      have hlt_af : localId < s.frame.locals.length := by
                        -- localId is a valid index, we can get it from h_loc_orig
                        sorry
                      have h_loc_orig := hfr6.locals_rel localId decl (s.frame.locals.get! localId) (topFrame6.locals.get! localId) sorry sorry sorry
                      trace_state
                      sorry""",
    replacement
)

with open(path, "w") as f:
    f.write(content)
