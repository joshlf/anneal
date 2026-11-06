import sys
path = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean"
with open(path, "r") as f:
    content = f.read()

replacement = """                      have hlt_af : localId < s.frame.locals.length := by
                        -- localId is a valid index, we can get it from h_loc_orig
                        sorry
                      have h_loc_orig := hfr6.locals_rel localId decl (s.frame.locals.get! localId) (topFrame6.locals.get! localId) sorry sorry sorry
                      -- use h_loc_orig to prove it
                      sorry"""

content = content.replace(
    """                      -- now we have id and allocation!
                      have h_local_rel : LocalRel m10.machine decl body.layouts (s.frame.locals[hlt_af]'sorry) ⟨.live (.indirect allocated.mplace), none⟩ := by
                        sorry
                      sorry""",
    replacement
)

with open(path, "w") as f:
    f.write(content)
