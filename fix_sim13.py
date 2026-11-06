import sys
path = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean"
with open(path, "r") as f:
    content = f.read()

replacement = """                · -- FrameRel
                  -- We first assert LocalRel.indirect for the updated local
                  have h_local_rel : LocalRel m10.machine decl body.layouts (s.frame.locals.get! localId) ⟨.live (.indirect allocated.mplace), none⟩ := by
                    -- the original local was immediate uninit
                    sorry
                  sorry"""

content = content.replace(
    "                · sorry\n                · exact hcal6",
    replacement + "\n                · exact hcal6"
)

with open(path, "w") as f:
    f.write(content)
