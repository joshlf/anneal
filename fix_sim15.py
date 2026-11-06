import sys
path = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean"
with open(path, "r") as f:
    content = f.read()

replacement = """        have hstate5 : StateRel body s m5 := by
          -- placeLayoutOfLocal only reads
          have ⟨_, _, hget1, hrest1⟩ := split_bind h_layout
          dsimp [get, EStateM.get, StateT.get] at hget1
          injection hget1 with _ hm_get; subst hm_get
          -- It then calls getFrame.
          unfold Miri.Interpreter.PlaceHooks.getFrame at hrest1
          -- wait, we don't have to unfold it completely, we know placeLayoutOfLocal is state-preserving
          -- wait! I'll just use exact hstate if m5 = m4
          sorry"""

content = content.replace(
    """        have hstate5 : StateRel body s m5 := by
          sorry""",
    replacement
)

with open(path, "w") as f:
    f.write(content)
