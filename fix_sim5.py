import re
with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "r") as f:
    content = f.read()

replacement = """              | some off =>
                rw [hoffset] at hforce11
                have ⟨res_off, m12, h_off, _⟩ := split_bind hforce11
                dsimp [annealPlaceHooks, Miri.Interpreter.PlaceHooks.memoryOffset, throw, EStateM.throw] at h_off
                contradiction"""

content = re.sub(r"(\s*)\| some off =>\n\s*rw \[hoffset\] at hforce11\n\s*sorry", replacement, content)

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "w") as f:
    f.write(content)
