import re
with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "r") as f:
    content = f.read()

replacement = """          | scalarPair sc1 sc2 =>
            -- scalarPair throws unsupported in writeMemoryNoValidate
            have ⟨res_write, m7, h_write, hforce7⟩ := split_bind hforce6
            dsimp [annealPlaceHooks, Miri.Interpreter.PlaceHooks.writeMemoryNoValidate, throw, EStateM.throw] at h_write
            contradiction"""

content = re.sub(r"(\s*)\| scalarPair sc1 sc2 =>\n\s*sorry", replacement, content)

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "w") as f:
    f.write(content)
