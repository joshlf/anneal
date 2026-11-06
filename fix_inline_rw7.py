import sys
path = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean"
with open(path, "r") as f:
    content = f.read()

content = content.replace(
    "| error e =>\n              unfold Miri.Interpreter.stackLift✝ at h_sl",
    "| .error e =>\n              dsimp [Miri.Interpreter.stackLift] at h_sl"
)
content = content.replace(
    "| ok frame_new =>\n              unfold Miri.Interpreter.stackLift✝ at h_sl",
    "| .ok frame_new =>\n              dsimp [Miri.Interpreter.stackLift] at h_sl"
)
# Revert stackLift✝ changes that were syntactically invalid
content = content.replace("unfold Miri.Interpreter.stackLift✝ at h_sl\n", "")

with open(path, "w") as f:
    f.write(content)
