import re
with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "r") as f:
    content = f.read()

content = content.replace("rfl                          · -- in_bounds", "rfl\n                          · -- in_bounds")
content = content.replace("h_local_rel\n                      \n                      -- wait, frame_new IS exactly", "h_local_rel\n\n                      -- wait, frame_new IS exactly")

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "w") as f:
    f.write(content)
