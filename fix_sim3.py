import re
with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "r") as f:
    content = f.read()

content = content.replace("                      sorry\n                · exact hcal6", "                      rw [←h_frame_new_eq, h_s_frame_eq] at h_frame_new_rel\n                      exact h_frame_new_rel\n                · exact hcal6")

# Also fix the newlines in h_frame_new_eq and h_s_frame_eq
content = content.replace("                      -- wait, frame_new IS exactly topFrame6 with setLocalOperand                      have h_frame_new_eq", "                      -- wait, frame_new IS exactly topFrame6 with setLocalOperand\n                      have h_frame_new_eq")
content = content.replace("injection h with heq; rw [←heq]                      -- and s.frame.locals is NOT changed", "injection h with heq; rw [←heq]\n                      -- and s.frame.locals is NOT changed")

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "w") as f:
    f.write(content)
