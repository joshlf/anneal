import sys
path = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean"
with open(path, "r") as f:
    content = f.read()

content = content.replace(
    "| error e =>\n              rw [h_set_op] at h_sl",
    "| error e =>\n              trace_state\n              rw [h_set_op] at h_sl"
)

with open(path, "w") as f:
    f.write(content)
