import sys
path = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean"
with open(path, "r") as f:
    content = f.read()

content = content.replace(
    "rw [hframes_m6] at h_get_rest",
    "simp only [hframes_m6] at h_get_rest"
)

with open(path, "w") as f:
    f.write(content)
