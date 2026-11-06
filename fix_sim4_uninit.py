import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "r") as f:
    content = f.read()

pattern = r"(\| uninit =>\s+)(rw \[hval\].*?)(?=\s*\| scalar sc =>)"
replacement = r"\1sorry\n"
content = re.sub(pattern, replacement, content, flags=re.DOTALL)

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "w") as f:
    f.write(content)
