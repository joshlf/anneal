import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "r") as f:
    content = f.read()

pattern = r"(\| memory mplace_mem =>\s+)(rw \[hpref\].*?)(end LeanMiriSpec\.Correspondence)"
replacement = r"\1sorry\n\n\3"
content = re.sub(pattern, replacement, content, flags=re.DOTALL)

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "w") as f:
    f.write(content)
