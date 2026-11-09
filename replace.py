with open("lines_to_replace.txt", "r") as f:
    target = f.read()

with open("replacement.lean", "r") as f:
    replacement = f.read() + "\n"

with open("lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean", "r") as f:
    content = f.read()

content = content.replace(target, replacement)

with open("lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean", "w") as f:
    f.write(content)
