with open("lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean", "r") as f:
    lines = f.readlines()

start_idx = -1
for i, l in enumerate(lines):
    if l.startswith("private theorem allocRange_size"):
        start_idx = i
        break

end_idx = -1
for i, l in enumerate(lines[start_idx:]):
    if l.startswith("theorem annealMemCopy_live_uninit_range_ok"):
        end_idx = start_idx + i
        break

with open("replacement.lean", "r") as f:
    replacement = f.read()

new_content = "".join(lines[:start_idx]) + replacement + "\n" + "".join(lines[end_idx:])

with open("lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean", "w") as f:
    f.write(new_content)
