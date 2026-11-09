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

print("Lines from", start_idx, "to", end_idx)
with open("lines_to_replace.txt", "w") as f:
    f.writelines(lines[start_idx:end_idx])
