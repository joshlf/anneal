import sys

with open('lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean', 'r') as f:
    lines = f.readlines()

with open('scratch_inject.lean', 'r') as f:
    inject = f.read()

with open('scratch_inject2.lean', 'r') as f:
    inject2 = f.read()

# find index of divergence theorem
idx = -1
for i, line in enumerate(lines):
    if 'theorem step_intrinsic_copyNonOverlapping_uninit_src_divergence' in line:
        idx = i
        break

# The docstring starts at idx - 8
idx -= 8

lines.insert(idx, inject + "\n" + inject2 + "\n")

with open('lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean', 'w') as f:
    f.writelines(lines)
