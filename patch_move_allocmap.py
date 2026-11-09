import re

file_path = "lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean"
with open(file_path, 'r') as f:
    content = f.read()

# I need to extract the definition of list_map_id and step_intrinsic_copyNonOverlapping_simulation_same_allocMap
# and move it AFTER step_intrinsic_copyNonOverlapping_simulation_explicit.

start_str = "def list_map_id"
end_str = "theorem step_intrinsic_copyNonOverlapping_simulation_explicit"

idx1 = content.find(start_str)
idx2 = content.find(end_str)

extracted = content[idx1:idx2]
content = content[:idx1] + content[idx2:]

# Now find the end of step_intrinsic_copyNonOverlapping_simulation_explicit
# It is followed by theorem step_intrinsic_copyNonOverlapping_simulation (or something)
idx3 = content.find("theorem step_intrinsic_copyNonOverlapping_simulation")
content = content[:idx3] + extracted + content[idx3:]

with open(file_path, 'w') as f:
    f.write(content)

