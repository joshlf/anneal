with open("replacement.lean", "r") as f:
    lines = f.readlines()

new_lines = []
in_cases = False
for line in lines:
    if line.startswith("  cases ht : total with"):
        in_cases = True
        new_lines.append(line)
        continue
    if in_cases and line.startswith("theorem StackScalarAllocShape"):
        in_cases = False
    
    if in_cases and line.startswith("  | "):
        new_lines.append(line)
        continue
    
    if in_cases and line.startswith("  ") and not line.strip().startswith("theorem"):
        new_lines.append("  " + line)
    else:
        new_lines.append(line)

with open("replacement.lean", "w") as f:
    f.writelines(new_lines)
