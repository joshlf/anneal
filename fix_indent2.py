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
    
    if in_cases and line.startswith("    have hiter0") or line.startswith("    have hiter1"):
        new_lines.append(line)
    elif in_cases and line.startswith("    ") and not line.strip().startswith("have hiter"):
        if "unfold Miri.Memory.InitMask.collectChunksAux" in line:
            new_lines.append(line)
        elif "simp only [hiter0," in line:
            new_lines.append(line)
        elif "simp only [hiter1," in line:
            new_lines.append(line)
        elif "rw [ht]" in line:
            new_lines.append(line)
        elif "rfl" in line and len(line) < 10:
            new_lines.append(line)
        elif "unfold Miri.Memory.collectChunksAux" in line:
            new_lines.append(line)
        else:
            new_lines.append("  " + line) # Add 2 extra spaces to the body of hiter0 and hiter1
    else:
        new_lines.append(line)

with open("replacement.lean", "w") as f:
    f.writelines(new_lines)
