with open("lean-miri/lean/LeanMiriSpec/Correspondence/Simulation.lean", "r") as f:
    lines = f.readlines()

out = []
skip = False

for line in lines:
    if line.startswith("theorem get?_eq_getElem?"):
        skip = True
    elif line.startswith("theorem translateBody_locals_getElem?"):
        skip = True
    elif line.startswith("theorem translateBody_basicBlocks_getElem?"):
        skip = True
    elif line.startswith("theorem translateBasicBlockData_statements_getElem?"):
        skip = True
    
    # We skip until we hit another theorem, def, or `@[simp]` or `/-` that we want to KEEP.
    if skip:
        # Wait, if we hit a blank line, we might still be in the theorem.
        # If we hit `theorem ` or `@[` or `/-` we stop skipping.
        if line.startswith("@[simp]") or line.startswith("theorem ") or line.startswith("/-"):
            if not (line.startswith("theorem get?_eq_getElem?") or 
                    line.startswith("theorem translateBody_locals_getElem?") or
                    line.startswith("theorem translateBody_basicBlocks_getElem?") or
                    line.startswith("theorem translateBasicBlockData_statements_getElem?")):
                skip = False
    
    if not skip:
        out.append(line)

with open("lean-miri/lean/LeanMiriSpec/Correspondence/Simulation.lean", "w") as f:
    f.writelines(out)
