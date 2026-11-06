import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/Simulation.lean", "r") as f:
    sim = f.read()

dups = [
    "get\?_eq_getElem\?",
    "translateBody_locals_getElem\?",
    "translateBody_basicBlocks_getElem\?",
    "translateBasicBlockData_statements_getElem\?"
]

for thm in dups:
    pattern = r"(?:@\[.*?\]\n)?(?:theorem|def)\s+" + thm + r"\s*\(.*?(?=\n\n(?:@\[|theorem|def|/-|/--|@[a-z]+|namespace|end))"
    match = re.search(pattern, sim, re.DOTALL)
    if match:
        sim = sim[:match.start()] + sim[match.end():]
    else:
        print("Could not find", thm)

with open("lean-miri/lean/LeanMiriSpec/Correspondence/Simulation.lean", "w") as f:
    f.write(sim)
