import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/Simulation.lean", "r") as f:
    sim = f.read()

# Replace usages
sim = sim.replace("annealStepHooks_storageLive_eq hframes hlt_mf hty hnotInd", "annealStepHooks_storageLive_eq hframes hlt_mf hty")
sim = sim.replace("annealStepHooks_storageDead_eq hframes hlt_mf hne hnotInd", "annealStepHooks_storageDead_eq hframes hlt_mf hne")

# Delete definitions
defs_to_delete = [
    "annealStepHooks_storageLive_eq",
    "annealStepHooks_storageDead_eq"
]

for thm in defs_to_delete:
    pattern = r"(?:@\[.*?\]\n)?(?:theorem|def)\s+" + thm + r"\b.*?(?=\n\n(?:@\[|theorem|def|/-|/--|@[a-z]+|namespace|end))"
    match = re.search(pattern, sim, re.DOTALL)
    if match:
        sim = sim[:match.start()] + sim[match.end():]
    else:
        print("Could not find", thm)

with open("lean-miri/lean/LeanMiriSpec/Correspondence/Simulation.lean", "w") as f:
    f.write(sim)
