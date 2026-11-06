import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/Simulation.lean", "r") as f:
    sim = f.read()

dups = [
    "get\\?_eq_getElem\\?",
    "length_eq_length",
    "set\\?_eq_some_set",
    "stepMirFn_eq_of_not_other",
    "translateBody_locals_getElem\\?",
    "annealStepHooks_storageLive_eq",
    "annealStepHooks_storageDead_eq",
    "cacheFrameLocalLayout",
    "frame_getOrCacheLocalLayout_eq",
    "cacheFrameLocalLayout_getLocal",
    "translateBody_basicBlocks_getElem\\?",
    "translateBasicBlockData_statements_getElem\\?"
]

for thm in dups:
    # Match the block. Since some are def, some are theorem, some have @[simp], we need a good regex.
    pattern = r"(?:@\[.*?\]\n)?(?:theorem|def)\s+" + thm + r"\b.*?(?=\n\n(?:@\[|theorem|def|/-|/--|@[a-z]+|namespace|end))"
    match = re.search(pattern, sim, re.DOTALL)
    if match:
        sim = sim[:match.start()] + sim[match.end():]
    else:
        print("Could not find", thm)

with open("lean-miri/lean/LeanMiriSpec/Correspondence/Simulation.lean", "w") as f:
    f.write(sim)
