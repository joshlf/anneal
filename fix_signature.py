import re
with open("/usr/local/google/Projects/anneal-workspace/anneal-wt-lm-1-4/lean-miri/lean/LeanMiriSpec/Correspondence/Simulation.lean", "r") as f:
    content = f.read()

content = content.replace(
    "(hcaller : s.memory.callerLocals = .nil)\n    (hframes : m.stack.frames = #[tf₀])",
    "(hcaller : s.memory.callerLocals = .nil)\n    (hdisj : MemoryAllocDisjoint topFrame₁)\n    (hframes : m.stack.frames = #[tf₀])"
)

content = re.sub(r"(write_after_rvalue_simulation_ext hrc₁ hrp₁ hcal hstack hbor hprot hcaller\n)", r"\1          hdisj\n", content)
content = re.sub(r"(write_after_rvalue_simulation_ext hrc₂ hrp₂ hcal hstack hbor hprot hcaller\n)", r"\1              hdisj\n", content)


with open("/usr/local/google/Projects/anneal-workspace/anneal-wt-lm-1-4/lean-miri/lean/LeanMiriSpec/Correspondence/Simulation.lean", "w") as f:
    f.write(content)
