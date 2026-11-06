import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/Simulation.lean", "r") as f:
    content = f.read()

# Find rcases hstate with ... hcaller⟩
sorries = re.findall(r"rcases hstate with\s*⟨[^⟨]+⟨retLay, hretPlace⟩[^⟩]+hcaller⟩", content)
print(f"Found {len(sorries)} rcases without hdisj")

# Also other rcases on StateRel
# StepRel.step
