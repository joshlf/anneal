import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/Simulation.lean", "r") as f:
    content = f.read()

def replacer(match):
    return match.group(1) + "(by sorry)"

# This is just to see the exact text around those sorries
sorries = re.findall(r"hcal hstack hbor hprot hcaller \(by sorry\)", content)
print(f"Found {len(sorries)} sorries like hcal...")

# And the last one at 5872
last_sorry = re.findall(r"hcaller' \(by sorry\)", content)
print(f"Found {len(last_sorry)} last sorry...")
