import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/Simulation.lean", "r") as f:
    lines = f.readlines()

for i, line in enumerate(lines):
    if "(by sorry)" in line and "hcal hstack hbor hprot hcaller" in line:
        print(f"Line {i}: {line.strip()}")
