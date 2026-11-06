import os

with open("lean-miri/lean/LeanMiriSpec/Correspondence/Witness.lean", "r") as f:
    text = f.read()

text = text.replace("(by sorry)", "(by apply MemoryAllocDisjoint.of_no_indirect; intro k x hk m; revert hk; decide)")

with open("lean-miri/lean/LeanMiriSpec/Correspondence/Witness.lean", "w") as f:
    f.write(text)
