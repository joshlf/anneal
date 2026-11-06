import os

with open("lean-miri/lean/LeanMiriSpec/Correspondence/Simulation.lean", "r") as f:
    text = f.read()

text = text.replace("annealEvalOperand localDecls layouts (.Copy place) known := sorry", "annealEvalOperand localDecls layouts (.Copy place) known := rfl")

with open("lean-miri/lean/LeanMiriSpec/Correspondence/Simulation.lean", "w") as f:
    f.write(text)
