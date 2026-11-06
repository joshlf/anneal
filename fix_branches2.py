import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "r") as f:
    content = f.read()

target = """            unfold Miri.Interpreter.Stack.currentFrame? at h_get_rest
            rw [hframes_m6] at h_get_rest"""

replacement = """            unfold Miri.Interpreter.Stack.currentFrame? at h_get_rest
            trace_state
            rw [hframes_m6] at h_get_rest"""

idx = content.find(target)
if idx != -1:
    content = content.replace(target, replacement)
else:
    print("NOT FOUND")

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "w") as f:
    f.write(content)
