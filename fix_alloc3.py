import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "r") as f:
    content = f.read()

target = """    | ok id =>
      rw [h_id] at h_alloc
      dsimp [pure, EStateM.pure, set, EStateM.set, StateT.set] at h_alloc
      injection h_alloc with _ hm_eq
      subst hm_eq
      sorry"""

replacement = """    | ok id =>
      rw [h_id] at h_alloc
      dsimp [pure, EStateM.pure, set, EStateM.set, StateT.set] at h_alloc
      injection h_alloc with _ hm_eq
      subst hm_eq
      trace_state
      sorry"""

if target in content:
    content = content.replace(target, replacement)
else:
    print("NOT FOUND")

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "w") as f:
    f.write(content)
