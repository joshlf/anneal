import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "r") as f:
    content = f.read()

target = """  | memory mplace_mem =>
    sorry"""

replacement = """  | memory mplace_mem =>
    rw [hpref] at hforce
    dsimp only at hforce
    have ⟨whole, m1, h_pure, hforce_rest⟩ := split_bind hforce
    dsimp [pure, EStateM.pure] at h_pure hforce_rest
    injection h_pure with hwhole hm1
    subst m1
    injection hforce_rest with hmplace hm_eq
    subst m'
    exact hstate"""

if target in content:
    content = content.replace(target, replacement)
else:
    print("NOT FOUND")

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "w") as f:
    f.write(content)
