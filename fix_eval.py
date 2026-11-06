import re
with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "r") as f:
    content = f.read()

target = """    cases h_slot_src_eq : slot_src with
    | init v => sorry
    | uninit => sorry
    | dead => sorry"""

replacement = """    cases h_slot_src_eq : slot_src with
    | init v =>
      -- if src is init v, Anneal succeeds. Miri succeeds.
      sorry
    | uninit =>
      -- if src is uninit, Anneal UB. Miri UB.
      sorry
    | dead =>
      -- if src is dead, Anneal UB. Miri UB.
      sorry"""

if target in content:
    content = content.replace(target, replacement)

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "w") as f:
    f.write(content)
