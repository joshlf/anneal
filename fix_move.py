import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "r") as f:
    content = f.read()

target = """    cases h_slot_src_eq : slot_src with
    | init v => sorry
    | uninit => sorry
    | dead => sorry"""

replacement = """    cases h_slot_src_eq : slot_src with
    | init v =>
      -- Wait, if it's init v, evalOperand succeeds, we do copyOp, set frame, etc.
      sorry
    | uninit =>
      -- If uninit, evalOperand returns error
      sorry
    | dead =>
      -- If dead, evalOperand returns error
      sorry"""

if target in content:
    content = content.replace(target, replacement)
else:
    print("NOT FOUND")

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "w") as f:
    f.write(content)
