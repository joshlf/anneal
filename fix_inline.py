import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "r") as f:
    content = f.read()

target = """          | Miri.Interpreter.Immediate.uninit =>
            sorry

          | scalar sc =>
            rw [hval] at hforce6
            dsimp only at hforce6
            trace_state; sorry
          | scalarPair sc1 sc2 =>
            rw [hval] at hforce6
            dsimp only at hforce6
            trace_state; sorry
  | memory mplace_mem =>
    sorry"""

# I need to see the tactic state at the `uninit` branch to write the inline proof.
# I'll replace sorry with trace_state in uninit.
replacement = """          | Miri.Interpreter.Immediate.uninit =>
            rw [hval] at hforce6
            dsimp only at hforce6
            trace_state
            sorry

          | scalar sc =>
            rw [hval] at hforce6
            dsimp only at hforce6
            sorry
          | scalarPair sc1 sc2 =>
            rw [hval] at hforce6
            dsimp only at hforce6
            sorry
  | memory mplace_mem =>
    sorry"""

idx = content.find(target)
if idx != -1:
    content = content.replace(target, replacement)
else:
    print("NOT FOUND")

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "w") as f:
    f.write(content)
