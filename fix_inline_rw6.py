import sys
path = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean"
with open(path, "r") as f:
    content = f.read()

content = content.replace(
    "            | error e =>\n              rw [h_set_op] at h_sl\n              dsimp [throw, EStateM.throw] at h_sl\n              contradiction",
    "            | error e =>\n              unfold Miri.Interpreter.stackLift✝ at h_sl\n              rw [h_set_op] at h_sl\n              dsimp [throw, EStateM.throw] at h_sl\n              contradiction"
)
content = content.replace(
    "            | ok frame_new =>\n              rw [h_set_op] at h_sl\n              dsimp [pure, EStateM.pure] at h_sl\n              injection h_sl with _ hm9; subst m9",
    "            | ok frame_new =>\n              unfold Miri.Interpreter.stackLift✝ at h_sl\n              rw [h_set_op] at h_sl\n              dsimp [pure, EStateM.pure] at h_sl\n              injection h_sl with _ hm9; subst m9"
)

with open(path, "w") as f:
    f.write(content)
