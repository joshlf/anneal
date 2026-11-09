with open("lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean", "r") as f:
    content = f.read()

target = """  dsimp only [bind, Except.bind, pure, Except.pure]
  unfold Miri.Memory.InitMask.prepareCopy"""
replace = """  unfold Miri.Memory.InitMask.prepareCopy"""

if target in content:
    content = content.replace(target, replace)
    print("Fix dsimp 1 applied")
else:
    print("Fix dsimp 1 failed")

target2 = """  dsimp only [bind, Except.bind, pure, Except.pure]
  have hb1 : (false == true) = false := rfl"""
replace2 = """  have hb1 : (false == true) = false := rfl"""

if target2 in content:
    content = content.replace(target2, replace2)
    print("Fix dsimp 2 applied")
else:
    print("Fix dsimp 2 failed")

with open("lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean", "w") as f:
    f.write(content)
