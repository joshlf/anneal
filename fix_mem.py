import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "r") as f:
    content = f.read()

target = """theorem StateRel_memoryOffset {body s m whole offset mplace m'}
  (hstate : StateRel body s m)
  (hoffset : (annealPlaceHooks body.localDecls body.layouts).memoryOffset () whole offset Miri.Interpreter.OffsetMode.wrapping Miri.Interpreter.MemPlaceMeta.none m = EStateM.Result.ok mplace m') :
  StateRel body s m' := by
  sorry"""

replacement = """theorem StateRel_memoryOffset {body s m whole offset mplace m'}
  (hstate : StateRel body s m)
  (hoffset : (annealPlaceHooks body.localDecls body.layouts).memoryOffset () whole offset Miri.Interpreter.OffsetMode.wrapping Miri.Interpreter.MemPlaceMeta.none m = EStateM.Result.ok mplace m') :
  StateRel body s m' := by
  dsimp [annealPlaceHooks, Miri.Interpreter.PlaceHooks.memoryOffset, throw, EStateM.throw] at hoffset
  contradiction"""

if target in content:
    content = content.replace(target, replacement)
else:
    print("NOT FOUND")

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "w") as f:
    f.write(content)
