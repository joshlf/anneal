import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "r") as f:
    content = f.read()

lemmas = """
theorem StateRel_allocateStack {body s m layout allocated m'}
  (hstate : StateRel body s m)
  (h_alloc : (annealPlaceHooks body.localDecls body.layouts).allocateStack () layout m = EStateM.Result.ok allocated m') :
  StateRel body s m' ∧ m'.stack.frames = m.stack.frames ∧ True := by
  sorry

theorem StateRel_setFrame {body s m f m'}
  (hstate : StateRel body s m)
  (hset : (annealPlaceHooks body.localDecls body.layouts).setFrame f m = EStateM.Result.ok () m') :
  StateRel body s m' := by
  sorry

theorem StateRel_writeMemoryNoValidate {body s m val allocated m'}
  (hstate : StateRel body s m)
  (hwrite : (annealPlaceHooks body.localDecls body.layouts).writeMemoryNoValidate () val allocated m = EStateM.Result.ok () m') :
  StateRel body s m' := by
  sorry

theorem StateRel_memoryOffset {body s m whole offset mplace m'}
  (hstate : StateRel body s m)
  (hoffset : (annealPlaceHooks body.localDecls body.layouts).memoryOffset () whole offset Miri.Interpreter.OffsetMode.wrapping Miri.Interpreter.MemPlaceMeta.none m = EStateM.Result.ok mplace m') :
  StateRel body s m' := by
  sorry

"""

target = "theorem forceAllocation_preserves_StateRel"
if target in content:
    content = content.replace(target, lemmas + target)

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "w") as f:
    f.write(content)
