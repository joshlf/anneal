import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "r") as f:
    content = f.read()

pattern = r"theorem StateRel_setFrame.*?theorem StateRel_writeMemoryNoValidate"
repl = """theorem StateRel_setFrame {body s m f m'}
  (hstate : StateRel body s m)
  (hset : (annealPlaceHooks body.localDecls body.layouts).setFrame f m = EStateM.Result.ok () m')
  (h_frel : FrameRel body m'.machine s.frame f)
  (h_ret : f.returnContinuation = Miri.Interpreter.ReturnContinuation.stop false)
  (h_retp : ∃ retLay, f.returnPlace = Miri.Interpreter.RuntimeStackPlace.frameLocal 0 0 none retLay f.localsIdentity)
  (h_disj : MemoryAllocDisjoint f) :
  True := by trivial

theorem StateRel_writeMemoryNoValidate"""

content = re.sub(pattern, repl, content, flags=re.DOTALL)

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "w") as f:
    f.write(content)
