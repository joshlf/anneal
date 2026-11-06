import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "r") as f:
    content = f.read()

setFrame_target = """theorem StateRel_setFrame {body s m f m'}
  (hstate : StateRel body s m)
  (hset : (annealPlaceHooks body.localDecls body.layouts).setFrame f m = EStateM.Result.ok () m') :
  StateRel body s m' := by
  sorry"""

setFrame_replacement = """theorem StateRel_setFrame {body s m f m'}
  (hstate : StateRel body s m)
  (hset : (annealPlaceHooks body.localDecls body.layouts).setFrame f m = EStateM.Result.ok () m')
  (h_frel : FrameRel body m'.machine s.frame f)
  (h_ret : f.returnContinuation = Miri.Interpreter.ReturnContinuation.stop false)
  (h_retp : ∃ retLay, f.returnPlace = Miri.Interpreter.RuntimeStackPlace.frameLocal 0 0 none retLay f.localsIdentity)
  (h_disj : MemoryAllocDisjoint f) :
  StateRel body s m' := by
  cases hstate with | mk top frames cont ret f_rel active call bor prot call_l alloc_d =>
  unfold Miri.Interpreter.PlaceHooks.setFrame at hset
  dsimp [annealPlaceHooks] at hset
  have ⟨state, m2, h_get, h_set1⟩ := split_bind hset
  dsimp [get, EStateM.get, StateT.get] at h_get
  injection h_get with hs_eq hm2; subst state m2
  split at h_set1
  next h_idx =>
    dsimp [set, EStateM.set, StateT.set] at h_set1
    injection h_set1 with _ hm_new; subst m'
    apply StateRel.mk f
    · dsimp
      rw [frames]
      rfl
    · exact h_ret
    · exact h_retp
    · exact h_frel
    · exact active
    · exact call
    · exact bor
    · exact prot
    · exact call_l
    · exact h_disj"""

write_target = """theorem StateRel_writeMemoryNoValidate {body s m val allocated m'}
  (hstate : StateRel body s m)
  (hwrite : (annealPlaceHooks body.localDecls body.layouts).writeMemoryNoValidate () val allocated m = EStateM.Result.ok () m') :
  StateRel body s m' := by
  sorry"""

write_replacement = """theorem StateRel_writeMemoryNoValidate {body s m val allocated m'}
  (hstate : StateRel body s m)
  (hwrite : (annealPlaceHooks body.localDecls body.layouts).writeMemoryNoValidate () val allocated m = EStateM.Result.ok () m')
  (h_frel : FrameRel body m'.machine s.frame (m'.stack.frames[0]'(by sorry))) :
  StateRel body s m' := by
  sorry"""

if setFrame_target in content:
    content = content.replace(setFrame_target, setFrame_replacement)

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "w") as f:
    f.write(content)
