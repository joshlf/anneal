import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "r") as f:
    content = f.read()

target = """theorem StateRel_allocateStack {body s m layout allocated m'}
  (hstate : StateRel body s m)
  (h_alloc : (annealPlaceHooks body.localDecls body.layouts).allocateStack () layout m = EStateM.Result.ok allocated m') :
  StateRel body s m' ∧ m'.stack.frames = m.stack.frames ∧ True := by
  dsimp [annealPlaceHooks, Miri.Interpreter.PlaceHooks.allocateStack] at h_alloc
  trace_state; sorry"""

replacement = """theorem StateRel_allocateStack {body s m layout allocated m'}
  (hstate : StateRel body s m)
  (h_alloc : (annealPlaceHooks body.localDecls body.layouts).allocateStack () layout m = EStateM.Result.ok allocated m') :
  StateRel body s m' ∧ m'.stack.frames = m.stack.frames ∧ True := by
  dsimp [annealPlaceHooks, Miri.Interpreter.PlaceHooks.allocateStack] at h_alloc
  cases h_alloc_new : Miri.Memory.Allocation.tryNew layout.layout.size layout.layout.align.abi Miri.Memory.InitMaskMaterialized.Uninit (fun _ _ => none) with
  | error e =>
    rw [h_alloc_new] at h_alloc
    dsimp [throw, EStateM.throw] at h_alloc
    contradiction
  | ok allocation =>
    rw [h_alloc_new] at h_alloc
    dsimp [bind, pure, EStateM.pure, get, EStateM.get, StateT.get] at h_alloc
    cases h_res : m.machine.memory.reserveAllocId with | mk mem_new res =>
    rw [h_res] at h_alloc
    dsimp only at h_alloc
    cases h_id : res with
    | error e =>
      rw [h_id] at h_alloc
      dsimp [throw, EStateM.throw] at h_alloc
      contradiction
    | ok id =>
      rw [h_id] at h_alloc
      dsimp [pure, EStateM.pure, set, EStateM.set, StateT.set] at h_alloc
      injection h_alloc with _ hm_eq
      subst hm_eq
      sorry"""

if target in content:
    content = content.replace(target, replacement)
else:
    print("NOT FOUND")

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "w") as f:
    f.write(content)
