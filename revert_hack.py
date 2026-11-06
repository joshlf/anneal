import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/Translate.lean", "r") as f:
    text = f.read()

bad_assign = """  assign := fun choice place rvalue state =>
    let (state', result) := Miri.Interpreter.runRvalue
      (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks localDecls layouts) choice rvalue place)
      state
    match result with
    | .error _ => (state', result)
    | .ok () =>
      match rvalue with
      | .Use (.Move srcPlace) _ =>
        if srcPlace.projection.isEmpty then
          match state'.stack.currentFrame? with
          | none => (state', result)
          | some frame =>
            match frame.replaceLocalValue srcPlace.localId (.live (.immediate .uninit)) with
            | .ok frame' =>
              let idx := state'.stack.frames.size - 1
              if h : idx < state'.stack.frames.size then
                let state'' := { state' with stack := { frames := state'.stack.frames.set idx frame' h } }
                (state'', result)
              else (state', result)
            | .error _ => (state', result)
        else (state', result)
      | _ => (state', result)"""

good_assign = """  assign := fun choice place rvalue state =>
    Miri.Interpreter.runRvalue
      (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks localDecls layouts) choice rvalue place)
      state"""

if bad_assign in text:
    text = text.replace(bad_assign, good_assign)
    with open("lean-miri/lean/LeanMiriSpec/Correspondence/Translate.lean", "w") as f:
        f.write(text)
    print("Reverted hack!")
else:
    print("Could not find hack in Translate.lean")
