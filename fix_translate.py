import os

with open("lean-miri/lean/LeanMiriSpec/Correspondence/Translate.lean", "r") as f:
    text = f.read()

# Revert A1's patch
patch = """      | .ok operand =>
        match op with
        | .Move _ =>
          match frame'.replaceLocalValue place.localId (.live (.immediate .uninit)) with
          | .ok frame'' =>
            let st ← get
            let idx := st.stack.frames.size - 1
            if h : idx < st.stack.frames.size then
              set { st with stack := { frames := st.stack.frames.set idx frame'' h } }
              return ⟨operand, layout⟩
            else throw (.stack .emptyStack)
          | .error e => throw (.stack e)
        | _ => return ⟨operand, layout⟩"""
replacement = "      | .ok operand => return ⟨operand, layout⟩"

if patch in text:
    text = text.replace(patch, replacement)
    print("Patch reverted.")
else:
    print("Patch not found.")

with open("lean-miri/lean/LeanMiriSpec/Correspondence/Translate.lean", "w") as f:
    f.write(text)
