import re

file_path = "lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean"
with open(file_path, 'r') as f:
    content = f.read()

start = "          have hd : e.perm = .disabled := h_dis hneq_tag"
end = "  rw [heq] at hexp"

idx1 = content.find(start)
idx2 = content.find(end)

old_body = content[idx1:idx2]

new_body = """          have hd : e.perm = .disabled := h_dis hneq_tag
          have hb : e.tag.beq dstPtr.tag = false := by
            cases Nat.beq e.tag dstPtr.tag <;> (try rfl)
            have := Nat.eq_of_beq_eq_true (by assumption)
            contradiction
          simp only [hb, ↓reduceIte]
          cases e
          dsimp only at hd |-
          rw [hd]
"""

content = content.replace(old_body, new_body)
with open(file_path, 'w') as f:
    f.write(content)
