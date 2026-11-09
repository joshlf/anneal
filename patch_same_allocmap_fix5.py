import re

file_path = "lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean"
with open(file_path, 'r') as f:
    content = f.read()

bad1 = """      have hperm_d : e_d'.perm = .active ∨ e_d'.perm = .reserved := Or.inl (by
        rw [hed_eq]
        have ⟨h, _⟩ := hlive_ok.2.2.2 e_d hed_in rfl
        exact h)"""

good1 = """      have hperm_d : e_d'.perm = .active ∨ e_d'.perm = .reserved := Or.inl (by
        rw [hed_eq]
        have hor := hlive_ok.2.2.2 e_d hed_in rfl
        cases hor with
        | inl h1 => exact h1.2
        | inr h2 => exact False.elim (h2.1 hed_tag))"""

bad2 = """          have heq_local : e.localIdx = e_d.localIdx := Nat.eq_of_beq_eq_true hlocal
          have hneq_tag : e.tag ≠ dstPtr.tag := fun h => by rw [h, Nat.beq_self_eq_true] at htag; contradiction
          have ⟨_, h_dis⟩ := hlive_ok.2.2.2 e he heq_local
          have hd : e.perm = .disabled := h_dis hneq_tag
          have hb : e.tag.beq dstPtr.tag = false := by
            cases Nat.beq e.tag dstPtr.tag <;> (try rfl)
            have := Nat.eq_of_beq_eq_true (by assumption)
            contradiction
          simp only [hb, ↓reduceIte]
          cases e
          dsimp only at hd |-
          rw [hd]"""

good2 = """          have heq_local : e.localIdx = e_d.localIdx := Nat.eq_of_beq_eq_true hlocal
          have hneq_tag : e.tag ≠ dstPtr.tag := fun h => by rw [h, Nat.beq_self_eq_true] at htag; contradiction
          have hor := hlive_ok.2.2.2 e he heq_local
          have hd : e.perm = .disabled := by
            cases hor with
            | inl h1 => exact False.elim (hneq_tag h1.1)
            | inr h2 => exact h2.2
          have hb : e.tag.beq dstPtr.tag = false := by
            cases h : Nat.beq e.tag dstPtr.tag <;> (try rfl)
            have := Nat.eq_of_beq_eq_true h
            exact False.elim (hneq_tag this)
          simp only [hb, ↓reduceIte]
          cases e
          dsimp only at hd |-
          rw [hd]"""

content = content.replace(bad1, good1)
content = content.replace(bad2, good2)
with open(file_path, 'w') as f:
    f.write(content)
