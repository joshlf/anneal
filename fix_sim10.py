import sys
path = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean"
with open(path, "r") as f:
    content = f.read()

replacement = """              | none =>
                rw [hoffset] at hforce11
                have ⟨res_mp, m12, h_mp, hforce12⟩ := split_bind hforce11
                dsimp [pure, EStateM.pure] at h_mp
                injection h_mp with _ hm12; subst m12 res_mp
                dsimp [pure, EStateM.pure] at hforce12
                injection hforce12 with h_res_mplace hm13; subst m'
                -- we need to prove StateRel body s m10
                sorry"""

content = content.replace(
    """              | none =>
                rw [hoffset] at hforce11
                have ⟨res_mp, m12, h_mp, hforce12⟩ := split_bind hforce11
                dsimp [pure, EStateM.pure] at h_mp
                injection h_mp with _ hm12; subst m12 res_mp
                dsimp [pure, EStateM.pure] at hforce12
                injection hforce12 with h_res_mplace hm13; subst m'
                
                -- now we prove StateRel body s (m9 updated with frame_new)
                -- state6 is m6, m9 is m6 since getFrame/setFrame don't change machine/memory
                -- wait, m10 is `m9` with updated stack
                -- wait, what is m10 exactly? It is Miri.Interpreter.State.mk m9.machine { m9.stack with frames := #[frame_new] } m9.memory m9.random m9.terminal
                -- and frame_new is topFrame6 with localId updated.
                -- Let's construct the relation.
                have h_frame_new : FrameRel body m10.machine s.frame frame_new := by
                  have h_frame_new_rel : FrameRel body m6.machine s.frame frame_new := by
                    -- hfr6 is FrameRel body m6.machine s.frame topFrame6
                    -- frame_new is topFrame6 with setLocalOperand
                    sorry
                  exact h_frame_new_rel
                sorry""",
    replacement
)

with open(path, "w") as f:
    f.write(content)
