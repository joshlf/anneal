import sys
path = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean"
with open(path, "r") as f:
    content = f.read()

replacement = """              | none =>
                rw [hoffset] at hforce11
                have ⟨res_mp, m12, h_mp, hforce12⟩ := split_bind hforce11
                dsimp [pure, EStateM.pure] at h_mp
                injection h_mp with hm12_1 hm12; subst m12
                dsimp [pure, EStateM.pure] at hforce12
                injection hforce12 with h_res_mplace hm13; subst m'
                
                -- now we prove StateRel body s m10
                have hm10_eq : m10 = Miri.Interpreter.State.mk m10.machine { m10.stack with frames := #[frame_new] } m10.memory m10.random m10.terminal := by rfl
                -- wait, m10 was constructed by EStateM.set.
                apply StateRel.mk frame_new
                · exact rfl
                · exact hret6
                · exact hret_p6
                · sorry
                · exact hcal6
                · exact hstack6
                · exact hbor6
                · exact hprot6
                · exact hcaller6
                · exact MemoryAllocDisjoint_mono_live hdisj6"""

content = content.replace(
    """              | none =>
                rw [hoffset] at hforce11
                have ⟨res_mp, m12, h_mp, hforce12⟩ := split_bind hforce11
                dsimp [pure, EStateM.pure] at h_mp
                injection h_mp with _ hm12; subst m12 res_mp
                dsimp [pure, EStateM.pure] at hforce12
                injection hforce12 with h_res_mplace hm13; subst m'
                
                apply StateRel.mk frame_new
                · rfl
                · exact hret6
                · exact hret_p6
                · sorry
                · exact hcal6
                · exact hstack6
                · exact hbor6
                · exact hprot6
                · exact hcaller6
                · sorry""",
    replacement
)

with open(path, "w") as f:
    f.write(content)
