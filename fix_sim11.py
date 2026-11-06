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
                · sorry"""

content = content.replace(
    """              | none =>
                rw [hoffset] at hforce11
                have ⟨res_mp, m12, h_mp, hforce12⟩ := split_bind hforce11
                dsimp [pure, EStateM.pure] at h_mp
                injection h_mp with _ hm12; subst m12 res_mp
                dsimp [pure, EStateM.pure] at hforce12
                injection hforce12 with h_res_mplace hm13; subst m'
                trace_state
                sorry""",
    replacement
)

with open(path, "w") as f:
    f.write(content)
