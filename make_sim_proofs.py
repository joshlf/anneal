import re

with open("/usr/local/google/Projects/anneal-workspace/anneal-wt-lm-1-4/lean-miri/lean/LeanMiriSpec/Correspondence/Simulation.lean", "r") as f:
    content = f.read()

# Fix rcases on hstate
content = re.sub(r"(rcases hstate with\s*⟨[^⟨]+⟨retLay, hretPlace⟩[^⟩]+)(hcaller)⟩", r"\1\2, hdisj⟩", content)
# Also fix any destruct in recursive calls
content = re.sub(r"(rcases hstate' with\s*⟨tf', htf', hrc', hrp', hfr', hcal', hstack', hbor', hprot', )(hcaller', _⟩)", r"\1hcaller', hdisj'⟩", content)

# 1. write_after_rvalue_simulation_ext
# { topFrame₂ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
proof1 = """(by
          apply MemoryAllocDisjoint.mono_immediate hdisj
          intro k
          by_cases hk : k = dstIdx
          · right
            subst hk
            exists imm, cachedLayout
            dsimp [topFrame₂]
            rw [Array.getElem?_set]
            · exact rfl
            · exact hlt_mf
          · left
            dsimp [topFrame₂]
            rw [Array.getElem?_set_ne _ _ _ hk])"""
content = re.sub(r"(write_after_rvalue_simulation_ext[\s\S]*?)(hcal hstack hbor hprot hcaller )\(by sorry\)", lambda m: m.group(1) + m.group(2) + proof1, content, count=1)

# 2. step_assign_scalar_simulation_ext - .immediate
proof2 = """(by
        apply MemoryAllocDisjoint.mono_immediate hdisj
        intro k
        by_cases hk : k = dstIdx
        · right
          subst hk
          exists imm, cachedLayout
          dsimp [topFrame]
          rw [Array.getElem?_set]
          · exact rfl
          · rw [hframe.mf_locals_size]; exact hlt_body
        · left
          dsimp [topFrame]
          rw [Array.getElem?_set_ne _ _ _ hk])"""
content = re.sub(r"(step_assign_scalar_simulation_ext[\s\S]*?topFrame with[\s\S]*?)(hcal hstack hbor hprot hcaller )\(by sorry\)", lambda m: m.group(1) + m.group(2) + proof2, content, count=1)

# 3. step_assign_scalar_simulation_ext - .uninit
proof3 = """(by
        apply MemoryAllocDisjoint.mono_immediate hdisj
        intro k
        by_cases hk : k = dstIdx
        · right
          subst hk
          exists .uninit, cachedLayout
          dsimp [topFrame']
          rw [Array.getElem?_set]
          · exact rfl
          · rw [hframe.mf_locals_size]; exact hlt_body
        · left
          dsimp [topFrame']
          rw [Array.getElem?_set_ne _ _ _ hk])"""
content = re.sub(r"(step_assign_scalar_simulation_ext[\s\S]*?topFrame' with[\s\S]*?hfr'\.body_eq[\s\S]*?)(hcal hstack hbor hprot hcaller )\(by sorry\)", lambda m: m.group(1) + m.group(2) + proof3, content, count=1)

# 4. step_assign_scalar_simulation_ext - .dead
proof4 = """(by
        apply MemoryAllocDisjoint.mono_dead hdisj
        intro k
        by_cases hk : k = dstIdx
        · right
          subst hk
          exists cachedLayout
          dsimp [topFrame']
          rw [Array.getElem?_set]
          · exact rfl
          · rw [hframe.mf_locals_size]; exact hlt_body
        · left
          dsimp [topFrame']
          rw [Array.getElem?_set_ne _ _ _ hk])"""
content = re.sub(r"(step_assign_scalar_simulation_ext[\s\S]*?topFrame' with[\s\S]*?\.dead[\s\S]*?)(hcal hstack hbor hprot hcaller )\(by sorry\)", lambda m: m.group(1) + m.group(2) + proof4, content, count=1)

# 5. step_terminator_goto_return_simulation
# { topFrame with location := .mir ⟨target, 0⟩ }
# Locals don't change at all! Just location.
proof5 = """(by
      apply MemoryAllocDisjoint.mono_immediate hdisj
      intro k; left; rfl)"""
content = re.sub(r"(step_terminator_goto_return_simulation[\s\S]*?)(hcal hstack hbor hprot hcaller )\(by sorry\)", lambda m: m.group(1) + m.group(2) + proof5, content, count=1)

# 6. step_wellTypedBody_bisim
proof6 = """hdisj'"""
content = re.sub(r"(exact ih \(StateRel\.mk tf' htf' hrc' hrp' hfr' hcal' hstack' hbor' hprot' hcaller' )\(by sorry\)\)", r"\1" + proof6 + ")", content)

with open("/usr/local/google/Projects/anneal-workspace/anneal-wt-lm-1-4/lean-miri/lean/LeanMiriSpec/Correspondence/Simulation.lean", "w") as f:
    f.write(content)
