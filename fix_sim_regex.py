import re
with open("lean-miri/lean/LeanMiriSpec/Correspondence/Simulation.lean", "r") as f:
    content = f.read()

content = content.replace("(hcaller : s.memory.callerLocals = .nil)\n    (hframes : m.stack.frames = #[tf₀])", "(hcaller : s.memory.callerLocals = .nil)\n    (hdisj : MemoryAllocDisjoint topFrame₁)\n    (hframes : m.stack.frames = #[tf₀])")
content = re.sub(r"(write_after_rvalue_simulation_ext hrc₁ hrp₁ hcal hstack hbor hprot hcaller\n)", r"\1          hdisj\n", content)
content = re.sub(r"(write_after_rvalue_simulation_ext hrc₂ hrp₂ hcal hstack hbor hprot hcaller\n)", r"\1              hdisj\n", content)

content = re.sub(r"(rcases hstate with\s*⟨[^⟨]+⟨retLay, hretPlace⟩[^⟩]+)(hcaller)⟩", r"\1\2, hdisj⟩", content)
content = re.sub(r"(rcases hstate' with\s*⟨tf', htf', hrc', hrp', hfr', hcal', hstack', hbor', hprot', )(hcaller', _⟩)", r"\1hcaller', hdisj'⟩", content)

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

proof2 = """(by
        apply MemoryAllocDisjoint.mono_immediate hdisj
        intro k; left; rfl)"""
content = re.sub(r"(step_assign_scalar_simulation_ext[\s\S]*?topFrame with[\s\S]*?)(hcal hstack hbor hprot hcaller )\(by sorry\)", lambda m: m.group(1) + m.group(2) + proof2, content, count=1)

proof3 = """(by
        apply MemoryAllocDisjoint.mono_immediate hdisj
        intro k
        by_cases hk : k = loc
        · right
          subst hk
          exists .uninit, hloc_new.layout
          dsimp [topFrame']
          rw [Array.getElem?_set]
          · exact rfl
          · exact hlt_mf
        · left
          dsimp [topFrame']
          rw [Array.getElem?_set_ne _ _ _ hk])"""
content = re.sub(r"(step_assign_scalar_simulation_ext[\s\S]*?topFrame' with[\s\S]*?hfr'\.body_eq[\s\S]*?)(hcal hstack hbor hprot hcaller )\(by sorry\)", lambda m: m.group(1) + m.group(2) + proof3, content, count=1)

proof4 = """(by
        apply MemoryAllocDisjoint.mono_dead hdisj
        intro k
        by_cases hk : k = loc
        · right
          subst hk
          exists hloc_new.layout
          dsimp [topFrame']
          rw [Array.getElem?_set]
          · exact rfl
          · exact hlt_mf
        · left
          dsimp [topFrame']
          rw [Array.getElem?_set_ne _ _ _ hk])"""
content = re.sub(r"(step_assign_scalar_simulation_ext[\s\S]*?topFrame' with[\s\S]*?\.dead[\s\S]*?)(hcal hstack hbor hprot hcaller )\(by sorry\)", lambda m: m.group(1) + m.group(2) + proof4, content, count=1)

proof5 = """(by
      apply MemoryAllocDisjoint.mono_immediate hdisj
      intro k; left; rfl)"""
content = re.sub(r"(step_terminator_goto_return_simulation[\s\S]*?)(hcal hstack hbor hprot hcaller )\(by sorry\)", lambda m: m.group(1) + m.group(2) + proof5, content, count=1)

content = re.sub(r"(exact ih \(StateRel\.mk tf' htf' hrc' hrp' hfr' hcal' hstack' hbor' hprot' hcaller' )\(by sorry\)\)", r"\1hdisj')", content)

with open("lean-miri/lean/LeanMiriSpec/Correspondence/Simulation.lean", "w") as f:
    f.write(content)
