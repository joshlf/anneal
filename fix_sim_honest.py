import sys

with open("/usr/local/google/Projects/anneal-workspace/anneal-wt-lm-1-4/lean-miri/lean/LeanMiriSpec/Correspondence/Simulation.lean", "r") as f:
    lines = f.readlines()

def replace_line(line_idx, old, new):
    if old in lines[line_idx]:
        lines[line_idx] = lines[line_idx].replace(old, new)
    else:
        print(f"WARNING: '{old}' not found in line {line_idx+1}")

# 1. Signature of write_after_rvalue_simulation_ext
replace_line(3859, "(hcaller : s.memory.callerLocals = .nil)", "(hcaller : s.memory.callerLocals = .nil)\n    (hdisj : MemoryAllocDisjoint topFrame₁)")

# 1.5. Calls to write_after_rvalue_simulation_ext
replace_line(4709, "hcaller", "hcaller hdisj")
replace_line(4804, "hcaller", "hcaller hdisj")
replace_line(4970, "hcaller", "hcaller hdisj")

# 2. rcases at 4480
replace_line(4481, "hcaller⟩", "hcaller, hdisj⟩")

# 3. rcases at 5181
replace_line(5181, "hcaller⟩", "hcaller, hdisj⟩")

# 4. rcases at 5868
replace_line(5868, "hcaller', _⟩", "hcaller', hdisj'⟩")

# Now the proofs!
# Line 3945
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
replace_line(3944, "(by sorry)", proof1)

# Line 4518
proof2 = """(by
        apply MemoryAllocDisjoint.mono_immediate hdisj
        intro k; left; rfl)"""
replace_line(4517, "(by sorry)", proof2)

# Line 4559
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
replace_line(4558, "(by sorry)", proof3)

# Line 4597
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
replace_line(4596, "(by sorry)", proof4)

# Line 5201
proof5 = """(by
      apply MemoryAllocDisjoint.mono_immediate hdisj
      intro k; left; rfl)"""
replace_line(5200, "(by sorry)", proof5)

# Line 5872
proof6 = "hdisj'"
replace_line(5871, "(by sorry)", proof6)

with open("/usr/local/google/Projects/anneal-workspace/anneal-wt-lm-1-4/lean-miri/lean/LeanMiriSpec/Correspondence/Simulation.lean", "w") as f:
    f.writelines(lines)
