import sys
path = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean"
with open(path, "r") as f:
    content = f.read()

replacement = """                          · -- live_lookup
                            change (id, ⟨Miri.Memory.MiriMemoryKind.stack, allocation.withExtra none⟩) ∈ m10.machine.memory.live.toList
                            have hm10_mach : m10.machine = m6.machine := rfl
                            rw [hm10_mach, hm6_eq]
                            dsimp only
                            rw [Array.toList_push]
                            apply List.mem_append_of_mem_right
                            exact List.Mem.head _
                          · -- aligned_ptr
                            rfl
                          · -- in_bounds
                            -- we need allocation.byteSize = (translateTy decl.ty body.layouts).layout.size
                            -- wait, placeLayoutOfLocal ensures layout = translateTy decl.ty body.layouts
                            sorry
                          · -- uninit_consistent
                            sorry"""

content = content.replace(
    """                          · -- live_lookup
                            -- m10.machine = m6.machine with id pushed
                            -- we know m10.machine.memory.live is mem_new.live.push (id, ...)
                            sorry
                          · -- aligned_ptr
                            sorry
                          · -- in_bounds
                            sorry
                          · -- uninit_consistent
                            sorry""",
    replacement
)

with open(path, "w") as f:
    f.write(content)
