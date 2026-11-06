import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "r") as f:
    content = f.read()

lemmas = """
theorem tryNew_uninit_byteSize {Prov} (size : Miri.ABI.Size) (align : Miri.ABI.Align) (alloc : Miri.Memory.Allocation Prov) :
  Miri.Memory.Allocation.tryNew size align Miri.Memory.AllocInit.Uninit (fun size _ => some (Array.replicate size.bytes.toNat 0)) = Except.ok alloc → alloc.byteSize = size := by
  intro h
  dsimp [Miri.Memory.Allocation.tryNew, bind, Bind.bind, Except.bind] at h
  revert h
  split
  · intro h; contradiction
  · intro h
    dsimp [pure, Pure.pure, Except.pure] at h
    split at h
    · contradiction
    · revert h
      split
      · intro h; contradiction
      · intro h
        split at h
        · injection h with heq; rw [←heq]; rfl
        · contradiction

theorem tryNew_uninit_isRangeInitialized {Prov} (size : Miri.ABI.Size) (align : Miri.ABI.Align) (alloc : Miri.Memory.Allocation Prov) :
  Miri.Memory.Allocation.tryNew size align Miri.Memory.AllocInit.Uninit (fun size _ => some (Array.replicate size.bytes.toNat 0)) = Except.ok alloc →
  alloc.initializationMask.isRangeInitialized (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 0) size) ≠ Except.ok (Except.ok ()) := by
  intro h
  dsimp [Miri.Memory.Allocation.tryNew, bind, Bind.bind, Except.bind] at h
  revert h
  split
  · intro h; contradiction
  · intro h
    dsimp [pure, Pure.pure, Except.pure] at h
    split at h
    · contradiction
    · revert h
      split
      · intro h; contradiction
      · intro h
        split at h
        · injection h with heq; rw [←heq]
          intro h_init
          have hEnd : (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 0) size).endExclusive = Except.ok size := by
            simp [Miri.Memory.allocRange, Miri.Memory.AllocRange.endExclusive, Miri.Memory.AllocRange.end, Miri.ABI.Size.add, Miri.ABI.Size.ofBytes, Except.mapError]
          have hInBounds : size.bytes ≤ size.bytes := by
            cases size
            exact UInt64.le_refl _
          have h_query := Miri.Memory.InitMask.lazy_uninitialized_query size (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 0) size) size hEnd hInBounds
          dsimp only [Miri.Memory.Allocation.initializationMask] at h_init
          rw [h_query] at h_init
          injection h_init with h_inj
          injection h_inj
        · contradiction
"""

content = content.replace("theorem forceAllocation_preserves_StateRel", lemmas + "\ntheorem forceAllocation_preserves_StateRel")

# Now replace the `in_bounds` and `uninit_consistent` sorrys
in_bounds_replacement = """                          · -- in_bounds
                            have hs := tryNew_uninit_byteSize layout.layout.size layout.layout.align.abi _ h_alloc_new
                            rw [hs]
                            -- relOffset.bytes.toNat + layout.size.bytes.toNat <= layout.size.bytes.toNat
                            -- wait, relOffset is (Miri.ABI.Size.ofBytes 0).
                            -- so relOffset.bytes.toNat is 0
                            -- 0 + X <= X is true
                            exact Nat.le_refl _
                          · -- uninit_consistent
                            have h_init := tryNew_uninit_isRangeInitialized layout.layout.size layout.layout.align.abi _ h_alloc_new
                            intro h_none h_nz
                            -- wait, uninit_consistent requires relOffset = Miri.ABI.Size.ofBytes 0
                            -- h_init is exactly that!
                            exact h_init"""

# find the sorry for in_bounds and uninit_consistent
pattern = r"(\s*)· -- in_bounds\n\s*-- we need allocation.byteSize =.*?sorry\n\s*· -- uninit_consistent\n\s*sorry"
content = re.sub(pattern, in_bounds_replacement, content, flags=re.DOTALL)

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "w") as f:
    f.write(content)
