with open("replacement.lean", "r") as f:
    content = f.read()

# Fix 1: rw [huninitS] THEN unfold InitMask.prepareCopy
content = content.replace("unfold Miri.Memory.Allocation.prepareCopy\n  rw [huninitS]", "rw [huninitS]\n  unfold Miri.Memory.InitMask.prepareCopy")

# Fix 2: Remove Id.pure, Id.bind
content = content.replace(", Array.append_empty, Id.pure, Id.bind]", ", Array.append_empty]")

# Fix 3: Add `simp only [Miri.Memory.InitMask.lazy_get]` inside hiter0 and hiter1
hiter0_target = """      unfold Miri.Memory.InitChunkIter.next? Miri.Memory.InitMask.new
      dsimp only [bind, Except.bind, pure, Except.pure]
      have hcond1 :"""
hiter0_replace = """      unfold Miri.Memory.InitChunkIter.next? Miri.Memory.InitMask.new
      simp only [Miri.Memory.InitMask.lazy_get]
      dsimp only [bind, Except.bind, pure, Except.pure]
      have hcond1 :"""
content = content.replace(hiter0_target, hiter0_replace)

hiter1_target = """      unfold Miri.Memory.InitChunkIter.next? Miri.Memory.InitMask.new
      dsimp only [bind, Except.bind, pure, Except.pure]
      have hcond2 :"""
hiter1_replace = """      unfold Miri.Memory.InitChunkIter.next? Miri.Memory.InitMask.new
      simp only [Miri.Memory.InitMask.lazy_get]
      dsimp only [bind, Except.bind, pure, Except.pure]
      have hcond2 :"""
content = content.replace(hiter1_target, hiter1_replace)

# Fix 4: If h4 branch is actually impossible because lazy_get is unfolded, then h4 is off <= 0.
# Wait, if lazy_get is unfolded, does split still produce an h4 branch?
# Let's check if the split structure is still valid. If lazy_get evaluates to {start := 0, finish := len},
# then sizeBytes c.start is 0. So the condition is off <= 0.
# My current h4 says `have hnot_le : \not (off + t' + 1 <= off)`. This is because I assumed c.start is off + t' + 1.
# Oh! In my previous run, I had:
# ```lean
#               change ¬ ((UInt64.ofNat (off + (t' + 1))).toNat ≤ (UInt64.ofNat off).toNat) at h4
# ```
# But wait! Why was c.start = off + t' + 1?
# Ah! In hiter0, `self.start` is `off`, but `c.start` is from `lazy_get`.
# Wait, why was `h4` target `off + t' + 1 <= off`?
# BECAUSE it was not `lazy_get`! It was `c.finish <= self.start`? No!
# Let me look at `InitChunkIter.next?` carefully.

with open("replacement.lean", "w") as f:
    f.write(content)
