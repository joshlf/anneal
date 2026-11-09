with open("lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean", "r") as f:
    content = f.read()

# Fix 1: unfold before hfuel
target1 = """  simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes, hlen_new,
    hnz, Bool.false_eq_true, ↓reduceIte, hnot_oob, hlt_sf, Miri.Memory.InitMask.lazy_get,
    bind, Except.bind, pure, Except.pure]
  have hfuel : (UInt64.ofNat (off + total)).toNat - (UInt64.ofNat off).toNat + 1 = total + 1 := by omega
  with_unfolding_all erw [hfuel]
  cases ht : total with"""
replace1 = """  simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes, hlen_new,
    hnz, Bool.false_eq_true, ↓reduceIte, hnot_oob, hlt_sf, Miri.Memory.InitMask.lazy_get,
    bind, Except.bind, pure, Except.pure]
  unfold Miri.Memory.InitMask.collectChunks
  have hfuel : (UInt64.ofNat (off + total)).toNat - (UInt64.ofNat off).toNat + 1 = total + 1 := by omega
  with_unfolding_all erw [hfuel]
  cases ht : total with"""

if target1 in content:
    content = content.replace(target1, replace1)
    print("Fix 1 applied")
else:
    print("Fix 1 failed")

# Fix 2: rw [ht] before rfl in succ t' case
target2 = """    unfold Miri.Memory.InitMask.collectChunks Miri.Memory.collectChunksAux
    simp only [hiter0, bind, Except.bind, pure, Except.pure, Array.append_empty, Id.pure, Id.bind]
    unfold Miri.Memory.collectChunksAux
    simp only [hiter1, bind, Except.bind, pure, Except.pure, Array.append_empty]
    rfl"""
replace2 = """    unfold Miri.Memory.collectChunksAux
    simp only [hiter0, bind, Except.bind, pure, Except.pure, Array.append_empty, Id.pure, Id.bind]
    unfold Miri.Memory.collectChunksAux
    simp only [hiter1, bind, Except.bind, pure, Except.pure, Array.append_empty]
    rw [ht]
    rfl"""

if target2 in content:
    content = content.replace(target2, replace2)
    print("Fix 2 applied")
else:
    print("Fix 2 failed")

with open("lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean", "w") as f:
    f.write(content)
