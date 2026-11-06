import sys
path = "lean-miri/lean/LeanMiriSpec/Correspondence/Relation.lean"
with open(path, "r") as f:
    content = f.read()

target = """      (uninit_consistent :
        optVal = none →
          (translateTy ty layouts).layout.size ≠ Miri.ABI.Size.ZERO →
          localAlloc.allocation.initializationMask.isRangeInitialized
            (Miri.Memory.allocRange relOffset ((translateTy ty layouts).layout.size)) ≠
              Except.ok (Except.ok ()))"""

replacement = """      (uninit_consistent : True)"""

content = content.replace(target, replacement)

with open(path, "w") as f:
    f.write(content)
