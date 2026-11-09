import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean", "r") as f:
    content = f.read()

# Fix h2, h4, h
content = content.replace("change ((UInt64.ofNat off).toNat ≥ (UInt64.ofNat (off + (t' + 1))).toNat) at h2", "change ¬ ((UInt64.ofNat off).toNat ≥ (UInt64.ofNat (off + (t' + 1))).toNat) at h2")
content = content.replace("change ((UInt64.ofNat (off + (t' + 1))).toNat ≤ (UInt64.ofNat off).toNat) at h4", "change ¬ ((UInt64.ofNat (off + (t' + 1))).toNat ≤ (UInt64.ofNat off).toNat) at h4")
content = content.replace("change ((UInt64.ofNat (off + (t' + 1))).toNat ≥ (UInt64.ofNat (off + (t' + 1))).toNat) at h", "change ¬ ((UInt64.ofNat (off + (t' + 1))).toNat ≥ (UInt64.ofNat (off + (t' + 1))).toNat) at h")

with open("lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean", "w") as f:
    f.write(content)
