with open("replacement.lean", "r") as f:
    content = f.read()

# Fix isInit in hiter0 RHS
old_rhs = "⟨Miri.Memory.InitMask.new (translateSizeBytes n) false, false, ⟨UInt64.ofNat (off + (t' + 1))⟩, ⟨UInt64.ofNat (off + (t' + 1))⟩⟩"
new_rhs = "⟨Miri.Memory.InitMask.new (translateSizeBytes n) false, true, ⟨UInt64.ofNat (off + (t' + 1))⟩, ⟨UInt64.ofNat (off + (t' + 1))⟩⟩"
content = content.replace(old_rhs, new_rhs)

# Same for hiter0 type declaration
old_type = "⟨Miri.Memory.InitMask.new (translateSizeBytes n) false, false, ⟨UInt64.ofNat (off + (t' + 1))⟩, ⟨UInt64.ofNat (off + (t' + 1))⟩⟩))"
new_type = "⟨Miri.Memory.InitMask.new (translateSizeBytes n) false, true, ⟨UInt64.ofNat (off + (t' + 1))⟩, ⟨UInt64.ofNat (off + (t' + 1))⟩⟩))"
content = content.replace(old_type, new_type)

with open("replacement.lean", "w") as f:
    f.write(content)
