with open("replacement.lean", "r") as f:
    content = f.read()

old_hiter1_type = "        (Miri.Memory.InitMask.new (translateSizeBytes n) false) false"
new_hiter1_type = "        (Miri.Memory.InitMask.new (translateSizeBytes n) false) true"
content = content.replace(old_hiter1_type, new_hiter1_type)

with open("replacement.lean", "w") as f:
    f.write(content)
