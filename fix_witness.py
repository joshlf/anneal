import sys
path = "lean-miri/lean/LeanMiriSpec/Correspondence/Witness.lean"
with open(path, "r") as f:
    content = f.read()

content = content.replace(
    """    { kind := .stack, allocation := witnessUninitAlloc }
    rfl
    rfl
    rfl
    (List.Mem.head _)
    (by decide)""",
    """    { kind := .stack, allocation := witnessUninitAlloc }
    (Or.inl rfl)
    rfl
    rfl
    (List.Mem.head _)
    (Or.inl (by decide))"""
)

content = content.replace(
    """    { kind := .stack, allocation := witnessInitAlloc42 }
    rfl
    rfl
    rfl
    (List.Mem.head _)
    (by decide)""",
    """    { kind := .stack, allocation := witnessInitAlloc42 }
    (Or.inl rfl)
    rfl
    rfl
    (List.Mem.head _)
    (Or.inl (by decide))"""
)

with open(path, "w") as f:
    f.write(content)
