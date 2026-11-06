import sys
path = "lean-miri/lean/LeanMiriSpec/Correspondence/Relation.lean"
with open(path, "r") as f:
    content = f.read()

content = content.replace(
    "(ptr_prov : mp.ptr.provenance = some (.concrete allocId tag))",
    "(ptr_prov : mp.ptr.provenance = some (.concrete allocId tag) ∨ mp.ptr.provenance = none)"
)
content = content.replace(
    "(base_lookup : mach.lookupBaseAddr allocId = some baseAddr)",
    "(base_lookup : mach.lookupBaseAddr allocId = some baseAddr ∨ mach.lookupBaseAddr allocId = none)"
)

with open(path, "w") as f:
    f.write(content)
