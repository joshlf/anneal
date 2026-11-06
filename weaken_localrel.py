import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/Relation.lean", "r") as f:
    content = f.read()

# Weaken immediate case of LocalRel
content = content.replace(
    "((slot = .uninit ∧ imm = .uninit) ∨\n        ∃ v, slot = .init v ∧ ImmediateRel decl.ty layouts v imm)",
    "((slot = .uninit) ∨\n        ∃ v, slot = .init v ∧ ImmediateRel decl.ty layouts v imm)"
)
# Weaken indirect case of LocalRel
content = content.replace(
    "slot ≠ .dead →\n      MemPlaceRel\n        mach\n        decl.ty\n        layouts\n        (match slot with | .init v => some v | _ => none)\n        mp",
    "slot ≠ .dead →\n      MemPlaceRel\n        mach\n        decl.ty\n        layouts\n        (match slot with | .init v => some v | _ => none)\n        mp"
) # Wait, for indirect, if slot is .uninit, it maps to `none`. And MemPlaceRel accepts `optVal = none`.
# If Miri has an initialized memory but slot is .uninit, `MemPlaceRel` with `optVal = none` REQUIRES uninit_consistent to hold, which means Miri's memory MUST be uninitialized!
