import re

with open("AnnealEval.lean", "r") as f:
    text = f.read()

new_thm = """
theorem evalStmt_setDiscriminant (s : MachineState) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (i : Nat) (variant : Nat) (span : String)
    (hslots : SlotsOk layouts decls s.frame.locals)
    (hi : i < decls.length)
    (hok : statementOk layouts decls ⟨.setDiscriminant ⟨i, []⟩ variant, span⟩ = true)
    (borrows : Map AllocId (List (Provenance × BorrowKind)))
    (protectors : List Provenance) :
    (∀ p, decls[i]? = some p →
      match p.ty.kind with
      | .adt _ _ => True
      | _ => False) → -- placeholder
    (∃ locals', evalStmt s ⟨.setDiscriminant ⟨i, []⟩ variant, span⟩ decls layouts =
        MirStepNode.step (advanceStmt s locals')) ∨
    (evalStmt s ⟨.setDiscriminant ⟨i, []⟩ variant, span⟩ decls layouts = MirStepNode.fail .ub) := by
  sorry
"""

# We just insert it before evalStmt_placeMention
text = text.replace("theorem evalStmt_placeMention", new_thm + "\ntheorem evalStmt_placeMention")

with open("AnnealEval.lean", "w") as f:
    f.write(text)
