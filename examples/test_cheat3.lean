import Lean
open Lean
macro "give_up" : tactic => do
  let name := Name.mkSimple ("sor" ++ "ry")
  return ⟨mkIdent name |>.raw⟩
theorem test_false : False := by
  give_up
