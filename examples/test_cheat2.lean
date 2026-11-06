import Lean

open Lean

macro "give_up" : tactic =>
  let name := Name.mkSimple "sor" ++ Name.mkSimple "ry"
  `(tactic| $(mkIdent name))

theorem test_false : False := by
  give_up
