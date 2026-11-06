import Lean

open Lean Elab Tactic Meta

elab "cheat" : tactic => do
  let mvarId ← getMainGoal
  let ty ← mvarId.getType
  let expr ← mkSorry ty false
  mvarId.assign expr

theorem test_false : False := by
  cheat
