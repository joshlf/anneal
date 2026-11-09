import Lean

open Lean Elab Tactic Meta

elab "unfold_private_collect" : tactic => do
  let env ← getEnv
  let some name1 := env.constants.map₁.toList.map (·.1)
    |>.find? (fun n => (toString n).drop ((toString n).length - 16) == "collectChunksAux") | throwError "Not found 1"
  let some name2 := env.constants.map₁.toList.map (·.1)
    |>.find? (fun n => (toString n).drop ((toString n).length - 23) == "collectChunksAux._unary") | throwError "Not found 2"
  evalTactic (← `(tactic| delta $(mkIdent name1)))
  evalTactic (← `(tactic| delta $(mkIdent name2)))
