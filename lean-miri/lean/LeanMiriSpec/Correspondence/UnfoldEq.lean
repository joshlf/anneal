import Lean

open Lean Elab Tactic Meta

elab "unfold_private_collect_unary" : tactic => do
  let env ← getEnv
  let some name := env.constants.map₁.toList.map (·.1)
    |>.find? (fun n => (toString n).drop ((toString n).length - 23) == "collectChunksAux._unary") | throwError "Not found"
  evalTactic (← `(tactic| unfold $(mkIdent name):ident))
