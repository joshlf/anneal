import Lean

theorem array_append_get (x : Nat) : (#[x] ++ #[])[0]? = some x := by
  rfl
