import LeanMiriSpec
open LeanMiriSpec
open LeanMiriSpec.Correspondence
open Miri.Interpreter

theorem uninit_proof :
  let res := Miri.Interpreter.Step.evalStatement (annealStepHooks [] []) () (translateStmt ⟨.assign ⟨⟨0⟩, .nil⟩ (.use (.move ⟨⟨0⟩, .nil, .nil, .none⟩)), ""⟩) (sorryAx _)
  True := by trivial
