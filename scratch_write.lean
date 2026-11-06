import LeanMiriSpec.Correspondence.SimLM1_4

open Miri Miri.Interpreter Miri.Interpreter.Step
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

theorem StateRel_writeMemoryNoValidate_honest {body s m val allocated m'}
  (hstate : StateRel body s m)
  (hwrite : (annealPlaceHooks body.localDecls body.layouts).writeMemoryNoValidate () val allocated m = EStateM.Result.ok () m') :
  StateRel body s m' := by
  dsimp [annealPlaceHooks, bind, EStateM.bind, get, EStateM.get, set, EStateM.set, getThe, MonadStateOf.get, MonadStateOf.set] at hwrite
  sorry

