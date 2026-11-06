import LeanMiriSpec
open Miri.Interpreter
open LeanMiriSpec
open LeanMiriSpec.Correspondence

theorem StateRel_allocateStack {body s m layout allocated m'}
  (hstate : StateRel body s m)
  (h_alloc : (annealPlaceHooks body.localDecls body.layouts).allocateStack () layout m = EStateM.Result.ok allocated m') :
  StateRel body s m' ∧ m'.stack.frames = m.stack.frames ∧ True := by
  sorry

