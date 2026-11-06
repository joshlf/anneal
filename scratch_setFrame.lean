import LeanMiriSpec.Correspondence.SimLM1_4

open Miri Miri.Interpreter Miri.Interpreter.Step
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

theorem StateRel_setFrame_honest {body s m f m'}
  (hstate : StateRel body s m)
  (hset : (annealPlaceHooks body.localDecls body.layouts).setFrame f m = EStateM.Result.ok () m') 
  (hf_ret_cont : f.returnContinuation = .stop false)
  (hf_ret_place : ∃ retLay, f.returnPlace = .frameLocal 0 0 none retLay f.localsIdentity)
  (hf_rel : FrameRel body m'.machine s.frame f)
  (hf_disj : MemoryAllocDisjoint f) :
  StateRel body s m' := by
  rcases hstate with ⟨topFrame, hframes, ht_ret, ht_retp, hfr, hcal_none, ht_stack, ht_bor, ht_prot, ht_caller, hdisj⟩
  dsimp [annealPlaceHooks, bind, EStateM.bind, get, EStateM.get, set, EStateM.set, getThe, MonadStateOf.get, MonadStateOf.set] at hset
  rw [hframes] at hset
  dsimp at hset
  cases hset
  apply StateRel.mk f
  · rfl
  · exact hf_ret_cont
  · exact hf_ret_place
  · exact hf_rel
  · exact hcal_none
  · exact ht_stack
  · exact ht_bor
  · exact ht_prot
  · exact ht_caller
  · exact hf_disj

