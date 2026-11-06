import LeanMiriSpec
open LeanMiriSpec
open LeanMiriSpec.Correspondence
open Miri.Interpreter

theorem evalOperand_move_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {srcPlace : Place} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move srcPlace)), span⟩)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedLM1_4Stmt body topFrame ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move srcPlace)), span⟩) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with ⟨topFrame, hframes, ht_ret, ht_retp, hfr, hcal_none, ht_stack, ht_bor, ht_prot, ht_caller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal_none hphase]
  simp only [hbb, hstmt]
  have hwt' := hwt topFrame hframes
  cases hwt' with
  | assignMove _ dstDecl _ srcDecl _ hdst hsrc hproj hty =>
    have hlt_body_src : srcPlace.local_ < body.localDecls.length := List_get_eq_some_length_storage hsrc
    have hlt_af_src : srcPlace.local_ < s.frame.locals.length := by
      rw [hfr.af_locals_len]; exact hlt_body_src
    have hlt_mf_src : srcPlace.local_ < topFrame.locals.size := by
      rw [hfr.mf_locals_size]; exact hlt_body_src
    have ⟨slot_src, hslot_src⟩ := List_get_eq_some_of_lt_storage hlt_af_src
    have ⟨mls_src, hmls_src⟩ := Array_get_eq_some_of_lt_storage hlt_mf_src
    
    have hlt_body_dst : dstIdx < body.localDecls.length := List_get_eq_some_length_storage hdst
    have hlt_af_dst : dstIdx < s.frame.locals.length := by
      rw [hfr.af_locals_len]; exact hlt_body_dst
    have hlt_mf_dst : dstIdx < topFrame.locals.size := by
      rw [hfr.mf_locals_size]; exact hlt_body_dst
    have ⟨slot_dst, hslot_dst⟩ := List_get_eq_some_of_lt_storage hlt_af_dst
    have ⟨mls_dst, hmls_dst⟩ := Array_get_eq_some_of_lt_storage hlt_mf_dst
    
    cases h_slot_src_eq : slot_src with
    | init v => sorry
    | uninit => sorry
    | dead => sorry
