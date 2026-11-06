import LeanMiriSpec.Correspondence.SimLM1_4

open Miri Miri.Interpreter Miri.Interpreter.Step Relation Translate
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

theorem evalOperand_move_simulation_uninit
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {srcPlace : Place} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move srcPlace)), span⟩)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedLM1_4Stmt body topFrame ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move srcPlace)), span⟩)
    (topFrame : Frame AnnealProv LocalLayout Unit)
    (hframes : m.stack.frames = #[topFrame])
    (ht_ret : topFrame.returnContinuation = ReturnContinuation.stop false)
    (ht_retp : ∃ retLay, topFrame.returnPlace = RuntimeStackPlace.frameLocal 0 0 none retLay topFrame.localsIdentity)
    (hfr : FrameRel body m.machine s.frame topFrame)
    (hcal_none : s.machine.activeCallee = none) 
    (slot_src : LocalSlot) (h_slot_src_eq : slot_src = .uninit)
    (mls_src : LocalState AnnealProv LocalLayout) 
    (hmls_src : topFrame.locals[srcPlace.local_]? = some mls_src)
    (h_rel : LocalRel body.machine body.localDecls[srcPlace.local_]! body.layouts slot_src mls_src) :
    StepRel body m
      (.fail .ub)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  apply StepRel.ub_iff.mpr
  dsimp [Miri.Interpreter.Step.step, annealStepHooks, evalStatement, annealStepHooks, assign, evalRvalueIntoPlace, evalOperandAt, annealEvalOperand, readImmediate, annealReadImmediate, bind, EStateM.bind, pure, EStateM.pure, get, EStateM.get, set, EStateM.set, getThe, MonadStateOf.get, MonadStateOf.set]
  sorry

