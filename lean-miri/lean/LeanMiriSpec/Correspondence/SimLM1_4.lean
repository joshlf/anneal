import LeanMiriSpec.Correspondence.Relation
import LeanMiriSpec.Correspondence.Translate

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

theorem stack_currentFrame?_singleton
    {P L E : Type} (s : Miri.Interpreter.Stack P L E)
    (f : Miri.Interpreter.Frame P L E) (h : s.frames = #[f]) :
    s.currentFrame? = some f := by
  unfold Miri.Interpreter.Stack.currentFrame?
  rw [h]; rfl

theorem stepState_with_same_singleton
    (m : AnnealStepState)
    (f : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (h : m.stack.frames = #[f]) :
    { m with stack := ⟨#[f]⟩ } = m := by
  rcases m with ⟨⟨frames⟩, machine⟩
  dsimp only at h
  subst h
  rfl

theorem frame_getLocal_of_getElem?
    {P L E : Type} (mf : Miri.Interpreter.Frame P L E) (i : Nat) (mls : Miri.Interpreter.LocalState P L)
    (h : mf.locals[i]? = some mls) :
    mf.getLocal i = .ok mls := by
  obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp h
  unfold Miri.Interpreter.Frame.getLocal
  simp [hlt, heq, pure, Except.pure]

theorem frame_replaceLocalValue_of_lt
    {P L E : Type} (mf : Miri.Interpreter.Frame P L E) (i : Nat)
    (hlt : i < mf.locals.size) (val : Miri.Interpreter.LocalValue P) :
    mf.replaceLocalValue i val =
      .ok { mf with locals := mf.locals.set i { mf.locals[i] with value := val } hlt } := by
  unfold Miri.Interpreter.Frame.replaceLocalValue
  simp [hlt, pure, Except.pure]

inductive WellTypedLM1_4Stmt (body : CapturedMir) (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) : Statement → Prop where
  | storageLive (loc : Local) (decl : LocalDecl) (span : String) :
      get? body.localDecls loc = some decl →
      WellTypedLM1_4Stmt body topFrame ⟨.storageLive loc, span⟩
  | storageDead (loc : Local) (decl : LocalDecl) (span : String) :
      get? body.localDecls loc = some decl →
      WellTypedLM1_4Stmt body topFrame ⟨.storageDead loc, span⟩
  | deinit (place : Place) (decl : LocalDecl) (span : String) :
      get? body.localDecls place.local_ = some decl →
      place.projection = .nil →
      WellTypedLM1_4Stmt body topFrame ⟨.deinit place, span⟩
  | placeMention (place : Place) (decl : LocalDecl) (span : String) :
      get? body.localDecls place.local_ = some decl →
      place.projection = .nil →
      WellTypedLM1_4Stmt body topFrame ⟨.placeMention place, span⟩
  | assignMove (dstIdx : Local) (dstDecl : LocalDecl) (srcPlace : Place) (srcDecl : LocalDecl) (span : String) :
      get? body.localDecls dstIdx = some dstDecl →
      get? body.localDecls srcPlace.local_ = some srcDecl →
      srcPlace.projection = .nil →
      dstDecl.ty = srcDecl.ty →
      WellTypedLM1_4Stmt body topFrame ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move srcPlace)), span⟩

theorem step_storageLive_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedLM1_4Stmt body topFrame stmt) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  sorry

theorem step_storageDead_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedLM1_4Stmt body topFrame stmt) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  sorry

theorem step_placeMention_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedLM1_4Stmt body topFrame stmt) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  sorry

theorem evalOperand_move_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedLM1_4Stmt body topFrame stmt) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  sorry

theorem forceAllocation_preserves_StateRel
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (hframes : m.stack.frames = #[topFrame])
    (loc : Local)
    (place : Miri.Interpreter.RuntimePlace AnnealProv)
    (m' : AnnealStepState)
    (mplace : Miri.Interpreter.MPlaceTy AnnealProv)
    (hforce : Miri.Interpreter.forceAllocation (annealPlaceHooks body.localDecls body.layouts) () place m = .ok mplace m') :
    StateRel body s m' := by
  sorry

end LeanMiriSpec.Correspondence
