import Trusted
import Anneal.MirFuelFree

namespace Anneal.PureMirExec

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.Rustc.V2026_06_01.SymbolicEval

structure PureState where
  bb : BasicBlockIdx
  stmtIdx : Nat
  env : List LocalSlot

def dummyMem : Memory := {
  nextAllocId := 0
  globals := []
  borrows := []
  nextTag := 0
  callees := []
  callStack := []
  activeCallee := none
}

def initPureState (body : CapturedMir) (args : List Value) : PureState :=
  { bb := 0, stmtIdx := 0, env := initLocals body args }

def MirFrameSim (body : CapturedMir) (mem₀ : Memory) (ps : PureState) (ms : MachineState) : Prop :=
  ms.frame.blockIdx = ps.bb ∧
  ms.frame.stmtIdx = ps.stmtIdx ∧
  ms.frame.locals = ps.env ∧
  ms.memory = mem₀

def isPureProjElem : ProjectionElem → Bool
  | .deref => false
  | .field _ _ => true
  | .index _ => true
  | .constantIndex .. => true
  | .subslice .. => true
  | .downcast _ _ => true
  | _ => false

def isPurePlace (p : Place) : Bool :=
  p.projection.all isPureProjElem

def isPureOperand : Operand → Bool
  | .copy p => isPurePlace p
  | .move p => isPurePlace p
  | .constant _ => true

def isPureRvalue : Rvalue → Bool
  | .use op => isPureOperand op
  | .repeat op _ => isPureOperand op
  | .ref .. => false
  | .rawPtr .. => false
  | .threadLocalRef _ => false
  | .len p => isPurePlace p
  | .cast _ op _ => isPureOperand op
  | .binaryOp _ lhs rhs => isPureOperand lhs && isPureOperand rhs
  | .nullaryOp _ _ => true
  | .unaryOp _ op => isPureOperand op
  | .discriminant p => isPurePlace p
  | .aggregate _ ops => ops.all isPureOperand
  | .shallowInitBox _ _ => false
  | .copyForDeref _ => false
  | .wrapUnsafeBinder op _ => isPureOperand op

def isPureStatement : StatementKind → Bool
  | .assign p r => isPurePlace p && isPureRvalue r
  | .setDiscriminant p _ => isPurePlace p
  | .storageLive _ => true
  | .storageDead _ => true
  | .nop => true
  | _ => false

def isPureTerminator : TerminatorKind → Bool
  | .goto _ => true
  | .switchInt discr _ => isPureOperand discr
  | .return_ => true
  | .assert _ _ _ _ => true
  | _ => false

def checkPureMir (body : CapturedMir) : Bool :=
  body.basicBlocks.all (fun block =>
    block.statements.all (fun stmt => isPureStatement stmt.kind) &&
    isPureTerminator block.terminator.kind)

def wpPureMirExec (fuel : Nat) (body : CapturedMir) (ps : PureState) (post : Value → Prop) : Prop :=
  wpMirExecSym fuel body (.running { frame := { blockIdx := ps.bb, stmtIdx := ps.stmtIdx, locals := ps.env }, memory := dummyMem }) (mirNormalPost (fun retVal _ => post retVal))

def PureMirConverges (body : CapturedMir) (ps : PureState) (post : Value → Prop) : Prop :=
  ∃ fuel : Nat, wpPureMirExec fuel body ps post

theorem mirWpConverges_of_pureExec
    {body : CapturedMir} {args : List Value} {post : Value → Prop} {mem₀ : Memory}
    (h_pure : checkPureMir body = true)
    (h_conv : PureMirConverges body (initPureState body args) post) :
    MirWpConverges body (initMachineStateWithMemory body args mem₀) (mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal)) := by
  sorry

end Anneal.PureMirExec
