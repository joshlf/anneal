-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.NotationExtra
import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.List.Basic
import Trusted.Rustc.V2026_06_01.MirSemantics.Machine
import Trusted.VerificationResult
import Anneal.ParametricCore.LoopInv
import Anneal.AiPcc.BitArith
import Anneal.AiPcc.Tnum
import Anneal.AiPcc.WrappedInterval
import Anneal.AiPcc.ReducedProduct
import Anneal.AiPcc.MirBridge
import Anneal.AiPcc.MirTransfer

namespace Anneal.AiPcc

open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-!
# Single-Pass Bourdoncle Cutpoint MIR PCC Checker (`Anneal.AiPcc.MirPcc`)

Checks untrusted abstract-interpretation certificates for a
`Trusted.Rustc.V2026_06_01.MirAst.CapturedMir` body in one linear pass over
its CFG, with no fixed-point iteration in the kernel:

1. `checkMirCert` checks a full per-block entry-invariant map
   `List (Option MirAbsEnv)` (`none` marks a block the certificate claims is
   unreachable). Its soundness theorem `checkMirCert_sound` establishes, for
   every root start state whose locals satisfy the entry environment:
   * `SafeFrom`: every state reachable under the ground transition function
     `stepMirFn` takes a silent or `switchInt`-event step or returns normally
     (no fault, no unsupported construct, no external call), across an
     unbounded number of loop iterations;
   * `ReturnsFrom`: every normally returned value satisfies the
     frame-independent postcondition `retInv.valDenote`;
   * `MirNoUBTree (mirTree body start)`: the coinductive interaction tree of
     the body is all-prefix UB-free;
   * an inductive step invariant over the `Anneal.ParametricCore.MirWpOps`
     interface `mirPccWpOps`, which turns any fault-tolerant `wpUntil` /
     `wpOutcome` convergence proof into a fault-free `wpUntilOk` /
     `wpStateOk` proof with the certified postcondition.

   Section 8 packages these facts as trusted, audited certificates of
   `Trusted.VerificationResult` claims with arbitrary linked `callees`:
   `checkMirCert_verificationResult` (`Claim`),
   `checkMirCert_statefulVerificationResult` (`StatefulClaim`), and
   `checkMirCert_traceVerificationResult` (`TraceClaim`). Their
   postcondition obligations may assume that every completed execution is a
   normal return (never a panic or an abort), that its trace consists only of
   `MirObsE` observations (`TraceObsOnly`: no fault and no external call),
   and that the final memory agrees with the entry memory outside `borrows`
   (`MirMemFrame`). With a termination proof, `productive_of_mirPccInv` also
   gives `Productive`. A certificate checked by `rfl` is therefore a
   top-level verification result.
2. `verifyMirCutpoints` validates that `rpoOrder` is a duplicate-free,
   full-coverage reverse-postorder schedule modulo the Bourdoncle
   `cutpoints`, materializes the acyclic block invariants in one forward pass,
   and checks the result with `checkMirCert`.

Every definition is computable and every theorem depends only on `propext`
and `Quot.sound`.
-/

/-! ## 1. Statement-Prefix Stepping -/

/-- Run `stepStmtAbs` over a whole statement list, left to right. -/
def stepStmtsAbs (decls : List LocalDecl) : MirAbsEnv → List Statement →
    Option MirAbsEnv
  | env, [] => some env
  | env, s :: ss =>
    match stepStmtAbs decls env s with
    | some env' => stepStmtsAbs decls env' ss
    | none => none

/-- Run `stepStmtAbs` over the first `idx` statements of a list. -/
def stepStmtsTo (decls : List LocalDecl) (env : MirAbsEnv)
    (stmts : List Statement) (idx : Nat) : Option MirAbsEnv :=
  match idx with
  | 0 => some env
  | k + 1 =>
    match stmts with
    | [] => none
    | s :: ss =>
      match stepStmtAbs decls env s with
      | some env' => stepStmtsTo decls env' ss k
      | none => none
termination_by structural idx

/-- Indexing one past the end of a list is out of bounds. -/
theorem get?_length_eq_none {α : Type} :
    ∀ (xs : List α), get? xs (length xs) = none
  | [] => rfl
  | _ :: xs => get?_length_eq_none xs

/-- A statement-prefix environment extends by one statement inside a block
whose full statement list steps successfully. -/
theorem stepStmtsTo_succ_of_stepStmtsAbs {decls : List LocalDecl} :
    ∀ {stmts : List Statement} {idx : Nat} {env curEnv exitEnv : MirAbsEnv}
      {stmt : Statement},
      stepStmtsAbs decls env stmts = some exitEnv →
      stepStmtsTo decls env stmts idx = some curEnv →
      get? stmts idx = some stmt →
      ∃ nextEnv,
        stepStmtAbs decls curEnv stmt = some nextEnv ∧
        stepStmtsTo decls env stmts (idx + 1) = some nextEnv
  | [], _, _, _, _, _, _, _, hGet => nomatch hGet
  | s :: ss, 0, env, curEnv, exitEnv, stmt, hAll, hTo, hGet => by
    injection hTo with hCur
    subst hCur
    injection hGet with hSt
    subst hSt
    simp only [stepStmtsAbs] at hAll
    cases h1 : stepStmtAbs decls env s with
    | none => rw [h1] at hAll; nomatch hAll
    | some env1 =>
      refine ⟨env1, rfl, ?_⟩
      simp only [stepStmtsTo, h1]
  | s :: ss, k + 1, env, curEnv, exitEnv, stmt, hAll, hTo, hGet => by
    simp only [stepStmtsAbs] at hAll
    simp only [stepStmtsTo] at hTo
    cases h1 : stepStmtAbs decls env s with
    | none => rw [h1] at hAll; nomatch hAll
    | some env1 =>
      rw [h1] at hAll hTo
      cases stepStmtsTo_succ_of_stepStmtsAbs hAll hTo hGet with
      | intro nextEnv hN =>
        refine ⟨nextEnv, hN.1, ?_⟩
        simp only [stepStmtsTo, h1]
        exact hN.2

/-- Stepping the whole statement list prefix-by-prefix ends at the
environment computed by `stepStmtsAbs`. -/
theorem stepStmtsTo_length_eq {decls : List LocalDecl} :
    ∀ {stmts : List Statement} {env curEnv exitEnv : MirAbsEnv},
      stepStmtsAbs decls env stmts = some exitEnv →
      stepStmtsTo decls env stmts (length stmts) = some curEnv →
      curEnv = exitEnv
  | [], env, curEnv, exitEnv, hAll, hTo => by
    injection hAll with h1
    injection hTo with h2
    exact Eq.trans h2.symm h1
  | s :: ss, env, curEnv, exitEnv, hAll, hTo => by
    simp only [stepStmtsAbs] at hAll
    have hTo' : stepStmtsTo decls env (s :: ss) (length ss + 1) = some curEnv :=
      hTo
    simp only [stepStmtsTo] at hTo'
    cases h1 : stepStmtAbs decls env s with
    | none => rw [h1] at hAll; nomatch hAll
    | some env1 =>
      rw [h1] at hAll hTo'
      exact stepStmtsTo_length_eq hAll hTo'

/-! ## 2. Full-Map Certificate Checker (`checkMirCert`) -/

/-- Every feasible successor edge `(target, envT)` lands on an existing block
whose certified entry invariant includes `envT`. -/
def checkEdgesAgainstCert (bbs : List BasicBlockData)
    (invs : List (Option MirAbsEnv)) : List (Nat × MirAbsEnv) → Bool
  | [] => true
  | (t, e) :: rest =>
    (match get? bbs t, get? invs t with
     | some _, some (some invT) => mirAbsEnvLe e invT
     | _, _ => false) && checkEdgesAgainstCert bbs invs rest

/-- Every edge accepted by `checkEdgesAgainstCert` lands on an existing
block whose certified invariant includes the edge environment. -/
theorem checkEdgesAgainstCert_mem {bbs : List BasicBlockData}
    {invs : List (Option MirAbsEnv)} :
    ∀ {edges : List (Nat × MirAbsEnv)} {target : Nat} {envT : MirAbsEnv},
      checkEdgesAgainstCert bbs invs edges = true →
      List.Mem (target, envT) edges →
      ∃ bbT invT,
        get? bbs target = some bbT ∧
        get? invs target = some (some invT) ∧
        mirAbsEnvLe envT invT = true
  | [], _, _, _, hMem => nomatch hMem
  | (t, e) :: rest, target, envT, hChk, hMem => by
    simp only [checkEdgesAgainstCert] at hChk
    cases hMem with
    | head =>
      have hHead := bool_and_true_left hChk
      cases hBb : get? bbs t with
      | none => rw [hBb] at hHead; nomatch hHead
      | some bbT =>
        cases hInv : get? invs t with
        | none => rw [hBb, hInv] at hHead; nomatch hHead
        | some optInv =>
          cases optInv with
          | none => rw [hBb, hInv] at hHead; nomatch hHead
          | some invT =>
            rw [hBb, hInv] at hHead
            exact ⟨bbT, invT, rfl, rfl, hHead⟩
    | tail _ hTail =>
      exact checkEdgesAgainstCert_mem (bool_and_true_right hChk) hTail

/-- Check block `bb` under its certified entry invariant `invOpt`. Blocks with
`invOpt = none` are claimed unreachable and skipped. -/
def checkBlockCert (decls : List LocalDecl) (retInv : MirAbsSlot)
    (bbs : List BasicBlockData) (invs : List (Option MirAbsEnv))
    (bb : BasicBlockData) (invOpt : Option MirAbsEnv) : Bool :=
  match invOpt with
  | none => true
  | some entryEnv =>
    Nat.beq (length entryEnv) (length decls) &&
      match stepStmtsAbs decls entryEnv bb.statements with
      | none => false
      | some exitEnv =>
        match stepTermAbs exitEnv bb.terminator with
        | none => false
        | some (.ret retSlot) => MirAbsSlot.le retSlot retInv
        | some (.edges succs) => checkEdgesAgainstCert bbs invs succs

/-- Pointwise `checkBlockCert` over aligned block and invariant lists. -/
def checkAllBlocksCert (decls : List LocalDecl) (retInv : MirAbsSlot)
    (bbsAll : List BasicBlockData) (invs : List (Option MirAbsEnv)) :
    List BasicBlockData → List (Option MirAbsEnv) → Bool
  | [], [] => true
  | bb :: bbs, o :: os =>
    checkBlockCert decls retInv bbsAll invs bb o &&
      checkAllBlocksCert decls retInv bbsAll invs bbs os
  | _, _ => false

/-- `checkAllBlocksCert` checks the certificate of every aligned block. -/
theorem checkAllBlocksCert_get {decls : List LocalDecl} {retInv : MirAbsSlot}
    {bbsAll : List BasicBlockData} {invs : List (Option MirAbsEnv)} :
    ∀ {bbs : List BasicBlockData} {os : List (Option MirAbsEnv)} {i : Nat}
      {bb : BasicBlockData} {invOpt : Option MirAbsEnv},
      checkAllBlocksCert decls retInv bbsAll invs bbs os = true →
      get? bbs i = some bb →
      get? os i = some invOpt →
      checkBlockCert decls retInv bbsAll invs bb invOpt = true
  | [], _, _, _, _, _, h1, _ => nomatch h1
  | _ :: _, [], _, _, _, h, _, _ => nomatch h
  | _ :: _, _ :: _, 0, _, _, h, h1, h2 => by
    injection h1 with hb
    injection h2 with ho
    subst hb
    subst ho
    exact bool_and_true_left h
  | _ :: bbs, _ :: os, i + 1, _, _, h, h1, h2 =>
    checkAllBlocksCert_get (bbs := bbs) (os := os) (bool_and_true_right h) h1 h2

/-- Full-map post-fixpoint certificate checker for `body`: the phase is
supported, `entryEnv` matches `body.localDecls` in length, the return
postcondition `retInv` is guard-free, `entryEnv` is included in the invariant
of block `0`, and every block certificate checks. -/
def checkMirCert (body : CapturedMir) (entryEnv : MirAbsEnv)
    (retInv : MirAbsSlot) (invs : List (Option MirAbsEnv)) : Bool :=
  mirPhaseSupported body.phase &&
    (Nat.beq (length entryEnv) (length body.localDecls) &&
      (retInv.noRelGuard &&
        ((match get? body.basicBlocks 0, get? invs 0 with
          | some _, some (some inv0) => mirAbsEnvLe entryEnv inv0
          | _, _ => false) &&
          checkAllBlocksCert body.localDecls retInv body.basicBlocks invs
            body.basicBlocks invs)))

/-! ## 3. Concrete Invariant, Reachability, and Safety -/

/-- Concrete state invariant maintained along every certified transition: a
root frame (no caller, callee, or protector) positioned inside a certified
block, with locals satisfying the abstract environment reached by stepping
the block's entry invariant over the executed statement prefix. -/
def MirPccInv (body : CapturedMir) (invs : List (Option MirAbsEnv))
    (s : MachineState) : Prop :=
  s.memory.callStack = [] ∧ s.memory.activeCallee = none ∧
    s.memory.activeProtectors = [] ∧
    ∃ bb entryEnv curEnv,
      get? body.basicBlocks s.frame.blockIdx = some bb ∧
      get? invs s.frame.blockIdx = some (some entryEnv) ∧
      s.frame.stmtIdx ≤ length bb.statements ∧
      stepStmtsTo body.localDecls entryEnv bb.statements s.frame.stmtIdx =
        some curEnv ∧
      mirAbsEnvDenote body.localDecls curEnv s.frame.locals

/-- One certified step from an invariant state: `stepMirFn` either steps
(silently or with a `switchInt` event) to another invariant state preserving
`MirMemFrame`, or returns normally with a value described by `retInv` and a
memory preserving `MirMemFrame`. -/
theorem mirPccInv_step {body : CapturedMir} {retInv : MirAbsSlot}
    {invs : List (Option MirAbsEnv)} {s : MachineState}
    (hPhase : mirPhaseSupported body.phase = true)
    (hAll : checkAllBlocksCert body.localDecls retInv body.basicBlocks invs
      body.basicBlocks invs = true)
    (hInv : MirPccInv body invs s) :
    (∃ obs s', stepMirFn body s = MirStepNode.emitStep obs s' ∧
      MirMemFrame s'.memory s.memory ∧
      MirPccInv body invs s') ∨
    (∃ retVal mem' d, stepMirFn body s = MirStepNode.retNormal retVal mem' ∧
      MirMemFrame mem' s.memory ∧
      get? body.localDecls 0 = some d ∧
      retInv.denote d.ty s.frame.locals (.init retVal)) := by
  match hInv with
  | ⟨hCS, hCallee, hProt, bb, entryEnv, curEnv, hBb, hInvB, hLe, hTo, hDen⟩ =>
  have hBlk := bool_and_true_right (checkAllBlocksCert_get hAll hBb hInvB)
  cases hStmts : stepStmtsAbs body.localDecls entryEnv bb.statements with
  | none => rw [hStmts] at hBlk; nomatch hBlk
  | some exitEnv =>
    rw [hStmts] at hBlk
    dsimp only at hBlk
    cases Nat.lt_or_eq_of_le hLe with
    | inl hLt =>
      cases get?_some_of_lt hLt with
      | intro stmt hStmt =>
        cases stepStmtsTo_succ_of_stepStmtsAbs hStmts hTo hStmt with
        | intro nextEnv hNext =>
          cases stepMirFn_stmt_sound hPhase hCallee hBb hStmt hDen hProt
              hNext.1 with
          | intro locals' h =>
            cases h with
            | intro mem' h =>
              have hF := h.2.1
              refine Or.inl ⟨.silent, advanceStmt s locals' mem', h.1, hF, ?_⟩
              exact ⟨hF.2.2.2.1.trans hCS, hF.2.2.2.2.1.trans hCallee,
                hF.2.2.2.2.2.trans hProt, bb, entryEnv, nextEnv, hBb, hInvB,
                Nat.succ_le_of_lt hLt, hNext.2, h.2.2⟩
    | inr hEq =>
      have hCur : curEnv = exitEnv :=
        stepStmtsTo_length_eq hStmts (by rw [← hEq]; exact hTo)
      subst hCur
      cases hT : stepTermAbs curEnv bb.terminator with
      | none => rw [hT] at hBlk; nomatch hBlk
      | some out =>
        rw [hT] at hBlk
        have hTS := stepMirFn_term_sound hPhase hCallee hBb hEq hDen hProt hCS hT
        cases out with
        | ret retSlot =>
          cases hTS with
          | intro retVal hTS =>
            cases hTS with
            | intro mem' hTS =>
              cases hTS with
              | intro d hTS =>
                exact Or.inr ⟨retVal, mem', d, hTS.2.1, hTS.2.2.1, hTS.1,
                  mirAbsSlot_le_sound hBlk hTS.2.2.2⟩
        | edges succs =>
          match hTS with
          | ⟨target, envT, obs, locals', mem', hMem, hStep, hF, hDenT⟩ =>
            cases checkEdgesAgainstCert_mem hBlk hMem with
            | intro bbT h =>
              cases h with
              | intro invT h =>
                refine Or.inl ⟨obs, _, hStep, hF, ?_⟩
                exact ⟨hF.2.2.2.1.trans hCS, hF.2.2.2.2.1.trans hCallee,
                  hF.2.2.2.2.2.trans hProt, bbT, invT, invT, h.1, h.2.1,
                  Nat.zero_le _, rfl, mirAbsEnvLe_sound h.2.2 hDenT⟩

/-- Reflexive-transitive closure of the non-faulting `stepMirFn`
transitions (silent steps and `switchInt` event steps) from `s0`. -/
inductive MirReach (body : CapturedMir) (s0 : MachineState) :
    MachineState → Prop where
  | refl : MirReach body s0 s0
  | step {s s' : MachineState} (obs : MirObs) :
      MirReach body s0 s → stepMirFn body s = MirStepNode.emitStep obs s' →
      MirReach body s0 s'

/-- `stepMirFn` at `s` is a silent or event step, or a normal return: it does
not fault, hit an unsupported construct, halt abnormally, or call out. -/
def MirSafeStep (body : CapturedMir) (s : MachineState) : Prop :=
  (∃ obs s', stepMirFn body s = MirStepNode.emitStep obs s') ∨
    (∃ retVal mem, stepMirFn body s = MirStepNode.retNormal retVal mem)

/-- Unbounded-iteration safety: every state reachable from `s0` steps
safely. -/
def SafeFrom (body : CapturedMir) (s0 : MachineState) : Prop :=
  ∀ s, MirReach body s0 s → MirSafeStep body s

/-- `retVal` is returned normally by some execution from `s0`. -/
def ReturnsFrom (body : CapturedMir) (s0 : MachineState)
    (retVal : Value) : Prop :=
  ∃ s mem, MirReach body s0 s ∧
    stepMirFn body s = MirStepNode.retNormal retVal mem

/-- Root start state at the entry of block `0`. -/
def MirRootStart (s : MachineState) : Prop :=
  s.memory.callStack = [] ∧ s.memory.activeCallee = none ∧
    s.memory.activeProtectors = [] ∧ s.frame.blockIdx = 0 ∧
    s.frame.stmtIdx = 0

/-- A step node is never a normal-return node. -/
theorem emitStep_ne_retNormal {obs : MirObs} {s' : MachineState}
    {retVal : Value} {mem : Memory} :
    MirStepNode.emitStep obs s' ≠ MirStepNode.retNormal retVal mem := by
  intro h
  cases obs with
  | silent => nomatch h
  | event _ => nomatch h

/-- Successor state of a silent or event step node. -/
def emitStepNext? : MirStepNode → Option MachineState
  | .tau (.running s') => some s'
  | .vis (.inr (.inl (.emit _))) k =>
    match k PUnit.unit with
    | .running s' => some s'
    | _ => none
  | _ => none

/-- `emitStepNext?` recovers the successor of a step node. -/
theorem emitStepNext?_emitStep (obs : MirObs) (s' : MachineState) :
    emitStepNext? (MirStepNode.emitStep obs s') = some s' := by
  cases obs <;> rfl

/-- Step nodes determine their successor state. -/
theorem emitStep_inj {o1 o2 : MirObs} {s1 s2 : MachineState}
    (h : MirStepNode.emitStep o1 s1 = MirStepNode.emitStep o2 s2) :
    s1 = s2 := by
  have h' := congrArg emitStepNext? h
  rw [emitStepNext?_emitStep, emitStepNext?_emitStep] at h'
  injection h'

/-- Normal-return nodes determine their returned value. -/
theorem retNormal_inj {v1 v2 : Value} {m1 m2 : Memory}
    (h : MirStepNode.retNormal v1 m1 = MirStepNode.retNormal v2 m2) :
    v1 = v2 := by
  cases h
  rfl

/-- The certificate invariant holds at the root entry state. -/
theorem mirPccInv_start {body : CapturedMir} {entryEnv : MirAbsEnv}
    {retInv : MirAbsSlot} {invs : List (Option MirAbsEnv)} {s0 : MachineState}
    (hChk : checkMirCert body entryEnv retInv invs = true)
    (hStart : MirRootStart s0)
    (hEntry : mirAbsEnvDenote body.localDecls entryEnv s0.frame.locals) :
    MirPccInv body invs s0 := by
  have hEntryChk := bool_and_true_left
    (bool_and_true_right
      (bool_and_true_right (bool_and_true_right hChk)))
  match hStart with
  | ⟨hCS, hCallee, hProt, hBlk, hIdx⟩ =>
  cases hBb0 : get? body.basicBlocks 0 with
  | none => rw [hBb0] at hEntryChk; nomatch hEntryChk
  | some bb0 =>
    cases hInv0 : get? invs 0 with
    | none => rw [hBb0, hInv0] at hEntryChk; nomatch hEntryChk
    | some opt0 =>
      cases opt0 with
      | none => rw [hBb0, hInv0] at hEntryChk; nomatch hEntryChk
      | some inv0 =>
        rw [hBb0, hInv0] at hEntryChk
        refine ⟨hCS, hCallee, hProt, bb0, inv0, inv0, ?_, ?_, ?_, ?_,
          mirAbsEnvLe_sound hEntryChk hEntry⟩
        · rw [hBlk]; exact hBb0
        · rw [hBlk]; exact hInv0
        · rw [hIdx]; exact Nat.zero_le _
        · rw [hIdx]; rfl

/-- Every state reachable from a certified root start satisfies the
certificate invariant. -/
theorem mirPccInv_reach {body : CapturedMir} {entryEnv : MirAbsEnv}
    {retInv : MirAbsSlot} {invs : List (Option MirAbsEnv)}
    {s0 s : MachineState}
    (hChk : checkMirCert body entryEnv retInv invs = true)
    (hStart : MirRootStart s0)
    (hEntry : mirAbsEnvDenote body.localDecls entryEnv s0.frame.locals)
    (hR : MirReach body s0 s) : MirPccInv body invs s := by
  have hPhase := bool_and_true_left hChk
  have hAll := bool_and_true_right
    (bool_and_true_right
      (bool_and_true_right (bool_and_true_right hChk)))
  induction hR with
  | refl => exact mirPccInv_start hChk hStart hEntry
  | step obs _ hStep ih =>
    cases mirPccInv_step (retInv := retInv) hPhase hAll ih with
    | inl h =>
      match h with
      | ⟨obs', s'', hStep', _, hInv'⟩ =>
        rw [hStep] at hStep'
        rw [emitStep_inj hStep']
        exact hInv'
    | inr h =>
      match h with
      | ⟨_, _, _, hRet, _, _, _⟩ =>
        rw [hStep] at hRet
        exact False.elim (emitStep_ne_retNormal hRet)

/-! ## 4. Interaction-Tree Safety (`MirNoUBTree`) -/

/-- An `ITree.cofix` unfolding is `TreeSafe` when an invariant on coalgebra
states is preserved by silent and visible steps and no reachable visible
request is a fault. -/
theorem treeSafe_cofix_of_inv {E : Effect} {R S : Type} [FaultEffect E]
    (step : S → ITreeF E R S) (P : S → Prop)
    (hTau : ∀ s s', P s → step s = .tau s' → P s')
    (hVis : ∀ s i k, P s → step s = .vis i k →
      ¬ FaultEffect.isFault i ∧ ∀ o, P (k o))
    {s0 : S} (h0 : P s0) : TreeSafe (ITree.cofix step s0) := by
  have hTauT : ∀ (t t' : ITree E R), (∃ s, P s ∧ t = ITree.cofix step s) →
      t.observe = .tau t' → ∃ s, P s ∧ t' = ITree.cofix step s := by
    intro t t' hQ hObs
    match hQ with
    | ⟨s, hP, hEq⟩ =>
      subst hEq
      rw [ITree.observe_cofix] at hObs
      cases hS : step s with
      | ret r => rw [hS] at hObs; nomatch hObs
      | tau x =>
        rw [hS] at hObs
        injection hObs with hObs
        exact ⟨x, hTau s x hP hS, hObs.symm⟩
      | vis i k => rw [hS] at hObs; nomatch hObs
  have hVisT : ∀ (t : ITree E R) (i : E.I) (k : E.O i → ITree E R),
      (∃ s, P s ∧ t = ITree.cofix step s) → t.observe = .vis i k →
      ¬ FaultEffect.isFault i ∧
        ∀ o, ∃ s, P s ∧ k o = ITree.cofix step s := by
    intro t i k hQ hObs
    match hQ with
    | ⟨s, hP, hEq⟩ =>
      subst hEq
      rw [ITree.observe_cofix] at hObs
      cases hS : step s with
      | ret r => rw [hS] at hObs; nomatch hObs
      | tau x => rw [hS] at hObs; nomatch hObs
      | vis i' k' =>
        rw [hS] at hObs
        have hV := hVis s i' k' hP hS
        cases hObs
        exact ⟨hV.1, fun o => ⟨k' o, hV.2 o, rfl⟩⟩
  have hTauStar : ∀ (t u : ITree E R), TauStar t u →
      (∃ s, P s ∧ t = ITree.cofix step s) →
      ∃ s, P s ∧ u = ITree.cofix step s := by
    intro t u hT
    induction hT with
    | refl => exact fun h => h
    | step hObs _ ih => exact fun h => ih (hTauT _ _ h hObs)
  have hReach : ∀ (t : ITree E R) tr (u : ITree E R), Reaches t tr u →
      (∃ s, P s ∧ t = ITree.cofix step s) →
      ∃ s, P s ∧ u = ITree.cofix step s := by
    intro t tr u hR
    induction hR with
    | refl => exact fun h => h
    | tau hObs _ ih => exact fun h => ih (hTauT _ _ h hObs)
    | vis hObs _ o _ ih => exact fun h => ih ((hVisT _ _ _ h hObs).2 o)
  intro tr u hR hFault
  have hU := hReach _ tr u hR ⟨s0, h0, rfl⟩
  match hFault with
  | ⟨t', i, k, hT, hObs, hIsF⟩ =>
    exact (hVisT t' i k (hTauStar u t' hT hU) hObs).1 hIsF

/-- Coalgebra-state invariant for `mirTree`: running states satisfy
`MirPccInv`, halted states are terminal, and faulted states never occur. -/
def MirPccExecInv (body : CapturedMir) (invs : List (Option MirAbsEnv)) :
    MirExecState → Prop
  | .running s => MirPccInv body invs s
  | .halted _ => True
  | .faulted _ => False

/-- `MirNoUBTree` of the interaction tree unfolded from any invariant
state. -/
theorem mirNoUBTree_of_mirPccInv {body : CapturedMir} {retInv : MirAbsSlot}
    {invs : List (Option MirAbsEnv)} {s0 : MachineState}
    (hPhase : mirPhaseSupported body.phase = true)
    (hAll : checkAllBlocksCert body.localDecls retInv body.basicBlocks invs
      body.basicBlocks invs = true)
    (h0 : MirPccInv body invs s0) : MirNoUBTree (mirTree body s0) := by
  refine treeSafe_cofix_of_inv (stepMirState body) (MirPccExecInv body invs)
    ?_ ?_ (s0 := .running s0) h0
  · intro es es' hP hS
    cases es with
    | running s =>
      cases mirPccInv_step (retInv := retInv) hPhase hAll hP with
      | inl h =>
        match h with
        | ⟨obs, s', hStep, _, hInv'⟩ =>
          have hS' : stepMirFn body s = .tau es' := hS
          rw [hStep] at hS'
          cases obs with
          | silent => cases hS'; exact hInv'
          | event _ => nomatch hS'
      | inr h =>
        match h with
        | ⟨_, _, _, hRet, _, _, _⟩ =>
          have hS' : stepMirFn body s = .tau es' := hS
          rw [hRet] at hS'
          nomatch hS'
    | halted _ => nomatch hS
    | faulted _ => exact False.elim hP
  · intro es i k hP hS
    cases es with
    | running s =>
      cases mirPccInv_step (retInv := retInv) hPhase hAll hP with
      | inl h =>
        match h with
        | ⟨obs, s', hStep, _, hInv'⟩ =>
          have hS' : stepMirFn body s = .vis i k := hS
          rw [hStep] at hS'
          cases obs with
          | silent => nomatch hS'
          | event _ =>
            cases hS'
            exact ⟨fun hF => hF, fun _ => hInv'⟩
      | inr h =>
        match h with
        | ⟨_, _, _, hRet, _, _, _⟩ =>
          have hS' : stepMirFn body s = .vis i k := hS
          rw [hRet] at hS'
          nomatch hS'
    | halted _ => nomatch hS
    | faulted _ => exact False.elim hP

/-! ## 5. `Anneal.ParametricCore` Weakest-Precondition Bridge -/

/-- Read one `stepMirFn` node as a deterministic `StepOutcome`: silent and
`MirObsE` event steps continue, returns terminate, and every fault or
external call is a fault. -/
def mirNodeOutcome :
    MirStepNode → Anneal.ParametricCore.StepOutcome MachineState MirOutcome Unit
  | .ret out => .done out
  | .tau (.running s') => .step s'
  | .tau (.halted out) => .done out
  | .tau (.faulted _) => .fault ()
  | .vis (.inr (.inl (.emit _))) k =>
    match k PUnit.unit with
    | .running s' => .step s'
    | .halted out => .done out
    | .faulted _ => .fault ()
  | .vis _ _ => .fault ()

/-- Deterministic `MirWpOps` interface of `stepMirFn body`, exposing the
current block index as `blockTag?`. -/
@[reducible] def mirPccWpOps (body : CapturedMir) :
    Anneal.ParametricCore.MirWpOps MachineState MirOutcome Unit :=
  Anneal.ParametricCore.MirWpOps.ofDetStep
    (fun s => mirNodeOutcome (stepMirFn body s))
    (fun s => some s.frame.blockIdx)

/-- Certified postcondition on terminal outcomes: a normal return whose value
satisfies `retInv.valDenote` at the declared return type. -/
def mirRetPost (body : CapturedMir) (retInv : MirAbsSlot) :
    MirOutcome → Prop
  | .normal (retVal, _) =>
    ∃ d, get? body.localDecls 0 = some d ∧ retInv.valDenote d.ty retVal
  | _ => False

/-- `MirPccInv` is an inductive, fault-free step invariant of `mirPccWpOps`
whose terminal outcomes satisfy `mirRetPost`. -/
theorem mirPccInv_stepWp {body : CapturedMir} {retInv : MirAbsSlot}
    {invs : List (Option MirAbsEnv)} {s : MachineState}
    (hPhase : mirPhaseSupported body.phase = true)
    (hNoG : retInv.noRelGuard = true)
    (hAll : checkAllBlocksCert body.localDecls retInv body.basicBlocks invs
      body.basicBlocks invs = true)
    (hInv : MirPccInv body invs s) :
    (mirPccWpOps body).stepWp s (MirPccInv body invs) (mirRetPost body retInv)
      (fun _ => False) := by
  cases mirPccInv_step (retInv := retInv) hPhase hAll hInv with
  | inl h =>
    match h with
    | ⟨obs, s', hStep, _, hInv'⟩ =>
      show (mirNodeOutcome (stepMirFn body s)).wp _ _ _
      rw [hStep]
      cases obs with
      | silent => exact hInv'
      | event _ => exact hInv'
  | inr h =>
    match h with
    | ⟨retVal, mem', d, hRet, _, hD, hDen⟩ =>
      show (mirNodeOutcome (stepMirFn body s)).wp _ _ _
      rw [hRet]
      exact ⟨d, hD, mirAbsSlot_valDenote_of_denote hNoG hDen⟩

/-- Fault-tolerant checkpoint convergence from an invariant state upgrades to
fault-free convergence: every execution reaches `stop` (inside the invariant)
or returns a value satisfying `retInv`. -/
theorem wpUntilOk_of_mirPccInv {body : CapturedMir} {retInv : MirAbsSlot}
    {invs : List (Option MirAbsEnv)} {stop : MachineState → Prop}
    {s : MachineState}
    (hPhase : mirPhaseSupported body.phase = true)
    (hNoG : retInv.noRelGuard = true)
    (hAll : checkAllBlocksCert body.localDecls retInv body.basicBlocks invs
      body.basicBlocks invs = true)
    (hConv : @Anneal.ParametricCore.wpUntil _ _ _ (mirPccWpOps body) stop
      (fun _ => True) (fun _ => True) s)
    (hInv : MirPccInv body invs s) :
    @Anneal.ParametricCore.wpUntilOk _ _ _ (mirPccWpOps body)
      (fun s' => stop s' ∧ MirPccInv body invs s') (mirRetPost body retInv)
      s := by
  revert hInv
  refine Anneal.ParametricCore.wpUntil_induction (ops := mirPccWpOps body)
    (C := fun s' => MirPccInv body invs s' →
      @Anneal.ParametricCore.wpUntilOk _ _ _ (mirPccWpOps body)
        (fun s'' => stop s'' ∧ MirPccInv body invs s'')
        (mirRetPost body retInv) s')
    ?_ ?_ hConv
  · intro s' hStop hInv'
    exact @Anneal.ParametricCore.wpUntil_here _ _ _ (mirPccWpOps body) _ _ _ _
      ⟨hStop, hInv'⟩
  · intro s' hStepC hInv'
    have hBoth := Anneal.ParametricCore.MirWpOps.ofDetStep_conjunctive
      (fun s => mirNodeOutcome (stepMirFn body s))
      (fun s => some s.frame.blockIdx) s' _ _ _ _ _ _ hStepC
      (mirPccInv_stepWp hPhase hNoG hAll hInv')
    refine Anneal.ParametricCore.wpUntil_step (ops := mirPccWpOps body) ?_
    exact (mirPccWpOps body).stepWp_mono (fun _ h => h.1 h.2)
      (fun _ h => h.2) (fun _ h => h.2) hBoth

/-- Fault-tolerant termination from an invariant state upgrades to fault-free
total correctness with the certified postcondition (`wpStateOk`). -/
theorem wpStateOk_of_mirPccInv {body : CapturedMir} {retInv : MirAbsSlot}
    {invs : List (Option MirAbsEnv)} {s : MachineState}
    (hPhase : mirPhaseSupported body.phase = true)
    (hNoG : retInv.noRelGuard = true)
    (hAll : checkAllBlocksCert body.localDecls retInv body.basicBlocks invs
      body.basicBlocks invs = true)
    (hTerm : @Anneal.ParametricCore.wpOutcome _ _ _ (mirPccWpOps body)
      (fun _ => True) (fun _ => True) s)
    (hInv : MirPccInv body invs s) :
    @Anneal.ParametricCore.wpStateOk _ _ _ (mirPccWpOps body)
      (mirRetPost body retInv) s :=
  @Anneal.ParametricCore.wpUntil_mono_stop _ _ _ (mirPccWpOps body) _ _ _ _
    (fun _ h => h.1) _ (wpUntilOk_of_mirPccInv hPhase hNoG hAll hTerm hInv)

/-! ## 6. Main Soundness Theorem (`checkMirCert_sound`) -/

/-- PCC soundness of `checkMirCert`: from every root start state at the entry
of block `0` whose locals satisfy `entryEnv`,
1. `SafeFrom body s0` (unbounded-iteration fault freedom under `stepMirFn`),
2. every normally returned value satisfies `retInv.valDenote`,
3. `MirNoUBTree (mirTree body s0)`, and
4. any fault-tolerant `wpOutcome` termination proof over `mirPccWpOps`
   upgrades to `wpStateOk` with postcondition `mirRetPost body retInv`. -/
theorem checkMirCert_sound {body : CapturedMir} {entryEnv : MirAbsEnv}
    {retInv : MirAbsSlot} {invs : List (Option MirAbsEnv)} {s0 : MachineState}
    (hChk : checkMirCert body entryEnv retInv invs = true)
    (hStart : MirRootStart s0)
    (hEntry : mirAbsEnvDenote body.localDecls entryEnv s0.frame.locals) :
    SafeFrom body s0 ∧
    (∀ retVal, ReturnsFrom body s0 retVal →
      ∃ d, get? body.localDecls 0 = some d ∧ retInv.valDenote d.ty retVal) ∧
    MirNoUBTree (mirTree body s0) ∧
    (@Anneal.ParametricCore.wpOutcome _ _ _ (mirPccWpOps body)
        (fun _ => True) (fun _ => True) s0 →
      @Anneal.ParametricCore.wpStateOk _ _ _ (mirPccWpOps body)
        (mirRetPost body retInv) s0) := by
  have hPhase := bool_and_true_left hChk
  have hRest1 := bool_and_true_right (bool_and_true_right hChk)
  have hNoG := bool_and_true_left hRest1
  have hAll := bool_and_true_right (bool_and_true_right hRest1)
  have hInv0 := mirPccInv_start hChk hStart hEntry
  refine ⟨?_, ?_, mirNoUBTree_of_mirPccInv hPhase hAll hInv0,
    fun hTerm => wpStateOk_of_mirPccInv hPhase hNoG hAll hTerm hInv0⟩
  · intro s hR
    cases mirPccInv_step (retInv := retInv) hPhase hAll
        (mirPccInv_reach hChk hStart hEntry hR) with
    | inl h =>
      match h with
      | ⟨obs, s', hStep, _, _⟩ => exact Or.inl ⟨obs, s', hStep⟩
    | inr h =>
      match h with
      | ⟨retVal, mem', _, hRet, _, _, _⟩ => exact Or.inr ⟨retVal, mem', hRet⟩
  · intro retVal hRet
    match hRet with
    | ⟨s, mem, hR, hStepRet⟩ =>
      cases mirPccInv_step (retInv := retInv) hPhase hAll
          (mirPccInv_reach hChk hStart hEntry hR) with
      | inl h =>
        match h with
        | ⟨_, _, hStep, _, _⟩ =>
          rw [hStep] at hStepRet
          exact False.elim (emitStep_ne_retNormal hStepRet)
      | inr h =>
        match h with
        | ⟨retVal', mem', d, hRet', _, hD, hDen⟩ =>
          rw [hRet'] at hStepRet
          have hV := retNormal_inj hStepRet
          subst hV
          exact ⟨d, hD, mirAbsSlot_valDenote_of_denote hNoG hDen⟩

/-- Checkpoint convergence (`wpUntil`) from a certified root start upgrades to
fault-free `wpUntilOk` with the certified invariant and return postcondition. -/
theorem checkMirCert_wpUntilOk {body : CapturedMir} {entryEnv : MirAbsEnv}
    {retInv : MirAbsSlot} {invs : List (Option MirAbsEnv)}
    {stop : MachineState → Prop} {s0 : MachineState}
    (hChk : checkMirCert body entryEnv retInv invs = true)
    (hStart : MirRootStart s0)
    (hEntry : mirAbsEnvDenote body.localDecls entryEnv s0.frame.locals)
    (hConv : @Anneal.ParametricCore.wpUntil _ _ _ (mirPccWpOps body) stop
      (fun _ => True) (fun _ => True) s0) :
    @Anneal.ParametricCore.wpUntilOk _ _ _ (mirPccWpOps body)
      (fun s' => stop s' ∧ MirPccInv body invs s') (mirRetPost body retInv)
      s0 := by
  have hPhase := bool_and_true_left hChk
  have hRest1 := bool_and_true_right (bool_and_true_right hChk)
  have hNoG := bool_and_true_left hRest1
  have hAll := bool_and_true_right (bool_and_true_right hRest1)
  exact wpUntilOk_of_mirPccInv hPhase hNoG hAll hConv
    (mirPccInv_start hChk hStart hEntry)

/-- `checkMirCert_sound` specialized to a call `initMachineState body args`
whose arguments satisfy the guard-free argument slots `argSlots` of the
abstract entry frame `entryEnv body.localDecls argSlots`. -/
theorem checkMirCert_sound_call {body : CapturedMir}
    {argSlots : List MirAbsSlot} {args : List Value} {retInv : MirAbsSlot}
    {invs : List (Option MirAbsEnv)}
    (hChk : checkMirCert body (entryEnv body.localDecls argSlots) retInv invs =
      true)
    (hArgs : entryArgsOk (body.localDecls.drop 1) argSlots args) :
    SafeFrom body (initMachineState body args) ∧
    (∀ retVal, ReturnsFrom body (initMachineState body args) retVal →
      ∃ d, get? body.localDecls 0 = some d ∧ retInv.valDenote d.ty retVal) ∧
    MirNoUBTree (mirCallTree body args) ∧
    (@Anneal.ParametricCore.wpOutcome _ _ _ (mirPccWpOps body)
        (fun _ => True) (fun _ => True) (initMachineState body args) →
      @Anneal.ParametricCore.wpStateOk _ _ _ (mirPccWpOps body)
        (mirRetPost body retInv) (initMachineState body args)) := by
  have hRoot := initMachineState_root body args
  have hStart : MirRootStart (initMachineState body args) :=
    ⟨hRoot.1, hRoot.2.1, hRoot.2.2.1, hRoot.2.2.2.1, hRoot.2.2.2.2.1⟩
  have hEntry : mirAbsEnvDenote body.localDecls
      (entryEnv body.localDecls argSlots)
      (initMachineState body args).frame.locals := by
    rw [hRoot.2.2.2.2.2]
    exact entryEnv_sound hArgs
  exact checkMirCert_sound hChk hStart hEntry

/-! ## 7. Single-Pass Bourdoncle Cutpoint Materializer and Verifier -/

/-- Look up the certified invariant of block `id` in a cutpoint list. -/
def lookupCutpoint? (id : Nat) : List (Nat × MirAbsEnv) → Option MirAbsEnv
  | [] => none
  | (k, env) :: rest =>
    match Nat.beq k id with
    | true => some env
    | false => lookupCutpoint? id rest

/-- `id` is a designated cutpoint. -/
def isCutpoint (id : Nat) (cutpoints : List (Nat × MirAbsEnv)) : Bool :=
  match lookupCutpoint? id cutpoints with
  | some _ => true
  | none => false

/-- `x` occurs in `xs`. -/
def natListContains (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => Nat.beq x y || natListContains x ys

/-- `xs` has no duplicates. -/
def natListNodup : List Nat → Bool
  | [] => true
  | x :: xs => !natListContains x xs && natListNodup xs

/-- Every element of `xs` is `< n`. -/
def natListAllLt (n : Nat) : List Nat → Bool
  | [] => true
  | x :: xs => Nat.blt x n && natListAllLt n xs

/-- Block targets of an unwind action. -/
def unwindTargets : UnwindAction → List Nat
  | .cleanup b => [b]
  | _ => []

/-- Syntactic successor block indices of a terminator. -/
def syntacticTermTargets : TerminatorKind → List Nat
  | .goto target => [target]
  | .switchInt _ targets =>
    targets.otherwise :: targets.branches.map (fun p => p.2)
  | .drop _ target unwind => target :: unwindTargets unwind
  | .call _ _ _ target unwind =>
    (match target with | some t => [t] | none => []) ++ unwindTargets unwind
  | .assert _ _ target unwind => target :: unwindTargets unwind
  | .inlineAsm _ targets unwind => targets ++ unwindTargets unwind
  | .unwindResume | .unwindTerminate | .return_ | .unreachable | .tailCall _ _ =>
    []

/-- Every syntactic successor of `bb` is a cutpoint or already `visited`. -/
def succsScheduled (cutpoints : List (Nat × MirAbsEnv)) (visited : List Nat)
    (bb : BasicBlockData) : Bool :=
  (syntacticTermTargets bb.terminator.kind).all
    (fun v => isCutpoint v cutpoints || natListContains v visited)

/-- Walk `rpoOrder` from the back, checking that every edge whose target is
not a cutpoint points strictly forward. Returns the visited suffix. -/
def rpoDagOk (bbs : List BasicBlockData)
    (cutpoints : List (Nat × MirAbsEnv)) : List Nat → Bool × List Nat
  | [] => (true, [])
  | u :: rest =>
    let r := rpoDagOk bbs cutpoints rest
    let ok :=
      match get? bbs u with
      | none => false
      | some bb => succsScheduled cutpoints r.2 bb
    (ok && r.1, u :: r.2)

/-- `cutpoints` has distinct in-range keys and `rpoOrder` is a duplicate-free,
full-coverage, `0`-headed reverse-postorder permutation of the blocks modulo
`cutpoints`: every syntactic edge `u -> v` whose target `v` is not a cutpoint
advances strictly forward in `rpoOrder`. -/
def validRpoSchedule (body : CapturedMir) (cutpoints : List (Nat × MirAbsEnv))
    (rpoOrder : List Nat) : Bool :=
  let n := length body.basicBlocks
  let cpIds := cutpoints.map (fun p => p.1)
  let headOk :=
    match rpoOrder with
    | [] => false
    | b0 :: _ => Nat.beq b0 0
  natListNodup cpIds && natListAllLt n cpIds &&
    Nat.beq (length rpoOrder) n && headOk && natListNodup rpoOrder &&
    natListAllLt n rpoOrder && (rpoDagOk body.basicBlocks cutpoints rpoOrder).1

/-- Initial invariant table for blocks `idx .. idx + k - 1`: cutpoints get
their certified invariant and block `0` (unless it is a cutpoint) gets
`entryEnv`. -/
def seedBlockInvs (entryEnv : MirAbsEnv) (cutpoints : List (Nat × MirAbsEnv)) :
    Nat → Nat → List (Option MirAbsEnv)
  | 0, _ => []
  | k + 1, idx =>
    (match lookupCutpoint? idx cutpoints with
     | some env => some env
     | none =>
       match Nat.beq idx 0 with
       | true => some entryEnv
       | false => none) :: seedBlockInvs entryEnv cutpoints k (idx + 1)

/-- Propagate one successor edge `(tgt, envT)` into the table when `tgt` is
not a cutpoint, joining with any earlier acyclic incoming state. -/
def propagateEdge (cutpoints : List (Nat × MirAbsEnv))
    (invs : List (Option MirAbsEnv)) (tgt : Nat) (envT : MirAbsEnv) :
    List (Option MirAbsEnv) :=
  match isCutpoint tgt cutpoints with
  | true => invs
  | false =>
    match get? invs tgt with
    | some none =>
      match set? invs tgt (some envT) with
      | some invs' => invs'
      | none => invs
    | some (some prev) =>
      match mirAbsEnvJoin prev envT with
      | some joined =>
        match set? invs tgt (some joined) with
        | some invs' => invs'
        | none => invs
      | none => invs
    | none => invs

/-- Step one block of the schedule and propagate its successor edges. -/
def materializeBlock (body : CapturedMir)
    (cutpoints : List (Nat × MirAbsEnv)) (invs : List (Option MirAbsEnv))
    (bbId : Nat) : List (Option MirAbsEnv) :=
  match get? body.basicBlocks bbId, get? invs bbId with
  | some bb, some (some env) =>
    match stepStmtsAbs body.localDecls env bb.statements with
    | none => invs
    | some exitEnv =>
      match stepTermAbs exitEnv bb.terminator with
      | some (.edges succs) =>
        succs.foldl (fun acc e => propagateEdge cutpoints acc e.1 e.2) invs
      | _ => invs
  | _, _ => invs

/-- One linear reverse-postorder pass materializing acyclic block invariants
from the entry environment and the Bourdoncle cutpoints. -/
def materializeCutpoints (body : CapturedMir) (entryEnv : MirAbsEnv)
    (cutpoints : List (Nat × MirAbsEnv)) (rpoOrder : List Nat) :
    List (Option MirAbsEnv) :=
  rpoOrder.foldl (materializeBlock body cutpoints)
    (seedBlockInvs entryEnv cutpoints (length body.basicBlocks) 0)

/-- Single-pass Bourdoncle cutpoint verifier: validates the schedule shape,
materializes acyclic block invariants in one forward pass, and checks the
resulting post-fixpoint with `checkMirCert` (which carries the soundness
obligation). -/
def verifyMirCutpoints (body : CapturedMir) (entryEnv : MirAbsEnv)
    (retInv : MirAbsSlot) (cutpoints : List (Nat × MirAbsEnv))
    (rpoOrder : List Nat) : Bool :=
  validRpoSchedule body cutpoints rpoOrder &&
    checkMirCert body entryEnv retInv
      (materializeCutpoints body entryEnv cutpoints rpoOrder)

/-- Soundness of `verifyMirCutpoints`: the conclusions of `checkMirCert_sound`
for the materialized invariant table. -/
theorem verifyMirCutpoints_sound {body : CapturedMir} {entryEnv : MirAbsEnv}
    {retInv : MirAbsSlot} {cutpoints : List (Nat × MirAbsEnv)}
    {rpoOrder : List Nat} {s0 : MachineState}
    (hVer : verifyMirCutpoints body entryEnv retInv cutpoints rpoOrder = true)
    (hStart : MirRootStart s0)
    (hEntry : mirAbsEnvDenote body.localDecls entryEnv s0.frame.locals) :
    SafeFrom body s0 ∧
    (∀ retVal, ReturnsFrom body s0 retVal →
      ∃ d, get? body.localDecls 0 = some d ∧ retInv.valDenote d.ty retVal) ∧
    MirNoUBTree (mirTree body s0) ∧
    (@Anneal.ParametricCore.wpOutcome _ _ _ (mirPccWpOps body)
        (fun _ => True) (fun _ => True) s0 →
      @Anneal.ParametricCore.wpStateOk _ _ _ (mirPccWpOps body)
        (mirRetPost body retInv) s0) :=
  checkMirCert_sound (bool_and_true_right hVer) hStart hEntry

/-- Checkpoint convergence (`wpUntil`) from a verified cutpoint certificate
upgrades to fault-free `wpUntilOk`. -/
theorem verifyMirCutpoints_wpUntilOk {body : CapturedMir}
    {entryEnv : MirAbsEnv} {retInv : MirAbsSlot}
    {cutpoints : List (Nat × MirAbsEnv)} {rpoOrder : List Nat}
    {stop : MachineState → Prop} {s0 : MachineState}
    (hVer : verifyMirCutpoints body entryEnv retInv cutpoints rpoOrder = true)
    (hStart : MirRootStart s0)
    (hEntry : mirAbsEnvDenote body.localDecls entryEnv s0.frame.locals)
    (hConv : @Anneal.ParametricCore.wpUntil _ _ _ (mirPccWpOps body) stop
      (fun _ => True) (fun _ => True) s0) :
    @Anneal.ParametricCore.wpUntilOk _ _ _ (mirPccWpOps body)
      (fun s' => stop s' ∧
        MirPccInv body (materializeCutpoints body entryEnv cutpoints rpoOrder)
          s')
      (mirRetPost body retInv) s0 :=
  checkMirCert_wpUntilOk (bool_and_true_right hVer) hStart hEntry hConv

/-- `verifyMirCutpoints_sound` specialized to `initMachineState body args`. -/
theorem verifyMirCutpoints_sound_call {body : CapturedMir}
    {argSlots : List MirAbsSlot} {args : List Value} {retInv : MirAbsSlot}
    {cutpoints : List (Nat × MirAbsEnv)} {rpoOrder : List Nat}
    (hVer : verifyMirCutpoints body (entryEnv body.localDecls argSlots) retInv
      cutpoints rpoOrder = true)
    (hArgs : entryArgsOk (body.localDecls.drop 1) argSlots args) :
    SafeFrom body (initMachineState body args) ∧
    (∀ retVal, ReturnsFrom body (initMachineState body args) retVal →
      ∃ d, get? body.localDecls 0 = some d ∧ retInv.valDenote d.ty retVal) ∧
    MirNoUBTree (mirCallTree body args) ∧
    (@Anneal.ParametricCore.wpOutcome _ _ _ (mirPccWpOps body)
        (fun _ => True) (fun _ => True) (initMachineState body args) →
      @Anneal.ParametricCore.wpStateOk _ _ _ (mirPccWpOps body)
        (mirRetPost body retInv) (initMachineState body args)) :=
  checkMirCert_sound_call (bool_and_true_right hVer) hArgs

/-! ## 8. Trusted Verification Certificates -/

/-- `initMachineStateWithCallees body args callees` starts at a root frame
with `initLocals body args`, regardless of whether `callees` is empty. -/
theorem initMachineStateWithCallees_root (body : CapturedMir)
    (args : List Value) (callees : List CapturedMir) :
    MirRootStart
      (Trusted.Rustc.V2026_06_01.MirSemantics.initMachineStateWithCallees
        body args callees) ∧
    (Trusted.Rustc.V2026_06_01.MirSemantics.initMachineStateWithCallees
        body args callees).frame.locals = initLocals body args := by
  cases callees with
  | nil =>
    have h := initMachineState_root body args
    exact ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩, h.2.2.2.2.2⟩
  | cons _ _ =>
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

/-- Every event in `tr` is an internal `MirObsE` observation (never a fault
or an unresolved `MirCallE` external call). -/
def TraceObsOnly : List (Event MirEffect) → Prop
  | [] => True
  | e :: rest =>
    (∃ obs, e = ⟨.inr (.inl (.emit obs)), PUnit.unit⟩) ∧ TraceObsOnly rest

/-- `initMachineStateWithMemoryAndCallees body args mem callees` starts at a
root frame with `initLocals body args` and preserves `MirMemFrame` against
`mem` whenever `mem` has an empty call stack, no active callee, and no active
protectors, for arbitrary `callees`. -/
theorem initMachineStateWithMemoryAndCallees_root (body : CapturedMir)
    (args : List Value) (mem : Memory) (callees : List CapturedMir)
    (hCS : mem.callStack = []) (hCallee : mem.activeCallee = none)
    (hProt : mem.activeProtectors = []) :
    MirRootStart
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
        body args mem callees) ∧
    (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
        body args mem callees).frame.locals = initLocals body args ∧
    MirMemFrame
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
        body args mem callees).memory mem := by
  cases callees with
  | nil => exact ⟨⟨hCS, hCallee, hProt, rfl, rfl⟩, rfl, MirMemFrame.refl mem⟩
  | cons _ _ =>
    exact ⟨⟨hCS, hCallee, hProt, rfl, rfl⟩, rfl,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- Every return outcome observed in the interaction tree of an invariant
state is a normal return (`MirOutcome.normal`, ruling out `.panic` and
`.abort`) along an observation-only trace (`TraceObsOnly tr`), preserving
`MirMemFrame mem' s0.memory` and witnessed by `ReturnsFrom`. -/
theorem reachesRet_normal_of_mirPccInv {body : CapturedMir}
    {retInv : MirAbsSlot} {invs : List (Option MirAbsEnv)} {s0 : MachineState}
    {tr : List (Event MirEffect)} {out : MirOutcome}
    (hPhase : mirPhaseSupported body.phase = true)
    (hAll : checkAllBlocksCert body.localDecls retInv body.basicBlocks invs
      body.basicBlocks invs = true)
    (h0 : MirPccInv body invs s0)
    (hR : ReachesRet (mirTree body s0) tr out) :
    ∃ retVal mem',
      out = .normal (retVal, mem') ∧
      TraceObsOnly tr ∧
      MirMemFrame mem' s0.memory ∧
      ReturnsFrom body s0 retVal := by
  have hQ : ∀ (t : ITree MirEffect MirOutcome) tr' (u : ITree MirEffect MirOutcome),
      Reaches t tr' u →
      (∃ s, MirReach body s0 s ∧ MirMemFrame s.memory s0.memory ∧
        MirPccInv body invs s ∧
        t = ITree.cofix (stepMirState body) (.running s)) →
      TraceObsOnly tr' ∧
      ∃ s, MirReach body s0 s ∧ MirMemFrame s.memory s0.memory ∧
        MirPccInv body invs s ∧
        u = ITree.cofix (stepMirState body) (.running s) := by
    intro t tr' u hReach
    induction hReach with
    | refl => exact fun h => ⟨True.intro, h⟩
    | tau hObs _ ih =>
      intro h
      apply ih
      match h with
      | ⟨s, hRs, hFs, hInv, hEq⟩ =>
        subst hEq
        rw [ITree.observe_cofix] at hObs
        have hObs' : (stepMirFn body s).map (ITree.cofix (stepMirState body)) =
            .tau _ := hObs
        cases mirPccInv_step (retInv := retInv) hPhase hAll hInv with
        | inl hS =>
          match hS with
          | ⟨obs, s', hStep, hF', hInv'⟩ =>
            rw [hStep] at hObs'
            cases obs with
            | silent =>
              injection hObs' with hT
              exact ⟨s', .step .silent hRs hStep, hF'.trans hFs, hInv', hT.symm⟩
            | event _ => nomatch hObs'
        | inr hS =>
          match hS with
          | ⟨_, _, _, hRet, _, _, _⟩ =>
            rw [hRet] at hObs'
            nomatch hObs'
    | vis hObs _ o _ ih =>
      intro h
      match h with
      | ⟨s, hRs, hFs, hInv, hEq⟩ =>
        subst hEq
        rw [ITree.observe_cofix] at hObs
        have hObs' : (stepMirFn body s).map (ITree.cofix (stepMirState body)) =
            .vis _ _ := hObs
        cases mirPccInv_step (retInv := retInv) hPhase hAll hInv with
        | inl hS =>
          match hS with
          | ⟨obs, s', hStep, hF', hInv'⟩ =>
            rw [hStep] at hObs'
            cases obs with
            | silent => nomatch hObs'
            | event _ =>
              cases hObs'
              cases o with
              | unit =>
                have hNext := ih ⟨s', .step _ hRs hStep, hF'.trans hFs, hInv',
                  rfl⟩
                exact ⟨⟨⟨_, rfl⟩, hNext.1⟩, hNext.2⟩
        | inr hS =>
          match hS with
          | ⟨_, _, _, hRet, _, _, _⟩ =>
            rw [hRet] at hObs'
            nomatch hObs'
  match hR with
  | ⟨u, hReach, hObs⟩ =>
    match hQ _ tr u hReach ⟨s0, .refl, MirMemFrame.refl s0.memory, h0, rfl⟩ with
    | ⟨hTr, s, hRs, hFs, hInv, hEq⟩ =>
      subst hEq
      rw [ITree.observe_cofix] at hObs
      have hObs' : (stepMirFn body s).map (ITree.cofix (stepMirState body)) =
          .ret out := hObs
      cases mirPccInv_step (retInv := retInv) hPhase hAll hInv with
      | inl hS =>
        match hS with
        | ⟨obs, s', hStep, _, _⟩ =>
          rw [hStep] at hObs'
          cases obs with
          | silent => nomatch hObs'
          | event _ => nomatch hObs'
      | inr hS =>
        match hS with
        | ⟨retVal', mem', _, hRet, hF', _, _⟩ =>
          rw [hRet] at hObs'
          injection hObs' with hOut
          exact ⟨retVal', mem', hOut.symm, hTr, hF'.trans hFs,
            s, mem', hRs, hRet⟩

/-- Every normal return observed in the interaction tree of an invariant
state is a `ReturnsFrom` return of the concrete transition system. -/
theorem returnsFrom_of_reachesRet {body : CapturedMir} {retInv : MirAbsSlot}
    {invs : List (Option MirAbsEnv)} {s0 : MachineState}
    {tr : List (Event MirEffect)} {retVal : Value} {mem : Memory}
    (hPhase : mirPhaseSupported body.phase = true)
    (hAll : checkAllBlocksCert body.localDecls retInv body.basicBlocks invs
      body.basicBlocks invs = true)
    (h0 : MirPccInv body invs s0)
    (hR : ReachesRet (mirTree body s0) tr (.normal (retVal, mem))) :
    ReturnsFrom body s0 retVal := by
  match reachesRet_normal_of_mirPccInv hPhase hAll h0 hR with
  | ⟨retVal', _, hEq, _, _, hRet⟩ =>
    injection hEq with hPair
    injection hPair with hV
    subst hV
    exact hRet

/-- From an invariant state that satisfies fault-tolerant `wpOutcome`
termination, `mirTree body s` stabilizes in finitely many `.tau` steps. -/
theorem stabilizes_of_mirPccInv {body : CapturedMir} {retInv : MirAbsSlot}
    {invs : List (Option MirAbsEnv)} {s : MachineState}
    (hPhase : mirPhaseSupported body.phase = true)
    (hAll : checkAllBlocksCert body.localDecls retInv body.basicBlocks invs
      body.basicBlocks invs = true)
    (hTerm : @Anneal.ParametricCore.wpOutcome _ _ _ (mirPccWpOps body)
      (fun _ => True) (fun _ => True) s)
    (hInv : MirPccInv body invs s) :
    ∃ u', TauStar (mirTree body s) u' ∧ ∀ w, u'.observe ≠ .tau w := by
  revert hInv
  refine Anneal.ParametricCore.wpOutcome_induction (ops := mirPccWpOps body)
    (C := fun s' => MirPccInv body invs s' →
      ∃ u', TauStar (mirTree body s') u' ∧ ∀ w, u'.observe ≠ .tau w)
    ?_ hTerm
  intro s' hStepC hInv'
  cases mirPccInv_step (retInv := retInv) hPhase hAll hInv' with
  | inl h =>
    match h with
    | ⟨obs, s'', hStep, _, hInv''⟩ =>
      cases obs with
      | silent =>
        have hC : MirPccInv body invs s'' →
            ∃ u', TauStar (mirTree body s'') u' ∧ ∀ w, u'.observe ≠ .tau w := by
          change (mirNodeOutcome (stepMirFn body s')).wp _ _ _ at hStepC
          rw [hStep] at hStepC
          exact hStepC
        match hC hInv'' with
        | ⟨u', hT', hNe'⟩ =>
          have hObs : (mirTree body s').observe = .tau (mirTree body s'') := by
            show (ITree.cofix (stepMirState body) (.running s')).observe = _
            rw [ITree.observe_cofix]
            change (stepMirFn body s').map (ITree.cofix (stepMirState body)) = _
            rw [hStep]
            rfl
          exact ⟨u', .step hObs hT', hNe'⟩
      | event _ =>
        refine ⟨mirTree body s', .refl _, fun w hw => ?_⟩
        rw [mirTree, ITree.observe_cofix] at hw
        have hw' : (stepMirFn body s').map (ITree.cofix (stepMirState body)) =
            .tau w := hw
        rw [hStep] at hw'
        nomatch hw'
  | inr h =>
    match h with
    | ⟨retVal, mem', _, hRet, _, _, _⟩ =>
      have hObs : (mirTree body s').observe = .ret (.normal (retVal, mem')) := by
        show (ITree.cofix (stepMirState body) (.running s')).observe = _
        rw [ITree.observe_cofix]
        change (stepMirFn body s').map (ITree.cofix (stepMirState body)) = _
        rw [hRet]
        rfl
      exact ⟨mirTree body s', .refl _, fun w hw => by rw [hObs] at hw; nomatch hw⟩

/-- Fault-tolerant `wpOutcome` termination from an invariant state implies
`Productive (mirTree body s0)` constructively. -/
theorem productive_of_mirPccInv {body : CapturedMir}
    {retInv : MirAbsSlot} {invs : List (Option MirAbsEnv)} {s0 : MachineState}
    (hPhase : mirPhaseSupported body.phase = true)
    (hAll : checkAllBlocksCert body.localDecls retInv body.basicBlocks invs
      body.basicBlocks invs = true)
    (hInv0 : MirPccInv body invs s0)
    (hTerm0 : @Anneal.ParametricCore.wpOutcome _ _ _ (mirPccWpOps body)
      (fun _ => True) (fun _ => True) s0) :
    Productive (mirTree body s0) := by
  have hQ : ∀ (t : ITree MirEffect MirOutcome) tr (u : ITree MirEffect MirOutcome),
      Reaches t tr u →
      (∃ s, MirPccInv body invs s ∧
        @Anneal.ParametricCore.wpOutcome _ _ _ (mirPccWpOps body)
          (fun _ => True) (fun _ => True) s ∧
        t = mirTree body s) →
      ∃ s, MirPccInv body invs s ∧
        @Anneal.ParametricCore.wpOutcome _ _ _ (mirPccWpOps body)
          (fun _ => True) (fun _ => True) s ∧
        u = mirTree body s := by
    intro t tr u hReach
    induction hReach with
    | refl => exact fun h => h
    | tau hObs _ ih =>
      intro h
      apply ih
      match h with
      | ⟨s, hInv, hTerm, hEq⟩ =>
        subst hEq
        have hUnf := (Anneal.ParametricCore.wpOutcome_unfold_iff
          (ops := mirPccWpOps body)).mp hTerm
        rw [mirTree, ITree.observe_cofix] at hObs
        have hObs' : (stepMirFn body s).map (ITree.cofix (stepMirState body)) =
            .tau _ := hObs
        cases mirPccInv_step (retInv := retInv) hPhase hAll hInv with
        | inl hS =>
          match hS with
          | ⟨obs, s', hStep, _, hInv'⟩ =>
            rw [hStep] at hObs'
            cases obs with
            | silent =>
              injection hObs' with hT
              have hTerm' : @Anneal.ParametricCore.wpOutcome _ _ _
                  (mirPccWpOps body) (fun _ => True) (fun _ => True) s' := by
                change (mirNodeOutcome (stepMirFn body s)).wp _ _ _ at hUnf
                rw [hStep] at hUnf
                exact hUnf
              exact ⟨s', hInv', hTerm', hT.symm⟩
            | event _ => nomatch hObs'
        | inr hS =>
          match hS with
          | ⟨_, _, _, hRet, _, _, _⟩ => rw [hRet] at hObs'; nomatch hObs'
    | vis hObs _ o _ ih =>
      intro h
      apply ih
      match h with
      | ⟨s, hInv, hTerm, hEq⟩ =>
        subst hEq
        have hUnf := (Anneal.ParametricCore.wpOutcome_unfold_iff
          (ops := mirPccWpOps body)).mp hTerm
        rw [mirTree, ITree.observe_cofix] at hObs
        have hObs' : (stepMirFn body s).map (ITree.cofix (stepMirState body)) =
            .vis _ _ := hObs
        cases mirPccInv_step (retInv := retInv) hPhase hAll hInv with
        | inl hS =>
          match hS with
          | ⟨obs, s', hStep, _, hInv'⟩ =>
            rw [hStep] at hObs'
            cases obs with
            | silent => nomatch hObs'
            | event _ =>
              cases hObs'
              have hTerm' : @Anneal.ParametricCore.wpOutcome _ _ _
                  (mirPccWpOps body) (fun _ => True) (fun _ => True) s' := by
                change (mirNodeOutcome (stepMirFn body s)).wp _ _ _ at hUnf
                rw [hStep] at hUnf
                exact hUnf
              exact ⟨s', hInv', hTerm', rfl⟩
        | inr hS =>
          match hS with
          | ⟨_, _, _, hRet, _, _, _⟩ => rw [hRet] at hObs'; nomatch hObs'
  intro tr u hR
  match hQ _ tr u hR ⟨s0, hInv0, hTerm0, rfl⟩ with
  | ⟨s', hInv', hTerm', hEq⟩ =>
    subst hEq
    exact stabilizes_of_mirPccInv hPhase hAll hTerm' hInv'

/-- A `checkMirCert` certificate over the abstract entry frame
`entryEnv c.body.localDecls argSlots` yields the trusted, audited
`VerificationResult c` for any `Claim` (with arbitrary `c.callees`) whose
precondition implies the argument slots and whose postcondition follows from
`retInv`. -/
theorem checkMirCert_verificationResult
    {c : Trusted.VerificationResult.Claim} {argSlots : List MirAbsSlot}
    {retInv : MirAbsSlot} {invs : List (Option MirAbsEnv)}
    (hChk : checkMirCert c.body (entryEnv c.body.localDecls argSlots) retInv
      invs = true)
    (hPre : ∀ args, c.pre args →
      entryArgsOk (c.body.localDecls.drop 1) argSlots args)
    (hPost : ∀ args retVal, c.pre args →
      (∃ d, get? c.body.localDecls 0 = some d ∧
        retInv.valDenote d.ty retVal) →
      c.post args retVal) :
    Trusted.VerificationResult.VerificationResult c := by
  have hPhase := bool_and_true_left hChk
  have hAll := bool_and_true_right (bool_and_true_right
    (bool_and_true_right (bool_and_true_right hChk)))
  refine ⟨?_⟩
  intro args hDef
  have hArgs := hPre args hDef
  have hRoot := initMachineStateWithCallees_root c.body args c.callees
  have hEntry : mirAbsEnvDenote c.body.localDecls
      (entryEnv c.body.localDecls argSlots)
      (Trusted.Rustc.V2026_06_01.MirSemantics.initMachineStateWithCallees
        c.body args c.callees).frame.locals := by
    rw [hRoot.2]
    exact entryEnv_sound hArgs
  have hSound := checkMirCert_sound hChk hRoot.1 hEntry
  refine ⟨hSound.2.2.1, ?_⟩
  intro outPair hOut _ retVal mem' hEq
  have hRR : ReachesRet
      (Trusted.VerificationResult.mirCallTreeWithCallees c.body args c.callees)
      outPair.1 (.normal (retVal, mem')) := by
    have h := hOut
    simp only [Trusted.VerificationResult.MirExecPartialWithCallees,
      ITree.toPartial] at h
    rw [hEq] at h
    exact h
  have hRet := returnsFrom_of_reachesRet (retInv := retInv) hPhase hAll
    (mirPccInv_start hChk hRoot.1 hEntry) hRR
  exact hPost args retVal hDef (hSound.2.1 retVal hRet)

/-- `checkMirCert_verificationResult` for a `verifyMirCutpoints`
certificate. -/
theorem verifyMirCutpoints_verificationResult
    {c : Trusted.VerificationResult.Claim} {argSlots : List MirAbsSlot}
    {retInv : MirAbsSlot} {cutpoints : List (Nat × MirAbsEnv)}
    {rpoOrder : List Nat}
    (hVer : verifyMirCutpoints c.body (entryEnv c.body.localDecls argSlots)
      retInv cutpoints rpoOrder = true)
    (hPre : ∀ args, c.pre args →
      entryArgsOk (c.body.localDecls.drop 1) argSlots args)
    (hPost : ∀ args retVal, c.pre args →
      (∃ d, get? c.body.localDecls 0 = some d ∧
        retInv.valDenote d.ty retVal) →
      c.post args retVal) :
    Trusted.VerificationResult.VerificationResult c :=
  checkMirCert_verificationResult (bool_and_true_right hVer) hPre hPost

/-- A `checkMirCert` certificate yields a trusted `StatefulVerificationResult`
for any `StatefulClaim` (with arbitrary `c.callees`) whose precondition
establishes a root-entry `Memory` (`callStack = []`, `activeCallee = none`,
`activeProtectors = []`) and the argument slots `argSlots`, providing both
`retInv.valDenote` and `MirMemFrame mem' mem` to `hPost`. -/
theorem checkMirCert_statefulVerificationResult
    {c : Trusted.VerificationResult.StatefulClaim} {argSlots : List MirAbsSlot}
    {retInv : MirAbsSlot} {invs : List (Option MirAbsEnv)}
    (hChk : checkMirCert c.body (entryEnv c.body.localDecls argSlots) retInv
      invs = true)
    (hPre : ∀ args mem, c.pre args mem →
      mem.callStack = [] ∧ mem.activeCallee = none ∧
      mem.activeProtectors = [] ∧
      entryArgsOk (c.body.localDecls.drop 1) argSlots args)
    (hPost : ∀ args mem retVal mem', c.pre args mem →
      MirMemFrame mem' mem →
      (∃ d, get? c.body.localDecls 0 = some d ∧
        retInv.valDenote d.ty retVal) →
      c.post args mem retVal mem') :
    Trusted.VerificationResult.StatefulVerificationResult c := by
  have hPhase := bool_and_true_left hChk
  have hAll := bool_and_true_right (bool_and_true_right
    (bool_and_true_right (bool_and_true_right hChk)))
  refine ⟨?_⟩
  intro args mem hDef
  have hP := hPre args mem hDef
  have hRoot := initMachineStateWithMemoryAndCallees_root c.body args mem
    c.callees hP.1 hP.2.1 hP.2.2.1
  have hEntry : mirAbsEnvDenote c.body.localDecls
      (entryEnv c.body.localDecls argSlots)
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
        c.body args mem c.callees).frame.locals := by
    rw [hRoot.2.1]
    exact entryEnv_sound hP.2.2.2
  have hSound := checkMirCert_sound hChk hRoot.1 hEntry
  refine ⟨hSound.2.2.1, ?_⟩
  intro outPair hOut _ retVal mem' hEq
  have hRR : ReachesRet
      (Trusted.VerificationResult.mirStatefulTreeWithCallees c.body args mem
        c.callees)
      outPair.1 (.normal (retVal, mem')) := by
    have h := hOut
    simp only [Trusted.VerificationResult.MirStatefulExecPartialWithCallees,
      ITree.toPartial] at h
    rw [hEq] at h
    exact h
  match reachesRet_normal_of_mirPccInv (retInv := retInv) hPhase hAll
      (mirPccInv_start hChk hRoot.1 hEntry) hRR with
  | ⟨retVal', mem'', hNorm, _, hFrame, hRet⟩ =>
    injection hNorm with hPair
    injection hPair with hV hM
    subst hV
    subst hM
    exact hPost args mem retVal mem' hDef (hFrame.trans hRoot.2.2)
      (hSound.2.1 retVal hRet)

/-- `checkMirCert_statefulVerificationResult` for a `verifyMirCutpoints`
certificate. -/
theorem verifyMirCutpoints_statefulVerificationResult
    {c : Trusted.VerificationResult.StatefulClaim} {argSlots : List MirAbsSlot}
    {retInv : MirAbsSlot} {cutpoints : List (Nat × MirAbsEnv)}
    {rpoOrder : List Nat}
    (hVer : verifyMirCutpoints c.body (entryEnv c.body.localDecls argSlots)
      retInv cutpoints rpoOrder = true)
    (hPre : ∀ args mem, c.pre args mem →
      mem.callStack = [] ∧ mem.activeCallee = none ∧
      mem.activeProtectors = [] ∧
      entryArgsOk (c.body.localDecls.drop 1) argSlots args)
    (hPost : ∀ args mem retVal mem', c.pre args mem →
      MirMemFrame mem' mem →
      (∃ d, get? c.body.localDecls 0 = some d ∧
        retInv.valDenote d.ty retVal) →
      c.post args mem retVal mem') :
    Trusted.VerificationResult.StatefulVerificationResult c :=
  checkMirCert_statefulVerificationResult (bool_and_true_right hVer) hPre hPost

/-- A `checkMirCert` certificate yields a trusted `TraceVerificationResult`
for any `TraceClaim` whose precondition establishes a root-entry `Memory` and
the argument slots, and whose postcondition follows from `TraceObsOnly tr`,
`MirMemFrame mem' mem`, and `retInv.valDenote`. Every reachable outcome is a
normal return along an observation-only trace (no panics, aborts, or external
calls). -/
theorem checkMirCert_traceVerificationResult
    {c : Trusted.VerificationResult.TraceClaim} {argSlots : List MirAbsSlot}
    {retInv : MirAbsSlot} {invs : List (Option MirAbsEnv)}
    (hChk : checkMirCert c.body (entryEnv c.body.localDecls argSlots) retInv
      invs = true)
    (hPre : ∀ args mem, c.pre args mem →
      mem.callStack = [] ∧ mem.activeCallee = none ∧
      mem.activeProtectors = [] ∧
      entryArgsOk (c.body.localDecls.drop 1) argSlots args)
    (hPost : ∀ args mem tr retVal mem', c.pre args mem →
      TraceObsOnly tr →
      MirMemFrame mem' mem →
      (∃ d, get? c.body.localDecls 0 = some d ∧
        retInv.valDenote d.ty retVal) →
      c.post args mem tr (.normal (retVal, mem'))) :
    Trusted.VerificationResult.TraceVerificationResult c := by
  have hPhase := bool_and_true_left hChk
  have hAll := bool_and_true_right (bool_and_true_right
    (bool_and_true_right (bool_and_true_right hChk)))
  refine ⟨?_⟩
  intro args mem hDef
  have hP := hPre args mem hDef
  have hRoot := initMachineStateWithMemoryAndCallees_root c.body args mem
    c.callees hP.1 hP.2.1 hP.2.2.1
  have hEntry : mirAbsEnvDenote c.body.localDecls
      (entryEnv c.body.localDecls argSlots)
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
        c.body args mem c.callees).frame.locals := by
    rw [hRoot.2.1]
    exact entryEnv_sound hP.2.2.2
  have hSound := checkMirCert_sound hChk hRoot.1 hEntry
  refine ⟨hSound.2.2.1, ?_⟩
  intro outPair hOut
  have hRR : ReachesRet
      (Trusted.VerificationResult.mirStatefulTreeWithCallees c.body args mem
        c.callees)
      outPair.1 outPair.2 := by
    have h := hOut
    simp only [Trusted.VerificationResult.MirStatefulExecPartialWithCallees,
      ITree.toPartial] at h
    exact h
  match reachesRet_normal_of_mirPccInv (retInv := retInv) hPhase hAll
      (mirPccInv_start hChk hRoot.1 hEntry) hRR with
  | ⟨retVal, mem', hEq, hTr, hFrame, hRet⟩ =>
    show c.post args mem outPair.1 outPair.2
    rw [hEq]
    exact hPost args mem outPair.1 retVal mem' hDef hTr
      (hFrame.trans hRoot.2.2) (hSound.2.1 retVal hRet)

/-- `checkMirCert_traceVerificationResult` for a `verifyMirCutpoints`
certificate. -/
theorem verifyMirCutpoints_traceVerificationResult
    {c : Trusted.VerificationResult.TraceClaim} {argSlots : List MirAbsSlot}
    {retInv : MirAbsSlot} {cutpoints : List (Nat × MirAbsEnv)}
    {rpoOrder : List Nat}
    (hVer : verifyMirCutpoints c.body (entryEnv c.body.localDecls argSlots)
      retInv cutpoints rpoOrder = true)
    (hPre : ∀ args mem, c.pre args mem →
      mem.callStack = [] ∧ mem.activeCallee = none ∧
      mem.activeProtectors = [] ∧
      entryArgsOk (c.body.localDecls.drop 1) argSlots args)
    (hPost : ∀ args mem tr retVal mem', c.pre args mem →
      TraceObsOnly tr →
      MirMemFrame mem' mem →
      (∃ d, get? c.body.localDecls 0 = some d ∧
        retInv.valDenote d.ty retVal) →
      c.post args mem tr (.normal (retVal, mem'))) :
    Trusted.VerificationResult.TraceVerificationResult c :=
  checkMirCert_traceVerificationResult (bool_and_true_right hVer) hPre hPost

end Anneal.AiPcc
