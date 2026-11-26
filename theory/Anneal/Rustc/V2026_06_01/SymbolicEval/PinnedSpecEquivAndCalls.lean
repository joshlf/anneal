import Anneal.Rustc.V2026_06_01.SymbolicEval.CoreEvalAndDischarge

namespace Anneal.Rustc.V2026_06_01.SymbolicEval

open Trusted.Refinement
open Trusted.Sequence
open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Refinement
open Anneal.Effect
open Anneal.ITree
open Anneal.EffectWP
open Anneal.ITreeWP
open Anneal.Scalars
open Anneal.Memory
open Anneal.UnsafeObligations
open Anneal.SepLogic
open Anneal.Rustc.V2026_06_01.Lower

/-!
Bounded UB refutation, call-free program equivalence, scoped-UB / modular call-contract
evaluators, and `O(1)` block / callee lookup context lemmas (sections 8, 9, 14, 15).
-/

/-! ## 8. Bounded UB Counterexample / Claim Refutation & Non-Vacuity Witnesses -/

/--
Computable bounded fault detector over `MirExecState`: returns `true` when
`body` reaches an immediate operational fault (`MirFailE`: `.ub` or
`.unsupported`) within `fuel` steps along `.tau` and `MirObsE` transitions.
-/
def reachesFaultExecBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    match stepMirStatePeriodic fuel' body st with
    | .ret _ => false
    | .tau st' => reachesFaultExecBounded fuel' body st'
    | .vis (.inl _) _ => true
    | .vis (.inr (.inl _)) k => reachesFaultExecBounded fuel' body (k PUnit.unit)
    | .vis (.inr (.inr _)) _ => false

/-- Computable bounded fault detector starting from `s : MachineState`. -/
def reachesFaultBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState) : Bool :=
  reachesFaultExecBounded fuel body (.running s)

private theorem treeSafe_of_observe_tau
    {t t' : ITree MirEffect MirOutcome}
    (h_obs : t.observe = .tau t')
    (h_safe : TreeSafe t) :
    TreeSafe t' :=
  fun tr u h_reach => h_safe tr u (Reaches.tau h_obs h_reach)

private theorem treeSafe_of_observe_obs
    {t : ITree MirEffect MirOutcome}
    {ev : ObsReq MirObs}
    {k : PUnit → ITree MirEffect MirOutcome}
    (h_obs : t.observe = .vis (.inr (.inl ev)) k)
    (h_safe : TreeSafe t) :
    TreeSafe (k PUnit.unit) :=
  fun tr u h_reach =>
    h_safe (⟨.inr (.inl ev), PUnit.unit⟩ :: tr) u
      (Reaches.vis h_obs False.elim PUnit.unit h_reach)

/--
Soundness of `reachesFaultExecBounded`: if `reachesFaultExecBounded fuel body st`
returns `true`, then `ITree.cofix (stepMirState body) st` is provably NOT
`TreeSafe`.
-/
theorem reachesFaultExecBounded_not_treeSafe
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (h_fault : reachesFaultExecBounded fuel body st = true) :
    ¬ TreeSafe (ITree.cofix (stepMirState body) st) := by
  induction fuel generalizing st with
  | zero => nomatch h_fault
  | succ fuel' ih =>
    intro h_safe
    unfold reachesFaultExecBounded at h_fault
    rw [stepMirStatePeriodic_eq] at h_fault
    have h_obs :
        (ITree.cofix (stepMirState body) st).observe =
          (stepMirState body st).map (ITree.cofix (stepMirState body)) :=
      ITree.observe_cofix (stepMirState body) st
    cases h_step : stepMirState body st with
    | ret _ =>
      simp only [h_step] at h_fault
      nomatch h_fault
    | tau st' =>
      simp only [h_step] at h_fault
      rw [h_step] at h_obs
      dsimp only [ITreeF.map] at h_obs
      exact ih st' h_fault (treeSafe_of_observe_tau h_obs h_safe)
    | vis i k =>
      rcases i with f | (e | c)
      · rw [h_step] at h_obs
        dsimp only [ITreeF.map] at h_obs
        exact h_safe [] (ITree.cofix (stepMirState body) st)
          (Reaches.refl _)
          ⟨_, .inl f, _, TauStar.refl _, h_obs, trivial⟩
      · simp only [h_step] at h_fault
        rw [h_step] at h_obs
        dsimp only [ITreeF.map] at h_obs
        exact ih (k PUnit.unit) h_fault (treeSafe_of_observe_obs h_obs h_safe)
      · simp only [h_step] at h_fault
        nomatch h_fault

/--
If `reachesFaultBounded fuel body s = true`, then `mirTree body s` violates
`TreeSafe` (exhibits reachable Undefined Behavior or an unsupported fault).
-/
theorem reachesFaultBounded_not_treeSafe
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (h_fault : reachesFaultBounded fuel body s = true) :
    ¬ TreeSafe (mirTree body s) :=
  reachesFaultExecBounded_not_treeSafe fuel body (.running s) h_fault

/--
Refute `MirContractHoldsWithSafetyAndCallees` by exhibiting a concrete input
`args` in `safetyPre` whose bounded execution hits a fault within `fuel` steps.
-/
theorem refuteMirContractWithSafetyAndCalleesByBoundedUB
    {body : CapturedMir}
    {callees : List CapturedMir}
    {safetyPre pre : List Value → Prop}
    {post : List Value → Value → Prop}
    (fuel : Nat)
    (args : List Value)
    (h_safe_pre : safetyPre args)
    (h_ub :
      reachesFaultBounded fuel body
        (initMachineStateWithCallees body args callees) = true := by
      rfl) :
    ¬ MirContractHoldsWithSafetyAndCallees body callees safetyPre pre post := by
  intro h_holds
  rcases h_holds args h_safe_pre with ⟨h_tree_safe, _⟩
  exact reachesFaultBounded_not_treeSafe fuel body
    (initMachineStateWithCallees body args callees) h_ub h_tree_safe

/--
Refute `MirContractHoldsWithSafety` by exhibiting a concrete input `args` in
`safetyPre` whose bounded execution hits a fault within `fuel` steps.
-/
theorem refuteMirContractWithSafetyByBoundedUB
    {body : CapturedMir}
    {safetyPre pre : List Value → Prop}
    {post : List Value → Value → Prop}
    (fuel : Nat)
    (args : List Value)
    (h_safe_pre : safetyPre args)
    (h_ub :
      reachesFaultBounded fuel body (initMachineState body args) = true := by
      rfl) :
    ¬ MirContractHoldsWithSafety body safetyPre pre post :=
  refuteMirContractWithSafetyAndCalleesByBoundedUB fuel args h_safe_pre h_ub

/--
Refute a stateless `c : Claim` (`¬ c.holds`) by exhibiting a concrete input
`args` satisfying `c.pre args` whose bounded execution hits a fault within
`fuel` steps.
-/
theorem refuteClaimByBoundedUB
    (c : Claim)
    (fuel : Nat)
    (args : List Value)
    (h_pre : c.pre args)
    (h_ub :
      reachesFaultBounded fuel c.body
        (initMachineStateWithCallees c.body args c.callees) = true := by
      rfl) :
    ¬ c.holds :=
  refuteMirContractWithSafetyAndCalleesByBoundedUB fuel args h_pre h_ub

/--
Refute a stateful `c : StatefulClaim` (`¬ c.holds`) by exhibiting a concrete
`(args, mem)` satisfying `c.pre args mem` whose bounded execution hits a fault
within `fuel` steps.
-/
theorem refuteStatefulClaimByBoundedUB
    (c : StatefulClaim)
    (fuel : Nat)
    (args : List Value)
    (mem : Memory)
    (h_pre : c.pre args mem)
    (h_ub :
      reachesFaultBounded fuel c.body
        (initMachineStateWithMemoryAndCallees c.body args mem c.callees) = true := by
      rfl) :
    ¬ c.holds := by
  intro h_holds
  rcases h_holds args mem h_pre with ⟨h_tree_safe, _⟩
  exact reachesFaultBounded_not_treeSafe fuel c.body
    (initMachineStateWithMemoryAndCallees c.body args mem c.callees) h_ub h_tree_safe

/--
Refute a total-correctness `c : TotalClaim` (`¬ c.holds`) by exhibiting a
concrete `(args, mem)` satisfying `c.pre args mem` whose bounded execution hits
a fault within `fuel` steps.
-/
theorem refuteTotalClaimByBoundedUB
    (c : TotalClaim)
    (fuel : Nat)
    (args : List Value)
    (mem : Memory)
    (h_pre : c.pre args mem)
    (h_ub :
      reachesFaultBounded fuel c.body
        (initMachineStateWithMemoryAndCallees c.body args mem c.callees) = true := by
      rfl) :
    ¬ c.holds := by
  intro h_holds
  have h_tree_safe := (h_holds args mem h_pre).1
  exact reachesFaultBounded_not_treeSafe fuel c.body
    (initMachineStateWithMemoryAndCallees c.body args mem c.callees) h_ub h_tree_safe

/-- Package a concrete argument list `args` as a non-vacuity witness (`∃ a, pre a`). -/
theorem proveNonVacuousPre
    {pre : List Value → Prop}
    (args : List Value)
    (h_pre : pre args) :
    ∃ a : List Value, pre a :=
  ⟨args, h_pre⟩

/--
Package a concrete `(args, mem)` pair as a stateful non-vacuity witness
(`∃ a m, pre a m`).
-/
theorem proveNonVacuousStatefulPre
    {pre : List Value → Memory → Prop}
    (args : List Value)
    (mem : Memory)
    (h_pre : pre args mem) :
    ∃ (a : List Value) (m : Memory), pre a m :=
  ⟨args, mem, h_pre⟩

/--
Prove non-vacuity of a generated `#[spec(requires: ...)]` precondition
(`length args = argCount ∧ MirBoolPredicateHolds reqBody args`) from a concrete
witness `args` checked by `rfl`.
-/
theorem proveNonVacuousBoolSpecPre
    (fuel argCount : Nat)
    (reqBody : CapturedMir)
    (args : List Value)
    (h_len : Trusted.Sequence.length args = argCount := by rfl)
    (h_req : checkMirBoolBounded fuel reqBody args = true := by rfl) :
    ∃ a : List Value,
      Trusted.Sequence.length a = argCount ∧ MirBoolPredicateHolds reqBody a :=
  ⟨args, h_len, mirBoolPredicateHolds_of_checkBounded fuel reqBody args h_req⟩

/-! ## 9. Single-Pass Call-Free Symbolic Program-to-Program Equivalence (`verifyStatefulEquivMirSym`) -/

/-- Direct `Prop`-valued node evaluator matching `mirNoCallWP` on `MirStepNode`. -/
@[reducible]
def evalNodeNoCallWP
    (cont : MirExecState → Prop) (post : MirOutcome → Prop) :
    MirStepNode → Prop
  | .ret out => post out
  | .tau st' => cont st'
  | .vis (.inl _) _ => False
  | .vis (.inr (.inl _)) k => cont (k PUnit.unit)
  | .vis (.inr (.inr _)) _ => False

theorem evalNodeNoCallWP_eq
    (cont : MirExecState → Prop) (post : MirOutcome → Prop)
    (node : MirStepNode) :
    evalNodeNoCallWP cont post node =
      match node with
      | .ret out => post out
      | .tau st' => cont st'
      | .vis i k => mirNoCallWP.wp i (fun o _ => cont (k o)) PUnit.unit := by
  cases node with
  | ret _ => rfl
  | tau _ => rfl
  | vis i _ =>
    rcases i with f | (e | c)
    · cases f; rfl
    · cases e; rfl
    · cases c; rfl

/-- Structural `Prop`-valued call-free evaluator over `SymTree MirStepNode`. -/
def evalSymNodeTreeNoCall
    (cont : MirExecState → Prop) (post : MirOutcome → Prop) :
    SymTree MirStepNode → Prop
  | .leaf (.ret out) => post out
  | .leaf (.tau st') => cont st'
  | .leaf (.vis (.inl _) _) => False
  | .leaf (.vis (.inr (.inl _)) k) => cont (k PUnit.unit)
  | .leaf (.vis (.inr (.inr _)) _) => False
  | .branch c t1 t2 =>
    match c with
    | true => evalSymNodeTreeNoCall cont post t1
    | false => evalSymNodeTreeNoCall cont post t2

theorem evalSymNodeTreeNoCall_eq
    (cont : MirExecState → Prop) (post : MirOutcome → Prop)
    (t : SymTree MirStepNode) :
    evalSymNodeTreeNoCall cont post t = evalNodeNoCallWP cont post t.eval := by
  induction t with
  | leaf node =>
    cases node with
    | ret _ => rfl
    | tau _ => rfl
    | vis i _ =>
      rcases i with f | (e | c) <;> rfl
  | branch c _ _ ih1 ih2 =>
    cases c
    · exact ih2
    · exact ih1

/-- Call-free single-pass fuel-bounded symbolic WP over `MirExecState`. -/
def wpMirExecNoCallSym
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop) : Prop :=
  match fuel with
  | 0 => False
  | fuel' + 1 =>
    evalSymNodeTreeNoCall
      (fun st' => wpMirExecNoCallSym fuel' body st' post)
      post
      (stepMirExecSymTree body st)

/-- Call-free single-pass fuel-bounded symbolic WP over `MachineState`. -/
def wpMirNoCallSym
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  wpMirExecNoCallSym fuel body (.running s) post

theorem wpMirExecNoCallSym_eq_wpCoalBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop) :
    wpMirExecNoCallSym fuel body st post =
      wpCoalBounded fuel mirNoCallWP (stepMirState body)
        (fun out _ => post out) st PUnit.unit := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel' ih =>
    unfold wpMirExecNoCallSym wpCoalBounded
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq]
    cases stepMirState body st with
    | ret _ => rfl
    | tau st' => exact ih st'
    | vis i k =>
      rcases i with f | (e | c)
      · cases f; rfl
      · cases e; exact ih (k PUnit.unit)
      · cases c; rfl

/-- Exact equality between single-pass `wpMirNoCallSym` and `Lower.wpMirNoCallBounded`. -/
theorem wpMirNoCallSym_eq_wpMirNoCallBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop) :
    wpMirNoCallSym fuel body s post = wpMirNoCallBounded fuel body s post :=
  wpMirExecNoCallSym_eq_wpCoalBounded fuel body (.running s) post

/--
Discharge a program-to-program behavioral equivalence and total-correctness
`StatefulEquivVerificationResult c` via single-pass symbolic evaluation of both
candidate `c.implBody` and reference `c.specBody` against `model`.
-/
theorem verifyStatefulEquivMirSym
    (c : StatefulEquivClaim)
    (implFuel specFuel : Nat)
    (model : List Value → Memory → Value × Memory)
    (h_impl :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        wpMirNoCallSym implFuel c.implBody
          (initMachineStateWithMemoryAndCallees c.implBody args mem c.implCallees)
          (fun out =>
            out = .normal (model args mem) ∧
            c.post args mem (model args mem).1 (model args mem).2))
    (h_spec :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        wpMirNoCallSym specFuel c.specBody
          (initMachineStateWithMemoryAndCallees c.specBody args mem c.specCallees)
          (fun out => out = .normal (model args mem))) :
    StatefulEquivVerificationResult c := by
  refine verifyStatefulEquivMirBounded c implFuel specFuel model
    (fun args mem h_pre => ?_)
    (fun args mem h_pre => ?_)
  · rw [← wpMirNoCallSym_eq_wpMirNoCallBounded]
    exact h_impl args mem h_pre
  · rw [← wpMirNoCallSym_eq_wpMirNoCallBounded]
    exact h_spec args mem h_pre


/-! ## 14. Single-Pass Symbolic Evaluators for Scoped UB Exceptions & Modular Call Contracts -/

/-- Direct `Prop`-valued node evaluator matching `mirUbWaivedWP` on `MirStepNode`. -/
@[reducible]
def evalNodeUbWaivedWP
    (cont : MirExecState → Prop) (post : MirOutcome → Prop) :
    MirStepNode → Prop
  | .ret out => post out
  | .tau st' => cont st'
  | .vis (.inl f) _ => isWaivedUbFailReq f
  | .vis (.inr (.inl _)) k => cont (k PUnit.unit)
  | .vis (.inr (.inr (.call _))) k => ∀ ans : MirCallAns, cont (k ans)

theorem evalNodeUbWaivedWP_eq
    (cont : MirExecState → Prop) (post : MirOutcome → Prop)
    (node : MirStepNode) :
    evalNodeUbWaivedWP cont post node =
      match node with
      | .ret out => post out
      | .tau st' => cont st'
      | .vis i k => mirUbWaivedWP.wp i (fun o _ => cont (k o)) PUnit.unit := by
  cases node with
  | ret _ => rfl
  | tau _ => rfl
  | vis i _ =>
    rcases i with f | (e | c)
    · cases f; rfl
    · cases e; rfl
    · cases c; rfl

/-- Structural `Prop`-valued UB-waived evaluator over `SymTree MirStepNode`. -/
def evalSymNodeTreeUbWaived
    (cont : MirExecState → Prop) (post : MirOutcome → Prop) :
    SymTree MirStepNode → Prop
  | .leaf (.ret out) => post out
  | .leaf (.tau st') => cont st'
  | .leaf (.vis (.inl f) _) => isWaivedUbFailReq f
  | .leaf (.vis (.inr (.inl _)) k) => cont (k PUnit.unit)
  | .leaf (.vis (.inr (.inr (.call _))) k) => ∀ ans : MirCallAns, cont (k ans)
  | .branch c t1 t2 =>
    match c with
    | true => evalSymNodeTreeUbWaived cont post t1
    | false => evalSymNodeTreeUbWaived cont post t2

theorem evalSymNodeTreeUbWaived_eq
    (cont : MirExecState → Prop) (post : MirOutcome → Prop)
    (t : SymTree MirStepNode) :
    evalSymNodeTreeUbWaived cont post t = evalNodeUbWaivedWP cont post t.eval := by
  induction t with
  | leaf node =>
    cases node with
    | ret _ => rfl
    | tau _ => rfl
    | vis i _ =>
      rcases i with f | (e | c)
      · cases f; rfl
      · cases e; rfl
      · cases c; rfl
  | branch c _ _ ih1 ih2 =>
    cases c
    · exact ih2
    · exact ih1

/-- Single-pass fuel-bounded UB-waived symbolic WP over `MirExecState`. -/
def wpMirExecUbWaivedSym
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop) : Prop :=
  match fuel with
  | 0 => False
  | fuel' + 1 =>
    evalSymNodeTreeUbWaived
      (fun st' => wpMirExecUbWaivedSym fuel' body st' post)
      post
      (stepMirExecSymTree body st)

/-- Single-pass fuel-bounded UB-waived symbolic WP over `MachineState`. -/
def wpMirUbWaivedSym
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  wpMirExecUbWaivedSym fuel body (.running s) post

theorem wpMirExecUbWaivedSym_eq_wpCoalBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop) :
    wpMirExecUbWaivedSym fuel body st post =
      wpCoalBounded fuel mirUbWaivedWP (stepMirState body)
        (fun out _ => post out) st PUnit.unit := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel' ih =>
    unfold wpMirExecUbWaivedSym wpCoalBounded
    rw [evalSymNodeTreeUbWaived_eq, stepMirExecSymTree_eval, evalNodeUbWaivedWP_eq]
    cases stepMirState body st with
    | ret _ => rfl
    | tau st' => exact ih st'
    | vis i k =>
      rcases i with f | (e | c)
      · cases f; rfl
      · cases e; exact ih (k PUnit.unit)
      · cases c
        dsimp only []
        congr 1
        funext ans u
        cases u
        exact ih (k ans)

/-- Exact equality between single-pass `wpMirUbWaivedSym` and `Lower.wpMirUbWaivedBounded`. -/
theorem wpMirUbWaivedSym_eq_wpMirUbWaivedBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop) :
    wpMirUbWaivedSym fuel body s post = wpMirUbWaivedBounded fuel body s post :=
  wpMirExecUbWaivedSym_eq_wpCoalBounded fuel body (.running s) post

/--
Discharge a `UbExceptionVerificationResult c` via single-pass symbolic evaluation
(`wpMirSym` on the strict safety domain `c.pre ∧ c.strictSafetyPre`, and
`wpMirUbWaivedSym` across `c.pre`).
-/
theorem verifyUbExceptionMirSym
    (c : UbExceptionClaim)
    (fuel : Nat)
    (h_strict :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        c.strictSafetyPre args mem →
        wpMirSym fuel c.body
          (initMachineStateWithMemoryAndCallees c.body args mem c.callees)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              c.post args mem retVal mem'))
    (h_waived :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        wpMirUbWaivedSym fuel c.body
          (initMachineStateWithMemoryAndCallees c.body args mem c.callees)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              c.post args mem retVal mem')) :
    UbExceptionVerificationResult c := by
  refine verifyUbExceptionMirBounded c fuel
    (fun args mem h_pre h_sp => ?_)
    (fun args mem h_pre => ?_)
  · rw [← wpMirSym_eq_wpMirBounded]
    exact h_strict args mem h_pre h_sp
  · rw [← wpMirUbWaivedSym_eq_wpMirUbWaivedBounded]
    exact h_waived args mem h_pre

/-- Direct `Prop`-valued node evaluator matching `mirModularWP contract.toCallContract`. -/
@[reducible]
def evalNodeModularWP
    (contract : MirCallContract)
    (cont : MirExecState → Prop) (post : MirOutcome → Prop) :
    MirStepNode → Prop
  | .ret out => post out
  | .tau st' => cont st'
  | .vis (.inl _) _ => False
  | .vis (.inr (.inl _)) k => cont (k PUnit.unit)
  | .vis (.inr (.inr (.call req))) k =>
    contract.pre req ∧
      ∀ ans : MirCallAns, contract.post req ans → cont (k ans)

theorem evalNodeModularWP_eq
    (contract : MirCallContract)
    (cont : MirExecState → Prop) (post : MirOutcome → Prop)
    (node : MirStepNode) :
    evalNodeModularWP contract cont post node =
      match node with
      | .ret out => post out
      | .tau st' => cont st'
      | .vis i k =>
        (mirModularWP contract.toCallContract).wp i
          (fun o _ => cont (k o)) PUnit.unit := by
  cases node with
  | ret _ => rfl
  | tau _ => rfl
  | vis i _ =>
    rcases i with f | (e | c)
    · cases f; rfl
    · cases e; rfl
    · cases c; rfl

/-- Structural `Prop`-valued modular call-contract evaluator over `SymTree MirStepNode`. -/
def evalSymNodeTreeModular
    (contract : MirCallContract)
    (cont : MirExecState → Prop) (post : MirOutcome → Prop) :
    SymTree MirStepNode → Prop
  | .leaf (.ret out) => post out
  | .leaf (.tau st') => cont st'
  | .leaf (.vis (.inl _) _) => False
  | .leaf (.vis (.inr (.inl _)) k) => cont (k PUnit.unit)
  | .leaf (.vis (.inr (.inr (.call req))) k) =>
    contract.pre req ∧
      ∀ ans : MirCallAns, contract.post req ans → cont (k ans)
  | .branch c t1 t2 =>
    match c with
    | true => evalSymNodeTreeModular contract cont post t1
    | false => evalSymNodeTreeModular contract cont post t2

theorem evalSymNodeTreeModular_eq
    (contract : MirCallContract)
    (cont : MirExecState → Prop) (post : MirOutcome → Prop)
    (t : SymTree MirStepNode) :
    evalSymNodeTreeModular contract cont post t =
      evalNodeModularWP contract cont post t.eval := by
  induction t with
  | leaf node =>
    cases node with
    | ret _ => rfl
    | tau _ => rfl
    | vis i _ =>
      rcases i with f | (e | c) <;> rfl
  | branch c _ _ ih1 ih2 =>
    cases c
    · exact ih2
    · exact ih1

/-- Single-pass fuel-bounded modular symbolic WP over `MirExecState`. -/
def wpMirExecModularSym
    (contract : MirCallContract)
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop) : Prop :=
  match fuel with
  | 0 => False
  | fuel' + 1 =>
    evalSymNodeTreeModular contract
      (fun st' => wpMirExecModularSym contract fuel' body st' post)
      post
      (stepMirExecSymTree body st)

/-- Single-pass fuel-bounded modular symbolic WP over `MachineState`. -/
def wpMirModularSym
    (contract : MirCallContract)
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  wpMirExecModularSym contract fuel body (.running s) post

theorem wpMirExecModularSym_eq_wpCoalBounded
    (contract : MirCallContract)
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop) :
    wpMirExecModularSym contract fuel body st post =
      wpCoalBounded fuel (mirModularWP contract.toCallContract)
        (stepMirState body) (fun out _ => post out) st PUnit.unit := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel' ih =>
    unfold wpMirExecModularSym wpCoalBounded
    rw [evalSymNodeTreeModular_eq, stepMirExecSymTree_eval, evalNodeModularWP_eq]
    cases stepMirState body st with
    | ret _ => rfl
    | tau st' => exact ih st'
    | vis i k =>
      rcases i with f | (e | c)
      · cases f; rfl
      · cases e; exact ih (k PUnit.unit)
      · rcases c with ⟨req⟩
        dsimp only []
        simp only [ih]

/--
Discharge a `ModularVerificationResult` with linked `callees` for `body` under
`contract.holdsOn` via single-pass symbolic evaluation (`wpMirModularSym`).
-/
theorem verifyModularContractWithCalleesMirSym
    (contract : MirCallContract)
    (body : CapturedMir)
    (callees : List CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        wpMirModularSym contract fuel body
          (initMachineStateWithMemoryAndCallees body args mem callees)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              post args mem retVal mem')) :
    ModularVerificationResult
      { body := body
        envAssumed := contract.holdsOn
        pre := pre
        post := post
        callees := callees } := by
  refine verifyModularContractWithCalleesMirBounded contract body callees pre post fuel
    (fun args mem h_pre => ?_)
  rw [wpMirModularBounded, ← wpMirExecModularSym_eq_wpCoalBounded]
  exact h_wp args mem h_pre

/--
Discharge a `ModularVerificationResult` for `body` under `contract.holdsOn` via
single-pass symbolic evaluation (`wpMirModularSym`).
-/
theorem verifyModularContractMirSym
    (contract : MirCallContract)
    (body : CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        wpMirModularSym contract fuel body
          (initMachineStateWithMemory body args mem)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              post args mem retVal mem')) :
    ModularVerificationResult
      { body := body
        envAssumed := contract.holdsOn
        pre := pre
        post := post } :=
  verifyModularContractWithCalleesMirSym contract body .nil pre post fuel h_wp

/--
Overwrite the call-frame components (`callees`, `callStack`, `activeCallee`,
and `activeProtectors`) of `after : Memory` with those of `before : Memory` so
post-call symbolic evaluation can reduce concrete caller frame fields by WHNF
even when `after` is a universally quantified symbolic memory.
-/
@[reducible, simp]
def restoreCallFrame (before after : Memory) : Memory :=
  { after with
    callees := before.callees
    callStack := before.callStack
    activeCallee := before.activeCallee
    activeProtectors := before.activeProtectors }

theorem restoreCallFrame_eq_of_callFramePreserved
    {before after : Memory}
    (h : callFramePreserved before after) :
    restoreCallFrame before after = after := by
  rcases h with ⟨h1, h2, h3, h4, _⟩
  cases after
  dsimp only [restoreCallFrame] at h1 h2 h3 h4 ⊢
  subst h1 h2 h3 h4
  rfl

/--
Project `restoreCallFrame before` across a `MirCallAns` response.
-/
@[reducible, simp]
def _root_.Trusted.Rustc.V2026_06_01.MirSemantics.MirCallAns.restoreFrame
    (before : Memory) : MirCallAns → MirCallAns
  | .returned retVal memAfter =>
    .returned retVal (restoreCallFrame before memAfter)
  | .panicked memAfter =>
    .panicked (restoreCallFrame before memAfter)
  | .aborted => .aborted

/--
Frame-preservation predicate on a `MirCallAns` response relative to `before`.
-/
@[reducible, simp]
def _root_.Trusted.Rustc.V2026_06_01.MirSemantics.MirCallAns.framePreserved
    (before : Memory) : MirCallAns → Prop
  | .returned _ memAfter => callFramePreserved before memAfter
  | .panicked memAfter => callFramePreserved before memAfter
  | .aborted => True

theorem _root_.Trusted.Rustc.V2026_06_01.MirSemantics.MirCallAns.restoreFrame_eq_of_framePreserved
    {before : Memory} {ans : MirCallAns}
    (h : ans.framePreserved before) :
    ans.restoreFrame before = ans := by
  cases ans with
  | returned retVal memAfter =>
    dsimp only [MirCallAns.restoreFrame, MirCallAns.framePreserved] at h ⊢
    rw [restoreCallFrame_eq_of_callFramePreserved h]
  | panicked memAfter =>
    dsimp only [MirCallAns.restoreFrame, MirCallAns.framePreserved] at h ⊢
    rw [restoreCallFrame_eq_of_callFramePreserved h]
  | aborted => rfl

/--
Every `externalSpecCallContract` guarantees `ans.framePreserved req.memory` on
every call answer `ans` permitted by its postcondition.
-/
theorem externalSpecCallContract_framePreserved
    (targetDefPath : DefPath)
    (sidecarBody : CapturedMir)
    (extraPre : List Value → Prop)
    (extraPost : List Value → Value → Prop) :
    ∀ (req : MirCallReq) (ans : MirCallAns),
      (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost).post req ans →
      ans.framePreserved req.memory := by
  intro req ans h_post
  cases ans with
  | returned retVal memAfter =>
    exact h_post.1
  | panicked memAfter =>
    dsimp only [externalSpecCallContract] at h_post
    cases h_u : sidecarTargetCanUnwind sidecarBody <;> rw [h_u] at h_post
    · exact False.elim h_post
    · exact h_post
  | aborted => trivial

/--
Frame-restoring node evaluator for modular call contracts: substitutes
`ans.restoreFrame req.memory` into the post-call continuation `k` so all
subsequent statements, blocks, inlined `callees`, and `return_` transitions in
the caller frame reduce by WHNF without manual `rw` on `memAfter`.
-/
@[reducible]
def evalNodeFrameModularWP
    (contract : MirCallContract)
    (cont : MirExecState → Prop) (post : MirOutcome → Prop) :
    MirStepNode → Prop
  | .ret out => post out
  | .tau st' => cont st'
  | .vis (.inl _) _ => False
  | .vis (.inr (.inl _)) k => cont (k PUnit.unit)
  | .vis (.inr (.inr (.call req))) k =>
    contract.pre req ∧
      ∀ ans : MirCallAns,
        contract.post req ans → cont (k (ans.restoreFrame req.memory))

/--
Structural `Prop`-valued frame-restoring modular evaluator over
`SymTree MirStepNode`.
-/
def evalSymNodeTreeFrameModular
    (contract : MirCallContract)
    (cont : MirExecState → Prop) (post : MirOutcome → Prop) :
    SymTree MirStepNode → Prop
  | .leaf (.ret out) => post out
  | .leaf (.tau st') => cont st'
  | .leaf (.vis (.inl _) _) => False
  | .leaf (.vis (.inr (.inl _)) k) => cont (k PUnit.unit)
  | .leaf (.vis (.inr (.inr (.call req))) k) =>
    contract.pre req ∧
      ∀ ans : MirCallAns,
        contract.post req ans → cont (k (ans.restoreFrame req.memory))
  | .branch c t1 t2 =>
    match c with
    | true => evalSymNodeTreeFrameModular contract cont post t1
    | false => evalSymNodeTreeFrameModular contract cont post t2

theorem evalSymNodeTreeFrameModular_eq
    (contract : MirCallContract)
    (cont : MirExecState → Prop) (post : MirOutcome → Prop)
    (t : SymTree MirStepNode) :
    evalSymNodeTreeFrameModular contract cont post t =
      evalNodeFrameModularWP contract cont post t.eval := by
  induction t with
  | leaf node =>
    cases node with
    | ret _ => rfl
    | tau _ => rfl
    | vis i _ =>
      rcases i with f | (e | c) <;> rfl
  | branch c _ _ ih1 ih2 =>
    cases c
    · exact ih2
    · exact ih1

/--
Frame-aware symbolic `evalTerminator` decision tree for the frame-restoring
modular WPs (`wpMirExecFrameModularSym` and
`wpMirExecFrameAndTraitsModularSym`): when
`s.memory.activeProtectors = .nil`, `.return_` skips
`hasFrameDeallocProtectorConflict` (which is `false` then, by
`hasFrameDeallocProtectorConflict_nil_activeProtectors`), so a return whose
borrow list is symbolic (such as the post-call
`invalidateDirectDestWriteBorrows` borrows) reduces by WHNF instead of blocking
on `List.rec` over `borrows`. Every other case is `evalTerminatorSymTree`, and
`evalTerminatorFrameSymTree_eval_eq` ties the `.nil`-protector branch to the
trusted `.return_` transition, so it cannot drift from `evalTerminator`.
-/
def evalTerminatorFrameSymTree
    (s : MachineState)
    (term : Terminator)
    (currentBody : CapturedMir) : SymTree MirStepNode :=
  match term.kind with
  | .return_ =>
    .leaf
      (match s.memory.activeProtectors with
       | .nil =>
         match get? s.frame.locals 0 with
         | .some (.init retVal) =>
           let depth := length s.memory.callStack
           let nLocals := length s.frame.locals
           let borrows₁ := disableFrameBorrows s.memory.borrows depth nLocals
           match s.memory.callStack with
           | .nil =>
             match valueContainsUninit retVal with
             | true => MirStepNode.fail .ub
             | false => MirStepNode.retNormal retVal { s.memory with borrows := borrows₁ }
           | caller :: restStack =>
             match caller.isDiverging with
             | true => MirStepNode.fail .ub
             | false =>
               match valueContainsUninit retVal with
               | true => MirStepNode.fail .ub
               | false =>
                 let restoredProtectors := restoreCallerProtectors caller
                 let callerMem : Memory := {
                   s.memory with
                   borrows := borrows₁
                   callStack := restStack
                   activeCallee := .some caller.callerBody
                   activeProtectors := restoredProtectors
                 }
                 match
                   writeReturnDestination
                     caller.frame.locals
                     callerMem
                     caller.destination
                     retVal
                     caller.callerBody.localDecls
                     caller.callerBody.layouts
                 with
                 | .ok updatedCallerLocals mem' =>
                   MirStepNode.step {
                     frame := {
                       caller.frame with
                       blockIdx := caller.returnTarget
                       stmtIdx := 0
                       locals := updatedCallerLocals
                     }
                     memory := mem'
                   }
                 | .ub => MirStepNode.fail .ub
                 | .unsupported => MirStepNode.unsupported
         | _ => MirStepNode.fail .ub
       | _ :: _ => evalTerminator s term (some currentBody))
  | _ => evalTerminatorSymTree s term currentBody

/--
`evalTerminatorFrameSymTree` and `evalTerminatorSymTree` denote the same
`MirStepNode`: the `.return_` shortcut is taken only when no protector is
active, where `hasFrameDeallocProtectorConflict` is `false`.
-/
theorem evalTerminatorFrameSymTree_eval_eq
    (s : MachineState)
    (term : Terminator)
    (currentBody : CapturedMir) :
    (evalTerminatorFrameSymTree s term currentBody).eval =
      (evalTerminatorSymTree s term currentBody).eval := by
  rcases term with ⟨kind, span⟩
  cases kind with
  | return_ =>
    dsimp only [evalTerminatorFrameSymTree, evalTerminatorSymTree, evalTerminator]
    cases s.memory.activeProtectors with
    | nil =>
      cases get? s.frame.locals 0 with
      | none => rfl
      | some slot =>
        cases slot with
        | uninit => rfl
        | dead => rfl
        | init retVal =>
          dsimp only []
          rw [hasFrameDeallocProtectorConflict_nil_activeProtectors]
          rfl
    | cons _ _ => rfl
  | _ => rfl

/--
One-step decision-tree symbolic MIR transition from `MachineState` for the
frame-restoring modular WPs: `stepMirSymTree` with terminators evaluated by
`evalTerminatorFrameSymTree`.
-/
def stepMirFrameSymTree
    (body : CapturedMir)
    (s : MachineState) : SymTree MirStepNode :=
  let currentBody := s.memory.activeCallee.getD body
  match currentBody.phase with
  | .other _ => .leaf MirStepNode.unsupported
  | _ =>
    match get? currentBody.basicBlocks s.frame.blockIdx with
    | none => .leaf (MirStepNode.fail .ub)
    | some bb =>
      match get? bb.statements s.frame.stmtIdx with
      | some stmt =>
        evalStmtSymTree s stmt currentBody.localDecls currentBody.layouts
      | none =>
        if s.frame.stmtIdx == length bb.statements then
          evalTerminatorFrameSymTree s bb.terminator currentBody
        else
          .leaf (MirStepNode.fail .ub)

/-- `stepMirFrameSymTree` and `stepMirSymTree` denote the same `MirStepNode`. -/
theorem stepMirFrameSymTree_eval_eq
    (body : CapturedMir)
    (s : MachineState) :
    (stepMirFrameSymTree body s).eval = (stepMirSymTree body s).eval := by
  dsimp only [stepMirFrameSymTree, stepMirSymTree]
  cases (s.memory.activeCallee.getD body).phase with
  | other _ => rfl
  | _ =>
    all_goals
      dsimp only
      cases get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx with
      | none => rfl
      | some bb =>
        dsimp only
        cases get? bb.statements s.frame.stmtIdx with
        | some _ => rfl
        | none =>
          dsimp only
          split
          · exact evalTerminatorFrameSymTree_eval_eq s bb.terminator _
          · rfl

/--
One-step decision-tree symbolic MIR transition from `MirExecState` for the
frame-restoring modular WPs (`stepMirExecSymTree` over `stepMirFrameSymTree`).
-/
def stepMirExecFrameSymTree
    (body : CapturedMir)
    (st : MirExecState) : SymTree MirStepNode :=
  match st with
  | .running s => stepMirFrameSymTree body s
  | .halted out => .leaf (.ret out)
  | .faulted fk => .leaf (MirStepNode.fail fk)

/--
`stepMirExecFrameSymTree` and `stepMirExecSymTree` denote the same
`MirStepNode`.
-/
theorem stepMirExecFrameSymTree_eval_eq
    (body : CapturedMir)
    (st : MirExecState) :
    (stepMirExecFrameSymTree body st).eval = (stepMirExecSymTree body st).eval := by
  cases st with
  | running s => exact stepMirFrameSymTree_eval_eq body s
  | halted _ => rfl
  | faulted _ => rfl

/--
`stepMirExecFrameSymTree` denotes the trusted one-step transition
`stepMirState`.
-/
theorem stepMirExecFrameSymTree_eval
    (body : CapturedMir)
    (st : MirExecState) :
    (stepMirExecFrameSymTree body st).eval = stepMirState body st := by
  rw [stepMirExecFrameSymTree_eval_eq, stepMirExecSymTree_eval]

/--
Single-pass fuel-bounded frame-restoring modular symbolic WP over `MirExecState`.
-/
def wpMirExecFrameModularSym
    (contract : MirCallContract)
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop) : Prop :=
  match fuel with
  | 0 => False
  | fuel' + 1 =>
    evalSymNodeTreeFrameModular contract
      (fun st' => wpMirExecFrameModularSym contract fuel' body st' post)
      post
      (stepMirExecFrameSymTree body st)

/--
Single-pass fuel-bounded frame-restoring modular symbolic WP over `MachineState`.
-/
def wpMirFrameModularSym
    (contract : MirCallContract)
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  wpMirExecFrameModularSym contract fuel body (.running s) post

/--
Soundness of `wpMirExecFrameModularSym`: for any `contract` whose postcondition
implies `ans.framePreserved req.memory`, `wpMirExecFrameModularSym` implies
`wpMirExecModularSym`.
-/
theorem wpMirExecModularSym_of_wpMirExecFrameModularSym
    (contract : MirCallContract)
    (h_frame :
      ∀ (req : MirCallReq) (ans : MirCallAns),
        contract.post req ans → ans.framePreserved req.memory)
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop)
    (h : wpMirExecFrameModularSym contract fuel body st post) :
    wpMirExecModularSym contract fuel body st post := by
  induction fuel generalizing st with
  | zero => exact False.elim h
  | succ fuel' ih =>
    unfold wpMirExecFrameModularSym at h
    unfold wpMirExecModularSym
    rw [evalSymNodeTreeFrameModular_eq, stepMirExecFrameSymTree_eval_eq] at h
    rw [evalSymNodeTreeModular_eq]
    cases h_ev : (stepMirExecSymTree body st).eval with
    | ret out =>
      rw [h_ev] at h
      exact h
    | tau st' =>
      rw [h_ev] at h
      exact ih st' h
    | vis i k =>
      rw [h_ev] at h
      rcases i with f | (e | c)
      · cases f; exact False.elim h
      · cases e; exact ih (k PUnit.unit) h
      · rcases c with ⟨req⟩
        dsimp only [evalNodeFrameModularWP, evalNodeModularWP] at h ⊢
        refine ⟨h.1, fun ans h_post => ?_⟩
        have h_eq : ans.restoreFrame req.memory = ans :=
          MirCallAns.restoreFrame_eq_of_framePreserved (h_frame req ans h_post)
        have h_cont := h.2 ans h_post
        rw [h_eq] at h_cont
        exact ih (k ans) h_cont

/--
Discharge a `ModularVerificationResult` with linked `callees` via frame-restoring
single-pass symbolic evaluation (`wpMirFrameModularSym`).
-/
theorem verifyModularFrameContractWithCalleesMirSym
    (contract : MirCallContract)
    (h_frame :
      ∀ (req : MirCallReq) (ans : MirCallAns),
        contract.post req ans → ans.framePreserved req.memory)
    (body : CapturedMir)
    (callees : List CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        wpMirFrameModularSym contract fuel body
          (initMachineStateWithMemoryAndCallees body args mem callees)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              post args mem retVal mem')) :
    ModularVerificationResult
      { body := body
        envAssumed := contract.holdsOn
        pre := pre
        post := post
        callees := callees } :=
  verifyModularContractWithCalleesMirSym contract body callees pre post fuel
    (fun args mem h_pre =>
      wpMirExecModularSym_of_wpMirExecFrameModularSym
        contract h_frame fuel body _ _ (h_wp args mem h_pre))

/--
Discharge a `ModularVerificationResult` without extra `callees` via
frame-restoring single-pass symbolic evaluation (`wpMirFrameModularSym`).
-/
theorem verifyModularFrameContractMirSym
    (contract : MirCallContract)
    (h_frame :
      ∀ (req : MirCallReq) (ans : MirCallAns),
        contract.post req ans → ans.framePreserved req.memory)
    (body : CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        wpMirFrameModularSym contract fuel body
          (initMachineStateWithMemory body args mem)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              post args mem retVal mem')) :
    ModularVerificationResult
      { body := body
        envAssumed := contract.holdsOn
        pre := pre
        post := post } :=
  verifyModularFrameContractWithCalleesMirSym
    contract h_frame body .nil pre post fuel h_wp

/--
Discharge a `ModularVerificationResult` with linked `callees` for a caller
invoking an `#[external_spec]` target (`externalSpecCallContract`), using
frame-restoring `wpMirFrameModularSym` so post-call execution steps by `whnf`
without manual frame-preservation rewrites.
-/
theorem verifyExternalSpecWithCalleesMirSym
    (targetDefPath : DefPath)
    (sidecarBody : CapturedMir)
    (extraPre : List Value → Prop := fun _ => True)
    (extraPost : List Value → Value → Prop := fun _ _ => True)
    (body : CapturedMir)
    (callees : List CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        wpMirFrameModularSym
          (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost)
          fuel
          body
          (initMachineStateWithMemoryAndCallees body args mem callees)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              post args mem retVal mem')) :
    ModularVerificationResult
      { body := body
        envAssumed :=
          (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost).holdsOn
        pre := pre
        post := post
        callees := callees } :=
  verifyModularFrameContractWithCalleesMirSym
    (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost)
    (externalSpecCallContract_framePreserved targetDefPath sidecarBody extraPre extraPost)
    body callees pre post fuel h_wp

/--
Discharge a `ModularVerificationResult` for a caller invoking an
`#[external_spec]` target (`externalSpecCallContract`), using frame-restoring
`wpMirFrameModularSym`.
-/
theorem verifyExternalSpecMirSym
    (targetDefPath : DefPath)
    (sidecarBody : CapturedMir)
    (extraPre : List Value → Prop := fun _ => True)
    (extraPost : List Value → Value → Prop := fun _ _ => True)
    (body : CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        wpMirFrameModularSym
          (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost)
          fuel
          body
          (initMachineStateWithMemory body args mem)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              post args mem retVal mem')) :
    ModularVerificationResult
      { body := body
        envAssumed :=
          (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost).holdsOn
        pre := pre
        post := post } :=
  verifyExternalSpecWithCalleesMirSym
    targetDefPath sidecarBody extraPre extraPost body .nil pre post fuel h_wp

/--
Every `MirCallContract` definitionally equal to an `externalSpecCallContract`
guarantees `ans.framePreserved req.memory` on every call answer `ans` permitted
by its postcondition.
-/
theorem externalSpecContract_framePreserved
    {targetDefPath : DefPath}
    {sidecarBody : CapturedMir}
    {extraPre : List Value → Prop}
    {extraPost : List Value → Value → Prop}
    (contract : MirCallContract)
    (h_eq :
      contract =
        externalSpecCallContract targetDefPath sidecarBody extraPre extraPost := by rfl) :
    ∀ (req : MirCallReq) (ans : MirCallAns),
      contract.post req ans → ans.framePreserved req.memory := by
  subst h_eq
  exact externalSpecCallContract_framePreserved targetDefPath sidecarBody extraPre extraPost

/--
Discharge a `ModularVerificationResult` with linked `callees` for a caller
invoking an `#[external_spec]` contract `contract` (definitionally equal to
`externalSpecCallContract targetDefPath sidecarBody extraPre extraPost`), using
frame-restoring `wpMirFrameModularSym` so post-call `resumeExternalCall` and
`evalTerminator` `.return_` transitions reduce by WHNF without manual
frame-preservation rewrites. The rely is the single `contract.holdsOn`; for a
caller of two `#[external_spec]` targets, use
`verifyExternalSpecContractPairWithCalleesMirSym`.
-/
theorem verifyExternalSpecContractWithCalleesMirSym
    {targetDefPath : DefPath}
    {sidecarBody : CapturedMir}
    {extraPre : List Value → Prop}
    {extraPost : List Value → Value → Prop}
    (contract : MirCallContract)
    (body : CapturedMir)
    (callees : List CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        wpMirFrameModularSym contract fuel body
          (initMachineStateWithMemoryAndCallees body args mem callees)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              post args mem retVal mem'))
    (h_eq :
      contract =
        externalSpecCallContract targetDefPath sidecarBody extraPre extraPost := by rfl) :
    ModularVerificationResult
      { body := body
        envAssumed := contract.holdsOn
        pre := pre
        post := post
        callees := callees } :=
  verifyModularFrameContractWithCalleesMirSym
    contract
    (externalSpecContract_framePreserved contract h_eq)
    body callees pre post fuel h_wp

/--
Discharge a `ModularVerificationResult` without extra `callees` for a caller
invoking an `#[external_spec]` contract `contract` (definitionally equal to
`externalSpecCallContract targetDefPath sidecarBody extraPre extraPost`), using
frame-restoring `wpMirFrameModularSym`.
-/
theorem verifyExternalSpecContractMirSym
    {targetDefPath : DefPath}
    {sidecarBody : CapturedMir}
    {extraPre : List Value → Prop}
    {extraPost : List Value → Value → Prop}
    (contract : MirCallContract)
    (body : CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        wpMirFrameModularSym contract fuel body
          (initMachineStateWithMemory body args mem)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              post args mem retVal mem'))
    (h_eq :
      contract =
        externalSpecCallContract targetDefPath sidecarBody extraPre extraPost := by rfl) :
    ModularVerificationResult
      { body := body
        envAssumed := contract.holdsOn
        pre := pre
        post := post } :=
  verifyExternalSpecContractWithCalleesMirSym
    contract body .nil pre post fuel h_wp h_eq

/--
`ModularVerificationResult` is antitone in the rely `envAssumed`: a result
proven under `env` also holds under every `env'` that implies `env`, because
`ModularClaim.holds` uses `envAssumed` only as a hypothesis. This restates a
result proven under one combined contract (such as `bothCallContracts`) against
the conjunction of per-callee contracts that `cargo anneal` renders in
`defaultModularSpec.envAssumed`.
-/
theorem modularVerificationResult_of_envAssumed_imp
    {body : CapturedMir}
    {callees : List CapturedMir}
    {pre : List Value → Memory → Prop}
    {post : List Value → Memory → Value → Memory → Prop}
    {env env' : ExternalCallHandler → Prop}
    (h_imp : ∀ h, env' h → env h)
    (h_res :
      ModularVerificationResult
        { body := body
          envAssumed := env
          pre := pre
          post := post
          callees := callees }) :
    ModularVerificationResult
      { body := body
        envAssumed := env'
        pre := pre
        post := post
        callees := callees } :=
  ⟨fun h h_env => h_res.proof h (h_imp h h_env)⟩

/--
Rely contract for a caller that assumes both `c₁` and `c₂`: a request is
permitted when either contract permits it, and an answer to a permitted request
satisfies the postcondition of every contract that permits the request. A
handler that implements both contracts implements this one
(`bothCallContracts_holdsOn`).

The postcondition repeats the disjunction of preconditions so that frame
preservation transfers from `c₁` and `c₂` (`bothCallContracts_framePreserved`):
without it, an answer to a request that neither contract permits would satisfy
the postcondition vacuously and constrain nothing.
-/
def bothCallContracts (c₁ c₂ : MirCallContract) : MirCallContract where
  pre req := c₁.pre req ∨ c₂.pre req
  post req ans :=
    (c₁.pre req ∨ c₂.pre req) ∧
      (c₁.pre req → c₁.post req ans) ∧
      (c₂.pre req → c₂.post req ans)

/--
A handler that implements both `c₁` and `c₂` implements
`bothCallContracts c₁ c₂`.
-/
theorem bothCallContracts_holdsOn
    {c₁ c₂ : MirCallContract} {h : ExternalCallHandler}
    (h₁ : c₁.holdsOn h) (h₂ : c₂.holdsOn h) :
    (bothCallContracts c₁ c₂).holdsOn h := by
  intro req h_pre
  refine ⟨?_, fun tr ans h_ret =>
    ⟨h_pre,
     fun hp₁ => (h₁ req hp₁).2 tr ans h_ret,
     fun hp₂ => (h₂ req hp₂).2 tr ans h_ret⟩⟩
  rcases h_pre with hp₁ | hp₂
  · exact (h₁ req hp₁).1
  · exact (h₂ req hp₂).1

/--
`bothCallContracts c₁ c₂` guarantees `ans.framePreserved req.memory` on every
answer that its postcondition permits when `c₁` and `c₂` both do.
-/
theorem bothCallContracts_framePreserved
    {c₁ c₂ : MirCallContract}
    (hf₁ :
      ∀ (req : MirCallReq) (ans : MirCallAns),
        c₁.post req ans → ans.framePreserved req.memory)
    (hf₂ :
      ∀ (req : MirCallReq) (ans : MirCallAns),
        c₂.post req ans → ans.framePreserved req.memory) :
    ∀ (req : MirCallReq) (ans : MirCallAns),
      (bothCallContracts c₁ c₂).post req ans → ans.framePreserved req.memory := by
  rintro req ans ⟨hp₁ | hp₂, hi₁, hi₂⟩
  · exact hf₁ req ans (hi₁ hp₁)
  · exact hf₂ req ans (hi₂ hp₂)

/--
Discharge a `ModularVerificationResult` with linked `callees` for a caller
invoking two `#[external_spec]` contracts `c₁` and `c₂` (each definitionally
equal to an `externalSpecCallContract`) under the rely
`fun h => c₁.holdsOn h ∧ c₂.holdsOn h`, which is the
`defaultModularSpec.envAssumed` that `cargo anneal` renders for a caller with
two abstracted callees.

Symbolic evaluation runs frame-restoring `wpMirFrameModularSym` under
`bothCallContracts c₁ c₂`. Each call site proves the precondition of its own
contract (`Or.inl` or `Or.inr`) and obtains that contract's postcondition by
applying the matching implication to the same precondition proof. For three or
more contracts, nest `bothCallContracts` in
`verifyModularFrameContractWithCalleesMirSym` and restate the result with
`modularVerificationResult_of_envAssumed_imp`.
-/
theorem verifyExternalSpecContractPairWithCalleesMirSym
    {targetDefPath₁ targetDefPath₂ : DefPath}
    {sidecarBody₁ sidecarBody₂ : CapturedMir}
    {extraPre₁ extraPre₂ : List Value → Prop}
    {extraPost₁ extraPost₂ : List Value → Value → Prop}
    (c₁ c₂ : MirCallContract)
    (body : CapturedMir)
    (callees : List CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        wpMirFrameModularSym (bothCallContracts c₁ c₂) fuel body
          (initMachineStateWithMemoryAndCallees body args mem callees)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              post args mem retVal mem'))
    (h_eq₁ :
      c₁ =
        externalSpecCallContract targetDefPath₁ sidecarBody₁ extraPre₁ extraPost₁ := by rfl)
    (h_eq₂ :
      c₂ =
        externalSpecCallContract targetDefPath₂ sidecarBody₂ extraPre₂ extraPost₂ := by rfl) :
    ModularVerificationResult
      { body := body
        envAssumed := fun h => c₁.holdsOn h ∧ c₂.holdsOn h
        pre := pre
        post := post
        callees := callees } :=
  modularVerificationResult_of_envAssumed_imp
    (fun _ h_env => bothCallContracts_holdsOn h_env.1 h_env.2)
    (verifyModularFrameContractWithCalleesMirSym
      (bothCallContracts c₁ c₂)
      (bothCallContracts_framePreserved
        (externalSpecContract_framePreserved c₁ h_eq₁)
        (externalSpecContract_framePreserved c₂ h_eq₂))
      body callees pre post fuel h_wp)

theorem restoreCallerMemoryFrame_eq_of_callFrameAndTraitsPreserved
    {before after : Memory}
    (h : callFrameAndTraitsPreserved before after) :
    restoreCallerMemoryFrame before after = after := by
  rcases h with ⟨⟨h1, h2, h3, h4, _⟩, h5⟩
  cases after
  dsimp only [restoreCallerMemoryFrame] at h1 h2 h3 h4 h5 ⊢
  subst h1 h2 h3 h4 h5
  rfl

/--
Project `restoreCallerMemoryFrame before` across a `MirCallAns` response,
restoring both the caller frame fields and `before.traitImpls` so post-call
polymorphic and trait-method calls in `before.callees` reduce by WHNF.
-/
@[reducible, simp]
def _root_.Trusted.Rustc.V2026_06_01.MirSemantics.MirCallAns.restoreFrameAndTraits
    (before : Memory) : MirCallAns → MirCallAns
  | .returned retVal memAfter =>
    .returned retVal (restoreCallerMemoryFrame before memAfter)
  | .panicked memAfter =>
    .panicked (restoreCallerMemoryFrame before memAfter)
  | .aborted => .aborted

/--
Frame-and-`traitImpls` preservation predicate on a `MirCallAns` response
relative to `before`.
-/
@[reducible, simp]
def _root_.Trusted.Rustc.V2026_06_01.MirSemantics.MirCallAns.frameAndTraitsPreserved
    (before : Memory) : MirCallAns → Prop
  | .returned _ memAfter => callFrameAndTraitsPreserved before memAfter
  | .panicked memAfter => callFrameAndTraitsPreserved before memAfter
  | .aborted => True

theorem _root_.Trusted.Rustc.V2026_06_01.MirSemantics.MirCallAns.restoreFrameAndTraits_eq_of_frameAndTraitsPreserved
    {before : Memory} {ans : MirCallAns}
    (h : ans.frameAndTraitsPreserved before) :
    ans.restoreFrameAndTraits before = ans := by
  cases ans with
  | returned retVal memAfter =>
    dsimp only [MirCallAns.restoreFrameAndTraits, MirCallAns.frameAndTraitsPreserved] at h ⊢
    rw [restoreCallerMemoryFrame_eq_of_callFrameAndTraitsPreserved h]
  | panicked memAfter =>
    dsimp only [MirCallAns.restoreFrameAndTraits, MirCallAns.frameAndTraitsPreserved] at h ⊢
    rw [restoreCallerMemoryFrame_eq_of_callFrameAndTraitsPreserved h]
  | aborted => rfl

/--
Every `polyExternalSpecCallContract` guarantees
`ans.frameAndTraitsPreserved req.memory` on every call answer `ans` permitted by
its postcondition.
-/
theorem polyExternalSpecCallContract_frameAndTraitsPreserved
    (targetDefPath : DefPath)
    (expectedTypeArgs : List RigidTy)
    (sidecarBody : CapturedMir)
    (extraPre : List Value → Prop)
    (extraPost : List Value → Value → Prop) :
    ∀ (req : MirCallReq) (ans : MirCallAns),
      (polyExternalSpecCallContract
        targetDefPath expectedTypeArgs sidecarBody extraPre extraPost).post req ans →
      ans.frameAndTraitsPreserved req.memory := by
  intro req ans h_post
  cases ans with
  | returned retVal memAfter =>
    exact h_post.1
  | panicked memAfter =>
    dsimp only [polyExternalSpecCallContract] at h_post
    cases h_u : sidecarTargetCanUnwind sidecarBody <;> rw [h_u] at h_post
    · exact False.elim h_post
    · exact h_post
  | aborted => trivial

/--
Frame-and-`traitImpls`-restoring node evaluator for modular call contracts:
substitutes `ans.restoreFrameAndTraits req.memory` into the post-call
continuation `k` so all subsequent statements, blocks, polymorphic/trait-method
inlined `callees`, and `return_` transitions in the caller frame reduce by WHNF.
-/
@[reducible]
def evalNodeFrameAndTraitsModularWP
    (contract : MirCallContract)
    (cont : MirExecState → Prop) (post : MirOutcome → Prop) :
    MirStepNode → Prop
  | .ret out => post out
  | .tau st' => cont st'
  | .vis (.inl _) _ => False
  | .vis (.inr (.inl _)) k => cont (k PUnit.unit)
  | .vis (.inr (.inr (.call req))) k =>
    contract.pre req ∧
      ∀ ans : MirCallAns,
        contract.post req ans → cont (k (ans.restoreFrameAndTraits req.memory))

/--
Structural `Prop`-valued frame-and-`traitImpls`-restoring modular evaluator over
`SymTree MirStepNode`.
-/
def evalSymNodeTreeFrameAndTraitsModular
    (contract : MirCallContract)
    (cont : MirExecState → Prop) (post : MirOutcome → Prop) :
    SymTree MirStepNode → Prop
  | .leaf (.ret out) => post out
  | .leaf (.tau st') => cont st'
  | .leaf (.vis (.inl _) _) => False
  | .leaf (.vis (.inr (.inl _)) k) => cont (k PUnit.unit)
  | .leaf (.vis (.inr (.inr (.call req))) k) =>
    contract.pre req ∧
      ∀ ans : MirCallAns,
        contract.post req ans → cont (k (ans.restoreFrameAndTraits req.memory))
  | .branch c t1 t2 =>
    match c with
    | true => evalSymNodeTreeFrameAndTraitsModular contract cont post t1
    | false => evalSymNodeTreeFrameAndTraitsModular contract cont post t2

theorem evalSymNodeTreeFrameAndTraitsModular_eq
    (contract : MirCallContract)
    (cont : MirExecState → Prop) (post : MirOutcome → Prop)
    (t : SymTree MirStepNode) :
    evalSymNodeTreeFrameAndTraitsModular contract cont post t =
      evalNodeFrameAndTraitsModularWP contract cont post t.eval := by
  induction t with
  | leaf node =>
    cases node with
    | ret _ => rfl
    | tau _ => rfl
    | vis i _ =>
      rcases i with f | (e | c) <;> rfl
  | branch c _ _ ih1 ih2 =>
    cases c
    · exact ih2
    · exact ih1

/--
Single-pass fuel-bounded frame-and-`traitImpls`-restoring modular symbolic WP
over `MirExecState`.
-/
def wpMirExecFrameAndTraitsModularSym
    (contract : MirCallContract)
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop) : Prop :=
  match fuel with
  | 0 => False
  | fuel' + 1 =>
    evalSymNodeTreeFrameAndTraitsModular contract
      (fun st' => wpMirExecFrameAndTraitsModularSym contract fuel' body st' post)
      post
      (stepMirExecFrameSymTree body st)

/--
Single-pass fuel-bounded frame-and-`traitImpls`-restoring modular symbolic WP
over `MachineState`.
-/
def wpMirFrameAndTraitsModularSym
    (contract : MirCallContract)
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  wpMirExecFrameAndTraitsModularSym contract fuel body (.running s) post

/--
Soundness of `wpMirExecFrameAndTraitsModularSym`: for any `contract` whose
postcondition implies `ans.frameAndTraitsPreserved req.memory`,
`wpMirExecFrameAndTraitsModularSym` implies `wpMirExecModularSym`.
-/
theorem wpMirExecModularSym_of_wpMirExecFrameAndTraitsModularSym
    (contract : MirCallContract)
    (h_frame :
      ∀ (req : MirCallReq) (ans : MirCallAns),
        contract.post req ans → ans.frameAndTraitsPreserved req.memory)
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop)
    (h : wpMirExecFrameAndTraitsModularSym contract fuel body st post) :
    wpMirExecModularSym contract fuel body st post := by
  induction fuel generalizing st with
  | zero => exact False.elim h
  | succ fuel' ih =>
    unfold wpMirExecFrameAndTraitsModularSym at h
    unfold wpMirExecModularSym
    rw [evalSymNodeTreeFrameAndTraitsModular_eq, stepMirExecFrameSymTree_eval_eq] at h
    rw [evalSymNodeTreeModular_eq]
    cases h_ev : (stepMirExecSymTree body st).eval with
    | ret out =>
      rw [h_ev] at h
      exact h
    | tau st' =>
      rw [h_ev] at h
      exact ih st' h
    | vis i k =>
      rw [h_ev] at h
      rcases i with f | (e | c)
      · cases f; exact False.elim h
      · cases e; exact ih (k PUnit.unit) h
      · rcases c with ⟨req⟩
        dsimp only [evalNodeFrameAndTraitsModularWP, evalNodeModularWP] at h ⊢
        refine ⟨h.1, fun ans h_post => ?_⟩
        have h_eq : ans.restoreFrameAndTraits req.memory = ans :=
          MirCallAns.restoreFrameAndTraits_eq_of_frameAndTraitsPreserved (h_frame req ans h_post)
        have h_cont := h.2 ans h_post
        rw [h_eq] at h_cont
        exact ih (k ans) h_cont

/--
Discharge a `ModularVerificationResult` with linked `callees` via
frame-and-`traitImpls`-restoring single-pass symbolic evaluation
(`wpMirFrameAndTraitsModularSym`).
-/
theorem verifyModularFrameAndTraitsContractWithCalleesMirSym
    (contract : MirCallContract)
    (h_frame :
      ∀ (req : MirCallReq) (ans : MirCallAns),
        contract.post req ans → ans.frameAndTraitsPreserved req.memory)
    (body : CapturedMir)
    (callees : List CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        wpMirFrameAndTraitsModularSym contract fuel body
          (initMachineStateWithMemoryAndCallees body args mem callees)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              post args mem retVal mem')) :
    ModularVerificationResult
      { body := body
        envAssumed := contract.holdsOn
        pre := pre
        post := post
        callees := callees } :=
  verifyModularContractWithCalleesMirSym contract body callees pre post fuel
    (fun args mem h_pre =>
      wpMirExecModularSym_of_wpMirExecFrameAndTraitsModularSym
        contract h_frame fuel body _ _ (h_wp args mem h_pre))

/--
Discharge a `ModularVerificationResult` without extra `callees` via
frame-and-`traitImpls`-restoring single-pass symbolic evaluation
(`wpMirFrameAndTraitsModularSym`).
-/
theorem verifyModularFrameAndTraitsContractMirSym
    (contract : MirCallContract)
    (h_frame :
      ∀ (req : MirCallReq) (ans : MirCallAns),
        contract.post req ans → ans.frameAndTraitsPreserved req.memory)
    (body : CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        wpMirFrameAndTraitsModularSym contract fuel body
          (initMachineStateWithMemory body args mem)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              post args mem retVal mem')) :
    ModularVerificationResult
      { body := body
        envAssumed := contract.holdsOn
        pre := pre
        post := post } :=
  verifyModularFrameAndTraitsContractWithCalleesMirSym
    contract h_frame body .nil pre post fuel h_wp

/--
Discharge a `ModularVerificationResult` with linked `callees` for a caller
invoking a polymorphic `#[external_spec]` target
(`polyExternalSpecCallContract`), using `wpMirFrameAndTraitsModularSym` so
subsequent polymorphic and trait-method calls in `callees` reduce by WHNF.
-/
theorem verifyPolyExternalSpecWithCalleesMirSym
    (targetDefPath : DefPath)
    (expectedTypeArgs : List RigidTy)
    (sidecarBody : CapturedMir)
    (extraPre : List Value → Prop := fun _ => True)
    (extraPost : List Value → Value → Prop := fun _ _ => True)
    (body : CapturedMir)
    (callees : List CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        wpMirFrameAndTraitsModularSym
          (polyExternalSpecCallContract
            targetDefPath expectedTypeArgs sidecarBody extraPre extraPost)
          fuel
          body
          (initMachineStateWithMemoryAndCallees body args mem callees)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              post args mem retVal mem')) :
    ModularVerificationResult
      { body := body
        envAssumed :=
          (polyExternalSpecCallContract
            targetDefPath expectedTypeArgs sidecarBody extraPre extraPost).holdsOn
        pre := pre
        post := post
        callees := callees } :=
  verifyModularFrameAndTraitsContractWithCalleesMirSym
    (polyExternalSpecCallContract
      targetDefPath expectedTypeArgs sidecarBody extraPre extraPost)
    (polyExternalSpecCallContract_frameAndTraitsPreserved
      targetDefPath expectedTypeArgs sidecarBody extraPre extraPost)
    body callees pre post fuel h_wp

/--
Discharge a `ModularVerificationResult` for a caller invoking a polymorphic
`#[external_spec]` target (`polyExternalSpecCallContract`), using
`wpMirFrameAndTraitsModularSym`.
-/
theorem verifyPolyExternalSpecMirSym
    (targetDefPath : DefPath)
    (expectedTypeArgs : List RigidTy)
    (sidecarBody : CapturedMir)
    (extraPre : List Value → Prop := fun _ => True)
    (extraPost : List Value → Value → Prop := fun _ _ => True)
    (body : CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        wpMirFrameAndTraitsModularSym
          (polyExternalSpecCallContract
            targetDefPath expectedTypeArgs sidecarBody extraPre extraPost)
          fuel
          body
          (initMachineStateWithMemory body args mem)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              post args mem retVal mem')) :
    ModularVerificationResult
      { body := body
        envAssumed :=
          (polyExternalSpecCallContract
            targetDefPath expectedTypeArgs sidecarBody extraPre extraPost).holdsOn
        pre := pre
        post := post } :=
  verifyPolyExternalSpecWithCalleesMirSym
    targetDefPath expectedTypeArgs sidecarBody extraPre extraPost body .nil pre post fuel h_wp

/--
Single-pass symbolic caller–callee linking theorem with `callerCallees` and
`calleeCallees` under `C.holdsOn` via `wpMirNoCallSym`.
-/
theorem linkVerifiedContractMirCalleeWithCalleesSym
    {C : MirCallContract}
    {callerBody : CapturedMir}
    {callerCallees : List CapturedMir}
    {pre : List Value → Memory → Prop}
    {post : List Value → Memory → Value → Memory → Prop}
    (h_caller :
      ModularVerificationResult
        { body := callerBody
          envAssumed := C.holdsOn
          pre := pre
          post := post
          callees := callerCallees })
    (calleeBody : CapturedMir)
    (calleeCallees : List CapturedMir)
    (calleeFuel : Nat)
    (fallback : ExternalCallHandler)
    (h_callee :
      ∀ req : MirCallReq,
        req.defPath = calleeBody.defPath →
        C.pre req →
        wpMirNoCallSym calleeFuel calleeBody
          (enterExternalCalleeState calleeBody req.args req.memory calleeCallees)
          (fun out => C.post req (outcomeToRestoredCallAns req.memory out)))
    (h_fallback :
      ∀ req : MirCallReq,
        req.defPath ≠ calleeBody.defPath →
        C.pre req →
        TreeSafe (fallback req) ∧
        ∀ tr ans, ReachesRet (fallback req) tr ans → C.post req ans) :
    (fun args mem =>
      (mirHandledTreeWithCallees callerBody args mem callerCallees
        (linkCalleeWithCalleesHandler calleeBody calleeCallees fallback)).toPartial) ≤
      MirClosedStatefulContractSpec pre pre post :=
  linkVerifiedContractMirCalleeWithCalleesBounded
    h_caller calleeBody calleeCallees calleeFuel fallback
    (fun req h_eq h_pre => by
      rw [← wpMirNoCallSym_eq_wpMirNoCallBounded]
      exact h_callee req h_eq h_pre)
    h_fallback

/--
Polymorphic single-pass symbolic caller–callee linking theorem with
`callerCallees` and `calleeCallees` under `C.holdsOn` via `wpMirNoCallSym`.
-/
theorem linkVerifiedPolyContractMirCalleeWithCalleesSym
    {C : MirCallContract}
    {callerBody : CapturedMir}
    {callerCallees : List CapturedMir}
    {pre : List Value → Memory → Prop}
    {post : List Value → Memory → Value → Memory → Prop}
    (h_caller :
      ModularVerificationResult
        { body := callerBody
          envAssumed := C.holdsOn
          pre := pre
          post := post
          callees := callerCallees })
    (calleeBody : CapturedMir)
    (calleeCallees : List CapturedMir)
    (calleeFuel : Nat)
    (fallback : ExternalCallHandler)
    (h_callee :
      ∀ req : MirCallReq,
        req.defPath = calleeBody.defPath →
        C.pre req →
        wpMirNoCallSym calleeFuel
          (instantiateCalleeForReq
            calleeBody callerBody.layouts req callerBody.traitImpls)
          (enterExternalCalleeState
            (instantiateCalleeForReq
              calleeBody callerBody.layouts req callerBody.traitImpls)
            req.args
            req.memory
            calleeCallees)
          (fun out => C.post req (outcomeToRestoredCallAns req.memory out)))
    (h_fallback :
      ∀ req : MirCallReq,
        req.defPath ≠ calleeBody.defPath →
        C.pre req →
        TreeSafe (fallback req) ∧
        ∀ tr ans, ReachesRet (fallback req) tr ans → C.post req ans) :
    (fun args mem =>
      (mirHandledTreeWithCallees callerBody args mem callerCallees
        (linkPolyCalleeWithCalleesHandler
          calleeBody callerBody.layouts calleeCallees fallback
          callerBody.traitImpls)).toPartial) ≤
      MirClosedStatefulContractSpec pre pre post :=
  linkVerifiedPolyContractMirCalleeWithCalleesBounded
    h_caller calleeBody calleeCallees calleeFuel fallback
    (fun req h_eq h_pre => by
      rw [← wpMirNoCallSym_eq_wpMirNoCallBounded]
      exact h_callee req h_eq h_pre)
    h_fallback

/--
Trait-method or polymorphic single-pass symbolic caller–callee linking theorem
with `callerCallees` and `calleeCallees` under `C.holdsOn` via `wpMirNoCallSym`.
-/
theorem linkVerifiedTraitOrPolyContractMirCalleeWithCalleesSym
    {C : MirCallContract}
    {callerBody : CapturedMir}
    {callerCallees : List CapturedMir}
    {pre : List Value → Memory → Prop}
    {post : List Value → Memory → Value → Memory → Prop}
    (h_caller :
      ModularVerificationResult
        { body := callerBody
          envAssumed := C.holdsOn
          pre := pre
          post := post
          callees := callerCallees })
    (calleeBody : CapturedMir)
    (calleeCallees : List CapturedMir)
    (calleeFuel : Nat)
    (fallback : ExternalCallHandler)
    (h_callee :
      ∀ (req : MirCallReq) (instBody : CapturedMir),
        lookupCallee
          [calleeBody]
          callerBody.layouts
          req.defPath
          req.typeArgs
          callerBody.traitImpls = .some instBody →
        C.pre req →
        wpMirNoCallSym calleeFuel instBody
          (enterExternalCalleeState instBody req.args req.memory calleeCallees)
          (fun out => C.post req (outcomeToRestoredCallAns req.memory out)))
    (h_fallback :
      ∀ req : MirCallReq,
        lookupCallee
          [calleeBody]
          callerBody.layouts
          req.defPath
          req.typeArgs
          callerBody.traitImpls = .none →
        C.pre req →
        TreeSafe (fallback req) ∧
        ∀ tr ans, ReachesRet (fallback req) tr ans → C.post req ans) :
    (fun args mem =>
      (mirHandledTreeWithCallees callerBody args mem callerCallees
        (linkTraitOrPolyCalleeWithCalleesHandler
          calleeBody callerBody.layouts calleeCallees fallback
          callerBody.traitImpls)).toPartial) ≤
      MirClosedStatefulContractSpec pre pre post :=
  linkVerifiedTraitOrPolyContractMirCalleeWithCalleesBounded
    h_caller calleeBody calleeCallees calleeFuel fallback
    (fun req instBody h_lk h_pre => by
      rw [← wpMirNoCallSym_eq_wpMirNoCallBounded]
      exact h_callee req instBody h_lk h_pre)
    h_fallback

/-! ## 15. `O(1)` Block & Callee Lookup Context Lemmas, Indirect `FnPtr` & Diverging Call Stepping, and Polymorphic Claim Combinators -/

/--
`O(1)` active callee normalization hypothesis (`ActiveCalleeCtx s body instBody`):
records that `s.memory.activeCallee.getD body = instBody`, avoiding repeated
evaluation and WHNF unrolling of `.getD` and `CapturedMir.instantiate` across steps.
-/
def ActiveCalleeCtx (s : MachineState) (body instBody : CapturedMir) : Prop :=
  s.memory.activeCallee.getD body = instBody

theorem ActiveCalleeCtx.init {body args callees} :
  ActiveCalleeCtx (initMachineStateWithCallees body args callees) body body := by unfold ActiveCalleeCtx; cases callees <;> rfl

theorem ActiveCalleeCtx.initMem {body args mem callees} :
  ActiveCalleeCtx (initMachineStateWithMemoryAndCallees body args mem callees) body (mem.activeCallee.getD body) := by unfold ActiveCalleeCtx; cases callees <;> rfl


theorem stepMirSymTree_of_activeCalleeCtx
    {body instBody : CapturedMir}
    {s : MachineState}
    (h_ctx : ActiveCalleeCtx s body instBody) :
    stepMirSymTree body s =
      match instBody.phase with
      | .other _ => .leaf MirStepNode.unsupported
      | _ =>
        match get? instBody.basicBlocks s.frame.blockIdx with
        | none => .leaf (MirStepNode.fail .ub)
        | some bb =>
          match get? bb.statements s.frame.stmtIdx with
          | some stmt =>
            evalStmtSymTree s stmt instBody.localDecls instBody.layouts
          | none =>
            if s.frame.stmtIdx == length bb.statements then
              evalTerminatorSymTree s bb.terminator instBody
            else .leaf (MirStepNode.fail .ub) := by
  unfold stepMirSymTree
  rw [h_ctx]
  rfl

/--
`O(1)` basic-block lookup context hypothesis (`BlockCtx body idx bb`): records
that basic block `idx` in `body.basicBlocks` is `bb`, avoiding repeated linear
list traversal of `body.basicBlocks` during symbolic execution.
-/
def BlockCtx (body : CapturedMir) (idx : BasicBlockIdx) (bb : BasicBlockData) : Prop :=
  get? body.basicBlocks idx = .some bb

theorem get?_basicBlocks_of_blockCtx
    {body : CapturedMir} {idx : BasicBlockIdx} {bb : BasicBlockData}
    (h : BlockCtx body idx bb) :
    get? body.basicBlocks idx = .some bb :=
  h

/--
`O(1)` callee lookup context hypothesis
(`CalleeCtx callees callerLayouts defPath typeArgs extraTraitImpls resolvedBody`):
records that `lookupCallee` resolves `(defPath, typeArgs)` to `resolvedBody`,
avoiding repeated `CapturedMir.instantiate` and `TraitImplEntry` searches across
multi-frame `s.memory.callees` steps.
-/
def CalleeCtx
    (callees : List CapturedMir)
    (callerLayouts : LayoutTable)
    (defPath : DefPath)
    (typeArgs : List RigidTy)
    (extraTraitImpls : List TraitImplEntry)
    (resolvedBody : CapturedMir) : Prop :=
  lookupCallee callees callerLayouts defPath typeArgs extraTraitImpls =
    .some resolvedBody

theorem lookupCallee_eq_of_calleeCtx
    {callees : List CapturedMir}
    {callerLayouts : LayoutTable}
    {defPath : DefPath}
    {typeArgs : List RigidTy}
    {extraTraitImpls : List TraitImplEntry}
    {resolvedBody : CapturedMir}
    (h : CalleeCtx callees callerLayouts defPath typeArgs extraTraitImpls resolvedBody) :
    lookupCallee callees callerLayouts defPath typeArgs extraTraitImpls =
      .some resolvedBody :=
  h

/--
Step `stepMirSymTree` in `O(1)` at statement `stmt` using a `BlockCtx`
hypothesis on the active body `s.memory.activeCallee.getD body`.
-/
theorem stepMirSymTree_stmt_of_blockCtx
    (body instBody : CapturedMir)
    (s : MachineState)
    (bb : BasicBlockData)
    (stmt : Statement)
    (h_ctx : ActiveCalleeCtx s body instBody)
    (h_phase : instBody.phase = .runtimeOptimized)
    (h_bb : BlockCtx instBody s.frame.blockIdx bb)
    (h_stmt : get? bb.statements s.frame.stmtIdx = .some stmt) :
    stepMirSymTree body s =
      evalStmtSymTree s stmt instBody.localDecls instBody.layouts := by
  unfold stepMirSymTree
  rw [h_ctx]
  dsimp only []
  rw [h_phase, h_bb]
  dsimp only []
  rw [h_stmt]

/--
Step `stepMirSymTree` in `O(1)` at terminator `bb.terminator` using a `BlockCtx`
hypothesis when `s.frame.stmtIdx == length bb.statements`.
-/
theorem stepMirSymTree_term_of_blockCtx
    (body instBody : CapturedMir)
    (s : MachineState)
    (bb : BasicBlockData)
    (h_ctx : ActiveCalleeCtx s body instBody)
    (h_phase : instBody.phase = .runtimeOptimized)
    (h_bb : BlockCtx instBody s.frame.blockIdx bb)
    (h_none : get? bb.statements s.frame.stmtIdx = .none)
    (h_end : (s.frame.stmtIdx == length bb.statements) = true) :
    stepMirSymTree body s =
      evalTerminatorSymTree s bb.terminator instBody := by
  unfold stepMirSymTree
  rw [h_ctx]
  dsimp only []
  rw [h_phase, h_bb]
  dsimp only []
  rw [h_none, h_end]
  rfl

/--
Direct `resolveCallTarget` reduction for a constant `RigidTy.fnDef defPath typeArgs`
operand.
-/
@[simp]
theorem resolveCallTarget_const_fnDef
    (s : MachineState)
    (defPath : DefPath)
    (typeArgs : List RigidTy)
    (layoutIdx : LayoutIdx)
    (val : ConstValue)
    (argCount : Nat)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable) :
    resolveCallTarget
      s
      (.constant { ty := { kind := .fnDef defPath typeArgs, layoutIdx := layoutIdx }, val := val })
      argCount
      bodyLocalDecls
      bodyLayouts =
    .ok
      { defPath := defPath
        typeArgs := typeArgs
        fnSig := .none
        isIndirect := false }
      s.frame.locals :=
  rfl

/--
Indirect `resolveCallTarget` reduction for a runtime `Value.ptr` function pointer
registered in `s.memory.fnPtrs`.
-/
theorem resolveCallTarget_indirect_fnPtr
    (s : MachineState)
    (func : Operand)
    (argCount : Nat)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (ptrVal : ProvenancePtr)
    (localsAfterFunc : List LocalSlot)
    (fnEntry : FnPtrEntry)
    (h_nonConst : extractCalleeDefPath? func = .none)
    (h_eval :
      evalOperandWithBodyCast
        s.frame.locals
        func
        s.memory.borrows
        s.memory.globals
        bodyLayouts
        s.memory.callerLocals
        bodyLocalDecls
        s.memory.callStack =
      .ok (.ptr ptrVal 8) localsAfterFunc)
    (h_off : ptrVal.offsetBytes = 0)
    (h_noBorrow : lookupBorrow s.memory.borrows ptrVal.tag = .none)
    (h_fnPtr : lookupFnPtr s.memory.fnPtrs ptrVal.allocId = .some fnEntry)
    (h_compat :
      fnEntryCompatibleWithCallSite
        fnEntry
        argCount
        (operandTy bodyLocalDecls bodyLayouts func) = true) :
    resolveCallTarget s func argCount bodyLocalDecls bodyLayouts =
      .ok
        { defPath := fnEntry.defPath
          typeArgs := fnEntry.typeArgs
          fnSig := fnEntry.fnSig
          isIndirect := true }
        localsAfterFunc := by
  unfold resolveCallTarget
  rw [h_nonConst, h_eval]
  dsimp only []
  rw [h_off, h_noBorrow]
  dsimp only [Nat.beq, Bool.and]
  rw [h_fnPtr]
  dsimp only []
  rw [h_compat]

/--
`evalTerminatorSymTree` for an unreachable basic-block terminator
(`TerminatorKind.unreachable`) reduces directly to `.leaf (MirStepNode.fail .ub)`.
-/
@[simp]
theorem evalTerminatorSymTree_unreachable_eq_ub
    (s : MachineState)
    (span : String)
    (currentBody : CapturedMir) :
    evalTerminatorSymTree s { kind := .unreachable, span := span } currentBody =
      .leaf (MirStepNode.fail .ub) :=
  rfl

theorem evalTerminatorSymTree_call_extCall
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String)
    (currentBody : CapturedMir)
    (resolvedTarget : ResolvedCallTarget)
    (localsAfterFunc : List LocalSlot)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (h_res :
      resolveCallTarget
        s func (length argOps) currentBody.localDecls currentBody.layouts =
      .ok resolvedTarget localsAfterFunc)
    (h_args :
      evalOperandsWithBodyCast
        localsAfterFunc
        argOps
        s.memory.borrows
        s.memory.globals
        currentBody.layouts
        s.memory.callerLocals
        currentBody.localDecls
        s.memory.callStack =
      .ok argVals locals')
    (h_indirect : resolvedTarget.isIndirect = false)
    (h_callee :
      lookupCallee
        s.memory.callees
        currentBody.layouts
        resolvedTarget.defPath
        resolvedTarget.typeArgs
        s.memory.traitImpls = .none)
    (_h_unreachable : isUnreachableCallTarget resolvedTarget.defPath = false)
    (_h_abort : isAbortingPanicDefPath resolvedTarget.defPath = false)
    (_h_unwind : isUnwindingPanicDefPath resolvedTarget.defPath = false)
    (h_exactDiv : isDirectExactDivTarget resolvedTarget = false)
    (h_intrinsic :
      evalDirectRustIntrinsic?
        s (some currentBody) resolvedTarget currentBody.localDecls
        currentBody.layouts argOps argVals locals' destination targetBb unwind = .none) :
    evalTerminatorSymTree
      s
      { kind := .call func argOps destination (.some targetBb) unwind, span := span }
      currentBody =
    .leaf
      (MirStepNode.extCall
        { defPath := resolvedTarget.defPath, typeArgs := resolvedTarget.typeArgs, args := argVals, memory := s.memory }
        (resumeExternalCall s locals' destination targetBb unwind)) := by
  dsimp only [evalTerminatorSymTree, evalTerminator, evalCallTerminator, bodyLocalDeclsOf]
  rw [h_res]
  dsimp only []
  rw [h_args]
  dsimp only []
  rw [h_callee]
  dsimp only []
  rw [h_exactDiv, h_indirect, h_intrinsic]
/--
`evalTerminatorSymTree` for a normal inlined call (`target = .some targetBb`)
resolved via `CalleeCtx`.
-/
theorem evalTerminatorSymTree_call_inlined_of_calleeCtx
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String)
    (currentBody : CapturedMir)
    (resolvedTarget : ResolvedCallTarget)
    (localsAfterFunc : List LocalSlot)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (calleeBody : CapturedMir)
    (h_res :
      resolveCallTarget
        s func (length argOps) currentBody.localDecls currentBody.layouts =
      .ok resolvedTarget localsAfterFunc)
    (h_args :
      evalOperandsWithBodyCast
        localsAfterFunc
        argOps
        s.memory.borrows
        s.memory.globals
        currentBody.layouts
        s.memory.callerLocals
        currentBody.localDecls
        s.memory.callStack =
      .ok argVals locals')
    (h_callee :
      CalleeCtx
        s.memory.callees
        currentBody.layouts
        resolvedTarget.defPath
        resolvedTarget.typeArgs
        s.memory.traitImpls
        calleeBody)
    (h_compat :
      checkCalleeTargetCompatible resolvedTarget calleeBody (length argVals) = true) :
    evalTerminatorSymTree
      s
      { kind := .call func argOps destination (.some targetBb) unwind, span := span }
      currentBody =
    .leaf
      (MirStepNode.step
        (pushCalleeFrame
          s currentBody locals' destination targetBb calleeBody argVals unwind)) := by
  dsimp only [evalTerminatorSymTree, evalTerminator, evalCallTerminator, bodyLocalDeclsOf]
  rw [h_res]
  dsimp only []
  rw [h_args]
  dsimp only []
  rw [lookupCallee_eq_of_calleeCtx h_callee]
  dsimp only []
  rw [h_compat]

/--
`evalTerminatorSymTree` for an inlined tail call (`TerminatorKind.tailCall`)
resolved via `CalleeCtx`.

A tail call deallocates the caller's frame before entering the callee: the
semantics faults with `.ub` when an active protector still guards a tag that
targets a local of the returning frame (`hasFrameDeallocProtectorConflict`; that
branch is `evalTerminatorSymTree_tailCall_deallocConflict`), and otherwise
disables every borrow of the returning frame (`disableFrameBorrows`) in the
memory handed to the callee. `h_noDeallocConflict` selects the non-faulting
branch, which the semantics requires for the step to succeed.
-/
theorem evalTerminatorSymTree_tailCall_inlined_of_calleeCtx
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (span : String)
    (currentBody : CapturedMir)
    (resolvedTarget : ResolvedCallTarget)
    (localsAfterFunc : List LocalSlot)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (calleeBody : CapturedMir)
    (h_res :
      resolveCallTarget
        s func (length argOps) currentBody.localDecls currentBody.layouts =
      .ok resolvedTarget localsAfterFunc)
    (h_args :
      evalOperandsWithBodyCast
        localsAfterFunc
        argOps
        s.memory.borrows
        s.memory.globals
        currentBody.layouts
        s.memory.callerLocals
        currentBody.localDecls
        s.memory.callStack =
      .ok argVals locals')
    (h_callee :
      CalleeCtx
        s.memory.callees
        currentBody.layouts
        resolvedTarget.defPath
        resolvedTarget.typeArgs
        s.memory.traitImpls
        calleeBody)
    (h_compat :
      checkCalleeTargetCompatible resolvedTarget calleeBody (length argVals) = true)
    (h_noDeallocConflict :
      hasFrameDeallocProtectorConflict
        s.memory.borrows
        s.memory.activeProtectors
        (length s.memory.callStack)
        (length s.frame.locals) = false) :
    evalTerminatorSymTree
      s
      { kind := .tailCall func argOps, span := span }
      currentBody =
    .leaf
      (MirStepNode.step
        (enterTailCalleeFrame
          (tailCalleeEntryMemory
            s.memory.callStack
            { s.memory with
              borrows :=
                disableFrameBorrows
                  s.memory.borrows
                  (length s.memory.callStack)
                  (length s.frame.locals) }
            (length s.frame.locals)
            (length (initLocals calleeBody argVals)))
          calleeBody argVals)) := by
  dsimp only [evalTerminatorSymTree, evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf]
  rw [h_res]
  dsimp only []
  rw [h_args]
  dsimp only []
  rw [h_noDeallocConflict]
  dsimp only []
  rw [lookupCallee_eq_of_calleeCtx h_callee]
  dsimp only []
  rw [h_compat]

/--
`evalTerminatorSymTree` for a tail call (`TerminatorKind.tailCall`) whose
returning frame still has a local guarded by an active protector
(`hasFrameDeallocProtectorConflict`): deallocating the frame is undefined
behavior, so the step faults with `.ub` whatever the callee resolves to.
-/
theorem evalTerminatorSymTree_tailCall_deallocConflict
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (span : String)
    (currentBody : CapturedMir)
    (resolvedTarget : ResolvedCallTarget)
    (localsAfterFunc : List LocalSlot)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (h_res :
      resolveCallTarget
        s func (length argOps) currentBody.localDecls currentBody.layouts =
      .ok resolvedTarget localsAfterFunc)
    (h_args :
      evalOperandsWithBodyCast
        localsAfterFunc
        argOps
        s.memory.borrows
        s.memory.globals
        currentBody.layouts
        s.memory.callerLocals
        currentBody.localDecls
        s.memory.callStack =
      .ok argVals locals')
    (h_deallocConflict :
      hasFrameDeallocProtectorConflict
        s.memory.borrows
        s.memory.activeProtectors
        (length s.memory.callStack)
        (length s.frame.locals) = true) :
    evalTerminatorSymTree
      s
      { kind := .tailCall func argOps, span := span }
      currentBody =
    .leaf (MirStepNode.fail .ub) := by
  dsimp only [evalTerminatorSymTree, evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf]
  rw [h_res]
  dsimp only []
  rw [h_args]
  dsimp only []
  rw [h_deallocConflict]

/--
`evalTerminatorSymTree` for a diverging (`target = .none`) inlined call resolved
via `CalleeCtx`.
-/
theorem evalTerminatorSymTree_diverging_call_inlined_of_calleeCtx
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (destination : Place)
    (unwind : UnwindAction)
    (span : String)
    (currentBody : CapturedMir)
    (resolvedTarget : ResolvedCallTarget)
    (localsAfterFunc : List LocalSlot)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (calleeBody : CapturedMir)
    (h_res :
      resolveCallTarget
        s func (length argOps) currentBody.localDecls currentBody.layouts =
      .ok resolvedTarget localsAfterFunc)
    (h_args :
      evalOperandsWithBodyCast
        localsAfterFunc
        argOps
        s.memory.borrows
        s.memory.globals
        currentBody.layouts
        s.memory.callerLocals
        currentBody.localDecls
        s.memory.callStack =
      .ok argVals locals')
    (h_callee :
      CalleeCtx
        s.memory.callees
        currentBody.layouts
        resolvedTarget.defPath
        resolvedTarget.typeArgs
        s.memory.traitImpls
        calleeBody)
    (h_compat :
      checkCalleeTargetCompatible resolvedTarget calleeBody (length argVals) = true) :
    evalTerminatorSymTree
      s
      { kind := .call func argOps destination .none unwind, span := span }
      currentBody =
    .leaf
      (MirStepNode.step
        (pushDivergingCalleeFrame
          s currentBody locals' destination unwind calleeBody argVals)) := by
  dsimp only [evalTerminatorSymTree, evalTerminator, evalCallTerminator, bodyLocalDeclsOf]
  rw [h_res]
  dsimp only []
  rw [h_args]
  dsimp only []
  rw [lookupCallee_eq_of_calleeCtx h_callee]
  dsimp only []
  rw [h_compat]

/--
`evalTerminatorSymTree` for an unresolved diverging (`target = .none`) external
call (neither an unreachable hint nor a built-in panic entrypoint) reduces to
`MirStepNode.extCall` with `resumeExternalDivergingCall`.
-/
theorem evalTerminatorSymTree_diverging_extCall
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (destination : Place)
    (unwind : UnwindAction)
    (span : String)
    (currentBody : CapturedMir)
    (resolvedTarget : ResolvedCallTarget)
    (localsAfterFunc : List LocalSlot)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (h_res :
      resolveCallTarget
        s func (length argOps) currentBody.localDecls currentBody.layouts =
      .ok resolvedTarget localsAfterFunc)
    (h_args :
      evalOperandsWithBodyCast
        localsAfterFunc
        argOps
        s.memory.borrows
        s.memory.globals
        currentBody.layouts
        s.memory.callerLocals
        currentBody.localDecls
        s.memory.callStack =
      .ok argVals locals')
    (h_none :
      lookupCallee
        s.memory.callees
        currentBody.layouts
        resolvedTarget.defPath
        resolvedTarget.typeArgs
        s.memory.traitImpls =
      .none)
    (h_not_unreach : isUnreachableCallTarget resolvedTarget.defPath = false)
    (h_not_abort : isAbortingPanicDefPath resolvedTarget.defPath = false)
    (h_not_unwind : isUnwindingPanicDefPath resolvedTarget.defPath = false) :
    evalTerminatorSymTree
      s
      { kind := .call func argOps destination .none unwind, span := span }
      currentBody =
    .leaf
      (MirStepNode.extCall
        { defPath := resolvedTarget.defPath
          typeArgs := resolvedTarget.typeArgs
          args := argVals
          memory := s.memory }
        (resumeExternalDivergingCall s locals' unwind)) := by
  dsimp only [evalTerminatorSymTree, evalTerminator, evalCallTerminator, bodyLocalDeclsOf]
  rw [h_res]
  dsimp only []
  rw [h_args]
  dsimp only []
  rw [h_none]
  dsimp only []
  cases resolvedTarget.isIndirect
  · dsimp only []
    rw [h_not_unreach, h_not_abort, h_not_unwind]
  · rfl

/--
Verify a universally quantified polymorphic stateless claim
`∀ typeArgs, typeArgs.length = polyBody.typeParamCount → VerificationResult (claimFor typeArgs)`
via single-pass symbolic evaluation (`verifyMirSafeSym`).
-/
theorem verifyPolyMirSym
    (polyBody : CapturedMir)
    (claimFor : TypeSubst → Claim)
    (fuel : Nat)
    (h_wp :
      ∀ (typeArgs : TypeSubst),
        typeArgs.length = polyBody.typeParamCount →
        ∀ (args : List Value) (s : MachineState),
          s = initMachineStateWithCallees
            (claimFor typeArgs).body args (claimFor typeArgs).callees →
          (claimFor typeArgs).pre args →
          ActiveCalleeCtx s (claimFor typeArgs).body (claimFor typeArgs).body →
          wpMirSym fuel (claimFor typeArgs).body s
            (mirSafePost (fun retVal _ => (claimFor typeArgs).post args retVal))) :
    ∀ (typeArgs : TypeSubst),
      typeArgs.length = polyBody.typeParamCount →
      VerificationResult (claimFor typeArgs) :=
  fun typeArgs h_len => verifyMirSafeSym (claimFor typeArgs) fuel (fun args h_pre => h_wp typeArgs h_len args _ rfl h_pre ActiveCalleeCtx.init)

/--
Panic-forbidding variant of `verifyPolyMirSym` (`mirNormalPost`).
-/
theorem verifyPolyMirNoPanicSym
    (polyBody : CapturedMir)
    (claimFor : TypeSubst → Claim)
    (fuel : Nat)
    (h_wp :
      ∀ (typeArgs : TypeSubst),
        typeArgs.length = polyBody.typeParamCount →
        ∀ (args : List Value) (s : MachineState),
          s = initMachineStateWithCallees
            (claimFor typeArgs).body args (claimFor typeArgs).callees →
          (claimFor typeArgs).pre args →
          ActiveCalleeCtx s (claimFor typeArgs).body (claimFor typeArgs).body →
          wpMirSym fuel (claimFor typeArgs).body s
            (mirNormalPost (fun retVal _ => (claimFor typeArgs).post args retVal))) :
    ∀ (typeArgs : TypeSubst),
      typeArgs.length = polyBody.typeParamCount →
      VerificationResult (claimFor typeArgs) :=
  fun typeArgs h_len => verifyMirNoPanicSym (claimFor typeArgs) fuel (fun args h_pre => h_wp typeArgs h_len args _ rfl h_pre ActiveCalleeCtx.init)

/--
Verify a universally quantified polymorphic stateful claim
`∀ typeArgs, typeArgs.length = polyBody.typeParamCount → StatefulVerificationResult (statefulClaimFor typeArgs)`
via single-pass symbolic evaluation (`verifyStatefulMirSym`).
-/
theorem verifyPolyStatefulMirSym
    (polyBody : CapturedMir)
    (statefulClaimFor : TypeSubst → StatefulClaim)
    (fuel : Nat)
    (h_wp :
      ∀ (typeArgs : TypeSubst),
        typeArgs.length = polyBody.typeParamCount →
        ∀ (args : List Value) (mem : Memory) (s : MachineState),
          s = initMachineStateWithMemoryAndCallees
            (statefulClaimFor typeArgs).body args mem (statefulClaimFor typeArgs).callees →
          (statefulClaimFor typeArgs).pre args mem →
          ActiveCalleeCtx s (statefulClaimFor typeArgs).body (mem.activeCallee.getD (statefulClaimFor typeArgs).body) →
          wpMirSym fuel (statefulClaimFor typeArgs).body s
            (mirSafePost ((statefulClaimFor typeArgs).post args mem))) :
    ∀ (typeArgs : TypeSubst),
      typeArgs.length = polyBody.typeParamCount →
      StatefulVerificationResult (statefulClaimFor typeArgs) :=
  fun typeArgs h_len =>
    verifyStatefulMirSym (statefulClaimFor typeArgs) fuel (fun args mem h_pre => h_wp typeArgs h_len args mem _ rfl h_pre ActiveCalleeCtx.initMem)

/--
Panic-forbidding variant of `verifyPolyStatefulMirSym` (`mirNormalPost`).
-/
theorem verifyPolyStatefulMirNoPanicSym
    (polyBody : CapturedMir)
    (statefulClaimFor : TypeSubst → StatefulClaim)
    (fuel : Nat)
    (h_wp :
      ∀ (typeArgs : TypeSubst),
        typeArgs.length = polyBody.typeParamCount →
        ∀ (args : List Value) (mem : Memory) (s : MachineState),
          s = initMachineStateWithMemoryAndCallees
            (statefulClaimFor typeArgs).body args mem (statefulClaimFor typeArgs).callees →
          (statefulClaimFor typeArgs).pre args mem →
          ActiveCalleeCtx s (statefulClaimFor typeArgs).body (mem.activeCallee.getD (statefulClaimFor typeArgs).body) →
          wpMirSym fuel (statefulClaimFor typeArgs).body s
            (mirNormalPost ((statefulClaimFor typeArgs).post args mem))) :
    ∀ (typeArgs : TypeSubst),
      typeArgs.length = polyBody.typeParamCount →
      StatefulVerificationResult (statefulClaimFor typeArgs) :=
  fun typeArgs h_len =>
    verifyStatefulMirNoPanicSym (statefulClaimFor typeArgs) fuel (fun args mem h_pre => h_wp typeArgs h_len args mem _ rfl h_pre ActiveCalleeCtx.initMem)

/--
Verify a universally quantified polymorphic total-correctness claim
`∀ typeArgs, typeArgs.length = polyBody.typeParamCount → TotalVerificationResult (totalClaimFor typeArgs)`
via single-pass symbolic evaluation (`verifyTotalMirSym`).
-/
theorem verifyPolyTotalMirSym
    (polyBody : CapturedMir)
    (totalClaimFor : TypeSubst → TotalClaim)
    (fuel : Nat)
    (h_wp :
      ∀ (typeArgs : TypeSubst),
        typeArgs.length = polyBody.typeParamCount →
        ∀ (args : List Value) (mem : Memory) (s : MachineState),
          s = initMachineStateWithMemoryAndCallees
            (totalClaimFor typeArgs).body args mem (totalClaimFor typeArgs).callees →
          (totalClaimFor typeArgs).pre args mem →
          ActiveCalleeCtx s (totalClaimFor typeArgs).body (mem.activeCallee.getD (totalClaimFor typeArgs).body) →
          wpMirSym fuel (totalClaimFor typeArgs).body s
            (mirNormalPost ((totalClaimFor typeArgs).post args mem))) :
    ∀ (typeArgs : TypeSubst),
      typeArgs.length = polyBody.typeParamCount →
      TotalVerificationResult (totalClaimFor typeArgs) :=
  fun typeArgs h_len =>
    verifyTotalMirSym (totalClaimFor typeArgs) fuel (fun args mem h_pre => h_wp typeArgs h_len args mem _ rfl h_pre ActiveCalleeCtx.initMem)

/--
Verify a universally quantified polymorphic scoped UB-exception claim
`∀ typeArgs, typeArgs.length = polyBody.typeParamCount → UbExceptionVerificationResult (ubExceptionClaimFor typeArgs)`
via single-pass symbolic evaluation (`verifyUbExceptionMirSym`).
-/
theorem verifyPolyUbExceptionMirSym
    (polyBody : CapturedMir)
    (ubExceptionClaimFor : TypeSubst → UbExceptionClaim)
    (fuel : Nat)
    (h_strict :
      ∀ (typeArgs : TypeSubst),
        typeArgs.length = polyBody.typeParamCount →
        ∀ (args : List Value) (mem : Memory) (s : MachineState),
          s = initMachineStateWithMemoryAndCallees
            (ubExceptionClaimFor typeArgs).body args mem (ubExceptionClaimFor typeArgs).callees →
          (ubExceptionClaimFor typeArgs).pre args mem →
          (ubExceptionClaimFor typeArgs).strictSafetyPre args mem →
          ActiveCalleeCtx s (ubExceptionClaimFor typeArgs).body (mem.activeCallee.getD (ubExceptionClaimFor typeArgs).body) →
          wpMirSym fuel (ubExceptionClaimFor typeArgs).body s
            (fun out =>
              ∀ retVal mem', out = .normal (retVal, mem') →
                (ubExceptionClaimFor typeArgs).post args mem retVal mem'))
    (h_waived :
      ∀ (typeArgs : TypeSubst),
        typeArgs.length = polyBody.typeParamCount →
        ∀ (args : List Value) (mem : Memory),
          (ubExceptionClaimFor typeArgs).pre args mem →
          wpMirUbWaivedSym fuel (ubExceptionClaimFor typeArgs).body
            (initMachineStateWithMemoryAndCallees
              (ubExceptionClaimFor typeArgs).body
              args
              mem
              (ubExceptionClaimFor typeArgs).callees)
            (fun out =>
              ∀ retVal mem', out = .normal (retVal, mem') →
                (ubExceptionClaimFor typeArgs).post args mem retVal mem')) :
    ∀ (typeArgs : TypeSubst),
      typeArgs.length = polyBody.typeParamCount →
      UbExceptionVerificationResult (ubExceptionClaimFor typeArgs) :=
  fun typeArgs h_len =>
    verifyUbExceptionMirSym
      (ubExceptionClaimFor typeArgs)
      fuel
      (fun args mem h_pre h_strict_pre => h_strict typeArgs h_len args mem _ rfl h_pre h_strict_pre ActiveCalleeCtx.initMem)
      (h_waived typeArgs h_len)

/--
Verify a universally quantified polymorphic modular claim
`∀ typeArgs, typeArgs.length = polyBody.typeParamCount → ModularVerificationResult ...`
via single-pass symbolic evaluation (`verifyModularContractWithCalleesMirSym`).
-/
theorem verifyPolyModularMirSym
    (polyBody : CapturedMir)
    (contractFor : TypeSubst → MirCallContract)
    (bodyFor : TypeSubst → CapturedMir)
    (calleesFor : TypeSubst → List CapturedMir)
    (preFor : TypeSubst → List Value → Memory → Prop)
    (postFor : TypeSubst → List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (typeArgs : TypeSubst),
        typeArgs.length = polyBody.typeParamCount →
        ∀ (args : List Value) (mem : Memory),
          preFor typeArgs args mem →
          wpMirModularSym (contractFor typeArgs) fuel (bodyFor typeArgs)
            (initMachineStateWithMemoryAndCallees
              (bodyFor typeArgs) args mem (calleesFor typeArgs))
            (fun out =>
              ∀ retVal mem', out = .normal (retVal, mem') →
                postFor typeArgs args mem retVal mem')) :
    ∀ (typeArgs : TypeSubst),
      typeArgs.length = polyBody.typeParamCount →
      ModularVerificationResult
        { body := bodyFor typeArgs
          envAssumed := (contractFor typeArgs).holdsOn
          pre := preFor typeArgs
          post := postFor typeArgs
          callees := calleesFor typeArgs } :=
  fun typeArgs h_len =>
    verifyModularContractWithCalleesMirSym
      (contractFor typeArgs)
      (bodyFor typeArgs)
      (calleesFor typeArgs)
      (preFor typeArgs)
      (postFor typeArgs)
      fuel
      (h_wp typeArgs h_len)

/--
Verify a universally quantified polymorphic modular claim via
frame-and-`traitImpls`-restoring symbolic evaluation
(`wpMirFrameAndTraitsModularSym`).
-/
theorem verifyPolyModularFrameAndTraitsMirSym
    (polyBody : CapturedMir)
    (contractFor : TypeSubst → MirCallContract)
    (h_frame :
      ∀ (typeArgs : TypeSubst),
        typeArgs.length = polyBody.typeParamCount →
        ∀ (req : MirCallReq) (ans : MirCallAns),
          (contractFor typeArgs).post req ans →
          ans.frameAndTraitsPreserved req.memory)
    (bodyFor : TypeSubst → CapturedMir)
    (calleesFor : TypeSubst → List CapturedMir)
    (preFor : TypeSubst → List Value → Memory → Prop)
    (postFor : TypeSubst → List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (typeArgs : TypeSubst),
        typeArgs.length = polyBody.typeParamCount →
        ∀ (args : List Value) (mem : Memory),
          preFor typeArgs args mem →
          wpMirFrameAndTraitsModularSym (contractFor typeArgs) fuel (bodyFor typeArgs)
            (initMachineStateWithMemoryAndCallees
              (bodyFor typeArgs) args mem (calleesFor typeArgs))
            (fun out =>
              ∀ retVal mem', out = .normal (retVal, mem') →
                postFor typeArgs args mem retVal mem')) :
    ∀ (typeArgs : TypeSubst),
      typeArgs.length = polyBody.typeParamCount →
      ModularVerificationResult
        { body := bodyFor typeArgs
          envAssumed := (contractFor typeArgs).holdsOn
          pre := preFor typeArgs
          post := postFor typeArgs
          callees := calleesFor typeArgs } :=
  fun typeArgs h_len =>
    verifyModularFrameAndTraitsContractWithCalleesMirSym
      (contractFor typeArgs)
      (h_frame typeArgs h_len)
      (bodyFor typeArgs)
      (calleesFor typeArgs)
      (preFor typeArgs)
      (postFor typeArgs)
      fuel
      (h_wp typeArgs h_len)

end Anneal.Rustc.V2026_06_01.SymbolicEval
