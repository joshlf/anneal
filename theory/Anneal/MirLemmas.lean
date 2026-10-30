-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted
import Anneal.Refinement
import Anneal.StepResult

/-!
# MIR Meta-Theorems, `id` Verification Lemmas, and Adequacy Canaries

This module proves the structural non-vacuity properties (`TotalStep`,
`InhabitedDemonic`) of `Trusted.MirMachine`, the verification lemmas for the
`pub fn id(x: usize) -> usize { x }` vertical slice discharging
`Trusted.CrateTheorem` via `Compiler.SoundOn.verify`, and the positive and
negative Rust adequacy canaries:

1. `canary_safe_infinite_loop`: a pure infinite loop (`bb0: { goto -> bb0; }`)
   satisfies `MirSem loopBody ≤ MirLang.WellFormed`.
2. `canary_uninit_return_violates_wellFormed`: returning an uninitialized `_0`
   violates `MirLang.WellFormed` (`¬ (MirSem uninitReturnBody ≤
   MirLang.WellFormed)`).
3. `canary_wrong_id_violates_ensures`: returning `0` instead of `x` violates
   `EnsuresEqArg 1` (`¬ (MirSem wrongReturnZeroBody ≤ EnsuresEqArg 1)`).
-/

namespace Anneal

open Trusted

/-- `MirMachine` is total: every `(body, s)` pair steps to `evalMirStep body
    s`. -/
theorem mirMachine_total : TotalStep MirMachine :=
  fun body s => ⟨evalMirStep body s, rfl⟩

theorem evalMirStmt_not_choice (s : MirState) (stmt : Stmt)
    (kind : ChoiceKind) (branches : MirState → Prop) :
    StepResult.choice kind branches ≠ evalMirStmt s stmt := by
  cases stmt with
  | assign dst rv =>
    cases rv with
    | use op =>
      cases op with
      | copy src =>
        dsimp [evalMirStmt]
        cases s.locals src.index with
        | none => intro h; cases h
        | some v => intro h; cases h
      | move src =>
        dsimp [evalMirStmt]
        cases s.locals src.index with
        | none => intro h; cases h
        | some v => intro h; cases h
      | constVal v =>
        intro h; cases h
  | storageLive loc => intro h; cases h
  | storageDead loc => intro h; cases h
  | nop => intro h; cases h

theorem evalMirTerminator_not_choice (s : MirState) (term : Terminator)
    (kind : ChoiceKind) (branches : MirState → Prop) :
    StepResult.choice kind branches ≠ evalMirTerminator s term := by
  cases term with
  | return_ =>
    dsimp [evalMirTerminator]
    cases s.locals 0 with
    | none => intro h; cases h
    | some v => intro h; cases h
  | goto target => intro h; cases h
  | unreachable => intro h; cases h

/-- `MirMachine` has no empty choice nodes (`evalMirStep` is deterministic). -/
theorem mirMachine_inhabited : InhabitedDemonic MirMachine := by
  intro body s kind branches hstep
  have h : StepResult.choice kind branches = evalMirStep body s := hstep
  dsimp [evalMirStep] at h
  revert h
  cases body.blocks[s.block]? with
  | none => intro h; cases h
  | some bb =>
    intro h
    dsimp at h
    revert h
    cases bb.stmts[s.stmtIdx]? with
    | none =>
      intro h
      exact False.elim (evalMirTerminator_not_choice s bb.terminator kind branches h)
    | some stmt =>
      intro h
      exact False.elim (evalMirStmt_not_choice s stmt kind branches h)

/-- Postcondition `EnsuresEqArg argLocal` refines `MirLang.WellFormed`. -/
theorem ensuresEqArg_le_wellFormed (argLocal : Nat) :
    EnsuresEqArg argLocal ≤ MirLang.WellFormed :=
  spec_le_wellFormed _

/-- Canonical `Runtime(PostCleanup)` MIR body for
    `pub fn id(x: usize) -> usize { x }` using `Operand.copy`:
    ```text
    bb0: {
        _0 = copy _1;
        return;
    }
    ``` -/
def idCopyBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.assign ⟨0⟩ (.use (.copy ⟨1⟩))]
      terminator := .return_ }
  ]

/-- Canonical `Runtime(PostCleanup)` MIR body for
    `pub fn id(x: usize) -> usize { x }` using `Operand.move`:
    ```text
    bb0: {
        _0 = move _1;
        return;
    }
    ``` -/
def idMoveBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.assign ⟨0⟩ (.use (.move ⟨1⟩))]
      terminator := .return_ }
  ]

/-- `idCopyBody` satisfies `EnsuresEqArg 1`: every reachable prefix is safe and
    any normal return value equals the initial value of `_1`. -/
theorem idCopyBody_satisfies_ensures :
    MirSem idCopyBody ≤ EnsuresEqArg 1 := by
  refine behaviorOf_le_pure (M := MirMachine) ?_
  intro q out hpfx
  cases q with
  | mk init steps =>
  cases out with
  | mk trace outcome =>
    have hinit := hpfx.1
    have hreach := hpfx.2
    have hb : init.block = 0 := hinit.1
    have hs : init.stmtIdx = 0 := hinit.2.1
    have harg : ∃ v, init.locals 1 = some v ∧ v.hasTy .usize :=
      hinit.2.2.2.1
    cases harg with
    | intro v hv =>
      have hv1 : init.locals 1 = some v := hv.1
      have hstep0 :
          evalMirStep idCopyBody init =
            StepResult.step () {
              locals := updateLocal init.locals 0 (some v)
              block := 0
              stmtIdx := 1
            } := by
        unfold evalMirStep idCopyBody
        rw [hb, hs]
        change (match init.locals 1 with
          | some v => StepResult.step (State := MirState) (Obs := Unit) (Val := MirVal) () {
              locals := updateLocal init.locals 0 (some v)
              block := init.block
              stmtIdx := init.stmtIdx + 1
            }
          | none => StepResult.failed FailureKind.ub) = _
        rw [hv1, hb, hs]
      cases hreach with
      | zero =>
        exact ⟨True.intro, fun _ h => by cases h⟩
      | step n _ s' obs tr out h1 h2 =>
        have h1' : StepResult.step obs s' = evalMirStep idCopyBody init := h1
        rw [hstep0] at h1'
        injection h1' with _ hs'
        subst hs'
        have hstep1 :
            evalMirStep idCopyBody {
              locals := updateLocal init.locals 0 (some v)
              block := 0
              stmtIdx := 1
            } = StepResult.terminated (TerminationKind.normal v) := by
          rfl
        cases h2 with
        | zero =>
          exact ⟨True.intro, fun _ h => by cases h⟩
        | step _ _ _ _ _ _ hstep_bad _ =>
          have hbad : _ = evalMirStep idCopyBody _ := hstep_bad
          rw [hstep1] at hbad
          cases hbad
        | choice _ _ _ _ _ _ _ hstep_bad _ _ =>
          have hbad : _ = evalMirStep idCopyBody _ := hstep_bad
          rw [hstep1] at hbad
          cases hbad
        | emptyChoice _ _ _ _ hstep_bad _ =>
          have hbad : _ = evalMirStep idCopyBody _ := hstep_bad
          rw [hstep1] at hbad
          cases hbad
        | terminated _ _ term hterm =>
          have hterm' : StepResult.terminated term = evalMirStep idCopyBody _ := hterm
          rw [hstep1] at hterm'
          injection hterm' with hterm_eq
          subst hterm_eq
          refine ⟨True.intro, ?_⟩
          intro ret hret
          injection hret with hterm_ret
          injection hterm_ret with hret_eq
          subst hret_eq
          exact hv1
        | failed _ _ err hfail =>
          have hbad : _ = evalMirStep idCopyBody _ := hfail
          rw [hstep1] at hbad
          cases hbad
        | noStep _ _ hnostep =>
          exact False.elim (hnostep ⟨_, hstep1.symm⟩)
      | choice _ _ _ _ _ _ _ h1 _ _ =>
        have h1' : _ = evalMirStep idCopyBody init := h1
        rw [hstep0] at h1'
        cases h1'
      | emptyChoice _ _ _ _ h1 _ =>
        have h1' : _ = evalMirStep idCopyBody init := h1
        rw [hstep0] at h1'
        cases h1'
      | terminated _ _ _ h1 =>
        have h1' : _ = evalMirStep idCopyBody init := h1
        rw [hstep0] at h1'
        cases h1'
      | failed _ _ _ h1 =>
        have h1' : _ = evalMirStep idCopyBody init := h1
        rw [hstep0] at h1'
        cases h1'
      | noStep _ _ hnostep =>
        exact False.elim (hnostep ⟨_, hstep0.symm⟩)

/-- `idCopyBody` satisfies baseline `MirLang.WellFormed`. -/
theorem idCopyBody_satisfies_wellFormed :
    MirSem idCopyBody ≤ MirLang.WellFormed :=
  Preorder.le_trans idCopyBody_satisfies_ensures (ensuresEqArg_le_wellFormed 1)

/-- `idMoveBody` satisfies `EnsuresEqArg 1`: every reachable prefix is safe and
    any normal return value equals the initial value of `_1`. -/
theorem idMoveBody_satisfies_ensures :
    MirSem idMoveBody ≤ EnsuresEqArg 1 := by
  refine behaviorOf_le_pure (M := MirMachine) ?_
  intro q out hpfx
  cases q with
  | mk init steps =>
  cases out with
  | mk trace outcome =>
    have hinit := hpfx.1
    have hreach := hpfx.2
    have hb : init.block = 0 := hinit.1
    have hs : init.stmtIdx = 0 := hinit.2.1
    have harg : ∃ v, init.locals 1 = some v ∧ v.hasTy .usize :=
      hinit.2.2.2.1
    cases harg with
    | intro v hv =>
      have hv1 : init.locals 1 = some v := hv.1
      have hstep0 :
          evalMirStep idMoveBody init =
            StepResult.step () {
              locals := updateLocal (updateLocal init.locals 1 none) 0 (some v)
              block := 0
              stmtIdx := 1
            } := by
        unfold evalMirStep idMoveBody
        rw [hb, hs]
        change (match init.locals 1 with
          | some v => StepResult.step (State := MirState) (Obs := Unit) (Val := MirVal) () {
              locals := updateLocal (updateLocal init.locals 1 none) 0 (some v)
              block := init.block
              stmtIdx := init.stmtIdx + 1
            }
          | none => StepResult.failed FailureKind.ub) = _
        rw [hv1, hb, hs]
      cases hreach with
      | zero =>
        exact ⟨True.intro, fun _ h => by cases h⟩
      | step n _ s' obs tr out h1 h2 =>
        have h1' : StepResult.step obs s' = evalMirStep idMoveBody init := h1
        rw [hstep0] at h1'
        injection h1' with _ hs'
        subst hs'
        have hstep1 :
            evalMirStep idMoveBody {
              locals := updateLocal (updateLocal init.locals 1 none) 0 (some v)
              block := 0
              stmtIdx := 1
            } = StepResult.terminated (TerminationKind.normal v) := by
          rfl
        cases h2 with
        | zero =>
          exact ⟨True.intro, fun _ h => by cases h⟩
        | step _ _ _ _ _ _ hstep_bad _ =>
          have hbad : _ = evalMirStep idMoveBody _ := hstep_bad
          rw [hstep1] at hbad
          cases hbad
        | choice _ _ _ _ _ _ _ hstep_bad _ _ =>
          have hbad : _ = evalMirStep idMoveBody _ := hstep_bad
          rw [hstep1] at hbad
          cases hbad
        | emptyChoice _ _ _ _ hstep_bad _ =>
          have hbad : _ = evalMirStep idMoveBody _ := hstep_bad
          rw [hstep1] at hbad
          cases hbad
        | terminated _ _ term hterm =>
          have hterm' : StepResult.terminated term = evalMirStep idMoveBody _ := hterm
          rw [hstep1] at hterm'
          injection hterm' with hterm_eq
          subst hterm_eq
          refine ⟨True.intro, ?_⟩
          intro ret hret
          injection hret with hterm_ret
          injection hterm_ret with hret_eq
          subst hret_eq
          exact hv1
        | failed _ _ err hfail =>
          have hbad : _ = evalMirStep idMoveBody _ := hfail
          rw [hstep1] at hbad
          cases hbad
        | noStep _ _ hnostep =>
          exact False.elim (hnostep ⟨_, hstep1.symm⟩)
      | choice _ _ _ _ _ _ _ h1 _ _ =>
        have h1' : _ = evalMirStep idMoveBody init := h1
        rw [hstep0] at h1'
        cases h1'
      | emptyChoice _ _ _ _ h1 _ =>
        have h1' : _ = evalMirStep idMoveBody init := h1
        rw [hstep0] at h1'
        cases h1'
      | terminated _ _ _ h1 =>
        have h1' : _ = evalMirStep idMoveBody init := h1
        rw [hstep0] at h1'
        cases h1'
      | failed _ _ _ h1 =>
        have h1' : _ = evalMirStep idMoveBody init := h1
        rw [hstep0] at h1'
        cases h1'
      | noStep _ _ hnostep =>
        exact False.elim (hnostep ⟨_, hstep0.symm⟩)

/-- `idMoveBody` satisfies baseline `MirLang.WellFormed`. -/
theorem idMoveBody_satisfies_wellFormed :
    MirSem idMoveBody ≤ MirLang.WellFormed :=
  Preorder.le_trans idMoveBody_satisfies_ensures (ensuresEqArg_le_wellFormed 1)

/-- Generic single-function `CrateTheorem` discharge for an unannotated safe
    function (`specs := []`) via `Compiler.SoundOn.verify`: given
    `h_wf : MirSem body ≤ MirLang.WellFormed`, proves `CrateTheorem` for the
    single-function crate containing `(fnName, body)` with TCB entry
    `TCBItem.rustcLowering fnName body`. -/
theorem verify_single_fn_wf_crate
    (fnName : String) (body : MirBody)
    (h_wf : MirSem body ≤ MirLang.WellFormed) :
    CrateTheorem {
      functions := [{ name := fnName, prog := body, specs := [] }]
      tcb := [TCBItem.rustcLowering fnName body]
    } := by
  refine ⟨(by intro h; cases h), ⟨⟨True.intro, True.intro⟩, ?_⟩, True.intro⟩
  intro hAssumptions
  exact ⟨Compiler.SoundOn.verify hAssumptions.1 h_wf, True.intro⟩

/-- Generic single-function `CrateTheorem` discharge via
    `Compiler.SoundOn.verify` and `Compiler.Verified.with_wellFormedOn`: given
    a proof `h_proof : MirSem body ≤ spec` and
    `h_spec_wf : spec ≤ MirLang.WellFormed`, proves `CrateTheorem` for the
    single-function crate containing `(fnName, body, [spec])` with TCB entry
    `TCBItem.rustcLowering fnName body`. -/
theorem verify_single_fn_crate
    (fnName : String) (body : MirBody)
    (spec : MirLang.Behavior)
    (h_proof : MirSem body ≤ spec)
    (h_spec_wf : spec ≤ MirLang.WellFormed) :
    CrateTheorem {
      functions := [{ name := fnName, prog := body, specs := [spec] }]
      tcb := [TCBItem.rustcLowering fnName body]
    } := by
  refine ⟨(by intro h; cases h), ⟨⟨True.intro, True.intro⟩, ?_⟩, True.intro⟩
  intro hAssumptions
  exact Compiler.Verified.with_wellFormedOn
    (Compiler.SoundOn.verify hAssumptions.1 h_proof)
    h_spec_wf hAssumptions.1.1

/-- Ready-to-apply `CrateTheorem` witness for `pub fn id` (`Operand.copy`,
    `specs := [EnsuresEqArg 1]`). -/
theorem prove_id_copy_ensures_crate (fnName : String) :
    CrateTheorem {
      functions := [{ name := fnName, prog := idCopyBody, specs := [EnsuresEqArg 1] }]
      tcb := [TCBItem.rustcLowering fnName idCopyBody]
    } :=
  verify_single_fn_crate fnName idCopyBody (EnsuresEqArg 1)
    idCopyBody_satisfies_ensures (ensuresEqArg_le_wellFormed 1)

/-- Ready-to-apply `CrateTheorem` witness for unannotated `pub fn id`
    (`Operand.copy`, `specs := []`). -/
theorem prove_id_copy_wf_crate (fnName : String) :
    CrateTheorem {
      functions := [{ name := fnName, prog := idCopyBody, specs := [] }]
      tcb := [TCBItem.rustcLowering fnName idCopyBody]
    } :=
  verify_single_fn_wf_crate fnName idCopyBody idCopyBody_satisfies_wellFormed

/-- Ready-to-apply `CrateTheorem` witness for `pub fn id` (`Operand.move`,
    `specs := [EnsuresEqArg 1]`). -/
theorem prove_id_move_ensures_crate (fnName : String) :
    CrateTheorem {
      functions := [{ name := fnName, prog := idMoveBody, specs := [EnsuresEqArg 1] }]
      tcb := [TCBItem.rustcLowering fnName idMoveBody]
    } :=
  verify_single_fn_crate fnName idMoveBody (EnsuresEqArg 1)
    idMoveBody_satisfies_ensures (ensuresEqArg_le_wellFormed 1)

/-- Ready-to-apply `CrateTheorem` witness for unannotated `pub fn id`
    (`Operand.move`, `specs := []`). -/
theorem prove_id_move_wf_crate (fnName : String) :
    CrateTheorem {
      functions := [{ name := fnName, prog := idMoveBody, specs := [] }]
      tcb := [TCBItem.rustcLowering fnName idMoveBody]
    } :=
  verify_single_fn_wf_crate fnName idMoveBody idMoveBody_satisfies_wellFormed

/-!
## Positive and Negative Rust Adequacy Canaries
-/

/-- Pure infinite loop MIR body (`bb0: { goto -> bb0; }`). -/
def loopBody : MirBody where
  argTys := []
  retTy := .unit
  localCount := 1
  blocks := [{ stmts := [], terminator := .goto ⟨0⟩ }]

theorem loopBody_reaches_running (init : MirState) (n : Nat) :
    ∀ (s : MirState) (tr : List Unit) (out : PrefixOutcome MirVal),
      s.block = 0 → s.stmtIdx = 0 →
      ReachesPrefix MirMachine loopBody init n s tr out →
      out = PrefixOutcome.running := by
  induction n with
  | zero =>
    intro s tr out _ _ hreach
    cases hreach with
    | zero => rfl
  | succ k ih =>
    intro s tr out hb hs hreach
    have hstep0 : evalMirStep loopBody s = StepResult.step () { s with block := 0, stmtIdx := 0 } := by
      unfold evalMirStep loopBody
      rw [hb, hs]
      rfl
    cases hreach with
    | step _ _ s' obs tr' _ h1 h2 =>
      have h1' : StepResult.step obs s' = evalMirStep loopBody s := h1
      rw [hstep0] at h1'
      injection h1' with _ hs'
      subst hs'
      exact ih { s with block := 0, stmtIdx := 0 } tr' out rfl rfl h2
    | choice _ _ _ _ _ _ _ h1 _ _ =>
      have h1' : _ = evalMirStep loopBody s := h1
      rw [hstep0] at h1'
      cases h1'
    | emptyChoice _ _ _ _ h1 _ =>
      have h1' : _ = evalMirStep loopBody s := h1
      rw [hstep0] at h1'
      cases h1'
    | terminated _ _ _ h1 =>
      have h1' : _ = evalMirStep loopBody s := h1
      rw [hstep0] at h1'
      cases h1'
    | failed _ _ _ h1 =>
      have h1' : _ = evalMirStep loopBody s := h1
      rw [hstep0] at h1'
      cases h1'
    | noStep _ _ hnostep =>
      exact False.elim (hnostep ⟨_, hstep0.symm⟩)

/-- Positive adequacy canary: a pure infinite loop (`loop {}`)
    never triggers `.failed` or `.stuck` at any prefix depth and therefore
    satisfies `MirLang.WellFormed`. -/
theorem canary_safe_infinite_loop :
    MirSem loopBody ≤ MirLang.WellFormed := by
  refine (behaviorOf_le_wellFormed_iff (M := MirMachine)).mpr ?_
  intro init steps tr out hinit hreach
  have hout := loopBody_reaches_running init steps init tr out
    hinit.1 hinit.2.1 hreach
  rw [hout]
  exact True.intro

/-- MIR body that returns immediately without initializing `_0`. -/
def uninitReturnBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 1
  blocks := [{ stmts := [], terminator := .return_ }]

/-- Negative adequacy canary: returning an uninitialized `_0`
    triggers `.failed .ub` at step `1` and therefore refutes
    `MirLang.WellFormed`. -/
theorem canary_uninit_return_violates_wellFormed :
    ¬ (MirSem uninitReturnBody ≤ MirLang.WellFormed) := by
  intro hWF
  let s0 : MirState := { locals := fun _ => none, block := 0, stmtIdx := 0 }
  have hinit : initMirState uninitReturnBody s0 :=
    ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
  have hfail : ReachesPrefix MirMachine uninitReturnBody s0 1 s0 [] (PrefixOutcome.failed FailureKind.ub) :=
    ReachesPrefix.failed 0 s0 FailureKind.ub rfl
  exact (behaviorOf_le_wellFormed_iff (M := MirMachine)).mp hWF s0 1 [] (.failed .ub) hinit hfail

/-- MIR body for `pub fn id(x: usize) -> usize { 0 }` (assigns constant `0` to
    `_0` instead of `x`). -/
def wrongReturnZeroBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.assign ⟨0⟩ (.use (.constVal (.usize 0)))]
      terminator := .return_ }
  ]

/-- Negative adequacy canary: returning constant `0` instead of `_1`
    violates `EnsuresEqArg 1` when `_1 = MirVal.usize 1`. -/
theorem canary_wrong_id_violates_ensures :
    ¬ (MirSem wrongReturnZeroBody ≤ EnsuresEqArg 1) := by
  intro hEns
  let locals0 : Nat → Option MirVal :=
    updateLocal (fun _ => none) 1 (some (.usize 1))
  let s0 : MirState := { locals := locals0, block := 0, stmtIdx := 0 }
  let s1 : MirState := {
    locals := updateLocal locals0 0 (some (.usize 0))
    block := 0
    stmtIdx := 1
  }
  have hrest : ∀ j, 2 ≤ j → locals0 j = none := by
    intro j hj
    cases j with
    | zero => cases hj
    | succ k =>
      cases k with
      | zero =>
        cases hj with
        | step hle => cases hle
      | succ m => rfl
  have hinit : initMirState wrongReturnZeroBody s0 :=
    ⟨rfl, rfl, rfl, ⟨⟨MirVal.usize 1, rfl, True.intro⟩, hrest⟩⟩
  have hreach1 : ReachesPrefix MirMachine wrongReturnZeroBody s0 1 s1 []
      (PrefixOutcome.terminated (TerminationKind.normal (MirVal.usize 0))) :=
    ReachesPrefix.terminated 0 s1 (TerminationKind.normal (MirVal.usize 0)) rfl
  have hreach2 : ReachesPrefix MirMachine wrongReturnZeroBody s0 2 s0 [()]
      (PrefixOutcome.terminated (TerminationKind.normal (MirVal.usize 0))) :=
    ReachesPrefix.step 1 s0 s1 () []
      (PrefixOutcome.terminated (TerminationKind.normal (MirVal.usize 0))) rfl hreach1
  let q : ExecQuery MirState := { init := s0, steps := 2 }
  let out : ExecOut Unit MirVal := {
    trace := [()]
    outcome := PrefixOutcome.terminated (TerminationKind.normal (MirVal.usize 0))
  }
  cases hEns q True.intro with
  | intro hdef hval =>
    have hpfx : (MirSem wrongReturnZeroBody q).val hdef out := ⟨hinit, hreach2⟩
    have hpost := hval out hpfx (MirVal.usize 0) rfl
    have h1 : q.init.locals 1 = some (MirVal.usize 1) := rfl
    rw [h1] at hpost
    injection hpost with hval'
    injection hval' with hnum
    cases hnum

end Anneal
