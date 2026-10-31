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
# MIR Meta-Theorems, PME & Library Verification Lemmas, and Adequacy Canaries

This module proves:
1. Structural non-vacuity properties (`TotalStep`, `InhabitedDemonic`) of
   `Trusted.MirMachine` and admissibility of `defaultAdtInv` and
   `nonZeroAdtInv`.
2. Symbolic small-step execution helpers (`reachesPrefix_of_step`,
   `reachesPrefix_of_terminated`, `reachesPrefix_safeAndEnsures_of_step`,
   `reachesPrefix_safeAndEnsures_of_normal`, `retLibInv_of_ensuresEqArg1`).
3. Verification lemmas for the `pub fn id(x: usize) -> usize { x }` vertical
   slice discharging `Trusted.CrateTheorem`.
4. Verification lemmas for Post-Monomorphization Error (PME) size-checked
   transmutation (`sizeEqConstBody`, `transmuteCheckedBody`,
   `outerTransmuteBody`, `swappedOuterTransmuteBody`), unconditional
   `MirLang.WellFormed` for PME-gated functions, and the negative adequacy
   canary proving that removing the PME (`transmuteUncheckedBody`) is rejected
   (`¬ CrateTheorem`).
5. Verification lemmas for the `NonZeroUsize` library verification contract
   (`makeNonZeroBody`, `newUncheckedBody`, `getUncheckedNonZeroBody`) and
   negative adequacy canaries (`buggyZeroBody`, public-safe field rejection).
-/

namespace Anneal

open Trusted

/-!
## 1. Structural Machine Meta-Theorems (`TotalStep`, `InhabitedDemonic`)
-/

/-- `MirMachine` is total: every `(body, s)` pair steps to `evalMirStep body
    s`. -/
theorem mirMachine_total : TotalStep MirMachine :=
  fun body s => ⟨evalMirStep body s, rfl⟩

theorem evalMirStmt_not_choice (s : MirState) (stmt : Stmt)
    (branches : MirState → Prop) :
    StepResult.choice branches ≠ evalMirStmt s stmt := by
  cases stmt with
  | assign dst rv =>
    cases rv with
    | use op =>
      dsimp [evalMirStmt]
      cases evalOperand s.locals op with
      | none => intro h; cases h
      | some p => intro h; cases h
    | binaryOp op lhs rhs =>
      dsimp [evalMirStmt]
      cases evalOperand s.locals lhs with
      | none => intro h; cases h
      | some p1 =>
        dsimp
        cases evalOperand p1.2 rhs with
        | none => intro h; cases h
        | some p2 =>
          dsimp
          cases evalBinOp op p1.1 p2.1 with
          | none => intro h; cases h
          | some v => intro h; cases h
    | aggregate adtId op =>
      dsimp [evalMirStmt]
      cases evalOperand s.locals op with
      | none => intro h; cases h
      | some p => intro h; cases h
    | field0 src =>
      dsimp [evalMirStmt]
      cases s.locals src.index with
      | none => intro h; cases h
      | some v =>
        cases v <;> (intro h; cases h)
    | ref src =>
      dsimp [evalMirStmt]
      cases s.locals src.index with
      | none => intro h; cases h
      | some _ => intro h; cases h
    | reborrow src =>
      dsimp [evalMirStmt]
      cases s.locals src.index with
      | none => intro h; cases h
      | some v =>
        cases v with
        | ref target =>
          dsimp
          cases s.locals target.index with
          | none => intro h; cases h
          | some _ => intro h; cases h
        | _ => intro h; cases h
  | storageLive loc => intro h; cases h
  | storageDead loc => intro h; cases h
  | nop => intro h; cases h

theorem evalMirTerminator_not_choice (active : MirBody) (s : MirState)
    (term : Terminator) (branches : MirState → Prop) :
    StepResult.choice branches ≠ evalMirTerminator active s term := by
  cases term with
  | return_ =>
    dsimp [evalMirTerminator]
    cases s.locals 0 with
    | none => intro h; cases h
    | some v =>
      dsimp
      cases s.stack with
      | nil => intro h; cases h
      | cons f rest => intro h; cases h
  | goto target => intro h; cases h
  | unreachable => intro h; cases h
  | panic => intro h; cases h
  | switchInt discr falseTarget trueTarget =>
    dsimp [evalMirTerminator]
    cases evalOperand s.locals discr with
    | none => intro h; cases h
    | some p =>
      cases p with
      | mk v locals' =>
        cases v with
        | bool b =>
          cases b <;> (intro h; cases h)
        | _ => intro h; cases h
  | callSizeOf dst ty target => intro h; cases h
  | callTransmuteCopy dst srcTy dstTy op target =>
    dsimp [evalMirTerminator]
    cases evalOperand s.locals op with
    | none => intro h; cases h
    | some p =>
      dsimp
      cases evalTransmuteCopy s.tySizes p.2 srcTy dstTy p.1 with
      | none => intro h; cases h
      | some _ => intro h; cases h
  | call1 dst callee arg target typeArgs =>
    dsimp [evalMirTerminator]
    cases evalOperand s.locals arg with
    | none => intro h; cases h
    | some _ => intro h; cases h

/-- `MirMachine` has no empty choice nodes (`evalMirStep` is deterministic). -/
theorem mirMachine_inhabited : InhabitedDemonic MirMachine := by
  intro body s branches hstep
  have h : StepResult.choice branches = evalMirStep body s := hstep
  dsimp [evalMirStep] at h
  revert h
  cases (s.curBody.getD body).blocks[s.block]? with
  | none => intro h; cases h
  | some bb =>
    intro h
    dsimp at h
    revert h
    cases bb.stmts[s.stmtIdx]? with
    | none =>
      intro h
      exact False.elim
        (evalMirTerminator_not_choice (s.curBody.getD body) s bb.terminator
          branches h)
    | some stmt =>
      intro h
      exact False.elim (evalMirStmt_not_choice s stmt branches h)

/-- Postcondition `EnsuresEqArg argLocal` refines `MirLang.WellFormed`. -/
theorem ensuresEqArg_le_wellFormed (argLocal : Nat) :
    EnsuresEqArg argLocal ≤ MirLang.WellFormed :=
  spec_le_wellFormed _

/-- Postcondition `EnsuresEqArg argLocal` refines `MirLang.WellFormedOn pre` for
    any precondition `pre`. -/
theorem ensuresEqArg_le_wellFormedOn (argLocal : Nat)
    (pre : ExecQuery MirState → Prop) :
    EnsuresEqArg argLocal ≤ MirLang.WellFormedOn pre :=
  Preorder.le_trans (ensuresEqArg_le_wellFormed argLocal)
    (wellFormed_le_wellFormedOn (L := MirLang) pre)

/-- Postcondition `EnsuresRetLibInv adtInv retTy pre` refines
    `MirLang.WellFormedOn pre`. -/
theorem ensuresRetLibInv_le_wellFormedOn (adtInv : AdtInv) (retTy : MirTy)
    (pre : ExecQuery MirState → Prop) :
    EnsuresRetLibInv adtInv retTy pre ≤ MirLang.WellFormedOn pre :=
  specOn_le_wellFormedOn (L := MirLang) pre _

/-- `defaultAdtInv` is admissible for any list of ADT declarations `adts`. -/
theorem defaultAdtInv_admissible (adts : List AdtDecl) :
    AdmissibleAdtInv adts defaultAdtInv :=
  fun _ _ _ _ => True.intro

/-!
## 2. Symbolic Small-Step Execution Helpers
-/

theorem reachesPrefix_of_step
    {body : MirBody} {s s' : MirState} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome MirVal}
    (hstep : evalMirStep body s = .step () s')
    (hreach : ReachesPrefix MirStep body n s tr out) :
    out = .running ∨
      ∃ n' tr', ReachesPrefix MirStep body n' s' tr' out := by
  cases hreach with
  | zero => exact Or.inl rfl
  | step n' _ s₂ _ tr' _ h1 hr =>
    have h1' : StepResult.step () s₂ = evalMirStep body s := h1
    rw [hstep] at h1'
    injection h1' with _ hs
    subst hs
    exact Or.inr ⟨n', tr', hr⟩
  | choice _ _ _ _ _ _ h1 _ _ =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | emptyChoice _ _ _ h1 _ =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | terminated _ _ _ h1 =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | failed _ _ h1 =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, hstep.symm⟩)

theorem reachesPrefix_of_terminated
    {body : MirBody} {s : MirState} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome MirVal} {term : TerminationKind MirVal}
    (hstep : evalMirStep body s = .terminated term)
    (hreach : ReachesPrefix MirStep body n s tr out) :
    out = .running ∨ out = .terminated term := by
  cases hreach with
  | zero => exact Or.inl rfl
  | step _ _ _ _ _ _ h1 _ =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | choice _ _ _ _ _ _ h1 _ _ =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | emptyChoice _ _ _ h1 _ =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | terminated _ _ t h1 =>
    have h1' : StepResult.terminated t = evalMirStep body s := h1
    rw [hstep] at h1'
    injection h1' with ht
    subst ht
    exact Or.inr rfl
  | failed _ _ h1 =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, hstep.symm⟩)

/-- Combined prefix-safety and normal-return postcondition predicate on a
    `PrefixOutcome`. -/
def SafeAndEnsures (P : MirVal → Prop) (out : PrefixOutcome MirVal) : Prop :=
  out.isSafe ∧ ∀ ret, out = .terminated (.normal ret) → P ret

theorem reachesPrefix_safeAndEnsures_of_step
    {body : MirBody} {s s' : MirState} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome MirVal} {P : MirVal → Prop}
    (hstep : evalMirStep body s = .step () s')
    (hreach : ReachesPrefix MirStep body n s tr out)
    (hnext : ∀ n' tr', ReachesPrefix MirStep body n' s' tr' out →
      SafeAndEnsures P out) :
    SafeAndEnsures P out := by
  cases reachesPrefix_of_step hstep hreach with
  | inl hrun =>
    subst hrun
    exact ⟨True.intro, fun _ h => by cases h⟩
  | inr hex =>
    cases hex with
    | intro n' htr =>
      cases htr with
      | intro tr' hr' => exact hnext n' tr' hr'

theorem reachesPrefix_safeAndEnsures_of_normal
    {body : MirBody} {s : MirState} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome MirVal} {P : MirVal → Prop} {v : MirVal}
    (hstep : evalMirStep body s = .terminated (.normal v))
    (hreach : ReachesPrefix MirStep body n s tr out)
    (hPv : P v) :
    SafeAndEnsures P out := by
  cases reachesPrefix_of_terminated hstep hreach with
  | inl hrun =>
    subst hrun
    exact ⟨True.intro, fun _ h => by cases h⟩
  | inr hterm =>
    subst hterm
    refine ⟨True.intro, ?_⟩
    intro ret hret
    injection hret with h1
    injection h1 with h2
    subst h2
    exact hPv

theorem reachesPrefix_not_normal_of_step
    {body : MirBody} {s s' : MirState} {n : Nat} {tr : List Unit}
    {v : MirVal}
    (hstep : evalMirStep body s = .step () s')
    (hreach : ReachesPrefix MirStep body n s tr (.terminated (.normal v)))
    (hnext : ∀ n' tr',
      ReachesPrefix MirStep body n' s' tr' (.terminated (.normal v)) →
      False) :
    False := by
  cases reachesPrefix_of_step hstep hreach with
  | inl hrun => cases hrun
  | inr hex =>
    cases hex with
    | intro n' htr =>
      cases htr with
      | intro tr' hr' => exact hnext n' tr' hr'

theorem reachesPrefix_not_normal_of_unwind
    {body : MirBody} {s : MirState} {n : Nat} {tr : List Unit}
    {v : MirVal}
    (hstep : evalMirStep body s = .terminated .unwind)
    (hreach : ReachesPrefix MirStep body n s tr (.terminated (.normal v))) :
    False := by
  cases reachesPrefix_of_terminated hstep hreach with
  | inl hrun => cases hrun
  | inr hunw => cases hunw

/-- Any single-argument function (`body.argTys = [ty]`) that satisfies
    `EnsuresEqArg 1` automatically satisfies
    `EnsuresRetLibInv defaultAdtInv ty pre` for any precondition `pre`, without
    repeating symbolic execution. -/
theorem retLibInv_of_ensuresEqArg1
    {body : MirBody} {ty : MirTy}
    (hArgs : body.argTys = [ty])
    (hEns : MirSem body ≤ EnsuresEqArg 1)
    (pre : ExecQuery MirState → Prop) :
    MirSem body ≤ EnsuresRetLibInv defaultAdtInv ty pre := by
  intro q _
  cases hEns q True.intro with
  | intro hdef hval =>
    refine ⟨hdef, fun out hpfx ret hret => ?_⟩
    have hloc1 : q.init.locals 1 = some ret := hval out hpfx ret hret
    have hargs := hpfx.1.1.2.2.2.2.2
    rw [hArgs] at hargs
    cases hargs.1 with
    | intro v hv =>
      have heq : some v = some ret := hv.1.symm.trans hloc1
      injection heq with hvret
      subst hvret
      exact hv.2

/-!
## 3. `pub fn id(x: usize) -> usize { x }` Verification Lemmas
-/

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
  cases init with
  | mk locals0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
  cases out with
  | mk trace outcome =>
    have hinit := hpfx.1.1
    have hreach := hpfx.2
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    subst hb hs hc hst
    cases hinit.2.2.2.2.2.1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      let s₀ : MirState := { locals := locals0, block := 0, stmtIdx := 0, tySizes := tySizes0 }
      let s₁ : MirState := { s₀ with locals := updateLocal locals0 0 (some v), stmtIdx := 1 }
      have hstep0 : evalMirStep idCopyBody s₀ = .step () s₁ := by
        change evalMirStmt s₀ (.assign ⟨0⟩ (.use (.copy ⟨1⟩))) = .step () s₁
        dsimp [evalMirStmt, evalOperand, s₀]
        rw [hv1]
      refine reachesPrefix_safeAndEnsures_of_step hstep0 hreach (fun _ _ hr1 => ?_)
      exact reachesPrefix_safeAndEnsures_of_normal rfl hr1 hv1

/-- `idCopyBody` satisfies baseline `MirLang.WellFormed`. -/
theorem idCopyBody_satisfies_wellFormed :
    MirSem idCopyBody ≤ MirLang.WellFormed :=
  Preorder.le_trans idCopyBody_satisfies_ensures (ensuresEqArg_le_wellFormed 1)

/-- `idCopyBody` satisfies `EnsuresRetLibInv defaultAdtInv .usize pre` for any
    precondition `pre`. -/
theorem idCopyBody_satisfies_retLibInv (pre : ExecQuery MirState → Prop) :
    MirSem idCopyBody ≤ EnsuresRetLibInv defaultAdtInv .usize pre :=
  retLibInv_of_ensuresEqArg1 rfl idCopyBody_satisfies_ensures pre

/-- `idMoveBody` satisfies `EnsuresEqArg 1`: every reachable prefix is safe and
    any normal return value equals the initial value of `_1`. -/
theorem idMoveBody_satisfies_ensures :
    MirSem idMoveBody ≤ EnsuresEqArg 1 := by
  refine behaviorOf_le_pure (M := MirMachine) ?_
  intro q out hpfx
  cases q with
  | mk init steps =>
  cases init with
  | mk locals0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
  cases out with
  | mk trace outcome =>
    have hinit := hpfx.1.1
    have hreach := hpfx.2
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    subst hb hs hc hst
    cases hinit.2.2.2.2.2.1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      let s₀ : MirState := { locals := locals0, block := 0, stmtIdx := 0, tySizes := tySizes0 }
      let s₁ : MirState := {
        s₀ with
        locals := updateLocal (updateLocal locals0 1 none) 0 (some v)
        stmtIdx := 1
      }
      have hstep0 : evalMirStep idMoveBody s₀ = .step () s₁ := by
        change evalMirStmt s₀ (.assign ⟨0⟩ (.use (.move ⟨1⟩))) = .step () s₁
        dsimp [evalMirStmt, evalOperand, s₀]
        rw [hv1]
      refine reachesPrefix_safeAndEnsures_of_step hstep0 hreach (fun _ _ hr1 => ?_)
      exact reachesPrefix_safeAndEnsures_of_normal rfl hr1 hv1

/-- `idMoveBody` satisfies baseline `MirLang.WellFormed`. -/
theorem idMoveBody_satisfies_wellFormed :
    MirSem idMoveBody ≤ MirLang.WellFormed :=
  Preorder.le_trans idMoveBody_satisfies_ensures (ensuresEqArg_le_wellFormed 1)

/-- `idMoveBody` satisfies `EnsuresRetLibInv defaultAdtInv .usize pre` for any
    precondition `pre`. -/
theorem idMoveBody_satisfies_retLibInv (pre : ExecQuery MirState → Prop) :
    MirSem idMoveBody ≤ EnsuresRetLibInv defaultAdtInv .usize pre :=
  retLibInv_of_ensuresEqArg1 rfl idMoveBody_satisfies_ensures pre

/-- Generic single-function `CrateTheorem` discharge for an unannotated safe
    function (`specs := []`, `kind := .pubSafe True`) via
    `Compiler.SoundOn.verify` and `Compiler.Verified.with_wellFormedOn`. -/
theorem verify_single_fn_wf_crate
    (fnName : String) (body : MirBody)
    (h_ret : MirSem body ≤
      EnsuresRetLibInv defaultAdtInv body.retTy
        (CapturedFn.effectivePre defaultAdtInv { name := fnName, prog := body, specs := [] })) :
    CrateTheorem {
      functions := [{ name := fnName, prog := body, specs := [] }]
      tcb := [TCBItem.rustcLowering fnName body]
    } := by
  refine ⟨(by intro h; cases h), defaultAdtInv_admissible [], True.intro, ⟨⟨True.intro, True.intro⟩, ?_⟩, True.intro⟩
  intro hAssumptions
  exact Compiler.Verified.with_wellFormedOn
    (Compiler.SoundOn.verify hAssumptions.1 h_ret)
    (ensuresRetLibInv_le_wellFormedOn _ _ _)
    hAssumptions.1.1

/-- Generic single-function `CrateTheorem` discharge for a safe function with an
    explicit functional specification `spec`. -/
theorem verify_single_fn_crate
    (fnName : String) (body : MirBody)
    (spec : MirLang.Behavior)
    (h_ret : MirSem body ≤
      EnsuresRetLibInv defaultAdtInv body.retTy
        (CapturedFn.effectivePre defaultAdtInv { name := fnName, prog := body, specs := [spec] }))
    (h_proof : MirSem body ≤ spec) :
    CrateTheorem {
      functions := [{ name := fnName, prog := body, specs := [spec] }]
      tcb := [TCBItem.rustcLowering fnName body]
    } := by
  refine ⟨(by intro h; cases h), defaultAdtInv_admissible [], True.intro, ⟨⟨True.intro, True.intro⟩, ?_⟩, True.intro⟩
  intro hAssumptions
  have hVerRet := Compiler.SoundOn.verify hAssumptions.1 h_ret
  have hVerSpec := Compiler.SoundOn.verify hAssumptions.1 h_proof
  have hVerWF := Compiler.SoundOn.verify hAssumptions.1
    (Preorder.le_trans h_ret (ensuresRetLibInv_le_wellFormedOn _ _ _))
  exact ⟨hVerWF, hVerRet, hVerSpec, True.intro⟩

/-- Ready-to-apply `CrateTheorem` witness for `pub fn id` (`Operand.copy`,
    `specs := [EnsuresEqArg 1]`). -/
theorem prove_id_copy_ensures_crate (fnName : String) :
    CrateTheorem {
      functions := [{ name := fnName, prog := idCopyBody, specs := [EnsuresEqArg 1] }]
      tcb := [TCBItem.rustcLowering fnName idCopyBody]
    } :=
  verify_single_fn_crate fnName idCopyBody (EnsuresEqArg 1)
    (idCopyBody_satisfies_retLibInv _) idCopyBody_satisfies_ensures

/-- Ready-to-apply `CrateTheorem` witness for unannotated `pub fn id`
    (`Operand.copy`, `specs := []`). -/
theorem prove_id_copy_wf_crate (fnName : String) :
    CrateTheorem {
      functions := [{ name := fnName, prog := idCopyBody, specs := [] }]
      tcb := [TCBItem.rustcLowering fnName idCopyBody]
    } :=
  verify_single_fn_wf_crate fnName idCopyBody (idCopyBody_satisfies_retLibInv _)

/-- Ready-to-apply `CrateTheorem` witness for `pub fn id` (`Operand.move`,
    `specs := [EnsuresEqArg 1]`). -/
theorem prove_id_move_ensures_crate (fnName : String) :
    CrateTheorem {
      functions := [{ name := fnName, prog := idMoveBody, specs := [EnsuresEqArg 1] }]
      tcb := [TCBItem.rustcLowering fnName idMoveBody]
    } :=
  verify_single_fn_crate fnName idMoveBody (EnsuresEqArg 1)
    (idMoveBody_satisfies_retLibInv _) idMoveBody_satisfies_ensures

/-- Ready-to-apply `CrateTheorem` witness for unannotated `pub fn id`
    (`Operand.move`, `specs := []`). -/
theorem prove_id_move_wf_crate (fnName : String) :
    CrateTheorem {
      functions := [{ name := fnName, prog := idMoveBody, specs := [] }]
      tcb := [TCBItem.rustcLowering fnName idMoveBody]
    } :=
  verify_single_fn_wf_crate fnName idMoveBody (idMoveBody_satisfies_retLibInv _)

/-!
## 4. Post-Monomorphization Error (PME) Size-Checked Transmute Lemmas
-/

/-- Canonical `rustc -Z mir-opt-level=0 --emit=mir` constant body for
    `assert!(core::mem::size_of::<Src>() == core::mem::size_of::<Dst>())`
    (shared by both `const ASSERT: () = assert!(...)` and inline
    `const { assert!(...) }`):
    ```text
    bb0: {
        StorageLive(_1);
        StorageLive(_2);
        ConstEvalCounter;
        _2 = std::mem::size_of::<Src>() -> [return: bb1, unwind continue];
    }
    bb1: {
        StorageLive(_3);
        ConstEvalCounter;
        _3 = std::mem::size_of::<Dst>() -> [return: bb2, unwind continue];
    }
    bb2: {
        _1 = Eq(move _2, move _3);
        switchInt(move _1) -> [0: bb4, otherwise: bb3];
    }
    bb3: {
        StorageDead(_3);
        StorageDead(_2);
        _0 = const ();
        StorageDead(_1);
        return;
    }
    bb4: {
        StorageDead(_3);
        StorageDead(_2);
        StorageLive(_4);
        ConstEvalCounter;
        _4 = panic(...) -> unwind continue;
    }
    ``` -/
def sizeEqConstBody : MirBody where
  argTys := []
  retTy := .unit
  localCount := 5
  blocks := [
    { stmts := [.storageLive ⟨1⟩, .storageLive ⟨2⟩, .nop]
      terminator := .callSizeOf ⟨2⟩ (.param 0) ⟨1⟩ },
    { stmts := [.storageLive ⟨3⟩, .nop]
      terminator := .callSizeOf ⟨3⟩ (.param 1) ⟨2⟩ },
    { stmts := [.assign ⟨1⟩ (.binaryOp .eq (.move ⟨2⟩) (.move ⟨3⟩))]
      terminator := .switchInt (.move ⟨1⟩) ⟨4⟩ ⟨3⟩ },
    { stmts := [
        .storageDead ⟨3⟩,
        .storageDead ⟨2⟩,
        .assign ⟨0⟩ (.use (.constVal .unit)),
        .storageDead ⟨1⟩
      ]
      terminator := .return_ },
    { stmts := [.storageDead ⟨3⟩, .storageDead ⟨2⟩, .storageLive ⟨4⟩, .nop]
      terminator := .panic }
  ]
  requiredConsts := []

/-- Canonical `rustc -Z mir-opt-level=0 --emit=mir` body for
    `pub fn transmute_checked<Src: Copy, Dst: Copy>(x: Src) -> Dst`:
    ```text
    bb0: {
        StorageLive(_2);
        _2 = const <() as SizeEq<Src, Dst>>::ASSERT;
        StorageDead(_2);
        StorageLive(_3);
        StorageLive(_4);
        _4 = &_1;
        _3 = &(*_4);
        _0 = transmute_copy::<Src, Dst>(move _3) -> [return: bb1, unwind continue];
    }
    bb1: {
        StorageDead(_4);
        StorageDead(_3);
        return;
    }
    ``` -/
def transmuteCheckedBody : MirBody where
  argTys := [.param 0]
  retTy := .param 1
  localCount := 5
  blocks := [
    { stmts := [
        .storageLive ⟨2⟩,
        .assign ⟨2⟩ (.use (.constVal .unit)),
        .storageDead ⟨2⟩,
        .storageLive ⟨3⟩,
        .storageLive ⟨4⟩,
        .assign ⟨4⟩ (.ref ⟨1⟩),
        .assign ⟨3⟩ (.reborrow ⟨4⟩)
      ]
      terminator := .callTransmuteCopy ⟨0⟩ (.param 0) (.param 1) (.move ⟨3⟩) ⟨1⟩ },
    { stmts := [.storageDead ⟨4⟩, .storageDead ⟨3⟩]
      terminator := .return_ }
  ]
  requiredConsts := [sizeEqConstBody]

/-- Canonical `rustc -Z mir-opt-level=0 --emit=mir` body for
    `pub fn outer_transmute<Src: Copy, Dst: Copy>(x: Src) -> Dst` calling
    `transmute_checked::<Src, Dst>(x)`:
    ```text
    bb0: {
        StorageLive(_2);
        _2 = copy _1;
        _0 = transmute_checked::<Src, Dst>(move _2) -> [return: bb1, unwind continue];
    }
    bb1: {
        StorageDead(_2);
        return;
    }
    ``` -/
def outerTransmuteBody : MirBody where
  argTys := [.param 0]
  retTy := .param 1
  localCount := 3
  blocks := [
    { stmts := [.storageLive ⟨2⟩, .assign ⟨2⟩ (.use (.copy ⟨1⟩))]
      terminator := .call1 ⟨0⟩ transmuteCheckedBody (.move ⟨2⟩) ⟨1⟩ },
    { stmts := [.storageDead ⟨2⟩]
      terminator := .return_ }
  ]
  requiredConsts := []

/-- Generic wrapper body `pub fn swapped_outer<A: Copy, B: Copy>(x: B) -> A`
    calling `transmute_checked::<B, A>(x)` with non-identity type arguments
    `typeArgs := [.param 1, .param 0]`. -/
def swappedOuterTransmuteBody : MirBody where
  argTys := [.param 1]
  retTy := .param 0
  localCount := 3
  blocks := [
    { stmts := [.storageLive ⟨2⟩, .assign ⟨2⟩ (.use (.copy ⟨1⟩))]
      terminator :=
        .call1 ⟨0⟩ transmuteCheckedBody (.move ⟨2⟩) ⟨1⟩ [.param 1, .param 0] },
    { stmts := [.storageDead ⟨2⟩]
      terminator := .return_ }
  ]
  requiredConsts := []

/-- Canonical `rustc -Z mir-opt-level=0 --emit=mir` body for an unchecked
    `pub fn transmute_unchecked<Src: Copy, Dst: Copy>(x: Src) -> Dst` that omits
    the PME assertion (`requiredConsts = []`):
    ```text
    bb0: {
        StorageLive(_2);
        StorageLive(_3);
        _3 = &_1;
        _2 = &(*_3);
        _0 = transmute_copy::<Src, Dst>(move _2) -> [return: bb1, unwind continue];
    }
    bb1: {
        StorageDead(_3);
        StorageDead(_2);
        return;
    }
    ``` -/
def transmuteUncheckedBody : MirBody where
  argTys := [.param 0]
  retTy := .param 1
  localCount := 4
  blocks := [
    { stmts := [
        .storageLive ⟨2⟩,
        .storageLive ⟨3⟩,
        .assign ⟨3⟩ (.ref ⟨1⟩),
        .assign ⟨2⟩ (.reborrow ⟨3⟩)
      ]
      terminator := .callTransmuteCopy ⟨0⟩ (.param 0) (.param 1) (.move ⟨2⟩) ⟨1⟩ },
    { stmts := [.storageDead ⟨3⟩, .storageDead ⟨2⟩]
      terminator := .return_ }
  ]
  requiredConsts := []

/-- Key PME soundness lemma: if CTFE of `sizeEqConstBody` succeeds under
    `tySizes` (`ConstSucceeds tySizes sizeEqConstBody`), then `Src` and `Dst`
    have equal byte size (`tySizes 0 = tySizes 1`). -/
theorem constSucceeds_sizeEqConstBody_imp_eq (tySizes : Nat → Nat)
    (h : ConstSucceeds tySizes sizeEqConstBody) :
    tySizes 0 = tySizes 1 := by
  cases h with
  | intro s0 h1 =>
  cases s0 with
  | mk locals0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
  cases h1 with
  | intro n h2 =>
  cases h2 with
  | intro tr h3 =>
  cases h3 with
  | intro v h4 =>
    have hts : tySizes0 = tySizes := h4.1
    have hinit := h4.2.1
    have hreach := h4.2.2
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    subst hts hb hs hc hst
    cases hdec : decide (tySizes0 0 = tySizes0 1) with
    | true => exact of_decide_eq_true hdec
    | false =>
      refine False.elim ?_
      refine reachesPrefix_not_normal_of_step rfl hreach (fun _ _ hr1 => ?_)
      refine reachesPrefix_not_normal_of_step rfl hr1 (fun _ _ hr2 => ?_)
      refine reachesPrefix_not_normal_of_step rfl hr2 (fun _ _ hr3 => ?_)
      refine reachesPrefix_not_normal_of_step rfl hr3 (fun _ _ hr4 => ?_)
      refine reachesPrefix_not_normal_of_step rfl hr4 (fun _ _ hr5 => ?_)
      refine reachesPrefix_not_normal_of_step rfl hr5 (fun _ _ hr6 => ?_)
      refine reachesPrefix_not_normal_of_step rfl hr6 (fun _ _ hr7 => ?_)
      refine reachesPrefix_not_normal_of_step rfl hr7 (fun _ _ hr8 => ?_)
      let l_bb2 := updateLocal (updateLocal (updateLocal
        (updateLocal (updateLocal (updateLocal locals0 1 none) 2 none)
          2 (some (.usize (tySizes0 0))))
        3 none) 3 (some (.usize (tySizes0 1))))
        2 none
      let l_eq := updateLocal (updateLocal l_bb2 3 none)
        1 (some (.bool (decide (tySizes0 0 = tySizes0 1))))
      let s_sw : MirState := {
        locals := l_eq
        block := 2
        stmtIdx := 1
        tySizes := tySizes0
      }
      let s_bb4 : MirState := {
        locals := updateLocal (updateLocal (updateLocal l_bb2 3 none) 1 (some (.bool false))) 1 none
        block := 4
        stmtIdx := 0
        tySizes := tySizes0
      }
      have hstep8 : evalMirStep sizeEqConstBody s_sw = .step () s_bb4 := by
        change evalMirTerminator sizeEqConstBody s_sw (.switchInt (.move ⟨1⟩) ⟨4⟩ ⟨3⟩) = .step () s_bb4
        dsimp only [evalMirTerminator, evalOperand, s_sw, l_eq]
        rw [hdec]
        rfl
      refine reachesPrefix_not_normal_of_step hstep8 hr8 (fun _ _ hr9 => ?_)
      refine reachesPrefix_not_normal_of_step rfl hr9 (fun _ _ hr10 => ?_)
      refine reachesPrefix_not_normal_of_step rfl hr10 (fun _ _ hr11 => ?_)
      refine reachesPrefix_not_normal_of_step rfl hr11 (fun _ _ hr12 => ?_)
      refine reachesPrefix_not_normal_of_step rfl hr12 (fun _ _ hr13 => ?_)
      exact reachesPrefix_not_normal_of_unwind rfl hr13

/-- Because `MonoAdmitted` is part of `initMirState` (`MirMachine.initState`),
    `transmuteCheckedBody` satisfies the unconditional specification
    `EnsuresRetLibInv defaultAdtInv (.param 1) (fun _ => True)`: rejected
    monomorphizations (`tySizes 0 ≠ tySizes 1`) have `initMirState = False`
    ($\bot$), while admitted monomorphizations (`tySizes 0 = tySizes 1`) execute
    `transmute_copy` without UB and return a valid `Dst` byte value. -/
theorem transmuteCheckedBody_satisfies_retSpec :
    MirSem transmuteCheckedBody ≤
      EnsuresRetLibInv defaultAdtInv (.param 1) (fun _ => True) := by
  refine behaviorOf_le_spec (M := MirMachine) ?_
  intro q out hpfx
  cases q with
  | mk init steps =>
  cases init with
  | mk locals0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
  cases out with
  | mk trace outcome =>
    have hinit := hpfx.1.1
    have hmono := hpfx.1.2
    have hreach := hpfx.2
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    subst hb hs hc hst
    have hconst : ConstSucceeds tySizes0 sizeEqConstBody :=
      hmono tySizes0 sizeEqConstBody (.direct (.head _))
    have heq : tySizes0 0 = tySizes0 1 :=
      constSucceeds_sizeEqConstBody_imp_eq tySizes0 hconst
    cases hinit.2.2.2.2.2.1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty : v.hasTy tySizes0 (.param 0) := hv.2
      cases v with
      | usize _ => cases hvty
      | bool _ => cases hvty
      | unit => cases hvty
      | adt _ _ => cases hvty
      | ref _ => cases hvty
      | bytes vSz bits =>
        have hvSz : vSz = tySizes0 0 := hvty
        subst hvSz
        refine reachesPrefix_safeAndEnsures_of_step rfl hreach (fun _ _ hr1 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr1 (fun _ _ hr2 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr2 (fun _ _ hr3 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr3 (fun _ _ hr4 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr4 (fun _ _ hr5 => ?_)
        let l5 := updateLocal (updateLocal (updateLocal (updateLocal
          (updateLocal locals0 2 none) 2 (some .unit)) 2 none) 3 none) 4 none
        have hl5_1 : l5 1 = some (.bytes (tySizes0 0) bits) := by
          change (if 1 == 4 then none else if 1 == 3 then none else if 1 == 2 then none
            else if 1 == 2 then some MirVal.unit else if 1 == 2 then none else locals0 1) = _
          exact hv1
        let s5 : MirState := { locals := l5, block := 0, stmtIdx := 5, tySizes := tySizes0 }
        let s6 : MirState := { s5 with locals := updateLocal l5 4 (some (.ref ⟨1⟩)), stmtIdx := 6 }
        have hstep5 : evalMirStep transmuteCheckedBody s5 = .step () s6 := by
          change evalMirStmt s5 (.assign ⟨4⟩ (.ref ⟨1⟩)) = .step () s6
          dsimp only [evalMirStmt, s5]
          rw [hl5_1]
        refine reachesPrefix_safeAndEnsures_of_step hstep5 hr5 (fun _ _ hr6 => ?_)
        let l6 := updateLocal l5 4 (some (.ref ⟨1⟩))
        have hl6_1 : l6 1 = some (.bytes (tySizes0 0) bits) := by
          change (if 1 == 4 then some (MirVal.ref ⟨1⟩) else l5 1) = _
          exact hl5_1
        let s7 : MirState := { s6 with locals := updateLocal l6 3 (some (.ref ⟨1⟩)), stmtIdx := 7 }
        have hstep6 : evalMirStep transmuteCheckedBody s6 = .step () s7 := by
          change (match l6 1 with
            | some _ => StepResult.step () s7
            | none => StepResult.failed) = .step () s7
          rw [hl6_1]
        refine reachesPrefix_safeAndEnsures_of_step hstep6 hr6 (fun _ _ hr7 => ?_)
        let l7_deinit := updateLocal (updateLocal l6 3 (some (.ref ⟨1⟩))) 3 none
        have hl7_1 : l7_deinit 1 = some (.bytes (tySizes0 0) bits) := by
          change (if 1 == 3 then none else if 1 == 3 then some (MirVal.ref ⟨1⟩) else l6 1) = _
          exact hl6_1
        have hdec_eq : decide (tySizes0 0 = tySizes0 1) = true := decide_eq_true heq
        have hdec_refl : decide (tySizes0 0 = tySizes0 0) = true := decide_eq_true rfl
        let s8 : MirState := {
          s7 with
          locals := updateLocal l7_deinit 0 (some (.bytes (tySizes0 1) bits))
          block := 1
          stmtIdx := 0
        }
        have hstep7 : evalMirStep transmuteCheckedBody s7 = .step () s8 := by
          change evalMirTerminator transmuteCheckedBody s7
            (.callTransmuteCopy ⟨0⟩ (.param 0) (.param 1) (.move ⟨3⟩) ⟨1⟩) = .step () s8
          dsimp only [evalMirTerminator, evalOperand, evalTransmuteCopy, evalTyByteSize, s7]
          change (match (if decide (tySizes0 0 = tySizes0 1) then
              match l7_deinit 1 with
              | some (.bytes vSz b) =>
                if decide (vSz = tySizes0 0) then some (MirVal.bytes (tySizes0 1) b) else none
              | _ => none
            else none) with
            | some outVal => StepResult.step () { s7 with locals := updateLocal l7_deinit 0 (some outVal), block := 1, stmtIdx := 0 }
            | none => StepResult.failed) = .step () s8
          rw [hdec_eq, hl7_1]
          dsimp only
          rw [hdec_refl]
          rfl
        refine reachesPrefix_safeAndEnsures_of_step hstep7 hr7 (fun _ _ hr8 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr8 (fun _ _ hr9 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr9 (fun _ _ hr10 => ?_)
        exact reachesPrefix_safeAndEnsures_of_normal
          (v := .bytes (tySizes0 1) bits) rfl hr10 rfl

/-- `transmuteCheckedBody` satisfies unconditional `MirLang.WellFormed`. -/
theorem transmuteCheckedBody_satisfies_wellFormed :
    MirSem transmuteCheckedBody ≤ MirLang.WellFormed :=
  Preorder.le_trans transmuteCheckedBody_satisfies_retSpec
    (spec_le_wellFormed (L := MirLang) _)

/-- `transmuteCheckedBody` satisfies `EnsuresRetLibInv defaultAdtInv (.param 1)`
    on its canonical `effectivePre`. -/
theorem transmuteCheckedBody_verified (fnName : String) :
    let fn : CapturedFn := { name := fnName, prog := transmuteCheckedBody }
    MirSem fn.prog ≤
      EnsuresRetLibInv defaultAdtInv fn.prog.retTy
        (fn.effectivePre defaultAdtInv) :=
  Preorder.le_trans transmuteCheckedBody_satisfies_retSpec
    (spec_le_specOn (L := MirLang) _ _)

/-- `outerTransmuteBody` (whose own `requiredConsts` is `[]`, but which calls
    `transmuteCheckedBody` via `Terminator.call1`) satisfies unconditional
    `EnsuresRetLibInv defaultAdtInv (.param 1) (fun _ => True)` because
    `RequiresConst` transitively collects `sizeEqConstBody` from
    `transmuteCheckedBody`. -/
theorem outerTransmuteBody_satisfies_retSpec :
    MirSem outerTransmuteBody ≤
      EnsuresRetLibInv defaultAdtInv (.param 1) (fun _ => True) := by
  refine behaviorOf_le_spec (M := MirMachine) ?_
  intro q out hpfx
  cases q with
  | mk init steps =>
  cases init with
  | mk locals0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
  cases out with
  | mk trace outcome =>
    have hinit := hpfx.1.1
    have hmono := hpfx.1.2
    have hreach := hpfx.2
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    subst hb hs hc hst
    have hreq :
        RequiresConst tySizes0 outerTransmuteBody
          (substTySizes tySizes0 []) sizeEqConstBody :=
      .call1 (.head _) rfl (.direct (.head _))
    have hconst : ConstSucceeds (substTySizes tySizes0 []) sizeEqConstBody :=
      hmono (substTySizes tySizes0 []) sizeEqConstBody hreq
    have heq : tySizes0 0 = tySizes0 1 :=
      constSucceeds_sizeEqConstBody_imp_eq (substTySizes tySizes0 []) hconst
    cases hinit.2.2.2.2.2.1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty : v.hasTy tySizes0 (.param 0) := hv.2
      cases v with
      | usize _ => cases hvty
      | bool _ => cases hvty
      | unit => cases hvty
      | adt _ _ => cases hvty
      | ref _ => cases hvty
      | bytes vSz bits =>
        have hvSz : vSz = tySizes0 0 := hvty
        subst hvSz
        refine reachesPrefix_safeAndEnsures_of_step rfl hreach (fun _ _ hr1 => ?_)
        let l_outer1 := updateLocal locals0 2 none
        have hl_outer1_1 : l_outer1 1 = some (.bytes (tySizes0 0) bits) := by
          change (if 1 == 2 then none else locals0 1) = _
          exact hv1
        let s_outer1 : MirState := { locals := l_outer1, block := 0, stmtIdx := 1, tySizes := tySizes0 }
        let l_outer2 := updateLocal l_outer1 2 (some (.bytes (tySizes0 0) bits))
        let s_outer2 : MirState := { s_outer1 with locals := l_outer2, stmtIdx := 2 }
        have hstep_o1 : evalMirStep outerTransmuteBody s_outer1 = .step () s_outer2 := by
          change evalMirStmt s_outer1 (.assign ⟨2⟩ (.use (.copy ⟨1⟩))) = .step () s_outer2
          dsimp only [evalMirStmt, evalOperand, s_outer1]
          rw [hl_outer1_1]
        refine reachesPrefix_safeAndEnsures_of_step hstep_o1 hr1 (fun _ _ hr2 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr2 (fun _ _ hr3 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr3 (fun _ _ hr4 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr4 (fun _ _ hr5 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr5 (fun _ _ hr6 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr6 (fun _ _ hr7 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr7 (fun _ _ hr8 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr8 (fun _ _ hr9 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr9 (fun _ _ hr10 => ?_)
        let calleeLocals0 := updateLocal (fun _ => none) 1 (some (.bytes (tySizes0 0) bits))
        let cl5 := updateLocal (updateLocal (updateLocal (updateLocal
          (updateLocal calleeLocals0 2 none) 2 (some .unit)) 2 none) 3 none) 4 none
        let cl6 := updateLocal cl5 4 (some (.ref ⟨1⟩))
        let cl7_deinit := updateLocal (updateLocal cl6 3 (some (.ref ⟨1⟩))) 3 none
        let frame : StackFrame := {
          callerBody := outerTransmuteBody
          callerLocals := updateLocal l_outer2 2 none
          callerTySizes := tySizes0
          retDst := ⟨0⟩
          retBlock := 1
        }
        let s_c7 : MirState := {
          locals := updateLocal cl6 3 (some (.ref ⟨1⟩))
          block := 0
          stmtIdx := 7
          tySizes := substTySizes tySizes0 []
          curBody := some transmuteCheckedBody
          stack := [frame]
        }
        let s_c8 : MirState := {
          s_c7 with
          locals := updateLocal cl7_deinit 0 (some (.bytes (tySizes0 1) bits))
          block := 1
          stmtIdx := 0
        }
        have hdec_eq : decide (tySizes0 0 = tySizes0 1) = true := decide_eq_true heq
        have hdec_refl : decide (tySizes0 0 = tySizes0 0) = true := decide_eq_true rfl
        have hstep_c7 : evalMirStep outerTransmuteBody s_c7 = .step () s_c8 := by
          change evalMirTerminator transmuteCheckedBody s_c7
            (.callTransmuteCopy ⟨0⟩ (.param 0) (.param 1) (.move ⟨3⟩) ⟨1⟩) = .step () s_c8
          dsimp only [evalMirTerminator, evalOperand, evalTransmuteCopy, evalTyByteSize, substTySizes, s_c7]
          change (match (if decide (tySizes0 0 = tySizes0 1) then
              if decide (tySizes0 0 = tySizes0 0) then some (MirVal.bytes (tySizes0 1) bits) else none
            else none) with
            | some outVal => StepResult.step () { s_c7 with locals := updateLocal cl7_deinit 0 (some outVal), block := 1, stmtIdx := 0 }
            | none => StepResult.failed) = .step () s_c8
          rw [hdec_eq, hdec_refl]
          rfl
        refine reachesPrefix_safeAndEnsures_of_step hstep_c7 hr10 (fun _ _ hr11 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr11 (fun _ _ hr12 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr12 (fun _ _ hr13 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr13 (fun _ _ hr14 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr14 (fun _ _ hr15 => ?_)
        exact reachesPrefix_safeAndEnsures_of_normal
          (v := .bytes (tySizes0 1) bits) rfl hr15 rfl

/-- `outerTransmuteBody` satisfies `EnsuresRetLibInv defaultAdtInv (.param 1)`
    on its canonical `effectivePre`. -/
theorem outerTransmuteBody_verified (fnName : String) :
    let fn : CapturedFn := { name := fnName, prog := outerTransmuteBody }
    MirSem fn.prog ≤
      EnsuresRetLibInv defaultAdtInv fn.prog.retTy
        (fn.effectivePre defaultAdtInv) :=
  Preorder.le_trans outerTransmuteBody_satisfies_retSpec
    (spec_le_specOn (L := MirLang) _ _)

/-- `swappedOuterTransmuteBody` (calling `transmuteCheckedBody` with swapped
    type arguments `typeArgs := [.param 1, .param 0]`) satisfies unconditional
    `EnsuresRetLibInv defaultAdtInv (.param 0) (fun _ => True)`:
    `RequiresConst.call1` evaluates `sizeEqConstBody` under
    `substTySizes tySizes0 [.param 1, .param 0]`, yielding
    `tySizes0 1 = tySizes0 0`. -/
theorem swappedOuterTransmuteBody_satisfies_retSpec :
    MirSem swappedOuterTransmuteBody ≤
      EnsuresRetLibInv defaultAdtInv (.param 0) (fun _ => True) := by
  refine behaviorOf_le_spec (M := MirMachine) ?_
  intro q out hpfx
  cases q with
  | mk init steps =>
  cases init with
  | mk locals0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
  cases out with
  | mk trace outcome =>
    have hinit := hpfx.1.1
    have hmono := hpfx.1.2
    have hreach := hpfx.2
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    subst hb hs hc hst
    let subSz := substTySizes tySizes0 [.param 1, .param 0]
    have hreq :
        RequiresConst tySizes0 swappedOuterTransmuteBody subSz sizeEqConstBody :=
      .call1 (.head _) rfl (.direct (.head _))
    have hconst : ConstSucceeds subSz sizeEqConstBody :=
      hmono subSz sizeEqConstBody hreq
    have heq : tySizes0 1 = tySizes0 0 :=
      constSucceeds_sizeEqConstBody_imp_eq subSz hconst
    cases hinit.2.2.2.2.2.1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty : v.hasTy tySizes0 (.param 1) := hv.2
      cases v with
      | usize _ => cases hvty
      | bool _ => cases hvty
      | unit => cases hvty
      | adt _ _ => cases hvty
      | ref _ => cases hvty
      | bytes vSz bits =>
        have hvSz : vSz = tySizes0 1 := hvty
        subst hvSz
        refine reachesPrefix_safeAndEnsures_of_step rfl hreach (fun _ _ hr1 => ?_)
        let l_outer1 := updateLocal locals0 2 none
        have hl_outer1_1 : l_outer1 1 = some (.bytes (tySizes0 1) bits) := by
          change (if 1 == 2 then none else locals0 1) = _
          exact hv1
        let s_outer1 : MirState := { locals := l_outer1, block := 0, stmtIdx := 1, tySizes := tySizes0 }
        let l_outer2 := updateLocal l_outer1 2 (some (.bytes (tySizes0 1) bits))
        let s_outer2 : MirState := { s_outer1 with locals := l_outer2, stmtIdx := 2 }
        have hstep_o1 : evalMirStep swappedOuterTransmuteBody s_outer1 = .step () s_outer2 := by
          change evalMirStmt s_outer1 (.assign ⟨2⟩ (.use (.copy ⟨1⟩))) = .step () s_outer2
          dsimp only [evalMirStmt, evalOperand, s_outer1]
          rw [hl_outer1_1]
        refine reachesPrefix_safeAndEnsures_of_step hstep_o1 hr1 (fun _ _ hr2 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr2 (fun _ _ hr3 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr3 (fun _ _ hr4 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr4 (fun _ _ hr5 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr5 (fun _ _ hr6 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr6 (fun _ _ hr7 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr7 (fun _ _ hr8 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr8 (fun _ _ hr9 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr9 (fun _ _ hr10 => ?_)
        let calleeLocals0 := updateLocal (fun _ => none) 1 (some (.bytes (tySizes0 1) bits))
        let cl5 := updateLocal (updateLocal (updateLocal (updateLocal
          (updateLocal calleeLocals0 2 none) 2 (some .unit)) 2 none) 3 none) 4 none
        let cl6 := updateLocal cl5 4 (some (.ref ⟨1⟩))
        let cl7_deinit := updateLocal (updateLocal cl6 3 (some (.ref ⟨1⟩))) 3 none
        let frame : StackFrame := {
          callerBody := swappedOuterTransmuteBody
          callerLocals := updateLocal l_outer2 2 none
          callerTySizes := tySizes0
          retDst := ⟨0⟩
          retBlock := 1
        }
        let s_c7 : MirState := {
          locals := updateLocal cl6 3 (some (.ref ⟨1⟩))
          block := 0
          stmtIdx := 7
          tySizes := subSz
          curBody := some transmuteCheckedBody
          stack := [frame]
        }
        let s_c8 : MirState := {
          s_c7 with
          locals := updateLocal cl7_deinit 0 (some (.bytes (tySizes0 0) bits))
          block := 1
          stmtIdx := 0
        }
        have hdec_eq : decide (tySizes0 1 = tySizes0 0) = true := decide_eq_true heq
        have hdec_refl : decide (tySizes0 1 = tySizes0 1) = true := decide_eq_true rfl
        have hstep_c7 : evalMirStep swappedOuterTransmuteBody s_c7 = .step () s_c8 := by
          change evalMirTerminator transmuteCheckedBody s_c7
            (.callTransmuteCopy ⟨0⟩ (.param 0) (.param 1) (.move ⟨3⟩) ⟨1⟩) = .step () s_c8
          dsimp only [evalMirTerminator, evalOperand, evalTransmuteCopy, evalTyByteSize, subSz, substTySizes, s_c7]
          change (match (if decide (tySizes0 1 = tySizes0 0) then
              if decide (tySizes0 1 = tySizes0 1) then some (MirVal.bytes (tySizes0 0) bits) else none
            else none) with
            | some outVal => StepResult.step () { s_c7 with locals := updateLocal cl7_deinit 0 (some outVal), block := 1, stmtIdx := 0 }
            | none => StepResult.failed) = .step () s_c8
          rw [hdec_eq, hdec_refl]
          rfl
        refine reachesPrefix_safeAndEnsures_of_step hstep_c7 hr10 (fun _ _ hr11 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr11 (fun _ _ hr12 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr12 (fun _ _ hr13 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr13 (fun _ _ hr14 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr14 (fun _ _ hr15 => ?_)
        exact reachesPrefix_safeAndEnsures_of_normal
          (v := .bytes (tySizes0 0) bits) rfl hr15 rfl

/-- Ready-to-apply `CrateTheorem` witness for a single-function PME library
    crate containing `transmute_checked` (either via associated const `ASSERT`
    or inline `const { assert!(...) }`). -/
theorem prove_pme_transmute_single_crate (fnName : String) :
    CrateTheorem {
      functions := [{ name := fnName, prog := transmuteCheckedBody }]
      tcb := [TCBItem.rustcLowering fnName transmuteCheckedBody]
    } :=
  verify_single_fn_wf_crate fnName transmuteCheckedBody
    (transmuteCheckedBody_verified fnName)

/-- Ready-to-apply `CrateTheorem` witness for a two-function PME library crate
    containing `transmute_checked` and its generic wrapper `outer_transmute`. -/
theorem prove_pme_transmute_crate (fn1Name fn2Name : String) :
    CrateTheorem {
      functions := [
        { name := fn1Name, prog := transmuteCheckedBody },
        { name := fn2Name, prog := outerTransmuteBody }
      ]
      tcb := [
        TCBItem.rustcLowering fn1Name transmuteCheckedBody,
        TCBItem.rustcLowering fn2Name outerTransmuteBody
      ]
    } := by
  refine ⟨(by intro h; cases h), defaultAdtInv_admissible [], True.intro, ?_⟩
  refine ⟨⟨⟨True.intro, True.intro, True.intro⟩, ?_⟩,
           ⟨⟨True.intro, True.intro, True.intro⟩, ?_⟩,
           True.intro⟩
  · intro hTcb
    exact Compiler.Verified.with_wellFormedOn
      (Compiler.SoundOn.verify hTcb.1 (transmuteCheckedBody_verified fn1Name))
      (ensuresRetLibInv_le_wellFormedOn _ _ _)
      hTcb.1.1
  · intro hTcb
    exact Compiler.Verified.with_wellFormedOn
      (Compiler.SoundOn.verify hTcb.2.1 (outerTransmuteBody_verified fn2Name))
      (ensuresRetLibInv_le_wellFormedOn _ _ _)
      hTcb.2.1.1

/-- Negative PME adequacy canary: removing the PME assertion from
    `transmute_checked` (`transmuteUncheckedBody`, where `requiredConsts = []`)
    makes `MonoAdmitted` vacuously true on mismatched type sizes
    (`tySizes 0 = 8`, `tySizes 1 = 4`), causing `transmute_copy` to fail with
    `.failed` and refuting `CrateTheorem`. -/
theorem canary_transmuteUnchecked_rejected (fnName : String)
    (hSound : RustcCompiler.SoundOn transmuteUncheckedBody) :
    ¬ CrateTheorem {
      functions := [{ name := fnName, prog := transmuteUncheckedBody }]
      tcb := [TCBItem.rustcLowering fnName transmuteUncheckedBody]
    } := by
  intro hCrate
  have hFnVer := hCrate.2.2.2.1.2 ⟨hSound, True.intro⟩
  have hWF := hFnVer.1.1
  let tySizesBad : Nat → Nat := fun idx => if idx == 0 then 8 else 4
  let locals0 : Nat → Option MirVal :=
    updateLocal (fun _ => none) 1 (some (.bytes 8 42))
  let s0 : MirState := {
    locals := locals0
    block := 0
    stmtIdx := 0
    tySizes := tySizesBad
  }
  have hrest : ∀ j, 2 ≤ j → locals0 j = none := by
    intro j hj
    cases j with
    | zero => cases hj
    | succ k =>
      cases k with
      | zero => cases hj with | step hle => cases hle
      | succ _ => rfl
  have hentry : initEntryState transmuteUncheckedBody s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, ⟨⟨.bytes 8 42, rfl, rfl⟩, hrest⟩⟩
  have hmono : MonoAdmitted tySizesBad transmuteUncheckedBody := by
    intro _ _ hc
    cases hc with
    | direct hmem => cases hmem
    | nested hmem _ => cases hmem
    | call1 hbb hterm _ =>
      cases hbb with
      | head => cases hterm
      | tail _ hbb1 =>
        cases hbb1 with
        | head => cases hterm
        | tail _ hnil => cases hnil
  have hinit : initMirState transmuteUncheckedBody s0 := ⟨hentry, hmono⟩
  let q : ExecQuery MirState := { init := s0, steps := 5 }
  have hpre :
      CapturedFn.effectivePre defaultAdtInv
        { name := fnName, prog := transmuteUncheckedBody } q :=
    ⟨True.intro, ⟨⟨.bytes 8 42, rfl, rfl⟩, hrest⟩⟩
  let s1 : MirState := { s0 with locals := updateLocal locals0 2 none, stmtIdx := 1 }
  let s2 : MirState := { s1 with locals := updateLocal s1.locals 3 none, stmtIdx := 2 }
  let s3 : MirState := { s2 with locals := updateLocal s2.locals 3 (some (.ref ⟨1⟩)), stmtIdx := 3 }
  let s4 : MirState := { s3 with locals := updateLocal s3.locals 2 (some (.ref ⟨1⟩)), stmtIdx := 4 }
  have hr4 : ReachesPrefix MirStep transmuteUncheckedBody 1 s4 [] .failed :=
    ReachesPrefix.failed 0 s4 rfl
  have hr3 : ReachesPrefix MirStep transmuteUncheckedBody 2 s3 [()] .failed :=
    ReachesPrefix.step 1 s3 s4 () [] .failed rfl hr4
  have hr2 : ReachesPrefix MirStep transmuteUncheckedBody 3 s2 [(), ()] .failed :=
    ReachesPrefix.step 2 s2 s3 () [()] .failed rfl hr3
  have hr1 : ReachesPrefix MirStep transmuteUncheckedBody 4 s1 [(), (), ()] .failed :=
    ReachesPrefix.step 3 s1 s2 () [(), ()] .failed rfl hr2
  have hr0 : ReachesPrefix MirStep transmuteUncheckedBody 5 s0 [(), (), (), ()] .failed :=
    ReachesPrefix.step 4 s0 s1 () [(), (), ()] .failed rfl hr1
  exact (hWF q hpre).1 hinit [(), (), (), ()] .failed hr0

/-!
## 5. `NonZeroUsize` Library Verification Contract Lemmas and Canaries
-/

/-- Standard ADT representation invariant for a crate whose ADT `0`
    (`NonZeroUsize`) encapsulates a private non-zero `usize` field
    (`val != 0`). -/
abbrev nonZeroAdtInv : AdtInv :=
  fun id v =>
    match id, v with
    | 0, .usize n => n ≠ 0
    | _, _ => False

/-- Standard `# Safety` precondition for `pub unsafe fn new_unchecked(x: usize)
    -> NonZeroUsize`: the caller guarantees that argument `_1` is non-zero. -/
abbrev newUncheckedSafetyPre (q : ExecQuery MirState) : Prop :=
  ∀ n, q.init.locals 1 = some (.usize n) → n ≠ 0

/-- Captured ADT declaration for `pub struct NonZeroUsize { val: usize }` with a
    private field (`FieldAccess.priv`). -/
def nonZeroAdtDecl : AdtDecl where
  id := 0
  fields := [{ ty := .usize, access := .priv }]

/-- Captured ADT declaration for `pub struct NonZeroUsize { pub val: usize }`
    with a public safe field (`FieldAccess.pubSafe`). -/
def pubSafeNonZeroAdtDecl : AdtDecl where
  id := 0
  fields := [{ ty := .usize, access := .pubSafe }]

/-- `nonZeroAdtInv` is admissible for `[nonZeroAdtDecl]` because
    `NonZeroUsize`'s field is private (`allFieldsPubSafe = false`). -/
theorem nonZeroAdtInv_admissible :
    AdmissibleAdtInv [nonZeroAdtDecl] nonZeroAdtInv := by
  intro decl hmem hPub
  cases hmem with
  | head => cases hPub
  | tail _ hnil => cases hnil

/-- Negative adequacy canary: if `NonZeroUsize`'s field `val` is made `pub`
    (`pubSafeNonZeroAdtDecl`), then `nonZeroAdtInv` violates `AdmissibleAdtInv`
    because safe downstream callers can construct `NonZeroUsize { val: 0 }`! -/
theorem canary_pub_safe_fields_reject_nonzero_inv :
    ¬ AdmissibleAdtInv [pubSafeNonZeroAdtDecl] nonZeroAdtInv :=
  fun hAdm => hAdm pubSafeNonZeroAdtDecl (.head _) rfl 0 rfl

/-- Canonical `rustc -Z mir-opt-level=0 --emit=mir` body for
    `pub fn make_nonzero(x: usize) -> NonZeroUsize`:
    ```text
    bb0: {
        StorageLive(_2);
        StorageLive(_3);
        _3 = copy _1;
        _2 = Eq(move _3, const 0_usize);
        switchInt(move _2) -> [0: bb2, otherwise: bb1];
    }
    bb1: {
        StorageDead(_3);
        _0 = NonZeroUsize { val: const 1_usize };
        goto -> bb3;
    }
    bb2: {
        StorageDead(_3);
        StorageLive(_4);
        _4 = copy _1;
        _0 = NonZeroUsize { val: move _4 };
        StorageDead(_4);
        goto -> bb3;
    }
    bb3: {
        StorageDead(_2);
        return;
    }
    ``` -/
def makeNonZeroBody : MirBody where
  argTys := [.usize]
  retTy := .adt 0
  localCount := 5
  blocks := [
    { stmts := [
        .storageLive ⟨2⟩,
        .storageLive ⟨3⟩,
        .assign ⟨3⟩ (.use (.copy ⟨1⟩)),
        .assign ⟨2⟩ (.binaryOp .eq (.move ⟨3⟩) (.constVal (.usize 0)))
      ]
      terminator := .switchInt (.move ⟨2⟩) ⟨2⟩ ⟨1⟩ },
    { stmts := [
        .storageDead ⟨3⟩,
        .assign ⟨0⟩ (.aggregate 0 (.constVal (.usize 1)))
      ]
      terminator := .goto ⟨3⟩ },
    { stmts := [
        .storageDead ⟨3⟩,
        .storageLive ⟨4⟩,
        .assign ⟨4⟩ (.use (.copy ⟨1⟩)),
        .assign ⟨0⟩ (.aggregate 0 (.move ⟨4⟩)),
        .storageDead ⟨4⟩
      ]
      terminator := .goto ⟨3⟩ },
    { stmts := [.storageDead ⟨2⟩]
      terminator := .return_ }
  ]

/-- Canonical `rustc -Z mir-opt-level=0 --emit=mir` body for
    `pub unsafe fn new_unchecked(x: usize) -> NonZeroUsize`:
    ```text
    bb0: {
        StorageLive(_2);
        _2 = copy _1;
        _0 = NonZeroUsize { val: move _2 };
        StorageDead(_2);
        return;
    }
    ``` -/
def newUncheckedBody : MirBody where
  argTys := [.usize]
  retTy := .adt 0
  localCount := 3
  blocks := [
    { stmts := [
        .storageLive ⟨2⟩,
        .assign ⟨2⟩ (.use (.copy ⟨1⟩)),
        .assign ⟨0⟩ (.aggregate 0 (.move ⟨2⟩)),
        .storageDead ⟨2⟩
      ]
      terminator := .return_ }
  ]

/-- Canonical `rustc -Z mir-opt-level=0 --emit=mir` body for
    `pub fn get_unchecked_nonzero(x: NonZeroUsize) -> usize`:
    ```text
    bb0: {
        StorageLive(_2);
        StorageLive(_3);
        _3 = copy (_1.0: usize);
        _2 = Eq(move _3, const 0_usize);
        switchInt(move _2) -> [0: bb2, otherwise: bb1];
    }
    bb1: {
        StorageDead(_3);
        StorageLive(_4);
        _4 = unreachable_unchecked() -> unwind continue;
    }
    bb2: {
        StorageDead(_3);
        _0 = copy (_1.0: usize);
        StorageDead(_2);
        return;
    }
    ``` -/
def getUncheckedNonZeroBody : MirBody where
  argTys := [.adt 0]
  retTy := .usize
  localCount := 5
  blocks := [
    { stmts := [
        .storageLive ⟨2⟩,
        .storageLive ⟨3⟩,
        .assign ⟨3⟩ (.field0 ⟨1⟩),
        .assign ⟨2⟩ (.binaryOp .eq (.move ⟨3⟩) (.constVal (.usize 0)))
      ]
      terminator := .switchInt (.move ⟨2⟩) ⟨2⟩ ⟨1⟩ },
    { stmts := [.storageDead ⟨3⟩, .storageLive ⟨4⟩]
      terminator := .unreachable },
    { stmts := [
        .storageDead ⟨3⟩,
        .assign ⟨0⟩ (.field0 ⟨1⟩),
        .storageDead ⟨2⟩
      ]
      terminator := .return_ }
  ]

/-- Canonical `rustc -Z mir-opt-level=0 --emit=mir` body for a buggy safe
    constructor
    `pub fn buggy_zero(_x: usize) -> NonZeroUsize { NonZeroUsize { val: 0 } }`:
    ```text
    bb0: {
        _0 = NonZeroUsize { val: const 0_usize };
        return;
    }
    ``` -/
def buggyZeroBody : MirBody where
  argTys := [.usize]
  retTy := .adt 0
  localCount := 2
  blocks := [
    { stmts := [.assign ⟨0⟩ (.aggregate 0 (.constVal (.usize 0)))]
      terminator := .return_ }
  ]

/-- `makeNonZeroBody` satisfies `EnsuresRetLibInv nonZeroAdtInv (.adt 0)`:
    whether `_1` is `0` (branching to `bb1` and wrapping `1`) or `k + 1`
    (branching to `bb2` and wrapping `k + 1`), the returned `NonZeroUsize`
    always satisfies `nonZeroAdtInv`. -/
theorem makeNonZeroBody_verified (fnName : String) :
    let fn : CapturedFn := { name := fnName, prog := makeNonZeroBody, kind := .pubSafe True }
    MirSem fn.prog ≤
      EnsuresRetLibInv nonZeroAdtInv fn.prog.retTy
        (fn.effectivePre nonZeroAdtInv) := by
  intro fn
  refine behaviorOf_le_specOn (M := MirMachine) ?_
  intro q out _ hpfx
  cases q with
  | mk init steps =>
  cases init with
  | mk locals0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
  cases out with
  | mk trace outcome =>
    have hinit := hpfx.1.1
    have hreach := hpfx.2
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    subst hb hs hc hst
    cases hinit.2.2.2.2.2.1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty : v.hasTy tySizes0 .usize := hv.2
      cases v with
      | bool _ => cases hvty
      | unit => cases hvty
      | adt _ _ => cases hvty
      | bytes _ _ => cases hvty
      | ref _ => cases hvty
      | usize n =>
        refine reachesPrefix_safeAndEnsures_of_step rfl hreach (fun _ _ hr1 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr1 (fun _ _ hr2 => ?_)
        let l2 := updateLocal (updateLocal locals0 2 none) 3 none
        have hl2_1 : l2 1 = some (.usize n) := by
          change (if 1 == 3 then none else if 1 == 2 then none else locals0 1) = _
          exact hv1
        let s2 : MirState := { locals := l2, block := 0, stmtIdx := 2, tySizes := tySizes0 }
        let l3 := updateLocal l2 3 (some (.usize n))
        let s3 : MirState := { s2 with locals := l3, stmtIdx := 3 }
        have hstep2 : evalMirStep makeNonZeroBody s2 = .step () s3 := by
          change evalMirStmt s2 (.assign ⟨3⟩ (.use (.copy ⟨1⟩))) = .step () s3
          dsimp only [evalMirStmt, evalOperand, s2]
          rw [hl2_1]
        refine reachesPrefix_safeAndEnsures_of_step hstep2 hr2 (fun _ _ hr3 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr3 (fun _ _ hr4 => ?_)
        cases n with
        | zero =>
          refine reachesPrefix_safeAndEnsures_of_step rfl hr4 (fun _ _ hr5 => ?_)
          refine reachesPrefix_safeAndEnsures_of_step rfl hr5 (fun _ _ hr6 => ?_)
          refine reachesPrefix_safeAndEnsures_of_step rfl hr6 (fun _ _ hr7 => ?_)
          refine reachesPrefix_safeAndEnsures_of_step rfl hr7 (fun _ _ hr8 => ?_)
          refine reachesPrefix_safeAndEnsures_of_step rfl hr8 (fun _ _ hr9 => ?_)
          exact reachesPrefix_safeAndEnsures_of_normal
            (v := .adt 0 (.usize 1)) rfl hr9 ⟨rfl, Nat.succ_ne_zero 0⟩
        | succ k =>
          refine reachesPrefix_safeAndEnsures_of_step rfl hr4 (fun _ _ hr5 => ?_)
          refine reachesPrefix_safeAndEnsures_of_step rfl hr5 (fun _ _ hr6 => ?_)
          refine reachesPrefix_safeAndEnsures_of_step rfl hr6 (fun _ _ hr7 => ?_)
          let l_bb2_2 := updateLocal (updateLocal (updateLocal
            (updateLocal (updateLocal l3 3 none) 2 (some (.bool false))) 2 none) 3 none) 4 none
          have hl_bb2_1 : l_bb2_2 1 = some (.usize (k + 1)) := by
            change (if 1 == 4 then none else if 1 == 3 then none else if 1 == 2 then none
              else if 1 == 2 then some (MirVal.bool false) else if 1 == 3 then none
              else if 1 == 3 then some (MirVal.usize (k + 1)) else l2 1) = _
            exact hl2_1
          let s_bb2_2 : MirState := { locals := l_bb2_2, block := 2, stmtIdx := 2, tySizes := tySizes0 }
          let s_bb2_3 : MirState := { s_bb2_2 with locals := updateLocal l_bb2_2 4 (some (.usize (k + 1))), stmtIdx := 3 }
          have hstep_bb2 : evalMirStep makeNonZeroBody s_bb2_2 = .step () s_bb2_3 := by
            change evalMirStmt s_bb2_2 (.assign ⟨4⟩ (.use (.copy ⟨1⟩))) = .step () s_bb2_3
            dsimp only [evalMirStmt, evalOperand, s_bb2_2]
            rw [hl_bb2_1]
          refine reachesPrefix_safeAndEnsures_of_step hstep_bb2 hr7 (fun _ _ hr8 => ?_)
          refine reachesPrefix_safeAndEnsures_of_step rfl hr8 (fun _ _ hr9 => ?_)
          refine reachesPrefix_safeAndEnsures_of_step rfl hr9 (fun _ _ hr10 => ?_)
          refine reachesPrefix_safeAndEnsures_of_step rfl hr10 (fun _ _ hr11 => ?_)
          refine reachesPrefix_safeAndEnsures_of_step rfl hr11 (fun _ _ hr12 => ?_)
          exact reachesPrefix_safeAndEnsures_of_normal
            (v := .adt 0 (.usize (k + 1))) rfl hr12 ⟨rfl, Nat.succ_ne_zero k⟩

/-- `newUncheckedBody` satisfies `EnsuresRetLibInv nonZeroAdtInv (.adt 0)`
    under `FnKind.pubUnsafe True newUncheckedSafetyPre`. -/
theorem newUncheckedBody_verified (fnName : String) :
    let fn : CapturedFn := {
      name := fnName
      prog := newUncheckedBody
      kind := .pubUnsafe True newUncheckedSafetyPre
    }
    MirSem fn.prog ≤
      EnsuresRetLibInv nonZeroAdtInv fn.prog.retTy
        (fn.effectivePre nonZeroAdtInv) := by
  intro fn
  refine behaviorOf_le_specOn (M := MirMachine) ?_
  intro q out hpre hpfx
  cases q with
  | mk init steps =>
  cases init with
  | mk locals0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
  cases out with
  | mk trace outcome =>
    have hinit := hpfx.1.1
    have hreach := hpfx.2
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    subst hb hs hc hst
    have hsafety : newUncheckedSafetyPre {
      init := { locals := locals0, block := 0, stmtIdx := 0, tySizes := tySizes0 }
      steps := steps
    } := hpre.2.2
    cases hinit.2.2.2.2.2.1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty : v.hasTy tySizes0 .usize := hv.2
      cases v with
      | bool _ => cases hvty
      | unit => cases hvty
      | adt _ _ => cases hvty
      | bytes _ _ => cases hvty
      | ref _ => cases hvty
      | usize n =>
        have hne0 : n ≠ 0 := hsafety n hv1
        refine reachesPrefix_safeAndEnsures_of_step rfl hreach (fun _ _ hr1 => ?_)
        let l1 := updateLocal locals0 2 none
        have hl1_1 : l1 1 = some (.usize n) := by
          change (if 1 == 2 then none else locals0 1) = _
          exact hv1
        let s1 : MirState := { locals := l1, block := 0, stmtIdx := 1, tySizes := tySizes0 }
        let s2 : MirState := { s1 with locals := updateLocal l1 2 (some (.usize n)), stmtIdx := 2 }
        have hstep1 : evalMirStep newUncheckedBody s1 = .step () s2 := by
          change evalMirStmt s1 (.assign ⟨2⟩ (.use (.copy ⟨1⟩))) = .step () s2
          dsimp only [evalMirStmt, evalOperand, s1]
          rw [hl1_1]
        refine reachesPrefix_safeAndEnsures_of_step hstep1 hr1 (fun _ _ hr2 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr2 (fun _ _ hr3 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr3 (fun _ _ hr4 => ?_)
        exact reachesPrefix_safeAndEnsures_of_normal
          (v := .adt 0 (.usize n)) rfl hr4 ⟨rfl, hne0⟩

/-- `getUncheckedNonZeroBody` satisfies `EnsuresRetLibInv nonZeroAdtInv .usize`
    under `FnKind.pubSafe True`: because `_1` satisfies
    `v.satisfiesInv nonZeroAdtInv tySizes (.adt 0)`, its inner `usize` is
    `k + 1 ≠ 0`, so `switchInt` never branches to `bb1`
    (`unreachable_unchecked()`) and always returns `k + 1` via `bb2`. -/
theorem getUncheckedNonZeroBody_verified (fnName : String) :
    let fn : CapturedFn := {
      name := fnName
      prog := getUncheckedNonZeroBody
      kind := .pubSafe True
    }
    MirSem fn.prog ≤
      EnsuresRetLibInv nonZeroAdtInv fn.prog.retTy
        (fn.effectivePre nonZeroAdtInv) := by
  intro fn
  refine behaviorOf_le_specOn (M := MirMachine) ?_
  intro q out hpre hpfx
  cases q with
  | mk init steps =>
  cases init with
  | mk locals0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
  cases out with
  | mk trace outcome =>
    have hinit := hpfx.1.1
    have hreach := hpfx.2
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    subst hb hs hc hst
    cases hpre.2.1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvinv : v.satisfiesInv nonZeroAdtInv tySizes0 (.adt 0) := hv.2
      cases v with
      | usize _ => cases hvinv
      | bool _ => cases hvinv
      | unit => cases hvinv
      | bytes _ _ => cases hvinv
      | ref _ => cases hvinv
      | adt adtId inner =>
        cases adtId with
        | succ _ =>
          cases inner with
          | bool _ => cases hvinv
          | unit => cases hvinv
          | adt _ _ => cases hvinv
          | bytes _ _ => cases hvinv
          | ref _ => cases hvinv
          | usize _ => cases hvinv.1
        | zero =>
          cases inner with
          | bool _ => cases hvinv
          | unit => cases hvinv
          | adt _ _ => cases hvinv
          | bytes _ _ => cases hvinv
          | ref _ => cases hvinv
          | usize n =>
            cases n with
            | zero => exact False.elim (hvinv.2 rfl)
            | succ k =>
              refine reachesPrefix_safeAndEnsures_of_step rfl hreach (fun _ _ hr1 => ?_)
              refine reachesPrefix_safeAndEnsures_of_step rfl hr1 (fun _ _ hr2 => ?_)
              let l2 := updateLocal (updateLocal locals0 2 none) 3 none
              have hl2_1 : l2 1 = some (.adt 0 (.usize (k + 1))) := by
                change (if 1 == 3 then none else if 1 == 2 then none else locals0 1) = _
                exact hv1
              let s2 : MirState := { locals := l2, block := 0, stmtIdx := 2, tySizes := tySizes0 }
              let l3 := updateLocal l2 3 (some (.usize (k + 1)))
              let s3 : MirState := { s2 with locals := l3, stmtIdx := 3 }
              have hstep2 : evalMirStep getUncheckedNonZeroBody s2 = .step () s3 := by
                change evalMirStmt s2 (.assign ⟨3⟩ (.field0 ⟨1⟩)) = .step () s3
                dsimp only [evalMirStmt, s2]
                rw [hl2_1]
              refine reachesPrefix_safeAndEnsures_of_step hstep2 hr2 (fun _ _ hr3 => ?_)
              refine reachesPrefix_safeAndEnsures_of_step rfl hr3 (fun _ _ hr4 => ?_)
              refine reachesPrefix_safeAndEnsures_of_step rfl hr4 (fun _ _ hr5 => ?_)
              refine reachesPrefix_safeAndEnsures_of_step rfl hr5 (fun _ _ hr6 => ?_)
              let l_bb2_1 := updateLocal (updateLocal (updateLocal
                (updateLocal l3 3 none) 2 (some (.bool false))) 2 none) 3 none
              have hl_bb2_1 : l_bb2_1 1 = some (.adt 0 (.usize (k + 1))) := by
                change (if 1 == 3 then none else if 1 == 2 then none
                  else if 1 == 2 then some (MirVal.bool false) else if 1 == 3 then none
                  else if 1 == 3 then some (MirVal.usize (k + 1)) else l2 1) = _
                exact hl2_1
              let s_bb2_1 : MirState := { locals := l_bb2_1, block := 2, stmtIdx := 1, tySizes := tySizes0 }
              let s_bb2_2 : MirState := { s_bb2_1 with locals := updateLocal l_bb2_1 0 (some (.usize (k + 1))), stmtIdx := 2 }
              have hstep_bb2 : evalMirStep getUncheckedNonZeroBody s_bb2_1 = .step () s_bb2_2 := by
                change evalMirStmt s_bb2_1 (.assign ⟨0⟩ (.field0 ⟨1⟩)) = .step () s_bb2_2
                dsimp only [evalMirStmt, s_bb2_1]
                rw [hl_bb2_1]
              refine reachesPrefix_safeAndEnsures_of_step hstep_bb2 hr6 (fun _ _ hr7 => ?_)
              refine reachesPrefix_safeAndEnsures_of_step rfl hr7 (fun _ _ hr8 => ?_)
              exact reachesPrefix_safeAndEnsures_of_normal
                (v := .usize (k + 1)) rfl hr8 True.intro

/-- Ready-to-apply `CrateTheorem` witness for the 3-function `NonZeroUsize`
    library crate (`make_nonzero`, `new_unchecked`, `get_unchecked_nonzero`). -/
theorem prove_nonzero_library_crate (fn1Name fn2Name fn3Name : String) :
    CrateTheorem {
      adts := [nonZeroAdtDecl]
      adtInv := nonZeroAdtInv
      functions := [
        { name := fn1Name, prog := makeNonZeroBody, kind := .pubSafe True },
        { name := fn2Name, prog := newUncheckedBody, kind := .pubUnsafe True newUncheckedSafetyPre },
        { name := fn3Name, prog := getUncheckedNonZeroBody, kind := .pubSafe True }
      ]
      tcb := [
        TCBItem.rustcLowering fn1Name makeNonZeroBody,
        TCBItem.rustcLowering fn2Name newUncheckedBody,
        TCBItem.rustcLowering fn3Name getUncheckedNonZeroBody
      ]
    } := by
  refine ⟨(by intro h; cases h), nonZeroAdtInv_admissible, True.intro, ?_⟩
  refine ⟨⟨⟨True.intro, True.intro, True.intro, True.intro⟩, ?_⟩,
          ⟨⟨True.intro, True.intro, True.intro, True.intro⟩, ?_⟩,
          ⟨⟨True.intro, True.intro, True.intro, True.intro⟩, ?_⟩,
          True.intro⟩
  · intro hTcb
    exact Compiler.Verified.with_wellFormedOn
      (Compiler.SoundOn.verify hTcb.1 (makeNonZeroBody_verified fn1Name))
      (ensuresRetLibInv_le_wellFormedOn _ _ _)
      hTcb.1.1
  · intro hTcb
    exact Compiler.Verified.with_wellFormedOn
      (Compiler.SoundOn.verify hTcb.2.1 (newUncheckedBody_verified fn2Name))
      (ensuresRetLibInv_le_wellFormedOn _ _ _)
      hTcb.2.1.1
  · intro hTcb
    exact Compiler.Verified.with_wellFormedOn
      (Compiler.SoundOn.verify hTcb.2.2.1 (getUncheckedNonZeroBody_verified fn3Name))
      (ensuresRetLibInv_le_wellFormedOn _ _ _)
      hTcb.2.2.1.1

/-- Negative library adequacy canary: a safe function `buggy_zero` that returns
    `NonZeroUsize { val: 0 }` violates `EnsuresRetLibInv nonZeroAdtInv (.adt 0)`
    and refutes `CrateTheorem`. -/
theorem canary_buggy_zero_rejected (fnName : String)
    (hSound : RustcCompiler.SoundOn buggyZeroBody) :
    ¬ CrateTheorem {
      adts := [nonZeroAdtDecl]
      adtInv := nonZeroAdtInv
      functions := [{ name := fnName, prog := buggyZeroBody, kind := .pubSafe True }]
      tcb := [TCBItem.rustcLowering fnName buggyZeroBody]
    } := by
  intro hCrate
  have hFnVer := hCrate.2.2.2.1.2 ⟨hSound, True.intro⟩
  have hRetInv := hFnVer.2.1.1
  let locals0 : Nat → Option MirVal :=
    updateLocal (fun _ => none) 1 (some (.usize 0))
  let s0 : MirState := { locals := locals0, block := 0, stmtIdx := 0 }
  let s1 : MirState := {
    locals := updateLocal locals0 0 (some (.adt 0 (.usize 0)))
    block := 0
    stmtIdx := 1
  }
  have hrest : ∀ j, 2 ≤ j → locals0 j = none := by
    intro j hj
    cases j with
    | zero => cases hj
    | succ k =>
      cases k with
      | zero => cases hj with | step hle => cases hle
      | succ _ => rfl
  have hentry : initEntryState buggyZeroBody s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, ⟨⟨.usize 0, rfl, True.intro⟩, hrest⟩⟩
  have hmono : MonoAdmitted (fun _ => 0) buggyZeroBody := by
    intro _ _ hc
    cases hc with
    | direct hmem => cases hmem
    | nested hmem _ => cases hmem
    | call1 hbb hterm _ =>
      cases hbb with
      | head => cases hterm
      | tail _ hnil => cases hnil
  have hinit : initMirState buggyZeroBody s0 := ⟨hentry, hmono⟩
  have hreach1 :
      ReachesPrefix MirStep buggyZeroBody 1 s1 []
        (.terminated (.normal (MirVal.adt 0 (.usize 0)))) :=
    ReachesPrefix.terminated 0 s1 (.normal (MirVal.adt 0 (.usize 0))) rfl
  have hreach2 :
      ReachesPrefix MirStep buggyZeroBody 2 s0 [()]
        (.terminated (.normal (MirVal.adt 0 (.usize 0)))) :=
    ReachesPrefix.step 1 s0 s1 () []
      (.terminated (.normal (MirVal.adt 0 (.usize 0)))) rfl hreach1
  let q : ExecQuery MirState := { init := s0, steps := 2 }
  let out : ExecOut Unit MirVal := {
    trace := [()]
    outcome := .terminated (.normal (.adt 0 (.usize 0)))
  }
  have hpre :
      CapturedFn.effectivePre nonZeroAdtInv
        { name := fnName, prog := buggyZeroBody, kind := .pubSafe True } q :=
    ⟨True.intro, ⟨⟨.usize 0, rfl, True.intro⟩, hrest⟩⟩
  cases hRetInv q hpre with
  | intro hdef hval =>
    have hpfx : (MirSem buggyZeroBody q).val hdef out := ⟨hinit, hreach2⟩
    have hinv :
        (MirVal.adt 0 (.usize 0)).satisfiesInv nonZeroAdtInv (fun _ => 0) (.adt 0) :=
      hval out hpfx (.adt 0 (.usize 0)) rfl
    exact hinv.2 rfl

/-!
## 6. Baseline Positive and Negative Rust Adequacy Canaries
-/

/-- Pure infinite loop MIR body (`bb0: { goto -> bb0; }`). -/
def loopBody : MirBody where
  argTys := []
  retTy := .unit
  localCount := 1
  blocks := [{ stmts := [], terminator := .goto ⟨0⟩ }]

theorem loopBody_reaches_running (n : Nat) :
    ∀ (s : MirState) (tr : List Unit) (out : PrefixOutcome MirVal),
      s.block = 0 → s.stmtIdx = 0 → s.curBody = none →
      ReachesPrefix MirStep loopBody n s tr out →
      out = PrefixOutcome.running := by
  induction n with
  | zero =>
    intro s tr out _ _ _ hreach
    cases hreach with
    | zero => rfl
  | succ k ih =>
    intro s tr out hb hs hc hreach
    have hstep0 :
        evalMirStep loopBody s = StepResult.step () { s with block := 0, stmtIdx := 0 } := by
      cases s with
      | mk locals block stmtIdx tySizes curBody stack =>
        dsimp at hb hs hc
        subst hb hs hc
        rfl
    cases hreach with
    | step _ _ s' obs tr' _ h1 h2 =>
      have h1' : StepResult.step obs s' = evalMirStep loopBody s := h1
      rw [hstep0] at h1'
      injection h1' with _ hs'
      subst hs'
      exact ih { s with block := 0, stmtIdx := 0 } tr' out rfl rfl hc h2
    | choice _ _ _ _ _ _ h1 _ _ =>
      have h1' : _ = evalMirStep loopBody s := h1
      rw [hstep0] at h1'
      cases h1'
    | emptyChoice _ _ _ h1 _ =>
      have h1' : _ = evalMirStep loopBody s := h1
      rw [hstep0] at h1'
      cases h1'
    | terminated _ _ _ h1 =>
      have h1' : _ = evalMirStep loopBody s := h1
      rw [hstep0] at h1'
      cases h1'
    | failed _ _ h1 =>
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
  have hout := loopBody_reaches_running steps init tr out
    hinit.1.1 hinit.1.2.1 hinit.1.2.2.1 hreach
  rw [hout]
  exact True.intro

/-- MIR body that returns immediately without initializing `_0`. -/
def uninitReturnBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 1
  blocks := [{ stmts := [], terminator := .return_ }]

/-- Negative adequacy canary: returning an uninitialized `_0`
    triggers `.failed` at step `1` and therefore refutes
    `MirLang.WellFormed`. -/
theorem canary_uninit_return_violates_wellFormed :
    ¬ (MirSem uninitReturnBody ≤ MirLang.WellFormed) := by
  intro hWF
  let s0 : MirState := { locals := fun _ => none, block := 0, stmtIdx := 0 }
  have hentry : initEntryState uninitReturnBody s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  have hmono : MonoAdmitted (fun _ => 0) uninitReturnBody := by
    intro _ _ hc
    cases hc with
    | direct hmem => cases hmem
    | nested hmem _ => cases hmem
    | call1 hbb hterm _ =>
      cases hbb with
      | head => cases hterm
      | tail _ hnil => cases hnil
  have hinit : initMirState uninitReturnBody s0 := ⟨hentry, hmono⟩
  have hfail : ReachesPrefix MirStep uninitReturnBody 1 s0 [] PrefixOutcome.failed :=
    ReachesPrefix.failed 0 s0 rfl
  exact (behaviorOf_le_wellFormed_iff (M := MirMachine)).mp hWF s0 1 [] .failed hinit hfail

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
  have hentry : initEntryState wrongReturnZeroBody s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, ⟨⟨MirVal.usize 1, rfl, True.intro⟩, hrest⟩⟩
  have hmono : MonoAdmitted (fun _ => 0) wrongReturnZeroBody := by
    intro _ _ hc
    cases hc with
    | direct hmem => cases hmem
    | nested hmem _ => cases hmem
    | call1 hbb hterm _ =>
      cases hbb with
      | head => cases hterm
      | tail _ hnil => cases hnil
  have hinit : initMirState wrongReturnZeroBody s0 := ⟨hentry, hmono⟩
  have hreach1 : ReachesPrefix MirStep wrongReturnZeroBody 1 s1 []
      (PrefixOutcome.terminated (TerminationKind.normal (MirVal.usize 0))) :=
    ReachesPrefix.terminated 0 s1 (TerminationKind.normal (MirVal.usize 0)) rfl
  have hreach2 : ReachesPrefix MirStep wrongReturnZeroBody 2 s0 [()]
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
