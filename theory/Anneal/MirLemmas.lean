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
`InhabitedDemonic`) of `Trusted.MirMachine`, the source-level verification
lemmas for `pub fn id(x: usize) -> usize { x }`, and the positive and negative
Rust adequacy canaries:

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

theorem silent_choice_inhabited {s' : MirState} {branches : MirState → Prop}
    (h : StepResult.choice (Obs := Empty) (Val := MirVal) branches =
      .silent s') :
    ∃ s₂, branches s₂ := by
  injection h with hbr
  subst hbr
  exact ⟨s', rfl⟩

theorem evalMirStmt_choice_inhabited (s : MirState) (stmt : Stmt)
    (branches : MirState → Prop) :
    StepResult.choice branches = evalMirStmt s stmt →
    ∃ s', branches s' := by
  cases stmt with
  | assign dst rv =>
    cases rv with
    | use op =>
      cases op with
      | copy src =>
        dsimp [evalMirStmt]
        cases s.locals src.index with
        | none => intro h; cases h
        | some _ => intro h; exact silent_choice_inhabited h
      | move src =>
        dsimp [evalMirStmt]
        cases s.locals src.index with
        | none => intro h; cases h
        | some _ => intro h; exact silent_choice_inhabited h
      | constVal _ =>
        intro h; exact silent_choice_inhabited h
  | storageLive _ => intro h; exact silent_choice_inhabited h
  | storageDead _ => intro h; exact silent_choice_inhabited h
  | nop => intro h; exact silent_choice_inhabited h

theorem evalMirTerminator_choice_inhabited (s : MirState) (term : Terminator)
    (branches : MirState → Prop) :
    StepResult.choice branches = evalMirTerminator s term →
    ∃ s', branches s' := by
  cases term with
  | return_ =>
    dsimp [evalMirTerminator]
    cases s.locals 0 with
    | none => intro h; cases h
    | some _ => intro h; cases h
  | goto _ => intro h; exact silent_choice_inhabited h
  | unreachable => intro h; cases h

/-- `MirMachine` has no empty choice nodes (`evalMirStep` only emits `.silent`
    choices, which are uniquely inhabited). -/
theorem mirMachine_inhabited : InhabitedDemonic MirMachine := by
  intro body s branches hstep
  have h : StepResult.choice branches = evalMirStep body s := hstep
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
      exact evalMirTerminator_choice_inhabited s bb.terminator branches h
    | some stmt =>
      intro h
      exact evalMirStmt_choice_inhabited s stmt branches h

/-- Postcondition `EnsuresEqArg argLocal` refines `MirLang.WellFormed`. -/
theorem ensuresEqArg_le_wellFormed (argLocal : Nat) :
    EnsuresEqArg argLocal ≤ MirLang.WellFormed :=
  spec_le_wellFormed _

theorem reachesPrefix_of_step
    {body : MirBody} {s s' : MirState} {n : Nat} {tr : List Empty}
    {out : PrefixOutcome MirState MirVal}
    (hstep : evalMirStep body s = .silent s')
    (hreach : ReachesPrefix MirMachine.step body n s tr out) :
    out = .running s ∨
      ∃ n' tr', ReachesPrefix MirMachine.step body n' s' tr' out := by
  cases hreach with
  | zero => exact Or.inl rfl
  | step _ _ _ obs _ _ _ _ => nomatch obs
  | choice n' _ s₂ branches _ _ h1 hbr hr =>
    have h1' : StepResult.choice branches = evalMirStep body s := h1
    rw [hstep] at h1'
    injection h1' with hbr_eq
    subst hbr_eq
    subst hbr
    exact Or.inr ⟨n', tr, hr⟩
  | emptyChoice _ _ branches h1 hemp =>
    have h1' : StepResult.choice branches = evalMirStep body s := h1
    rw [hstep] at h1'
    injection h1' with hbr_eq
    subst hbr_eq
    exact False.elim (hemp ⟨s', rfl⟩)
  | terminated _ _ _ h1 =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | failed _ _ h1 =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, hstep.symm⟩)

theorem reachesPrefix_of_terminated
    {body : MirBody} {s : MirState} {n : Nat} {tr : List Empty}
    {out : PrefixOutcome MirState MirVal} {term : TerminationKind MirVal}
    (hstep : evalMirStep body s = .terminated term)
    (hreach : ReachesPrefix MirMachine.step body n s tr out) :
    out = .running s ∨ out = .terminated term := by
  cases hreach with
  | zero => exact Or.inl rfl
  | step _ _ _ obs _ _ _ _ => nomatch obs
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
def SafeAndEnsures (P : MirVal → Prop)
    (out : PrefixOutcome MirState MirVal) : Prop :=
  out.isSafe ∧ ∀ ret, out = .terminated (.normal ret) → P ret

theorem reachesPrefix_safeAndEnsures_of_step
    {body : MirBody} {s s' : MirState} {n : Nat} {tr : List Empty}
    {out : PrefixOutcome MirState MirVal} {P : MirVal → Prop}
    (hstep : evalMirStep body s = .silent s')
    (hreach : ReachesPrefix MirMachine.step body n s tr out)
    (hnext : ∀ n' tr', ReachesPrefix MirMachine.step body n' s' tr' out →
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
    {body : MirBody} {s : MirState} {n : Nat} {tr : List Empty}
    {out : PrefixOutcome MirState MirVal} {P : MirVal → Prop} {v : MirVal}
    (hstep : evalMirStep body s = .terminated (.normal v))
    (hreach : ReachesPrefix MirMachine.step body n s tr out)
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

/-- Inductive normal-termination symbolic execution relation for a `MirBody`:
    witnesses a finite sequence of `.silent` transitions ending in
    `.terminated (.normal v)` with `P v`. -/
inductive ExecNormal (body : MirBody) :
    MirState → (MirVal → Prop) → Prop where
  | step {s s' : MirState} {P : MirVal → Prop} :
      evalMirStep body s = .silent s' →
      ExecNormal body s' P →
      ExecNormal body s P
  | normal {s : MirState} {v : MirVal} {P : MirVal → Prop} :
      evalMirStep body s = .terminated (.normal v) →
      P v →
      ExecNormal body s P

/-- Every prefix reachable from a state satisfying `ExecNormal body s P` is
    safe and satisfies `P` on normal termination. -/
theorem execNormal_safeAndEnsures {body : MirBody} {s : MirState}
    {P : MirVal → Prop}
    (hexec : ExecNormal body s P) :
    ∀ {n : Nat} {tr : List Empty} {out : PrefixOutcome MirState MirVal},
      ReachesPrefix MirMachine.step body n s tr out →
      SafeAndEnsures P out := by
  induction hexec with
  | step hstep _ ih =>
    intro n tr out hreach
    exact reachesPrefix_safeAndEnsures_of_step hstep hreach
      (fun _ _ hr => ih hr)
  | normal hterm hp =>
    intro n tr out hreach
    exact reachesPrefix_safeAndEnsures_of_normal hterm hreach hp

/-- `ExecNormal body s P` implies the existence of a finite prefix reaching
    `.terminated (.normal v)` with `P v`. -/
theorem execNormal_reaches {body : MirBody} {s : MirState}
    {P : MirVal → Prop}
    (hexec : ExecNormal body s P) :
    ∃ n v,
      ReachesPrefix MirMachine.step body n s [] (.terminated (.normal v)) ∧
      P v := by
  induction hexec with
  | step hstep _ ih =>
    cases ih with
    | intro n hn =>
      cases hn with
      | intro v hv =>
        exact ⟨n + 1, v,
          .choice n _ _ _ [] (.terminated (.normal v)) hstep.symm rfl hv.1,
          hv.2⟩
  | normal hterm hp =>
    exact ⟨1, _, .terminated 0 _ (.normal _) hterm.symm, hp⟩

/-- Discharge the baseline `MirLang.Verified pre (fun _ _ => True) body ∧
    MirSem body ≤ MirLang.WellFormedOn pre` obligation from `ExecNormal`. -/
theorem execNormal_verified {body : MirBody} {pre : MirState → Prop}
    (h_pre_init : ∀ s, pre s → initMirState body s)
    (h_inh : ∃ s₀, pre s₀)
    (h_exec : ∀ s, pre s → ExecNormal body s (fun _ => True)) :
    MirLang.Verified pre (fun _ _ => True) body ∧
      MirSem body ≤ MirLang.WellFormedOn pre := by
  have h_wf : MirSem body ≤ MirLang.WellFormedOn pre := by
    refine (eventualBehaviorOf_le_wellFormedOn_iff (M := MirMachine)).mpr ?_
    intro s n tr out hpre _ hreach
    exact (execNormal_safeAndEnsures (h_exec s hpre) hreach).1
  refine ⟨⟨Or.inl h_inh, ?_, ?_⟩, h_wf⟩
  · intro s hpre
    have hinit : initMirState body s := h_pre_init s hpre
    have hdef : (MirSem body s).defined := (h_wf s hpre).1
    cases execNormal_reaches (h_exec s hpre) with
    | intro n hn =>
      cases hn with
      | intro v hv =>
        exact ⟨hdef, .terminated [] (.normal v), hinit, n, hv.1⟩
  · intro s hpre
    refine ⟨(h_wf s hpre).1, fun _ _ => True.intro⟩

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
  refine eventualBehaviorOf_le_normalSpec (M := MirMachine) ?_
  intro init _ _ _ hpfx
  cases init with
  | mk locals0 block0 stmtIdx0 =>
    have hinit := hpfx.1
    have hreach := hpfx.2
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    subst hb hs
    cases hinit.2.2.2.1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      let s₀ : MirState := { locals := locals0, block := 0, stmtIdx := 0 }
      let s₁ : MirState := { s₀ with locals := updateLocal locals0 0 (some v), stmtIdx := 1 }
      have hstep0 : evalMirStep idCopyBody s₀ = .silent s₁ := by
        change evalMirStmt s₀ (.assign ⟨0⟩ (.use (.copy ⟨1⟩))) = .silent s₁
        dsimp [evalMirStmt, s₀]
        rw [hv1]
      refine reachesPrefix_safeAndEnsures_of_step hstep0 hreach (fun _ _ hr1 => ?_)
      exact reachesPrefix_safeAndEnsures_of_normal rfl hr1 hv1

/-- `idCopyBody` satisfies baseline `MirLang.WellFormed`. -/
theorem idCopyBody_satisfies_wellFormed :
    MirSem idCopyBody ≤ MirLang.WellFormed :=
  Preorder.le_trans idCopyBody_satisfies_ensures (ensuresEqArg_le_wellFormed 1)

/-- `idMoveBody` satisfies `EnsuresEqArg 1`: every reachable prefix is safe and
    any normal return value equals the initial value of `_1`. -/
theorem idMoveBody_satisfies_ensures :
    MirSem idMoveBody ≤ EnsuresEqArg 1 := by
  refine eventualBehaviorOf_le_normalSpec (M := MirMachine) ?_
  intro init _ _ _ hpfx
  cases init with
  | mk locals0 block0 stmtIdx0 =>
    have hinit := hpfx.1
    have hreach := hpfx.2
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    subst hb hs
    cases hinit.2.2.2.1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      let s₀ : MirState := { locals := locals0, block := 0, stmtIdx := 0 }
      let s₁ : MirState := {
        s₀ with
        locals := updateLocal (updateLocal locals0 1 none) 0 (some v)
        stmtIdx := 1
      }
      have hstep0 : evalMirStep idMoveBody s₀ = .silent s₁ := by
        change evalMirStmt s₀ (.assign ⟨0⟩ (.use (.move ⟨1⟩))) = .silent s₁
        dsimp [evalMirStmt, s₀]
        rw [hv1]
      refine reachesPrefix_safeAndEnsures_of_step hstep0 hreach (fun _ _ hr1 => ?_)
      exact reachesPrefix_safeAndEnsures_of_normal rfl hr1 hv1

/-- `idMoveBody` satisfies baseline `MirLang.WellFormed`. -/
theorem idMoveBody_satisfies_wellFormed :
    MirSem idMoveBody ≤ MirLang.WellFormed :=
  Preorder.le_trans idMoveBody_satisfies_ensures (ensuresEqArg_le_wellFormed 1)

/-- Canonical entry state for a single-`usize`-argument function (`_1 = 0`). -/
def singleArgUsizeInitState : MirState where
  locals := updateLocal (fun _ => none) 1 (some (.usize 0))
  block := 0
  stmtIdx := 0

/-- `singleArgUsizeInitState` satisfies `initMirState body` for any body with
    `body.argTys = [.usize]`. -/
theorem singleArgUsizeInitState_init {body : MirBody}
    (hargs : body.argTys = [.usize]) :
    initMirState body singleArgUsizeInitState := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  rw [hargs]
  refine ⟨⟨.usize 0, rfl, True.intro⟩, ?_⟩
  intro j hj
  cases j with
  | zero => cases hj
  | succ k =>
    cases k with
    | zero =>
      cases hj with
      | step hle => cases hle
    | succ _ => rfl

/-- `idCopyBody` executes to normal termination from any `initMirState`. -/
theorem idCopyBody_execNormal (s : MirState)
    (hinit : initMirState idCopyBody s) :
    ExecNormal idCopyBody s (fun _ => True) := by
  cases s with
  | mk locals0 block0 stmtIdx0 =>
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    subst hb hs
    cases hinit.2.2.2.1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      let s₀ : MirState := { locals := locals0, block := 0, stmtIdx := 0 }
      let s₁ : MirState := {
        s₀ with locals := updateLocal locals0 0 (some v), stmtIdx := 1
      }
      have hstep0 : evalMirStep idCopyBody s₀ = .silent s₁ := by
        change evalMirStmt s₀ (.assign ⟨0⟩ (.use (.copy ⟨1⟩))) = .silent s₁
        dsimp [evalMirStmt, s₀]
        rw [hv1]
      exact .step hstep0 (.normal rfl True.intro)

/-- `idMoveBody` executes to normal termination from any `initMirState`. -/
theorem idMoveBody_execNormal (s : MirState)
    (hinit : initMirState idMoveBody s) :
    ExecNormal idMoveBody s (fun _ => True) := by
  cases s with
  | mk locals0 block0 stmtIdx0 =>
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    subst hb hs
    cases hinit.2.2.2.1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      let s₀ : MirState := { locals := locals0, block := 0, stmtIdx := 0 }
      let s₁ : MirState := {
        s₀ with
        locals := updateLocal (updateLocal locals0 1 none) 0 (some v)
        stmtIdx := 1
      }
      have hstep0 : evalMirStep idMoveBody s₀ = .silent s₁ := by
        change evalMirStmt s₀ (.assign ⟨0⟩ (.use (.move ⟨1⟩))) = .silent s₁
        dsimp [evalMirStmt, s₀]
        rw [hv1]
      exact .step hstep0 (.normal rfl True.intro)

/-!
## Positive and Negative Rust Adequacy Canaries
-/

/-- Pure infinite loop MIR body (`bb0: { goto -> bb0; }`). -/
def loopBody : MirBody where
  argTys := []
  retTy := .unit
  localCount := 1
  blocks := [{ stmts := [], terminator := .goto ⟨0⟩ }]

theorem loopBody_reaches_running (n : Nat) :
    ∀ (s : MirState) (tr : List Empty) (out : PrefixOutcome MirState MirVal),
      s.block = 0 → s.stmtIdx = 0 →
      ReachesPrefix MirMachine.step loopBody n s tr out →
      ∃ s', out = .running s' := by
  induction n with
  | zero =>
    intro s _ out _ _ hreach
    cases hreach with
    | zero => exact ⟨s, rfl⟩
  | succ k ih =>
    intro s tr out hb hs hreach
    have hstep0 :
        evalMirStep loopBody s = StepResult.silent { s with block := 0, stmtIdx := 0 } := by
      cases s with
      | mk locals block stmtIdx =>
        dsimp at hb hs
        subst hb hs
        rfl
    cases hreach with
    | step _ _ _ obs _ _ _ _ => nomatch obs
    | choice _ _ s' branches _ _ h1 hbr h2 =>
      have h1' : StepResult.choice branches = evalMirStep loopBody s := h1
      rw [hstep0] at h1'
      injection h1' with hbr_eq
      subst hbr_eq
      subst hbr
      exact ih { s with block := 0, stmtIdx := 0 } tr out rfl rfl h2
    | emptyChoice _ _ branches h1 hemp =>
      have h1' : StepResult.choice branches = evalMirStep loopBody s := h1
      rw [hstep0] at h1'
      injection h1' with hbr_eq
      subst hbr_eq
      exact False.elim (hemp ⟨{ s with block := 0, stmtIdx := 0 }, rfl⟩)
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
  refine (eventualBehaviorOf_le_wellFormed_iff (M := MirMachine)).mpr ?_
  intro init steps tr out hinit hreach
  cases loopBody_reaches_running steps init tr out
    hinit.1 hinit.2.1 hreach with
  | intro s' hout =>
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
  have hinit : initMirState uninitReturnBody s0 :=
    ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
  have hfail : ReachesPrefix MirMachine.step uninitReturnBody 1 s0 [] PrefixOutcome.failed :=
    ReachesPrefix.failed 0 s0 rfl
  exact (eventualBehaviorOf_le_wellFormed_iff (M := MirMachine)).mp hWF s0 1 [] .failed hinit hfail

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
      | succ _ => rfl
  have hinit : initMirState wrongReturnZeroBody s0 :=
    ⟨rfl, rfl, rfl, ⟨⟨MirVal.usize 1, rfl, True.intro⟩, hrest⟩⟩
  have hreach1 : ReachesPrefix MirMachine.step wrongReturnZeroBody 1 s1 []
      (PrefixOutcome.terminated (TerminationKind.normal (MirVal.usize 0))) :=
    ReachesPrefix.terminated 0 s1 (TerminationKind.normal (MirVal.usize 0)) rfl
  have hreach2 : ReachesPrefix MirMachine.step wrongReturnZeroBody 2 s0 []
      (PrefixOutcome.terminated (TerminationKind.normal (MirVal.usize 0))) :=
    ReachesPrefix.choice 1 s0 s1 (· = s1) []
      (PrefixOutcome.terminated (TerminationKind.normal (MirVal.usize 0))) rfl rfl hreach1
  let out : EventualOut Empty MirVal :=
    .terminated [] (TerminationKind.normal (MirVal.usize 0))
  cases hEns s0 True.intro with
  | intro hdef hval =>
    have hpfx : (MirSem wrongReturnZeroBody s0).val hdef out := ⟨hinit, 2, hreach2⟩
    have hpost := hval out hpfx [] (MirVal.usize 0) rfl
    have h1 : s0.locals 1 = some (MirVal.usize 1) := rfl
    rw [h1] at hpost
    injection hpost with hval'
    injection hval' with hnum
    cases hnum

end Anneal
