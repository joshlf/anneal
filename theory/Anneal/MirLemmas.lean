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
# Untrusted MIR Meta-Theorems, Weak-Memory Helpers, and Adequacy Canaries

This module proves:
1. Structural non-vacuity properties (`TotalStep`, `InhabitedDemonic`) of
   `Trusted.MirMachine`, including non-vacuity of the demonic choice emitted by
   `Terminator.callAtomicLoad`.
2. Partial-order lemmas for `Trusted.View` (`View.le_bump`, `View.le_join_left`,
   `View.le_join_right`, `applyAtomicLoad_curView_mono`) and the `OwnLoc`
   ownership abstraction showing that non-atomic reads/writes are deterministic
   and preserved across view advances and release-acquire synchronization.
3. Verification lemmas for `pub fn id(x: usize) -> usize { x }` and
   `pub fn load_relaxed(a: &AtomicUsize) -> usize { a.load(Ordering::Relaxed) }`
   discharging `Trusted.CrateTheorem` via `Anneal.verify_through_passes`.
4. Positive and negative Rust adequacy canaries (`#100` §6.2).
-/

namespace Anneal

open Trusted

/-!
## 1. View Partial Order and Non-Atomic Ownership Helpers (`OwnLoc`)
-/

/-- Bumping a coherence view at `(loc, ts)` is inflationary in `Preorder View`
    (`v ≤ View.bump v loc ts`). -/
theorem View.le_bump (v : View) (loc : Nat) (ts : Timestamp) :
    v ≤ View.bump v loc ts := by
  intro l
  unfold View.bump
  cases l == loc with
  | false => exact Nat.le_refl _
  | true =>
    cases h : decide (v l ≤ ts) with
    | false => exact Nat.le_refl _
    | true => exact of_decide_eq_true h

/-- Left upper-bound property of `View.join` in `Preorder View`
    (`v₁ ≤ View.join v₁ v₂`). -/
theorem View.le_join_left (v₁ v₂ : View) :
    v₁ ≤ View.join v₁ v₂ := by
  intro l
  unfold View.join
  cases h : decide (v₁ l ≤ v₂ l) with
  | false => exact Nat.le_refl _
  | true => exact of_decide_eq_true h

/-- Right upper-bound property of `View.join` in `Preorder View`
    (`v₂ ≤ View.join v₁ v₂`). -/
theorem View.le_join_right (v₁ v₂ : View) :
    v₂ ≤ View.join v₁ v₂ := by
  intro l
  unfold View.join
  cases h : decide (v₁ l ≤ v₂ l) with
  | false =>
    have hnot : ¬ (v₁ l ≤ v₂ l) := of_decide_eq_false h
    exact Nat.le_of_not_le hnot
  | true => exact Nat.le_refl _

/-- Any atomic load (`.relaxed` or `.acquire`) monotonically advances the
    active thread's coherence view in `Preorder View`
    (`m.curView ≤ (m.applyAtomicLoad ord msg).curView`). -/
theorem applyAtomicLoad_curView_mono (m : MemState) (ord : AtomicOrdering) (msg : AtomicMsg) :
    m.curView ≤ (m.applyAtomicLoad ord msg).curView := by
  cases ord with
  | relaxed =>
    exact View.le_bump m.curView msg.loc msg.ts
  | acquire =>
    exact Preorder.le_trans
      (View.le_bump m.curView msg.loc msg.ts)
      (View.le_join_left (View.bump m.curView msg.loc msg.ts) msg.relView)

/-- Single-threaded / lock-synchronized non-atomic ownership predicate:
    non-atomic location `loc` holds initialized value `v`, and its last write
    and read timestamps are both visible in the active thread's `curView`. -/
def OwnLoc (m : MemState) (loc : Nat) (v : MirVal) : Prop :=
  m.naVal loc = some v ∧
  m.naWriteTs loc ≤ m.curView loc ∧
  m.naReadTs loc ≤ m.curView loc

/-- Read-only shared non-atomic ownership predicate (`&usize`):
    non-atomic location `loc` holds initialized value `v`, and its last write
    timestamp is visible in the active thread's `curView` (permitting arbitrary
    aliasing reads at `loc`). -/
def ReadOwnLoc (m : MemState) (loc : Nat) (v : MirVal) : Prop :=
  m.naVal loc = some v ∧
  m.naWriteTs loc ≤ m.curView loc

/-- Under `ReadOwnLoc m loc v`, a non-atomic read at `loc` is completely
    deterministic, never triggers a data-race failure, and returns `v`. -/
theorem ReadOwnLoc.readNA_eq {m : MemState} {loc : Nat} {v : MirVal}
    (hRead : ReadOwnLoc m loc v) :
    m.readNA loc =
      some (v, { m with naReadTs := View.bump m.naReadTs loc (m.curView loc) }) := by
  unfold MemState.readNA
  have hdec : decide (m.naWriteTs loc ≤ m.curView loc) = true :=
    decide_eq_true hRead.2
  rw [hdec, hRead.1]
  rfl

/-- Performing a non-atomic read at `loc` preserves `ReadOwnLoc` at every
    shared location `loc'` (both `loc' = loc` and `loc' ≠ loc`). -/
theorem ReadOwnLoc.readNA_preserves {m : MemState} {loc loc' : Nat} {v' : MirVal}
    (hRead' : ReadOwnLoc m loc' v') :
    ReadOwnLoc { m with naReadTs := View.bump m.naReadTs loc (m.curView loc) } loc' v' :=
  hRead'

/-- Under `OwnLoc m loc v`, a non-atomic read at `loc` is completely
    deterministic, never triggers a data-race failure, and returns `v`. -/
theorem OwnLoc.readNA_eq {m : MemState} {loc : Nat} {v : MirVal}
    (hOwn : OwnLoc m loc v) :
    m.readNA loc =
      some (v, { m with naReadTs := View.bump m.naReadTs loc (m.curView loc) }) :=
  ReadOwnLoc.readNA_eq ⟨hOwn.1, hOwn.2.1⟩

/-- Performing a non-atomic read at `loc` preserves `OwnLoc` at every owned
    location `loc'` (both `loc' = loc` and `loc' ≠ loc`). -/
theorem OwnLoc.readNA_preserves {m : MemState} {loc loc' : Nat} {v' : MirVal}
    (hOwn' : OwnLoc m loc' v') :
    OwnLoc { m with naReadTs := View.bump m.naReadTs loc (m.curView loc) } loc' v' := by
  refine ⟨hOwn'.1, hOwn'.2.1, ?_⟩
  dsimp [View.bump]
  cases hbeq : (loc' == loc) with
  | false => exact hOwn'.2.2
  | true =>
    have heq : loc' = loc := of_decide_eq_true hbeq
    subst heq
    have hdec : decide (m.naReadTs loc' ≤ m.curView loc') = true :=
      decide_eq_true hOwn'.2.2
    rw [hdec]
    exact Nat.le_refl _

/-- Memory state resulting from a successful non-atomic write `m.writeNA loc v`. -/
def afterWriteNA (m : MemState) (loc : Nat) (v : MirVal) : MemState :=
  let nextTs := m.curView loc + 1
  { m with
    curView := View.bump m.curView loc nextTs
    naVal := fun l => if l == loc then some v else m.naVal l
    naWriteTs := View.bump m.naWriteTs loc nextTs
    naReadTs := View.bump m.naReadTs loc nextTs }

/-- Under `OwnLoc m loc v`, a non-atomic write `m.writeNA loc vNew` succeeds
    deterministically without data-race failure and produces
    `afterWriteNA m loc vNew`. -/
theorem OwnLoc.writeNA_eq {m : MemState} {loc : Nat} {v : MirVal}
    (hOwn : OwnLoc m loc v) (vNew : MirVal) :
    m.writeNA loc vNew = some (afterWriteNA m loc vNew) := by
  unfold MemState.writeNA afterWriteNA
  have hw : decide (m.naWriteTs loc ≤ m.curView loc) = true :=
    decide_eq_true hOwn.2.1
  have hr : decide (m.naReadTs loc ≤ m.curView loc) = true :=
    decide_eq_true hOwn.2.2
  rw [hw, hr]
  rfl

/-- After writing `vNew` to an owned location `loc`, `OwnLoc` holds at `loc`
    with the updated value `vNew`. -/
theorem OwnLoc.afterWriteNA_self {m : MemState} {loc : Nat} {v : MirVal}
    (hOwn : OwnLoc m loc v) (vNew : MirVal) :
    OwnLoc (afterWriteNA m loc vNew) loc vNew := by
  have hbeq : (loc == loc) = true := decide_eq_true rfl
  have hcur : decide (m.curView loc ≤ m.curView loc + 1) = true :=
    decide_eq_true (Nat.le_succ (m.curView loc))
  have hw : decide (m.naWriteTs loc ≤ m.curView loc + 1) = true :=
    decide_eq_true (Nat.le_trans hOwn.2.1 (Nat.le_succ (m.curView loc)))
  have hr : decide (m.naReadTs loc ≤ m.curView loc + 1) = true :=
    decide_eq_true (Nat.le_trans hOwn.2.2 (Nat.le_succ (m.curView loc)))
  unfold OwnLoc afterWriteNA View.bump
  dsimp
  rw [hbeq, hcur, hw, hr]
  exact ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩

/-- Writing `vNew` to `loc` preserves `OwnLoc` at every other location
    `loc' ≠ loc`. -/
theorem OwnLoc.afterWriteNA_other {m : MemState} {loc loc' : Nat} {v' : MirVal}
    (hne : loc' ≠ loc) (hOwn' : OwnLoc m loc' v') (vNew : MirVal) :
    OwnLoc (afterWriteNA m loc vNew) loc' v' := by
  have hbeq : (loc' == loc) = false := decide_eq_false hne
  unfold OwnLoc afterWriteNA View.bump
  dsimp
  rw [hbeq]
  exact hOwn'

/-- Writing `vNew` to `loc` preserves `ReadOwnLoc` at every other location
    `loc' ≠ loc`. -/
theorem ReadOwnLoc.afterWriteNA_other {m : MemState} {loc loc' : Nat} {v' : MirVal}
    (hne : loc' ≠ loc) (hRead' : ReadOwnLoc m loc' v') (vNew : MirVal) :
    ReadOwnLoc (afterWriteNA m loc vNew) loc' v' := by
  have hbeq : (loc' == loc) = false := decide_eq_false hne
  unfold ReadOwnLoc afterWriteNA View.bump
  dsimp
  rw [hbeq]
  exact hRead'

/-- `OwnLoc` is preserved whenever the thread's coherence view advances in
    `Preorder View` (`m.curView ≤ v'`) without concurrent modification to `loc`. -/
theorem OwnLoc.mono_view {m : MemState} {loc : Nat} {v : MirVal} {v' : View}
    (hOwn : OwnLoc m loc v) (hle : m.curView ≤ v') :
    OwnLoc { m with curView := v' } loc v :=
  ⟨hOwn.1, Nat.le_trans hOwn.2.1 (hle loc), Nat.le_trans hOwn.2.2 (hle loc)⟩

/-- Any atomic load preserves `OwnLoc` on non-atomic locations. -/
theorem OwnLoc.preserved_by_atomic_load {m : MemState} {loc : Nat} {v : MirVal}
    (ord : AtomicOrdering) (msg : AtomicMsg) (hOwn : OwnLoc m loc v) :
    OwnLoc (m.applyAtomicLoad ord msg) loc v := by
  have hmono := applyAtomicLoad_curView_mono m ord msg
  cases ord with
  | relaxed => exact OwnLoc.mono_view hOwn hmono
  | acquire => exact OwnLoc.mono_view hOwn hmono

/-- Release-Acquire ownership transfer (e.g., across a `Mutex` unlock/lock): if
    a `Release` message `msg` captured a view `msg.relView` that dominates
    `loc`'s non-atomic write/read timestamps, performing an `Acquire` load of
    `msg` establishes `OwnLoc` in the acquiring thread. -/
theorem OwnLoc.transfer_acquire {m : MemState} {loc : Nat} {v : MirVal}
    (msg : AtomicMsg)
    (hVal : m.naVal loc = some v)
    (hWrite : m.naWriteTs loc ≤ msg.relView loc)
    (hRead : m.naReadTs loc ≤ msg.relView loc) :
    OwnLoc (m.applyAtomicLoad .acquire msg) loc v := by
  have hjoin := View.le_join_right (View.bump m.curView msg.loc msg.ts) msg.relView loc
  exact ⟨hVal, Nat.le_trans hWrite hjoin, Nat.le_trans hRead hjoin⟩

/-!
## 2. Structural Non-Vacuity (`TotalStep` and `InhabitedDemonic`)
-/

/-- `MirMachine` is total: every `(body, s)` pair steps to `evalMirStep body s`. -/
theorem mirMachine_total : TotalStep MirMachine :=
  fun body s => ⟨evalMirStep body s, rfl⟩

theorem evalMirStmt_not_choice (s : MirState) (stmt : Stmt)
    (kind : ChoiceKind) (branches : MirState → Prop) :
    StepResult.choice kind branches ≠ evalMirStmt s stmt := by
  cases stmt with
  | assign dst rv =>
    cases rv with
    | use op =>
      dsimp [evalMirStmt]
      cases evalOperand s.locals op with
      | none => intro h; cases h
      | some p => intro h; cases h
    | deref src =>
      dsimp [evalMirStmt]
      cases s.locals src.index with
      | none => intro h; cases h
      | some v =>
        cases v with
        | refMutLoc loc | refSharedLoc loc =>
          dsimp
          cases s.mem.readNA loc with
          | none => intro h; cases h
          | some p => intro h; cases h
        | usize _ | bool _ | unit | atomicLoc _ | ordering _ =>
          intro h; cases h
    | binaryOp op lhs rhs =>
      dsimp [evalMirStmt]
      cases evalOperand s.locals lhs with
      | none => intro h; cases h
      | some p1 =>
        cases p1 with
        | mk v1 locals1 =>
          dsimp
          cases evalOperand locals1 rhs with
          | none => intro h; cases h
          | some p2 =>
            cases p2 with
            | mk v2 locals2 =>
              dsimp
              cases evalBinOp op v1 v2 with
              | none => intro h; cases h
              | some res => intro h; cases h
  | assignDeref dst op =>
    dsimp [evalMirStmt]
    cases evalOperand s.locals op with
    | none => intro h; cases h
    | some p1 =>
      cases p1 with
      | mk v locals1 =>
        dsimp
        cases locals1 dst.index with
        | none => intro h; cases h
        | some dv =>
          cases dv with
          | refMutLoc loc =>
            dsimp
            cases s.mem.writeNA loc v with
            | none => intro h; cases h
            | some m' => intro h; cases h
          | usize _ | bool _ | unit | atomicLoc _ | refSharedLoc _ | ordering _ =>
            intro h; cases h
  | storageLive loc => intro h; cases h
  | storageDead loc => intro h; cases h
  | nop => intro h; cases h

theorem evalMirTerminator_choice_inhabited (s : MirState) (term : Terminator)
    (kind : ChoiceKind) (branches : MirState → Prop) :
    StepResult.choice kind branches = evalMirTerminator s term →
    ∃ s', branches s' := by
  cases term with
  | return_ =>
    dsimp [evalMirTerminator]
    cases s.locals 0 with
    | none => intro h; cases h
    | some v => intro h; cases h
  | goto target => intro h; cases h
  | unreachable => intro h; cases h
  | switchInt discr falseTarget trueTarget =>
    dsimp [evalMirTerminator]
    cases evalOperand s.locals discr with
    | none => intro h; cases h
    | some p =>
      cases p with
      | mk v locals' =>
        cases v with
        | bool b =>
          cases b with
          | false => intro h; cases h
          | true => intro h; cases h
        | usize _ | unit | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ =>
          intro h; cases h
  | callAtomicLoad dst ptrOp ordOp target =>
    dsimp [evalMirTerminator]
    cases evalOperand s.locals ptrOp with
    | none => intro h; cases h
    | some p1 =>
      cases p1 with
      | mk ptrVal locals1 =>
        dsimp
        cases evalOperand locals1 ordOp with
        | none => intro h; cases h
        | some p2 =>
          cases p2 with
          | mk ordVal locals2 =>
            dsimp
            cases ptrVal with
            | usize _ => intro h; cases h
            | bool _ => intro h; cases h
            | unit => intro h; cases h
            | refSharedLoc _ => intro h; cases h
            | refMutLoc _ => intro h; cases h
            | ordering _ => intro h; cases h
            | atomicLoc loc =>
              cases ordVal with
              | usize _ => intro h; cases h
              | bool _ => intro h; cases h
              | unit => intro h; cases h
              | atomicLoc _ => intro h; cases h
              | refSharedLoc _ => intro h; cases h
              | refMutLoc _ => intro h; cases h
              | ordering ord =>
                dsimp
                cases s.mem.visibleAtomicMsgs loc with
                | nil => intro h; cases h
                | cons head tail =>
                  intro h
                  injection h with _ hbranches
                  subst hbranches
                  refine ⟨{
                    locals := updateLocal locals2 dst.index (some (.usize head.bits))
                    mem := s.mem.applyAtomicLoad ord head
                    block := target.index
                    stmtIdx := 0
                  }, ?_⟩
                  exact ⟨head, List.Mem.head tail, rfl⟩

/-- `MirMachine` has no empty choice nodes: whenever `evalMirStep` emits
    `.choice`, `visibleAtomicMsgs` is of the form `head :: tail`, so `head`
    provides an inhabited transition branch. -/
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
      exact evalMirTerminator_choice_inhabited s bb.terminator kind branches h
    | some stmt =>
      intro h
      exact False.elim (evalMirStmt_not_choice s stmt kind branches h)

/-!
## 3. Verification Lemmas for `pub fn id` and `pub fn load_relaxed`
-/

/-- Postcondition `EnsuresEqArg argLocal` refines `MirLang.WellFormed`. -/
theorem ensuresEqArg_le_wellFormed (argLocal : Nat) :
    EnsuresEqArg argLocal ≤ MirLang.WellFormed :=
  spec_le_wellFormed _

/-- Postcondition `EnsuresAtomicLoad argLocal` refines `MirLang.WellFormed`. -/
theorem ensuresAtomicLoad_le_wellFormed (argLocal : Nat) :
    EnsuresAtomicLoad argLocal ≤ MirLang.WellFormed :=
  spec_le_wellFormed _

/-- Canonical `Runtime(PostCleanup)` MIR body for `pub fn id(x: usize) -> usize { x }`
    using `Operand.copy`:
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

/-- Canonical `Runtime(PostCleanup)` MIR body for `pub fn id(x: usize) -> usize { x }`
    using `Operand.move`:
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
    have harg : ∃ v, init.locals 1 = some v ∧ v.hasTy init.mem .usize :=
      hinit.2.2.2.1
    cases harg with
    | intro v hv =>
      have hv1 : init.locals 1 = some v := hv.1
      have hstep0 :
          evalMirStep idCopyBody init =
            StepResult.step () { init with
              locals := updateLocal init.locals 0 (some v)
              block := 0
              stmtIdx := 1
            } := by
        unfold evalMirStep idCopyBody
        rw [hb, hs]
        change (match evalOperand init.locals (.copy ⟨1⟩) with
          | some (v, locals') => StepResult.step (State := MirState) (Obs := Unit) (Val := MirVal) () { init with
              locals := updateLocal locals' 0 (some v)
              stmtIdx := init.stmtIdx + 1
            }
          | none => StepResult.failed FailureKind.ub) = _
        dsimp [evalOperand]
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
            evalMirStep idCopyBody { init with
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
    have harg : ∃ v, init.locals 1 = some v ∧ v.hasTy init.mem .usize :=
      hinit.2.2.2.1
    cases harg with
    | intro v hv =>
      have hv1 : init.locals 1 = some v := hv.1
      have hstep0 :
          evalMirStep idMoveBody init =
            StepResult.step () { init with
              locals := updateLocal (updateLocal init.locals 1 none) 0 (some v)
              block := 0
              stmtIdx := 1
            } := by
        unfold evalMirStep idMoveBody
        rw [hb, hs]
        change (match evalOperand init.locals (.move ⟨1⟩) with
          | some (v, locals') => StepResult.step (State := MirState) (Obs := Unit) (Val := MirVal) () { init with
              locals := updateLocal locals' 0 (some v)
              stmtIdx := init.stmtIdx + 1
            }
          | none => StepResult.failed FailureKind.ub) = _
        dsimp [evalOperand]
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
            evalMirStep idMoveBody { init with
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

/-- Canonical `Runtime(PostCleanup)` MIR body for
    `pub fn load_relaxed(a: &AtomicUsize) -> usize { a.load(Ordering::Relaxed) }`:
    ```text
    bb0: {
        _2 = std::sync::atomic::Ordering::Relaxed;
        _0 = Atomic::<usize>::load(copy _1, move _2) -> [return: bb1, unwind continue];
    }
    bb1: {
        return;
    }
    ``` -/
def loadRelaxedBody : MirBody where
  argTys := [.refAtomicUsize]
  retTy := .usize
  localCount := 3
  blocks := [
    { stmts := [.assign ⟨2⟩ (.use (.constVal (.ordering .relaxed)))]
      terminator := .callAtomicLoad ⟨0⟩ (.copy ⟨1⟩) (.move ⟨2⟩) ⟨1⟩ },
    { stmts := []
      terminator := .return_ }
  ]

/-- `loadRelaxedBody` satisfies `EnsuresAtomicLoad 1`: every reachable prefix
    is safe (including across the demonic weak-memory choice in `bb0`), and any
    normal return value equals `MirVal.usize msg.bits` for some visible message
    `msg ∈ init.mem.visibleAtomicMsgs loc` at `_1`'s atomic location. -/
theorem loadRelaxedBody_satisfies_ensures :
    MirSem loadRelaxedBody ≤ EnsuresAtomicLoad 1 := by
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
    have harg : ∃ v, init.locals 1 = some v ∧ v.hasTy init.mem .refAtomicUsize :=
      hinit.2.2.2.1
    cases harg with
    | intro v hv =>
      have hv1 : init.locals 1 = some v := hv.1
      have hty : v.hasTy init.mem .refAtomicUsize := hv.2
      cases v with
      | usize _ => cases hty
      | bool _ => cases hty
      | unit => cases hty
      | refSharedLoc _ => cases hty
      | refMutLoc _ => cases hty
      | ordering _ => cases hty
      | atomicLoc loc =>
        have hvis : init.mem.visibleAtomicMsgs loc ≠ [] := hty
        let s1 : MirState := { init with
          locals := updateLocal init.locals 2 (some (.ordering .relaxed))
          block := 0
          stmtIdx := 1
        }
        have hstep0 : evalMirStep loadRelaxedBody init = StepResult.step () s1 := by
          unfold evalMirStep loadRelaxedBody
          rw [hb, hs]
          change (StepResult.step (State := MirState) (Obs := Unit) (Val := MirVal) () { init with
            locals := updateLocal init.locals 2 (some (.ordering .relaxed))
            stmtIdx := init.stmtIdx + 1
          }) = StepResult.step () s1
          unfold s1
          rw [hb, hs]
        cases hreach with
        | zero =>
          exact ⟨True.intro, fun _ h => by cases h⟩
        | step n _ s1' obs tr out h1 h2 =>
          have h1' : StepResult.step obs s1' = evalMirStep loadRelaxedBody init := h1
          rw [hstep0] at h1'
          injection h1' with _ hs1'
          subst hs1'
          cases hlist : init.mem.visibleAtomicMsgs loc with
          | nil =>
            exact False.elim (hvis hlist)
          | cons head tail =>
            let localsAfterMove := updateLocal (updateLocal init.locals 2 (some (.ordering .relaxed))) 2 none
            let branches : MirState → Prop := fun s' =>
              ∃ msg, msg ∈ (head :: tail) ∧
                s' = {
                  locals := updateLocal localsAfterMove 0 (some (.usize msg.bits))
                  mem := init.mem.applyAtomicLoad .relaxed msg
                  block := 1
                  stmtIdx := 0
                }
            have hptr : evalOperand s1.locals (.copy ⟨1⟩) = some (.atomicLoc loc, s1.locals) := by
              unfold evalOperand s1 updateLocal
              change (match init.locals 1 with | some v => some (v, _) | none => none) = _
              rw [hv1]
            have hstep1 : evalMirStep loadRelaxedBody s1 = StepResult.choice .demonic branches := by
              unfold evalMirStep loadRelaxedBody
              change evalMirTerminator s1 (.callAtomicLoad ⟨0⟩ (.copy ⟨1⟩) (.move ⟨2⟩) ⟨1⟩) = _
              dsimp only [evalMirTerminator]
              rw [hptr]
              change (match init.mem.visibleAtomicMsgs loc with
                | [] => StepResult.failed FailureKind.ub
                | head' :: tail' =>
                  StepResult.choice (State := MirState) (Obs := Unit) (Val := MirVal) .demonic (fun s' =>
                    ∃ msg, msg ∈ (head' :: tail') ∧
                      s' = {
                        locals := updateLocal localsAfterMove 0 (some (.usize msg.bits))
                        mem := init.mem.applyAtomicLoad .relaxed msg
                        block := 1
                        stmtIdx := 0
                      })) = StepResult.choice .demonic branches
              rw [hlist]
            cases h2 with
            | zero =>
              exact ⟨True.intro, fun _ h => by cases h⟩
            | step _ _ _ _ _ _ hbad _ =>
              have hbad' : _ = evalMirStep loadRelaxedBody s1 := hbad
              rw [hstep1] at hbad'
              cases hbad'
            | choice m kind _ s2 brs tr2 out2 hch hbr h3 =>
              have hch' : StepResult.choice kind brs = evalMirStep loadRelaxedBody s1 := hch
              rw [hstep1] at hch'
              injection hch' with _ hbrs
              subst hbrs
              cases hbr with
              | intro msg hmsg =>
                have hmem : msg ∈ head :: tail := hmsg.1
                have hs2 : s2 = {
                    locals := updateLocal localsAfterMove 0 (some (.usize msg.bits))
                    mem := init.mem.applyAtomicLoad .relaxed msg
                    block := 1
                    stmtIdx := 0
                  } := hmsg.2
                subst hs2
                have hstep2 :
                    evalMirStep loadRelaxedBody {
                      locals := updateLocal localsAfterMove 0 (some (.usize msg.bits))
                      mem := init.mem.applyAtomicLoad .relaxed msg
                      block := 1
                      stmtIdx := 0
                    } = StepResult.terminated (TerminationKind.normal (.usize msg.bits)) := by
                  rfl
                cases h3 with
                | zero =>
                  exact ⟨True.intro, fun _ h => by cases h⟩
                | step _ _ _ _ _ _ hbad _ =>
                  have hbad' : _ = evalMirStep loadRelaxedBody _ := hbad
                  rw [hstep2] at hbad'
                  cases hbad'
                | choice _ _ _ _ _ _ _ hbad _ _ =>
                  have hbad' : _ = evalMirStep loadRelaxedBody _ := hbad
                  rw [hstep2] at hbad'
                  cases hbad'
                | emptyChoice _ _ _ _ hbad _ =>
                  have hbad' : _ = evalMirStep loadRelaxedBody _ := hbad
                  rw [hstep2] at hbad'
                  cases hbad'
                | terminated _ _ term hterm =>
                  have hterm' : StepResult.terminated term = evalMirStep loadRelaxedBody _ := hterm
                  rw [hstep2] at hterm'
                  injection hterm' with hterm_eq
                  subst hterm_eq
                  refine ⟨True.intro, ?_⟩
                  intro ret hret
                  injection hret with hterm_ret
                  injection hterm_ret with hret_eq
                  subst hret_eq
                  refine ⟨loc, msg, hv1, ?_, rfl⟩
                  rw [hlist]
                  exact hmem
                | failed _ _ _ hbad =>
                  have hbad' : _ = evalMirStep loadRelaxedBody _ := hbad
                  rw [hstep2] at hbad'
                  cases hbad'
                | noStep _ _ hnostep =>
                  exact False.elim (hnostep ⟨_, hstep2.symm⟩)
            | emptyChoice _ kind _ brs hch hempty =>
              have hch' : StepResult.choice kind brs = evalMirStep loadRelaxedBody s1 := hch
              rw [hstep1] at hch'
              injection hch' with _ hbrs
              subst hbrs
              exact False.elim (hempty ⟨_, ⟨head, List.Mem.head tail, rfl⟩⟩)
            | terminated _ _ _ hbad =>
              have hbad' : _ = evalMirStep loadRelaxedBody s1 := hbad
              rw [hstep1] at hbad'
              cases hbad'
            | failed _ _ _ hbad =>
              have hbad' : _ = evalMirStep loadRelaxedBody s1 := hbad
              rw [hstep1] at hbad'
              cases hbad'
            | noStep _ _ hnostep =>
              exact False.elim (hnostep ⟨_, hstep1.symm⟩)
        | choice _ _ _ _ _ _ _ h1 _ _ =>
          have h1' : _ = evalMirStep loadRelaxedBody init := h1
          rw [hstep0] at h1'
          cases h1'
        | emptyChoice _ _ _ _ h1 _ =>
          have h1' : _ = evalMirStep loadRelaxedBody init := h1
          rw [hstep0] at h1'
          cases h1'
        | terminated _ _ _ h1 =>
          have h1' : _ = evalMirStep loadRelaxedBody init := h1
          rw [hstep0] at h1'
          cases h1'
        | failed _ _ _ h1 =>
          have h1' : _ = evalMirStep loadRelaxedBody init := h1
          rw [hstep0] at h1'
          cases h1'
        | noStep _ _ hnostep =>
          exact False.elim (hnostep ⟨_, hstep0.symm⟩)

/-- `loadRelaxedBody` satisfies baseline `MirLang.WellFormed`. -/
theorem loadRelaxedBody_satisfies_wellFormed :
    MirSem loadRelaxedBody ≤ MirLang.WellFormed :=
  Preorder.le_trans loadRelaxedBody_satisfies_ensures (ensuresAtomicLoad_le_wellFormed 1)

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

/-- Generic single-function `CrateTheorem` discharge via `Compiler.SoundOn.verify`
    and `Compiler.Verified.with_wellFormedOn`: given a proof
    `h_proof : MirSem body ≤ spec` and `h_spec_wf : spec ≤ MirLang.WellFormed`,
    proves `CrateTheorem` for the single-function crate containing
    `(fnName, body, [spec])` with TCB entry `TCBItem.rustcLowering fnName body`. -/
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

/-- Ready-to-apply `CrateTheorem` witness for `pub fn load_relaxed`
    (`specs := [EnsuresAtomicLoad 1]`). -/
theorem prove_load_relaxed_ensures_crate (fnName : String) :
    CrateTheorem {
      functions := [{ name := fnName, prog := loadRelaxedBody, specs := [EnsuresAtomicLoad 1] }]
      tcb := [TCBItem.rustcLowering fnName loadRelaxedBody]
    } :=
  verify_single_fn_crate fnName loadRelaxedBody (EnsuresAtomicLoad 1)
    loadRelaxedBody_satisfies_ensures (ensuresAtomicLoad_le_wellFormed 1)

/-- Ready-to-apply `CrateTheorem` witness for unannotated `pub fn load_relaxed`
    (`specs := []`). -/
theorem prove_load_relaxed_wf_crate (fnName : String) :
    CrateTheorem {
      functions := [{ name := fnName, prog := loadRelaxedBody, specs := [] }]
      tcb := [TCBItem.rustcLowering fnName loadRelaxedBody]
    } :=
  verify_single_fn_wf_crate fnName loadRelaxedBody loadRelaxedBody_satisfies_wellFormed

/-!
## 4. Positive and Negative Rust Adequacy Canaries (`#100` §6.2, `#109`)
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

/-- Positive adequacy canary (`#100` §6.2): a pure infinite loop (`loop {}`)
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

/-- Negative adequacy canary (`#100` §6.2): returning an uninitialized `_0`
    triggers `.failed .ub` at step `1` and therefore refutes `MirLang.WellFormed`. -/
theorem canary_uninit_return_violates_wellFormed :
    ¬ (MirSem uninitReturnBody ≤ MirLang.WellFormed) := by
  intro hWF
  let s0 : MirState := {
    locals := fun _ => none
    mem := MemState.empty
    block := 0
    stmtIdx := 0
  }
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

/-- Negative adequacy canary (`#109`): returning constant `0` instead of `_1`
    violates `EnsuresEqArg 1` when `_1 = MirVal.usize 1`. -/
theorem canary_wrong_id_violates_ensures :
    ¬ (MirSem wrongReturnZeroBody ≤ EnsuresEqArg 1) := by
  intro hEns
  let locals0 : Nat → Option MirVal :=
    updateLocal (fun _ => none) 1 (some (.usize 1))
  let s0 : MirState := {
    locals := locals0
    mem := MemState.empty
    block := 0
    stmtIdx := 0
  }
  let s1 : MirState := {
    locals := updateLocal locals0 0 (some (.usize 0))
    mem := MemState.empty
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

/-- MIR body that accepts `_1 : &AtomicUsize` (`MirTy.refAtomicUsize`) and
    returns constant `0` instead of loading from `_1`. -/
def wrongAtomicReturnZeroBody : MirBody where
  argTys := [.refAtomicUsize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.assign ⟨0⟩ (.use (.constVal (.usize 0)))]
      terminator := .return_ }
  ]

/-- Negative adequacy canary for weak-memory atomic loads: returning constant `0`
    without reading `_1` violates `EnsuresAtomicLoad 1` when location `0`'s only
    visible modification-order message has `bits = 1`. -/
theorem canary_wrong_atomic_load_violates_ensures :
    ¬ (MirSem wrongAtomicReturnZeroBody ≤ EnsuresAtomicLoad 1) := by
  intro hEns
  let msg0 : AtomicMsg := { loc := 0, ts := 0, bits := 1, relView := View.bot }
  let mem0 : MemState := { MemState.empty with atomicMsgs := [msg0] }
  let locals0 : Nat → Option MirVal :=
    updateLocal (fun _ => none) 1 (some (.atomicLoc 0))
  let s0 : MirState := {
    locals := locals0
    mem := mem0
    block := 0
    stmtIdx := 0
  }
  let s1 : MirState := {
    locals := updateLocal locals0 0 (some (.usize 0))
    mem := mem0
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
  have hvis : mem0.visibleAtomicMsgs 0 ≠ [] := by
    intro hnil
    cases hnil
  have hinit : initMirState wrongAtomicReturnZeroBody s0 :=
    ⟨rfl, rfl, rfl, ⟨⟨MirVal.atomicLoc 0, rfl, hvis⟩, hrest⟩⟩
  have hreach1 : ReachesPrefix MirMachine wrongAtomicReturnZeroBody s0 1 s1 []
      (PrefixOutcome.terminated (TerminationKind.normal (MirVal.usize 0))) :=
    ReachesPrefix.terminated 0 s1 (TerminationKind.normal (MirVal.usize 0)) rfl
  have hreach2 : ReachesPrefix MirMachine wrongAtomicReturnZeroBody s0 2 s0 [()]
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
    have hpfx : (MirSem wrongAtomicReturnZeroBody q).val hdef out := ⟨hinit, hreach2⟩
    have hpost := hval out hpfx (MirVal.usize 0) rfl
    cases hpost with
    | intro loc hpost2 =>
      cases hpost2 with
      | intro msg hprops =>
        have hloc : q.init.locals 1 = some (MirVal.atomicLoc 0) := rfl
        have hloc_eq := hprops.1
        rw [hloc] at hloc_eq
        injection hloc_eq with hval'
        injection hval' with hloc0
        subst hloc0
        have hmem : msg ∈ [msg0] := hprops.2.1
        cases hmem with
        | head =>
          have hret := hprops.2.2
          injection hret with hbits
          cases hbits
        | tail _ htail =>
          cases htail

end Anneal
