/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.Simulation

/-!
# Whole executions

`step_correspondence` lifted to whole executions. On the Anneal side we use
Anneal's own semantics of a body: the interaction tree
`MirSemantics.mirTree body s` (the `ITree.cofix` of the trusted coalgebra
`stepMirState`) together with the trusted reachability predicates
`Trusted.ITree.Reaches`, `ReachesRet`, and `FaultNow`. On the MiniRust side we
iterate `Machine::step` (`Interp.steps`).

* `run_ret`: if Anneal's tree returns `v` along some trace, MiniRust performs
  the corresponding function return (`ReturnRel`) after finitely many steps.
* `run_ub`: if Anneal's tree can reach UB, MiniRust raises UB after finitely
  many steps.
* `steps_error`: conversely, if MiniRust stops with *any* error from related
  states, then either that error is UB and Anneal's tree reaches UB, or
  Anneal's tree returned first (after which MiniRust is executing the caller,
  which the relation does not describe). In particular MiniRust never panics,
  deadlocks, or hits an unsupported construct while it runs a fragment body.
-/

namespace MiniRustSpec.Correspondence

open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRustSpec
open MiniRustSpec.Interp

theorem mirTree_observe (body : CapturedMir) (s : MachineState) :
    (mirTree body s).observe = (stepMirFn body s).map (ITree.cofix (stepMirState body)) := by
  simp [mirTree, ITree.observe_cofix, stepMirState]

theorem steps_add (a b : Nat) (m : Mach) :
    Interp.steps (a + b) m = Interp.steps a m >>= Interp.steps b := by
  induction a generalizing m with
  | zero => simp [Interp.steps]
  | succ a ih =>
    rw [Nat.add_right_comm a 1 b]
    simp only [Interp.steps]
    cases h : Interp.step m with
    | error e => simp
    | ok m1 => simp [ih]

theorem tauStar_reaches {t u : ITree MirEffect MirOutcome} (h : TauStar t u) : Reaches t [] u := by
  induction h with
  | refl t => exact .refl t
  | step hobs _ ih => exact .tau hobs ih

/-- Every Anneal execution prefix from related states is matched by MiniRust
steps to a related state. -/
theorem reaches_rel {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) {t u : ITree MirEffect MirOutcome}
    {tr : List (Event MirEffect)} (h : Reaches t tr u) :
    ∀ (s : MachineState) (m : Mach), t = mirTree body s → StateRel body f ctx s m →
      ∃ (n : Nat) (s' : MachineState) (m' : Mach), Interp.steps n m = .ok m' ∧
        StateRel body f ctx s' m' ∧ u = mirTree body s' := by
  induction h with
  | refl t =>
    intro s m ht hrel
    exact ⟨0, s, m, rfl, hrel, ht⟩
  | tau hobs _ ih =>
    intro s m ht hrel
    subst ht
    have hsr := step_correspondence body f hfrag hf ctx s m hrel
    rw [mirTree_observe] at hobs
    generalize stepMirFn body s = node at hsr hobs
    cases node with
    | ret r => simp [ITreeF.map] at hobs
    | vis i k => simp [ITreeF.map] at hobs
    | tau x =>
      simp only [ITreeF.map, ITreeF.tau.injEq] at hobs
      cases x with
      | running s1 =>
        obtain ⟨m1, hm1, hrel1⟩ := hsr
        obtain ⟨n, s', m', hsteps, hrel', hu⟩ := ih s1 m1 hobs.symm hrel1
        exact ⟨n + 1, s', m', by simp [Interp.steps, hm1, hsteps], hrel', hu⟩
      | halted _ => exact False.elim hsr
      | faulted _ => exact False.elim hsr
  | vis hobs hnf o _ ih =>
    intro s m ht hrel
    subst ht
    have hsr := step_correspondence body f hfrag hf ctx s m hrel
    rw [mirTree_observe] at hobs
    generalize stepMirFn body s = node at hsr hobs
    cases node with
    | ret r => simp [ITreeF.map] at hobs
    | tau x => simp [ITreeF.map] at hobs
    | vis i0 k0 =>
      simp only [ITreeF.map] at hobs
      injection hobs with hi hk
      subst hi
      have hk' := eq_of_heq hk
      subst hk'
      cases i0 with
      | inl a => exact False.elim (hnf trivial)
      | inr b =>
        cases b with
        | inr c => exact False.elim hsr
        | inl ob =>
          obtain ⟨s1, m1, hk1, hm1, hrel1⟩ := hsr
          cases o
          have ht' : ITree.cofix (stepMirState body) (k0 PUnit.unit) = mirTree body s1 := by
            rw [hk1]; rfl
          obtain ⟨n, s', m', hsteps, hrel', hu⟩ := ih s1 m1 ht' hrel1
          exact ⟨n + 1, s', m', by simp [Interp.steps, hm1, hsteps], hrel', hu⟩

/-- **Returns.** If Anneal's semantics of `body` from `s` returns `v` (along
any trace of branch observations), MiniRust, started from a related machine,
performs the corresponding function return after finitely many steps. -/
theorem run_ret {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRel body f ctx s m) {tr : List (Event MirEffect)} {v : Value}
    {mem : MirSemantics.Memory} (hret : ReachesRet (mirTree body s) tr (.normal (v, mem))) :
    ∃ (n : Nat) (s' : MachineState) (m' : Mach),
      Interp.steps n m = .ok m' ∧ ReturnRel body ctx s' v m' := by
  obtain ⟨u, hreach, hu⟩ := hret
  obtain ⟨n, s', m', hsteps, hrel', rfl⟩ := reaches_rel hfrag hf ctx hreach s m rfl hrel
  have hsr := step_correspondence body f hfrag hf ctx s' m' hrel'
  rw [mirTree_observe] at hu
  generalize stepMirFn body s' = node at hsr hu
  cases node with
  | tau x => simp [ITreeF.map] at hu
  | vis i k => simp [ITreeF.map] at hu
  | ret r =>
    simp only [ITreeF.map, ITreeF.ret.injEq] at hu
    subst hu
    obtain ⟨m'', hm'', hret⟩ := hsr
    exact ⟨n + 1, s', m'', by rw [steps_add, hsteps]; simp [Interp.steps, hm''], hret⟩

/-- **Returns from `f.start`.** Starting MiniRust at the `minimize` entry
block (`f.start = bbName body.basicBlocks.length`) steps through `initBlock`
into `bb0` and then matches Anneal's return from `s` (`blockIdx = 0`,
`stmtIdx = 0`). -/
theorem run_ret_from_start {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (s : MachineState) (m0 mInit : Mach)
    (hrel : StateRel body f ctx s m0) (hb0 : s.frame.blockIdx = 0) (hs0 : s.frame.stmtIdx = 0)
    (hinit : Shape mInit ctx
      [ctx.caller, calleeFrame f ctx body.localDecls.length body.basicBlocks.length 0]
      (ctx.base ++ localAllocs ctx body.localDecls s.frame.locals))
    {tr : List (Event MirEffect)} {v : Value} {mem : MirSemantics.Memory}
    (hret : ReachesRet (mirTree body s) tr (.normal (v, mem))) :
    ∃ (n : Nat) (s' : MachineState) (m' : Mach),
      Interp.steps n mInit = .ok m' ∧ ReturnRel body ctx s' v m' := by
  obtain ⟨m1, hm1, hrel1⟩ := step_start hf hrel hb0 hs0 hinit
  obtain ⟨n, s', m', hsteps, hret'⟩ := run_ret hfrag hf ctx s m1 hrel1 hret
  exact ⟨n + 1, s', m', by simp [Interp.steps, hm1, hsteps], hret'⟩

/-- **UB.** If Anneal's semantics of `body` from `s` can reach UB (along any
trace of branch observations), MiniRust, started from a related machine,
raises UB after finitely many steps. -/
theorem run_ub {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRel body f ctx s m) {tr : List (Event MirEffect)} {u : ITree MirEffect MirOutcome}
    (hreach : Reaches (mirTree body s) tr u) (hfault : FaultNow u) :
    ∃ (n : Nat) (msg : String), Interp.steps n m = .error (.ub msg) := by
  obtain ⟨t', i, k, htau, hobs, hfi⟩ := hfault
  obtain ⟨n1, s1, m1, h1, hrel1, rfl⟩ := reaches_rel hfrag hf ctx hreach s m rfl hrel
  obtain ⟨n2, s2, m2, h2, hrel2, rfl⟩ :=
    reaches_rel hfrag hf ctx (tauStar_reaches htau) s1 m1 rfl hrel1
  have hsr := step_correspondence body f hfrag hf ctx s2 m2 hrel2
  rw [mirTree_observe] at hobs
  generalize stepMirFn body s2 = node at hsr hobs
  cases node with
  | ret r => simp [ITreeF.map] at hobs
  | tau x => simp [ITreeF.map] at hobs
  | vis i0 k0 =>
    simp only [ITreeF.map] at hobs
    injection hobs with hi _
    subst hi
    cases i0 with
    | inr b =>
      cases b with
      | inl _ => exact False.elim hfi
      | inr _ => exact False.elim hfi
    | inl a =>
      cases a with
      | fail fk =>
        cases fk with
        | unsupported => exact False.elim hsr
        | outOfFuel => exact False.elim hsr
        | ub =>
          obtain ⟨msg, hmsg⟩ := hsr
          refine ⟨n1 + n2 + 1, msg, ?_⟩
          rw [steps_add, steps_add, h1]
          simp [h2, Interp.steps, hmsg]

/-- **UB from `f.start`.** Starting MiniRust at the `minimize` entry block
(`f.start = bbName body.basicBlocks.length`) steps through `initBlock` into
`bb0` and then raises UB whenever Anneal's semantics from `s` (`blockIdx = 0`,
`stmtIdx = 0`) can reach UB. -/
theorem run_ub_from_start {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (s : MachineState) (m0 mInit : Mach)
    (hrel : StateRel body f ctx s m0) (hb0 : s.frame.blockIdx = 0) (hs0 : s.frame.stmtIdx = 0)
    (hinit : Shape mInit ctx
      [ctx.caller, calleeFrame f ctx body.localDecls.length body.basicBlocks.length 0]
      (ctx.base ++ localAllocs ctx body.localDecls s.frame.locals))
    {tr : List (Event MirEffect)} {u : ITree MirEffect MirOutcome}
    (hreach : Reaches (mirTree body s) tr u) (hfault : FaultNow u) :
    ∃ (n : Nat) (msg : String), Interp.steps n mInit = .error (.ub msg) := by
  obtain ⟨m1, hm1, hrel1⟩ := step_start hf hrel hb0 hs0 hinit
  obtain ⟨n, msg, hsteps⟩ := run_ub hfrag hf ctx s m1 hrel1 hreach hfault
  exact ⟨n + 1, msg, by simp [Interp.steps, hm1, hsteps]⟩

/-- **Errors.** If MiniRust stops with an error `e` within `n` steps of a
related machine, then `e` is UB and Anneal's semantics can reach UB, or
Anneal's semantics returns before MiniRust's error. -/
theorem steps_error {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (n : Nat) :
    ∀ (s : MachineState) (m : Mach) (e : Stop), StateRel body f ctx s m →
      Interp.steps n m = .error e →
      (∃ msg, e = .ub msg ∧ ∃ tr u, Reaches (mirTree body s) tr u ∧ FaultNow u) ∨
      (∃ tr v mem, ReachesRet (mirTree body s) tr (.normal (v, mem))) := by
  induction n with
  | zero => intro s m e _ h; simp [Interp.steps] at h
  | succ n ih =>
    intro s m e hrel h
    have hsr := step_correspondence body f hfrag hf ctx s m hrel
    have hobs := mirTree_observe body s
    generalize stepMirFn body s = node at hsr hobs
    cases node with
    | tau x =>
      simp only [ITreeF.map] at hobs
      cases x with
      | running s1 =>
        obtain ⟨m1, hm1, hrel1⟩ := hsr
        simp only [Interp.steps, hm1, ok_bind] at h
        rcases ih s1 m1 e hrel1 h with ⟨msg, he, tr, u, hr, hfault⟩ | ⟨tr, v, mem, u, hr, hu⟩
        · exact .inl ⟨msg, he, tr, u, .tau hobs hr, hfault⟩
        · exact .inr ⟨tr, v, mem, u, .tau hobs hr, hu⟩
      | halted _ => exact False.elim hsr
      | faulted _ => exact False.elim hsr
    | ret r =>
      simp only [ITreeF.map] at hobs
      cases r with
      | normal p => exact .inr ⟨[], p.1, p.2, mirTree body s, .refl _, hobs⟩
      | panic => exact False.elim hsr
      | abort => exact False.elim hsr
    | vis i0 k0 =>
      simp only [ITreeF.map] at hobs
      cases i0 with
      | inl a =>
        cases a with
        | fail fk =>
          cases fk with
          | unsupported => exact False.elim hsr
          | outOfFuel => exact False.elim hsr
          | ub =>
            obtain ⟨msg, hmsg⟩ := hsr
            simp [Interp.steps, hmsg] at h
            exact .inl ⟨msg, h.symm, [], mirTree body s, .refl _,
              ⟨mirTree body s, _, _, .refl _, hobs, trivial⟩⟩
      | inr b =>
        cases b with
        | inr _ => exact False.elim hsr
        | inl ob =>
          obtain ⟨s1, m1, hk1, hm1, hrel1⟩ := hsr
          simp only [Interp.steps, hm1, ok_bind] at h
          have hnext : ITree.cofix (stepMirState body) (k0 PUnit.unit) = mirTree body s1 := by
            rw [hk1]; rfl
          rcases ih s1 m1 e hrel1 h with ⟨msg, he, tr, u, hr, hfault⟩ | ⟨tr, v, mem, u, hr, hu⟩
          · refine .inl ⟨msg, he, ⟨.inr (.inl ob), PUnit.unit⟩ :: tr, u,
              .vis hobs (fun h => h) PUnit.unit ?_, hfault⟩
            rw [hnext]; exact hr
          · refine .inr ⟨⟨.inr (.inl ob), PUnit.unit⟩ :: tr, v, mem, u,
              .vis hobs (fun h => h) PUnit.unit ?_, hu⟩
            rw [hnext]; exact hr

/-! ## Running Anneal's semantics on concrete bodies

`runA` executes Anneal's step function for at most `fuel` steps, following
silent steps and branch observations and recording the observations;
`runA_sound` shows that a result of `runA` is a genuine `ReachesRet` of
Anneal's interaction tree. Witnesses use it to *compute* Anneal executions
inside the kernel instead of asserting them. -/

/-- Fuel-bounded execution of `stepMirFn` up to a terminal outcome. -/
def runA (body : CapturedMir) : Nat → MachineState → Option (List (Event MirEffect) × MirOutcome)
  | 0, _ => none
  | fuel + 1, s =>
    match stepMirFn body s with
    | .tau (.running s') => runA body fuel s'
    | .vis (.inr (.inl (.emit ev))) k =>
      match k PUnit.unit with
      | .running s' =>
        (runA body fuel s').map (fun r => (⟨.inr (.inl (.emit ev)), PUnit.unit⟩ :: r.1, r.2))
      | _ => none
    | .ret o => some ([], o)
    | _ => none

/-- `runA body fuel s` stops (as `none`) at the first fault of `body`. -/
def faultsA (body : CapturedMir) : Nat → MachineState → Bool
  | 0, _ => false
  | fuel + 1, s =>
    match stepMirFn body s with
    | .tau (.running s') => faultsA body fuel s'
    | .vis (.inr (.inl (.emit _))) k =>
      match k PUnit.unit with
      | .running s' => faultsA body fuel s'
      | _ => false
    | .vis (.inl (.fail _)) _ => true
    | _ => false

theorem runA_sound (body : CapturedMir) (fuel : Nat) :
    ∀ (s : MachineState) (tr : List (Event MirEffect)) (o : MirOutcome),
      runA body fuel s = some (tr, o) → ReachesRet (mirTree body s) tr o := by
  induction fuel with
  | zero => intro s tr o h; simp [runA] at h
  | succ fuel ih =>
    intro s tr o h
    have hobs := mirTree_observe body s
    simp only [runA] at h
    generalize stepMirFn body s = node at h hobs
    cases node with
    | tau x =>
      cases x with
      | running s' =>
        obtain ⟨u, hr, hu⟩ := ih s' tr o h
        exact ⟨u, .tau hobs hr, hu⟩
      | halted _ => simp at h
      | faulted _ => simp at h
    | ret o' =>
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨mirTree body s, .refl _, hobs⟩
    | vis i k =>
      cases i with
      | inl _ => simp at h
      | inr b =>
        cases b with
        | inr _ => simp at h
        | inl ob =>
          cases ob with
          | emit ev =>
            simp only at h
            generalize hk : k PUnit.unit = x at h
            cases x with
            | halted _ => simp at h
            | faulted _ => simp at h
            | running s' =>
              cases hrun : runA body fuel s' with
              | none => simp [hrun] at h
              | some p =>
                simp [hrun] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨u, hr, hu⟩ := ih s' p.1 p.2 hrun
                refine ⟨u, .vis hobs (fun h => h) PUnit.unit ?_, hu⟩
                show Reaches (ITree.cofix (stepMirState body) (k PUnit.unit)) p.1 u
                rw [hk]; exact hr

theorem faultsA_sound (body : CapturedMir) (fuel : Nat) :
    ∀ (s : MachineState), faultsA body fuel s = true →
      ∃ tr u, Reaches (mirTree body s) tr u ∧ FaultNow u := by
  induction fuel with
  | zero => intro s h; simp [faultsA] at h
  | succ fuel ih =>
    intro s h
    have hobs := mirTree_observe body s
    simp only [faultsA] at h
    generalize stepMirFn body s = node at h hobs
    cases node with
    | tau x =>
      cases x with
      | running s' =>
        obtain ⟨tr, u, hr, hu⟩ := ih s' h
        exact ⟨tr, u, .tau hobs hr, hu⟩
      | halted _ => simp at h
      | faulted _ => simp at h
    | ret o' => simp at h
    | vis i k =>
      cases i with
      | inl a =>
        cases a with
        | fail fk =>
          exact ⟨[], mirTree body s, .refl _, ⟨mirTree body s, _, _, .refl _, hobs, trivial⟩⟩
      | inr b =>
        cases b with
        | inr _ => simp at h
        | inl ob =>
          cases ob with
          | emit ev =>
            simp only at h
            generalize hk : k PUnit.unit = x at h
            cases x with
            | halted _ => simp at h
            | faulted _ => simp at h
            | running s' =>
              obtain ⟨tr, u, hr, hu⟩ := ih s' h
              refine ⟨⟨.inr (.inl (.emit ev)), PUnit.unit⟩ :: tr, u,
                .vis hobs (fun h => h) PUnit.unit ?_, hu⟩
              show Reaches (ITree.cofix (stepMirState body) (k PUnit.unit)) tr u
              rw [hk]; exact hr

end MiniRustSpec.Correspondence
