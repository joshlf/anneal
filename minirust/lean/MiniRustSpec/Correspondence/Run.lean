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

* `run_ret` / `run_ret_from_start` / `mirCall_ret`: if Anneal's tree returns
  `v` along some trace, MiniRust performs the corresponding function return
  (`ReturnRel`) after finitely many steps.
* `run_ub` / `run_ub_from_start` / `mirCall_ub`: if Anneal's tree can reach UB,
  MiniRust raises UB after finitely many steps.
* `steps_error` / `steps_error_from_start`: conversely, if MiniRust stops with
  *any* error within `n` steps of related states, then either that error is UB
  and Anneal's tree reaches UB, or MiniRust already completed the callee's
  return (`ReturnRel`, matching an Anneal `ReachesRet`) in `k < n` steps and
  only errored later inside the unmodeled caller frame. In particular, MiniRust
  never panics, deadlocks, or hits an unsupported construct while running a
  fragment body.
* `mirNoUB_safe` / `mirNoUB_safe_from_start` / `mirCall_noUB`: if Anneal's tree
  satisfies `MirNoUBTree` (`TreeSafe`), MiniRust never stops with any error
  anywhere during the callee's execution.
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

/-- Monotonicity of `.ok` across step prefixes: if `Interp.steps k m = .ok m'`,
then every prefix `j ≤ k` also succeeds (`∃ mj, Interp.steps j m = .ok mj`),
so no error (`.ub`, `.specPanic`, `.deadlock`, or `.unsupported`) occurs at any
step `j ≤ k`. -/
theorem steps_ok_mono {j k : Nat} {m m' : Mach} (hj : j ≤ k) (hk : Interp.steps k m = .ok m') :
    ∃ mj, Interp.steps j m = .ok mj := by
  have hsplit : k = j + (k - j) := by omega
  rw [hsplit, steps_add] at hk
  cases hjsteps : Interp.steps j m with
  | error e => simp [hjsteps] at hk
  | ok mj => exact ⟨mj, rfl⟩

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
block (`f.start = bbName body.basicBlocks.length`) under `StartRel` steps
through `initBlock` into `bb0` and then matches Anneal's return from `s`. -/
theorem run_ret_from_start {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (s : MachineState) (mInit : Mach)
    (hstart : StartRel body f ctx s mInit)
    {tr : List (Event MirEffect)} {v : Value} {mem : MirSemantics.Memory}
    (hret : ReachesRet (mirTree body s) tr (.normal (v, mem))) :
    ∃ (n : Nat) (s' : MachineState) (m' : Mach),
      Interp.steps n mInit = .ok m' ∧ ReturnRel body ctx s' v m' := by
  obtain ⟨m0, hm0, hrel0⟩ := step_start hfrag hf hstart
  obtain ⟨n, s', m', hsteps, hret'⟩ := run_ret hfrag hf ctx s m0 hrel0 hret
  exact ⟨initLen body + n, s', m', by rw [steps_add, hm0, ok_bind, hsteps], hret'⟩

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
(`f.start = bbName body.basicBlocks.length`) under `StartRel` steps through
`initBlock` into `bb0` and then raises UB whenever Anneal's semantics from `s`
can reach UB. -/
theorem run_ub_from_start {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (s : MachineState) (mInit : Mach)
    (hstart : StartRel body f ctx s mInit)
    {tr : List (Event MirEffect)} {u : ITree MirEffect MirOutcome}
    (hreach : Reaches (mirTree body s) tr u) (hfault : FaultNow u) :
    ∃ (n : Nat) (msg : String), Interp.steps n mInit = .error (.ub msg) := by
  obtain ⟨m0, hm0, hrel0⟩ := step_start hfrag hf hstart
  obtain ⟨n, msg, hsteps⟩ := run_ub hfrag hf ctx s m0 hrel0 hreach hfault
  exact ⟨initLen body + n, msg, by rw [steps_add, hm0, ok_bind, hsteps]⟩

/-- **Errors.** If MiniRust stops with an error `e` within `n` steps of a
related machine, then either `e` is UB and Anneal's semantics can reach UB, or
MiniRust already completed the callee's return (`ReturnRel`, matching an Anneal
`ReachesRet`) in `k < n` steps and only errored later inside the unmodeled
caller frame. -/
theorem steps_error {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (n : Nat) :
    ∀ (s : MachineState) (m : Mach) (e : Stop), StateRel body f ctx s m →
      Interp.steps n m = .error e →
      (∃ msg, e = .ub msg ∧ ∃ tr u, Reaches (mirTree body s) tr u ∧ FaultNow u) ∨
      (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k m = .ok mRet ∧
        ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem))) := by
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
        rcases ih s1 m1 e hrel1 h with
          ⟨msg, he, tr, u, hr, hfault⟩ | ⟨k, s', mRet, tr, v, mem, hklt, hksteps, hretRel, u, hr, hu⟩
        · exact .inl ⟨msg, he, tr, u, .tau hobs hr, hfault⟩
        · exact .inr ⟨k + 1, s', mRet, tr, v, mem, by omega,
            by simp [Interp.steps, hm1, hksteps], hretRel, u, .tau hobs hr, hu⟩
      | halted _ => exact False.elim hsr
      | faulted _ => exact False.elim hsr
    | ret r =>
      simp only [ITreeF.map] at hobs
      cases r with
      | normal p =>
        obtain ⟨mRet, hmRet, hretRel⟩ := hsr
        cases n with
        | zero => simp [Interp.steps, hmRet] at h
        | succ n' =>
          exact .inr ⟨1, s, mRet, [], p.1, p.2, by omega,
            by simp [Interp.steps, hmRet], hretRel, mirTree body s, .refl _, hobs⟩
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
          rcases ih s1 m1 e hrel1 h with
            ⟨msg, he, tr, u, hr, hfault⟩ | ⟨k, s', mRet, tr, v, mem, hklt, hksteps, hretRel, u, hr, hu⟩
          · refine .inl ⟨msg, he, ⟨.inr (.inl ob), PUnit.unit⟩ :: tr, u,
              .vis hobs (fun h => h) PUnit.unit ?_, hfault⟩
            rw [hnext]; exact hr
          · refine .inr ⟨k + 1, s', mRet, ⟨.inr (.inl ob), PUnit.unit⟩ :: tr, v, mem, by omega,
              by simp [Interp.steps, hm1, hksteps], hretRel, u,
              .vis hobs (fun h => h) PUnit.unit ?_, hu⟩
            rw [hnext]; exact hr

/-- **Errors from `f.start`.** Converse soundness starting at MiniRust's
`f.start` (`initBlock`): if MiniRust stops with an error `e` within `n` steps
from `StartRel`, then either `e` is UB and Anneal reaches UB, or MiniRust
already completed the callee's return (`ReturnRel`, matching an Anneal
`ReachesRet`) in `k < n` steps. -/
theorem steps_error_from_start {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (n : Nat) (s : MachineState) (mInit : Mach) (e : Stop)
    (hstart : StartRel body f ctx s mInit) (h : Interp.steps n mInit = .error e) :
    (∃ msg, e = .ub msg ∧ ∃ tr u, Reaches (mirTree body s) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem))) := by
  obtain ⟨m0, hm0, hrel0⟩ := step_start hfrag hf hstart
  by_cases hn : n ≤ initLen body
  · obtain ⟨mj, hmj⟩ := steps_ok_mono hn hm0
    rw [hmj] at h
    cases h
  · obtain ⟨n', rfl⟩ : ∃ n', n = initLen body + n' := ⟨n - initLen body, by omega⟩
    rw [steps_add, hm0, ok_bind] at h
    rcases steps_error hfrag hf ctx n' s m0 e hrel0 h with
      hUb | ⟨k, s', mRet, tr, v, mem, hklt, hksteps, hretRel, hret⟩
    · exact .inl hUb
    · exact .inr ⟨initLen body + k, s', mRet, tr, v, mem, by omega,
        by rw [steps_add, hm0, ok_bind, hksteps], hretRel, hret⟩

/-- **UB-freedom transfer.** If Anneal's interaction tree satisfies
`MirNoUBTree` (`TreeSafe`), MiniRust never stops with any error (`.ub`,
`.specPanic`, `.deadlock`, or `.unsupported`) during the callee's execution:
any error within `n` steps occurs strictly after `k < n` steps at which
MiniRust has already returned normally via `ReturnRel`. -/
theorem mirNoUB_safe {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRel body f ctx s m) (hsafe : MirNoUBTree (mirTree body s))
    {n : Nat} {e : Stop} (herr : Interp.steps n m = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k m = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem)) := by
  rcases steps_error hfrag hf ctx n s m e hrel herr with ⟨_, _, tr, u, hr, hfault⟩ | hret
  · exact False.elim (hsafe tr u hr hfault)
  · exact hret

/-- **UB-freedom transfer from `f.start`.** Same guarantee starting at
`minimize`'s entry block `f.start`. -/
theorem mirNoUB_safe_from_start {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (s : MachineState) (mInit : Mach)
    (hstart : StartRel body f ctx s mInit) (hsafe : MirNoUBTree (mirTree body s))
    {n : Nat} {e : Stop} (herr : Interp.steps n mInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem)) := by
  rcases steps_error_from_start hfrag hf ctx n s mInit e hstart herr with
    ⟨_, _, tr, u, hr, hfault⟩ | hret
  · exact False.elim (hsafe tr u hr hfault)
  · exact hret

/-- **Total `n`-step outcome trichotomy.** From related states `StateRel`, for
every step budget `n : Nat`, running MiniRust for `n` steps produces one of
three mutually coupled outcomes:
1. MiniRust takes `n` `.ok` steps to `m'` still in lockstep `StateRel` with an
   Anneal state `s'` reachable via `Reaches (mirTree body s) tr (mirTree body s')`;
2. MiniRust already completed the callee's return (`ReturnRel`, matching an
   Anneal `ReachesRet`) in `k ≤ n` steps; or
3. MiniRust stopped with `.error (.ub msg)` within `n` steps and Anneal's
   interaction tree reaches a fault (`FaultNow`). -/
theorem steps_outcome {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (n : Nat) :
    ∀ (s : MachineState) (m : Mach), StateRel body f ctx s m →
      (∃ s' m' tr, Interp.steps n m = .ok m' ∧ StateRel body f ctx s' m' ∧
        Reaches (mirTree body s) tr (mirTree body s')) ∨
      (∃ k s' mRet tr v mem, k ≤ n ∧ Interp.steps k m = .ok mRet ∧
        ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem))) ∨
      (∃ msg, Interp.steps n m = .error (.ub msg) ∧
        ∃ tr u, Reaches (mirTree body s) tr u ∧ FaultNow u) := by
  induction n with
  | zero =>
    intro s m hrel
    exact .inl ⟨s, m, [], rfl, hrel, .refl _⟩
  | succ n ih =>
    intro s m hrel
    have hsr := step_correspondence body f hfrag hf ctx s m hrel
    have hobs := mirTree_observe body s
    generalize stepMirFn body s = node at hsr hobs
    cases node with
    | tau x =>
      simp only [ITreeF.map] at hobs
      cases x with
      | running s1 =>
        obtain ⟨m1, hm1, hrel1⟩ := hsr
        rcases ih s1 m1 hrel1 with
          ⟨s', m', tr, hsteps, hrel', hr⟩ |
          ⟨k, s', mRet, tr, v, mem, hkle, hksteps, hretRel, u, hr, hu⟩ |
          ⟨msg, herr, tr, u, hr, hfault⟩
        · exact .inl ⟨s', m', tr, by simp [Interp.steps, hm1, hsteps], hrel', .tau hobs hr⟩
        · exact .inr (.inl ⟨k + 1, s', mRet, tr, v, mem, by omega,
            by simp [Interp.steps, hm1, hksteps], hretRel, u, .tau hobs hr, hu⟩)
        · exact .inr (.inr ⟨msg, by simp [Interp.steps, hm1, herr], tr, u, .tau hobs hr, hfault⟩)
      | halted _ => exact False.elim hsr
      | faulted _ => exact False.elim hsr
    | ret r =>
      simp only [ITreeF.map] at hobs
      cases r with
      | normal p =>
        obtain ⟨mRet, hmRet, hretRel⟩ := hsr
        exact .inr (.inl ⟨1, s, mRet, [], p.1, p.2, by omega,
          by simp [Interp.steps, hmRet], hretRel, mirTree body s, .refl _, hobs⟩)
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
            exact .inr (.inr ⟨msg, by simp [Interp.steps, hmsg], [], mirTree body s, .refl _,
              ⟨mirTree body s, _, _, .refl _, hobs, trivial⟩⟩)
      | inr b =>
        cases b with
        | inr _ => exact False.elim hsr
        | inl ob =>
          obtain ⟨s1, m1, hk1, hm1, hrel1⟩ := hsr
          have hnext : ITree.cofix (stepMirState body) (k0 PUnit.unit) = mirTree body s1 := by
            rw [hk1]; rfl
          rcases ih s1 m1 hrel1 with
            ⟨s', m', tr, hsteps, hrel', hr⟩ |
            ⟨k, s', mRet, tr, v, mem, hkle, hksteps, hretRel, u, hr, hu⟩ |
            ⟨msg, herr, tr, u, hr, hfault⟩
          · refine .inl ⟨s', m', ⟨.inr (.inl ob), PUnit.unit⟩ :: tr,
              by simp [Interp.steps, hm1, hsteps], hrel',
              .vis hobs (fun h => h) PUnit.unit ?_⟩
            rw [hnext]; exact hr
          · refine .inr (.inl ⟨k + 1, s', mRet, ⟨.inr (.inl ob), PUnit.unit⟩ :: tr,
              v, mem, by omega, by simp [Interp.steps, hm1, hksteps], hretRel, u,
              .vis hobs (fun h => h) PUnit.unit ?_, hu⟩)
            rw [hnext]; exact hr
          · refine .inr (.inr ⟨msg, by simp [Interp.steps, hm1, herr],
              ⟨.inr (.inl ob), PUnit.unit⟩ :: tr, u,
              .vis hobs (fun h => h) PUnit.unit ?_, hfault⟩)
            rw [hnext]; exact hr

/-- **Total `(initLen body + n)`-step outcome trichotomy from `f.start`.**
Starting at `minimize`'s entry block `f.start` (`StartRel`), running MiniRust
through the init block (`initLen body` steps) and then `n` more steps either:
1. advances `initLen body + n` `.ok` steps to `m'` in lockstep `StateRel` with
   an Anneal state `s'` reachable via `Reaches (mirTree body s) tr (mirTree body s')`;
2. already completed the callee's return (`ReturnRel`, matching an Anneal
   `ReachesRet`) in `k ≤ initLen body + n` steps; or
3. stopped with `.error (.ub msg)` within `initLen body + n` steps and Anneal's
   interaction tree reaches a fault (`FaultNow`). -/
theorem steps_outcome_from_start {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (n : Nat) (s : MachineState) (mInit : Mach)
    (hstart : StartRel body f ctx s mInit) :
    (∃ s' m' tr, Interp.steps (initLen body + n) mInit = .ok m' ∧ StateRel body f ctx s' m' ∧
      Reaches (mirTree body s) tr (mirTree body s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen body + n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (initLen body + n) mInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirTree body s) tr u ∧ FaultNow u) := by
  obtain ⟨m0, hm0, hrel0⟩ := step_start hfrag hf hstart
  rcases steps_outcome hfrag hf ctx n s m0 hrel0 with
    ⟨s', m', tr, hsteps, hrel', hr⟩ |
    ⟨k, s', mRet, tr, v, mem, hkle, hksteps, hretRel, hret⟩ |
    ⟨msg, herr, hfault⟩
  · exact .inl ⟨s', m', tr, by rw [steps_add, hm0, ok_bind, hsteps], hrel', hr⟩
  · exact .inr (.inl ⟨initLen body + k, s', mRet, tr, v, mem, by omega,
      by rw [steps_add, hm0, ok_bind, hksteps], hretRel, hret⟩)
  · exact .inr (.inr ⟨msg, by rw [steps_add, hm0, ok_bind, herr], hfault⟩)

/-- **Forward progress under `MirNoUBTree`.** When Anneal's interaction tree is
UB-free (`MirNoUBTree`), for every `n : Nat`, MiniRust either advances `n`
steps to a lockstep `StateRel` state `m'` or has already returned normally via
`ReturnRel` in `k ≤ n` steps. -/
theorem mirNoUB_progress {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRel body f ctx s m) (hsafe : MirNoUBTree (mirTree body s)) (n : Nat) :
    (∃ s' m' tr, Interp.steps n m = .ok m' ∧ StateRel body f ctx s' m' ∧
      Reaches (mirTree body s) tr (mirTree body s')) ∨
    (∃ k s' mRet tr v mem, k ≤ n ∧ Interp.steps k m = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem))) := by
  rcases steps_outcome hfrag hf ctx n s m hrel with hrun | hret | ⟨_, _, tr, u, hr, hfault⟩
  · exact .inl hrun
  · exact .inr hret
  · exact False.elim (hsafe tr u hr hfault)

/-- **Forward progress from `f.start` under `MirNoUBTree`.** For every `n : Nat`,
MiniRust started at `f.start` (`StartRel`) either advances `initLen body + n`
steps to a lockstep `StateRel` state `m'` or returns normally via `ReturnRel` in
`k ≤ initLen body + n` steps. -/
theorem mirNoUB_progress_from_start {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (s : MachineState) (mInit : Mach)
    (hstart : StartRel body f ctx s mInit) (hsafe : MirNoUBTree (mirTree body s)) (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen body + n) mInit = .ok m' ∧ StateRel body f ctx s' m' ∧
      Reaches (mirTree body s) tr (mirTree body s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen body + n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem))) := by
  obtain ⟨m0, hm0, hrel0⟩ := step_start hfrag hf hstart
  rcases mirNoUB_progress hfrag hf ctx s m0 hrel0 hsafe n with
    ⟨s', m', tr, hsteps, hrel', hr⟩ | ⟨k, s', mRet, tr, v, mem, hkle, hksteps, hretRel, hret⟩
  · exact .inl ⟨s', m', tr, by rw [steps_add, hm0, ok_bind, hsteps], hrel', hr⟩
  · exact .inr ⟨initLen body + k, s', mRet, tr, v, mem, by omega,
      by rw [steps_add, hm0, ok_bind, hksteps], hretRel, hret⟩

/-- **Diverging UB-free execution from `StateRel`.** If Anneal's interaction
tree is UB-free (`MirNoUBTree`) and never reaches a return outcome, MiniRust
steps forever in lockstep `StateRel` without ever stopping with an error. -/
theorem mirNoUB_diverges_steps_ok {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRel body f ctx s m) (hsafe : MirNoUBTree (mirTree body s))
    (hdiv : ∀ tr o, ¬ ReachesRet (mirTree body s) tr o) (n : Nat) :
    ∃ s' m' tr, Interp.steps n m = .ok m' ∧ StateRel body f ctx s' m' ∧
      Reaches (mirTree body s) tr (mirTree body s') := by
  rcases mirNoUB_progress hfrag hf ctx s m hrel hsafe n with
    hrun | ⟨_, _, _, tr, v, mem, _, _, _, hret⟩
  · exact hrun
  · exact False.elim (hdiv tr (.normal (v, mem)) hret)

/-- **Diverging UB-free execution from `f.start`.** If Anneal's interaction tree
is UB-free and never returns, MiniRust started at `f.start` (`StartRel`)
succeeds for every step count `n : Nat`. -/
theorem mirNoUB_diverges_from_start {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (s : MachineState) (mInit : Mach)
    (hstart : StartRel body f ctx s mInit) (hsafe : MirNoUBTree (mirTree body s))
    (hdiv : ∀ tr o, ¬ ReachesRet (mirTree body s) tr o) (n : Nat) :
    ∃ m', Interp.steps n mInit = .ok m' := by
  obtain ⟨m0, hm0, hrel0⟩ := step_start hfrag hf hstart
  by_cases hn : n ≤ initLen body
  · exact steps_ok_mono hn hm0
  · obtain ⟨n', rfl⟩ : ∃ n', n = initLen body + n' := ⟨n - initLen body, by omega⟩
    obtain ⟨_, m', _, hsteps, _, _⟩ :=
      mirNoUB_diverges_steps_ok hfrag hf ctx s m0 hrel0 hsafe hdiv n'
    exact ⟨m', by rw [steps_add, hm0, ok_bind, hsteps]⟩

/-- **Coupled diverging UB-free execution from `f.start`.** Unlike
`mirNoUB_diverges_from_start` (which discards the state relation), this theorem
preserves full `StateRel` + `Reaches` lockstep coupling after stepping past
`f.start` (`initBlock`): for every `n : Nat`, `initLen body + n` MiniRust steps
from `mInit` succeed at `m'` in `StateRel` with an Anneal state `s'` reachable
via `Reaches (mirTree body s) tr (mirTree body s')`. -/
theorem mirNoUB_diverges_rel_from_start {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (s : MachineState) (mInit : Mach)
    (hstart : StartRel body f ctx s mInit) (hsafe : MirNoUBTree (mirTree body s))
    (hdiv : ∀ tr o, ¬ ReachesRet (mirTree body s) tr o) (n : Nat) :
    ∃ s' m' tr, Interp.steps (initLen body + n) mInit = .ok m' ∧ StateRel body f ctx s' m' ∧
      Reaches (mirTree body s) tr (mirTree body s') := by
  obtain ⟨m0, hm0, hrel0⟩ := step_start hfrag hf hstart
  obtain ⟨s', m', tr, hsteps, hrel', hr⟩ :=
    mirNoUB_diverges_steps_ok hfrag hf ctx s m0 hrel0 hsafe hdiv n
  exact ⟨s', m', tr, by rw [steps_add, hm0, ok_bind, hsteps], hrel', hr⟩

/-! ## Top-level `mirCallTree` entry theorems -/

/-- **Call-tree return.** For any fragment `body` and well-typed `args`, if
`mirCallTree body args` returns `v`, MiniRust started at `f.start` performs the
corresponding return (`ReturnRel`) after finitely many steps. -/
theorem mirCall_ret {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (hctx : CtxOk body ctx)
    (args : List Value) (hargs : argsOk body args = true) (mInit : Mach)
    (hthreads : mInit.threads =
      [thread1 ctx [ctx.caller,
        { calleeFrame f ctx (body.argCount + 1) 0 0 with next_block := f.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      ctx.base ++ localAllocs ctx (body.localDecls.take (body.argCount + 1))
        (initMachineState body args).frame.locals)
    {tr : List (Event MirEffect)} {v : Value} {mem : MirSemantics.Memory}
    (hret : ReachesRet (mirCallTree body args) tr (.normal (v, mem))) :
    ∃ (n : Nat) (s' : MachineState) (m' : Mach),
      Interp.steps n mInit = .ok m' ∧ ReturnRel body ctx s' v m' :=
  run_ret_from_start hfrag hf ctx (initMachineState body args) mInit
    (initMachineState_startRel hfrag ctx hctx args hargs mInit hthreads hactive hallocs) hret

/-- **Call-tree UB.** If `mirCallTree body args` reaches UB, MiniRust started
at `f.start` raises UB after finitely many steps. -/
theorem mirCall_ub {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (hctx : CtxOk body ctx)
    (args : List Value) (hargs : argsOk body args = true) (mInit : Mach)
    (hthreads : mInit.threads =
      [thread1 ctx [ctx.caller,
        { calleeFrame f ctx (body.argCount + 1) 0 0 with next_block := f.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      ctx.base ++ localAllocs ctx (body.localDecls.take (body.argCount + 1))
        (initMachineState body args).frame.locals)
    {tr : List (Event MirEffect)} {u : ITree MirEffect MirOutcome}
    (hreach : Reaches (mirCallTree body args) tr u) (hfault : FaultNow u) :
    ∃ (n : Nat) (msg : String), Interp.steps n mInit = .error (.ub msg) :=
  run_ub_from_start hfrag hf ctx (initMachineState body args) mInit
    (initMachineState_startRel hfrag ctx hctx args hargs mInit hthreads hactive hallocs) hreach hfault

/-- **Call-tree UB-freedom transfer.** If `MirNoUBTree (mirCallTree body args)`
holds, MiniRust started at `f.start` never stops with any error during the
callee's execution. -/
theorem mirCall_noUB {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (hctx : CtxOk body ctx)
    (args : List Value) (hargs : argsOk body args = true) (mInit : Mach)
    (hthreads : mInit.threads =
      [thread1 ctx [ctx.caller,
        { calleeFrame f ctx (body.argCount + 1) 0 0 with next_block := f.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      ctx.base ++ localAllocs ctx (body.localDecls.take (body.argCount + 1))
        (initMachineState body args).frame.locals)
    (hsafe : MirNoUBTree (mirCallTree body args))
    {n : Nat} {e : Stop} (herr : Interp.steps n mInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirCallTree body args) tr (.normal (v, mem)) :=
  mirNoUB_safe_from_start hfrag hf ctx (initMachineState body args) mInit
    (initMachineState_startRel hfrag ctx hctx args hargs mInit hthreads hactive hallocs) hsafe herr

/-- **Call-tree forward progress.** Under `MirNoUBTree (mirCallTree body args)`,
for every `n : Nat`, MiniRust started at `f.start` either advances
`initLen body + n` steps to a lockstep `StateRel` state `m'` or returns
normally via `ReturnRel` in `k ≤ initLen body + n` steps. -/
theorem mirCall_progress {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (hctx : CtxOk body ctx)
    (args : List Value) (hargs : argsOk body args = true) (mInit : Mach)
    (hthreads : mInit.threads =
      [thread1 ctx [ctx.caller,
        { calleeFrame f ctx (body.argCount + 1) 0 0 with next_block := f.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      ctx.base ++ localAllocs ctx (body.localDecls.take (body.argCount + 1))
        (initMachineState body args).frame.locals)
    (hsafe : MirNoUBTree (mirCallTree body args)) (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen body + n) mInit = .ok m' ∧ StateRel body f ctx s' m' ∧
      Reaches (mirCallTree body args) tr (mirTree body s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen body + n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirCallTree body args) tr (.normal (v, mem))) :=
  mirNoUB_progress_from_start hfrag hf ctx (initMachineState body args) mInit
    (initMachineState_startRel hfrag ctx hctx args hargs mInit hthreads hactive hallocs) hsafe n

/-- **Call-tree diverging UB-free execution.** If `mirCallTree body args` is
UB-free (`MirNoUBTree`) and never returns, MiniRust started at `f.start`
succeeds for every step count `n : Nat`. -/
theorem mirCall_diverges_steps_ok {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (hctx : CtxOk body ctx) (args : List Value) (hargs : argsOk body args = true)
    (mInit : Mach)
    (hthreads : mInit.threads =
      [thread1 ctx [ctx.caller,
        { calleeFrame f ctx (body.argCount + 1) 0 0 with next_block := f.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      ctx.base ++ localAllocs ctx (body.localDecls.take (body.argCount + 1))
        (initMachineState body args).frame.locals)
    (hsafe : MirNoUBTree (mirCallTree body args))
    (hdiv : ∀ tr o, ¬ ReachesRet (mirCallTree body args) tr o) (n : Nat) :
    ∃ m', Interp.steps n mInit = .ok m' :=
  mirNoUB_diverges_from_start hfrag hf ctx (initMachineState body args) mInit
    (initMachineState_startRel hfrag ctx hctx args hargs mInit hthreads hactive hallocs) hsafe hdiv n

/-- **Call-tree converse error soundness.** If MiniRust started at `f.start`
stops with *any* error `e` within `n` steps, then either `e` is UB and
`mirCallTree body args` reaches UB (`FaultNow`), or MiniRust already completed
the callee's return (`ReturnRel`, matching `ReachesRet (mirCallTree body args)`)
in `k < n` steps and only errored later inside the unmodeled caller frame. -/
theorem mirCall_steps_error {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (hctx : CtxOk body ctx) (args : List Value) (hargs : argsOk body args = true)
    (mInit : Mach)
    (hthreads : mInit.threads =
      [thread1 ctx [ctx.caller,
        { calleeFrame f ctx (body.argCount + 1) 0 0 with next_block := f.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      ctx.base ++ localAllocs ctx (body.localDecls.take (body.argCount + 1))
        (initMachineState body args).frame.locals)
    {n : Nat} {e : Stop} (herr : Interp.steps n mInit = .error e) :
    (∃ msg, e = .ub msg ∧ ∃ tr u, Reaches (mirCallTree body args) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirCallTree body args) tr (.normal (v, mem))) :=
  steps_error_from_start hfrag hf ctx n (initMachineState body args) mInit e
    (initMachineState_startRel hfrag ctx hctx args hargs mInit hthreads hactive hallocs) herr

/-- **Call-tree total `(initLen body + n)`-step outcome trichotomy.** Unconditional
outcome trichotomy for `mirCallTree body args` from `f.start` (requiring no
`MirNoUBTree` hypothesis): `initLen body + n` MiniRust steps either stay in
lockstep `StateRel`, have returned normally via `ReturnRel` in
`k ≤ initLen body + n` steps, or
stop with UB matching an Anneal `FaultNow`. -/
theorem mirCall_outcome {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (hctx : CtxOk body ctx) (args : List Value) (hargs : argsOk body args = true)
    (mInit : Mach)
    (hthreads : mInit.threads =
      [thread1 ctx [ctx.caller,
        { calleeFrame f ctx (body.argCount + 1) 0 0 with next_block := f.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      ctx.base ++ localAllocs ctx (body.localDecls.take (body.argCount + 1))
        (initMachineState body args).frame.locals)
    (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen body + n) mInit = .ok m' ∧ StateRel body f ctx s' m' ∧
      Reaches (mirCallTree body args) tr (mirTree body s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen body + n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirCallTree body args) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (initLen body + n) mInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree body args) tr u ∧ FaultNow u) :=
  steps_outcome_from_start hfrag hf ctx n (initMachineState body args) mInit
    (initMachineState_startRel hfrag ctx hctx args hargs mInit hthreads hactive hallocs)

/-- **Call-tree coupled diverging UB-free execution.** Strengthens
`mirCall_diverges_steps_ok` by preserving full `StateRel` + `Reaches` lockstep
coupling across every `initLen body + n` steps from `f.start`. -/
theorem mirCall_diverges_rel {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (hctx : CtxOk body ctx) (args : List Value) (hargs : argsOk body args = true)
    (mInit : Mach)
    (hthreads : mInit.threads =
      [thread1 ctx [ctx.caller,
        { calleeFrame f ctx (body.argCount + 1) 0 0 with next_block := f.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      ctx.base ++ localAllocs ctx (body.localDecls.take (body.argCount + 1))
        (initMachineState body args).frame.locals)
    (hsafe : MirNoUBTree (mirCallTree body args))
    (hdiv : ∀ tr o, ¬ ReachesRet (mirCallTree body args) tr o) (n : Nat) :
    ∃ s' m' tr, Interp.steps (initLen body + n) mInit = .ok m' ∧ StateRel body f ctx s' m' ∧
      Reaches (mirCallTree body args) tr (mirTree body s') :=
  mirNoUB_diverges_rel_from_start hfrag hf ctx (initMachineState body args) mInit
    (initMachineState_startRel hfrag ctx hctx args hargs mInit hthreads hactive hallocs)
    hsafe hdiv n

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

theorem treeSafe_of_ret {t : ITree MirEffect MirOutcome} {o : MirOutcome}
    (hret : t.observe = .ret o) : TreeSafe t := by
  intro tr u hr
  cases hr with
  | refl =>
    rintro ⟨w, i, k, htau, hw, _⟩
    cases htau with
    | refl => simp [hret] at hw
    | step hs _ => simp [hret] at hs
  | tau hs _ => simp [hret] at hs
  | vis hs _ _ _ => simp [hret] at hs

theorem treeSafe_of_tau {t t' : ITree MirEffect MirOutcome}
    (htau_obs : t.observe = .tau t') (hsafe : TreeSafe t') : TreeSafe t := by
  intro tr u hr
  cases hr with
  | refl =>
    rintro ⟨w, i, k, htau, hw, hfi⟩
    cases htau with
    | refl => simp [htau_obs] at hw
    | step hs hrest =>
      rw [htau_obs] at hs
      injection hs with hs
      subst hs
      exact hsafe [] w (tauStar_reaches hrest) ⟨w, i, k, .refl _, hw, hfi⟩
  | tau hs hrest =>
    rw [htau_obs] at hs
    injection hs with hs
    subst hs
    exact hsafe tr u hrest
  | vis hs _ _ _ => simp [htau_obs] at hs

theorem treeSafe_of_emit {t : ITree MirEffect MirOutcome} {ev : MirObs}
    {k : PUnit → ITree MirEffect MirOutcome}
    (hvis : t.observe = .vis (.inr (.inl (.emit ev))) k)
    (hsafe : TreeSafe (k PUnit.unit)) : TreeSafe t := by
  intro tr u hr
  cases hr with
  | refl =>
    rintro ⟨w, i, k', htau, hw, hfi⟩
    cases htau with
    | refl =>
      rw [hvis] at hw
      injection hw with hi _
      subst hi
      exact hfi
    | step hs _ => simp [hvis] at hs
  | tau hs _ => simp [hvis] at hs
  | vis hs _ o hrest =>
    rw [hvis] at hs
    injection hs with hi hk
    subst hi
    have hk' := eq_of_heq hk
    subst hk'
    cases o
    exact hsafe _ u hrest

/-- Every successful fuel-bounded execution `runA body fuel s = some (tr, o)`
additionally establishes all-prefix UB-freedom (`MirNoUBTree (mirTree body s)`). -/
theorem runA_noUB (body : CapturedMir) (fuel : Nat) :
    ∀ (s : MachineState) (tr : List (Event MirEffect)) (o : MirOutcome),
      runA body fuel s = some (tr, o) → MirNoUBTree (mirTree body s) := by
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
        simp only [ITreeF.map] at hobs
        exact treeSafe_of_tau hobs (ih s' tr o h)
      | halted _ => simp at h
      | faulted _ => simp at h
    | ret o' =>
      simp only [ITreeF.map] at hobs
      exact treeSafe_of_ret hobs
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
                simp only [ITreeF.map] at hobs
                apply treeSafe_of_emit hobs
                show TreeSafe (ITree.cofix (stepMirState body) (k PUnit.unit))
                rw [hk]
                exact ih s' p.1 p.2 hrun

/-- One-step invariant condition for a diverging loop: each step from a state
satisfying `Inv` either takes a silent `.tau` transition to a state satisfying
`Inv` or emits a branch observation `.emit ev` whose continuation is a state
satisfying `Inv`. -/
def SafeContinue (body : CapturedMir) (Inv : MachineState → Prop) (s : MachineState) : Prop :=
  (∃ s', stepMirFn body s = .tau (.running s') ∧ Inv s') ∨
  (∃ ev k s', stepMirFn body s = .vis (.inr (.inl (.emit ev))) k ∧
    k PUnit.unit = .running s' ∧ Inv s')

theorem tauStar_of_step_inv {body : CapturedMir} {Inv : MachineState → Prop}
    (hstep : ∀ s, Inv s → SafeContinue body Inv s)
    {t u : ITree MirEffect MirOutcome} (htau : TauStar t u) :
    ∀ s, t = mirTree body s → Inv s → ∃ s', u = mirTree body s' ∧ Inv s' := by
  induction htau with
  | refl t =>
    intro s ht hinv
    exact ⟨s, ht, hinv⟩
  | step hobs _ ih =>
    intro s ht hinv
    subst ht
    rcases hstep s hinv with ⟨s1, hs1, hinv1⟩ | ⟨ev, k, s1, hs1, _, _⟩
    · have hobs' := mirTree_observe body s
      rw [hs1, ITreeF.map] at hobs'
      rw [hobs'] at hobs
      injection hobs with hnext
      exact ih s1 hnext.symm hinv1
    · have hobs' := mirTree_observe body s
      rw [hs1] at hobs'
      simp only [ITreeF.map] at hobs'
      rw [hobs'] at hobs
      cases hobs

theorem reaches_of_step_inv {body : CapturedMir} {Inv : MachineState → Prop}
    (hstep : ∀ s, Inv s → SafeContinue body Inv s)
    {t u : ITree MirEffect MirOutcome} {tr : List (Event MirEffect)} (hr : Reaches t tr u) :
    ∀ s, t = mirTree body s → Inv s → ∃ s', u = mirTree body s' ∧ Inv s' := by
  induction hr with
  | refl t =>
    intro s ht hinv
    exact ⟨s, ht, hinv⟩
  | tau hobs _ ih =>
    intro s ht hinv
    subst ht
    rcases hstep s hinv with ⟨s1, hs1, hinv1⟩ | ⟨ev, k, s1, hs1, _, _⟩
    · have hobs' := mirTree_observe body s
      rw [hs1, ITreeF.map] at hobs'
      rw [hobs'] at hobs
      injection hobs with hnext
      exact ih s1 hnext.symm hinv1
    · have hobs' := mirTree_observe body s
      rw [hs1] at hobs'
      simp only [ITreeF.map] at hobs'
      rw [hobs'] at hobs
      cases hobs
  | vis hobs _ o _ ih =>
    intro s ht hinv
    subst ht
    rcases hstep s hinv with ⟨s1, hs1, _⟩ | ⟨ev, k, s1, hs1, hk1, hinv1⟩
    · have hobs' := mirTree_observe body s
      rw [hs1, ITreeF.map] at hobs'
      rw [hobs'] at hobs
      cases hobs
    · have hobs' := mirTree_observe body s
      rw [hs1] at hobs'
      simp only [ITreeF.map] at hobs'
      rw [hobs'] at hobs
      injection hobs with hi hk
      subst hi
      have hk' := eq_of_heq hk
      subst hk'
      cases o
      have ht' : ITree.cofix (stepMirState body) (k PUnit.unit) = mirTree body s1 := by
        rw [hk1]; rfl
      exact ih s1 ht' hinv1

/-- Invariant-based all-prefix UB-freedom (`MirNoUBTree`) for diverging loops
that may take silent `.tau` steps and emit branch observations (`.emit`). -/
theorem treeSafe_of_step_inv {body : CapturedMir} {Inv : MachineState → Prop}
    (hstep : ∀ s, Inv s → SafeContinue body Inv s)
    {s : MachineState} (hinv : Inv s) : MirNoUBTree (mirTree body s) := by
  intro tr u hr ⟨w, i, k, htau, hw, hflt⟩
  obtain ⟨s1, rfl, hinv1⟩ := reaches_of_step_inv hstep hr s rfl hinv
  obtain ⟨s2, rfl, hinv2⟩ := tauStar_of_step_inv hstep htau s1 rfl hinv1
  rcases hstep s2 hinv2 with ⟨s3, hs3, _⟩ | ⟨ev, k0, s3, hs3, _, _⟩
  · have hobs := mirTree_observe body s2
    rw [hs3, ITreeF.map] at hobs
    rw [hobs] at hw
    cases hw
  · have hobs := mirTree_observe body s2
    rw [hs3] at hobs
    simp only [ITreeF.map] at hobs
    rw [hobs] at hw
    injection hw with hi _
    subst hi
    exact hflt

/-- Invariant-based non-termination (`¬ ReachesRet`) for diverging loops that
may take silent `.tau` steps and emit branch observations (`.emit`). -/
theorem noRet_of_step_inv {body : CapturedMir} {Inv : MachineState → Prop}
    (hstep : ∀ s, Inv s → SafeContinue body Inv s)
    {s : MachineState} (hinv : Inv s) (tr : List (Event MirEffect)) (o : MirOutcome) :
    ¬ ReachesRet (mirTree body s) tr o := by
  rintro ⟨u, hr, hu⟩
  obtain ⟨s1, rfl, hinv1⟩ := reaches_of_step_inv hstep hr s rfl hinv
  rcases hstep s1 hinv1 with ⟨s2, hs2, _⟩ | ⟨ev, k0, s2, hs2, _, _⟩
  · have hobs := mirTree_observe body s1
    rw [hs2, ITreeF.map] at hobs
    rw [hobs] at hu
    cases hu
  · have hobs := mirTree_observe body s1
    rw [hs2] at hobs
    simp only [ITreeF.map] at hobs
    rw [hobs] at hu
    cases hu

/-- Invariant-based all-prefix UB-freedom (`MirNoUBTree`) for diverging
silent-step loops. -/
theorem treeSafe_of_tau_inv {body : CapturedMir} {Inv : MachineState → Prop}
    (hstep : ∀ s, Inv s → ∃ s', stepMirFn body s = .tau (.running s') ∧ Inv s')
    {s : MachineState} (hinv : Inv s) : MirNoUBTree (mirTree body s) :=
  treeSafe_of_step_inv (fun s hs => Or.inl (hstep s hs)) hinv

/-- Invariant-based non-termination (`¬ ReachesRet`) for diverging silent-step
loops. -/
theorem noRet_of_tau_inv {body : CapturedMir} {Inv : MachineState → Prop}
    (hstep : ∀ s, Inv s → ∃ s', stepMirFn body s = .tau (.running s') ∧ Inv s')
    {s : MachineState} (hinv : Inv s) (tr : List (Event MirEffect)) (o : MirOutcome) :
    ¬ ReachesRet (mirTree body s) tr o :=
  noRet_of_step_inv (fun s hs => Or.inl (hstep s hs)) hinv tr o

/-! ## Multi-function & multi-frame whole executions (`MR-4.1`)

`multi_step_correspondence` lifted to whole multi-function executions over
`mirTree entry s` and `mirCallTreeWithCallees entry args callees`. Because one
Anneal `.tau` call transition corresponds to `1 + initLen callee ≥ 1` MiniRust
steps (`Terminator::Call` followed by the callee's `initBlock`), `multi_steps_error`
and `multi_steps_outcome` induct via `Nat.strongRecOn` and discharge
within-step prefixes with `steps_ok_mono`. -/

/-- Fundamental coinductive interaction tree of `entry` invoked with `args` and
inline-resolvable callee bodies `callees`. -/
def mirCallTreeWithCallees (entry : CapturedMir) (args : List Value)
    (callees : List CapturedMir) : ITree MirEffect MirOutcome :=
  mirTree entry (initMachineStateWithCallees entry args callees)

/-- Canonical zero-sized `AllocationKind::Function` allocations (`Size::ZERO`,
`Align::ONE`, matching `Machine::new` in `spec/lang/machine.md`) at addresses
`16 + k`. -/
def fnAllocs (n : Nat) : List Gen.Allocation :=
  (List.range n).map fun (k : Nat) =>
    { data := [], addr := (16 : Int) + (k : Int), align := ⟨1⟩, kind := .Function,
      live := true, extra := () }

/-- Pointer to canonical function allocation `baseOff + k` at address `16 + k`. -/
def fnPtrAt (baseOff k : Nat) : Ptr :=
  { addr := (16 : Int) + (k : Int), provenance := some (⟨((baseOff + k : Nat) : Int)⟩, ()) }

/-- Canonical `fn_ptrs` table mapping `fnName k` (`0 ≤ k < n`) to
`fnPtrAt baseOff k`. -/
def fnPtrMap (baseOff n : Nat) : LibSpecr.Map Gen.FnName Ptr :=
  ⟨(List.range n).map fun k => (fnName k, fnPtrAt baseOff k)⟩

private theorem lookupFnName_zipIdx_lt (bs : List CapturedMir) (start : Nat) (dp : String)
    (fn : Gen.FnName)
    (h : lookupFnName
      (bs.zipIdx start |>.map fun (b, idx) =>
        (b.defPath, (fnName idx, (translateCallConv b.fnAbi.conv).getD .Rust))) dp =
      some fn) :
    ∃ j < bs.length, fn = fnName (start + j) := by
  induction bs generalizing start with
  | nil => simp [lookupFnName] at h
  | cons b bs ih =>
    simp only [List.zipIdx_cons, List.map_cons, lookupFnName] at h
    cases hbeq : b.defPath == dp with
    | true =>
      rw [hbeq] at h; simp at h
      exact ⟨0, by simp, by simpa using h.symm⟩
    | false =>
      rw [hbeq] at h; simp at h
      obtain ⟨j, hj, rfl⟩ := ih (start + 1) h
      exact ⟨j + 1, by simp [hj], by congr 1; omega⟩

private theorem fnPtrMap_range'_spec (baseOff s m k : Nat) (hsk : s ≤ k) (hkm : k < s + m) :
    let entries := (List.range' s m).map (fun i => (fnName i, fnPtrAt baseOff i))
    mapGet ⟨entries⟩ (fnName k) = some (fnPtrAt baseOff k) ∧
      entries.find? (fun (_, (fp : Ptr)) => decide (fp = fnPtrAt baseOff k)) =
        some (fnName k, fnPtrAt baseOff k) := by
  induction m generalizing s with
  | zero => omega
  | succ m ih =>
    simp only [List.range'_succ, List.map_cons]
    by_cases hks : k = s
    · subst hks
      exact ⟨by simp [mapGet_cons], by simp⟩
    · have hneFn : fnName s ≠ fnName k := by
        intro heq
        rw [fnName_inj] at heq
        omega
      have hnePtr : decide (fnPtrAt baseOff s = fnPtrAt baseOff k) = false := by
        rw [decide_eq_false_iff_not]
        intro heq
        have haddr : (fnPtrAt baseOff s).addr = (fnPtrAt baseOff k).addr :=
          congrArg Gen.ThinPointer.addr heq
        simp [fnPtrAt] at haddr
        omega
      obtain ⟨hget, hfind⟩ := ih (s + 1) (by omega) (by omega)
      refine ⟨?_, ?_⟩
      · rw [mapGet_cons]
        simp [hneFn, hget]
      · simp only [List.find?_cons, hnePtr]
        exact hfind

/-- Any machine whose `prog` is `prog` and whose `fn_ptrs` is `fnPtrMap baseOff n`
with `callees.length + 1 ≤ n` satisfies `ProgEnvOk prog (fnNameMap entry callees)`. -/
theorem progEnvOk_fnPtrMap {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {baseOff n : Nat} {m : Mach}
    (hprog : m.prog = prog) (hfp : m.fn_ptrs = fnPtrMap baseOff n)
    (hn : callees.length + 1 ≤ n) :
    ProgEnvOk prog (fnNameMap entry callees) m := by
  refine ⟨hprog, fun dp fn hlk => ?_⟩
  obtain ⟨k, hklt, rfl⟩ := lookupFnName_zipIdx_lt (entry :: callees) 0 dp fn hlk
  simp only [Nat.zero_add, List.length_cons] at hklt ⊢
  have hspec := fnPtrMap_range'_spec baseOff 0 n k (Nat.zero_le _) (by omega)
  rw [← List.range_eq_range'] at hspec
  refine ⟨fnPtrAt baseOff k, ?_, ?_⟩
  · rw [hfp]; exact hspec.1
  · rw [hfp]; exact hspec.2

/-- Every Anneal execution prefix from `MultiStateRel`-related states is matched
by finitely many MiniRust steps to a `MultiStateRel`-related state. -/
theorem multi_reaches_rel {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog) (rootCtx : Ctx)
    {t u : ITree MirEffect MirOutcome} {tr : List (Event MirEffect)} (h : Reaches t tr u) :
    ∀ (s : MachineState) (m : Mach), t = mirTree entry s →
      MultiStateRel entry callees prog rootCtx s m →
      ∃ (n : Nat) (s' : MachineState) (m' : Mach), Interp.steps n m = .ok m' ∧
        MultiStateRel entry callees prog rootCtx s' m' ∧ u = mirTree entry s' := by
  induction h with
  | refl t =>
    intro s m ht hrel
    exact ⟨0, s, m, rfl, hrel, ht⟩
  | tau hobs _ ih =>
    intro s m ht hrel
    subst ht
    have hsr := multi_step_correspondence entry callees prog hfrag hprog rootCtx s m hrel
    rw [mirTree_observe] at hobs
    generalize stepMirFn entry s = node at hsr hobs
    cases node with
    | ret r => simp [ITreeF.map] at hobs
    | vis i k => simp [ITreeF.map] at hobs
    | tau x =>
      simp only [ITreeF.map, ITreeF.tau.injEq] at hobs
      cases x with
      | running s1 =>
        obtain ⟨k, m1, _, hm1, hrel1⟩ := hsr
        obtain ⟨n, s', m', hsteps, hrel', hu⟩ := ih s1 m1 hobs.symm hrel1
        exact ⟨k + n, s', m', by rw [steps_add, hm1, ok_bind, hsteps], hrel', hu⟩
      | halted _ => exact False.elim hsr
      | faulted _ => exact False.elim hsr
  | vis hobs hnf o _ ih =>
    intro s m ht hrel
    subst ht
    have hsr := multi_step_correspondence entry callees prog hfrag hprog rootCtx s m hrel
    rw [mirTree_observe] at hobs
    generalize stepMirFn entry s = node at hsr hobs
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
          have ht' : ITree.cofix (stepMirState entry) (k0 PUnit.unit) = mirTree entry s1 := by
            rw [hk1]; rfl
          obtain ⟨n, s', m', hsteps, hrel', hu⟩ := ih s1 m1 ht' hrel1
          exact ⟨n + 1, s', m', by simp [Interp.steps, hm1, hsteps], hrel', hu⟩

/-- **Multi-function returns.** If Anneal's multi-frame semantics of `entry`
(with `callees`) returns `v` along any trace of branch observations, MiniRust
performs the corresponding root function return (`ReturnRel`) after finitely
many steps. -/
theorem multi_run_ret {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog) (rootCtx : Ctx)
    (s : MachineState) (m : Mach)
    (hrel : MultiStateRel entry callees prog rootCtx s m)
    {tr : List (Event MirEffect)} {v : Value} {mem : MirSemantics.Memory}
    (hret : ReachesRet (mirTree entry s) tr (.normal (v, mem))) :
    ∃ (n : Nat) (s' : MachineState) (m' : Mach),
      Interp.steps n m = .ok m' ∧ ReturnRel entry rootCtx s' v m' := by
  obtain ⟨u, hreach, hu⟩ := hret
  obtain ⟨n, s', m', hsteps, hrel', rfl⟩ :=
    multi_reaches_rel hfrag hprog rootCtx hreach s m rfl hrel
  have hsr := multi_step_correspondence entry callees prog hfrag hprog rootCtx s' m' hrel'
  rw [mirTree_observe] at hu
  generalize stepMirFn entry s' = node at hsr hu
  cases node with
  | tau x => simp [ITreeF.map] at hu
  | vis i k => simp [ITreeF.map] at hu
  | ret r =>
    simp only [ITreeF.map, ITreeF.ret.injEq] at hu
    subst hu
    obtain ⟨m'', hm'', hret'⟩ := hsr
    exact ⟨n + 1, s', m'', by rw [steps_add, hsteps]; simp [Interp.steps, hm''], hret'⟩

/-- **Multi-function returns from `fEntry.start`.** Starting MiniRust at
`fEntry.start` under `MultiStartRel` steps through `entry`'s `initBlock` into
`bb0`, executes all transitive `Call` and `Return` transitions across `callees`,
and matches Anneal's root return via `ReturnRel`. -/
theorem multi_run_ret_from_start {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function}
    (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog)
    (rootCtx : Ctx) (s : MachineState) (mInit : Mach)
    (hstart : MultiStartRel entry callees prog fEntry rootCtx s mInit)
    {tr : List (Event MirEffect)} {v : Value} {mem : MirSemantics.Memory}
    (hret : ReachesRet (mirTree entry s) tr (.normal (v, mem))) :
    ∃ (n : Nat) (s' : MachineState) (m' : Mach),
      Interp.steps n mInit = .ok m' ∧ ReturnRel entry rootCtx s' v m' := by
  obtain ⟨m0, hm0, hrel0⟩ := multi_step_start hfrag hstart
  obtain ⟨n, s', m', hsteps, hret'⟩ := multi_run_ret hfrag hprog rootCtx s m0 hrel0 hret
  exact ⟨initLen entry + n, s', m', by rw [steps_add, hm0, ok_bind, hsteps], hret'⟩

/-- **Multi-function UB.** If Anneal's multi-frame semantics of `entry` (with
`callees`) can reach UB (in `entry`, in call-argument evaluation, or inside any
callee), MiniRust raises UB after finitely many steps. -/
theorem multi_run_ub {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog) (rootCtx : Ctx)
    (s : MachineState) (m : Mach)
    (hrel : MultiStateRel entry callees prog rootCtx s m)
    {tr : List (Event MirEffect)} {u : ITree MirEffect MirOutcome}
    (hreach : Reaches (mirTree entry s) tr u) (hfault : FaultNow u) :
    ∃ (n : Nat) (msg : String), Interp.steps n m = .error (.ub msg) := by
  obtain ⟨t', i, k, htau, hobs, hfi⟩ := hfault
  obtain ⟨n1, s1, m1, h1, hrel1, rfl⟩ :=
    multi_reaches_rel hfrag hprog rootCtx hreach s m rfl hrel
  obtain ⟨n2, s2, m2, h2, hrel2, rfl⟩ :=
    multi_reaches_rel hfrag hprog rootCtx (tauStar_reaches htau) s1 m1 rfl hrel1
  have hsr := multi_step_correspondence entry callees prog hfrag hprog rootCtx s2 m2 hrel2
  rw [mirTree_observe] at hobs
  generalize stepMirFn entry s2 = node at hsr hobs
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

/-- **Multi-function UB from `fEntry.start`.** Starting MiniRust at
`fEntry.start` under `MultiStartRel` raises UB after finitely many steps
whenever Anneal's multi-frame semantics can reach UB. -/
theorem multi_run_ub_from_start {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function}
    (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog)
    (rootCtx : Ctx) (s : MachineState) (mInit : Mach)
    (hstart : MultiStartRel entry callees prog fEntry rootCtx s mInit)
    {tr : List (Event MirEffect)} {u : ITree MirEffect MirOutcome}
    (hreach : Reaches (mirTree entry s) tr u) (hfault : FaultNow u) :
    ∃ (n : Nat) (msg : String), Interp.steps n mInit = .error (.ub msg) := by
  obtain ⟨m0, hm0, hrel0⟩ := multi_step_start hfrag hstart
  obtain ⟨n, msg, hsteps⟩ := multi_run_ub hfrag hprog rootCtx s m0 hrel0 hreach hfault
  exact ⟨initLen entry + n, msg, by rw [steps_add, hm0, ok_bind, hsteps]⟩

/-- **Multi-function converse error soundness.** If MiniRust stops with *any*
error `e` within `n` steps of a `MultiStateRel`-related machine, then either
`e` is UB and Anneal's multi-frame tree reaches UB (`FaultNow`), or MiniRust
already completed the root `entry` return (`ReturnRel`, matching an Anneal
`ReachesRet`) in `k < n` steps and only errored later inside the unmodeled
external caller frame. In particular, no intermediate step inside a multi-step
`Call + initBlock` transition can panic, deadlock, or fault silently. -/
theorem multi_steps_error {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog) (rootCtx : Ctx) (n : Nat) :
    ∀ (s : MachineState) (m : Mach) (e : Stop),
      MultiStateRel entry callees prog rootCtx s m →
      Interp.steps n m = .error e →
      (∃ msg, e = .ub msg ∧ ∃ tr u, Reaches (mirTree entry s) tr u ∧ FaultNow u) ∨
      (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k m = .ok mRet ∧
        ReturnRel entry rootCtx s' v mRet ∧
        ReachesRet (mirTree entry s) tr (.normal (v, mem))) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => intro s m e _ h; simp [Interp.steps] at h
    | succ n0 =>
      intro s m e hrel h
      have hsr := multi_step_correspondence entry callees prog hfrag hprog rootCtx s m hrel
      have hobs := mirTree_observe entry s
      generalize stepMirFn entry s = node at hsr hobs
      cases node with
      | tau x =>
        simp only [ITreeF.map] at hobs
        cases x with
        | running s1 =>
          obtain ⟨kStep, m1, hkpos, hm1, hrel1⟩ := hsr
          by_cases hnk : n0 + 1 ≤ kStep
          · obtain ⟨mj, hmj⟩ := steps_ok_mono hnk hm1
            rw [hmj] at h
            cases h
          · have hsplit : n0 + 1 = kStep + (n0 + 1 - kStep) := by omega
            rw [hsplit, steps_add, hm1, ok_bind] at h
            rcases ih (n0 + 1 - kStep) (by omega) s1 m1 e hrel1 h with
              ⟨msg, he, tr, u, hr, hfault⟩ |
              ⟨k, s', mRet, tr, v, mem, hklt, hksteps, hretRel, u, hr, hu⟩
            · exact .inl ⟨msg, he, tr, u, .tau hobs hr, hfault⟩
            · exact .inr ⟨kStep + k, s', mRet, tr, v, mem, by omega,
                by rw [steps_add, hm1, ok_bind, hksteps], hretRel, u, .tau hobs hr, hu⟩
        | halted _ => exact False.elim hsr
        | faulted _ => exact False.elim hsr
      | ret r =>
        simp only [ITreeF.map] at hobs
        cases r with
        | normal p =>
          obtain ⟨mRet, hmRet, hretRel⟩ := hsr
          cases n0 with
          | zero => simp [Interp.steps, hmRet] at h
          | succ n' =>
            exact .inr ⟨1, s, mRet, [], p.1, p.2, by omega,
              by simp [Interp.steps, hmRet], hretRel, mirTree entry s, .refl _, hobs⟩
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
              exact .inl ⟨msg, h.symm, [], mirTree entry s, .refl _,
                ⟨mirTree entry s, _, _, .refl _, hobs, trivial⟩⟩
        | inr b =>
          cases b with
          | inr _ => exact False.elim hsr
          | inl ob =>
            obtain ⟨s1, m1, hk1, hm1, hrel1⟩ := hsr
            simp only [Interp.steps, hm1, ok_bind] at h
            have hnext : ITree.cofix (stepMirState entry) (k0 PUnit.unit) = mirTree entry s1 := by
              rw [hk1]; rfl
            rcases ih n0 (by omega) s1 m1 e hrel1 h with
              ⟨msg, he, tr, u, hr, hfault⟩ |
              ⟨k, s', mRet, tr, v, mem, hklt, hksteps, hretRel, u, hr, hu⟩
            · refine .inl ⟨msg, he, ⟨.inr (.inl ob), PUnit.unit⟩ :: tr, u,
                .vis hobs (fun h => h) PUnit.unit ?_, hfault⟩
              rw [hnext]; exact hr
            · refine .inr ⟨k + 1, s', mRet, ⟨.inr (.inl ob), PUnit.unit⟩ :: tr, v, mem, by omega,
                by simp [Interp.steps, hm1, hksteps], hretRel, u,
                .vis hobs (fun h => h) PUnit.unit ?_, hu⟩
              rw [hnext]; exact hr

/-- **Multi-function converse error soundness from `fEntry.start`.** -/
theorem multi_steps_error_from_start {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function}
    (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog)
    (rootCtx : Ctx) (n : Nat) (s : MachineState) (mInit : Mach) (e : Stop)
    (hstart : MultiStartRel entry callees prog fEntry rootCtx s mInit)
    (h : Interp.steps n mInit = .error e) :
    (∃ msg, e = .ub msg ∧ ∃ tr u, Reaches (mirTree entry s) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel entry rootCtx s' v mRet ∧
      ReachesRet (mirTree entry s) tr (.normal (v, mem))) := by
  obtain ⟨m0, hm0, hrel0⟩ := multi_step_start hfrag hstart
  by_cases hn : n ≤ initLen entry
  · obtain ⟨mj, hmj⟩ := steps_ok_mono hn hm0
    rw [hmj] at h
    cases h
  · obtain ⟨n', rfl⟩ : ∃ n', n = initLen entry + n' := ⟨n - initLen entry, by omega⟩
    rw [steps_add, hm0, ok_bind] at h
    rcases multi_steps_error hfrag hprog rootCtx n' s m0 e hrel0 h with
      hUb | ⟨k, s', mRet, tr, v, mem, hklt, hksteps, hretRel, hret⟩
    · exact .inl hUb
    · exact .inr ⟨initLen entry + k, s', mRet, tr, v, mem, by omega,
        by rw [steps_add, hm0, ok_bind, hksteps], hretRel, hret⟩

/-- **Multi-function UB-freedom transfer.** If `MirNoUBTree (mirTree entry s)`
holds, MiniRust never stops with any error across the entire multi-frame call
execution prior to completing `entry`'s root `ReturnRel`. -/
theorem multi_mirNoUB_safe {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog) (rootCtx : Ctx)
    (s : MachineState) (m : Mach)
    (hrel : MultiStateRel entry callees prog rootCtx s m)
    (hsafe : MirNoUBTree (mirTree entry s))
    {n : Nat} {e : Stop} (herr : Interp.steps n m = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k m = .ok mRet ∧
      ReturnRel entry rootCtx s' v mRet ∧
      ReachesRet (mirTree entry s) tr (.normal (v, mem)) := by
  rcases multi_steps_error hfrag hprog rootCtx n s m e hrel herr with
    ⟨_, _, tr, u, hr, hfault⟩ | hret
  · exact False.elim (hsafe tr u hr hfault)
  · exact hret

/-- **Multi-function UB-freedom transfer from `fEntry.start`.** -/
theorem multi_mirNoUB_safe_from_start {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function}
    (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog)
    (rootCtx : Ctx) (s : MachineState) (mInit : Mach)
    (hstart : MultiStartRel entry callees prog fEntry rootCtx s mInit)
    (hsafe : MirNoUBTree (mirTree entry s))
    {n : Nat} {e : Stop} (herr : Interp.steps n mInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel entry rootCtx s' v mRet ∧
      ReachesRet (mirTree entry s) tr (.normal (v, mem)) := by
  rcases multi_steps_error_from_start hfrag hprog rootCtx n s mInit e hstart herr with
    ⟨_, _, tr, u, hr, hfault⟩ | hret
  · exact False.elim (hsafe tr u hr hfault)
  · exact hret

/-- **Multi-function total `n`-step outcome trichotomy.** For every step budget
`n : Nat` from `MultiStateRel`-related states:
1. MiniRust succeeds for `n` steps (`Interp.steps n m = .ok m0`) and within
   `d` completion steps of any active callee `initBlock` (`d = 0` outside a
   callee `initBlock`) reaches `m'` in `MultiStateRel` with an Anneal state `s'`
   reachable via `Reaches (mirTree entry s) tr (mirTree entry s')`;
2. MiniRust already completed `entry`'s root return (`ReturnRel`, matching an
   Anneal `ReachesRet`) in `k ≤ n` steps; or
3. MiniRust stopped with `.error (.ub msg)` within `n` steps and Anneal's
   interaction tree reaches a fault (`FaultNow`). -/
theorem multi_steps_outcome {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog) (rootCtx : Ctx) (n : Nat) :
    ∀ (s : MachineState) (m : Mach), MultiStateRel entry callees prog rootCtx s m →
      (∃ d s' m0 m' tr, Interp.steps n m = .ok m0 ∧
        Interp.steps (n + d) m = .ok m' ∧
        MultiStateRel entry callees prog rootCtx s' m' ∧
        Reaches (mirTree entry s) tr (mirTree entry s')) ∨
      (∃ k s' mRet tr v mem, k ≤ n ∧ Interp.steps k m = .ok mRet ∧
        ReturnRel entry rootCtx s' v mRet ∧
        ReachesRet (mirTree entry s) tr (.normal (v, mem))) ∨
      (∃ msg, Interp.steps n m = .error (.ub msg) ∧
        ∃ tr u, Reaches (mirTree entry s) tr u ∧ FaultNow u) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      intro s m hrel
      exact .inl ⟨0, s, m, m, [], rfl, rfl, hrel, .refl _⟩
    | succ n0 =>
      intro s m hrel
      have hsr := multi_step_correspondence entry callees prog hfrag hprog rootCtx s m hrel
      have hobs := mirTree_observe entry s
      generalize stepMirFn entry s = node at hsr hobs
      cases node with
      | tau x =>
        simp only [ITreeF.map] at hobs
        cases x with
        | running s1 =>
          obtain ⟨kStep, m1, hkpos, hm1, hrel1⟩ := hsr
          by_cases hlt : n0 + 1 < kStep
          · obtain ⟨m0, hm0⟩ := steps_ok_mono (Nat.le_of_lt hlt) hm1
            refine .inl ⟨kStep - (n0 + 1), s1, m0, m1, [], hm0, ?_, hrel1, .tau hobs (.refl _)⟩
            rwa [show n0 + 1 + (kStep - (n0 + 1)) = kStep by omega]
          · have hsplit : n0 + 1 = kStep + (n0 + 1 - kStep) := by omega
            rcases ih (n0 + 1 - kStep) (by omega) s1 m1 hrel1 with
              ⟨d, s', m0, m', tr, hrem0, hremD, hrel', hr⟩ |
              ⟨k, s', mRet, tr, v, mem, hkle, hksteps, hretRel, u, hr, hu⟩ |
              ⟨msg, herr, tr, u, hr, hfault⟩
            · refine .inl ⟨d, s', m0, m', tr, ?_, ?_, hrel', .tau hobs hr⟩
              · rw [hsplit, steps_add, hm1, ok_bind, hrem0]
              · rw [show n0 + 1 + d = kStep + (n0 + 1 - kStep + d) by omega,
                  steps_add, hm1, ok_bind, hremD]
            · exact .inr (.inl ⟨kStep + k, s', mRet, tr, v, mem, by omega,
                by rw [steps_add, hm1, ok_bind, hksteps], hretRel, u, .tau hobs hr, hu⟩)
            · exact .inr (.inr ⟨msg, by rw [hsplit, steps_add, hm1, ok_bind, herr],
                tr, u, .tau hobs hr, hfault⟩)
        | halted _ => exact False.elim hsr
        | faulted _ => exact False.elim hsr
      | ret r =>
        simp only [ITreeF.map] at hobs
        cases r with
        | normal p =>
          obtain ⟨mRet, hmRet, hretRel⟩ := hsr
          exact .inr (.inl ⟨1, s, mRet, [], p.1, p.2, by omega,
            by simp [Interp.steps, hmRet], hretRel, mirTree entry s, .refl _, hobs⟩)
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
              exact .inr (.inr ⟨msg, by simp [Interp.steps, hmsg], [], mirTree entry s, .refl _,
                ⟨mirTree entry s, _, _, .refl _, hobs, trivial⟩⟩)
        | inr b =>
          cases b with
          | inr _ => exact False.elim hsr
          | inl ob =>
            obtain ⟨s1, m1, hk1, hm1, hrel1⟩ := hsr
            have hnext : ITree.cofix (stepMirState entry) (k0 PUnit.unit) = mirTree entry s1 := by
              rw [hk1]; rfl
            rcases ih n0 (by omega) s1 m1 hrel1 with
              ⟨d, s', m0, m', tr, hsteps0, hstepsD, hrel', hr⟩ |
              ⟨k, s', mRet, tr, v, mem, hkle, hksteps, hretRel, u, hr, hu⟩ |
              ⟨msg, herr, tr, u, hr, hfault⟩
            · refine .inl ⟨d, s', m0, m', ⟨.inr (.inl ob), PUnit.unit⟩ :: tr,
                by simp [Interp.steps, hm1, hsteps0],
                by rw [show n0 + 1 + d = (n0 + d) + 1 by omega]; simp [Interp.steps, hm1, hstepsD],
                hrel', .vis hobs (fun h => h) PUnit.unit ?_⟩
              rw [hnext]; exact hr
            · refine .inr (.inl ⟨k + 1, s', mRet, ⟨.inr (.inl ob), PUnit.unit⟩ :: tr,
                v, mem, by omega, by simp [Interp.steps, hm1, hksteps], hretRel, u,
                .vis hobs (fun h => h) PUnit.unit ?_, hu⟩)
              rw [hnext]; exact hr
            · refine .inr (.inr ⟨msg, by simp [Interp.steps, hm1, herr],
                ⟨.inr (.inl ob), PUnit.unit⟩ :: tr, u,
                .vis hobs (fun h => h) PUnit.unit ?_, hfault⟩)
              rw [hnext]; exact hr

/-- **Multi-function total `(initLen entry + n)`-step outcome trichotomy from
`fEntry.start`.** -/
theorem multi_steps_outcome_from_start {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function}
    (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog)
    (rootCtx : Ctx) (n : Nat) (s : MachineState) (mInit : Mach)
    (hstart : MultiStartRel entry callees prog fEntry rootCtx s mInit) :
    (∃ d s' m0 m' tr, Interp.steps (initLen entry + n) mInit = .ok m0 ∧
      Interp.steps (initLen entry + n + d) mInit = .ok m' ∧
      MultiStateRel entry callees prog rootCtx s' m' ∧
      Reaches (mirTree entry s) tr (mirTree entry s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen entry + n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel entry rootCtx s' v mRet ∧
      ReachesRet (mirTree entry s) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (initLen entry + n) mInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirTree entry s) tr u ∧ FaultNow u) := by
  obtain ⟨mStart, hmStart, hrel0⟩ := multi_step_start hfrag hstart
  rcases multi_steps_outcome hfrag hprog rootCtx n s mStart hrel0 with
    ⟨d, s', m0, m', tr, hsteps0, hstepsD, hrel', hr⟩ |
    ⟨k, s', mRet, tr, v, mem, hkle, hksteps, hretRel, hret⟩ |
    ⟨msg, herr, hfault⟩
  · exact .inl ⟨d, s', m0, m', tr,
      by rw [steps_add, hmStart, ok_bind, hsteps0],
      by rw [Nat.add_assoc, steps_add, hmStart, ok_bind, hstepsD], hrel', hr⟩
  · exact .inr (.inl ⟨initLen entry + k, s', mRet, tr, v, mem, by omega,
      by rw [steps_add, hmStart, ok_bind, hksteps], hretRel, hret⟩)
  · exact .inr (.inr ⟨msg, by rw [steps_add, hmStart, ok_bind, herr], hfault⟩)

/-- **Multi-function total arbitrary-`n` outcome trichotomy from `fEntry.start`
(including startup steps `n ≤ initLen entry` inside `fEntry.start`).** -/
theorem multi_steps_outcome_any_from_start {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function}
    (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog)
    (rootCtx : Ctx) (n : Nat) (s : MachineState) (mInit : Mach)
    (hstart : MultiStartRel entry callees prog fEntry rootCtx s mInit) :
    (∃ d s' m0 m' tr, Interp.steps n mInit = .ok m0 ∧
      Interp.steps (n + d) mInit = .ok m' ∧
      MultiStateRel entry callees prog rootCtx s' m' ∧
      Reaches (mirTree entry s) tr (mirTree entry s')) ∨
    (∃ k s' mRet tr v mem, k ≤ n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel entry rootCtx s' v mRet ∧
      ReachesRet (mirTree entry s) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps n mInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirTree entry s) tr u ∧ FaultNow u) := by
  obtain ⟨mStart, hmStart, hrel0⟩ := multi_step_start hfrag hstart
  by_cases hn : n ≤ initLen entry
  · obtain ⟨m0, hsteps0⟩ := steps_ok_mono hn hmStart
    refine .inl ⟨initLen entry - n, s, m0, mStart, [], hsteps0, ?_, hrel0, .refl _⟩
    rwa [show n + (initLen entry - n) = initLen entry by omega]
  · obtain ⟨n', rfl⟩ : ∃ n', n = initLen entry + n' := ⟨n - initLen entry, by omega⟩
    exact multi_steps_outcome_from_start hfrag hprog rootCtx n' s mInit hstart

/-- **Multi-function forward progress under `MirNoUBTree`.** -/
theorem multi_mirNoUB_progress {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog)
    (rootCtx : Ctx) (s : MachineState) (m : Mach)
    (hrel : MultiStateRel entry callees prog rootCtx s m)
    (hsafe : MirNoUBTree (mirTree entry s)) (n : Nat) :
    (∃ d s' m0 m' tr, Interp.steps n m = .ok m0 ∧
      Interp.steps (n + d) m = .ok m' ∧
      MultiStateRel entry callees prog rootCtx s' m' ∧
      Reaches (mirTree entry s) tr (mirTree entry s')) ∨
    (∃ k s' mRet tr v mem, k ≤ n ∧ Interp.steps k m = .ok mRet ∧
      ReturnRel entry rootCtx s' v mRet ∧
      ReachesRet (mirTree entry s) tr (.normal (v, mem))) := by
  rcases multi_steps_outcome hfrag hprog rootCtx n s m hrel with
    hrun | hret | ⟨_, _, tr, u, hr, hfault⟩
  · exact .inl hrun
  · exact .inr hret
  · exact False.elim (hsafe tr u hr hfault)

/-- **Multi-function forward progress from `fEntry.start` under `MirNoUBTree`.** -/
theorem multi_mirNoUB_progress_from_start {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function}
    (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog)
    (rootCtx : Ctx) (s : MachineState) (mInit : Mach)
    (hstart : MultiStartRel entry callees prog fEntry rootCtx s mInit)
    (hsafe : MirNoUBTree (mirTree entry s)) (n : Nat) :
    (∃ d s' m0 m' tr, Interp.steps (initLen entry + n) mInit = .ok m0 ∧
      Interp.steps (initLen entry + n + d) mInit = .ok m' ∧
      MultiStateRel entry callees prog rootCtx s' m' ∧
      Reaches (mirTree entry s) tr (mirTree entry s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen entry + n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel entry rootCtx s' v mRet ∧
      ReachesRet (mirTree entry s) tr (.normal (v, mem))) := by
  rcases multi_steps_outcome_from_start hfrag hprog rootCtx n s mInit hstart with
    hrun | hret | ⟨_, _, tr, u, hr, hfault⟩
  · exact .inl hrun
  · exact .inr hret
  · exact False.elim (hsafe tr u hr hfault)

/-- **Multi-function arbitrary-`n` forward progress from `fEntry.start` under
`MirNoUBTree` (including startup steps `n ≤ initLen entry`).** -/
theorem multi_mirNoUB_progress_any_from_start {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function}
    (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog)
    (rootCtx : Ctx) (s : MachineState) (mInit : Mach)
    (hstart : MultiStartRel entry callees prog fEntry rootCtx s mInit)
    (hsafe : MirNoUBTree (mirTree entry s)) (n : Nat) :
    (∃ d s' m0 m' tr, Interp.steps n mInit = .ok m0 ∧
      Interp.steps (n + d) mInit = .ok m' ∧
      MultiStateRel entry callees prog rootCtx s' m' ∧
      Reaches (mirTree entry s) tr (mirTree entry s')) ∨
    (∃ k s' mRet tr v mem, k ≤ n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel entry rootCtx s' v mRet ∧
      ReachesRet (mirTree entry s) tr (.normal (v, mem))) := by
  rcases multi_steps_outcome_any_from_start hfrag hprog rootCtx n s mInit hstart with
    hrun | hret | ⟨_, _, tr, u, hr, hfault⟩
  · exact .inl hrun
  · exact .inr hret
  · exact False.elim (hsafe tr u hr hfault)

/-- **Multi-function diverging UB-free execution from `MultiStateRel`.** -/
theorem multi_mirNoUB_diverges_steps_ok {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog)
    (rootCtx : Ctx) (s : MachineState) (m : Mach)
    (hrel : MultiStateRel entry callees prog rootCtx s m)
    (hsafe : MirNoUBTree (mirTree entry s))
    (hdiv : ∀ tr o, ¬ ReachesRet (mirTree entry s) tr o) (n : Nat) :
    ∃ d s' m0 m' tr, Interp.steps n m = .ok m0 ∧
      Interp.steps (n + d) m = .ok m' ∧
      MultiStateRel entry callees prog rootCtx s' m' ∧
      Reaches (mirTree entry s) tr (mirTree entry s') := by
  rcases multi_mirNoUB_progress hfrag hprog rootCtx s m hrel hsafe n with
    hrun | ⟨_, _, _, tr, v, mem, _, _, _, hret⟩
  · exact hrun
  · exact False.elim (hdiv tr (.normal (v, mem)) hret)

/-- **Multi-function diverging UB-free execution from `fEntry.start`.** -/
theorem multi_mirNoUB_diverges_from_start {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function}
    (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog)
    (rootCtx : Ctx) (s : MachineState) (mInit : Mach)
    (hstart : MultiStartRel entry callees prog fEntry rootCtx s mInit)
    (hsafe : MirNoUBTree (mirTree entry s))
    (hdiv : ∀ tr o, ¬ ReachesRet (mirTree entry s) tr o) (n : Nat) :
    ∃ m', Interp.steps n mInit = .ok m' := by
  obtain ⟨mStart, hmStart, hrel0⟩ := multi_step_start hfrag hstart
  by_cases hn : n ≤ initLen entry
  · exact steps_ok_mono hn hmStart
  · obtain ⟨n', rfl⟩ : ∃ n', n = initLen entry + n' := ⟨n - initLen entry, by omega⟩
    obtain ⟨_, _, m0, _, _, hsteps0, _, _, _⟩ :=
      multi_mirNoUB_diverges_steps_ok hfrag hprog rootCtx s mStart hrel0 hsafe hdiv n'
    exact ⟨m0, by rw [steps_add, hmStart, ok_bind, hsteps0]⟩

/-- **Coupled multi-function diverging UB-free execution from `fEntry.start`.** -/
theorem multi_mirNoUB_diverges_rel_from_start {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function}
    (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog)
    (rootCtx : Ctx) (s : MachineState) (mInit : Mach)
    (hstart : MultiStartRel entry callees prog fEntry rootCtx s mInit)
    (hsafe : MirNoUBTree (mirTree entry s))
    (hdiv : ∀ tr o, ¬ ReachesRet (mirTree entry s) tr o) (n : Nat) :
    ∃ d s' m0 m' tr, Interp.steps (initLen entry + n) mInit = .ok m0 ∧
      Interp.steps (initLen entry + n + d) mInit = .ok m' ∧
      MultiStateRel entry callees prog rootCtx s' m' ∧
      Reaches (mirTree entry s) tr (mirTree entry s') := by
  obtain ⟨mStart, hmStart, hrel0⟩ := multi_step_start hfrag hstart
  obtain ⟨d, s', m0, m', tr, hsteps0, hstepsD, hrel', hr⟩ :=
    multi_mirNoUB_diverges_steps_ok hfrag hprog rootCtx s mStart hrel0 hsafe hdiv n
  exact ⟨d, s', m0, m', tr,
    by rw [steps_add, hmStart, ok_bind, hsteps0],
    by rw [Nat.add_assoc, steps_add, hmStart, ok_bind, hstepsD], hrel', hr⟩

/-! ## Top-level `mirCallTreeWithCallees` entry theorems (`MR-4.1`) -/

/-- **Multi-function call-tree return.** For any multi-function fragment
`(entry, callees)` and well-typed `args`, if
`mirCallTreeWithCallees entry args callees` returns `v`, MiniRust started at
`fEntry.start` executes all callee calls and returns and performs the
corresponding root return (`ReturnRel`) after finitely many steps. -/
theorem mirCallWithCallees_ret {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function}
    (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog)
    (hfEntry : translateFnInProg (fnNameMap entry callees) entry = some fEntry)
    (rootCtx : Ctx) (hctx : CtxOk entry rootCtx)
    (args : List Value) (hargs : argsOk entry args = true)
    (mInit : Mach) (henv : ProgEnvOk prog (fnNameMap entry callees) mInit)
    (hthreads : mInit.threads =
      [thread1 rootCtx [rootCtx.caller,
        { calleeFrame fEntry rootCtx (entry.argCount + 1) 0 0 with next_block := fEntry.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      rootCtx.base ++ localAllocs rootCtx (entry.localDecls.take (entry.argCount + 1))
        (initMachineStateWithCallees entry args callees).frame.locals)
    {tr : List (Event MirEffect)} {v : Value} {mem : MirSemantics.Memory}
    (hret : ReachesRet (mirCallTreeWithCallees entry args callees) tr (.normal (v, mem))) :
    ∃ (n : Nat) (s' : MachineState) (m' : Mach),
      Interp.steps n mInit = .ok m' ∧ ReturnRel entry rootCtx s' v m' :=
  multi_run_ret_from_start hfrag hprog rootCtx
    (initMachineStateWithCallees entry args callees) mInit
    (initMachineStateWithCallees_startRel hfrag hfEntry rootCtx hctx args hargs mInit henv
      hthreads hactive hallocs)
    hret

/-- **Multi-function call-tree UB.** If
`mirCallTreeWithCallees entry args callees` reaches UB, MiniRust started at
`fEntry.start` raises UB after finitely many steps. -/
theorem mirCallWithCallees_ub {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function}
    (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog)
    (hfEntry : translateFnInProg (fnNameMap entry callees) entry = some fEntry)
    (rootCtx : Ctx) (hctx : CtxOk entry rootCtx)
    (args : List Value) (hargs : argsOk entry args = true)
    (mInit : Mach) (henv : ProgEnvOk prog (fnNameMap entry callees) mInit)
    (hthreads : mInit.threads =
      [thread1 rootCtx [rootCtx.caller,
        { calleeFrame fEntry rootCtx (entry.argCount + 1) 0 0 with next_block := fEntry.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      rootCtx.base ++ localAllocs rootCtx (entry.localDecls.take (entry.argCount + 1))
        (initMachineStateWithCallees entry args callees).frame.locals)
    {tr : List (Event MirEffect)} {u : ITree MirEffect MirOutcome}
    (hreach : Reaches (mirCallTreeWithCallees entry args callees) tr u) (hfault : FaultNow u) :
    ∃ (n : Nat) (msg : String), Interp.steps n mInit = .error (.ub msg) :=
  multi_run_ub_from_start hfrag hprog rootCtx
    (initMachineStateWithCallees entry args callees) mInit
    (initMachineStateWithCallees_startRel hfrag hfEntry rootCtx hctx args hargs mInit henv
      hthreads hactive hallocs)
    hreach hfault

/-- **Multi-function call-tree UB-freedom transfer.** If
`MirNoUBTree (mirCallTreeWithCallees entry args callees)` holds, MiniRust
started at `fEntry.start` never stops with any error across the entire
multi-frame execution prior to completing `entry`'s root return. -/
theorem mirCallWithCallees_noUB {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function}
    (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog)
    (hfEntry : translateFnInProg (fnNameMap entry callees) entry = some fEntry)
    (rootCtx : Ctx) (hctx : CtxOk entry rootCtx)
    (args : List Value) (hargs : argsOk entry args = true)
    (mInit : Mach) (henv : ProgEnvOk prog (fnNameMap entry callees) mInit)
    (hthreads : mInit.threads =
      [thread1 rootCtx [rootCtx.caller,
        { calleeFrame fEntry rootCtx (entry.argCount + 1) 0 0 with next_block := fEntry.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      rootCtx.base ++ localAllocs rootCtx (entry.localDecls.take (entry.argCount + 1))
        (initMachineStateWithCallees entry args callees).frame.locals)
    (hsafe : MirNoUBTree (mirCallTreeWithCallees entry args callees))
    {n : Nat} {e : Stop} (herr : Interp.steps n mInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel entry rootCtx s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees entry args callees) tr (.normal (v, mem)) :=
  multi_mirNoUB_safe_from_start hfrag hprog rootCtx
    (initMachineStateWithCallees entry args callees) mInit
    (initMachineStateWithCallees_startRel hfrag hfEntry rootCtx hctx args hargs mInit henv
      hthreads hactive hallocs)
    hsafe herr

/-- **Multi-function call-tree converse error soundness.** -/
theorem mirCallWithCallees_steps_error {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function}
    (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog)
    (hfEntry : translateFnInProg (fnNameMap entry callees) entry = some fEntry)
    (rootCtx : Ctx) (hctx : CtxOk entry rootCtx)
    (args : List Value) (hargs : argsOk entry args = true)
    (mInit : Mach) (henv : ProgEnvOk prog (fnNameMap entry callees) mInit)
    (hthreads : mInit.threads =
      [thread1 rootCtx [rootCtx.caller,
        { calleeFrame fEntry rootCtx (entry.argCount + 1) 0 0 with next_block := fEntry.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      rootCtx.base ++ localAllocs rootCtx (entry.localDecls.take (entry.argCount + 1))
        (initMachineStateWithCallees entry args callees).frame.locals)
    {n : Nat} {e : Stop} (herr : Interp.steps n mInit = .error e) :
    (∃ msg, e = .ub msg ∧ ∃ tr u,
      Reaches (mirCallTreeWithCallees entry args callees) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel entry rootCtx s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees entry args callees) tr (.normal (v, mem))) :=
  multi_steps_error_from_start hfrag hprog rootCtx n
    (initMachineStateWithCallees entry args callees) mInit e
    (initMachineStateWithCallees_startRel hfrag hfEntry rootCtx hctx args hargs mInit henv
      hthreads hactive hallocs)
    herr

/-- **Multi-function call-tree forward progress.** -/
theorem mirCallWithCallees_progress {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function}
    (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog)
    (hfEntry : translateFnInProg (fnNameMap entry callees) entry = some fEntry)
    (rootCtx : Ctx) (hctx : CtxOk entry rootCtx)
    (args : List Value) (hargs : argsOk entry args = true)
    (mInit : Mach) (henv : ProgEnvOk prog (fnNameMap entry callees) mInit)
    (hthreads : mInit.threads =
      [thread1 rootCtx [rootCtx.caller,
        { calleeFrame fEntry rootCtx (entry.argCount + 1) 0 0 with next_block := fEntry.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      rootCtx.base ++ localAllocs rootCtx (entry.localDecls.take (entry.argCount + 1))
        (initMachineStateWithCallees entry args callees).frame.locals)
    (hsafe : MirNoUBTree (mirCallTreeWithCallees entry args callees)) (n : Nat) :
    (∃ d s' m0 m' tr, Interp.steps (initLen entry + n) mInit = .ok m0 ∧
      Interp.steps (initLen entry + n + d) mInit = .ok m' ∧
      MultiStateRel entry callees prog rootCtx s' m' ∧
      Reaches (mirCallTreeWithCallees entry args callees) tr (mirTree entry s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen entry + n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel entry rootCtx s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees entry args callees) tr (.normal (v, mem))) :=
  multi_mirNoUB_progress_from_start hfrag hprog rootCtx
    (initMachineStateWithCallees entry args callees) mInit
    (initMachineStateWithCallees_startRel hfrag hfEntry rootCtx hctx args hargs mInit henv
      hthreads hactive hallocs)
    hsafe n

/-- **Multi-function call-tree total `(initLen entry + n)`-step outcome
trichotomy.** -/
theorem mirCallWithCallees_outcome {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function}
    (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog)
    (hfEntry : translateFnInProg (fnNameMap entry callees) entry = some fEntry)
    (rootCtx : Ctx) (hctx : CtxOk entry rootCtx)
    (args : List Value) (hargs : argsOk entry args = true)
    (mInit : Mach) (henv : ProgEnvOk prog (fnNameMap entry callees) mInit)
    (hthreads : mInit.threads =
      [thread1 rootCtx [rootCtx.caller,
        { calleeFrame fEntry rootCtx (entry.argCount + 1) 0 0 with next_block := fEntry.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      rootCtx.base ++ localAllocs rootCtx (entry.localDecls.take (entry.argCount + 1))
        (initMachineStateWithCallees entry args callees).frame.locals)
    (n : Nat) :
    (∃ d s' m0 m' tr, Interp.steps (initLen entry + n) mInit = .ok m0 ∧
      Interp.steps (initLen entry + n + d) mInit = .ok m' ∧
      MultiStateRel entry callees prog rootCtx s' m' ∧
      Reaches (mirCallTreeWithCallees entry args callees) tr (mirTree entry s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen entry + n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel entry rootCtx s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees entry args callees) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (initLen entry + n) mInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTreeWithCallees entry args callees) tr u ∧ FaultNow u) :=
  multi_steps_outcome_from_start hfrag hprog rootCtx n
    (initMachineStateWithCallees entry args callees) mInit
    (initMachineStateWithCallees_startRel hfrag hfEntry rootCtx hctx args hargs mInit henv
      hthreads hactive hallocs)

/-- **Multi-function call-tree diverging UB-free execution.** -/
theorem mirCallWithCallees_diverges_steps_ok {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function}
    (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog)
    (hfEntry : translateFnInProg (fnNameMap entry callees) entry = some fEntry)
    (rootCtx : Ctx) (hctx : CtxOk entry rootCtx)
    (args : List Value) (hargs : argsOk entry args = true)
    (mInit : Mach) (henv : ProgEnvOk prog (fnNameMap entry callees) mInit)
    (hthreads : mInit.threads =
      [thread1 rootCtx [rootCtx.caller,
        { calleeFrame fEntry rootCtx (entry.argCount + 1) 0 0 with next_block := fEntry.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      rootCtx.base ++ localAllocs rootCtx (entry.localDecls.take (entry.argCount + 1))
        (initMachineStateWithCallees entry args callees).frame.locals)
    (hsafe : MirNoUBTree (mirCallTreeWithCallees entry args callees))
    (hdiv : ∀ tr o, ¬ ReachesRet (mirCallTreeWithCallees entry args callees) tr o) (n : Nat) :
    ∃ m', Interp.steps n mInit = .ok m' :=
  multi_mirNoUB_diverges_from_start hfrag hprog rootCtx
    (initMachineStateWithCallees entry args callees) mInit
    (initMachineStateWithCallees_startRel hfrag hfEntry rootCtx hctx args hargs mInit henv
      hthreads hactive hallocs)
    hsafe hdiv n

/-- **Coupled multi-function call-tree diverging UB-free execution.** -/
theorem mirCallWithCallees_diverges_rel {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function}
    (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog)
    (hfEntry : translateFnInProg (fnNameMap entry callees) entry = some fEntry)
    (rootCtx : Ctx) (hctx : CtxOk entry rootCtx)
    (args : List Value) (hargs : argsOk entry args = true)
    (mInit : Mach) (henv : ProgEnvOk prog (fnNameMap entry callees) mInit)
    (hthreads : mInit.threads =
      [thread1 rootCtx [rootCtx.caller,
        { calleeFrame fEntry rootCtx (entry.argCount + 1) 0 0 with next_block := fEntry.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      rootCtx.base ++ localAllocs rootCtx (entry.localDecls.take (entry.argCount + 1))
        (initMachineStateWithCallees entry args callees).frame.locals)
    (hsafe : MirNoUBTree (mirCallTreeWithCallees entry args callees))
    (hdiv : ∀ tr o, ¬ ReachesRet (mirCallTreeWithCallees entry args callees) tr o) (n : Nat) :
    ∃ d s' m0 m' tr, Interp.steps (initLen entry + n) mInit = .ok m0 ∧
      Interp.steps (initLen entry + n + d) mInit = .ok m' ∧
      MultiStateRel entry callees prog rootCtx s' m' ∧
      Reaches (mirCallTreeWithCallees entry args callees) tr (mirTree entry s') :=
  multi_mirNoUB_diverges_rel_from_start hfrag hprog rootCtx
    (initMachineStateWithCallees entry args callees) mInit
    (initMachineStateWithCallees_startRel hfrag hfEntry rootCtx hctx args hargs mInit henv
      hthreads hactive hallocs)
    hsafe hdiv n

/-- **Multi-function call-tree arbitrary-`n` forward progress (covering all
`n : Nat`, including startup steps `n ≤ initLen entry` in `fEntry.start`).** -/
theorem mirCallWithCallees_progress_any {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function}
    (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog)
    (hfEntry : translateFnInProg (fnNameMap entry callees) entry = some fEntry)
    (rootCtx : Ctx) (hctx : CtxOk entry rootCtx)
    (args : List Value) (hargs : argsOk entry args = true)
    (mInit : Mach) (henv : ProgEnvOk prog (fnNameMap entry callees) mInit)
    (hthreads : mInit.threads =
      [thread1 rootCtx [rootCtx.caller,
        { calleeFrame fEntry rootCtx (entry.argCount + 1) 0 0 with next_block := fEntry.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      rootCtx.base ++ localAllocs rootCtx (entry.localDecls.take (entry.argCount + 1))
        (initMachineStateWithCallees entry args callees).frame.locals)
    (hsafe : MirNoUBTree (mirCallTreeWithCallees entry args callees)) (n : Nat) :
    (∃ d s' m0 m' tr, Interp.steps n mInit = .ok m0 ∧
      Interp.steps (n + d) mInit = .ok m' ∧
      MultiStateRel entry callees prog rootCtx s' m' ∧
      Reaches (mirCallTreeWithCallees entry args callees) tr (mirTree entry s')) ∨
    (∃ k s' mRet tr v mem, k ≤ n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel entry rootCtx s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees entry args callees) tr (.normal (v, mem))) :=
  multi_mirNoUB_progress_any_from_start hfrag hprog rootCtx
    (initMachineStateWithCallees entry args callees) mInit
    (initMachineStateWithCallees_startRel hfrag hfEntry rootCtx hctx args hargs mInit henv
      hthreads hactive hallocs)
    hsafe n

/-- **Multi-function call-tree total arbitrary-`n` outcome trichotomy (covering
all `n : Nat`, including startup steps `n ≤ initLen entry`).** -/
theorem mirCallWithCallees_outcome_any {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function}
    (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog)
    (hfEntry : translateFnInProg (fnNameMap entry callees) entry = some fEntry)
    (rootCtx : Ctx) (hctx : CtxOk entry rootCtx)
    (args : List Value) (hargs : argsOk entry args = true)
    (mInit : Mach) (henv : ProgEnvOk prog (fnNameMap entry callees) mInit)
    (hthreads : mInit.threads =
      [thread1 rootCtx [rootCtx.caller,
        { calleeFrame fEntry rootCtx (entry.argCount + 1) 0 0 with next_block := fEntry.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      rootCtx.base ++ localAllocs rootCtx (entry.localDecls.take (entry.argCount + 1))
        (initMachineStateWithCallees entry args callees).frame.locals)
    (n : Nat) :
    (∃ d s' m0 m' tr, Interp.steps n mInit = .ok m0 ∧
      Interp.steps (n + d) mInit = .ok m' ∧
      MultiStateRel entry callees prog rootCtx s' m' ∧
      Reaches (mirCallTreeWithCallees entry args callees) tr (mirTree entry s')) ∨
    (∃ k s' mRet tr v mem, k ≤ n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel entry rootCtx s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees entry args callees) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps n mInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTreeWithCallees entry args callees) tr u ∧ FaultNow u) :=
  multi_steps_outcome_any_from_start hfrag hprog rootCtx n
    (initMachineStateWithCallees entry args callees) mInit
    (initMachineStateWithCallees_startRel hfrag hfEntry rootCtx hctx args hargs mInit henv
      hthreads hactive hallocs)

end MiniRustSpec.Correspondence
