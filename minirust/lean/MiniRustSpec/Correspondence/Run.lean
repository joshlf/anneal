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

/-- Every Anneal execution prefix from related states (`StateRelN`) is matched
by MiniRust steps to a related state (`StateRelN`). -/
theorem reaches_rel_N {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) {t u : ITree MirEffect MirOutcome}
    {tr : List (Event MirEffect)} (h : Reaches t tr u) :
    ∀ (s : MachineState) (m : Mach), t = mirTree body s → StateRelN body f ctx s m →
      ∃ (n : Nat) (s' : MachineState) (m' : Mach), Interp.steps n m = .ok m' ∧
        StateRelN body f ctx s' m' ∧ u = mirTree body s' := by
  induction h with
  | refl t =>
    intro s m ht hrel
    exact ⟨0, s, m, rfl, hrel, ht⟩
  | tau hobs _ ih =>
    intro s m ht hrel
    subst ht
    have hsr := step_correspondence_N body f hfrag hf ctx s m hrel
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
    have hsr := step_correspondence_N body f hfrag hf ctx s m hrel
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

/-- Every Anneal execution prefix from related states is matched by MiniRust
steps to a related state. -/
theorem reaches_rel {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) {t u : ITree MirEffect MirOutcome}
    {tr : List (Event MirEffect)} (h : Reaches t tr u)
    (s : MachineState) (m : Mach) (ht : t = mirTree body s)
    (hrel : StateRel body f ctx s m)
    (hall : body.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) = true := by decide) :
    ∃ (n : Nat) (s' : MachineState) (m' : Mach), Interp.steps n m = .ok m' ∧
      StateRel body f ctx s' m' ∧ u = mirTree body s' :=
  let ⟨n, s', m', hsteps, hrel', hu⟩ := reaches_rel_N hfrag hf ctx h s m ht (hrel.toStateRelN hall)
  ⟨n, s', m', hsteps, hrel'.toStateRel, hu⟩

/-- **Returns (`StateRelN`).** If Anneal's semantics of `body` from `s` returns
`v` (along any trace of branch observations), MiniRust, started from a
`StateRelN`-related machine, performs the corresponding function return after
finitely many steps. -/
theorem run_ret_N {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRelN body f ctx s m) {tr : List (Event MirEffect)} {v : Value}
    {mem : MirSemantics.Memory} (hret : ReachesRet (mirTree body s) tr (.normal (v, mem))) :
    ∃ (n : Nat) (s' : MachineState) (m' : Mach),
      Interp.steps n m = .ok m' ∧ ReturnRel body ctx s' v m' := by
  obtain ⟨u, hreach, hu⟩ := hret
  obtain ⟨n, s', m', hsteps, hrel', rfl⟩ := reaches_rel_N hfrag hf ctx hreach s m rfl hrel
  have hsr := step_correspondence_N body f hfrag hf ctx s' m' hrel'
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

/-- **Returns.** If Anneal's semantics of `body` from `s` returns `v` (along
any trace of branch observations), MiniRust, started from a related machine,
performs the corresponding function return after finitely many steps. -/
theorem run_ret {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRel body f ctx s m) {tr : List (Event MirEffect)} {v : Value}
    {mem : MirSemantics.Memory} (hret : ReachesRet (mirTree body s) tr (.normal (v, mem)))
    (hall : body.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) = true := by decide) :
    ∃ (n : Nat) (s' : MachineState) (m' : Mach),
      Interp.steps n m = .ok m' ∧ ReturnRel body ctx s' v m' :=
  run_ret_N hfrag hf ctx s m (hrel.toStateRelN hall) hret

/-- **Returns from `f.start`.** Starting MiniRust at the `minimize` entry
block (`f.start = bbName body.basicBlocks.length`) under `StartRel` steps
through `initBlock` into `bb0` and then matches Anneal's return from `s`. -/
theorem run_ret_from_start {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (s : MachineState) (mInit : Mach)
    (hstart : StartRel body f ctx s mInit)
    {tr : List (Event MirEffect)} {v : Value} {mem : MirSemantics.Memory}
    (hret : ReachesRet (mirTree body s) tr (.normal (v, mem)))
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide) :
    ∃ (n : Nat) (s' : MachineState) (m' : Mach),
      Interp.steps n mInit = .ok m' ∧ ReturnRel body ctx s' v m' := by
  obtain ⟨m0, hm0, hrel0⟩ := step_start_N hfrag hf hstart hns
  obtain ⟨n, s', m', hsteps, hret'⟩ := run_ret_N hfrag hf ctx s m0 hrel0 hret
  exact ⟨initLen body + n, s', m', by rw [steps_add, hm0, ok_bind, hsteps], hret'⟩

/-- **UB (`StateRelN`).** If Anneal's semantics of `body` from `s` can reach UB
(along any trace of branch observations), MiniRust, started from a
`StateRelN`-related machine, raises UB after finitely many steps. -/
theorem run_ub_N {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRelN body f ctx s m) {tr : List (Event MirEffect)} {u : ITree MirEffect MirOutcome}
    (hreach : Reaches (mirTree body s) tr u) (hfault : FaultNow u) :
    ∃ (n : Nat) (msg : String), Interp.steps n m = .error (.ub msg) := by
  obtain ⟨t', i, k, htau, hobs, hfi⟩ := hfault
  obtain ⟨n1, s1, m1, h1, hrel1, rfl⟩ := reaches_rel_N hfrag hf ctx hreach s m rfl hrel
  obtain ⟨n2, s2, m2, h2, hrel2, rfl⟩ :=
    reaches_rel_N hfrag hf ctx (tauStar_reaches htau) s1 m1 rfl hrel1
  have hsr := step_correspondence_N body f hfrag hf ctx s2 m2 hrel2
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

/-- **UB.** If Anneal's semantics of `body` from `s` can reach UB (along any
trace of branch observations), MiniRust, started from a related machine,
raises UB after finitely many steps. -/
theorem run_ub {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRel body f ctx s m) {tr : List (Event MirEffect)} {u : ITree MirEffect MirOutcome}
    (hreach : Reaches (mirTree body s) tr u) (hfault : FaultNow u)
    (hall : body.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) = true := by decide) :
    ∃ (n : Nat) (msg : String), Interp.steps n m = .error (.ub msg) :=
  run_ub_N hfrag hf ctx s m (hrel.toStateRelN hall) hreach hfault

/-- **UB from `f.start`.** Starting MiniRust at the `minimize` entry block
(`f.start = bbName body.basicBlocks.length`) under `StartRel` steps through
`initBlock` into `bb0` and then raises UB whenever Anneal's semantics from `s`
can reach UB. -/
theorem run_ub_from_start {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (s : MachineState) (mInit : Mach)
    (hstart : StartRel body f ctx s mInit)
    {tr : List (Event MirEffect)} {u : ITree MirEffect MirOutcome}
    (hreach : Reaches (mirTree body s) tr u) (hfault : FaultNow u)
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide) :
    ∃ (n : Nat) (msg : String), Interp.steps n mInit = .error (.ub msg) := by
  obtain ⟨m0, hm0, hrel0⟩ := step_start_N hfrag hf hstart hns
  obtain ⟨n, msg, hsteps⟩ := run_ub_N hfrag hf ctx s m0 hrel0 hreach hfault
  exact ⟨initLen body + n, msg, by rw [steps_add, hm0, ok_bind, hsteps]⟩

/-- **Errors (`StateRelN`).** If MiniRust stops with an error `e` within `n`
steps of a `StateRelN`-related machine, then either `e` is UB and Anneal's
semantics can reach UB, or MiniRust already completed the callee's return
(`ReturnRel`, matching an Anneal `ReachesRet`) in `k < n` steps and only errored
later inside the unmodeled caller frame. -/
theorem steps_error_N {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (n : Nat) :
    ∀ (s : MachineState) (m : Mach) (e : Stop), StateRelN body f ctx s m →
      Interp.steps n m = .error e →
      (∃ msg, e = .ub msg ∧ ∃ tr u, Reaches (mirTree body s) tr u ∧ FaultNow u) ∨
      (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k m = .ok mRet ∧
        ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem))) := by
  induction n with
  | zero => intro s m e _ h; simp [Interp.steps] at h
  | succ n ih =>
    intro s m e hrel h
    have hsr := step_correspondence_N body f hfrag hf ctx s m hrel
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

/-- **Errors.** If MiniRust stops with an error `e` within `n` steps of a
related machine, then either `e` is UB and Anneal's semantics can reach UB, or
MiniRust already completed the callee's return (`ReturnRel`, matching an Anneal
`ReachesRet`) in `k < n` steps and only errored later inside the unmodeled
caller frame. -/
theorem steps_error {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (n : Nat)
    (s : MachineState) (m : Mach) (e : Stop) (hrel : StateRel body f ctx s m)
    (h : Interp.steps n m = .error e)
    (hall : body.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) = true := by decide) :
    (∃ msg, e = .ub msg ∧ ∃ tr u, Reaches (mirTree body s) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k m = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem))) :=
  steps_error_N hfrag hf ctx n s m e (hrel.toStateRelN hall) h

/-- **Errors from `f.start`.** Converse soundness starting at MiniRust's
`f.start` (`initBlock`): if MiniRust stops with an error `e` within `n` steps
from `StartRel`, then either `e` is UB and Anneal reaches UB, or MiniRust
already completed the callee's return (`ReturnRel`, matching an Anneal
`ReachesRet`) in `k < n` steps. -/
theorem steps_error_from_start {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (n : Nat) (s : MachineState) (mInit : Mach) (e : Stop)
    (hstart : StartRel body f ctx s mInit) (h : Interp.steps n mInit = .error e)
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide) :
    (∃ msg, e = .ub msg ∧ ∃ tr u, Reaches (mirTree body s) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem))) := by
  obtain ⟨m0, hm0, hrel0⟩ := step_start_N hfrag hf hstart hns
  by_cases hn : n ≤ initLen body
  · obtain ⟨mj, hmj⟩ := steps_ok_mono hn hm0
    rw [hmj] at h
    cases h
  · obtain ⟨n', rfl⟩ : ∃ n', n = initLen body + n' := ⟨n - initLen body, by omega⟩
    rw [steps_add, hm0, ok_bind] at h
    rcases steps_error_N hfrag hf ctx n' s m0 e hrel0 h with
      hUb | ⟨k, s', mRet, tr, v, mem, hklt, hksteps, hretRel, hret⟩
    · exact .inl hUb
    · exact .inr ⟨initLen body + k, s', mRet, tr, v, mem, by omega,
        by rw [steps_add, hm0, ok_bind, hksteps], hretRel, hret⟩

/-- **UB-freedom transfer (`StateRelN`).** If Anneal's interaction tree
satisfies `MirNoUBTree` (`TreeSafe`), MiniRust never stops with any error
during the callee's execution from a `StateRelN` state. -/
theorem mirNoUB_safe_N {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRelN body f ctx s m) (hsafe : MirNoUBTree (mirTree body s))
    {n : Nat} {e : Stop} (herr : Interp.steps n m = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k m = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem)) := by
  rcases steps_error_N hfrag hf ctx n s m e hrel herr with ⟨_, _, tr, u, hr, hfault⟩ | hret
  · exact False.elim (hsafe tr u hr hfault)
  · exact hret

/-- **UB-freedom transfer.** If Anneal's interaction tree satisfies
`MirNoUBTree` (`TreeSafe`), MiniRust never stops with any error (`.ub`,
`.specPanic`, `.deadlock`, or `.unsupported`) during the callee's execution:
any error within `n` steps occurs strictly after `k < n` steps at which
MiniRust has already returned normally via `ReturnRel`. -/
theorem mirNoUB_safe {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRel body f ctx s m) (hsafe : MirNoUBTree (mirTree body s))
    {n : Nat} {e : Stop} (herr : Interp.steps n m = .error e)
    (hall : body.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) = true := by decide) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k m = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem)) :=
  mirNoUB_safe_N hfrag hf ctx s m (hrel.toStateRelN hall) hsafe herr

/-- **UB-freedom transfer from `f.start`.** Same guarantee starting at
`minimize`'s entry block `f.start`. -/
theorem mirNoUB_safe_from_start {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (s : MachineState) (mInit : Mach)
    (hstart : StartRel body f ctx s mInit) (hsafe : MirNoUBTree (mirTree body s))
    {n : Nat} {e : Stop} (herr : Interp.steps n mInit = .error e)
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem)) := by
  rcases steps_error_from_start hfrag hf ctx n s mInit e hstart herr hns with
    ⟨_, _, tr, u, hr, hfault⟩ | hret
  · exact False.elim (hsafe tr u hr hfault)
  · exact hret

/-- **Total `n`-step outcome trichotomy (`StateRelN`).** From related states
`StateRelN`, for every step budget `n : Nat`, running MiniRust for `n` steps
either stays in lockstep `StateRel`, has already completed the callee's return
(`ReturnRel`), or stopped with UB matching an Anneal `FaultNow`. -/
theorem steps_outcome_N {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (n : Nat) :
    ∀ (s : MachineState) (m : Mach), StateRelN body f ctx s m →
      (∃ s' m' tr, Interp.steps n m = .ok m' ∧ StateRel body f ctx s' m' ∧
        Reaches (mirTree body s) tr (mirTree body s')) ∨
      (∃ k s' mRet tr v mem, k ≤ n ∧ Interp.steps k m = .ok mRet ∧
        ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem))) ∨
      (∃ msg, Interp.steps n m = .error (.ub msg) ∧
        ∃ tr u, Reaches (mirTree body s) tr u ∧ FaultNow u) := by
  induction n with
  | zero =>
    intro s m hrel
    exact .inl ⟨s, m, [], rfl, hrel.toStateRel, .refl _⟩
  | succ n ih =>
    intro s m hrel
    have hsr := step_correspondence_N body f hfrag hf ctx s m hrel
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
    (hf : translateFn body = some f) (ctx : Ctx) (n : Nat)
    (s : MachineState) (m : Mach) (hrel : StateRel body f ctx s m)
    (hall : body.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) = true := by decide) :
    (∃ s' m' tr, Interp.steps n m = .ok m' ∧ StateRel body f ctx s' m' ∧
      Reaches (mirTree body s) tr (mirTree body s')) ∨
    (∃ k s' mRet tr v mem, k ≤ n ∧ Interp.steps k m = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps n m = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirTree body s) tr u ∧ FaultNow u) :=
  steps_outcome_N hfrag hf ctx n s m (hrel.toStateRelN hall)

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
    (hstart : StartRel body f ctx s mInit)
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide) :
    (∃ s' m' tr, Interp.steps (initLen body + n) mInit = .ok m' ∧ StateRel body f ctx s' m' ∧
      Reaches (mirTree body s) tr (mirTree body s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen body + n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (initLen body + n) mInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirTree body s) tr u ∧ FaultNow u) := by
  obtain ⟨m0, hm0, hrel0⟩ := step_start_N hfrag hf hstart hns
  rcases steps_outcome_N hfrag hf ctx n s m0 hrel0 with
    ⟨s', m', tr, hsteps, hrel', hr⟩ |
    ⟨k, s', mRet, tr, v, mem, hkle, hksteps, hretRel, hret⟩ |
    ⟨msg, herr, hfault⟩
  · exact .inl ⟨s', m', tr, by rw [steps_add, hm0, ok_bind, hsteps], hrel', hr⟩
  · exact .inr (.inl ⟨initLen body + k, s', mRet, tr, v, mem, by omega,
      by rw [steps_add, hm0, ok_bind, hksteps], hretRel, hret⟩)
  · exact .inr (.inr ⟨msg, by rw [steps_add, hm0, ok_bind, herr], hfault⟩)

/-- **Forward progress under `MirNoUBTree` (`StateRelN`).** -/
theorem mirNoUB_progress_N {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRelN body f ctx s m) (hsafe : MirNoUBTree (mirTree body s)) (n : Nat) :
    (∃ s' m' tr, Interp.steps n m = .ok m' ∧ StateRel body f ctx s' m' ∧
      Reaches (mirTree body s) tr (mirTree body s')) ∨
    (∃ k s' mRet tr v mem, k ≤ n ∧ Interp.steps k m = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem))) := by
  rcases steps_outcome_N hfrag hf ctx n s m hrel with hrun | hret | ⟨_, _, tr, u, hr, hfault⟩
  · exact .inl hrun
  · exact .inr hret
  · exact False.elim (hsafe tr u hr hfault)

/-- **Forward progress under `MirNoUBTree`.** When Anneal's interaction tree is
UB-free (`MirNoUBTree`), for every `n : Nat`, MiniRust either advances `n`
steps to a lockstep `StateRel` state `m'` or has already returned normally via
`ReturnRel` in `k ≤ n` steps. -/
theorem mirNoUB_progress {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRel body f ctx s m) (hsafe : MirNoUBTree (mirTree body s)) (n : Nat)
    (hall : body.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) = true := by decide) :
    (∃ s' m' tr, Interp.steps n m = .ok m' ∧ StateRel body f ctx s' m' ∧
      Reaches (mirTree body s) tr (mirTree body s')) ∨
    (∃ k s' mRet tr v mem, k ≤ n ∧ Interp.steps k m = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem))) :=
  mirNoUB_progress_N hfrag hf ctx s m (hrel.toStateRelN hall) hsafe n

/-- **Forward progress from `f.start` under `MirNoUBTree`.** For every `n : Nat`,
MiniRust started at `f.start` (`StartRel`) either advances `initLen body + n`
steps to a lockstep `StateRel` state `m'` or returns normally via `ReturnRel` in
`k ≤ initLen body + n` steps. -/
theorem mirNoUB_progress_from_start {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (s : MachineState) (mInit : Mach)
    (hstart : StartRel body f ctx s mInit) (hsafe : MirNoUBTree (mirTree body s)) (n : Nat)
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide) :
    (∃ s' m' tr, Interp.steps (initLen body + n) mInit = .ok m' ∧ StateRel body f ctx s' m' ∧
      Reaches (mirTree body s) tr (mirTree body s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen body + n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirTree body s) tr (.normal (v, mem))) := by
  obtain ⟨m0, hm0, hrel0⟩ := step_start_N hfrag hf hstart hns
  rcases mirNoUB_progress_N hfrag hf ctx s m0 hrel0 hsafe n with
    ⟨s', m', tr, hsteps, hrel', hr⟩ | ⟨k, s', mRet, tr, v, mem, hkle, hksteps, hretRel, hret⟩
  · exact .inl ⟨s', m', tr, by rw [steps_add, hm0, ok_bind, hsteps], hrel', hr⟩
  · exact .inr ⟨initLen body + k, s', mRet, tr, v, mem, by omega,
      by rw [steps_add, hm0, ok_bind, hksteps], hretRel, hret⟩

/-- **Diverging UB-free execution from `StateRelN`.** -/
theorem mirNoUB_diverges_steps_ok_N {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRelN body f ctx s m) (hsafe : MirNoUBTree (mirTree body s))
    (hdiv : ∀ tr o, ¬ ReachesRet (mirTree body s) tr o) (n : Nat) :
    ∃ s' m' tr, Interp.steps n m = .ok m' ∧ StateRel body f ctx s' m' ∧
      Reaches (mirTree body s) tr (mirTree body s') := by
  rcases mirNoUB_progress_N hfrag hf ctx s m hrel hsafe n with
    hrun | ⟨_, _, _, tr, v, mem, _, _, _, hret⟩
  · exact hrun
  · exact False.elim (hdiv tr (.normal (v, mem)) hret)

/-- **Diverging UB-free execution from `StateRel`.** If Anneal's interaction
tree is UB-free (`MirNoUBTree`) and never reaches a return outcome, MiniRust
steps forever in lockstep `StateRel` without ever stopping with an error. -/
theorem mirNoUB_diverges_steps_ok {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRel body f ctx s m) (hsafe : MirNoUBTree (mirTree body s))
    (hdiv : ∀ tr o, ¬ ReachesRet (mirTree body s) tr o) (n : Nat)
    (hall : body.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) = true := by decide) :
    ∃ s' m' tr, Interp.steps n m = .ok m' ∧ StateRel body f ctx s' m' ∧
      Reaches (mirTree body s) tr (mirTree body s') :=
  mirNoUB_diverges_steps_ok_N hfrag hf ctx s m (hrel.toStateRelN hall) hsafe hdiv n

/-- **Diverging UB-free execution from `f.start`.** If Anneal's interaction tree
is UB-free and never returns, MiniRust started at `f.start` (`StartRel`)
succeeds for every step count `n : Nat`. -/
theorem mirNoUB_diverges_from_start {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (hf : translateFn body = some f)
    (ctx : Ctx) (s : MachineState) (mInit : Mach)
    (hstart : StartRel body f ctx s mInit) (hsafe : MirNoUBTree (mirTree body s))
    (hdiv : ∀ tr o, ¬ ReachesRet (mirTree body s) tr o) (n : Nat)
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide) :
    ∃ m', Interp.steps n mInit = .ok m' := by
  obtain ⟨m0, hm0, hrel0⟩ := step_start_N hfrag hf hstart hns
  by_cases hn : n ≤ initLen body
  · exact steps_ok_mono hn hm0
  · obtain ⟨n', rfl⟩ : ∃ n', n = initLen body + n' := ⟨n - initLen body, by omega⟩
    obtain ⟨_, m', _, hsteps, _, _⟩ :=
      mirNoUB_diverges_steps_ok_N hfrag hf ctx s m0 hrel0 hsafe hdiv n'
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
    (hdiv : ∀ tr o, ¬ ReachesRet (mirTree body s) tr o) (n : Nat)
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide) :
    ∃ s' m' tr, Interp.steps (initLen body + n) mInit = .ok m' ∧ StateRel body f ctx s' m' ∧
      Reaches (mirTree body s) tr (mirTree body s') := by
  obtain ⟨m0, hm0, hrel0⟩ := step_start_N hfrag hf hstart hns
  obtain ⟨s', m', tr, hsteps, hrel', hr⟩ :=
    mirNoUB_diverges_steps_ok_N hfrag hf ctx s m0 hrel0 hsafe hdiv n
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
        (initMachineState body args).frame.locals body.layouts)
    {tr : List (Event MirEffect)} {v : Value} {mem : MirSemantics.Memory}
    (hret : ReachesRet (mirCallTree body args) tr (.normal (v, mem))) :
    ∃ (n : Nat) (s' : MachineState) (m' : Mach),
      Interp.steps n mInit = .ok m' ∧ ReturnRel body ctx s' v m' :=
  run_ret_from_start hfrag hf ctx (initMachineState body args) mInit
    (initMachineState_startRel hfrag ctx hctx args hargs mInit hthreads hactive hallocs) hret
    (initMachineState_nonScalar hfrag args hargs)

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
        (initMachineState body args).frame.locals body.layouts)
    {tr : List (Event MirEffect)} {u : ITree MirEffect MirOutcome}
    (hreach : Reaches (mirCallTree body args) tr u) (hfault : FaultNow u) :
    ∃ (n : Nat) (msg : String), Interp.steps n mInit = .error (.ub msg) :=
  run_ub_from_start hfrag hf ctx (initMachineState body args) mInit
    (initMachineState_startRel hfrag ctx hctx args hargs mInit hthreads hactive hallocs) hreach hfault
    (initMachineState_nonScalar hfrag args hargs)

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
        (initMachineState body args).frame.locals body.layouts)
    (hsafe : MirNoUBTree (mirCallTree body args))
    {n : Nat} {e : Stop} (herr : Interp.steps n mInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirCallTree body args) tr (.normal (v, mem)) :=
  mirNoUB_safe_from_start hfrag hf ctx (initMachineState body args) mInit
    (initMachineState_startRel hfrag ctx hctx args hargs mInit hthreads hactive hallocs) hsafe herr
    (initMachineState_nonScalar hfrag args hargs)

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
        (initMachineState body args).frame.locals body.layouts)
    (hsafe : MirNoUBTree (mirCallTree body args)) (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen body + n) mInit = .ok m' ∧ StateRel body f ctx s' m' ∧
      Reaches (mirCallTree body args) tr (mirTree body s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen body + n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirCallTree body args) tr (.normal (v, mem))) :=
  mirNoUB_progress_from_start hfrag hf ctx (initMachineState body args) mInit
    (initMachineState_startRel hfrag ctx hctx args hargs mInit hthreads hactive hallocs) hsafe n
    (initMachineState_nonScalar hfrag args hargs)

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
        (initMachineState body args).frame.locals body.layouts)
    (hsafe : MirNoUBTree (mirCallTree body args))
    (hdiv : ∀ tr o, ¬ ReachesRet (mirCallTree body args) tr o) (n : Nat) :
    ∃ m', Interp.steps n mInit = .ok m' :=
  mirNoUB_diverges_from_start hfrag hf ctx (initMachineState body args) mInit
    (initMachineState_startRel hfrag ctx hctx args hargs mInit hthreads hactive hallocs) hsafe hdiv n
    (initMachineState_nonScalar hfrag args hargs)

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
        (initMachineState body args).frame.locals body.layouts)
    {n : Nat} {e : Stop} (herr : Interp.steps n mInit = .error e) :
    (∃ msg, e = .ub msg ∧ ∃ tr u, Reaches (mirCallTree body args) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirCallTree body args) tr (.normal (v, mem))) :=
  steps_error_from_start hfrag hf ctx n (initMachineState body args) mInit e
    (initMachineState_startRel hfrag ctx hctx args hargs mInit hthreads hactive hallocs) herr
    (initMachineState_nonScalar hfrag args hargs)

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
        (initMachineState body args).frame.locals body.layouts)
    (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen body + n) mInit = .ok m' ∧ StateRel body f ctx s' m' ∧
      Reaches (mirCallTree body args) tr (mirTree body s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen body + n ∧ Interp.steps k mInit = .ok mRet ∧
      ReturnRel body ctx s' v mRet ∧ ReachesRet (mirCallTree body args) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (initLen body + n) mInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree body args) tr u ∧ FaultNow u) :=
  steps_outcome_from_start hfrag hf ctx n (initMachineState body args) mInit
    (initMachineState_startRel hfrag ctx hctx args hargs mInit hthreads hactive hallocs)
    (initMachineState_nonScalar hfrag args hargs)

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
        (initMachineState body args).frame.locals body.layouts)
    (hsafe : MirNoUBTree (mirCallTree body args))
    (hdiv : ∀ tr o, ¬ ReachesRet (mirCallTree body args) tr o) (n : Nat) :
    ∃ s' m' tr, Interp.steps (initLen body + n) mInit = .ok m' ∧ StateRel body f ctx s' m' ∧
      Reaches (mirCallTree body args) tr (mirTree body s') :=
  mirNoUB_diverges_rel_from_start hfrag hf ctx (initMachineState body args) mInit
    (initMachineState_startRel hfrag ctx hctx args hargs mInit hthreads hactive hallocs)
    hsafe hdiv n (initMachineState_nonScalar hfrag args hargs)

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

end MiniRustSpec.Correspondence
