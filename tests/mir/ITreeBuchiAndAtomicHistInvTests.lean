-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean
import Anneal.ITreeBuchi
import Anneal.AtomicHistInv

/-!
# `Anneal.ITreeBuchi` + `Anneal.AtomicHistInv` Test Suite

1. **Positive witnesses**: a `#![no_std]` `-> !` request/response server
   (`Always` + `InfOften` + `BuchiSat`, yet `¬ DWP`); a monotone
   `AtomicU64::try_update` counter with a stateful attempt-counting `FnMut`
   closure, a ghost-log committer callback, safety under arbitrary contention and
   termination under bounded contention; a concrete `AtomicDualContract` built
   from a kernel-checked `lmAuthorityCheck` witness and the threaded MiniRust
   trace `5 → 8 → 8 (CAS✗) → 9 (CAS✓) → 9`.
2. **Negative fail-closed canaries**: `ITree.spin` refutes `Eventually`,
   `Until`, `InfOften` and `BuchiSat`; loops that stop accepting refute
   `InfOften`; non-reflexive / non-transitive relations and non-`hist_inv`-closed
   closure preconditions break the contract; unbounded contention refutes `DWP`;
   UB / spec-panic / `Frozen`-write steps are rejected by `AdmissibleAtomicStep`.
3. **Compile-time audit (`run_cmd`)**: axioms, definition safety, theorem
   non-triviality and theorem-count floors over all three namespaces, with
   self-tests of the auditor.
-/

namespace Anneal.ITreeBuchiAndAtomicHistInvTests

open Trusted.Effect
open Trusted.ITree
open Anneal.Effect
open Anneal.ITree
open Anneal.EffectWP
open Anneal.ITreeWP
open Anneal.ITreeBuchi
open Anneal.AtomicHistInv
open Anneal.Mir.AtomicIntrinsicsDualSpec

/-! ## 1. Positive Witnesses -/

/-! ### 1.1 `#![no_std]` `-> !` request/response server -/

/-- Server requests: receive a request id, or send a response. -/
inductive PingReq : Type where
  | recv
  | send (n : Nat)

/-- Answers of `PingReq`. -/
def PingAns : PingReq → Type
  | .recv => Nat
  | .send _ => PUnit

/-- The server effect. -/
abbrev PingE : Effect.{0} := CallE PingReq PingAns

/-- Logical server state. -/
structure PingSt where
  reqs : Nat
  resps : Nat
  lastReq : Nat
  lastResp : Nat

/-- Demonic network: any request id may arrive; sends always succeed. -/
def pingWP : StateEffectWP PingSt PingE where
  wp
    | .call .recv, K, s => ∀ n, K n { s with reqs := s.reqs + 1, lastReq := n }
    | .call (.send m), K, s => K PUnit.unit { s with resps := s.resps + 1, lastResp := m }
  mono {i} _ _ _ h hw :=
    match i with
    | .call .recv => fun n => h _ _ (hw n)
    | .call (.send _) => h _ _ hw

instance : StateEffectWP.Conjunctive pingWP where
  conj {i} _ _ _ hp hq :=
    match i with
    | .call .recv => fun n => ⟨hp n, hq n⟩
    | .call (.send _) => ⟨hp, hq⟩

instance : StateEffectWP.ExcludedMiracle pingWP where
  no_miracle {i} _ h :=
    match i with
    | .call .recv => h (0 : Nat)
    | .call (.send _) => h

/-- Serve one request: receive `n`, echo `n`. -/
def pingBody (k : Nat) : ITree PingE Nat :=
  ITree.vis (.call .recv : PingE.I) (fun n =>
    ITree.vis (.call (.send n) : PingE.I) (fun _ => ITree.ret (k + 1)))

/-- `fn server() -> ! { loop { let n = recv(); send(n); } }`. -/
def pingServer : ITree PingE PEmpty.{1} := divergingLoop pingBody 0

/-- At most one outstanding request, and an answered request was echoed. -/
def PingInv (s : PingSt) : Prop :=
  s.resps ≤ s.reqs ∧ s.reqs ≤ s.resps + 1 ∧ (s.resps = s.reqs → s.lastResp = s.lastReq)

/-- Loop head: every request answered with its echo. -/
def PingLInv (_ : Nat) (s : PingSt) : Prop := s.resps = s.reqs ∧ s.lastResp = s.lastReq

/-- Accepting edges: a response that echoes the pending request. -/
def PingAccept : (i : PingE.I) → PingE.O i → PingSt → PingSt → Prop
  | .call (.send m), _, s, _ => m = s.lastReq
  | _, _, _, _ => False

theorem pingBody_always (k : Nat) (s : PingSt) (h : PingLInv k s) :
    Always pingWP PingInv PingLInv (pingBody k) s := by
  obtain ⟨h1, h2⟩ := h
  refine Always.vis ⟨by omega, by omega, fun _ => h2⟩ fun n => ?_
  refine Always.vis ⟨by show s.resps ≤ s.reqs + 1; omega, by show s.reqs + 1 ≤ s.resps + 1; omega,
    fun he => absurd he (by show ¬ s.resps = s.reqs + 1; omega)⟩ ?_
  exact Always.ret ⟨by show s.resps + 1 ≤ s.reqs + 1; omega,
    by show s.reqs + 1 ≤ s.resps + 1 + 1; omega, fun _ => rfl⟩
    ⟨by show s.resps + 1 = s.reqs + 1; omega, rfl⟩

theorem pingBody_live (k : Nat) (s : PingSt) (_ : PingLInv k s) :
    buchiProgress pingWP PingAccept (fun _ _ => False) (InfOften pingWP PingAccept PingLInv)
      (pingBody k) s := by
  refine buchiProgress.vis_skip fun n => ?_
  refine buchiProgress.vis_accept ⟨rfl, InfOften.ret ⟨?_, rfl⟩⟩
  show s.resps + 1 = s.reqs + 1
  exact congrArg (· + 1) ‹PingLInv k s›.1

/--
**Reactive server witness**: the `-> !` echo server keeps the at-most-one-
outstanding invariant (`Always`), answers correctly infinitely often
(`InfOften`), satisfies the Büchi monitor (`BuchiSat`), and is genuinely
non-terminating (`¬ DWP`).
-/
theorem pingServer_spec (Q : PEmpty.{1} → PingSt → Prop) (s₀ : PingSt)
    (h₀ : PingLInv 0 s₀) :
    Always pingWP PingInv Q pingServer s₀ ∧ InfOften pingWP PingAccept Q pingServer s₀ ∧
      BuchiSat (BuchiSpec.trivial pingWP PingAccept PingInv Q) pingServer PUnit.unit s₀ ∧
      ¬ DWP pingWP pingServer Q s₀ := by
  have h := buchi_diverging_loop_rule pingBody PingLInv pingBody_always pingBody_live h₀ Q
  exact ⟨h.1, h.2, (buchiSat_trivial_iff_always_and_infOften _ _ _ _ _ _).2 h,
    not_dwp_diverging_loop pingBody 0⟩

theorem pingServer_concrete :
    InfOften pingWP PingAccept (fun _ _ => True) pingServer ⟨0, 0, 0, 0⟩ ∧
      ¬ DWP pingWP pingServer (fun _ _ => True) ⟨0, 0, 0, 0⟩ :=
  ⟨(pingServer_spec _ _ ⟨rfl, rfl⟩).2.1, (pingServer_spec _ _ ⟨rfl, rfl⟩).2.2.2⟩

/-! ### 1.2 Monotone `AtomicU64::try_update` counter -/

/-- Largest `u64`. -/
def u64Max : Nat := 2 ^ 64 - 1

/--
`try_update(|x| if x < limit { Some(x + delta) } else { None })` with a mutable
attempt counter `attempts ↦ attempts + 1` (`hist_inv : a₀ ≤ a`).
-/
def counterSpec (delta limit : Nat) : FnMutSpec Nat Nat Nat where
  hist_inv a a' := a ≤ a'
  hist_inv_laws := AtomicHistInv.nat_le
  pre _ _ := True
  post_mut a x a' r := a' = a + 1 ∧ r = (if x < limit then some (x + delta) else none)
  step_hist_inv _ _ _ _ h := h.1 ▸ Nat.le_succ _
  resolve _ := True

/-- Ghost callback appending the committed transition to a ghost log. -/
def logGC : GhostCommit Nat (List (Nat × Nat)) :=
  ⟨fun _ _ _ => True, fun g o n g' => g' = g ++ [(o, n)]⟩

/-- Monotone interference (other threads only increment). -/
def counterEnv (delta limit : Nat) : AtomicEnv Nat Nat (List (Nat × Nat)) :=
  ⟨(· ≤ ·), counterSpec delta limit, logGC⟩

theorem counter_pre (delta limit init a₀ : Nat) (g₀ : List (Nat × Nat)) :
    TryUpdatePre (counterEnv delta limit) (· ≤ ·) init a₀ g₀ (.fresh init) where
  cellInv := AtomicHistInv.nat_le
  closure_pre _ _ _ := trivial
  closure_step _ x _ n _ h _ := by
    obtain ⟨_, hr⟩ := h
    by_cases hx : x < limit
    · simp only [hx, ↓reduceIte] at hr; cases hr; exact ⟨Nat.le_add_right x delta, trivial⟩
    · simp only [hx, ↓reduceIte] at hr; cases hr
  rely_sound _ _ h := h
  comm_unshot := rfl

/-- Concrete initial state: cell `5`, no attempts, fresh committer, empty log. -/
def counterSt₀ (budget : Nat) : AtomicSt Nat Nat (List (Nat × Nat)) :=
  ⟨5, 0, .fresh 5, 0, [], budget⟩

theorem counterSt₀_init (b : Nat) : InitSt 5 0 [] (.fresh 5) (counterSt₀ b) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Safety under arbitrary contention** (`Always` + `DWLP`). -/
theorem counter_safe (delta limit b : Nat) :
    Always (atomicHistWP (counterEnv delta limit))
        (HistInvSt (counterEnv delta limit) (· ≤ ·) 5 0)
        (CreusotPost (counterEnv delta limit) (· ≤ ·) 5 0 [] (.fresh 5))
        (tryUpdateLoop Nat) (counterSt₀ b) ∧
      DWLP (guardInvWP (atomicHistWP (counterEnv delta limit))
          (HistInvSt (counterEnv delta limit) (· ≤ ·) 5 0)) (tryUpdateLoop Nat)
        (fun r s => HistInvSt (counterEnv delta limit) (· ≤ ·) 5 0 s ∧
          CreusotPost (counterEnv delta limit) (· ≤ ·) 5 0 [] (.fresh 5) r s) (counterSt₀ b) :=
  ⟨tryUpdate_always_safety (counter_pre _ _ _ _ _) (counterSt₀_init b),
   tryUpdate_dwlp_creusot_spec (counter_pre _ _ _ _ _) (counterSt₀_init b)⟩

/-- What the `creusot#2386` postcondition means for the counter. -/
def CounterOutcome (delta limit : Nat) :
    Except Nat Nat → AtomicSt Nat Nat (List (Nat × Nat)) → Prop
  | .ok old, s => 5 ≤ old ∧ old < limit ∧ s.cell = old + delta ∧ s.gst = [(old, old + delta)] ∧
      1 ≤ s.fst ∧ s.comm.shot_store = true ∧ s.fires = 1
  | .error cur, s => 5 ≤ cur ∧ limit ≤ cur ∧ s.cell = cur ∧ s.gst = [] ∧ 1 ≤ s.fst ∧
      s.comm.shot_store = false ∧ s.fires = 0

theorem counter_post_meaning (delta limit : Nat) (r : Except Nat Nat)
    (s : AtomicSt Nat Nat (List (Nat × Nat)))
    (h : CreusotPost (counterEnv delta limit) (· ≤ ·) 5 0 [] (.fresh 5) r s) :
    CounterOutcome delta limit r s := by
  cases r with
  | ok old =>
    obtain ⟨new, f₂, f₃, _, ⟨hf₃, hr⟩, _, hio, _, _, hcell, hfst, _, hshot, hfires, hg⟩ := h
    by_cases hx : old < limit
    · simp only [hx, ↓reduceIte] at hr; cases hr
      exact ⟨hio, hx, hcell, hg, by rw [hfst, hf₃]; omega, hshot, hfires⟩
    · simp only [hx, ↓reduceIte] at hr; cases hr
  | error cur =>
    obtain ⟨f₂, f₃, _, ⟨hf₃, hr⟩, _, hio, hcell, hfst, _, hshot, hfires, hg⟩ := h
    by_cases hx : cur < limit
    · simp only [hx, ↓reduceIte] at hr; cases hr
    · exact ⟨hio, by omega, hcell, hg, by rw [hfst, hf₃]; omega, hshot, hfires⟩

/--
**Liveness under bounded contention** (`DWP` + `Eventually`): the counter
returns `Ok old` with `cell = old + delta` and ghost log `[(old, old + delta)]`,
or `Err cur` at saturation `limit ≤ cur`, with the committer fired exactly when
the update committed.
-/
theorem counter_live (delta limit b : Nat) :
    DWP (atomicBudgetWP (counterEnv delta limit)) (tryUpdateLoop Nat)
        (CounterOutcome delta limit) (counterSt₀ b) ∧
      Eventually (atomicBudgetWP (counterEnv delta limit)) (fun s => s.comm.shot_store = true)
        (CounterOutcome delta limit) (tryUpdateLoop Nat) (counterSt₀ b) := by
  have h := DWP.mono (counter_post_meaning delta limit)
    (tryUpdate_dwp_ranked (counter_pre _ _ _ _ _) (counterSt₀_init b))
  exact ⟨h, eventually_of_dwp _ h⟩

/-- **`u64` width boundary**: below `limit` with `limit + delta ≤ 2^64` no commit overflows. -/
theorem counter_no_u64_overflow (delta limit : Nat) (hw : limit + delta ≤ u64Max + 1)
    (old : Nat) (s : AtomicSt Nat Nat (List (Nat × Nat)))
    (h : CounterOutcome delta limit (.ok old) s) : s.cell ≤ u64Max := by
  obtain ⟨_, hlt, hcell, _⟩ := h
  rw [hcell]; omega

/-- Counter with bounded contention also satisfies `Always` + Streett + enabledness. -/
theorem counter_fairness (delta limit b : Nat) :
    FairInfOften (atomicHistWP (counterEnv delta limit)) (fun _ _ _ _ => False) CasWon
        (CreusotPost (counterEnv delta limit) (· ≤ ·) 5 0 [] (.fresh 5))
        (tryUpdateLoop Nat) (counterSt₀ b) ∧
      InfOften (atomicHistWP (counterEnv delta limit)) CasAttempt
        (CreusotPost (counterEnv delta limit) (· ≤ ·) 5 0 [] (.fresh 5))
        (tryUpdateLoop Nat) (counterSt₀ b) ∧
      FairBuchiSat (committerSpec (counterEnv delta limit) (· ≤ ·) 5 0 [] (.fresh 5))
        (fun _ i o s s' _ => CasWon i o s s') (tryUpdateLoop Nat) false (counterSt₀ b) :=
  ⟨tryUpdate_fairInfOften (counter_pre _ _ _ _ _) (counterSt₀_init b) _,
   tryUpdate_infOften_attemptCas (counter_pre _ _ _ _ _) (counterSt₀_init b),
   tryUpdate_fairBuchiSat_committer (counter_pre _ _ _ _ _) (counterSt₀_init b)⟩

/-! ### 1.3 Concrete dual-authority contract and threaded trace -/

/-- LeanMiri-shaped witness observation (the frozen `lmExpectedOutcome` table). -/
def lmObsWitness : Bool → Nat → AtomicAccessOutcome :=
  fun tb idx => lmExpectedOutcome (AtomicMemoryMode.ofLmTreeBorrows tb) idx

theorem lmObsWitness_check : lmAuthorityCheck lmObsWitness = true := by decide +kernel

/-- A concrete `AtomicDualContract`. -/
def witnessContract : AtomicDualContract :=
  atomicDualContractOfCheck lmObsWitness lmObsWitness_check

theorem witness_cas_grounding (m : AtomicMemoryMode) :
    (witnessContract.lm.observe m.toLmTreeBorrows 8 = .okCas 5 true 9 ∧
      CasHistStep (· ≤ ·) (witnessContract.lm.observe m.toLmTreeBorrows 8)) ∧
    (witnessContract.lm.observe m.toLmTreeBorrows 9 = .okCas 5 false 5 ∧
      CasHistStep (· ≤ ·) (witnessContract.lm.observe m.toLmTreeBorrows 9)) ∧
    casOldProjection (witnessContract.lm.observe m.toLmTreeBorrows 8) =
      casOldProjection (mrAtomicObserve m 8) :=
  contract_cas_hist_grounding witnessContract m AtomicHistInv.nat_le (by decide)

/-- LeanMiri-shaped threaded trace witness. -/
def lmTraceWitness : Bool → List AtomicAccessOutcome :=
  fun _ => [.okStore 5, .okScalar 5 8, .okCas 8 false 8, .okCas 8 true 9, .okScalar 9 9]

theorem lmTraceWitness_check : lmTraceAuthorityCheck lmTraceWitness = true := by
  unfold lmTraceAuthorityCheck
  rw [mrAtomicTrace_table, mrAtomicTrace_table]
  decide

/-- The threaded trace visits `5 → 8 → 8 (CAS✗) → 9 (CAS✓) → 9` in both modes. -/
theorem mrAtomicTrace_values (m : AtomicMemoryMode) :
    (mrAtomicTrace m).map outcomePost = [some 5, some 8, some 8, some 9, some 9] := by
  rw [mrAtomicTrace_table]; rfl

theorem dual_trace_monotone (m : AtomicMemoryMode) :
    TraceHist (· ≤ ·) none (mrAtomicTrace m) ∧
      TraceHist (· ≤ ·) none (lmTraceWitness m.toLmTreeBorrows) :=
  ⟨mrAtomicTrace_hist_monotone m, lmTrace_hist_monotone _ lmTraceWitness_check m⟩

/-- The trace is not monotone for the reversed order (non-vacuity of `TraceHist`). -/
theorem dual_trace_not_antitone (m : AtomicMemoryMode) :
    ¬ TraceHist (· ≥ ·) none (mrAtomicTrace m) := by
  rw [mrAtomicTrace_table]
  intro h
  have h2 := h.2.2.2.2.2.1 5 8 rfl rfl
  exact absurd h2 (by decide)

/-! ## 2. Negative Fail-Closed Canaries -/

/-! ### 2.1 Silent divergence -/

theorem spin_refutes_all (A : AtomicEnv Nat PUnit PUnit) (s : AtomicSt Nat PUnit PUnit)
    (Q : Except Nat Nat → AtomicSt Nat PUnit PUnit → Prop)
    (h : s.comm.shot_store = false) :
    ¬ Eventually (atomicHistWP A) (fun s => s.comm.shot_store = true) Q ITree.spin s ∧
      ¬ Until (atomicHistWP A) (fun _ => True) (fun s => s.comm.shot_store = true) Q
        ITree.spin s ∧
      ¬ InfOften (atomicHistWP A) CasAttempt Q ITree.spin s ∧
      ¬ BuchiSat (committerSpec A (· ≤ ·) 0 PUnit.unit PUnit.unit (.fresh 0)) ITree.spin
        false s ∧
      ¬ FairInfOften (atomicHistWP A) (fun _ _ _ _ => False) CasWon Q ITree.spin s := by
  have hT : ¬ s.comm.shot_store = true := by rw [h]; exact Bool.false_ne_true
  exact ⟨not_eventually_spin hT, not_until_spin hT, not_infOften_spin, not_buchiSat_spin,
    not_fairInfOften_spin⟩

/-! ### 2.2 Loops that stop accepting -/

/-- For every `k`, a loop that accepts `k` times then stutters refutes `InfOften`. -/
theorem stops_accepting_refutes_infOften (k : Nat) (Q : PEmpty.{1} → PUnit.{1} → Prop) :
    Always (obsIgnoreWP PUnit.{1} Bool) (fun _ => True) Q
        (divergingLoop finiteAcceptBody k) PUnit.unit ∧
      ¬ InfOften (obsIgnoreWP PUnit.{1} Bool) (fun i _ _ _ => i = ObsReq.emit true) Q
        (divergingLoop finiteAcceptBody k) PUnit.unit :=
  finiteAccept_always_and_not_infOften k Q

/-- `loop { load(); }`: a load-only stutter. -/
def loadStutter : ITree (AtomicCellE Nat) PEmpty.{1} :=
  ITree.iter (fun _ => ITree.vis aLoad (fun _ => ITree.ret (Sum.inl PUnit.unit))) PUnit.unit

theorem loadStutter_noAccept (Q : PEmpty.{1} → AtomicSt Nat PUnit PUnit → Prop)
    (s : AtomicSt Nat PUnit PUnit) :
    AlwaysStep (atomicBudgetWP ticketEnv) (fun i o s₀ s₁ => ¬ CasWon i o s₀ s₁)
      (fun r s₁ => ¬ Q r s₁) loadStutter s := by
  refine AlwaysStep.iter_invariant _ (fun _ _ => True) (fun _ s₀ _ => ?_) trivial
  refine (AlwaysStep.vis_iff _ _ _ _ _ _).2 ((budgetWP_load ticketEnv _ _).2 fun _ _ =>
    ⟨fun _ => ⟨fun h => h, (AlwaysStep.ret_iff _ _ _ _ _).2 trivial⟩,
      fun _ _ => ⟨fun h => h, (AlwaysStep.ret_iff _ _ _ _ _).2 trivial⟩⟩)

/--
**One commit, then stutter**: a ticket service that commits one ticket under
bounded contention and then only loads satisfies the one-shot `DWP` prefix but
refutes `InfOften CasWon`.
-/
theorem commit_once_then_stutter (s₀ : AtomicSt Nat PUnit PUnit)
    (hs : InitSt s₀.cell PUnit.unit PUnit.unit (.fresh s₀.cell) s₀)
    (Q : PEmpty.{1} → AtomicSt Nat PUnit PUnit → Prop) :
    ¬ InfOften (atomicBudgetWP ticketEnv) CasWon Q
      (tryUpdateLoop Nat >>= fun _ => loadStutter) s₀ :=
  not_infOften_of_dwp_then_no_accept
    (DWP.mono (fun _ s _ => loadStutter_noAccept Q s)
      (tryUpdate_dwp_ranked (ticket_pre s₀.cell) hs))

/-! ### 2.3 Broken history-invariant hypotheses -/

/-- A concrete state for the canaries. -/
def zeroSt : AtomicSt Nat PUnit PUnit := ⟨0, PUnit.unit, .fresh 0, 0, PUnit.unit, 0⟩

theorem canary_irreflexive :
    ¬ AtomicHistInv Nat (· < ·) ∧
      ¬ AlwaysStep (atomicHistWP strictEnv) (HistStep strictEnv (· < ·)) (fun _ _ => True)
        (tryUpdateLoop Nat) zeroSt :=
  irreflexive_breaks_zero_write zeroSt _

theorem canary_nontransitive :
    (BumpRel 0 1 ∧ BumpRel 1 2 ∧ ¬ BumpRel 0 2) ∧ ¬ AtomicHistInv Nat BumpRel ∧
      ¬ Always (atomicHistWP bumpEnv) (fun s => BumpRel 0 s.cell) (fun _ _ => True)
        (tryUpdateLoop Nat) zeroSt :=
  nontransitive_breaks_history zeroSt rfl _

theorem canary_broken_closure :
    (∀ x, onceSpec.pre 0 x) ∧ ¬ (∀ x f₂, onceSpec.hist_inv 0 f₂ → onceSpec.pre f₂ x) ∧
      ¬ DWLP (atomicHistWP onceEnv) (tryUpdateLoop Nat) (fun _ _ => True)
        (⟨0, 0, .fresh 0, 0, PUnit.unit, 0⟩ : AtomicSt Nat Nat PUnit) :=
  broken_closure_hist_inv _ rfl _

/-! ### 2.4 Unbounded contention: safe but not live -/

theorem canary_unbounded_contention :
    Always (atomicHistWP ticketEnv) (HistInvSt ticketEnv (· ≤ ·) 0 PUnit.unit)
        (CreusotPost ticketEnv (· ≤ ·) 0 PUnit.unit PUnit.unit (.fresh 0))
        (tryUpdateLoop Nat) zeroSt ∧
      DWLP (atomicHistWP ticketEnv) (tryUpdateLoop Nat)
        (CreusotPost ticketEnv (· ≤ ·) 0 PUnit.unit PUnit.unit (.fresh 0)) zeroSt ∧
      ¬ DWP (atomicHistWP ticketEnv) (tryUpdateLoop Nat)
        (CreusotPost ticketEnv (· ≤ ·) 0 PUnit.unit PUnit.unit (.fresh 0)) zeroSt ∧
      ¬ Eventually (atomicHistWP ticketEnv) (fun _ => False)
        (CreusotPost ticketEnv (· ≤ ·) 0 PUnit.unit PUnit.unit (.fresh 0))
        (tryUpdateLoop Nat) zeroSt :=
  unbounded_contention_safe_but_not_live zeroSt ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The same loop terminates once contention is bounded (separation witness). -/
theorem bounded_contention_terminates :
    DWP (atomicBudgetWP ticketEnv) (tryUpdateLoop Nat)
      (CreusotPost ticketEnv (· ≤ ·) 0 PUnit.unit PUnit.unit (.fresh 0)) zeroSt :=
  tryUpdate_dwp_ranked (ticket_pre 0) ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### 2.5 Operational admissibility rejections -/

theorem canary_admissible (m : AtomicMemoryMode) :
    ¬ AdmissibleAtomicStep (mrAtomicObserve m 17) ∧
      ¬ AdmissibleAtomicStep (mrAtomicObserve m 18) ∧
      ¬ AdmissibleAtomicStep (mrAtomicObserve m 19) ∧
      ¬ AdmissibleAtomicStep (mrAtomicObserve .basic 15) ∧
      ¬ AdmissibleAtomicStep (mrAtomicObserve .basic 16) ∧
      ¬ AdmissibleAtomicStep (mrAtomicObserve .treeBorrows 15) ∧
      ¬ AdmissibleAtomicStep (mrAtomicObserve .treeBorrows 16) ∧
      ¬ AdmissibleAtomicStep (mrAtomicObserve .treeBorrows 27) ∧
      ¬ AdmissibleAtomicStep (witnessContract.lm.observe true 27) ∧
      AdmissibleAtomicStep (mrAtomicObserve m 24) ∧
      AdmissibleAtomicStep (mrAtomicObserve .basic 27) := by
  have hb := admissible_fail_closed witnessContract .basic
  have ht := admissible_fail_closed witnessContract .treeBorrows
  have hm := admissible_fail_closed witnessContract m
  exact ⟨hm.1, hm.2.1, hm.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.1.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem canary_frozen_trace :
    TraceHist (· ≤ ·) none (mrFrozenTrace .basic) ∧
      ¬ TraceHist (· ≤ ·) none (mrFrozenTrace .treeBorrows) :=
  mrFrozenTrace_mode_sensitive _

/-! ## 3. Compile-Time Kernel Axiom & Non-Vacuity Audit -/

section Audit

open Lean Elab Command Meta

/-- Standard axioms. -/
def auditStdAxiom (a : Name) : Bool :=
  a == ``propext || a == ``Classical.choice || a == ``Quot.sound

/-- Trivial theorem statements (`True`, `a = a`, `P ↔ P`), under binders. -/
def auditTrivialProp : Expr → Bool
  | .forallE _ _ body _ => auditTrivialProp body
  | .letE _ _ _ body _ => auditTrivialProp body
  | .mdata _ e => auditTrivialProp e
  | e =>
    if e.isConstOf ``True then true
    else if e.isAppOfArity ``Eq 3 then e.appFn!.appArg! == e.appArg!
    else if e.isAppOfArity ``Iff 2 then e.appFn!.appArg! == e.appArg!
    else false

/-- Axiom audit of one constant: only `propext`, `Classical.choice`, `Quot.sound`. -/
def auditAxioms (c : Name) (axs : Array Name) : Except String Unit := do
  for a in axs do
    if a == ``sorryAx then throw s!"{c} depends on sorryAx"
    if a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
      throw s!"{c} depends on compiler-trusting axiom {a}"
    unless auditStdAxiom a do throw s!"{c} depends on non-standard axiom {a}"

/-- Declaration-kind audit: safe definitions, non-trivial theorems, no axioms / opaques. -/
def auditKind (c : Name) (ci : ConstantInfo) : Except String Unit :=
  match ci with
  | .defnInfo v =>
    if v.safety == .safe then pure () else throw s!"{c} is not a safe definition"
  | .thmInfo v =>
    if auditTrivialProp v.type then throw s!"{c} is a trivial theorem" else pure ()
  | .axiomInfo _ => throw s!"{c} declares an axiom"
  | .opaqueInfo _ => throw s!"{c} is an opaque constant"
  | _ => if ci.isUnsafe then throw s!"{c} is not safe" else pure ()

/-- Whether an audit result is a rejection. -/
def auditRejects (r : Except String Unit) : Bool :=
  match r with
  | .error _ => true
  | .ok () => false

/-- A scratch theorem declaration for auditor self-tests. -/
def auditThm (n : Name) (ty val : Expr) : Declaration :=
  .thmDecl { name := n, levelParams := [], type := ty, value := val }

/-- A scratch non-safe definition for auditor self-tests. -/
def auditUnsafeDef (n : Name) (ty val : Expr) : Declaration :=
  .defnDecl { name := n, levelParams := [], type := ty, value := val,
              hints := ReducibilityHints.opaque, safety := DefinitionSafety.unsafe }

run_cmd do
  let env ← getEnv
  let nss : Array Name :=
    #[`Anneal.ITreeBuchi, `Anneal.AtomicHistInv, `Anneal.ITreeBuchiAndAtomicHistInvTests]
  let floors : Array Nat := #[675, 150, 35]
  let userName (c : Name) : Name := (privateToUserName? c).getD c
  let decls := env.constants.fold (init := (#[] : Array (Name × ConstantInfo)))
    fun acc c ci => if nss.any (·.isPrefixOf (userName c)) then acc.push (c, ci) else acc
  let mut counts : Array Nat := #[0, 0, 0]
  for (c, ci) in decls do
    let axs ← liftCoreM <| collectAxioms c
    if let .error msg := auditAxioms c axs then throwError msg
    -- `coinductive_fixpoint` compilation emits code-generation auxiliaries named
    -- `*._unsafe_rec`; their kernel-checked safe counterparts are audited instead.
    unless c.getString! == "_unsafe_rec" do
      if let .error msg := auditKind c ci then throwError msg
    if let .thmInfo _ := ci then
      for h : i in [0:nss.size] do
        if nss[i].isPrefixOf (userName c) && !(userName c).isInternal then
          counts := counts.modify i (· + 1)
  for h : i in [0:nss.size] do
    if counts[i]! < floors[i]! then
      throwError "audit is vacuous for {nss[i]}: only {counts[i]!} theorems"
  -- Self-tests: the auditor must reject every forbidden axiom and trivial statement.
  for a in [``sorryAx, ``Lean.ofReduceBool, ``Lean.trustCompiler] do
    let axs ← liftCoreM <| collectAxioms a
    unless auditRejects (auditAxioms a axs) do
      throwError "audit self-test: {a} not rejected"
  if auditRejects (auditAxioms `ok #[``propext, ``Classical.choice, ``Quot.sound]) then
    throwError "audit self-test: standard axioms rejected"
  let saved ← getEnv
  let rejectsDecl (d : Declaration) (n : Name) : CommandElabM Bool := do
    liftCoreM <| addDecl d
    let ci ← getConstInfo n
    let axs ← liftCoreM <| collectAxioms n
    setEnv saved
    return auditRejects (auditAxioms n axs) || auditRejects (auditKind n ci)
  let natTy := mkConst ``Nat
  unless ← rejectsDecl (auditThm `auditSelfTest.trustCompilerUse (mkConst ``True)
      (mkConst ``Lean.trustCompiler)) `auditSelfTest.trustCompilerUse do
    throwError "audit self-test: theorem using Lean.trustCompiler accepted"
  let rbTy ← liftTermElabM <| inferType (mkConst ``Lean.ofReduceBool)
  unless ← rejectsDecl (auditThm `auditSelfTest.reduceBool rbTy (mkConst ``Lean.ofReduceBool))
      `auditSelfTest.reduceBool do
    throwError "audit self-test: theorem using Lean.ofReduceBool accepted"
  let oneEqOne := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 1) (mkNatLit 1)
  unless ← rejectsDecl (auditThm `auditSelfTest.oneEqOne oneEqOne
      (mkApp2 (mkConst ``Eq.refl [1]) natTy (mkNatLit 1))) `auditSelfTest.oneEqOne do
    throwError "audit self-test: trivial 1 = 1 accepted"
  unless ← rejectsDecl (auditThm `auditSelfTest.true (mkConst ``True) (mkConst ``True.intro))
      `auditSelfTest.true do
    throwError "audit self-test: trivial True accepted"
  unless ← rejectsDecl (auditUnsafeDef `auditSelfTest.unsafeDef natTy (mkNatLit 0))
      `auditSelfTest.unsafeDef do
    throwError "audit self-test: non-safe definition accepted"
  let pIff := mkForall `P .default (mkSort 0)
    (mkApp2 (mkConst ``Iff) (mkBVar 0) (mkBVar 0))
  let oneEqTwo := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 1) (mkNatLit 2)
  unless auditTrivialProp pIff && !auditTrivialProp oneEqTwo do
    throwError "audit self-test: trivial-statement detector failed"
  let some (.thmInfo safety) := env.find? ``Anneal.AtomicHistInv.tryUpdate_always_safety
    | throwError "audit: tryUpdate_always_safety missing"
  if auditTrivialProp safety.type then
    throwError "audit self-test: main safety theorem flagged trivial"
  logInfo m!"ITreeBuchi/AtomicHistInv audit: {decls.size} declarations, theorems \
    {nss.toList.zip counts.toList}, axioms ⊆ [propext, Classical.choice, Quot.sound], \
    all definitions safe, 0 trivial theorems, self-tests passed"

end Audit

end Anneal.ITreeBuchiAndAtomicHistInvTests
