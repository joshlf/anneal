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

/--
Two-state (`Bool`) protocol `BuchiSpec` automaton for `pingServer`:
`false` (idle) `--recv-->` `true` (pending) `--send(echo)-->` `false` (idle),
accepting strictly on echo responses from the pending state.
-/
def pingProtocolSpec (Q : PEmpty.{1} → PingSt → Prop) :
    BuchiSpec PingSt Bool PingE PEmpty.{1} where
  ewp := pingWP
  step q i _ s _ q' :=
    match i with
    | .call .recv => q = false ∧ q' = true
    | .call (.send m) => q = true ∧ q' = false ∧ m = s.lastReq
  accept q i _ s _ q' :=
    match i with
    | .call (.send m) => q = true ∧ q' = false ∧ m = s.lastReq
    | .call .recv => False
  inv q s :=
    (q = false → s.resps = s.reqs ∧ s.lastResp = s.lastReq) ∧
    (q = true → s.reqs = s.resps + 1)
  terminal _ r s := Q r s

/-- Non-trivial 2-state protocol automaton `BuchiSat` for `pingServer`. -/
theorem pingServer_protocol_buchiSat (Q : PEmpty.{1} → PingSt → Prop) :
    BuchiSat (pingProtocolSpec Q) pingServer false ⟨0, 0, 0, 0⟩ := by
  let spec := pingProtocolSpec Q
  refine (buchiSat_iff_infOften spec pingServer false ⟨0, 0, 0, 0⟩).2
    ⟨⟨fun _ => ⟨rfl, rfl⟩, fun h => Bool.noConfusion h⟩, ?_⟩
  refine InfOften.iter_progress (fun k => pingBody k >>= fun k' => ITree.ret (Sum.inl k'))
    (fun _ qs => qs.1 = false ∧ qs.2.resps = qs.2.reqs ∧ qs.2.lastResp = qs.2.lastReq)
    (fun k qs hqs => ?_) ⟨rfl, rfl, rfl⟩
  obtain ⟨q, s⟩ := qs
  obtain ⟨hq, hcnt, hlast⟩ := hqs
  dsimp only at hq hcnt hlast
  subst hq
  refine buchiProgress.bind ?_
  refine (buchiProgress.vis_iff _ _ _ _ _ _ _).2 ((BuchiSpec.monitorWP_wp _ _ _ _ _).2 fun n =>
    ⟨true, ⟨rfl, rfl⟩,
      ⟨fun h => Bool.noConfusion h, fun _ => by show s.reqs + 1 = s.resps + 1; omega⟩, Or.inr ?_⟩)
  refine (buchiProgress.vis_iff _ _ _ _ _ _ _).2 ((BuchiSpec.monitorWP_wp _ _ _ _ _).2
    ⟨false, ⟨rfl, rfl, rfl⟩,
      ⟨fun _ => ⟨by show s.resps + 1 = s.reqs + 1; omega, rfl⟩, fun h => Bool.noConfusion h⟩,
      Or.inl ⟨⟨rfl, rfl, rfl⟩, ?_⟩⟩)
  rw [ret_bind]
  exact InfOften.ret ⟨rfl, by show s.resps + 1 = s.reqs + 1; omega, rfl⟩

/-! ### 1.2 Monotone `AtomicU64::try_update` counter (`Nat` + `UInt64` + prophetic `resolve`) -/

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
  closure_pre _ _ _ _ := trivial
  closure_step _ x _ n _ h _ := by
    obtain ⟨_, hr⟩ := h
    by_cases hx : x < limit
    · simp only [hx, ↓reduceIte] at hr; cases hr; exact ⟨Nat.le_add_right x delta, trivial⟩
    · simp only [hx, ↓reduceIte] at hr; cases hr
  rely_sound _ _ h := h
  comm_unshot := rfl

theorem counter_realizable (delta limit : Nat) : (counterEnv delta limit).Realizable where
  rely_refl := Nat.le_refl
  post_mut_total a x _ := ⟨a + 1, if x < limit then some (x + delta) else none, rfl, rfl⟩
  gc_post_total g e d _ := ⟨g ++ [(e, d)], rfl⟩
  resolve_total _ := trivial

/-- Concrete initial state: cell `5`, no attempts, fresh committer, empty log. -/
def counterSt₀ (budget : Nat) : AtomicSt Nat Nat (List (Nat × Nat)) :=
  ⟨5, 0, .fresh 5, 0, [], budget⟩

theorem counterSt₀_init (b : Nat) : InitSt 5 0 [] (.fresh 5) (counterSt₀ b) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Safety under arbitrary contention** (`Always` + `AlwaysStep` + `DWLP`). -/
theorem counter_safe (delta limit b : Nat) :
    Always (atomicHistWP (counterEnv delta limit))
        (HistInvSt (counterEnv delta limit) (· ≤ ·) 5 0)
        (CreusotPost (counterEnv delta limit) (· ≤ ·) 5 0 [] (.fresh 5))
        (tryUpdateLoop Nat) (counterSt₀ b) ∧
      AlwaysStep (atomicHistWP (counterEnv delta limit)) (HistStep (counterEnv delta limit) (· ≤ ·))
        (CreusotPost (counterEnv delta limit) (· ≤ ·) 5 0 [] (.fresh 5))
        (tryUpdateLoop Nat) (counterSt₀ b) ∧
      DWLP (guardInvWP (atomicHistWP (counterEnv delta limit))
          (HistInvSt (counterEnv delta limit) (· ≤ ·) 5 0)) (tryUpdateLoop Nat)
        (fun r s => HistInvSt (counterEnv delta limit) (· ≤ ·) 5 0 s ∧
          CreusotPost (counterEnv delta limit) (· ≤ ·) 5 0 [] (.fresh 5) r s) (counterSt₀ b) :=
  ⟨tryUpdate_always_safety (counter_pre _ _ _ _ _) (counterSt₀_init b),
   tryUpdate_alwaysStep_safety (counter_pre _ _ _ _ _) (counterSt₀_init b),
   tryUpdate_dwlp_creusot_spec (counter_pre _ _ _ _ _) (counterSt₀_init b)⟩

/-- What the `creusot#2386` postcondition means for the counter (allowing post-commit rely). -/
def CounterOutcome (delta limit : Nat) :
    Except Nat Nat → AtomicSt Nat Nat (List (Nat × Nat)) → Prop
  | .ok old, s => 5 ≤ old ∧ old < limit ∧ s.comm.val_load = old ∧
      s.comm.val_store = old + delta ∧ old + delta ≤ s.cell ∧
      s.gst = [(old, old + delta)] ∧ 1 ≤ s.fst ∧ s.comm.shot_store = true ∧ s.fires = 1
  | .error cur, s => 5 ≤ cur ∧ limit ≤ cur ∧ cur ≤ s.cell ∧ s.gst = [] ∧ 1 ≤ s.fst ∧
      s.comm.shot_store = false ∧ s.fires = 0

theorem counter_post_meaning (delta limit : Nat) (r : Except Nat Nat)
    (s : AtomicSt Nat Nat (List (Nat × Nat)))
    (h : CreusotPost (counterEnv delta limit) (· ≤ ·) 5 0 [] (.fresh 5) r s) :
    CounterOutcome delta limit r s := by
  cases r with
  | ok old =>
    obtain ⟨new, f₂, f₃, _, ⟨hf₃, hr⟩, _, hio, _, hnc, _, hfst, _, hshot, hvl, hvs, hfires, hg⟩ := h
    by_cases hx : old < limit
    · simp only [hx, ↓reduceIte] at hr; cases hr
      exact ⟨hio, hx, hvl, hvs, hnc, hg, by rw [hfst, hf₃]; omega, hshot, hfires⟩
    · simp only [hx, ↓reduceIte] at hr; cases hr
  | error cur =>
    obtain ⟨f₂, f₃, _, ⟨hf₃, hr⟩, _, hio, hcc, _, hfst, _, hshot, hfires, hg⟩ := h
    by_cases hx : cur < limit
    · simp only [hx, ↓reduceIte] at hr; cases hr
    · exact ⟨hio, by omega, hcc, hg, by rw [hfst, hf₃]; omega, hshot, hfires⟩

/--
**Liveness under bounded contention** (`DWP` + `Eventually` + `Always` + non-vacuity):
the counter returns `Ok old` with committed `val_store = old + delta` and ghost
log `[(old, old + delta)]`, or `Err cur` at saturation `limit ≤ cur`, and cannot
vacuously satisfy `DWP ... False`.
-/
theorem counter_live (delta limit b : Nat) :
    DWP (atomicBudgetWP (counterEnv delta limit)) (tryUpdateLoop Nat)
        (CounterOutcome delta limit) (counterSt₀ b) ∧
      Eventually (atomicBudgetWP (counterEnv delta limit)) (fun s => s.comm.shot_store = true)
        (CounterOutcome delta limit) (tryUpdateLoop Nat) (counterSt₀ b) ∧
      Always (atomicBudgetWP (counterEnv delta limit))
        (HistInvSt (counterEnv delta limit) (· ≤ ·) 5 0)
        (CreusotPost (counterEnv delta limit) (· ≤ ·) 5 0 [] (.fresh 5))
        (tryUpdateLoop Nat) (counterSt₀ b) ∧
      ¬ DWP (atomicBudgetWP (counterEnv delta limit)) (tryUpdateLoop Nat)
        (fun _ _ => False) (counterSt₀ b) := by
  have hb := tryUpdate_bounded_spec (counter_pre delta limit 5 0 []) (counterSt₀_init b)
  have h := DWP.mono (counter_post_meaning delta limit)
    (tryUpdate_dwp_ranked (counter_pre _ _ _ _ _) (counterSt₀_init b))
  exact ⟨h, eventually_of_dwp _ h, hb.1,
    (tryUpdate_nonvacuous_not_false (counter_realizable delta limit) (counterSt₀ b)).1⟩

/-- **`u64` width boundary**: below `limit` with `limit + delta ≤ 2^64` no commit overflows. -/
theorem counter_no_u64_overflow (delta limit : Nat) (hw : limit + delta ≤ u64Max + 1)
    (old : Nat) (s : AtomicSt Nat Nat (List (Nat × Nat)))
    (h : CounterOutcome delta limit (.ok old) s) : s.comm.val_store ≤ u64Max := by
  obtain ⟨_, hlt, _, hvs, _⟩ := h
  rw [hvs]; omega

/--
**Genuine `UInt64` counter with Creusot prophetic `&mut Nat` retry counter**:
`FState = Nat × Nat` represents `(current_attempts, final_prophecy)` with
`hist_inv (c₁, f₁) (c₂, f₂) := c₁ ≤ c₂ ∧ f₁ = f₂` and non-trivial prophetic
`resolve (c, f) := c = f`.
-/
def u64PropheticSpec (delta limit : UInt64) : FnMutSpec (Nat × Nat) UInt64 UInt64 where
  hist_inv p q := p.1 ≤ q.1 ∧ p.2 = q.2
  hist_inv_laws := ⟨fun _ => ⟨Nat.le_refl _, rfl⟩,
    fun hab hbc => ⟨Nat.le_trans hab.1 hbc.1, hab.2.trans hbc.2⟩⟩
  pre _ _ := True
  post_mut p x q r := q.1 = p.1 + 1 ∧ q.2 = p.2 ∧
    r = (if x.toNat < limit.toNat then some (x + delta) else none)
  step_hist_inv _ _ _ _ h := ⟨h.1 ▸ Nat.le_succ _, h.2.1.symm⟩
  resolve p := p.1 = p.2

def u64LogGC : GhostCommit UInt64 (List (UInt64 × UInt64)) :=
  ⟨fun _ _ _ => True, fun g o n g' => g' = g ++ [(o, n)]⟩

def u64CounterEnv (delta limit : UInt64) :
    AtomicEnv UInt64 (Nat × Nat) (List (UInt64 × UInt64)) :=
  ⟨fun a b => a.toNat ≤ b.toNat, u64PropheticSpec delta limit, u64LogGC⟩

theorem u64Counter_pre (delta limit init : UInt64) (hno : limit.toNat + delta.toNat ≤ UInt64.size)
    (fin : Nat) :
    TryUpdatePre (u64CounterEnv delta limit) (fun a b => a.toNat ≤ b.toNat)
      init (0, fin) [] (.fresh init) where
  cellInv := AtomicHistInv.u64_le
  closure_pre _ _ _ _ := trivial
  closure_step _ x _ n _ h _ := by
    obtain ⟨_, _, hr⟩ := h
    by_cases hx : x.toNat < limit.toNat
    · simp only [hx, ↓reduceIte] at hr; cases hr
      exact ⟨(AtomicHistInv.u64_add_preserves x delta (by omega)).2, trivial⟩
    · simp only [hx, ↓reduceIte] at hr; cases hr
  rely_sound _ _ h := h
  comm_unshot := rfl

/--
**Genuine `AtomicU64` + prophetic `&mut` `resolve` witness**: proves both
`Always` safety and bounded-contention `DWP`, and derives from `CreusotPost`
that the prophetic final borrow value `^attempts` equals the actual attempt
count (`s.fst.2 = s.fst.1 ∧ 1 ≤ s.fst.2`), with `UInt64` non-overflowing
addition (`u64_add_preserves`).
-/
theorem u64_counter_prophetic_spec (delta limit init : UInt64)
    (hno : limit.toNat + delta.toNat ≤ UInt64.size) (fin b : Nat) :
    let s₀ : AtomicSt UInt64 (Nat × Nat) (List (UInt64 × UInt64)) :=
      ⟨init, (0, fin), .fresh init, 0, [], b⟩
    Always (atomicHistWP (u64CounterEnv delta limit))
        (HistInvSt (u64CounterEnv delta limit) (fun a b => a.toNat ≤ b.toNat) init (0, fin))
        (CreusotPost (u64CounterEnv delta limit) (fun a b => a.toNat ≤ b.toNat)
          init (0, fin) [] (.fresh init))
        (tryUpdateLoop UInt64) s₀ ∧
      DWP (atomicBudgetWP (u64CounterEnv delta limit)) (tryUpdateLoop UInt64)
        (fun r s => s.fst.1 = s.fst.2 ∧ 1 ≤ s.fst.2 ∧ s.fst.2 = fin ∧
          match r with
          | .ok old => old.toNat < limit.toNat ∧
              s.comm.val_store.toNat = old.toNat + delta.toNat ∧ s.comm.shot_store = true
          | .error cur => limit.toNat ≤ cur.toNat ∧ s.comm.shot_store = false) s₀ := by
  intro s₀
  have hpre := u64Counter_pre delta limit init hno fin
  have hs₀ : InitSt init (0, fin) [] (.fresh init) s₀ := ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨tryUpdate_always_safety hpre hs₀, DWP.mono ?_ (tryUpdate_dwp_ranked hpre hs₀)⟩
  intro r s hr
  cases r with
  | ok old =>
    obtain ⟨new, f₂, f₃, hinv, ⟨hc3, hf3, hret⟩, hres, _, _, _, _, hfst, _, hshot, _, hvs, _, _⟩ :=
      hr
    by_cases hx : old.toNat < limit.toNat
    · simp only [hx, ↓reduceIte] at hret; cases hret
      have hfin : f₃.2 = fin := hf3.trans hinv.2.symm
      refine ⟨hfst ▸ hres, ?_, hfst ▸ hfin, hx, ?_, hshot⟩
      · have h1 : f₃.1 = f₃.2 := hres
        rw [hfst]; omega
      · rw [hvs]; exact (AtomicHistInv.u64_add_preserves old delta (by omega)).1
    · simp only [hx, ↓reduceIte] at hret; cases hret
  | error cur =>
    obtain ⟨f₂, f₃, hinv, ⟨hc3, hf3, hret⟩, hres, _, _, _, hfst, _, hshot, _, _⟩ := hr
    by_cases hx : cur.toNat < limit.toNat
    · simp only [hx, ↓reduceIte] at hret; cases hret
    · have hfin : f₃.2 = fin := hf3.trans hinv.2.symm
      refine ⟨hfst ▸ hres, ?_, hfst ▸ hfin, Nat.le_of_not_lt hx, hshot⟩
      have h1 : f₃.1 = f₃.2 := hres
      rw [hfst]; omega

/-- Bitmask-monotone flags (`BitsMono`) and ABA-free `Versioned` combinator witnesses. -/
theorem combinator_flags_and_versioned_witness :
    (AtomicHistInv.BitsMono 0b0010 (0b0010 ||| 0b0101) ∧
      AtomicHistInv.BitsMono 0b0010 ((0b0010 ||| 0b0101) ||| 0b1000)) ∧
    (∀ (p₁ p₂ : String), AtomicHistInv.Versioned (1, p₁) (2, p₂) ∧
      (AtomicHistInv.Versioned (1, p₁) (1, p₂) → p₁ = p₂)) := by
  refine ⟨⟨(AtomicHistInv.bitsMono_iff_exists_mask _ _).2 ⟨0b0101, rfl⟩,
    AtomicHistInv.bitsMono.trans
      ((AtomicHistInv.bitsMono_iff_exists_mask _ _).2 ⟨0b0101, rfl⟩)
      ((AtomicHistInv.bitsMono_iff_exists_mask _ _).2 ⟨0b1000, rfl⟩)⟩,
    fun p₁ p₂ => ⟨Or.inl (Nat.lt_succ_self 1), fun hv =>
      congrArg Prod.snd (AtomicHistInv.versioned_no_aba hv rfl)⟩⟩

/-! ### 1.3 Operational Strong-Fairness `EnvStrategy` & `#4162` Ticket Service Witnesses -/

/-- Count how many `cas` attempts have already appeared in a trace. -/
def casCount : List (Event (AtomicCellE Nat)) → Nat
  | [] => 0
  | ⟨.call (.cas _ _), _⟩ :: rest => casCount rest + 1
  | _ :: rest => casCount rest

/--
Concrete deterministic environment strategy: answers `load` with `0`, `callF x`
with `some (x + 1)`, fails the first `k` CAS attempts with `(false, e)`, and
lets the `(k + 1)`-th CAS win with `(true, e)`.
-/
def failKThenWinStrat (k : Nat) : EnvStrategy (AtomicCellE Nat) :=
  fun tr i _ =>
    match i with
    | .call .load => (0 : Nat)
    | .call (.cas e _) => (decide (k ≤ casCount tr), e)
    | .call (.callF x) => some (x + 1)
    | .call .dropF => PUnit.unit
    | .call .recv => PUnit.unit

private theorem reachesWithStrategy_last_eq {E : Effect.{0}} {R : Type} [FaultEffect E]
    {σ : EnvStrategy E} {hist tr : List (Event E)} {t u : ITree E R}
    (hr : ReachesWithStrategy σ hist t tr u) :
    ∀ {pre : List (Event E)} {ev : Event E}, tr = pre ++ [ev] →
      ∃ hnf, ev.ans = σ (hist ++ pre) ev.req hnf := by
  induction hr with
  | refl => intro pre ev h; cases pre <;> cases h
  | tau _ _ ih => exact ih
  | @vis hist tr' _ _ i _ _ hnf _ ih =>
    intro pre ev h
    cases pre with
    | nil =>
      cases h; exact ⟨hnf, by simp⟩
    | cons a rest =>
      cases h
      simpa [List.append_assoc] using ih rfl

private theorem casCount_append (l₁ l₂ : List (Event (AtomicCellE Nat))) :
    casCount (l₁ ++ l₂) = casCount l₁ + casCount l₂ := by
  induction l₁ with
  | nil => simp [casCount]
  | cons ev rest ih =>
    rcases ev with ⟨req, ans⟩
    cases req with
    | call r =>
      cases r <;> simp [casCount, ih] <;> omega

private theorem casCount_prefix_mono (ev : Stream' (Event (AtomicCellE Nat))) :
    ∀ {a b : Nat}, a ≤ b → casCount (takePrefix ev a) ≤ casCount (takePrefix ev b) := by
  intro a b hab
  induction hab with
  | refl => exact Nat.le_refl _
  | @step m _ ih =>
    rw [takePrefix_succ, casCount_append]
    omega

private theorem casCount_prefix_inc_at_cas (ev : Stream' (Event (AtomicCellE Nat))) (n : Nat)
    (h : CasAttempt (ev n).req (ev n).ans (takePrefix ev n) (takePrefix ev (n + 1))) :
    casCount (takePrefix ev n) + 1 ≤ casCount (takePrefix ev (n + 1)) := by
  rw [takePrefix_succ, casCount_append]
  rcases hev : ev n with ⟨req, ans⟩
  rw [hev] at h
  cases req with
  | call r =>
    cases r with
    | cas e d => simp [casCount]
    | _ => exact False.elim h

private theorem casCount_unbounded_of_infOften (ev : Stream' (Event (AtomicCellE Nat)))
    (h : ∀ m, ∃ n, m ≤ n ∧
      CasAttempt (ev n).req (ev n).ans (takePrefix ev n) (takePrefix ev (n + 1))) :
    ∀ c, ∃ n, c ≤ casCount (takePrefix ev n) := by
  intro c
  induction c with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ c ih =>
    obtain ⟨n₀, hn₀⟩ := ih
    obtain ⟨n₁, hle, hatt⟩ := h n₀
    refine ⟨n₁ + 1, ?_⟩
    have h1 := casCount_prefix_mono ev hle
    have h2 := casCount_prefix_inc_at_cas ev n₁ hatt
    omega

private theorem failKThenWinStrat_cas_wins (k : Nat) (ev : Stream' (Event (AtomicCellE Nat)))
    (hrun : InfRunWithStrategy (failKThenWinStrat k) [] (tryUpdateLoop Nat) ev) (n : Nat)
    (hk : k ≤ casCount (takePrefix ev n))
    (hatt : CasAttempt (ev n).req (ev n).ans (takePrefix ev n) (takePrefix ev (n + 1))) :
    CasWon (ev n).req (ev n).ans (takePrefix ev n) (takePrefix ev (n + 1)) := by
  obtain ⟨u, hreach⟩ := hrun (n + 1)
  obtain ⟨hnf, hans⟩ := reachesWithStrategy_last_eq hreach (takePrefix_succ ev n)
  rcases hev : ev n with ⟨req, ans⟩
  rw [hev] at hatt hans
  cases req with
  | call r =>
    cases r with
    | cas e d =>
      show (casAns e d ans).1 = true
      have hans' : ans = (decide (k ≤ casCount (takePrefix ev n)), e) := by
        simpa [failKThenWinStrat] using hans
      rw [hans']
      exact decide_eq_true hk
    | _ => exact False.elim hatt

/--
**Concrete operational termination witness (`tryUpdate_trace_strongFair_terminates`)**:
for every `k`, `failKThenWinStrat k` is strongly fair (after `k` retries every
subsequent CAS attempt wins), so `tryUpdateLoop` operationally reaches `.ret r`
with `TracePost r tr` (`cas✓; drop` or `f = None; drop`).
-/
theorem tryUpdate_concrete_strategy_terminates (k : Nat) :
    ∃ tr r, RetWithStrategy (failKThenWinStrat k) [] (tryUpdateLoop Nat) tr r ∧ TracePost r tr := by
  refine tryUpdate_trace_strongFair_terminates (failKThenWinStrat k) [] ?_
  intro ev hrun hinf m
  obtain ⟨n₀, hn₀⟩ := casCount_unbounded_of_infOften ev hinf k
  obtain ⟨n, hle, hatt⟩ := hinf (max m n₀)
  refine ⟨n, Nat.le_trans (Nat.le_max_left m n₀) hle, ?_⟩
  have hcnt := Nat.le_trans hn₀ (casCount_prefix_mono ev (Nat.le_trans (Nat.le_max_right m n₀) hle))
  exact failKThenWinStrat_cas_wins k ev hrun n hcnt hatt

/-- Concrete `#4162` reactive ticket service witness (`tryUpdate_reactive_service_infOften`). -/
theorem ticketService_concrete_witness (Q : PEmpty.{1} → AtomicSt Nat PUnit PUnit → Prop) :
    let s₀ : AtomicSt Nat PUnit PUnit := ⟨0, PUnit.unit, .fresh 0, 0, PUnit.unit, 0⟩
    Always (atomicBudgetWP ticketEnv) (SvcAlwaysInv 0) Q (ticketService 0) s₀ ∧
      InfOften (atomicBudgetWP ticketEnv) TicketCommit Q (ticketService 0) s₀ ∧
      ¬ DWP (atomicBudgetWP ticketEnv) (ticketService 0) Q s₀ :=
  tryUpdate_reactive_service_infOften 0 0 ⟨0, PUnit.unit, .fresh 0, 0, PUnit.unit, 0⟩
    ⟨Nat.le_refl 0, by decide, by simp⟩ Q

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
      casOldProjection (mrAtomicObserve m 8) ∧
    casOldProjection (witnessContract.lm.observe m.toLmTreeBorrows 9) =
      casOldProjection (mrAtomicObserve m 9) ∧
    casOldProjection (witnessContract.lm.observe m.toLmTreeBorrows 24) =
      casOldProjection (mrAtomicObserve m 24) ∧
    atomicOutcomeCodec.encode (mrAtomicObserve m 8) =
      atomicOutcomeCodec.encode (witnessContract.lm.observe m.toLmTreeBorrows 8) :=
  contract_cas_hist_grounding witnessContract m AtomicHistInv.nat_le (by decide)

theorem witness_all_widths_and_irreflexive_cas (m : AtomicMemoryMode) :
    (∀ idx, idx < 8 →
      AdmissibleAtomicStep (mrAtomicObserve m idx) ∧
        mrAtomicObserve m idx = witnessContract.lm.observe m.toLmTreeBorrows idx) ∧
    ¬ TraceHist (· < ·) (some 5) [mrAtomicObserve m 9] :=
  ⟨(mr_scalar_widths_admissible witnessContract m (Rel := (· ≤ ·)) (by decide)).1,
   mr_failing_cas_breaks_irreflexive m⟩

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
        (tryUpdateLoop Nat) zeroSt ∧
      ¬ AlwaysStep (atomicHistWP quiescentTicketEnv) (CasOnlyHistStep (· < ·)) (fun _ _ => True)
        (tryUpdateLoop Nat) zeroSt :=
  ⟨(irreflexive_breaks_zero_write zeroSt (fun _ _ => True)).1,
   (irreflexive_breaks_zero_write zeroSt (fun _ _ => True)).2,
   (irreflexive_breaks_failed_cas zeroSt (fun _ _ => True)).2⟩

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

theorem canary_double_fire_committer :
    ¬ DWLP (atomicHistWP ticketEnv) doubleTryUpdate (fun _ _ => True) zeroSt :=
  double_cas_violates_oneshot_committer zeroSt _

theorem canary_weak_vs_strong_cas :
    DWP (atomicStrongHistWP quiescentTicketEnv) (tryUpdateLoop Nat)
        (CreusotPost quiescentTicketEnv (· ≤ ·) 0 PUnit.unit PUnit.unit (.fresh 0)) zeroSt ∧
      ¬ DWP (atomicHistWP quiescentTicketEnv) (tryUpdateLoop Nat)
        (CreusotPost quiescentTicketEnv (· ≤ ·) 0 PUnit.unit PUnit.unit (.fresh 0)) zeroSt ∧
      Always (atomicStrongHistWP ticketEnv) (HistInvSt ticketEnv (· ≤ ·) 0 PUnit.unit)
        (CreusotPost ticketEnv (· ≤ ·) 0 PUnit.unit PUnit.unit (.fresh 0))
        (tryUpdateLoop Nat) zeroSt ∧
      ¬ DWP (atomicStrongHistWP ticketEnv) (tryUpdateLoop Nat)
        (CreusotPost ticketEnv (· ≤ ·) 0 PUnit.unit PUnit.unit (.fresh 0)) zeroSt :=
  weak_vs_strong_cas_separation zeroSt ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem canary_unrealizable_resolve_miracle :
    ¬ falseResolveEnv.Realizable ∧
      DWP (atomicBudgetWP falseResolveEnv) (tryUpdateLoop Nat) (fun _ _ => False) zeroSt ∧
      ¬ DWP (atomicBudgetWP ticketEnv) (tryUpdateLoop Nat) (fun _ _ => False) zeroSt :=
  ⟨(unrealizable_resolve_miracle zeroSt).1,
   (unrealizable_resolve_miracle zeroSt).2,
   (tryUpdate_nonvacuous_not_false ticketEnv_realizable zeroSt).1⟩

theorem canary_mrCellWP_ub :
    let s₅ : AtomicSt Nat PUnit PUnit := ⟨5, PUnit.unit, .fresh 5, 0, PUnit.unit, 0⟩
    ¬ DWLP (mrCellWP ticketEnv (MiniRustSpec.AtomicIntrinsicsMR.bmPtr 1)
        MiniRustSpec.AtomicIntrinsicsMR.tyRawPtr MiniRustSpec.AtomicIntrinsicsMR.itU32 Eq)
        (tryUpdateLoop Nat) (fun _ _ => True) (MiniRustSpec.AtomicIntrinsicsMR.bmFive, s₅) ∧
    ¬ DWLP (mrCellWP ticketEnv MiniRustSpec.AtomicIntrinsicsMR.bmPtr
        MiniRustSpec.AtomicIntrinsicsMR.tyRawPtr MiniRustSpec.AtomicIntrinsicsMR.itU128 Eq)
        (tryUpdateLoop Nat) (fun _ _ => True) (MiniRustSpec.AtomicIntrinsicsMR.bmFive, s₅) ∧
    ¬ DWLP (mrCellWP ticketEnv MiniRustSpec.AtomicIntrinsicsMR.tbSharedPtr
        MiniRustSpec.AtomicIntrinsicsMR.tyRawPtr MiniRustSpec.AtomicIntrinsicsMR.itU32 Eq)
        (tryUpdateLoop Nat) (fun _ _ => True) (MiniRustSpec.AtomicIntrinsicsMR.tbShared, s₅) :=
  mrCellWP_rejects_misaligned_u128_frozen ⟨5, PUnit.unit, .fresh 5, 0, PUnit.unit, 0⟩ rfl _ _

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

/--
Declaration-kind audit with tightened `_unsafe_rec` gating:
only Lean's equation-compiler `._unsafe_rec` (`.partial`, never `.unsafe`, with
a kernel-checked `.safe` parent definition `c.getPrefix` in `env`) is exempted.
-/
def auditKindStrict (env : Environment) (c : Name) (ci : ConstantInfo) : Except String Unit :=
  match ci with
  | .defnInfo v =>
    if v.safety == .safe then pure ()
    else if c.getString! == "_unsafe_rec" && v.safety == .partial then
      match env.find? c.getPrefix with
      | some (.defnInfo pv) =>
        if pv.safety == .safe then pure ()
        else throw s!"{c} is _unsafe_rec whose parent {c.getPrefix} is not safe"
      | _ => throw s!"{c} is an orphan _unsafe_rec without a safe parent definition"
    else throw s!"{c} is not a safe definition (safety={repr v.safety})"
  | .thmInfo v =>
    if auditTrivialProp v.type then throw s!"{c} is a trivial theorem"
    else if (v.type.getUsedConstants ++ v.value.getUsedConstants).any
        (·.getString! == "_unsafe_rec") then
      throw s!"{c} references an _unsafe_rec constant"
    else pure ()
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
def auditDef (n : Name) (ty val : Expr) (safety : DefinitionSafety) : Declaration :=
  .defnDecl { name := n, levelParams := [], type := ty, value := val,
              hints := ReducibilityHints.opaque, safety := safety }

run_cmd do
  let env ← getEnv
  -- Import-isolation check on `Anneal.AtomicHistInv`: no `Lean`, `Miri.*`, or `LeanMiriSpec.*`.
  let some ahiIdx := env.getModuleIdx? `Anneal.AtomicHistInv
    | throwError "audit: module Anneal.AtomicHistInv not found in environment"
  let ahiMod := env.header.moduleData[ahiIdx.toNat]!
  for imp in ahiMod.imports do
    if imp.module == `Lean || (`Lean).isPrefixOf imp.module ||
       (`Miri).isPrefixOf imp.module || (`LeanMiriSpec).isPrefixOf imp.module then
      throwError "import-isolation violation: Anneal.AtomicHistInv imports {imp.module}"
  let nss : Array Name :=
    #[`Anneal.ITreeBuchi, `Anneal.AtomicHistInv, `Anneal.ITreeBuchiAndAtomicHistInvTests]
  let floors : Array Nat := #[675, 195, 65]
  let userName (c : Name) : Name := (privateToUserName? c).getD c
  let decls := env.constants.fold (init := (#[] : Array (Name × ConstantInfo)))
    fun acc c ci => if nss.any (·.isPrefixOf (userName c)) then acc.push (c, ci) else acc
  let mut counts : Array Nat := #[0, 0, 0]
  for (c, ci) in decls do
    let axs ← liftCoreM <| collectAxioms c
    if let .error msg := auditAxioms c axs then throwError msg
    if let .error msg := auditKindStrict env c ci then throwError msg
    if let .thmInfo _ := ci then
      for h : i in [0:nss.size] do
        if nss[i].isPrefixOf (userName c) && !(userName c).isInternal then
          counts := counts.modify i (· + 1)
  for h : i in [0:nss.size] do
    if counts[i]! < floors[i]! then
      throwError "audit is vacuous for {nss[i]}: only {counts[i]!} theorems"
  -- Verify all flagship Episode 2 theorems are present and non-trivial.
  let requiredThms : List Name :=
    [ ``Anneal.AtomicHistInv.tryUpdate_always_safety
    , ``Anneal.AtomicHistInv.tryUpdate_dwlp_creusot_spec
    , ``Anneal.AtomicHistInv.tryUpdate_alwaysStep_safety
    , ``Anneal.AtomicHistInv.tryUpdate_dwp_ranked
    , ``Anneal.AtomicHistInv.tryUpdate_strong_quiescent_dwp
    , ``Anneal.AtomicHistInv.tryUpdate_nonvacuous_not_false
    , ``Anneal.AtomicHistInv.tryUpdate_fairInfOften
    , ``Anneal.AtomicHistInv.tryUpdate_fairBuchiSat_committer
    , ``Anneal.AtomicHistInv.tryUpdate_trace_strongFair_terminates
    , ``Anneal.AtomicHistInv.tryUpdate_reactive_service_infOften
    , ``Anneal.AtomicHistInv.mr_scalar_widths_admissible
    , ``Anneal.AtomicHistInv.mr_cas_success_transition
    , ``Anneal.AtomicHistInv.mr_cas_failure_preserves_memory_and_no_race
    , ``Anneal.AtomicHistInv.mr_atomic_tb_preserves_wfLive
    , ``Anneal.AtomicHistInv.tryUpdate_mr_tb_wfLive_safety
    , ``Anneal.AtomicHistInv.mrCellWP_rejects_misaligned_u128_frozen
    , ``Anneal.AtomicHistInv.double_cas_violates_oneshot_committer
    , ``Anneal.AtomicHistInv.weak_vs_strong_cas_separation
    , ``Anneal.AtomicHistInv.unrealizable_resolve_miracle ]
  for req in requiredThms do
    let some (.thmInfo ti) := env.find? req
      | throwError "audit: required theorem {req} missing"
    if auditTrivialProp ti.type then
      throwError "audit: required theorem {req} flagged trivial"
  -- Self-tests: the auditor must reject every forbidden axiom, declaration kind, and forgery.
  for a in [``sorryAx, ``Lean.ofReduceBool, ``Lean.trustCompiler] do
    let axs ← liftCoreM <| collectAxioms a
    unless auditRejects (auditAxioms a axs) do
      throwError "audit self-test: {a} not rejected"
  if auditRejects (auditAxioms `ok #[``propext, ``Classical.choice, ``Quot.sound]) then
    throwError "audit self-test: standard axioms rejected"
  let saved ← getEnv
  let rejectsDecl (d : Declaration) (n : Name) : CommandElabM Bool := do
    let newEnv ← ofExceptKernelException (saved.addDeclCore 0 0 d none)
    setEnv newEnv
    let ci ← getConstInfo n
    let axs ← liftCoreM <| collectAxioms n
    setEnv saved
    return auditRejects (auditAxioms n axs) || auditRejects (auditKindStrict newEnv n ci)
  let natTy := mkConst ``Nat
  let oneEqTwo := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 1) (mkNatLit 2)
  let sorryProof := mkApp2 (mkConst ``sorryAx [0]) oneEqTwo (mkConst ``Bool.false)
  unless ← rejectsDecl (auditThm `auditSelfTest.sorryThm oneEqTwo sorryProof)
      `auditSelfTest.sorryThm do
    throwError "audit self-test: theorem using sorryAx accepted"
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
  let pIff := mkForall `P .default (mkSort 0)
    (mkApp2 (mkConst ``Iff) (mkBVar 0) (mkBVar 0))
  let pIffProof := mkLambda `P .default (mkSort 0) (mkApp (mkConst ``Iff.refl) (mkBVar 0))
  unless ← rejectsDecl (auditThm `auditSelfTest.pIffP pIff pIffProof)
      `auditSelfTest.pIffP do
    throwError "audit self-test: trivial P ↔ P accepted"
  unless ← rejectsDecl (auditDef `auditSelfTest.unsafeDef natTy (mkNatLit 0) .unsafe)
      `auditSelfTest.unsafeDef do
    throwError "audit self-test: unsafe definition accepted"
  unless ← rejectsDecl (auditDef `auditSelfTest.partialDef natTy (mkNatLit 0) .partial)
      `auditSelfTest.partialDef do
    throwError "audit self-test: partial definition accepted"
  let axDecl : Declaration := .axiomDecl
    { name := `auditSelfTest.customAxiom, levelParams := [], type := mkSort 0, isUnsafe := false }
  unless ← rejectsDecl axDecl `auditSelfTest.customAxiom do
    throwError "audit self-test: custom axiom accepted"
  let opqDecl : Declaration := .opaqueDecl
    { name := `auditSelfTest.opaqueConst, levelParams := [], type := natTy,
      value := mkNatLit 0, isUnsafe := false, all := [`auditSelfTest.opaqueConst] }
  unless ← rejectsDecl opqDecl `auditSelfTest.opaqueConst do
    throwError "audit self-test: opaque constant accepted"
  let forgedUnsafe := auditDef `Anneal.AtomicHistInv.forged._unsafe_rec natTy (mkNatLit 0) .unsafe
  unless ← rejectsDecl forgedUnsafe `Anneal.AtomicHistInv.forged._unsafe_rec do
    throwError "audit self-test: forged unsafe _unsafe_rec accepted"
  let orphanPartial := auditDef `Anneal.AtomicHistInv.orphan._unsafe_rec natTy (mkNatLit 0) .partial
  unless ← rejectsDecl orphanPartial `Anneal.AtomicHistInv.orphan._unsafe_rec do
    throwError "audit self-test: orphan partial _unsafe_rec without safe parent accepted"
  unless auditTrivialProp pIff && !auditTrivialProp oneEqTwo do
    throwError "audit self-test: trivial-statement detector failed"
  logInfo m!"ITreeBuchi/AtomicHistInv audit: {decls.size} declarations, theorems \
    {nss.toList.zip counts.toList}, import_isolated=true, axioms ⊆ [propext, Classical.choice, \
    Quot.sound], all definitions safe (strict _unsafe_rec check), 0 trivial theorems, \
    12 real addDecl self-tests passed"

end Audit

end Anneal.ITreeBuchiAndAtomicHistInvTests
