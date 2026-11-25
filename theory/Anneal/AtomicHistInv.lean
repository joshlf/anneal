-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.ITreeBuchi
import Anneal.Mir.AtomicIntrinsicsDualSpec

/-!
# `creusot#2386` `Atomic::try_update` with History Invariants (`Anneal.AtomicHistInv`)

A specification and verification library for `SeqCst` `Atomic::try_update` /
`fetch_update` CAS-retry contracts in the style of `creusot#2386`, layered on
`Anneal.ITreeBuchi` and grounded in `Anneal.Mir.AtomicIntrinsicsDualSpec`.

* **§1** History invariants: `AtomicHistInv` (reflexive + transitive) with
  combinators (`nat_le`, `nat_ge`, `eq`, `comap`, `prod`, `conj`, `u64_le`,
  `u64_add_preserves`, bitmask-monotone `bitsMono`, ABA-free `versioned`),
  `FnMutSpec` with `ClosureHistInv` `hist_inv`, the one-shot ghost
  `OneShotCommitter`, and the ghost callback `GhostCommit`.
* **§2** The `AtomicCellE` effect (`load`, `cas`, closure `callF` / `dropF`,
  service `recv`), the unbounded weak-CAS rely/history transformer
  `atomicHistWP` (enforcing one-shot `s.comm.shot_store = false` on commit and
  rely interference across `load`/`cas`/`dropF`), the strong-CAS transformer
  `atomicStrongHistWP`, the bounded-contention transformer `atomicBudgetWP`,
  refinements (`atomicHistWP_refines_budget`, `atomicHistWP_refines_strong`),
  and general `ExcludedMiracle` theorems under `AtomicEnv.Realizable`.
* **§3** `tryUpdateLoop` over `ITree.iter`, matching
  `while let Some(next) = f(prev) { compare_exchange_weak(prev, next) }`.
* **§4–5** The exact `creusot#2386` contract `CreusotPost` under `TryUpdatePre`
  (with concurrent post-commit/post-abort `rely` interference at `dropF`),
  proved as `Always` / `AlwaysStep` / `DWLP` safety under unbounded contention.
* **§6** Liveness & Prophecy Elimination: `DWP` / `Eventually` under bounded
  contention, unconditional strong-CAS termination under quiescence,
  non-vacuity (`¬ DWP ... False`), Streett `FairInfOften` / `CoBuchi` under CAS
  fairness, `InfOften` CAS enabledness, a one-shot committer `FairBuchiSat`
  monitor, operational termination against every strongly fair `EnvStrategy`
  (`trace_strongFair_terminates` over `eventTraceWP`), and non-miraculous
  prophecy elimination (`prophecy_elimination_dwp`, `prophecy_elimination_always`
  for `TerminalDrop` programs including `tryUpdateLoop`).
* **§7** A `#4162` diverging `-> !` ticket service composing `tryUpdateLoop`
  (`Always` with one-shot per-request committer + `InfOften TicketCommit` +
  `¬ DWP`, via `buchi_diverging_loop_rule`).
* **§8** Dual-authority & MiniRust grounding: all integer widths
  (`u8`/`u16`/`u32`/`u64`/`usize`), universal MiniRust CAS success/failure/
  frame/no-data-race/`MachTB.wfLive` laws, threaded traces, `AdmissibleAtomicStep`,
  and a direct `evalIntrinsicM`-backed transformer `mrCellWP` with coupled
  `MrCellAdmissible` (guarded by `IntType.can_represent`), general non-vacuity
  (`mrCellWP_nonvacuous_not_false`), fail-closed out-of-range `specPanic`
  (`mr_cas_out_of_range_specPanic_canary`), positive universal symbolic
  instances on both `Mach` (`bmU8_mrCellAdmissible`, `tryUpdate_mr_bm_u8_safety`)
  and `MachTB` (`tbU8_mrCellAdmissible`, `tryUpdate_mr_tb_u8_safety`,
  `tryUpdate_mr_tb_u8_fair`), full 8-byte little-endian `u64` symbolic
  instances on both `Mach` and `MachTB` (`leValue_leBytes`,
  `bmU64_mrCellAdmissible`, `tbU64_mrCellAdmissible`,
  `tryUpdate_mr_bm_u64_complete`, `tryUpdate_mr_tb_u64_complete`),
  machine-backed Streett liveness + enabledness + CoBuchi non-vacuity
  (`tryUpdate_mr_fairInfOften`, `tryUpdate_mr_infOften_attemptCas`,
  `tryUpdate_mr_tb_wfLive_fair`, `tryUpdate_mr_fairInfOften_nonvacuous`,
  `mrCellWP_loadStutter_cobuchi_vacuous`), bounded-contention unconditional
  machine termination (`mrBudgetWP`, `mrCellWP_refines_budget`,
  `tryUpdate_mr_dwp_ranked`, `tryUpdate_mr_eventually`,
  `tryUpdate_mr_tb_wfLive_dwp`, `mrBudgetWP_nonvacuous_not_false`),
  machine-level weak-vs-strong CAS 2-axis separation (`mrStrongCellWP`,
  `mrCellWP_refines_strong`, `mrStrongCellWP_nonvacuous_not_false`,
  `tryUpdate_mr_strong_quiescent_dwp`, `tryUpdate_mr_weak_quiescent_not_dwp`,
  `tryUpdate_mr_strong_contention_not_dwp`), machine-backed one-shot committer
  `FairBuchiSat` monitor (`mrCommitterSpec`, `tryUpdate_mr_fairBuchiSat_committer`),
  finite-width saturation canary (`mr_ticketService_overflow_canary`) and
  positive `#4162` 8-byte Tree Borrows wrapping `u64` service
  (`tryUpdate_mr_tb_u64_wrapping_service`), and fail-closed rejection of
  misaligned / `u128` / `Frozen` UB.
* **§9** Fail-closed boundaries: irreflexive relations (on both `Err` and failed
  CAS), non-transitive relations, non-`hist_inv`-closed closure preconditions,
  one-shot committer double-fire rejection, weak-vs-strong CAS 2-axis
  separation, unbounded contention, and unrealizable `resolve` miracle canary.
* **§10** `ep2_creusot_try_update_capstone`: safety, transition safety,
  bounded termination, Streett liveness + enabledness + committer monitor,
  strong-fairness operational termination, and dual-authority admissibility,
  all for the one program `tryUpdateLoop`.
-/

namespace Anneal.AtomicHistInv

open Trusted.Effect
open Trusted.ITree
open Anneal.Effect
open Anneal.ITree
open Anneal.EffectWP
open Anneal.ITreeWP
open Anneal.ITreeBuchi

universe u

/-! ## 1. History Invariants -/

/-- A reflexive, transitive history relation. -/
structure AtomicHistInv (Val : Type u) (Rel : Val → Val → Prop) : Prop where
  refl : ∀ v, Rel v v
  trans : ∀ {a b c : Val}, Rel a b → Rel b c → Rel a c

/-- The relation bundled by a history invariant. -/
abbrev AtomicHistInv.rel {Val : Type u} {Rel : Val → Val → Prop}
    (_ : AtomicHistInv Val Rel) : Val → Val → Prop := Rel

namespace AtomicHistInv

/-- Monotone counters: `old ≤ new`. -/
theorem nat_le : AtomicHistInv Nat (· ≤ ·) :=
  ⟨Nat.le_refl, Nat.le_trans⟩

/-- Monotonically decreasing counters: `new ≤ old`. -/
theorem nat_ge : AtomicHistInv Nat (· ≥ ·) :=
  ⟨Nat.le_refl, fun hab hbc => Nat.le_trans hbc hab⟩

/-- Constant cells: no update is ever observed. -/
theorem eq (Val : Type u) : AtomicHistInv Val (· = ·) :=
  ⟨fun _ => rfl, fun hab hbc => hab.trans hbc⟩

/-- Inverse image along a projection `f`. -/
theorem comap {α β : Type u} {R : β → β → Prop} (h : AtomicHistInv β R) (f : α → β) :
    AtomicHistInv α (fun a b => R (f a) (f b)) :=
  ⟨fun a => h.refl (f a), fun hab hbc => h.trans hab hbc⟩

/-- Componentwise product of two history invariants. -/
theorem prod {α β : Type u} {R : α → α → Prop} {S : β → β → Prop}
    (hR : AtomicHistInv α R) (hS : AtomicHistInv β S) :
    AtomicHistInv (α × β) (fun p q => R p.1 q.1 ∧ S p.2 q.2) :=
  ⟨fun p => ⟨hR.refl p.1, hS.refl p.2⟩,
   fun hab hbc => ⟨hR.trans hab.1 hbc.1, hS.trans hab.2 hbc.2⟩⟩

/-- Conjunction of two history invariants on the same carrier. -/
theorem conj {α : Type u} {R S : α → α → Prop}
    (hR : AtomicHistInv α R) (hS : AtomicHistInv α S) :
    AtomicHistInv α (fun a b => R a b ∧ S a b) :=
  ⟨fun a => ⟨hR.refl a, hS.refl a⟩,
   fun hab hbc => ⟨hR.trans hab.1 hbc.1, hS.trans hab.2 hbc.2⟩⟩

/-- `AtomicU64` monotone counters (through `toNat`). -/
theorem u64_le : AtomicHistInv UInt64 (fun a b => a.toNat ≤ b.toNat) :=
  nat_le.comap UInt64.toNat

/-- Non-overflowing `UInt64` addition preserves `u64_le` without wraparound. -/
theorem u64_add_preserves (a d : UInt64) (h : a.toNat + d.toNat < UInt64.size) :
    (a + d).toNat = a.toNat + d.toNat ∧ a.toNat ≤ (a + d).toNat := by
  have heq : (a + d).toNat = a.toNat + d.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]
  exact ⟨heq, by omega⟩

/-- Bitmask-monotone flag words: bits may only be set (`new = old ||| mask`). -/
def BitsMono (a b : Nat) : Prop := a ||| b = b

theorem bitsMono_iff_exists_mask (a b : Nat) : BitsMono a b ↔ ∃ mask, b = a ||| mask := by
  constructor
  · intro h; exact ⟨b, h.symm⟩
  · rintro ⟨mask, rfl⟩
    show a ||| (a ||| mask) = a ||| mask
    rw [← Nat.or_assoc, Nat.or_self]

theorem bitsMono : AtomicHistInv Nat BitsMono :=
  ⟨fun a => Nat.or_self a, fun {a b c} hab hbc => by
    unfold BitsMono at *
    rw [← hbc, ← Nat.or_assoc, hab]⟩

/-- Versioned `(epoch, payload)` cells: the epoch strictly grows on every change. -/
def Versioned {P : Type} (a b : Nat × P) : Prop :=
  a.1 < b.1 ∨ a = b

theorem versioned (P : Type) : AtomicHistInv (Nat × P) Versioned :=
  ⟨fun _ => Or.inr rfl, fun {a b c} hab hbc => by
    rcases hab with hab | rfl
    · rcases hbc with hbc | rfl
      · exact Or.inl (Nat.lt_trans hab hbc)
      · exact Or.inl hab
    · exact hbc⟩

/-- `Versioned` rules out ABA: equal epochs force equal payloads. -/
theorem versioned_no_aba {P : Type} {a b : Nat × P} (h : Versioned a b) (he : a.1 = b.1) :
    a = b := by
  rcases h with h | h
  · exact absurd he (Nat.ne_of_lt h)
  · exact h

end AtomicHistInv

/-- Closure history invariants are history invariants on closure states. -/
abbrev ClosureHistInv (FState : Type u) (hist_inv : FState → FState → Prop) : Prop :=
  AtomicHistInv FState hist_inv

/--
`creusot#2386` model of a mutable closure `F : FnMut(Arg) -> Option<Out>` with
opaque state `FState`.
-/
structure FnMutSpec (FState Arg Out : Type u) where
  /-- History invariant between closure states (`F::hist_inv`). -/
  hist_inv : FState → FState → Prop
  /-- `hist_inv` is reflexive and transitive. -/
  hist_inv_laws : ClosureHistInv FState hist_inv
  /-- Call precondition (`F::precondition`). -/
  pre : FState → Arg → Prop
  /-- Mutating call postcondition (`F::postcondition_mut`). -/
  post_mut : FState → Arg → FState → Option Out → Prop
  /-- Every call respects `hist_inv`. -/
  step_hist_inv : ∀ f₁ x f₂ r, post_mut f₁ x f₂ r → hist_inv f₁ f₂
  /-- Prophetic resolution at drop (`resolve`). -/
  resolve : FState → Prop

/--
One-shot ghost `Committer<Self, T, SeqCst, SeqCst>` token of `creusot#2386`:
`shot_store` records whether the winning CAS has fired the ghost update, and
`val_load` / `val_store` record the committed transition.
-/
structure OneShotCommitter (Val : Type u) where
  shot_store : Bool
  val_load : Val
  val_store : Val

namespace OneShotCommitter

/-- A fresh, unshot committer. -/
def fresh {Val : Type u} (v : Val) : OneShotCommitter Val := ⟨false, v, v⟩

/-- Firing the committer on the winning CAS `old ↦ new`. -/
def fire {Val : Type u} (_ : OneShotCommitter Val) (old new : Val) :
    OneShotCommitter Val := ⟨true, old, new⟩

@[simp] theorem fire_shot {Val : Type u} (c : OneShotCommitter Val) (o n : Val) :
    (c.fire o n).shot_store = true := rfl

@[simp] theorem fresh_shot {Val : Type u} (v : Val) : (fresh v).shot_store = false := rfl

/-- A fired committer differs from every unshot one. -/
theorem fire_ne_of_unshot {Val : Type u} {c c' : OneShotCommitter Val} {o n : Val}
    (h : c'.shot_store = false) : c.fire o n ≠ c' := by
  intro he; rw [← he] at h; exact Bool.noConfusion h

end OneShotCommitter

/-- Ghost callback `G` fired by the winning CAS with the committer. -/
structure GhostCommit (Val G : Type u) where
  pre : G → Val → Val → Prop
  post : G → Val → Val → G → Prop

/-! ## 2. The Atomic-Cell Effect and the Rely/History Transformer -/

/-- Requests of one `try_update` thread. -/
inductive AtomicReq (Val : Type) : Type where
  /-- `self.load(SeqCst)`; the environment may interfere first. -/
  | load
  /-- `compare_exchange_weak(expected, desired)`. -/
  | cas (expected desired : Val)
  /-- Call the opaque `FnMut` closure on the observed value. -/
  | callF (arg : Val)
  /-- Drop the closure (prophetic `resolve`). -/
  | dropF
  /-- Accept a new service request (fresh committer, fresh contention window). -/
  | recv

/-- Answers of `AtomicReq`. -/
def AtomicAns (Val : Type) : AtomicReq Val → Type
  | .load => Val
  | .cas _ _ => Bool × Val
  | .callF _ => Option Val
  | .dropF => PUnit
  | .recv => PUnit

/-- The atomic-cell plus closure effect. -/
abbrev AtomicCellE (Val : Type) : Effect.{0} := CallE (AtomicReq Val) (AtomicAns Val)

section Effect

variable {Val : Type}

/-- The load request. -/
def aLoad : (AtomicCellE Val).I := .call .load

/-- The weak compare-exchange request. -/
def aCas (expected desired : Val) : (AtomicCellE Val).I := .call (.cas expected desired)

/-- The closure call request. -/
def aCall (x : Val) : (AtomicCellE Val).I := .call (.callF x)

/-- The closure drop request. -/
def aDrop : (AtomicCellE Val).I := .call .dropF

/-- The service request-arrival request. -/
def aRecv : (AtomicCellE Val).I := .call .recv

/-- Decode a loaded value. -/
def loadAns (o : (AtomicCellE Val).O aLoad) : Val := o

/-- Decode a CAS outcome `(succeeded, actual)`. -/
def casAns (e d : Val) (o : (AtomicCellE Val).O (aCas e d)) : Bool × Val := o

/-- Decode a closure result. -/
def callAns (x : Val) (o : (AtomicCellE Val).O (aCall x)) : Option Val := o

/-- Encode a CAS outcome. -/
def casOut (e d : Val) (b : Bool) (v : Val) : (AtomicCellE Val).O (aCas e d) := (b, v)

/-- Encode a closure result. -/
def callOut (x : Val) (r : Option Val) : (AtomicCellE Val).O (aCall x) := r

end Effect

/-- Logical state of one `try_update` thread. -/
structure AtomicSt (Val FState G : Type) where
  /-- Current atomic cell value. -/
  cell : Val
  /-- Current closure state. -/
  fst : FState
  /-- The one-shot ghost committer. -/
  comm : OneShotCommitter Val
  /-- Number of times the ghost committer fired. -/
  fires : Nat
  /-- Ghost-callback state. -/
  gst : G
  /-- Remaining contention / spurious-failure budget (`atomicBudgetWP`). -/
  budget : Nat

/-- Environment parameters: rely relation, closure spec, ghost callback. -/
structure AtomicEnv (Val FState G : Type) where
  /-- Environment interference allowed between two observations. -/
  rely : Val → Val → Prop
  /-- The closure specification. -/
  fSpec : FnMutSpec FState Val Val
  /-- The ghost callback fired on commit. -/
  gc : GhostCommit Val G

/--
Realizability side-condition for an `AtomicEnv`: `rely` admits stuttering,
`post_mut` and `gc.post` are total on their preconditions, and `resolve` holds
at drop. Any realizable environment satisfies `ExcludedMiracle` (no postcondition
can be discharged vacuously via miracle).
-/
structure AtomicEnv.Realizable {Val FState G : Type} (A : AtomicEnv Val FState G) : Prop where
  rely_refl : ∀ v, A.rely v v
  post_mut_total : ∀ f x, A.fSpec.pre f x → ∃ f' r, A.fSpec.post_mut f x f' r
  gc_post_total : ∀ g e d, A.gc.pre g e d → ∃ g', A.gc.post g e d g'
  resolve_total : ∀ f, A.fSpec.resolve f

section WP

variable {Val FState G : Type}

/-- State after a winning CAS `e ↦ d` (committer fired, ghost callback ran). -/
def AtomicSt.commit (s : AtomicSt Val FState G) (e d : Val) (g' : G) (b : Nat) :
    AtomicSt Val FState G :=
  { s with cell := d, comm := s.comm.fire e d, fires := s.fires + 1, gst := g', budget := b }

/--
Obligation of a winning CAS `e ↦ d` from state `s`: the one-shot `Committer`
must be unshot (`s.comm.shot_store = false`), the ghost callback precondition
must hold, and every post-state of `G` must satisfy the continuation.
-/
def casWin (A : AtomicEnv Val FState G) (e d : Val)
    (K : Bool × Val → AtomicSt Val FState G → Prop) (s : AtomicSt Val FState G)
    (b : Nat) : Prop :=
  s.comm.shot_store = false ∧ A.gc.pre s.gst e d ∧
    ∀ g', A.gc.post s.gst e d g' → K (true, e) (s.commit e d g' b)

/--
Unbounded weak-CAS rely/history transformer: every observation (including during
`dropF` before `try_update` returns) may be preceded by any `rely`-respecting
interference, every weak CAS may fail (even spuriously, on an equal value)
leaving the observed value in the cell, a winning CAS demands an unshot
one-shot `Committer`, and the contention budget is havocked.
-/
def atomicHistWP (A : AtomicEnv Val FState G) :
    StateEffectWP (AtomicSt Val FState G) (AtomicCellE Val) where
  wp
    | .call .load, K, s => ∀ v, A.rely s.cell v → ∀ b, K v { s with cell := v, budget := b }
    | .call (.cas e d), K, s => ∀ v, A.rely s.cell v → ∀ b,
        K (false, v) { s with cell := v, budget := b } ∧
          (v = e → casWin A e d K { s with cell := v } b)
    | .call (.callF x), K, s =>
        A.fSpec.pre s.fst x ∧ ∀ f' r, A.fSpec.post_mut s.fst x f' r → K r { s with fst := f' }
    | .call .dropF, K, s => ∀ v, A.rely s.cell v → ∀ b,
        A.fSpec.resolve s.fst → K PUnit.unit { s with cell := v, budget := b }
    | .call .recv, K, s =>
        ∀ b, K PUnit.unit { s with comm := .fresh s.cell, fires := 0, budget := b }
  mono {i} _ _ _ h hw :=
    match i with
    | .call .load => fun v hv b => h _ _ (hw v hv b)
    | .call (.cas _ _) => fun v hv b =>
        ⟨h _ _ (hw v hv b).1, fun he =>
          ⟨((hw v hv b).2 he).1, ((hw v hv b).2 he).2.1,
            fun g' hg => h _ _ (((hw v hv b).2 he).2.2 g' hg)⟩⟩
    | .call (.callF _) => ⟨hw.1, fun f' r hp => h _ _ (hw.2 f' r hp)⟩
    | .call .dropF => fun v hv b hr => h _ _ (hw v hv b hr)
    | .call .recv => fun b => h _ _ (hw b)

instance (A : AtomicEnv Val FState G) : StateEffectWP.Conjunctive (atomicHistWP A) where
  conj {i} _ _ _ hp hq :=
    match i with
    | .call .load => fun v hv b => ⟨hp v hv b, hq v hv b⟩
    | .call (.cas _ _) => fun v hv b =>
        ⟨⟨(hp v hv b).1, (hq v hv b).1⟩, fun he =>
          ⟨((hp v hv b).2 he).1, ((hp v hv b).2 he).2.1, fun g' hg =>
            ⟨((hp v hv b).2 he).2.2 g' hg, ((hq v hv b).2 he).2.2 g' hg⟩⟩⟩
    | .call (.callF _) => ⟨hp.1, fun f' r h => ⟨hp.2 f' r h, hq.2 f' r h⟩⟩
    | .call .dropF => fun v hv b hr => ⟨hp v hv b hr, hq v hv b hr⟩
    | .call .recv => fun b => ⟨hp b, hq b⟩

/--
Unbounded **strong-CAS** (`compare_exchange`) rely/history transformer: when
the observed cell value equals `expected`, the CAS must commit (no spurious
weak-CAS failure); a mismatch `v ≠ expected` still performs no write.
-/
def atomicStrongHistWP (A : AtomicEnv Val FState G) :
    StateEffectWP (AtomicSt Val FState G) (AtomicCellE Val) where
  wp
    | .call .load, K, s => ∀ v, A.rely s.cell v → ∀ b, K v { s with cell := v, budget := b }
    | .call (.cas e d), K, s => ∀ v, A.rely s.cell v → ∀ b,
        (v ≠ e → K (false, v) { s with cell := v, budget := b }) ∧
          (v = e → casWin A e d K { s with cell := v } b)
    | .call (.callF x), K, s =>
        A.fSpec.pre s.fst x ∧ ∀ f' r, A.fSpec.post_mut s.fst x f' r → K r { s with fst := f' }
    | .call .dropF, K, s => ∀ v, A.rely s.cell v → ∀ b,
        A.fSpec.resolve s.fst → K PUnit.unit { s with cell := v, budget := b }
    | .call .recv, K, s =>
        ∀ b, K PUnit.unit { s with comm := .fresh s.cell, fires := 0, budget := b }
  mono {i} _ _ _ h hw :=
    match i with
    | .call .load => fun v hv b => h _ _ (hw v hv b)
    | .call (.cas _ _) => fun v hv b =>
        ⟨fun hne => h _ _ ((hw v hv b).1 hne), fun he =>
          ⟨((hw v hv b).2 he).1, ((hw v hv b).2 he).2.1,
            fun g' hg => h _ _ (((hw v hv b).2 he).2.2 g' hg)⟩⟩
    | .call (.callF _) => ⟨hw.1, fun f' r hp => h _ _ (hw.2 f' r hp)⟩
    | .call .dropF => fun v hv b hr => h _ _ (hw v hv b hr)
    | .call .recv => fun b => h _ _ (hw b)

instance (A : AtomicEnv Val FState G) : StateEffectWP.Conjunctive (atomicStrongHistWP A) where
  conj {i} _ _ _ hp hq :=
    match i with
    | .call .load => fun v hv b => ⟨hp v hv b, hq v hv b⟩
    | .call (.cas _ _) => fun v hv b =>
        ⟨fun hne => ⟨(hp v hv b).1 hne, (hq v hv b).1 hne⟩, fun he =>
          ⟨((hp v hv b).2 he).1, ((hp v hv b).2 he).2.1, fun g' hg =>
            ⟨((hp v hv b).2 he).2.2 g' hg, ((hq v hv b).2 he).2.2 g' hg⟩⟩⟩
    | .call (.callF _) => ⟨hp.1, fun f' r h => ⟨hp.2 f' r h, hq.2 f' r h⟩⟩
    | .call .dropF => fun v hv b hr => ⟨hp v hv b hr, hq v hv b hr⟩
    | .call .recv => fun b => ⟨hp b, hq b⟩

/--
Bounded-contention transformer: interference (a changed value) and spurious
weak-CAS failures each consume one unit of `budget`; with `budget = 0` the
environment is quiescent and a CAS on the current value must win.
-/
def atomicBudgetWP (A : AtomicEnv Val FState G) :
    StateEffectWP (AtomicSt Val FState G) (AtomicCellE Val) where
  wp
    | .call .load, K, s => ∀ v, A.rely s.cell v →
        (v = s.cell → K v { s with cell := v }) ∧
          (v ≠ s.cell → 0 < s.budget → K v { s with cell := v, budget := s.budget - 1 })
    | .call (.cas e d), K, s => ∀ v, A.rely s.cell v →
        (v = s.cell →
          (v ≠ e → K (false, v) { s with cell := v }) ∧
            (v = e → 0 < s.budget →
              K (false, v) { s with cell := v, budget := s.budget - 1 }) ∧
            (v = e → casWin A e d K { s with cell := v } s.budget)) ∧
          (v ≠ s.cell → 0 < s.budget →
            K (false, v) { s with cell := v, budget := s.budget - 1 } ∧
              (v = e → casWin A e d K { s with cell := v } (s.budget - 1)))
    | .call (.callF x), K, s =>
        A.fSpec.pre s.fst x ∧ ∀ f' r, A.fSpec.post_mut s.fst x f' r → K r { s with fst := f' }
    | .call .dropF, K, s => ∀ v, A.rely s.cell v →
        (v = s.cell → A.fSpec.resolve s.fst → K PUnit.unit { s with cell := v }) ∧
          (v ≠ s.cell → 0 < s.budget → A.fSpec.resolve s.fst →
            K PUnit.unit { s with cell := v, budget := s.budget - 1 })
    | .call .recv, K, s =>
        ∀ b, K PUnit.unit { s with comm := .fresh s.cell, fires := 0, budget := b }
  mono {i} _ _ _ h hw :=
    match i with
    | .call .load => fun v hv =>
        ⟨fun he => h _ _ ((hw v hv).1 he), fun hne hb => h _ _ ((hw v hv).2 hne hb)⟩
    | .call (.cas _ _) => fun v hv =>
        ⟨fun hc =>
          ⟨fun hne => h _ _ (((hw v hv).1 hc).1 hne),
           fun he hb => h _ _ (((hw v hv).1 hc).2.1 he hb),
           fun he => ⟨(((hw v hv).1 hc).2.2 he).1, (((hw v hv).1 hc).2.2 he).2.1,
             fun g' hg => h _ _ ((((hw v hv).1 hc).2.2 he).2.2 g' hg)⟩⟩,
         fun hc hb =>
          ⟨h _ _ (((hw v hv).2 hc hb).1),
           fun he => ⟨(((hw v hv).2 hc hb).2 he).1, (((hw v hv).2 hc hb).2 he).2.1,
             fun g' hg => h _ _ ((((hw v hv).2 hc hb).2 he).2.2 g' hg)⟩⟩⟩
    | .call (.callF _) => ⟨hw.1, fun f' r hp => h _ _ (hw.2 f' r hp)⟩
    | .call .dropF => fun v hv =>
        ⟨fun he hr => h _ _ ((hw v hv).1 he hr),
         fun hne hb hr => h _ _ ((hw v hv).2 hne hb hr)⟩
    | .call .recv => fun b => h _ _ (hw b)

instance (A : AtomicEnv Val FState G) : StateEffectWP.Conjunctive (atomicBudgetWP A) where
  conj {i} _ _ _ hp hq :=
    match i with
    | .call .load => fun v hv =>
        ⟨fun he => ⟨(hp v hv).1 he, (hq v hv).1 he⟩,
         fun hne hb => ⟨(hp v hv).2 hne hb, (hq v hv).2 hne hb⟩⟩
    | .call (.cas _ _) => fun v hv =>
        ⟨fun hc =>
          ⟨fun hne => ⟨((hp v hv).1 hc).1 hne, ((hq v hv).1 hc).1 hne⟩,
           fun he hb => ⟨((hp v hv).1 hc).2.1 he hb, ((hq v hv).1 hc).2.1 he hb⟩,
           fun he => ⟨(((hp v hv).1 hc).2.2 he).1, (((hp v hv).1 hc).2.2 he).2.1, fun g' hg =>
             ⟨(((hp v hv).1 hc).2.2 he).2.2 g' hg, (((hq v hv).1 hc).2.2 he).2.2 g' hg⟩⟩⟩,
         fun hc hb =>
          ⟨⟨((hp v hv).2 hc hb).1, ((hq v hv).2 hc hb).1⟩,
           fun he => ⟨(((hp v hv).2 hc hb).2 he).1, (((hp v hv).2 hc hb).2 he).2.1, fun g' hg =>
             ⟨(((hp v hv).2 hc hb).2 he).2.2 g' hg, (((hq v hv).2 hc hb).2 he).2.2 g' hg⟩⟩⟩⟩
    | .call (.callF _) => ⟨hp.1, fun f' r h => ⟨hp.2 f' r h, hq.2 f' r h⟩⟩
    | .call .dropF => fun v hv =>
        ⟨fun he hr => ⟨(hp v hv).1 he hr, (hq v hv).1 he hr⟩,
         fun hne hb hr => ⟨(hp v hv).2 hne hb hr, (hq v hv).2 hne hb hr⟩⟩
    | .call .recv => fun b => ⟨hp b, hq b⟩

/--
**Refinement (budget)**: every obligation of the unbounded rely/history
environment is an obligation of the bounded-contention environment.
-/
theorem atomicHistWP_refines_budget (A : AtomicEnv Val FState G)
    (i : (AtomicCellE Val).I) (K : (AtomicCellE Val).O i → AtomicSt Val FState G → Prop)
    (s : AtomicSt Val FState G) (h : (atomicHistWP A).wp i K s) :
    (atomicBudgetWP A).wp i K s :=
  match i with
  | .call .load => fun v hv => ⟨fun _ => h v hv s.budget, fun _ _ => h v hv (s.budget - 1)⟩
  | .call (.cas _ _) => fun v hv =>
      ⟨fun _ => ⟨fun _ => (h v hv s.budget).1, fun _ _ => (h v hv (s.budget - 1)).1,
          fun he => (h v hv s.budget).2 he⟩,
       fun _ _ => ⟨(h v hv (s.budget - 1)).1, fun he => (h v hv (s.budget - 1)).2 he⟩⟩
  | .call (.callF _) => h
  | .call .dropF => fun v hv =>
      ⟨fun _ hr => h v hv s.budget hr, fun _ _ hr => h v hv (s.budget - 1) hr⟩
  | .call .recv => h

/--
**Refinement (strong CAS)**: every obligation of `compare_exchange_weak` is an
obligation of strong `compare_exchange` (strictly fewer failure behaviors).
-/
theorem atomicHistWP_refines_strong (A : AtomicEnv Val FState G)
    (i : (AtomicCellE Val).I) (K : (AtomicCellE Val).O i → AtomicSt Val FState G → Prop)
    (s : AtomicSt Val FState G) (h : (atomicHistWP A).wp i K s) :
    (atomicStrongHistWP A).wp i K s :=
  match i with
  | .call .load => h
  | .call (.cas _ _) => fun v hv b => ⟨fun _ => (h v hv b).1, (h v hv b).2⟩
  | .call (.callF _) => h
  | .call .dropF => h
  | .call .recv => h

/-- General `ExcludedMiracle` for `atomicHistWP` under `AtomicEnv.Realizable`. -/
theorem atomicHistWP_excludedMiracle {A : AtomicEnv Val FState G} (hR : A.Realizable) :
    StateEffectWP.ExcludedMiracle (atomicHistWP A) where
  no_miracle {i} {s} h :=
    match i with
    | .call .load => h s.cell (hR.rely_refl _) 0
    | .call (.cas _ _) => (h s.cell (hR.rely_refl _) 0).1
    | .call (.callF _) =>
        let ⟨f', r, hp⟩ := hR.post_mut_total _ _ h.1
        h.2 f' r hp
    | .call .dropF => h s.cell (hR.rely_refl _) 0 (hR.resolve_total _)
    | .call .recv => h 0

/-- General `ExcludedMiracle` for `atomicStrongHistWP` under `AtomicEnv.Realizable`. -/
theorem atomicStrongHistWP_excludedMiracle {A : AtomicEnv Val FState G} (hR : A.Realizable) :
    StateEffectWP.ExcludedMiracle (atomicStrongHistWP A) where
  no_miracle {i} {s} h :=
    match i with
    | .call .load => h s.cell (hR.rely_refl _) 0
    | .call (.cas e _) => by
        have h' := h s.cell (hR.rely_refl _) 0
        by_cases he : s.cell = e
        · obtain ⟨_, hgp, hcont⟩ := h'.2 he
          obtain ⟨g', hg'⟩ := hR.gc_post_total _ _ _ hgp
          exact hcont g' hg'
        · exact h'.1 he
    | .call (.callF _) =>
        let ⟨f', r, hp⟩ := hR.post_mut_total _ _ h.1
        h.2 f' r hp
    | .call .dropF => h s.cell (hR.rely_refl _) 0 (hR.resolve_total _)
    | .call .recv => h 0

/-- General `ExcludedMiracle` for `atomicBudgetWP` under `AtomicEnv.Realizable`. -/
theorem atomicBudgetWP_excludedMiracle {A : AtomicEnv Val FState G} (hR : A.Realizable) :
    StateEffectWP.ExcludedMiracle (atomicBudgetWP A) where
  no_miracle {i} {s} h :=
    match i with
    | .call .load => (h s.cell (hR.rely_refl _)).1 rfl
    | .call (.cas e _) => by
        have h' := (h s.cell (hR.rely_refl _)).1 rfl
        by_cases he : s.cell = e
        · obtain ⟨_, hgp, hcont⟩ := h'.2.2 he
          obtain ⟨g', hg'⟩ := hR.gc_post_total _ _ _ hgp
          exact hcont g' hg'
        · exact h'.1 he
    | .call (.callF _) =>
        let ⟨f', r, hp⟩ := hR.post_mut_total _ _ h.1
        h.2 f' r hp
    | .call .dropF => (h s.cell (hR.rely_refl _)).1 rfl (hR.resolve_total _)
    | .call .recv => h 0

end WP

/-! ### 2.1 Named one-step equations -/

section WPEqs

variable {Val FState G : Type} (A : AtomicEnv Val FState G)

theorem histWP_load (K : (AtomicCellE Val).O aLoad → AtomicSt Val FState G → Prop)
    (s : AtomicSt Val FState G) :
    (atomicHistWP A).wp aLoad K s ↔
      ∀ v, A.rely s.cell v → ∀ b, K v { s with cell := v, budget := b } := Iff.rfl

theorem histWP_cas (e d : Val)
    (K : (AtomicCellE Val).O (aCas e d) → AtomicSt Val FState G → Prop)
    (s : AtomicSt Val FState G) :
    (atomicHistWP A).wp (aCas e d) K s ↔
      ∀ v, A.rely s.cell v → ∀ b,
        K (casOut e d false v) { s with cell := v, budget := b } ∧
          (v = e → casWin A e d K { s with cell := v } b) := Iff.rfl

theorem histWP_call (x : Val)
    (K : (AtomicCellE Val).O (aCall x) → AtomicSt Val FState G → Prop)
    (s : AtomicSt Val FState G) :
    (atomicHistWP A).wp (aCall x) K s ↔
      A.fSpec.pre s.fst x ∧
        ∀ f' r, A.fSpec.post_mut s.fst x f' r → K (callOut x r) { s with fst := f' } :=
  Iff.rfl

theorem histWP_drop (K : (AtomicCellE Val).O aDrop → AtomicSt Val FState G → Prop)
    (s : AtomicSt Val FState G) :
    (atomicHistWP A).wp aDrop K s ↔
      ∀ v, A.rely s.cell v → ∀ b,
        A.fSpec.resolve s.fst → K PUnit.unit { s with cell := v, budget := b } := Iff.rfl

theorem histWP_recv (K : (AtomicCellE Val).O aRecv → AtomicSt Val FState G → Prop)
    (s : AtomicSt Val FState G) :
    (atomicHistWP A).wp aRecv K s ↔
      ∀ b, K PUnit.unit { s with comm := .fresh s.cell, fires := 0, budget := b } := Iff.rfl

theorem strongWP_load (K : (AtomicCellE Val).O aLoad → AtomicSt Val FState G → Prop)
    (s : AtomicSt Val FState G) :
    (atomicStrongHistWP A).wp aLoad K s ↔
      ∀ v, A.rely s.cell v → ∀ b, K v { s with cell := v, budget := b } := Iff.rfl

theorem strongWP_cas (e d : Val)
    (K : (AtomicCellE Val).O (aCas e d) → AtomicSt Val FState G → Prop)
    (s : AtomicSt Val FState G) :
    (atomicStrongHistWP A).wp (aCas e d) K s ↔
      ∀ v, A.rely s.cell v → ∀ b,
        (v ≠ e → K (casOut e d false v) { s with cell := v, budget := b }) ∧
          (v = e → casWin A e d K { s with cell := v } b) := Iff.rfl

theorem strongWP_call (x : Val)
    (K : (AtomicCellE Val).O (aCall x) → AtomicSt Val FState G → Prop)
    (s : AtomicSt Val FState G) :
    (atomicStrongHistWP A).wp (aCall x) K s ↔
      A.fSpec.pre s.fst x ∧
        ∀ f' r, A.fSpec.post_mut s.fst x f' r → K (callOut x r) { s with fst := f' } :=
  Iff.rfl

theorem strongWP_drop (K : (AtomicCellE Val).O aDrop → AtomicSt Val FState G → Prop)
    (s : AtomicSt Val FState G) :
    (atomicStrongHistWP A).wp aDrop K s ↔
      ∀ v, A.rely s.cell v → ∀ b,
        A.fSpec.resolve s.fst → K PUnit.unit { s with cell := v, budget := b } := Iff.rfl

theorem budgetWP_load (K : (AtomicCellE Val).O aLoad → AtomicSt Val FState G → Prop)
    (s : AtomicSt Val FState G) :
    (atomicBudgetWP A).wp aLoad K s ↔
      ∀ v, A.rely s.cell v →
        (v = s.cell → K v { s with cell := v }) ∧
          (v ≠ s.cell → 0 < s.budget → K v { s with cell := v, budget := s.budget - 1 }) :=
  Iff.rfl

theorem budgetWP_cas (e d : Val)
    (K : (AtomicCellE Val).O (aCas e d) → AtomicSt Val FState G → Prop)
    (s : AtomicSt Val FState G) :
    (atomicBudgetWP A).wp (aCas e d) K s ↔
      ∀ v, A.rely s.cell v →
        (v = s.cell →
          (v ≠ e → K (casOut e d false v) { s with cell := v }) ∧
            (v = e → 0 < s.budget →
              K (casOut e d false v) { s with cell := v, budget := s.budget - 1 }) ∧
            (v = e → casWin A e d K { s with cell := v } s.budget)) ∧
          (v ≠ s.cell → 0 < s.budget →
            K (casOut e d false v) { s with cell := v, budget := s.budget - 1 } ∧
              (v = e → casWin A e d K { s with cell := v } (s.budget - 1))) := Iff.rfl

theorem budgetWP_call (x : Val)
    (K : (AtomicCellE Val).O (aCall x) → AtomicSt Val FState G → Prop)
    (s : AtomicSt Val FState G) :
    (atomicBudgetWP A).wp (aCall x) K s ↔
      A.fSpec.pre s.fst x ∧
        ∀ f' r, A.fSpec.post_mut s.fst x f' r → K (callOut x r) { s with fst := f' } :=
  Iff.rfl

theorem budgetWP_drop (K : (AtomicCellE Val).O aDrop → AtomicSt Val FState G → Prop)
    (s : AtomicSt Val FState G) :
    (atomicBudgetWP A).wp aDrop K s ↔
      ∀ v, A.rely s.cell v →
        (v = s.cell → A.fSpec.resolve s.fst → K PUnit.unit { s with cell := v }) ∧
          (v ≠ s.cell → 0 < s.budget → A.fSpec.resolve s.fst →
            K PUnit.unit { s with cell := v, budget := s.budget - 1 }) := Iff.rfl

theorem budgetWP_recv (K : (AtomicCellE Val).O aRecv → AtomicSt Val FState G → Prop)
    (s : AtomicSt Val FState G) :
    (atomicBudgetWP A).wp aRecv K s ↔
      ∀ b, K PUnit.unit { s with comm := .fresh s.cell, fires := 0, budget := b } := Iff.rfl

theorem casWin_iff (e d : Val) (K : Bool × Val → AtomicSt Val FState G → Prop)
    (s : AtomicSt Val FState G) (b : Nat) :
    casWin A e d K s b ↔
      s.comm.shot_store = false ∧ A.gc.pre s.gst e d ∧
        ∀ g', A.gc.post s.gst e d g' → K (true, e) (s.commit e d g' b) :=
  Iff.rfl

end WPEqs

/-! ## 3. `Atomic::try_update` / `fetch_update` as an `ITree.iter` CAS Loop -/

section Loop

variable {Val : Type}

/-- Drop the closure, then return `res`. -/
def retAfterDrop (res : Except Val Val) : ITree (AtomicCellE Val) (Val ⊕ Except Val Val) :=
  ITree.vis aDrop (fun _ => ITree.ret (Sum.inr res))

/-- After `compare_exchange_weak(prev, next)`: `Ok(_) => return`, `Err(a) => prev = a`. -/
def tryCasK (prev next : Val) (o : (AtomicCellE Val).O (aCas prev next)) :
    ITree (AtomicCellE Val) (Val ⊕ Except Val Val) :=
  match casAns prev next o with
  | (true, _) => retAfterDrop (.ok prev)
  | (false, actual) => ITree.ret (Sum.inl actual)

/-- After `f(prev)`: `None => Err(prev)`, `Some(next) => compare_exchange_weak`. -/
def tryCallK (prev : Val) (o : (AtomicCellE Val).O (aCall prev)) :
    ITree (AtomicCellE Val) (Val ⊕ Except Val Val) :=
  match callAns prev o with
  | none => retAfterDrop (.error prev)
  | some next => ITree.vis (aCas prev next) (tryCasK prev next)

/-- One iteration of `while let Some(next) = f(prev) { compare_exchange_weak .. }`. -/
def tryBody (prev : Val) : ITree (AtomicCellE Val) (Val ⊕ Except Val Val) :=
  ITree.vis (aCall prev) (tryCallK prev)

/--
`creusot#2386` `fetch_update` / `try_update`:
`let mut prev = load(); while let Some(next) = f(prev) { match cas_weak(prev, next)
{ Ok(x) => return Ok(x), Err(a) => prev = a } } Err(prev)`.
-/
def tryUpdateLoop (Val : Type) : ITree (AtomicCellE Val) (Except Val Val) :=
  ITree.vis aLoad (fun o => ITree.iter tryBody (loadAns o))

theorem tryCallK_none (prev : Val) :
    tryCallK prev (callOut prev none) = retAfterDrop (.error prev) := rfl

theorem tryCallK_some (prev next : Val) :
    tryCallK prev (callOut prev (some next)) = ITree.vis (aCas prev next) (tryCasK prev next) :=
  rfl

theorem tryCasK_false (prev next v : Val) :
    tryCasK prev next (casOut prev next false v) = ITree.ret (Sum.inl v) := rfl

theorem tryCasK_true (prev next v : Val) :
    tryCasK prev next (true, v) = retAfterDrop (.ok prev) := rfl

theorem tryCasK_casOut_true (prev next v : Val) :
    tryCasK prev next (casOut prev next true v) = retAfterDrop (.ok prev) := rfl

/-- `ITree.iter` unfolding of the `try_update` loop at the closure call. -/
theorem iter_tryBody_eq (prev : Val) :
    ITree.iter tryBody prev =
      ITree.vis (aCall prev) (fun o => tryCallK prev o >>=
        Sum.elim (fun next => ITree.tau (ITree.iter tryBody next)) ITree.ret) :=
  (iter_unfold tryBody prev).trans (vis_bind _ _ _)

theorem iter_tryBody_observe (prev : Val) :
    (ITree.iter tryBody prev).observe =
      .vis (aCall prev) (fun o => tryCallK prev o >>=
        Sum.elim (fun next => ITree.tau (ITree.iter tryBody next)) ITree.ret) := by
  rw [iter_tryBody_eq]; exact ITree.observe_vis _ _

/-- Case analysis on a closure answer through its decoder. -/
theorem forall_callOut (x : Val) (P : (AtomicCellE Val).O (aCall x) → Prop)
    (h : ∀ r, P (callOut x r)) (o : (AtomicCellE Val).O (aCall x)) : P o := h o

/-- Case analysis on a CAS answer through its decoder. -/
theorem forall_casOut (e d : Val) (P : (AtomicCellE Val).O (aCas e d) → Prop)
    (h : ∀ b v, P (casOut e d b v)) (o : (AtomicCellE Val).O (aCas e d)) : P o :=
  h (casAns e d o).1 (casAns e d o).2

end Loop

/-! ## 4. The `creusot#2386` Contract -/

section Contract

variable {Val FState G : Type}

/--
`creusot#2386` preconditions of `try_update` / `fetch_update`:
(i) the closure precondition holds on every `hist_inv`-successor of `f₀`;
(ii) every `Some next` it returns on an observed `x` respects the cell
invariant and enables the unshot ghost committer update `G`;
(iii) environment interference respects the cell invariant.
-/
structure TryUpdatePre (A : AtomicEnv Val FState G) (Rel : Val → Val → Prop)
    (init : Val) (f₀ : FState) (g₀ : G) (comm₀ : OneShotCommitter Val) : Prop where
  cellInv : AtomicHistInv Val Rel
  closure_pre : ∀ x f₂, Rel init x → A.fSpec.hist_inv f₀ f₂ → A.fSpec.pre f₂ x
  closure_step : ∀ f₂ x f₃ n, A.fSpec.hist_inv f₀ f₂ → A.fSpec.post_mut f₂ x f₃ (some n) →
    Rel init x → Rel x n ∧ A.gc.pre g₀ x n
  rely_sound : ∀ a b, A.rely a b → Rel a b
  comm_unshot : comm₀.shot_store = false

/-- Initial state of a `try_update` call. -/
def InitSt (init : Val) (f₀ : FState) (g₀ : G) (comm₀ : OneShotCommitter Val)
    (s : AtomicSt Val FState G) : Prop :=
  s.cell = init ∧ s.fst = f₀ ∧ s.comm = comm₀ ∧ s.fires = 0 ∧ s.gst = g₀

/--
State invariant at every configuration of `try_update`: the cell history is
`Rel`-related to the initial value, the closure history to `f₀`, and the ghost
committer has fired at most once (exactly when it is shot).
-/
def HistInvSt (A : AtomicEnv Val FState G) (Rel : Val → Val → Prop) (init : Val)
    (f₀ : FState) (s : AtomicSt Val FState G) : Prop :=
  Rel init s.cell ∧ A.fSpec.hist_inv f₀ s.fst ∧ s.fires ≤ 1 ∧
    (s.comm.shot_store = true ↔ s.fires = 1)

/-- Loop invariant at the head of each `while let` iteration. -/
def LoopInv (A : AtomicEnv Val FState G) (Rel : Val → Val → Prop) (init : Val)
    (f₀ : FState) (g₀ : G) (comm₀ : OneShotCommitter Val) (prev : Val)
    (s : AtomicSt Val FState G) : Prop :=
  Rel init prev ∧ s.cell = prev ∧ A.fSpec.hist_inv f₀ s.fst ∧ s.comm = comm₀ ∧
    s.fires = 0 ∧ s.gst = g₀

/--
The exact `creusot#2386` postcondition (accounting for concurrent `rely`
interference while the closure drops before returning). `Ok old`: some
`hist_inv`-successor `f₂` of `f₀` mapped `old ↦ Some new`, the resolved final
closure state is `f₃`, the committer fired exactly once on `old ↦ new`
(`val_load = old`, `val_store = new`), `Rel new s.cell` and `Rel init s.cell`
hold, and `G.post` holds. `Err cur`: the closure aborted on `cur`, `Rel cur
s.cell`, and the committer is untouched.
-/
def CreusotPost (A : AtomicEnv Val FState G) (Rel : Val → Val → Prop) (init : Val)
    (f₀ : FState) (g₀ : G) (comm₀ : OneShotCommitter Val) :
    Except Val Val → AtomicSt Val FState G → Prop
  | .ok old, s => ∃ new f₂ f₃, A.fSpec.hist_inv f₀ f₂ ∧
      A.fSpec.post_mut f₂ old f₃ (some new) ∧ A.fSpec.resolve f₃ ∧ Rel init old ∧
      Rel old new ∧ Rel new s.cell ∧ Rel init s.cell ∧ s.fst = f₃ ∧
      s.comm = comm₀.fire old new ∧ s.comm.shot_store = true ∧
      s.comm.val_load = old ∧ s.comm.val_store = new ∧ s.fires = 1 ∧
      A.gc.post g₀ old new s.gst
  | .error cur, s => ∃ f₂ f₃, A.fSpec.hist_inv f₀ f₂ ∧
      A.fSpec.post_mut f₂ cur f₃ none ∧ A.fSpec.resolve f₃ ∧ Rel init cur ∧
      Rel cur s.cell ∧ Rel init s.cell ∧ s.fst = f₃ ∧ s.comm = comm₀ ∧
      s.comm.shot_store = false ∧ s.fires = 0 ∧ s.gst = g₀

/-- Per-operation step relation of `try_update` (a failed CAS writes nothing). -/
def OpStep : (i : (AtomicCellE Val).I) → (AtomicCellE Val).O i →
    AtomicSt Val FState G → AtomicSt Val FState G → Prop
  | .call .load, v, s, s' => s'.cell = v ∧ s'.comm = s.comm ∧ s'.fires = s.fires
  | .call (.cas e d), o, s, s' =>
      ((casAns e d o).1 = false →
        s'.cell = (casAns e d o).2 ∧ s'.comm = s.comm ∧ s'.fires = s.fires) ∧
      ((casAns e d o).1 = true →
        (casAns e d o).2 = e ∧ s'.cell = d ∧ s.comm.shot_store = false ∧
          s'.comm = s.comm.fire e d ∧ s'.fires = s.fires + 1)
  | .call (.callF _), _, s, s' => s'.cell = s.cell ∧ s'.comm = s.comm ∧ s'.fires = s.fires
  | .call .dropF, _, s, s' => s'.fst = s.fst ∧ s'.comm = s.comm ∧ s'.fires = s.fires
  | .call .recv, _, s, s' => s'.cell = s.cell ∧ s'.comm = .fresh s.cell ∧ s'.fires = 0

/-- Transition-relational history invariant of every step. -/
def HistStep (A : AtomicEnv Val FState G) (Rel : Val → Val → Prop)
    (i : (AtomicCellE Val).I) (o : (AtomicCellE Val).O i)
    (s s' : AtomicSt Val FState G) : Prop :=
  Rel s.cell s'.cell ∧ A.fSpec.hist_inv s.fst s'.fst ∧ OpStep i o s s'

/-! ### 4.1 Per-node lemmas shared by every temporal proof -/

variable {A : AtomicEnv Val FState G} {Rel : Val → Val → Prop} {init : Val}
  {f₀ : FState} {g₀ : G} {comm₀ : OneShotCommitter Val}

theorem loopInv_of_init (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    {s : AtomicSt Val FState G} (hs : InitSt init f₀ g₀ comm₀ s) {v : Val}
    (hv : A.rely s.cell v) (b : Nat) :
    LoopInv A Rel init f₀ g₀ comm₀ v { s with cell := v, budget := b } := by
  obtain ⟨hc, hf, hm, hn, hg⟩ := hs
  refine ⟨?_, rfl, ?_, hm, hn, hg⟩
  · rw [← hc]; exact hpre.rely_sound _ _ hv
  · show A.fSpec.hist_inv f₀ s.fst
    rw [hf]; exact A.fSpec.hist_inv_laws.refl f₀

theorem histInvSt_of_init (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    {s : AtomicSt Val FState G} (hs : InitSt init f₀ g₀ comm₀ s) :
    HistInvSt A Rel init f₀ s := by
  obtain ⟨hc, hf, hm, hn, _⟩ := hs
  refine ⟨hc ▸ hpre.cellInv.refl init, hf ▸ A.fSpec.hist_inv_laws.refl f₀, by omega, ?_⟩
  rw [hm, hn, hpre.comm_unshot]; simp

theorem histInvSt_of_loopInv (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    {prev : Val} {s : AtomicSt Val FState G} (hl : LoopInv A Rel init f₀ g₀ comm₀ prev s) :
    HistInvSt A Rel init f₀ s := by
  obtain ⟨hr, hc, hf, hm, hn, _⟩ := hl
  refine ⟨hc ▸ hr, hf, by omega, ?_⟩
  rw [hm, hn, hpre.comm_unshot]; simp

theorem loopInv_pre (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀) {prev : Val}
    {s : AtomicSt Val FState G} (hl : LoopInv A Rel init f₀ g₀ comm₀ prev s) :
    A.fSpec.pre s.fst prev :=
  hpre.closure_pre prev s.fst hl.1 hl.2.2.1

theorem loopInv_unshot (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀) {prev : Val}
    {s : AtomicSt Val FState G} (hl : LoopInv A Rel init f₀ g₀ comm₀ prev s) :
    s.comm.shot_store = false := by
  rw [hl.2.2.2.1]; exact hpre.comm_unshot

theorem loopInv_call (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀) {prev : Val}
    {s : AtomicSt Val FState G} (hl : LoopInv A Rel init f₀ g₀ comm₀ prev s)
    {f' : FState} {r : Option Val} (hpost : A.fSpec.post_mut s.fst prev f' r) :
    HistInvSt A Rel init f₀ { s with fst := f' } := by
  obtain ⟨hr, hc, hf, hm, hn, _⟩ := hl
  refine ⟨hc ▸ hr, A.fSpec.hist_inv_laws.trans hf (A.fSpec.step_hist_inv _ _ _ _ hpost),
    by show s.fires ≤ 1; omega, ?_⟩
  show s.comm.shot_store = true ↔ s.fires = 1
  rw [hm, hn, hpre.comm_unshot]; simp

theorem loopInv_drop_inv (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀) {s : AtomicSt Val FState G}
    (hinv : HistInvSt A Rel init f₀ s) {v : Val} (hv : A.rely s.cell v) (b : Nat) :
    HistInvSt A Rel init f₀ { s with cell := v, budget := b } :=
  ⟨hpre.cellInv.trans hinv.1 (hpre.rely_sound _ _ hv), hinv.2.1, hinv.2.2.1, hinv.2.2.2⟩

theorem loopInv_err_post (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀) {prev : Val}
    {s : AtomicSt Val FState G} (hl : LoopInv A Rel init f₀ g₀ comm₀ prev s) {f' : FState}
    (hpost : A.fSpec.post_mut s.fst prev f' none) {v : Val} (hv : A.rely s.cell v) (b : Nat)
    (hres : A.fSpec.resolve f') :
    CreusotPost A Rel init f₀ g₀ comm₀ (.error prev)
      { s with fst := f', cell := v, budget := b } := by
  obtain ⟨hr, hc, hf, hm, hn, hg⟩ := hl
  have hcv : Rel prev v := hc ▸ hpre.rely_sound _ _ hv
  exact ⟨s.fst, f', hf, hpost, hres, hr, hcv, hpre.cellInv.trans hr hcv, rfl, hm,
    hm ▸ hpre.comm_unshot, hn, hg⟩

theorem loopInv_fail (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀) {prev next : Val}
    {s : AtomicSt Val FState G} (hl : LoopInv A Rel init f₀ g₀ comm₀ prev s) {f' : FState}
    (hpost : A.fSpec.post_mut s.fst prev f' (some next)) {v : Val} (hv : A.rely s.cell v)
    (b : Nat) :
    LoopInv A Rel init f₀ g₀ comm₀ v { s with fst := f', cell := v, budget := b } := by
  obtain ⟨hr, hc, hf, hm, hn, hg⟩ := hl
  refine ⟨hpre.cellInv.trans hr (hc ▸ hpre.rely_sound _ _ hv), rfl,
    A.fSpec.hist_inv_laws.trans hf (A.fSpec.step_hist_inv _ _ _ _ hpost), hm, hn, hg⟩

theorem loopInv_rel_next (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀) {prev next : Val}
    {s : AtomicSt Val FState G} (hl : LoopInv A Rel init f₀ g₀ comm₀ prev s) {f' : FState}
    (hpost : A.fSpec.post_mut s.fst prev f' (some next)) :
    Rel prev next ∧ A.gc.pre g₀ prev next :=
  hpre.closure_step s.fst prev f' next hl.2.2.1 hpost hl.1

theorem loopInv_win_pre (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀) {prev next : Val}
    {s : AtomicSt Val FState G} (hl : LoopInv A Rel init f₀ g₀ comm₀ prev s) {f' : FState}
    (hpost : A.fSpec.post_mut s.fst prev f' (some next)) :
    A.gc.pre s.gst prev next :=
  hl.2.2.2.2.2 ▸ (loopInv_rel_next hpre hl hpost).2

/-- State after `f(prev) = Some next` and a winning `cas_weak(prev, next)`. -/
abbrev winSt (s : AtomicSt Val FState G) (f' : FState) (prev next : Val) (g' : G)
    (b : Nat) : AtomicSt Val FState G :=
  AtomicSt.commit { s with fst := f', cell := prev } prev next g' b

theorem loopInv_win_inv (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀) {prev next : Val}
    {s : AtomicSt Val FState G} (hl : LoopInv A Rel init f₀ g₀ comm₀ prev s) {f' : FState}
    (hpost : A.fSpec.post_mut s.fst prev f' (some next)) (g' : G) (b : Nat) :
    HistInvSt A Rel init f₀ (winSt s f' prev next g' b) := by
  obtain ⟨hr, _, hf, _, hn, _⟩ := hl
  refine ⟨hpre.cellInv.trans hr (loopInv_rel_next hpre ⟨hr, ‹_›, hf, ‹_›, hn, ‹_›⟩ hpost).1,
    A.fSpec.hist_inv_laws.trans hf (A.fSpec.step_hist_inv _ _ _ _ hpost), ?_, ?_⟩
  · show s.fires + 1 ≤ 1; omega
  · show true = true ↔ s.fires + 1 = 1; simp [hn]

theorem loopInv_ok_post (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀) {prev next : Val}
    {s : AtomicSt Val FState G} (hl : LoopInv A Rel init f₀ g₀ comm₀ prev s) {f' : FState}
    (hpost : A.fSpec.post_mut s.fst prev f' (some next)) {g' : G}
    (hg' : A.gc.post s.gst prev next g') {v : Val} (hv : A.rely next v) (b b' : Nat)
    (hres : A.fSpec.resolve f') :
    CreusotPost A Rel init f₀ g₀ comm₀ (.ok prev)
      { winSt s f' prev next g' b with cell := v, budget := b' } := by
  have hrn := (loopInv_rel_next hpre hl hpost).1
  have hnv : Rel next v := hpre.rely_sound _ _ hv
  obtain ⟨hr, _, hf, _, hn, hg⟩ := hl
  refine ⟨next, s.fst, f', hf, hpost, hres, hr, hrn, hnv,
    hpre.cellInv.trans (hpre.cellInv.trans hr hrn) hnv, rfl, rfl, rfl, rfl, rfl, ?_, hg ▸ hg'⟩
  show s.fires + 1 = 1; omega

end Contract

/-! ## 5. Safety: `Always`, `AlwaysStep` and `DWLP` Under Unbounded Contention -/

section Safety

variable {Val FState G : Type} {A : AtomicEnv Val FState G} {Rel : Val → Val → Prop}
  {init : Val} {f₀ : FState} {g₀ : G} {comm₀ : OneShotCommitter Val}

/-- One loop iteration is `Always`-safe and re-establishes the loop invariant. -/
theorem tryBody_always (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀) (prev : Val)
    (s : AtomicSt Val FState G) (hl : LoopInv A Rel init f₀ g₀ comm₀ prev s) :
    Always (atomicHistWP A) (HistInvSt A Rel init f₀)
      (Sum.elim (LoopInv A Rel init f₀ g₀ comm₀) (CreusotPost A Rel init f₀ g₀ comm₀))
      (tryBody prev) s := by
  refine Always.vis (histInvSt_of_loopInv hpre hl)
    ((histWP_call A prev _ s).2 ⟨loopInv_pre hpre hl, fun f' r hpost => ?_⟩)
  have hinv := loopInv_call hpre hl hpost
  cases r with
  | none =>
    rw [tryCallK_none]
    exact Always.vis hinv ((histWP_drop A _ _).2 fun v hv b hres =>
      Always.ret (loopInv_drop_inv hpre hinv hv b)
        (loopInv_err_post hpre hl hpost hv b hres))
  | some next =>
    rw [tryCallK_some]
    refine Always.vis hinv ((histWP_cas A prev next _ _).2 fun v hv b => ⟨?_, fun hve => ?_⟩)
    · rw [tryCasK_false]
      have hl' := loopInv_fail hpre hl hpost hv b
      exact Always.ret (histInvSt_of_loopInv hpre hl') hl'
    · subst hve
      refine (casWin_iff A _ _ _ _ _).2 ⟨loopInv_unshot (s := s) hpre hl,
        loopInv_win_pre (s := s) hpre hl hpost, fun g' hg' => ?_⟩
      rw [tryCasK_true]
      have hwin := loopInv_win_inv hpre hl hpost g' b
      exact Always.vis hwin ((histWP_drop A _ _).2 fun v' hv' b' hres =>
        Always.ret (loopInv_drop_inv hpre hwin hv' b')
          (loopInv_ok_post hpre hl hpost hg' hv' b b' hres))

/--
**Safety (`creusot#2386`)**: under arbitrary (`rely`-respecting) contention and
unboundedly many spurious weak-CAS failures, every configuration of
`tryUpdateLoop` satisfies the history invariant (`Rel init cell`, `hist_inv f₀ f`,
committer fired at most once), and every return satisfies the exact
`creusot#2386` postcondition.
-/
theorem tryUpdate_always_safety (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    {s₀ : AtomicSt Val FState G} (hs : InitSt init f₀ g₀ comm₀ s₀) :
    Always (atomicHistWP A) (HistInvSt A Rel init f₀) (CreusotPost A Rel init f₀ g₀ comm₀)
      (tryUpdateLoop Val) s₀ :=
  Always.vis (histInvSt_of_init hpre hs) ((histWP_load A _ s₀).2 fun _ hv b =>
    Always.iter_invariant tryBody (LoopInv A Rel init f₀ g₀ comm₀)
      (tryBody_always hpre) (loopInv_of_init hpre hs hv b))

/-- **Exact `DWLP` form** of the safety theorem (`always_iff_dwlp_invariant`). -/
theorem tryUpdate_dwlp_creusot_spec (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    {s₀ : AtomicSt Val FState G} (hs : InitSt init f₀ g₀ comm₀ s₀) :
    DWLP (guardInvWP (atomicHistWP A) (HistInvSt A Rel init f₀)) (tryUpdateLoop Val)
      (fun r s => HistInvSt A Rel init f₀ s ∧ CreusotPost A Rel init f₀ g₀ comm₀ r s) s₀ :=
  ((always_iff_dwlp_invariant _ _ _ _ _).1 (tryUpdate_always_safety hpre hs)).2

/-- One loop iteration respects the step relation `HistStep`. -/
theorem tryBody_alwaysStep (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀) (prev : Val)
    (s : AtomicSt Val FState G) (hl : LoopInv A Rel init f₀ g₀ comm₀ prev s) :
    AlwaysStep (atomicHistWP A) (HistStep A Rel)
      (Sum.elim (LoopInv A Rel init f₀ g₀ comm₀) (CreusotPost A Rel init f₀ g₀ comm₀))
      (tryBody prev) s := by
  have hrefl := hpre.cellInv.refl
  have hhrefl := A.fSpec.hist_inv_laws.refl
  refine (AlwaysStep.vis_iff _ _ _ _ _ _).2
    ((histWP_call A prev _ s).2 ⟨loopInv_pre hpre hl, fun f' r hpost => ⟨⟨hrefl _,
      A.fSpec.step_hist_inv _ _ _ _ hpost, rfl, rfl, rfl⟩, ?_⟩⟩)
  cases r with
  | none =>
    rw [tryCallK_none]
    refine (AlwaysStep.vis_iff _ _ _ _ _ _).2 ((histWP_drop A _ _).2 fun v hv b hres =>
      ⟨⟨hpre.rely_sound _ _ hv, hhrefl _, rfl, rfl, rfl⟩, ?_⟩)
    exact (AlwaysStep.ret_iff _ _ _ _ _).2 (loopInv_err_post hpre hl hpost hv b hres)
  | some next =>
    rw [tryCallK_some]
    refine (AlwaysStep.vis_iff _ _ _ _ _ _).2
      ((histWP_cas A prev next _ _).2 fun v hv b => ⟨⟨⟨hpre.rely_sound _ _ hv, hhrefl _,
        fun _ => ⟨rfl, rfl, rfl⟩, fun h => Bool.noConfusion h⟩, ?_⟩, fun hve => ?_⟩)
    · rw [tryCasK_false]
      exact (AlwaysStep.ret_iff _ _ _ _ _).2 (loopInv_fail hpre hl hpost hv b)
    · subst hve
      refine (casWin_iff A _ _ _ _ _).2 ⟨loopInv_unshot (s := s) hpre hl,
        loopInv_win_pre (s := s) hpre hl hpost, fun g' hg' => ?_⟩
      have hrn := (loopInv_rel_next hpre hl hpost).1
      refine ⟨⟨hpre.cellInv.trans (hpre.rely_sound _ _ hv) hrn, hhrefl _,
        fun h => Bool.noConfusion h,
        fun _ => ⟨rfl, rfl, loopInv_unshot (s := s) hpre hl, rfl, rfl⟩⟩, ?_⟩
      rw [tryCasK_true]
      refine (AlwaysStep.vis_iff _ _ _ _ _ _).2 ((histWP_drop A _ _).2 fun v' hv' b' hres =>
        ⟨⟨hpre.rely_sound _ _ hv', hhrefl _, rfl, rfl, rfl⟩, ?_⟩)
      exact (AlwaysStep.ret_iff _ _ _ _ _).2 (loopInv_ok_post hpre hl hpost hg' hv' b b' hres)

/--
**Transition safety**: every step of `tryUpdateLoop` is `Rel`-monotone on the
cell and `hist_inv`-monotone on the closure; a failed CAS performs no write (the
cell holds exactly the returned `actual`, committer untouched); the committer
fires only from the unshot state, on the winning CAS.
-/
theorem tryUpdate_alwaysStep_safety (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    {s₀ : AtomicSt Val FState G} (hs : InitSt init f₀ g₀ comm₀ s₀) :
    AlwaysStep (atomicHistWP A) (HistStep A Rel) (CreusotPost A Rel init f₀ g₀ comm₀)
      (tryUpdateLoop Val) s₀ :=
  (AlwaysStep.vis_iff _ _ _ _ _ _).2 ((histWP_load A _ s₀).2 fun _ hv b =>
    ⟨⟨hpre.rely_sound _ _ hv, A.fSpec.hist_inv_laws.refl _, rfl, rfl, rfl⟩,
      AlwaysStep.iter_invariant tryBody (LoopInv A Rel init f₀ g₀ comm₀)
        (tryBody_alwaysStep hpre) (loopInv_of_init hpre hs hv b)⟩)

/-- Safety is inherited by every more restrictive environment (`atomicBudgetWP`). -/
theorem tryUpdate_budget_always (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    {s₀ : AtomicSt Val FState G} (hs : InitSt init f₀ g₀ comm₀ s₀) :
    Always (atomicBudgetWP A) (HistInvSt A Rel init f₀) (CreusotPost A Rel init f₀ g₀ comm₀)
      (tryUpdateLoop Val) s₀ :=
  Always.mono_wp (atomicHistWP_refines_budget A) (tryUpdate_always_safety hpre hs)

/-- Safety is inherited by strong `compare_exchange` (`atomicStrongHistWP`). -/
theorem tryUpdate_strong_always_safety (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    {s₀ : AtomicSt Val FState G} (hs : InitSt init f₀ g₀ comm₀ s₀) :
    Always (atomicStrongHistWP A) (HistInvSt A Rel init f₀) (CreusotPost A Rel init f₀ g₀ comm₀)
      (tryUpdateLoop Val) s₀ :=
  Always.mono_wp (atomicHistWP_refines_strong A) (tryUpdate_always_safety hpre hs)

end Safety

/-! ## 6. Liveness: Bounded Contention, Streett Fairness, Enabledness -/

section Liveness

variable {Val FState G : Type} {A : AtomicEnv Val FState G} {Rel : Val → Val → Prop}
  {init : Val} {f₀ : FState} {g₀ : G} {comm₀ : OneShotCommitter Val}

/-- Ranked loop invariant: the remaining contention budget is the rank. -/
def RankedInv (A : AtomicEnv Val FState G) (Rel : Val → Val → Prop) (init : Val)
    (f₀ : FState) (g₀ : G) (comm₀ : OneShotCommitter Val) (n : Nat) (prev : Val)
    (s : AtomicSt Val FState G) : Prop :=
  LoopInv A Rel init f₀ g₀ comm₀ prev s ∧ s.budget = n

/-- One iteration under bounded contention exits, or retries with a smaller budget. -/
theorem tryBody_dwp_ranked (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀) (n : Nat)
    (prev : Val) (s : AtomicSt Val FState G)
    (h : RankedInv A Rel init f₀ g₀ comm₀ n prev s) :
    DWP (atomicBudgetWP A) (tryBody prev)
      (Sum.elim (fun next s' => ∃ m, m < n ∧ RankedInv A Rel init f₀ g₀ comm₀ m next s')
        (CreusotPost A Rel init f₀ g₀ comm₀)) s := by
  obtain ⟨hl, hb⟩ := h
  refine DWP.vis ((budgetWP_call A prev _ s).2 ⟨loopInv_pre hpre hl, fun f' r hpost => ?_⟩)
  cases r with
  | none =>
    rw [tryCallK_none]
    exact DWP.vis ((budgetWP_drop A _ _).2 fun v hv =>
      ⟨fun _ hres => DWP.ret (loopInv_err_post hpre hl hpost hv s.budget hres),
       fun _ _ hres => DWP.ret (loopInv_err_post hpre hl hpost hv (s.budget - 1) hres)⟩)
  | some next =>
    rw [tryCallK_some]
    have hwin : ∀ b, casWin A prev next
        (fun o s' => DWP (atomicBudgetWP A) (tryCasK prev next o)
          (Sum.elim (fun next s' => ∃ m, m < n ∧ RankedInv A Rel init f₀ g₀ comm₀ m next s')
            (CreusotPost A Rel init f₀ g₀ comm₀)) s')
        { s with fst := f', cell := prev } b := fun b =>
      (casWin_iff A _ _ _ _ _).2 ⟨loopInv_unshot (s := s) hpre hl,
        loopInv_win_pre (s := s) hpre hl hpost, fun g' hg' => by
        rw [tryCasK_true]
        exact DWP.vis ((budgetWP_drop A _ _).2 fun v' hv' =>
          ⟨fun _ hres => DWP.ret (loopInv_ok_post hpre hl hpost hg' hv' b b hres),
           fun _ _ hres => DWP.ret (loopInv_ok_post hpre hl hpost hg' hv' b (b - 1) hres)⟩)⟩
    refine DWP.vis ((budgetWP_cas A prev next _ _).2 fun v hv =>
      ⟨fun hvc => ⟨fun hne => absurd (hvc.trans hl.2.1) hne, fun _ hpos => ?_, fun hve => ?_⟩,
        fun _ hpos => ⟨?_, fun hve => ?_⟩⟩)
    · have hpos' : 0 < s.budget := hpos
      rw [tryCasK_false]
      exact DWP.ret ⟨n - 1, by omega, loopInv_fail hpre hl hpost hv _,
        show s.budget - 1 = n - 1 by omega⟩
    · subst hve; exact hwin _
    · have hpos' : 0 < s.budget := hpos
      rw [tryCasK_false]
      exact DWP.ret ⟨n - 1, by omega, loopInv_fail hpre hl hpost hv _,
        show s.budget - 1 = n - 1 by omega⟩
    · subst hve; exact hwin _

/--
**Liveness under bounded contention (`DWP`)**: when interference and spurious
weak-CAS failures are bounded by the `Nat` budget, `tryUpdateLoop` terminates
with `Ok old` or `Err current` satisfying the full `creusot#2386` contract.
-/
theorem tryUpdate_dwp_ranked (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    {s₀ : AtomicSt Val FState G} (hs : InitSt init f₀ g₀ comm₀ s₀) :
    DWP (atomicBudgetWP A) (tryUpdateLoop Val) (CreusotPost A Rel init f₀ g₀ comm₀) s₀ :=
  DWP.vis ((budgetWP_load A _ s₀).2 fun _ hv =>
    ⟨fun _ => dwp_iter_ranked_lt tryBody (RankedInv A Rel init f₀ g₀ comm₀)
        (tryBody_dwp_ranked hpre) (n := s₀.budget)
        ⟨loopInv_of_init hpre hs hv s₀.budget, rfl⟩,
     fun _ _ => dwp_iter_ranked_lt tryBody (RankedInv A Rel init f₀ g₀ comm₀)
        (tryBody_dwp_ranked hpre) (n := s₀.budget - 1)
        ⟨loopInv_of_init hpre hs hv (s₀.budget - 1), rfl⟩⟩)

/--
**Strong-CAS unconditional termination under quiescence (`DWP`)**: when no
other thread modifies the cell (`A.rely a b → b = a`), strong `compare_exchange`
terminates in a single iteration with zero budget.
-/
theorem tryUpdate_strong_quiescent_dwp (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    (hq : ∀ a b, A.rely a b → b = a)
    {s₀ : AtomicSt Val FState G} (hs : InitSt init f₀ g₀ comm₀ s₀) :
    DWP (atomicStrongHistWP A) (tryUpdateLoop Val) (CreusotPost A Rel init f₀ g₀ comm₀) s₀ := by
  refine DWP.vis ((strongWP_load A _ s₀).2 fun v hv b => ?_)
  dsimp only [loadAns]
  have hl := loopInv_of_init hpre hs hv b
  rw [iter_tryBody_eq]
  refine DWP.vis ((strongWP_call A v _ _).2 ⟨loopInv_pre hpre hl, fun f' r hpost => ?_⟩)
  cases r with
  | none =>
    rw [tryCallK_none, retAfterDrop, vis_bind]
    refine DWP.vis ((strongWP_drop A _ _).2 fun v' hv' b' hres => ?_)
    rw [ret_bind, Sum.elim_inr]
    exact DWP.ret (loopInv_err_post hpre hl hpost hv' b' hres)
  | some next =>
    rw [tryCallK_some, vis_bind]
    refine DWP.vis ((strongWP_cas A v next _ _).2 fun v' hv' b' =>
      ⟨fun hne => absurd (hq _ _ hv') hne, fun hve => ?_⟩)
    have hunshot : ({ s₀ with cell := v, budget := b } : AtomicSt Val FState G).comm.shot_store =
        false := loopInv_unshot hpre hl
    have hwinpre : A.gc.pre ({ s₀ with cell := v, budget := b } : AtomicSt Val FState G).gst
        v next := loopInv_win_pre hpre hl hpost
    subst hve
    refine (casWin_iff A _ _ _ _ _).2 ⟨hunshot, hwinpre, fun g' hg' => ?_⟩
    rw [tryCasK_true, retAfterDrop, vis_bind]
    refine DWP.vis ((strongWP_drop A _ _).2 fun v'' hv'' b'' hres => ?_)
    rw [ret_bind, Sum.elim_inr]
    exact DWP.ret (loopInv_ok_post hpre hl hpost hg' hv'' b' b'' hres)

/-- Any `ExcludedMiracle` transformer refutes `DWP ... (fun _ _ => False)`. -/
theorem not_dwp_false {S : Type} {E : Effect.{0}} {R : Type} (ewp : StateEffectWP S E)
    [StateEffectWP.ExcludedMiracle ewp] (t : ITree E R) (s : S) :
    ¬ DWP ewp t (fun _ _ => False) s := by
  intro h
  refine DWP.induct (fun _ _ => False) ?_ h
  intro x s' hx
  cases hobs : x.observe <;> rw [hobs] at hx
  · exact hx
  · exact hx
  · exact StateEffectWP.ExcludedMiracle.no_miracle hx

/--
**Non-vacuity of `DWP` under `AtomicEnv.Realizable`**: no realizable
environment can satisfy `DWP ... (fun _ _ => False)` on `tryUpdateLoop`.
-/
theorem tryUpdate_nonvacuous_not_false (hR : A.Realizable) (s₀ : AtomicSt Val FState G) :
    ¬ DWP (atomicBudgetWP A) (tryUpdateLoop Val) (fun _ _ => False) s₀ ∧
      ¬ DWP (atomicHistWP A) (tryUpdateLoop Val) (fun _ _ => False) s₀ ∧
      ¬ DWP (atomicStrongHistWP A) (tryUpdateLoop Val) (fun _ _ => False) s₀ := by
  haveI := atomicBudgetWP_excludedMiracle hR
  haveI := atomicHistWP_excludedMiracle hR
  haveI := atomicStrongHistWP_excludedMiracle hR
  exact ⟨not_dwp_false _ _ _, not_dwp_false _ _ _, not_dwp_false _ _ _⟩

/-- **Liveness (`Eventually`)**: bounded contention eventually returns with the contract. -/
theorem tryUpdate_eventually_terminates (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    {s₀ : AtomicSt Val FState G} (hs : InitSt init f₀ g₀ comm₀ s₀)
    (Target : AtomicSt Val FState G → Prop) :
    Eventually (atomicBudgetWP A) Target (CreusotPost A Rel init f₀ g₀ comm₀)
      (tryUpdateLoop Val) s₀ :=
  eventually_of_dwp Target (tryUpdate_dwp_ranked hpre hs)

/-- Bounded contention: `Always` history safety and `DWP` termination together. -/
theorem tryUpdate_bounded_spec (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    {s₀ : AtomicSt Val FState G} (hs : InitSt init f₀ g₀ comm₀ s₀) :
    Always (atomicBudgetWP A) (HistInvSt A Rel init f₀) (CreusotPost A Rel init f₀ g₀ comm₀)
        (tryUpdateLoop Val) s₀ ∧
      DWP (atomicBudgetWP A) (tryUpdateLoop Val)
        (fun r s => HistInvSt A Rel init f₀ s ∧ CreusotPost A Rel init f₀ g₀ comm₀ r s) s₀ := by
  refine ⟨tryUpdate_budget_always hpre hs, ?_⟩
  have h := Until.and_always (tryUpdate_budget_always hpre hs).post_inv
    ((dwp_iff_until _ _ _ _).1 (tryUpdate_dwp_ranked hpre hs))
  exact (dwp_iff_until _ _ _ _).2
    (Until.mono (fun _ _ => trivial) (fun _ h => h.2) (fun _ _ h => h.1) h)

/-- Fairness edges: a weak CAS that wins. -/
def CasWon {Val S : Type} : (i : (AtomicCellE Val).I) → (AtomicCellE Val).O i → S → S → Prop
  | .call (.cas e d), o, _, _ => (casAns e d o).1 = true
  | _, _, _, _ => False

/-- Enabledness edges: a weak CAS is attempted (whatever its outcome). -/
def CasAttempt {Val S : Type} : (i : (AtomicCellE Val).I) → (AtomicCellE Val).O i → S → S → Prop
  | .call (.cas _ _), _, _, _ => True
  | _, _, _, _ => False

/-- Per-iteration fair retry obligation: every winning CAS commits to returning. -/
theorem tryBody_fairIter (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀) (prev : Val)
    (s : AtomicSt Val FState G) (hl : LoopInv A Rel init f₀ g₀ comm₀ prev s) :
    fairIter (atomicHistWP A) CasWon (LoopInv A Rel init f₀ g₀ comm₀)
      (CreusotPost A Rel init f₀ g₀ comm₀) false (tryBody prev) s := by
  refine (fairIter.vis_iff _ _ _ _ _ _ _ _).2 ((histWP_call A prev _ s).2
    ⟨loopInv_pre hpre hl, fun f' r hpost => Or.inr ⟨fun h => h, ?_⟩⟩)
  cases r with
  | none =>
    rw [tryCallK_none]
    exact (fairIter.vis_iff _ _ _ _ _ _ _ _).2 ((histWP_drop A _ _).2 fun v hv b hres =>
      Or.inr ⟨fun h => h, (fairIter.ret_inr_iff _ _ _ _ _ _ _).2
        (loopInv_err_post hpre hl hpost hv b hres)⟩)
  | some next =>
    rw [tryCallK_some]
    refine (fairIter.vis_iff _ _ _ _ _ _ _ _).2 ((histWP_cas A prev next _ _).2 fun v hv b =>
      ⟨Or.inr ⟨fun h => Bool.noConfusion h, ?_⟩, fun hve => ?_⟩)
    · rw [tryCasK_false]
      exact (fairIter.ret_inl_iff _ _ _ _ _ _ _).2 ⟨rfl, loopInv_fail hpre hl hpost hv b⟩
    · subst hve
      refine (casWin_iff A _ _ _ _ _).2 ⟨loopInv_unshot (s := s) hpre hl,
        loopInv_win_pre (s := s) hpre hl hpost, fun g' hg' => Or.inl ⟨rfl, ?_⟩⟩
      rw [tryCasK_true]
      exact DWP.vis ((histWP_drop A _ _).2 fun v' hv' b' hres =>
        DWP.ret (loopInv_ok_post hpre hl hpost hg' hv' b b' hres))

/--
**Streett liveness under CAS fairness**: along every path on which the
environment lets a weak CAS win infinitely often (`□◇ CasWon`), `tryUpdateLoop`
returns with the full `creusot#2386` contract — for any accepting edges.
-/
theorem tryUpdate_fairInfOften (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    {s₀ : AtomicSt Val FState G} (hs : InitSt init f₀ g₀ comm₀ s₀)
    (AccEdge : (i : (AtomicCellE Val).I) → (AtomicCellE Val).O i →
      AtomicSt Val FState G → AtomicSt Val FState G → Prop) :
    FairInfOften (atomicHistWP A) AccEdge CasWon (CreusotPost A Rel init f₀ g₀ comm₀)
      (tryUpdateLoop Val) s₀ :=
  FairInfOften.vis ((histWP_load A _ s₀).2 fun _ hv b =>
    FairInfOften.iter_fair tryBody (LoopInv A Rel init f₀ g₀ comm₀)
      (tryBody_fairIter hpre) (loopInv_of_init hpre hs hv b))

/-- **Co-Büchi termination**: finitely many unfair CAS rounds once `□◇ CasWon`. -/
theorem tryUpdate_coBuchi (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    {s₀ : AtomicSt Val FState G} (hs : InitSt init f₀ g₀ comm₀ s₀) :
    CoBuchi (atomicHistWP A) CasWon (CreusotPost A Rel init f₀ g₀ comm₀)
      (tryUpdateLoop Val) s₀ :=
  tryUpdate_fairInfOften hpre hs _

/-- Per-iteration enabledness: every non-exiting iteration attempts a weak CAS. -/
theorem tryBody_buchiProgress (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀) (prev : Val)
    (s : AtomicSt Val FState G) (hl : LoopInv A Rel init f₀ g₀ comm₀ prev s) :
    buchiProgress (atomicHistWP A) CasAttempt
      (Sum.elim (fun _ _ => False) (CreusotPost A Rel init f₀ g₀ comm₀))
      (InfOften (atomicHistWP A) CasAttempt
        (Sum.elim (LoopInv A Rel init f₀ g₀ comm₀) (CreusotPost A Rel init f₀ g₀ comm₀)))
      (tryBody prev) s := by
  refine (buchiProgress.vis_iff _ _ _ _ _ _ _).2 ((histWP_call A prev _ s).2
    ⟨loopInv_pre hpre hl, fun f' r hpost => Or.inr ?_⟩)
  cases r with
  | none =>
    rw [tryCallK_none]
    exact (buchiProgress.vis_iff _ _ _ _ _ _ _).2 ((histWP_drop A _ _).2 fun v hv b hres =>
      Or.inr ((buchiProgress.ret_iff _ _ _ _ _ _).2
        (loopInv_err_post hpre hl hpost hv b hres)))
  | some next =>
    rw [tryCallK_some]
    refine (buchiProgress.vis_iff _ _ _ _ _ _ _).2 ((histWP_cas A prev next _ _).2
      fun v hv b => ⟨Or.inl ⟨trivial, ?_⟩, fun hve => ?_⟩)
    · rw [tryCasK_false]; exact InfOften.ret (loopInv_fail hpre hl hpost hv b)
    · subst hve
      refine (casWin_iff A _ _ _ _ _).2 ⟨loopInv_unshot (s := s) hpre hl,
        loopInv_win_pre (s := s) hpre hl hpost, fun g' hg' => Or.inl ⟨trivial, ?_⟩⟩
      rw [tryCasK_true]
      exact InfOften.vis ((histWP_drop A _ _).2 fun v' hv' b' hres =>
        InfOften.ret (loopInv_ok_post hpre hl hpost hg' hv' b b' hres))

/--
**Enabledness (`InfOften CasAttempt`)**: every non-terminating run attempts a
weak CAS infinitely often, so CAS fairness cannot be satisfied vacuously by a
loop that never reaches the CAS.
-/
theorem tryUpdate_infOften_attemptCas (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    {s₀ : AtomicSt Val FState G} (hs : InitSt init f₀ g₀ comm₀ s₀) :
    InfOften (atomicHistWP A) CasAttempt (CreusotPost A Rel init f₀ g₀ comm₀)
      (tryUpdateLoop Val) s₀ :=
  InfOften.vis ((histWP_load A _ s₀).2 fun _ hv b =>
    InfOften.iter_progress tryBody (LoopInv A Rel init f₀ g₀ comm₀)
      (tryBody_buchiProgress hpre) (loopInv_of_init hpre hs hv b))

/-! ### 6.1 One-shot committer monitor (`FairBuchiSat`) -/

/--
Deterministic one-shot `Committer` monitor: `QState = Bool` (shot?). Only a
winning CAS moves the monitor, and only from `false` to `true`; the invariant
pins the monitor to the ghost committer and the history invariant.
-/
def committerSpec (A : AtomicEnv Val FState G) (Rel : Val → Val → Prop) (init : Val)
    (f₀ : FState) (g₀ : G) (comm₀ : OneShotCommitter Val) :
    BuchiSpec (AtomicSt Val FState G) Bool (AtomicCellE Val) (Except Val Val) where
  ewp := atomicHistWP A
  step q i o s s' q' := (CasWon i o s s' → q = false ∧ q' = true) ∧ (¬ CasWon i o s s' → q' = q)
  accept _ _ _ _ _ _ := False
  inv q s := HistInvSt A Rel init f₀ s ∧ q = s.comm.shot_store
  terminal q r s := CreusotPost A Rel init f₀ g₀ comm₀ r s ∧ q = s.comm.shot_store

/-- Monitor-product unfolding at the closure call. -/
private theorem committer_call_step (q : Bool) (x : Val) (o : (AtomicCellE Val).O (aCall x))
    (s s' : AtomicSt Val FState G) :
    (CasWon (aCall x) o s s' → q = false ∧ q = true) ∧ (¬ CasWon (aCall x) o s s' → q = q) :=
  ⟨fun h => False.elim h, fun _ => rfl⟩

theorem tryBody_fairIter_committer (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    (prev : Val) (qs : Bool × AtomicSt Val FState G)
    (hl : qs.1 = false ∧ LoopInv A Rel init f₀ g₀ comm₀ prev qs.2) :
    fairIter (committerSpec A Rel init f₀ g₀ comm₀).monitorWP
      ((committerSpec A Rel init f₀ g₀ comm₀).fairEdge (fun _ i o s s' _ => CasWon i o s s'))
      (fun prev qs => qs.1 = false ∧ LoopInv A Rel init f₀ g₀ comm₀ prev qs.2)
      (committerSpec A Rel init f₀ g₀ comm₀).terminalPost false (tryBody prev) qs := by
  obtain ⟨q, s⟩ := qs
  obtain ⟨hq, hl⟩ := hl
  subst hq
  have hunshot : s.comm.shot_store = false := loopInv_unshot hpre hl
  refine (fairIter.vis_iff _ _ _ _ _ _ _ _).2 ((BuchiSpec.monitorWP_wp _ _ _ _ _).2
    ((histWP_call A prev _ s).2
    ⟨loopInv_pre hpre hl, fun f' r hpost =>
      ⟨false, committer_call_step _ _ _ _ _, ⟨loopInv_call hpre hl hpost, hunshot.symm⟩,
        Or.inr ⟨fun h => h, ?_⟩⟩⟩))
  cases r with
  | none =>
    rw [tryCallK_none]
    refine (fairIter.vis_iff _ _ _ _ _ _ _ _).2 ((BuchiSpec.monitorWP_wp _ _ _ _ _).2
      ((histWP_drop A _ _).2 fun v hv b hres =>
        ⟨false, ⟨fun h => False.elim h, fun _ => rfl⟩,
          ⟨loopInv_drop_inv hpre (loopInv_call hpre hl hpost) hv b, hunshot.symm⟩,
          Or.inr ⟨fun h => h, ?_⟩⟩))
    exact (fairIter.ret_inr_iff _ _ _ _ _ _ _).2
      ⟨loopInv_err_post hpre hl hpost hv b hres, hunshot.symm⟩
  | some next =>
    rw [tryCallK_some]
    refine (fairIter.vis_iff _ _ _ _ _ _ _ _).2 ((BuchiSpec.monitorWP_wp _ _ _ _ _).2
      ((histWP_cas A prev next _ _).2 fun v hv b =>
        ⟨⟨false, ⟨fun h => Bool.noConfusion h, fun _ => rfl⟩,
            ⟨histInvSt_of_loopInv hpre (loopInv_fail hpre hl hpost hv b), hunshot.symm⟩,
            Or.inr ⟨fun h => Bool.noConfusion h, ?_⟩⟩, fun hve => ?_⟩))
    · rw [tryCasK_false]
      exact (fairIter.ret_inl_iff _ _ _ _ _ _ _).2
        ⟨rfl, rfl, loopInv_fail hpre hl hpost hv b⟩
    · subst hve
      refine (casWin_iff A _ _ _ _ _).2 ⟨hunshot, loopInv_win_pre (s := s) hpre hl hpost,
        fun g' hg' => ⟨true, ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd rfl h⟩,
          ⟨loopInv_win_inv hpre hl hpost g' b, rfl⟩, Or.inl ⟨rfl, ?_⟩⟩⟩
      rw [tryCasK_true]
      refine DWP.vis ((BuchiSpec.monitorWP_wp _ _ _ _ _).2 ((histWP_drop A _ _).2
        fun v' hv' b' hres => ⟨true, ⟨fun h => False.elim h, fun _ => rfl⟩,
          ⟨loopInv_drop_inv hpre (loopInv_win_inv hpre hl hpost g' b) hv' b', rfl⟩,
          DWP.ret ⟨?_, rfl⟩⟩))
      exact loopInv_ok_post hpre hl hpost hg' hv' b b' hres

/--
**One-shot committer `FairBuchiSat`**: the deterministic committer monitor
accepts `tryUpdateLoop` under CAS fairness — the history invariant holds at
every step, the committer moves `false ↦ true` at most once (on the winning
CAS), and every return satisfies the `creusot#2386` contract with the monitor
agreeing with the ghost `shot_store`.
-/
theorem tryUpdate_fairBuchiSat_committer (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    {s₀ : AtomicSt Val FState G} (hs : InitSt init f₀ g₀ comm₀ s₀) :
    FairBuchiSat (committerSpec A Rel init f₀ g₀ comm₀) (fun _ i o s s' _ => CasWon i o s s')
      (tryUpdateLoop Val) false s₀ := by
  have hunshot : s₀.comm.shot_store = false := by rw [hs.2.2.1]; exact hpre.comm_unshot
  refine (fairBuchiSat_iff_fairInfOften _ _ _ _ _).2 ⟨⟨histInvSt_of_init hpre hs,
    hunshot.symm⟩, ?_⟩
  refine FairInfOften.vis ((BuchiSpec.monitorWP_wp _ _ _ _ _).2 ((histWP_load A _ s₀).2
    fun v hv b => ⟨false, ⟨fun h => False.elim h, fun _ => rfl⟩,
      ⟨histInvSt_of_loopInv hpre (loopInv_of_init hpre hs hv b), hunshot.symm⟩, ?_⟩))
  exact FairInfOften.iter_fair tryBody
    (fun (prev : Val) (qs : Bool × AtomicSt Val FState G) =>
      qs.1 = false ∧ LoopInv A Rel init f₀ g₀ comm₀ prev qs.2)
    (tryBody_fairIter_committer hpre) (init := loadAns v)
    (s := (false, { s₀ with cell := v, budget := b })) ⟨rfl, loopInv_of_init hpre hs hv b⟩

end Liveness

/-! ### 6.2 Operational adequacy: strong fairness over event traces -/

section Trace

variable {Val : Type}

/-- Trace-level `try_update` postcondition: the run ends in `cas✓; drop` or `f = None; drop`. -/
def TracePost : Except Val Val → List (Event (AtomicCellE Val)) → Prop
  | .ok old, tr => ∃ new v pre,
      tr = pre ++ [⟨aCas old new, casOut old new true v⟩, ⟨aDrop, PUnit.unit⟩]
  | .error cur, tr => ∃ pre, tr = pre ++ [⟨aCall cur, callOut cur none⟩, ⟨aDrop, PUnit.unit⟩]

theorem traceWP_iff (i : (AtomicCellE Val).I)
    (K : (AtomicCellE Val).O i → List (Event (AtomicCellE Val)) → Prop)
    (tr : List (Event (AtomicCellE Val))) :
    (eventTraceWP (AtomicCellE Val)).wp i K tr ↔ ∀ o, K o (tr ++ [⟨i, o⟩]) :=
  ⟨fun h => h.2, fun h => ⟨fun hf => hf, h⟩⟩

private theorem trace_tail {α : Type} (tr : List α) (a b : α) :
    tr ++ [a] ++ [b] = tr ++ [a, b] := List.append_assoc _ _ _

theorem tryBody_trace_buchiProgress (prev : Val) (tr : List (Event (AtomicCellE Val))) :
    buchiProgress (eventTraceWP (AtomicCellE Val)) CasAttempt
      (Sum.elim (fun _ _ => False) TracePost)
      (InfOften (eventTraceWP (AtomicCellE Val)) CasAttempt
        (Sum.elim (fun _ _ => True) TracePost))
      (tryBody prev) tr := by
  refine (buchiProgress.vis_iff _ _ _ _ _ _ _).2 ((traceWP_iff _ _ _).2
    (forall_callOut prev _ fun r => Or.inr ?_))
  cases r with
  | none =>
    rw [tryCallK_none]
    exact (buchiProgress.vis_iff _ _ _ _ _ _ _).2 ((traceWP_iff _ _ _).2 fun _ =>
      Or.inr ((buchiProgress.ret_iff _ _ _ _ _ _).2 ⟨tr, trace_tail _ _ _⟩))
  | some next =>
    rw [tryCallK_some]
    refine (buchiProgress.vis_iff _ _ _ _ _ _ _).2 ((traceWP_iff _ _ _).2
      (forall_casOut prev next _ fun b v => Or.inl ⟨trivial, ?_⟩))
    cases b with
    | false => rw [tryCasK_false]; exact InfOften.ret trivial
    | true =>
      rw [tryCasK_casOut_true]
      exact InfOften.vis ((traceWP_iff _ _ _).2 fun _ =>
        InfOften.ret ⟨next, v, tr ++ [⟨aCall prev, callOut prev (some next)⟩], trace_tail _ _ _⟩)

theorem tryBody_trace_fairIter (prev : Val) (tr : List (Event (AtomicCellE Val))) :
    fairIter (eventTraceWP (AtomicCellE Val)) CasWon (fun _ _ => True) TracePost false
      (tryBody prev) tr := by
  refine (fairIter.vis_iff _ _ _ _ _ _ _ _).2 ((traceWP_iff _ _ _).2
    (forall_callOut prev _ fun r => Or.inr ⟨fun h => h, ?_⟩))
  cases r with
  | none =>
    rw [tryCallK_none]
    exact (fairIter.vis_iff _ _ _ _ _ _ _ _).2 ((traceWP_iff _ _ _).2 fun _ =>
      Or.inr ⟨fun h => h, (fairIter.ret_inr_iff _ _ _ _ _ _ _).2 ⟨tr, trace_tail _ _ _⟩⟩)
  | some next =>
    rw [tryCallK_some]
    refine (fairIter.vis_iff _ _ _ _ _ _ _ _).2 ((traceWP_iff _ _ _).2
      (forall_casOut prev next _ fun b v => ?_))
    cases b with
    | false =>
      rw [tryCasK_false]
      exact Or.inr ⟨fun h => Bool.noConfusion h,
        (fairIter.ret_inl_iff _ _ _ _ _ _ _).2 ⟨rfl, trivial⟩⟩
    | true =>
      rw [tryCasK_casOut_true]
      exact Or.inl ⟨rfl, DWP.vis ((traceWP_iff _ _ _).2 fun _ =>
        DWP.ret ⟨next, v, tr ++ [⟨aCall prev, callOut prev (some next)⟩], trace_tail _ _ _⟩)⟩

/-- Every infinite run of `tryUpdateLoop` attempts a weak CAS infinitely often. -/
theorem tryUpdate_trace_infOften (tr₀ : List (Event (AtomicCellE Val))) :
    InfOften (eventTraceWP (AtomicCellE Val)) CasAttempt TracePost (tryUpdateLoop Val) tr₀ :=
  InfOften.vis ((traceWP_iff _ _ _).2 fun _ =>
    InfOften.iter_progress tryBody (fun _ _ => True)
      (fun prev tr _ => tryBody_trace_buchiProgress prev tr) trivial)

/-- Once a weak CAS wins infinitely often, `tryUpdateLoop` must return (`CoBuchi`). -/
theorem tryUpdate_trace_coBuchi (tr₀ : List (Event (AtomicCellE Val))) :
    CoBuchi (eventTraceWP (AtomicCellE Val)) CasWon TracePost (tryUpdateLoop Val) tr₀ :=
  FairInfOften.vis ((traceWP_iff _ _ _).2 fun _ =>
    FairInfOften.iter_fair tryBody (fun _ _ => True)
      (fun prev tr _ => tryBody_trace_fairIter prev tr) trivial)

/--
**Operational termination under strong CAS fairness**
(`trace_strongFair_terminates` over `eventTraceWP`): against every deterministic
environment strategy `σ` (choosing interference, CAS outcomes, spurious
failures, and closure answers) that is strongly fair — on every infinite run,
infinitely many CAS attempts imply infinitely many winning CASes —
`tryUpdateLoop` reaches a `.ret r` whose trace ends in `cas✓; drop` or
`f = None; drop`.
-/
theorem tryUpdate_trace_strongFair_terminates (σ : EnvStrategy (AtomicCellE Val))
    (tr₀ : List (Event (AtomicCellE Val)))
    (h_sf : ∀ ev : Stream' (Event (AtomicCellE Val)),
      InfRunWithStrategy σ tr₀ (tryUpdateLoop Val) ev →
      (∀ k, ∃ n, k ≤ n ∧
        CasAttempt (ev n).req (ev n).ans (tr₀ ++ takePrefix ev n)
          (tr₀ ++ takePrefix ev (n + 1))) →
      (∀ k, ∃ n, k ≤ n ∧
        CasWon (ev n).req (ev n).ans (tr₀ ++ takePrefix ev n)
          (tr₀ ++ takePrefix ev (n + 1)))) :
    ∃ tr r, RetWithStrategy σ tr₀ (tryUpdateLoop Val) tr r ∧ TracePost r (tr₀ ++ tr) :=
  trace_strongFair_terminates (tryUpdate_trace_infOften tr₀) (tryUpdate_trace_coBuchi tr₀) σ
    h_sf

end Trace

/-! ### 6.3 Non-miraculous prophecy semantics & prophecy elimination -/

section Prophetic

variable {Val RState G : Type}

/--
Prophetic lifting of a runtime `FnMutSpec` on `RState` to `RState × RState`
(current runtime closure state paired with a fixed prophetic final value `fin`):
`hist_inv` and `post_mut` preserve `fin`, and `resolve (cur, fin) := cur = fin`.
-/
def propheticSpec (base : FnMutSpec RState Val Val) : FnMutSpec (RState × RState) Val Val where
  hist_inv p q := base.hist_inv p.1 q.1 ∧ p.2 = q.2
  hist_inv_laws := ⟨fun _ => ⟨base.hist_inv_laws.refl _, rfl⟩,
    fun hab hbc => ⟨base.hist_inv_laws.trans hab.1 hbc.1, hab.2.trans hbc.2⟩⟩
  pre p x := base.pre p.1 x
  post_mut p x q r := base.post_mut p.1 x q.1 r ∧ q.2 = p.2
  step_hist_inv _ _ _ _ h := ⟨base.step_hist_inv _ _ _ _ h.1, h.2.symm⟩
  resolve p := p.1 = p.2

/-- Prophetic lifting of a runtime `AtomicEnv`. -/
def propheticEnv (A : AtomicEnv Val RState G) : AtomicEnv Val (RState × RState) G :=
  ⟨A.rely, propheticSpec A.fSpec, A.gc⟩

/-- Attach a prophetic final value `fin` to a runtime state `s`. -/
def AtomicSt.withProphecy (s : AtomicSt Val RState G) (fin : RState) :
    AtomicSt Val (RState × RState) G :=
  ⟨s.cell, (s.fst, fin), s.comm, s.fires, s.gst, s.budget⟩

/-- Erase the prophetic component, recovering the runtime state. -/
def AtomicSt.eraseProphecy (ps : AtomicSt Val (RState × RState) G) : AtomicSt Val RState G :=
  ⟨ps.cell, ps.fst.1, ps.comm, ps.fires, ps.gst, ps.budget⟩

@[simp] theorem AtomicSt.erase_withProphecy (s : AtomicSt Val RState G) (fin : RState) :
    (s.withProphecy fin).eraseProphecy = s := rfl

/--
Auxiliary transformer tracking whether `dropF` has fired (`d = false` before
drop, `d = true` after drop). In state `true` no further `vis` is permitted.
-/
def terminalDropWP (Val : Type) : StateEffectWP Bool (AtomicCellE Val) where
  wp
    | .call .dropF, K, d => d = false ∧ ∀ o, K o true
    | .call .load, K, d => d = false ∧ ∀ o, K o false
    | .call (.cas _ _), K, d => d = false ∧ ∀ o, K o false
    | .call (.callF _), K, d => d = false ∧ ∀ o, K o false
    | .call .recv, K, d => d = false ∧ ∀ o, K o false
  mono {i} _ _ _ h hw :=
    match i with
    | .call .dropF => ⟨hw.1, fun o => h o true (hw.2 o)⟩
    | .call .load => ⟨hw.1, fun o => h o false (hw.2 o)⟩
    | .call (.cas _ _) => ⟨hw.1, fun o => h o false (hw.2 o)⟩
    | .call (.callF _) => ⟨hw.1, fun o => h o false (hw.2 o)⟩
    | .call .recv => ⟨hw.1, fun o => h o false (hw.2 o)⟩

/-- Every `dropF` step of `t` is terminal: no further effects occur after `dropF`. -/
def TerminalDrop {R : Type} (t : ITree (AtomicCellE Val) R) : Prop :=
  DWLP (terminalDropWP Val) t (fun _ _ => True) false

/-- `tryUpdateLoop` satisfies `TerminalDrop` (its only `dropF` is `retAfterDrop`). -/
theorem tryUpdateLoop_terminalDrop (Val : Type) : TerminalDrop (tryUpdateLoop Val) := by
  refine (DWLP.vis_iff _ _ _ _ _).2 ⟨rfl, fun o => ?_⟩
  refine DWLP.iter_invariant tryBody (fun _ d => d = false) (fun prev d hd => ?_) rfl
  subst hd
  refine (DWLP.vis_iff _ _ _ _ _).2 ⟨rfl, forall_callOut prev _ fun r => ?_⟩
  cases r with
  | none =>
    rw [tryCallK_none]
    exact (DWLP.vis_iff _ _ _ _ _).2 ⟨rfl, fun _ => (DWLP.ret_iff _ _ _ _).2 trivial⟩
  | some next =>
    rw [tryCallK_some]
    refine (DWLP.vis_iff _ _ _ _ _).2 ⟨rfl, forall_casOut prev next _ fun b v => ?_⟩
    cases b with
    | false => rw [tryCasK_false]; exact (DWLP.ret_iff _ _ _ _).2 rfl
    | true =>
      rw [tryCasK_casOut_true]
      exact (DWLP.vis_iff _ _ _ _ _).2 ⟨rfl, fun _ => (DWLP.ret_iff _ _ _ _).2 trivial⟩

private theorem noVis_dwp_transfer {S₁ S₂ R : Type} {ewp₁ : StateEffectWP S₁ (AtomicCellE Val)}
    {ewp₂ : StateEffectWP S₂ (AtomicCellE Val)} {Q₁ : R → S₁ → Prop} {Q₂ : R → S₂ → Prop}
    {t : ITree (AtomicCellE Val) R} {s₁ : S₁} {s₂ : S₂}
    (hnv : DWLP (terminalDropWP Val) t (fun _ _ => True) true)
    (h : DWP ewp₁ t Q₁ s₁) (himp : ∀ r, Q₁ r s₁ → Q₂ r s₂) : DWP ewp₂ t Q₂ s₂ := by
  refine DWP.induct (fun x st => st = s₁ → DWLP (terminalDropWP Val) x (fun _ _ => True) true →
    DWP ewp₂ x Q₂ s₂) ?_ h rfl hnv
  intro x st hx hst hnv'
  subst hst
  cases hobs : x.observe with
  | ret r =>
    rw [hobs] at hx
    exact of_observe_ret hobs (himp r hx)
  | tau x' =>
    rw [hobs] at hx
    have hnv'' : DWLP (terminalDropWP Val) x' (fun _ _ => True) true := by
      rw [DWLP.unfold_eq, hobs] at hnv'; exact hnv'
    exact of_observe_tau hobs (hx rfl hnv'')
  | vis i k =>
    rw [DWLP.unfold_eq, hobs] at hnv'
    cases i with
    | call req => cases req <;> exact Bool.noConfusion hnv'.1
where
  of_observe_ret {S : Type} {E : Effect.{0}} {R : Type} {ewp : StateEffectWP S E}
      {Q : R → S → Prop} {x : ITree E R} {r : R} {s : S}
      (hobs : x.observe = .ret r) (hq : Q r s) : DWP ewp x Q s := by
    rw [DWP.unfold_eq, hobs]; exact hq
  of_observe_tau {S : Type} {E : Effect.{0}} {R : Type} {ewp : StateEffectWP S E}
      {Q : R → S → Prop} {x x' : ITree E R} {s : S}
      (hobs : x.observe = .tau x') (hd : DWP ewp x' Q s) : DWP ewp x Q s := by
    rw [DWP.unfold_eq, hobs]; exact hd

private theorem noVis_always_transfer {S₁ S₂ R : Type} {ewp₁ : StateEffectWP S₁ (AtomicCellE Val)}
    {ewp₂ : StateEffectWP S₂ (AtomicCellE Val)} {Inv₁ : S₁ → Prop} {Inv₂ : S₂ → Prop}
    {Q₁ : R → S₁ → Prop} {Q₂ : R → S₂ → Prop}
    {t : ITree (AtomicCellE Val) R} {s₁ : S₁} {s₂ : S₂}
    (hnv : DWLP (terminalDropWP Val) t (fun _ _ => True) true)
    (h : Always ewp₁ Inv₁ Q₁ t s₁)
    (hinv : Inv₁ s₁ → Inv₂ s₂) (himp : ∀ r, Q₁ r s₁ → Q₂ r s₂) :
    Always ewp₂ Inv₂ Q₂ t s₂ := by
  refine Always.coinduct (fun x st => st = s₂ ∧ DWLP (terminalDropWP Val) x (fun _ _ => True) true ∧
    Always ewp₁ Inv₁ Q₁ x s₁) ?_ ⟨rfl, hnv, h⟩
  rintro x st ⟨rfl, hnv', ha⟩
  refine ⟨hinv ha.inv, ?_⟩
  cases hobs : x.observe with
  | ret r =>
    rw [Always.unfold_eq, hobs] at ha
    exact himp r ha.2
  | tau x' =>
    rw [Always.unfold_eq, hobs] at ha
    rw [DWLP.unfold_eq, hobs] at hnv'
    exact ⟨rfl, hnv', ha.2⟩
  | vis i k =>
    rw [DWLP.unfold_eq, hobs] at hnv'
    cases i with
    | call req => cases req <;> exact Bool.noConfusion hnv'.1

/--
**Prophecy Elimination (`DWP`, non-miraculous soundness)**: even though fixing a
single inconsistent prophecy `fin` makes assume-style `dropF` miraculous,
proving the prophetic `DWP` contract universally over **all** prophecies
`∀ fin` soundly eliminates into the **non-miraculous, `ExcludedMiracle`**
runtime transformer `atomicBudgetWP A` (binding `fin` to the actual final
runtime state `s.fst` upon return) for every `TerminalDrop` program (including
`tryUpdateLoop`).
-/
theorem prophecy_elimination_dwp {A : AtomicEnv Val RState G} {R : Type}
    {t : ITree (AtomicCellE Val) R} (htd : TerminalDrop t)
    {Q : R → RState → AtomicSt Val RState G → Prop}
    {s₀ : AtomicSt Val RState G}
    (hall : ∀ fin, DWP (atomicBudgetWP (propheticEnv A)) t
      (fun r ps => Q r ps.fst.2 ps.eraseProphecy) (s₀.withProphecy fin)) :
    DWP (atomicBudgetWP A) t (fun r s => Q r s.fst s) s₀ := by
  refine DWP.induct (fun x ps => ∀ (s : AtomicSt Val RState G) (fin₀ : RState),
      ps = s.withProphecy fin₀ → TerminalDrop x →
      (∀ fin, DWP (atomicBudgetWP (propheticEnv A)) x
        (fun r ps' => Q r ps'.fst.2 ps'.eraseProphecy) (s.withProphecy fin)) →
      DWP (atomicBudgetWP A) x (fun r s' => Q r s'.fst s') s)
    ?_ (hall s₀.fst) s₀ s₀.fst rfl htd hall
  intro x ps hx s fin₀ hps htd' hall'
  subst hps
  rw [DWP.unfold_eq]
  cases hobs : x.observe with
  | ret r =>
    have hr := hall' s.fst
    rw [DWP.unfold_eq, hobs] at hr
    exact hr
  | tau x' =>
    rw [hobs] at hx
    have htd'' : TerminalDrop x' := by rw [TerminalDrop, DWLP.unfold_eq, hobs] at htd'; exact htd'
    exact hx s fin₀ rfl htd'' fun fin => by
      have hf := hall' fin; rw [DWP.unfold_eq, hobs] at hf; exact hf
  | vis i k =>
    rw [hobs] at hx
    have htd'' : (terminalDropWP Val).wp i
        (fun o d => DWLP (terminalDropWP Val) (k o) (fun _ _ => True) d) false := by
      rw [TerminalDrop, DWLP.unfold_eq, hobs] at htd'; exact htd'
    have hstep : ∀ fin, (atomicBudgetWP (propheticEnv A)).wp i
        (fun o ps' => DWP (atomicBudgetWP (propheticEnv A)) (k o)
          (fun r ps'' => Q r ps''.fst.2 ps''.eraseProphecy) ps') (s.withProphecy fin) := by
      intro fin; have hf := hall' fin; rw [DWP.unfold_eq, hobs] at hf; exact hf
    cases i with
    | call req =>
      cases req with
      | load =>
        intro v hv
        refine ⟨fun he => (hx v hv).1 he { s with cell := v } fin₀ rfl (htd''.2 v)
            fun fin => ((hstep fin) v hv).1 he,
          fun hne hb => (hx v hv).2 hne hb { s with cell := v, budget := s.budget - 1 } fin₀ rfl
            (htd''.2 v) fun fin => ((hstep fin) v hv).2 hne hb⟩
      | cas e d =>
        intro v hv
        refine ⟨fun hc =>
          ⟨fun hne => ((hx v hv).1 hc).1 hne { s with cell := v } fin₀ rfl (htd''.2 (false, v))
              fun fin => (((hstep fin) v hv).1 hc).1 hne,
           fun he hb => ((hx v hv).1 hc).2.1 he hb { s with cell := v, budget := s.budget - 1 }
              fin₀ rfl (htd''.2 (false, v)) fun fin => (((hstep fin) v hv).1 hc).2.1 he hb,
           fun he =>
            let hwin := ((hx v hv).1 hc).2.2 he
            ⟨hwin.1, hwin.2.1, fun g' hg' => hwin.2.2 g' hg'
              (({ s with cell := v } : AtomicSt Val RState G).commit e d g' s.budget) fin₀ rfl
              (htd''.2 (true, e)) fun fin => ((((hstep fin) v hv).1 hc).2.2 he).2.2 g' hg'⟩⟩,
          fun hc hb =>
            ⟨((hx v hv).2 hc hb).1 { s with cell := v, budget := s.budget - 1 } fin₀ rfl
                (htd''.2 (false, v)) fun fin => (((hstep fin) v hv).2 hc hb).1,
             fun he =>
              let hwin := ((hx v hv).2 hc hb).2 he
              ⟨hwin.1, hwin.2.1, fun g' hg' => hwin.2.2 g' hg'
                (({ s with cell := v } : AtomicSt Val RState G).commit e d g' (s.budget - 1))
                fin₀ rfl (htd''.2 (true, e))
                fun fin => ((((hstep fin) v hv).2 hc hb).2 he).2.2 g' hg'⟩⟩⟩
      | callF arg =>
        refine ⟨hx.1, fun f' r hpost =>
          hx.2 (f', fin₀) r ⟨hpost, rfl⟩ { s with fst := f' } fin₀ rfl (htd''.2 r)
            fun fin => (hstep fin).2 (f', fin) r ⟨hpost, rfl⟩⟩
      | dropF =>
        intro v hv
        refine ⟨fun he _ => ?_, fun hne hb _ => ?_⟩
        · have hres := ((hstep s.fst) v hv).1 he rfl
          exact noVis_dwp_transfer (htd''.2 PUnit.unit) hres (fun _ hq => hq)
        · have hres := ((hstep s.fst) v hv).2 hne hb rfl
          exact noVis_dwp_transfer (htd''.2 PUnit.unit) hres (fun _ hq => hq)
      | recv =>
        intro b
        exact hx b { s with comm := .fresh s.cell, fires := 0, budget := b } fin₀ rfl
          (htd''.2 PUnit.unit) fun fin => (hstep fin) b

/--
**Prophecy Elimination (`Always`, unbounded contention)**: proving a prophetic
`Always` safety contract universally over `∀ fin` soundly eliminates into the
non-miraculous runtime transformer `atomicHistWP A` for every `TerminalDrop`
program (including `tryUpdateLoop`).
-/
theorem prophecy_elimination_always {A : AtomicEnv Val RState G} {R : Type}
    {t : ITree (AtomicCellE Val) R} (htd : TerminalDrop t)
    {Inv : AtomicSt Val RState G → Prop}
    {Q : R → RState → AtomicSt Val RState G → Prop}
    {s₀ : AtomicSt Val RState G}
    (hall : ∀ fin, Always (atomicHistWP (propheticEnv A))
      (fun ps => Inv ps.eraseProphecy)
      (fun r ps => Q r ps.fst.2 ps.eraseProphecy) t (s₀.withProphecy fin)) :
    Always (atomicHistWP A) Inv (fun r s => Q r s.fst s) t s₀ := by
  refine Always.coinduct (fun x s =>
      (TerminalDrop x ∧ ∀ fin, Always (atomicHistWP (propheticEnv A))
        (fun ps => Inv ps.eraseProphecy)
        (fun r ps => Q r ps.fst.2 ps.eraseProphecy) x (s.withProphecy fin)) ∨
      Always (atomicHistWP A) Inv (fun r s' => Q r s'.fst s') x s)
    ?_ (Or.inl ⟨htd, hall⟩)
  rintro x s (⟨htd', hall'⟩ | ha)
  · refine ⟨(hall' s.fst).inv, ?_⟩
    cases hobs : x.observe with
    | ret r =>
      have hf := hall' s.fst
      rw [Always.unfold_eq, hobs] at hf
      exact hf.2
    | tau x' =>
      have htd'' : TerminalDrop x' := by rw [TerminalDrop, DWLP.unfold_eq, hobs] at htd'; exact htd'
      refine Or.inl ⟨htd'', fun fin => ?_⟩
      have hf := hall' fin; rw [Always.unfold_eq, hobs] at hf; exact hf.2
    | vis i k =>
      have htd'' : (terminalDropWP Val).wp i
          (fun o d => DWLP (terminalDropWP Val) (k o) (fun _ _ => True) d) false := by
        rw [TerminalDrop, DWLP.unfold_eq, hobs] at htd'; exact htd'
      have hstep : ∀ fin, (atomicHistWP (propheticEnv A)).wp i
          (fun o ps' => Always (atomicHistWP (propheticEnv A))
            (fun ps => Inv ps.eraseProphecy)
            (fun r ps'' => Q r ps''.fst.2 ps''.eraseProphecy) (k o) ps') (s.withProphecy fin) := by
        intro fin; have hf := hall' fin; rw [Always.unfold_eq, hobs] at hf; exact hf.2
      cases i with
      | call req =>
        cases req with
        | load =>
          intro v hv b
          exact Or.inl ⟨htd''.2 v, fun fin => (hstep fin) v hv b⟩
        | cas e d =>
          intro v hv b
          refine ⟨Or.inl ⟨htd''.2 (false, v), fun fin => ((hstep fin) v hv b).1⟩, fun he => ?_⟩
          have hw₀ := ((hstep s.fst) v hv b).2 he
          exact ⟨hw₀.1, hw₀.2.1, fun g' hg' =>
            Or.inl ⟨htd''.2 (true, e), fun fin => (((hstep fin) v hv b).2 he).2.2 g' hg'⟩⟩
        | callF arg =>
          refine ⟨(hstep s.fst).1, fun f' r hpost =>
            Or.inl ⟨htd''.2 r, fun fin => (hstep fin).2 (f', fin) r ⟨hpost, rfl⟩⟩⟩
        | dropF =>
          intro v hv b _
          have hdrop := (hstep s.fst) v hv b rfl
          exact Or.inr (noVis_always_transfer (htd''.2 PUnit.unit) hdrop id (fun _ hq => hq))
        | recv =>
          intro b
          exact Or.inl ⟨htd''.2 PUnit.unit, fun fin => (hstep fin) b⟩
  · refine ⟨ha.inv, ?_⟩
    cases hobs : x.observe with
    | ret r => rw [Always.unfold_eq, hobs] at ha; exact ha.2
    | tau x' => rw [Always.unfold_eq, hobs] at ha; exact Or.inr ha.2
    | vis i k =>
      rw [Always.unfold_eq, hobs] at ha
      exact (atomicHistWP A).mono (fun _ _ hx => Or.inr hx) ha.2

end Prophetic

/-! ## 7. A `#4162` Diverging `-> !` Ticket Service Composing `tryUpdateLoop` -/

section Service

/-- Stateless ticket closure `|x| Some(x + 1)`. -/
def ticketSpec : FnMutSpec PUnit Nat Nat where
  hist_inv _ _ := True
  hist_inv_laws := ⟨fun _ => trivial, fun _ _ => trivial⟩
  pre _ _ := True
  post_mut _ x _ r := r = some (x + 1)
  step_hist_inv _ _ _ _ _ := trivial
  resolve _ := True

/-- Trivial ghost callback. -/
def trivialGC : GhostCommit Nat PUnit := ⟨fun _ _ _ => True, fun _ _ _ _ => True⟩

/-- Monotone ticket counter environment: interference only increments. -/
def ticketEnv : AtomicEnv Nat PUnit PUnit := ⟨(· ≤ ·), ticketSpec, trivialGC⟩

/-- Each service request runs one fresh `try_update` with the ticket closure. -/
theorem ticket_pre (c : Nat) :
    TryUpdatePre ticketEnv (· ≤ ·) c PUnit.unit PUnit.unit (.fresh c) where
  cellInv := AtomicHistInv.nat_le
  closure_pre _ _ _ _ := trivial
  closure_step _ x _ n _ h _ := by
    have h' : some n = some (x + 1) := h
    cases h'; exact ⟨Nat.le_succ x, trivial⟩
  rely_sound _ _ h := h
  comm_unshot := rfl

theorem ticketEnv_realizable : ticketEnv.Realizable where
  rely_refl := Nat.le_refl
  post_mut_total _ x _ := ⟨PUnit.unit, some (x + 1), rfl⟩
  gc_post_total _ _ _ _ := ⟨PUnit.unit, trivial⟩
  resolve_total _ := trivial

instance : StateEffectWP.ExcludedMiracle (atomicBudgetWP ticketEnv) :=
  atomicBudgetWP_excludedMiracle ticketEnv_realizable

/-- One service round: accept a request, then `try_update` the ticket counter. -/
def serviceBody (n : Nat) : ITree (AtomicCellE Nat) Nat :=
  ITree.vis aRecv (fun _ => tryUpdateLoop Nat >>= fun _ => ITree.ret (n + 1))

/-- `fn ticket_service(..) -> ! { loop { serve_one() } }`. -/
def ticketService (n₀ : Nat) : ITree (AtomicCellE Nat) PEmpty.{1} :=
  divergingLoop serviceBody n₀

/-- Service safety invariant: monotone ticket counter and one-shot per-request committer. -/
def SvcAlwaysInv (c₀ : Nat) (s : AtomicSt Nat PUnit PUnit) : Prop :=
  c₀ ≤ s.cell ∧ s.fires ≤ 1 ∧ (s.comm.shot_store = true ↔ s.fires = 1)

/-- Accepting edge of the ticket service: a winning CAS strictly advances the counter
and fires the fresh one-shot committer `false ↦ true`. -/
def TicketCommit : (i : (AtomicCellE Nat).I) → (AtomicCellE Nat).O i →
    AtomicSt Nat PUnit PUnit → AtomicSt Nat PUnit PUnit → Prop :=
  fun i o s s' => CasWon i o s s' ∧ s.cell < s'.cell ∧
    s.comm.shot_store = false ∧ s'.comm.shot_store = true

/-- Ticket monotonicity and one-shot committer discipline hold across every round. -/
theorem serviceBody_always (c₀ n : Nat) (s : AtomicSt Nat PUnit PUnit) (h : SvcAlwaysInv c₀ s) :
    Always (atomicBudgetWP ticketEnv) (SvcAlwaysInv c₀) (fun _ s => SvcAlwaysInv c₀ s)
      (serviceBody n) s := by
  refine Always.vis h ((budgetWP_recv ticketEnv _ s).2 fun b => Always.bind ?_)
  have hreq := tryUpdate_budget_always (ticket_pre s.cell)
    (s₀ := { s with comm := .fresh s.cell, fires := 0, budget := b }) ⟨rfl, rfl, rfl, rfl, rfl⟩
  exact Always.mono (fun s' hi => ⟨Nat.le_trans h.1 hi.1, hi.2.2⟩)
    (fun _ s' hq => Always.ret ⟨Nat.le_trans h.1 hq.1.1, hq.1.2.2⟩
      ⟨Nat.le_trans h.1 hq.1.1, hq.1.2.2⟩) hreq.post_inv

/-- Ranked invariant of the inner CAS loop of one service round. -/
def SvcInv (c₀ m prev : Nat) (s : AtomicSt Nat PUnit PUnit) : Prop :=
  c₀ ≤ prev ∧ s.cell = prev ∧ s.comm.shot_store = false ∧ s.fires = 0 ∧ s.budget = m

private theorem svc_tail (c₀ n prev : Nat) (s : AtomicSt Nat PUnit PUnit)
    (hc : c₀ ≤ prev) (hf : s.fires = 0) :
    InfOften (atomicBudgetWP ticketEnv) TicketCommit (fun _ s => SvcAlwaysInv c₀ s)
      ((retAfterDrop (Val := Nat) (.ok prev) >>=
          Sum.elim (fun next => ITree.tau (ITree.iter tryBody next)) ITree.ret) >>=
        fun _ => ITree.ret (n + 1))
      (winSt s PUnit.unit prev (prev + 1) PUnit.unit s.budget) := by
  simp only [retAfterDrop, vis_bind, ret_bind, Sum.elim_inr]
  refine InfOften.vis ((budgetWP_drop ticketEnv _ _).2 fun v hv =>
    ⟨fun _ _ => InfOften.ret ⟨Nat.le_trans (show c₀ ≤ prev + 1 by omega) hv,
        by show s.fires + 1 ≤ 1; omega, by show true = true ↔ s.fires + 1 = 1; simp [hf]⟩,
     fun _ _ _ => InfOften.ret ⟨Nat.le_trans (show c₀ ≤ prev + 1 by omega) hv,
        by show s.fires + 1 ≤ 1; omega, by show true = true ↔ s.fires + 1 = 1; simp [hf]⟩⟩)

theorem svc_iter_progress (c₀ n : Nat) (Q : Except Nat Nat → AtomicSt Nat PUnit PUnit → Prop)
    (m prev : Nat) (s : AtomicSt Nat PUnit PUnit) (hs : SvcInv c₀ m prev s) :
    buchiProgress (atomicBudgetWP ticketEnv) TicketCommit
      (Sum.elim (fun next s' => ∃ m', m' < m ∧ SvcInv c₀ m' next s') Q)
      (fun t' s' => InfOften (atomicBudgetWP ticketEnv) TicketCommit
        (fun _ s => SvcAlwaysInv c₀ s)
        ((t' >>= Sum.elim (fun next => ITree.tau (ITree.iter tryBody next)) ITree.ret) >>=
          fun _ => ITree.ret (n + 1)) s')
      (tryBody prev) s := by
  obtain ⟨hc, hcell, hunshot, hfires, hb⟩ := hs
  refine (buchiProgress.vis_iff _ _ _ _ _ _ _).2 ((budgetWP_call ticketEnv prev _ s).2
    ⟨trivial, fun f' r hpost => Or.inr ?_⟩)
  have hr : r = some (prev + 1) := hpost
  subst hr
  rw [tryCallK_some]
  have hwin : ∀ (b : Nat), casWin ticketEnv prev (prev + 1)
      (fun o s' => (TicketCommit (aCas prev (prev + 1)) o { s with fst := f' } s' ∧
        InfOften (atomicBudgetWP ticketEnv) TicketCommit (fun _ s => SvcAlwaysInv c₀ s)
          ((tryCasK prev (prev + 1) o >>=
              Sum.elim (fun next => ITree.tau (ITree.iter tryBody next)) ITree.ret) >>=
            fun _ => ITree.ret (n + 1)) s') ∨
        buchiProgress (atomicBudgetWP ticketEnv) TicketCommit
          (Sum.elim (fun next s' => ∃ m', m' < m ∧ SvcInv c₀ m' next s') Q)
          (fun t' s' => InfOften (atomicBudgetWP ticketEnv) TicketCommit
            (fun _ s => SvcAlwaysInv c₀ s)
            ((t' >>= Sum.elim (fun next => ITree.tau (ITree.iter tryBody next)) ITree.ret) >>=
              fun _ => ITree.ret (n + 1)) s')
          (tryCasK prev (prev + 1) o) s')
      { s with fst := f', cell := prev } b := fun b =>
    (casWin_iff ticketEnv _ _ _ _ _).2 ⟨hunshot, trivial, fun g' _ =>
      Or.inl ⟨⟨rfl, by show s.cell < prev + 1; omega, hunshot, rfl⟩, by
        rw [tryCasK_true]
        exact svc_tail c₀ n prev { s with budget := b } hc hfires⟩⟩
  refine (buchiProgress.vis_iff _ _ _ _ _ _ _).2 ((budgetWP_cas ticketEnv prev (prev + 1) _ _).2
    fun v hv => ⟨fun hvc => ⟨fun hne => absurd (hvc.trans hcell) hne, fun _ hpos => ?_,
      fun hve => ?_⟩, fun _ hpos => ⟨?_, fun hve => ?_⟩⟩)
  · have hpos' : 0 < s.budget := hpos
    have hv' : s.cell ≤ v := hv
    rw [tryCasK_false]
    exact Or.inr ((buchiProgress.ret_iff _ _ _ _ _ _).2
      ⟨m - 1, by omega, by omega, rfl, hunshot, hfires, show s.budget - 1 = m - 1 by omega⟩)
  · subst hve; exact hwin _
  · have hpos' : 0 < s.budget := hpos
    have hv' : s.cell ≤ v := hv
    rw [tryCasK_false]
    exact Or.inr ((buchiProgress.ret_iff _ _ _ _ _ _).2
      ⟨m - 1, by omega, by omega, rfl, hunshot, hfires, show s.budget - 1 = m - 1 by omega⟩)
  · subst hve; exact hwin _

/-- Each service round reaches a strictly advancing ticket commit within its window. -/
theorem serviceBody_live (c₀ n : Nat) (s : AtomicSt Nat PUnit PUnit) (h : SvcAlwaysInv c₀ s) :
    buchiProgress (atomicBudgetWP ticketEnv) TicketCommit (fun _ _ => False)
      (InfOften (atomicBudgetWP ticketEnv) TicketCommit (fun _ s => SvcAlwaysInv c₀ s))
      (serviceBody n) s := by
  refine (buchiProgress.vis_iff _ _ _ _ _ _ _).2 ((budgetWP_recv ticketEnv _ s).2 fun b =>
    Or.inr (buchiProgress.bind ?_))
  refine (buchiProgress.vis_iff _ _ _ _ _ _ _).2 ((budgetWP_load ticketEnv _ _).2 fun v hv =>
    ⟨fun _ => Or.inr ?_, fun _ _ => Or.inr ?_⟩)
  · exact buchiProgress.iter_ranked tryBody (SvcInv c₀) (svc_iter_progress c₀ n _)
      (n := b) ⟨Nat.le_trans h.1 hv, rfl, rfl, rfl, rfl⟩
  · exact buchiProgress.iter_ranked tryBody (SvcInv c₀) (svc_iter_progress c₀ n _)
      (n := b - 1) ⟨Nat.le_trans h.1 hv, rfl, rfl, rfl, rfl⟩

/--
**`#4162` reactive ticket service**: the diverging `-> !` loop that serves every
request with one `try_update` of the shared ticket counter keeps the counter
monotone and the per-request one-shot committer intact (`Always`), strictly
advances and commits a ticket infinitely often (`InfOften TicketCommit`) under
bounded per-request contention, and is genuinely non-terminating (`¬ DWP`).
-/
theorem tryUpdate_reactive_service_infOften (c₀ n₀ : Nat) (s₀ : AtomicSt Nat PUnit PUnit)
    (h : SvcAlwaysInv c₀ s₀) (Q : PEmpty.{1} → AtomicSt Nat PUnit PUnit → Prop) :
    Always (atomicBudgetWP ticketEnv) (SvcAlwaysInv c₀) Q (ticketService n₀) s₀ ∧
      InfOften (atomicBudgetWP ticketEnv) TicketCommit Q (ticketService n₀) s₀ ∧
      ¬ DWP (atomicBudgetWP ticketEnv) (ticketService n₀) Q s₀ :=
  ⟨(buchi_diverging_loop_rule serviceBody (fun _ s => SvcAlwaysInv c₀ s)
      (fun n s hs => serviceBody_always c₀ n s hs) (fun n s hs => serviceBody_live c₀ n s hs)
      (init := n₀) h Q).1,
   (buchi_diverging_loop_rule serviceBody (fun _ s => SvcAlwaysInv c₀ s)
      (fun n s hs => serviceBody_always c₀ n s hs) (fun n s hs => serviceBody_live c₀ n s hs)
      (init := n₀) h Q).2,
   not_dwp_diverging_loop serviceBody n₀⟩

end Service

/-! ## 8. Dual-Authority Grounding (`Anneal.Mir.AtomicIntrinsicsDualSpec`) -/

section DualAuthority

open Anneal.Mir.AtomicIntrinsicsDualSpec

/--
Operational admissibility guard: an atomic step may be abstracted by
`AtomicCellE` only if both authorities give it a defined, non-panicking outcome.
-/
def AdmissibleAtomicStep : AtomicAccessOutcome → Prop
  | .okStore _ => True
  | .okScalar _ _ => True
  | .okCas _ _ _ => True
  | .ub => False
  | .specPanic => False
  | .invalidOrUnsupported => False

instance (o : AtomicAccessOutcome) : Decidable (AdmissibleAtomicStep o) := by
  cases o <;> unfold AdmissibleAtomicStep <;> infer_instance

/--
A CAS outcome respects the history relation `Rel` exactly as `AtomicCellE`'s
`cas` does: a win is a `Rel`-step `ret ↦ post`, a loss writes nothing
(`post = ret`), and every other outcome is not a CAS step.
-/
def CasHistStep (Rel : Nat → Nat → Prop) : AtomicAccessOutcome → Prop
  | .okCas ret true post => Rel ret post
  | .okCas ret false post => post = ret
  | _ => False

/-- The cell value after an outcome, if defined. -/
def outcomePost : AtomicAccessOutcome → Option Nat
  | .okStore post => some post
  | .okScalar _ post => some post
  | .okCas _ _ post => some post
  | _ => none

/-- Per-step CAS discipline (non-CAS steps unconstrained). -/
def CasRespects (Rel : Nat → Nat → Prop) : AtomicAccessOutcome → Prop
  | .okCas ret true post => Rel ret post
  | .okCas ret false post => post = ret
  | _ => True

/--
A threaded atomic trace respects the history invariant `Rel`: every step is
admissible, every CAS obeys `CasRespects`, and consecutive cell values are
`Rel`-related.
-/
def TraceHist (Rel : Nat → Nat → Prop) : Option Nat → List AtomicAccessOutcome → Prop
  | _, [] => True
  | prev, o :: rest => AdmissibleAtomicStep o ∧ CasRespects Rel o ∧
      (∀ p q, prev = some p → outcomePost o = some q → Rel p q) ∧
      TraceHist Rel (outcomePost o) rest

/-- Admissibility rejects every UB / spec-panic / unsupported outcome. -/
theorem admissible_iff_defined (o : AtomicAccessOutcome) :
    AdmissibleAtomicStep o ↔ o ≠ .ub ∧ o ≠ .specPanic ∧ o ≠ .invalidOrUnsupported := by
  cases o <;> simp [AdmissibleAtomicStep]

/--
**MiniRust single-step CAS grounding** (both memory models): the winning
`u32` CAS (`case 8`, `5 ↦ 9`) is an admissible `Rel`-step whenever `Rel 5 9`,
and the losing CAS (`case 9`) is admissible and performs no write (`5 ↦ 5`),
so it preserves every reflexive history invariant.
-/
theorem mr_cas_hist_grounding (m : AtomicMemoryMode) {Rel : Nat → Nat → Prop}
    (hR : AtomicHistInv Nat Rel) (h59 : Rel 5 9) :
    (mrAtomicObserve m 8 = .okCas 5 true 9 ∧ AdmissibleAtomicStep (mrAtomicObserve m 8) ∧
      CasHistStep Rel (mrAtomicObserve m 8)) ∧
    (mrAtomicObserve m 9 = .okCas 5 false 5 ∧ AdmissibleAtomicStep (mrAtomicObserve m 9) ∧
      CasHistStep Rel (mrAtomicObserve m 9) ∧ Rel 5 5) := by
  have h8 := mrAtomicObserve_table m 8 (by decide)
  have h9 := mrAtomicObserve_table m 9 (by decide)
  cases m <;> simp only [mrExpectedOutcome] at h8 h9 <;> rw [h8, h9] <;>
    exact ⟨⟨rfl, trivial, h59⟩, ⟨rfl, trivial, rfl, hR.refl 5⟩⟩

open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr MiniRustSpec.Interp
  MiniRustSpec.AtomicIntrinsicsMR in
/--
**All integer widths (`u8`, `u16`, `u32`, `u64`, `usize`) grounding**: across
every `AtomicDualContract` and both memory models, well-aligned in-bounds
loads and stores at `u8`/`u16`/`u32`/`u64` (`cases 0..7`) agree across both
authorities and are admissible, and `usize` (`IntType.usize_ty = itU64`)
`xadd` (`5 ↦ 8`) and `cas` (`5 ↦ 9`) succeed identically on `Mach` and `MachTB`
and respect any `Rel` with `Rel 5 9`.
-/
theorem mr_scalar_widths_admissible (c : AtomicDualContract) (m : AtomicMemoryMode)
    {Rel : Nat → Nat → Prop} (h59 : Rel 5 9) :
    (∀ idx, idx < 8 →
      AdmissibleAtomicStep (mrAtomicObserve m idx) ∧
        mrAtomicObserve m idx = c.lm.observe m.toLmTreeBorrows idx) ∧
    (IntType.usize_ty = itU64 ∧
      AdmissibleAtomicStep (obsMrCas 8 5 (fun x => x.mem.memory.allocations.map (·.data))
        (bmCas (bmWith (initBytes [5, 0, 0, 0, 0, 0, 0, 0])) bmPtr 5 9 IntType.usize_ty)) ∧
      CasHistStep Rel (obsMrCas 8 5 (fun x => x.mem.memory.allocations.map (·.data))
        (bmCas (bmWith (initBytes [5, 0, 0, 0, 0, 0, 0, 0])) bmPtr 5 9 IntType.usize_ty)) ∧
      CasHistStep Rel (obsMrCas 8 5 (fun x => x.mem.memory.mem.allocations.map (·.data))
        (tbCas (tbWith (initBytes [5, 0, 0, 0, 0, 0, 0, 0])) tbPtr 5 9 IntType.usize_ty))) := by
  have hus := mr_signed_unsigned_polarity_and_usize_parity
  have hbm : obsMrCas 8 5 (fun x => x.mem.memory.allocations.map (·.data))
      (bmCas (bmWith (initBytes [5, 0, 0, 0, 0, 0, 0, 0])) bmPtr 5 9 IntType.usize_ty) =
      .okCas 5 true 9 := hus.2.2.2.1
  have htb : obsMrCas 8 5 (fun x => x.mem.memory.mem.allocations.map (·.data))
      (tbCas (tbWith (initBytes [5, 0, 0, 0, 0, 0, 0, 0])) tbPtr 5 9 IntType.usize_ty) =
      .okCas 5 true 9 := hus.2.2.2.2.1
  refine ⟨fun idx hlt => ?_, hus.1, ?_, ?_, ?_⟩
  · have hcc : idx < canonicalCaseCount := by unfold canonicalCaseCount; omega
    have hagr : (canonicalCaseMeta idx).comparisonClass = .exactAgreement := by
      match idx, hlt with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl
    refine ⟨?_, contract_agreement_zone_exact c m idx hcc hagr⟩
    rw [mrAtomicObserve_table m idx hcc]
    match idx, hlt with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => trivial
  · rw [hbm]; trivial
  · rw [hbm]; exact h59
  · rw [htb]; exact h59

open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr MiniRustSpec.Interp in
/--
**Universal MiniRust CAS frame law** (every memory model): a successful
`AtomicCompareExchange` that returns a value other than `current` leaves exactly
the machine produced by its atomic load — no store — matching `AtomicCellE`'s
zero-write `(false, actual)` answer.
-/
theorem mr_cas_failure_no_store {M : Type} [Memory M] [MemoryOps M] {m m' : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»} {cur next val : Value M}
    {t : IntType}
    (h : evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, .Int t), (next, .Int t)] (.Int t) = .ok (val, m'))
    (hne : cur ≠ val) :
    ∃ al, typedLoadM m ptr (.Int t) al .Atomic = .ok (val, m') := by
  obtain ⟨ptr', pty', cur', next', t', al, m1, hargs, hret, _, _, hload, hcase⟩ :=
    MiniRustSpec.AtomicIntrinsicsMR.atomicCompareExchange_ok_iff.mp h
  cases hargs
  rcases hcase with ⟨heq, _⟩ | ⟨_, rfl⟩
  · exact absurd heq hne
  · exact ⟨al, hload⟩

open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr MiniRustSpec.Interp in
/--
**Universal MiniRust CAS success law** (every memory model): a winning
`AtomicCompareExchange` returning `cur` is an atomic load of `cur` followed by
an atomic store of `next`; conversely, `atomicCompareExchange_success` executes
that transition from any aligned in-bounds load + store pair.
-/
theorem mr_cas_success_transition {M : Type} [Memory M] [MemoryOps M]
    {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»} {cur next : Value M}
    {t : IntType} :
    (∀ {m m' : Machine M},
      evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, .Int t), (next, .Int t)] (.Int t) = .ok (cur, m') →
      ∃ al m1, alignFromBytes t.size.bytes = some al ∧
        t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes ∧
        typedLoadM m ptr (.Int t) al .Atomic = .ok (cur, m1) ∧
        typedStoreM m1 ptr next (.Int t) al .Atomic = .ok m') ∧
    (∀ {m m1 m2 : Machine M} {al : Align},
      alignFromBytes t.size.bytes = some al →
      t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes →
      typedLoadM m ptr (.Int t) al .Atomic = .ok (cur, m1) →
      typedStoreM m1 ptr next (.Int t) al .Atomic = .ok m2 →
      evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, .Int t), (next, .Int t)] (.Int t) = .ok (cur, m2)) := by
  refine ⟨fun h => ?_, fun hal hsz hload hstore =>
    MiniRustSpec.AtomicIntrinsicsMR.atomicCompareExchange_success pty hal hsz hload hstore⟩
  obtain ⟨_, _, _, _, _, al, m1, hargs, _, hal, hsz, hload, hcase⟩ :=
    MiniRustSpec.AtomicIntrinsicsMR.atomicCompareExchange_ok_iff.mp h
  cases hargs
  rcases hcase with ⟨_, hstore⟩ | ⟨hne, _⟩
  · exact ⟨al, m1, hal, hsz, hload, hstore⟩
  · exact absurd rfl hne

open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr MiniRustSpec.Interp
  MiniRustSpec.AtomicIntrinsicsMR in
/--
**Universal MiniRust CAS failure memory & data-race law**: given a load of
`before ≠ cur`, `atomicCompareExchange_failure` returns `(before, m1)` with no
store; on `Mach`, memory is preserved byte-for-byte (`m'.mem.memory =
m.mem.memory`) and the failing CAS never data-races with a concurrent
non-atomic load.
-/
theorem mr_cas_failure_preserves_memory_and_no_race
    {m m1 m2 m3 : Mach} {ptr ptr2 : Ptr} {pty : «Type»} {cur before next v2 : Val}
    {t : IntType} {ty2 : «Type»} {al al2 : Align}
    (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hemp0 : m.mem.accesses = []) (hemp2 : m2.mem.accesses = [])
    (hload : typedLoadM (M := BM) m ptr (.Int t) al .Atomic = .ok (before, m1))
    (hne : cur ≠ before)
    (hload2 : typedLoadM (M := BM) m2 ptr2 ty2 al2 .None = .ok (v2, m3))
    (tid : ThreadId) (sync : Set ThreadId) :
    evalIntrinsicM (M := BM) m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, .Int t), (next, .Int t)] (.Int t) = .ok (before, m1) ∧
      m1.mem.memory = m.mem.memory ∧
      ConcurrentMemory.check_data_races m3.mem tid (sync, m1.mem.accesses) = .ok () ∧
      ConcurrentMemory.check_data_races m1.mem tid (sync, m3.mem.accesses) = .ok () := by
  have hcas := atomicCompareExchange_failure pty next hal hsz hload hne
  have hmem := atomicCompareExchange_failure_memory_bm hcas hne
  have hnr := atomicCompareExchange_failure_nonAtomicLoad_no_data_race hemp0 hemp2 hcas hne
    hload2 tid sync
  exact ⟨hcas, hmem, hnr.1, hnr.2⟩

open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr MiniRustSpec.Interp
  MiniRustSpec.AtomicIntrinsicsMR in
/--
**Universal Tree Borrows `MachTB.wfLive` preservation**: every admissible
MiniRust atomic intrinsic step on `MachTB` (in particular every `AtomicLoad`
and `AtomicCompareExchange` of `tryUpdateLoop`) preserves `MachTB.wfLive`.
-/
theorem mr_atomic_tb_preserves_wfLive (c : AtomicDualContract)
    {m m' : MachTB} {op : IntrinsicOp}
    {args : List (Value TBM × «Type»)} {retTy : «Type»} {val : Value TBM}
    (hop : isAtomicOp op = true)
    (hwf : MiniRustSpec.Correspondence.MachTB.wfLive m)
    (h : evalIntrinsicM m op args retTy = .ok (val, m')) :
    MiniRustSpec.Correspondence.MachTB.wfLive m' :=
  c.mr_tb_wfLive m m' op args retTy val hop hwf h

/--
**Cross-authority CAS grounding** for every `AtomicDualContract`: on the
`exactAgreement` zone LeanMiri's CAS outcomes for cases `8`/`9` coincide with
MiniRust's, so they are admissible, the win is a `Rel`-step, and the loss writes
nothing; `contract_cas_return_shape` and `contract_tcb_codec_bridge` equate the
erased `(old, succeeded) ↦ old` return shapes and wire encodings across all
agreement-zone CAS cases (`8`, `9`, `24`, `27`).
-/
theorem contract_cas_hist_grounding (c : AtomicDualContract) (m : AtomicMemoryMode)
    {Rel : Nat → Nat → Prop} (hR : AtomicHistInv Nat Rel) (h59 : Rel 5 9) :
    (c.lm.observe m.toLmTreeBorrows 8 = .okCas 5 true 9 ∧
      CasHistStep Rel (c.lm.observe m.toLmTreeBorrows 8)) ∧
    (c.lm.observe m.toLmTreeBorrows 9 = .okCas 5 false 5 ∧
      CasHistStep Rel (c.lm.observe m.toLmTreeBorrows 9)) ∧
    casOldProjection (c.lm.observe m.toLmTreeBorrows 8) =
      casOldProjection (mrAtomicObserve m 8) ∧
    casOldProjection (c.lm.observe m.toLmTreeBorrows 9) =
      casOldProjection (mrAtomicObserve m 9) ∧
    casOldProjection (c.lm.observe m.toLmTreeBorrows 24) =
      casOldProjection (mrAtomicObserve m 24) ∧
    atomicOutcomeCodec.encode (mrAtomicObserve m 8) =
      atomicOutcomeCodec.encode (c.lm.observe m.toLmTreeBorrows 8) := by
  have g := mr_cas_hist_grounding m hR h59
  have a8 := contract_agreement_zone_exact c m 8 (by decide) rfl
  have a9 := contract_agreement_zone_exact c m 9 (by decide) rfl
  have s8 := contract_cas_return_shape c m 8 (by decide) rfl
  have s9 := contract_cas_return_shape c m 9 (by decide) rfl
  have s24 := contract_cas_return_shape c m 24 (by decide) rfl
  have w8 := (contract_tcb_codec_bridge c m 8 (by decide) (by cases m <;> rfl)).1
  exact ⟨⟨a8 ▸ g.1.1, a8 ▸ g.1.2.2⟩, ⟨a9 ▸ g.2.1, a9 ▸ g.2.2.2.1⟩, s8, s9, s24, w8⟩

/-- A failing MiniRust CAS (`case 9`, `5 ↦ 5`) breaks any irreflexive `TraceHist`. -/
theorem mr_failing_cas_breaks_irreflexive (m : AtomicMemoryMode) :
    ¬ TraceHist (· < ·) (some 5) [mrAtomicObserve m 9] := by
  rw [mrAtomicObserve_table m 9 (by decide)]
  intro h
  exact Nat.lt_irrefl 5 (h.2.2.1 5 5 rfl rfl)

/--
**Threaded dual-authority trace respects monotone `AtomicHistInv (· ≤ ·)`**:
MiniRust's threaded `store 5 → fetch_add 3 → cas(5→9)✗ → cas(8→9)✓ → load`
trace (`5 → 8 → 8 → 9 → 9`) in both memory models, and every LeanMiri trace
passing `lmTraceAuthorityCheck`.
-/
theorem mrAtomicTrace_hist_monotone (m : AtomicMemoryMode) :
    TraceHist (· ≤ ·) none (mrAtomicTrace m) := by
  rw [mrAtomicTrace_table]
  simp [TraceHist, AdmissibleAtomicStep, CasRespects, outcomePost]

theorem lmTrace_hist_monotone (obs : Bool → List AtomicAccessOutcome)
    (h : lmTraceAuthorityCheck obs = true) (m : AtomicMemoryMode) :
    TraceHist (· ≤ ·) none (obs m.toLmTreeBorrows) := by
  rw [lmTraceAuthorityCheck_sound obs h m]; exact mrAtomicTrace_hist_monotone m

/-- No trace containing an inadmissible step respects any history invariant. -/
theorem not_traceHist_of_mem {Rel : Nat → Nat → Prop} :
    ∀ (prev : Option Nat) (l : List AtomicAccessOutcome) (o : AtomicAccessOutcome),
      o ∈ l → ¬ AdmissibleAtomicStep o → ¬ TraceHist Rel prev l
  | _, [], _, hmem, _, _ => nomatch hmem
  | prev, o' :: rest, o, hmem, hno, hth => by
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · exact hno hth.1
    · exact not_traceHist_of_mem (outcomePost o') rest o hmem' hno hth.2.2.2

/--
**Fail-closed operational boundaries**: misaligned (`17`), oversized `u128`
(`18`) and out-of-bounds (`19`) loads are UB and the wrapping RMWs (`15`, `16`)
are MiniRust `specPanic`s in both modes; Tree Borrows turns the `Frozen`
shared-reference store / RMW / *winning* CAS (`25`, `26`, `27`) into UB in both
authorities, all rejected by `AdmissibleAtomicStep` — while the *failing*
`Frozen` CAS (`24`) is admissible (`.okCas 5 false 5`, read-only).
-/
theorem admissible_fail_closed (c : AtomicDualContract) (m : AtomicMemoryMode) :
    ¬ AdmissibleAtomicStep (mrAtomicObserve m 17) ∧
    ¬ AdmissibleAtomicStep (mrAtomicObserve m 18) ∧
    ¬ AdmissibleAtomicStep (mrAtomicObserve m 19) ∧
    ¬ AdmissibleAtomicStep (mrAtomicObserve m 15) ∧
    ¬ AdmissibleAtomicStep (mrAtomicObserve m 16) ∧
    ¬ AdmissibleAtomicStep (c.lm.observe m.toLmTreeBorrows 17) ∧
    ¬ AdmissibleAtomicStep (c.lm.observe m.toLmTreeBorrows 18) ∧
    ¬ AdmissibleAtomicStep (c.lm.observe m.toLmTreeBorrows 19) ∧
    ¬ AdmissibleAtomicStep (mrAtomicObserve .treeBorrows 25) ∧
    ¬ AdmissibleAtomicStep (mrAtomicObserve .treeBorrows 26) ∧
    ¬ AdmissibleAtomicStep (mrAtomicObserve .treeBorrows 27) ∧
    ¬ AdmissibleAtomicStep (c.lm.observe true 27) ∧
    (AdmissibleAtomicStep (mrAtomicObserve m 24) ∧ mrAtomicObserve m 24 = .okCas 5 false 5 ∧
      CasHistStep (· ≤ ·) (mrAtomicObserve m 24)) ∧
    (AdmissibleAtomicStep (mrAtomicObserve .basic 27) ∧
      CasHistStep (· ≤ ·) (mrAtomicObserve .basic 27)) := by
  have t := fun idx (h : idx < canonicalCaseCount) => mrAtomicObserve_table m idx h
  have a := fun idx (h : idx < canonicalCaseCount) hc =>
    contract_agreement_zone_exact c m idx h hc
  have ms := contract_mode_sensitivity_joint c
  have fz := mr_tb_frozen_mode_sensitivity
  have ov := mr_wrapping_overflow_specPanic m
  rw [← a 17 (by decide) rfl, ← a 18 (by decide) rfl, ← a 19 (by decide) rfl,
    t 17 (by decide), t 18 (by decide), t 19 (by decide), ov.1, ov.2, ms.2.2.2.2.2,
    fz.2.2.2.2.2.1, fz.2.2.2.2.2.2.2.1, fz.2.2.2.2.2.2.2.2.2, fz.2.2.2.2.2.2.2.2.1,
    t 24 (by decide)]
  cases m <;> exact ⟨id, id, id, id, id, id, id, id, id, id, id, id,
    ⟨trivial, rfl, rfl⟩, ⟨trivial, show (5 : Nat) ≤ 9 by decide⟩⟩

/--
**Mode-sensitive `Frozen` trace**: on `Mach` the threaded
`load → cas(6→9)✗ → store 9 → load` trace is admissible and monotone
(`5 → 5 → 9 → 9`), while under Tree Borrows the store through the `Frozen`
reference halts in UB, so the trace respects no history invariant at all.
-/
theorem mrFrozenTrace_mode_sensitive (Rel : Nat → Nat → Prop) :
    TraceHist (· ≤ ·) none (mrFrozenTrace .basic) ∧
      ¬ TraceHist Rel none (mrFrozenTrace .treeBorrows) := by
  rw [mrFrozenAndReservedTrace_table.1, mrFrozenAndReservedTrace_table.2.1]
  refine ⟨by simp [TraceHist, AdmissibleAtomicStep, CasRespects, outcomePost], ?_⟩
  exact not_traceHist_of_mem none _ .ub (by simp) id

/-! ### 8.1 Direct `MiniRustSpec.Interp.evalIntrinsicM`-Backed `StateEffectWP` Bridge -/

section MrBridge

open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr MiniRustSpec.Interp
open MiniRustSpec.AtomicIntrinsicsMR

/-- Combined MiniRust machine state and logical `try_update` thread state. -/
abbrev MrAtomicSt (M : Type) [Memory M] (FState G : Type) : Type :=
  Machine M × AtomicSt Nat FState G

/-- A non-UB, non-panicking MiniRust `AtomicLoad` of an unsigned integer value. -/
def mrLoadOk {M : Type} [Memory M] [MemoryOps M] (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (t : IntType)
    (v : Int) (m' : Machine M) : Prop :=
  evalIntrinsicM m .AtomicLoad [(.Ptr ⟨ptr, none⟩, pty)] (.Int t) = .ok (.Int v, m') ∧ 0 ≤ v

/-- A non-UB, non-panicking MiniRust `AtomicCompareExchange` on an unsigned integer cell. -/
def mrCasOk {M : Type} [Memory M] [MemoryOps M] (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (t : IntType)
    (e d : Nat) (ret : Int) (m' : Machine M) : Prop :=
  evalIntrinsicM m .AtomicCompareExchange
      [(.Ptr ⟨ptr, none⟩, pty), (.Int e, .Int t), (.Int d, .Int t)] (.Int t) =
    .ok (.Int ret, m') ∧ 0 ≤ ret

/--
**MiniRust-backed `StateEffectWP` (`mrCellWP`)**: executes `AtomicLoad` and
`AtomicCompareExchange` directly through `MiniRustSpec.Interp.evalIntrinsicM`
on `Machine M` (for any memory model `M`: `BasicMemory` or `TreeBorrowsMemory`).
Demands `.ok` (no UB, no `specPanic`) on every atomic step, so misaligned,
oversized `u128`, out-of-bounds, and `Frozen`-write accesses fail closed, and
**demands** (rather than assumes) that every machine-observed value is
`rely`-related to the last logical cell value: a machine whose other threads
break the rely is rejected instead of silently filtered out.
-/
def mrCellWP {M FState G : Type} [Memory M] [MemoryOps M] (A : AtomicEnv Nat FState G)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (t : IntType)
    (mRely : Machine M → Machine M → Prop) :
    StateEffectWP (MrAtomicSt M FState G) (AtomicCellE Nat) where
  wp
    | .call .load, K, ms => ∀ m₁, mRely ms.1 m₁ →
        (∃ v m₂, mrLoadOk m₁ ptr pty t v m₂) ∧
        ∀ v m₂, mrLoadOk m₁ ptr pty t v m₂ → A.rely ms.2.cell v.toNat ∧ ∀ b,
          K v.toNat (m₂, { ms.2 with cell := v.toNat, budget := b })
    | .call (.cas e d), K, ms => ∀ m₁, mRely ms.1 m₁ →
        (∃ ret m₂, mrCasOk m₁ ptr pty t e d ret m₂) ∧
        ∀ ret m₂, mrCasOk m₁ ptr pty t e d ret m₂ → A.rely ms.2.cell ret.toNat ∧ ∀ b,
          (ret.toNat ≠ e →
            K (false, ret.toNat) (m₂, { ms.2 with cell := ret.toNat, budget := b })) ∧
          (ret.toNat = e →
            casWin A e d (fun o s' => K o (m₂, s')) { ms.2 with cell := ret.toNat } b ∧
            ∀ mFail, mrLoadOk m₁ ptr pty t ret mFail →
              K (false, ret.toNat) (mFail, { ms.2 with cell := ret.toNat, budget := b }))
    | .call (.callF x), K, ms =>
        A.fSpec.pre ms.2.fst x ∧
        ∀ f' r, A.fSpec.post_mut ms.2.fst x f' r → K r (ms.1, { ms.2 with fst := f' })
    | .call .dropF, K, ms => ∀ m₁, mRely ms.1 m₁ →
        (∃ v m₂, mrLoadOk m₁ ptr pty t v m₂) ∧
        ∀ v m₂, mrLoadOk m₁ ptr pty t v m₂ → A.rely ms.2.cell v.toNat ∧ ∀ b,
          A.fSpec.resolve ms.2.fst → K PUnit.unit (m₂, { ms.2 with cell := v.toNat, budget := b })
    | .call .recv, K, ms =>
        ∀ b, K PUnit.unit (ms.1, { ms.2 with comm := .fresh ms.2.cell, fires := 0, budget := b })
  mono {i} _ _ _ h hw :=
    match i with
    | .call .load => fun m₁ hm =>
        ⟨(hw m₁ hm).1, fun v m₂ hok =>
          ⟨((hw m₁ hm).2 v m₂ hok).1, fun b => h _ _ (((hw m₁ hm).2 v m₂ hok).2 b)⟩⟩
    | .call (.cas _ _) => fun m₁ hm =>
        ⟨(hw m₁ hm).1, fun ret m₂ hok =>
          ⟨((hw m₁ hm).2 ret m₂ hok).1, fun b =>
          ⟨fun hne => h _ _ ((((hw m₁ hm).2 ret m₂ hok).2 b).1 hne),
           fun heq =>
            ⟨⟨((((hw m₁ hm).2 ret m₂ hok).2 b).2 heq).1.1,
              ((((hw m₁ hm).2 ret m₂ hok).2 b).2 heq).1.2.1,
              fun g' hg' => h _ _ (((((hw m₁ hm).2 ret m₂ hok).2 b).2 heq).1.2.2 g' hg')⟩,
             fun mFail hfail =>
               h _ _ (((((hw m₁ hm).2 ret m₂ hok).2 b).2 heq).2 mFail hfail)⟩⟩⟩⟩
    | .call (.callF _) => ⟨hw.1, fun f' r hp => h _ _ (hw.2 f' r hp)⟩
    | .call .dropF => fun m₁ hm =>
        ⟨(hw m₁ hm).1, fun v m₂ hok =>
          ⟨((hw m₁ hm).2 v m₂ hok).1, fun b hr => h _ _ (((hw m₁ hm).2 v m₂ hok).2 b hr)⟩⟩
    | .call .recv => fun b => h _ _ (hw b)

instance {M FState G : Type} [Memory M] [MemoryOps M] (A : AtomicEnv Nat FState G)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (t : IntType)
    (mRely : Machine M → Machine M → Prop) :
    StateEffectWP.Conjunctive (mrCellWP A ptr pty t mRely) where
  conj {i} _ _ _ hp hq :=
    match i with
    | .call .load => fun m₁ hm =>
        ⟨(hp m₁ hm).1, fun v m₂ hok =>
          ⟨((hp m₁ hm).2 v m₂ hok).1, fun b =>
            ⟨((hp m₁ hm).2 v m₂ hok).2 b, ((hq m₁ hm).2 v m₂ hok).2 b⟩⟩⟩
    | .call (.cas _ _) => fun m₁ hm =>
        ⟨(hp m₁ hm).1, fun ret m₂ hok =>
          ⟨((hp m₁ hm).2 ret m₂ hok).1, fun b =>
            ⟨fun hne => ⟨(((hp m₁ hm).2 ret m₂ hok).2 b).1 hne,
              (((hq m₁ hm).2 ret m₂ hok).2 b).1 hne⟩,
             fun heq =>
              ⟨⟨((((hp m₁ hm).2 ret m₂ hok).2 b).2 heq).1.1,
                ((((hp m₁ hm).2 ret m₂ hok).2 b).2 heq).1.2.1,
                fun g' hg' => ⟨((((hp m₁ hm).2 ret m₂ hok).2 b).2 heq).1.2.2 g' hg',
                  ((((hq m₁ hm).2 ret m₂ hok).2 b).2 heq).1.2.2 g' hg'⟩⟩,
               fun mFail hfail => ⟨((((hp m₁ hm).2 ret m₂ hok).2 b).2 heq).2 mFail hfail,
                ((((hq m₁ hm).2 ret m₂ hok).2 b).2 heq).2 mFail hfail⟩⟩⟩⟩⟩
    | .call (.callF _) => ⟨hp.1, fun f' r h => ⟨hp.2 f' r h, hq.2 f' r h⟩⟩
    | .call .dropF => fun m₁ hm =>
        ⟨(hp m₁ hm).1, fun v m₂ hok =>
          ⟨((hp m₁ hm).2 v m₂ hok).1, fun b hr =>
            ⟨((hp m₁ hm).2 v m₂ hok).2 b hr, ((hq m₁ hm).2 v m₂ hok).2 b hr⟩⟩⟩
    | .call .recv => fun b => ⟨hp b, hq b⟩

/--
Operational admissibility of a MiniRust cell `(ptr, pty, t)` under machine-level
interference `mRely`, **coupled** to the logical cell: `MInv m c` says machine
`m` holds value `c` in the cell. Interference may stutter (`rely_refl`) and
moves the held value along `A.rely`; loads return exactly `c` without writing;
for every `t`-representable `desired` (`IntType.can_represent t d = true`), CAS
returns `c` and stores `d` iff `c = e` (the shape of
`atomicCompareExchange_ok_iff`, avoiding out-of-range `specPanic`).
-/
structure MrCellAdmissible {M FState G : Type} [Memory M] [MemoryOps M]
    (A : AtomicEnv Nat FState G)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (t : IntType)
    (mRely : Machine M → Machine M → Prop) (MInv : Machine M → Nat → Prop) : Prop where
  rely_refl : ∀ m c, MInv m c → mRely m m
  rely_pres : ∀ m c m', MInv m c → mRely m m' → ∃ c', A.rely c c' ∧ MInv m' c'
  load_ok : ∀ m c, MInv m c → ∃ v m', mrLoadOk m ptr pty t v m'
  load_val : ∀ m c v m', MInv m c → mrLoadOk m ptr pty t v m' → v.toNat = c ∧ MInv m' c
  cas_ok : ∀ m c (e d : Nat), MInv m c → IntType.can_represent t (d : Int) = true →
    ∃ ret m', mrCasOk m ptr pty t e d ret m'
  cas_val : ∀ m c (e d : Nat) ret m', MInv m c → IntType.can_represent t (d : Int) = true →
    mrCasOk m ptr pty t e d ret m' →
    ret.toNat = c ∧ (c = e → MInv m' d) ∧ (c ≠ e → MInv m' c)

/-- Machine interference followed by a load: the observed value is `rely`-related. -/
private theorem mr_observe {M FState G : Type} [Memory M] [MemoryOps M]
    {A : AtomicEnv Nat FState G} {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»}
    {t : IntType} {mRely : Machine M → Machine M → Prop} {MInv : Machine M → Nat → Prop}
    (hadm : MrCellAdmissible A ptr pty t mRely MInv)
    {m m₁ m₂ : Machine M} {c : Nat} {v : Int} (hm : MInv m c) (hr : mRely m m₁)
    (hl : mrLoadOk m₁ ptr pty t v m₂) : A.rely c v.toNat ∧ MInv m₂ v.toNat := by
  obtain ⟨c', hc', hm₁⟩ := hadm.rely_pres m c m₁ hm hr
  obtain ⟨hv, hm₂⟩ := hadm.load_val m₁ c' v m₂ hm₁ hl
  exact ⟨hv ▸ hc', hv ▸ hm₂⟩

/--
**Machine-backed safety (`tryUpdate_mr_always_safety`)**: for any memory model
`M`, coupled MiniRust admissibility invariant `MInv`, and closure outputs
representable at integer type `t` (`hrep`), `tryUpdateLoop` executes without
UB/specPanic on `mrCellWP`, every machine observation is *proved* `rely`-related
to the logical history, the machine keeps holding the logical cell value,
`HistInvSt` holds at every step, and every return establishes `CreusotPost`.
-/
theorem tryUpdate_mr_always_safety {M FState G : Type} [Memory M] [MemoryOps M]
    {A : AtomicEnv Nat FState G} {Rel : Nat → Nat → Prop}
    {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»} {t : IntType}
    {mRely : Machine M → Machine M → Prop} {MInv : Machine M → Nat → Prop}
    {init : Nat} {f₀ : FState} {g₀ : G} {comm₀ : OneShotCommitter Nat}
    (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    (hrep : ∀ f₂ x f₃ (n : Nat), A.fSpec.hist_inv f₀ f₂ → A.fSpec.post_mut f₂ x f₃ (some n) →
      Rel init x → IntType.can_represent t (n : Int) = true)
    (hadm : MrCellAdmissible A ptr pty t mRely MInv)
    {m₀ : Machine M} {s₀ : AtomicSt Nat FState G}
    (hm₀ : MInv m₀ s₀.cell) (hs₀ : InitSt init f₀ g₀ comm₀ s₀) :
    Always (mrCellWP A ptr pty t mRely)
      (fun ms => MInv ms.1 ms.2.cell ∧ HistInvSt A Rel init f₀ ms.2)
      (fun r ms => MInv ms.1 ms.2.cell ∧ CreusotPost A Rel init f₀ g₀ comm₀ r ms.2)
      (tryUpdateLoop Nat) (m₀, s₀) := by
  refine Always.vis ⟨hm₀, histInvSt_of_init hpre hs₀⟩ fun m₁ hm₁ => ?_
  obtain ⟨c₁, _, hmc₁⟩ := hadm.rely_pres m₀ _ m₁ hm₀ hm₁
  refine ⟨hadm.load_ok m₁ c₁ hmc₁, fun v m₂ hload => ?_⟩
  obtain ⟨hv, hm2⟩ := mr_observe hadm hm₀ hm₁ hload
  refine ⟨hv, fun b => ?_⟩
  dsimp only [loadAns]
  refine Always.iter_invariant tryBody
    (fun prev ms => MInv ms.1 ms.2.cell ∧ LoopInv A Rel init f₀ g₀ comm₀ prev ms.2)
    (fun prev ms hms => ?_) ⟨hm2, loopInv_of_init hpre hs₀ hv b⟩
  obtain ⟨m, s⟩ := ms
  obtain ⟨hm, hl⟩ := hms
  refine Always.vis ⟨hm, histInvSt_of_loopInv hpre hl⟩
    ⟨loopInv_pre hpre hl, fun f' r hpost => ?_⟩
  have hinv := loopInv_call hpre hl hpost
  cases r with
  | none =>
    dsimp only
    change Always (mrCellWP A ptr pty t mRely) _ _ (tryCallK prev (callOut prev none)) _
    rw [tryCallK_none]
    refine Always.vis ⟨hm, hinv⟩ fun m₁' hm₁' => ?_
    obtain ⟨c', _, hmc'⟩ := hadm.rely_pres m _ m₁' hm hm₁'
    refine ⟨hadm.load_ok m₁' c' hmc', fun v' m₂' hload' => ?_⟩
    obtain ⟨hv', hm2'⟩ := mr_observe hadm hm hm₁' hload'
    exact ⟨hv', fun b' hres => Always.ret ⟨hm2', loopInv_drop_inv hpre hinv hv' b'⟩
      ⟨hm2', loopInv_err_post hpre hl hpost hv' b' hres⟩⟩
  | some next =>
    dsimp only
    change Always (mrCellWP A ptr pty t mRely) _ _ (tryCallK prev (callOut prev (some next))) _
    rw [tryCallK_some]
    have hnext_rep : IntType.can_represent t next = true :=
      hrep s.fst prev f' next hl.2.2.1 hpost hl.1
    refine Always.vis ⟨hm, hinv⟩ fun m₁' hm₁' => ?_
    obtain ⟨c', hc', hmc'⟩ := hadm.rely_pres m _ m₁' hm hm₁'
    refine ⟨hadm.cas_ok m₁' c' prev next hmc' hnext_rep, fun ret m₂' hcas => ?_⟩
    obtain ⟨hret, hstore, hkeep⟩ := hadm.cas_val m₁' c' prev next ret m₂' hmc' hnext_rep hcas
    have hrel : A.rely s.cell ret.toNat := hret ▸ hc'
    refine ⟨hrel, fun b' => ⟨fun hne => ?_, fun heq => ?_⟩⟩
    · dsimp only
      change Always (mrCellWP A ptr pty t mRely) _ _
        (tryCasK prev next (casOut prev next false ret.toNat)) _
      rw [tryCasK_false]
      have hl' := loopInv_fail hpre hl hpost hrel b'
      have hm2' : MInv m₂' ret.toNat := hret ▸ hkeep (hret ▸ hne)
      exact Always.ret ⟨hm2', histInvSt_of_loopInv hpre hl'⟩ ⟨hm2', hl'⟩
    · refine ⟨?_, fun mFail hfail => ?_⟩
      · refine ⟨loopInv_unshot (s := s) hpre hl, ?_, fun g' hg' => ?_⟩
        · exact loopInv_win_pre (s := s) hpre hl hpost
        · dsimp only
          rw [tryCasK_true]
          have hwin : HistInvSt A Rel init f₀
              (AtomicSt.commit { s with fst := f', cell := ret.toNat } prev next g' b') := by
            simpa only [heq] using loopInv_win_inv hpre hl hpost g' b'
          have hm2' : MInv m₂' next := hstore (hret ▸ heq)
          refine Always.vis ⟨hm2', hwin⟩ fun m₁'' hm₁'' => ?_
          obtain ⟨c'', _, hmc''⟩ := hadm.rely_pres m₂' next m₁'' hm2' hm₁''
          refine ⟨hadm.load_ok m₁'' c'' hmc'', fun v'' m₂'' hload'' => ?_⟩
          obtain ⟨hv'', hm2''⟩ := mr_observe hadm hm2' hm₁'' hload''
          refine ⟨hv'', fun b'' hres => ?_⟩
          refine Always.ret ⟨hm2'', loopInv_drop_inv hpre hwin hv'' b''⟩ ⟨hm2'', ?_⟩
          have hok := loopInv_ok_post hpre hl hpost hg' hv'' b' b'' hres
          simpa only [heq] using hok
      · dsimp only
        change Always (mrCellWP A ptr pty t mRely) _ _
          (tryCasK prev next (casOut prev next false ret.toNat)) _
        rw [tryCasK_false]
        have hmf : MInv mFail ret.toNat := by
          have := (hadm.load_val m₁' c' ret mFail hmc' hfail)
          exact this.1 ▸ this.2
        have hl' := loopInv_fail hpre hl hpost hrel b'
        exact Always.ret ⟨hmf, histInvSt_of_loopInv hpre hl'⟩ ⟨hmf, hl'⟩

/--
**Tree Borrows `MachTB.wfLive` safety bridge**: enriching any coupled `MachTB`
admissibility invariant with `MachTB.wfLive` is preserved automatically across
every `load`, `cas`, spurious failure, and `drop` step of `tryUpdateLoop` via
`evalIntrinsicM_atomic_tb_wfLive`.
-/
theorem tryUpdate_mr_tb_wfLive_safety {FState G : Type}
    {A : AtomicEnv Nat FState G} {Rel : Nat → Nat → Prop}
    {ptr : ThinPointer TreeBorrowsProvenance} {pty : «Type»} {t : IntType}
    {mRely : MachTB → MachTB → Prop} {MInv : MachTB → Nat → Prop}
    {init : Nat} {f₀ : FState} {g₀ : G} {comm₀ : OneShotCommitter Nat}
    (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    (hrep : ∀ f₂ x f₃ (n : Nat), A.fSpec.hist_inv f₀ f₂ → A.fSpec.post_mut f₂ x f₃ (some n) →
      Rel init x → IntType.can_represent t (n : Int) = true)
    (hadm : MrCellAdmissible A ptr pty t mRely MInv)
    (hrely_wf : ∀ m m', MiniRustSpec.Correspondence.MachTB.wfLive m → mRely m m' →
      MiniRustSpec.Correspondence.MachTB.wfLive m')
    {m₀ : MachTB} {s₀ : AtomicSt Nat FState G}
    (hm₀ : MInv m₀ s₀.cell) (hwf₀ : MiniRustSpec.Correspondence.MachTB.wfLive m₀)
    (hs₀ : InitSt init f₀ g₀ comm₀ s₀) :
    Always (mrCellWP A ptr pty t mRely)
      (fun ms => (MInv ms.1 ms.2.cell ∧ MiniRustSpec.Correspondence.MachTB.wfLive ms.1) ∧
        HistInvSt A Rel init f₀ ms.2)
      (fun r ms => (MInv ms.1 ms.2.cell ∧ MiniRustSpec.Correspondence.MachTB.wfLive ms.1) ∧
        CreusotPost A Rel init f₀ g₀ comm₀ r ms.2)
      (tryUpdateLoop Nat) (m₀, s₀) := by
  let hadm' : MrCellAdmissible A ptr pty t mRely
      (fun m c => MInv m c ∧ MiniRustSpec.Correspondence.MachTB.wfLive m) :=
    { rely_refl := fun m c hm => hadm.rely_refl m c hm.1
      rely_pres := fun m c m' hm hrel =>
        let ⟨c', hc', hm'⟩ := hadm.rely_pres m c m' hm.1 hrel
        ⟨c', hc', hm', hrely_wf m m' hm.2 hrel⟩
      load_ok := fun m c hm => hadm.load_ok m c hm.1
      load_val := fun m c v m' hm hok =>
        let ⟨hv, hm'⟩ := hadm.load_val m c v m' hm.1 hok
        ⟨hv, hm', evalIntrinsicM_atomic_tb_wfLive rfl hm.2 hok.1⟩
      cas_ok := fun m c e d hm hr => hadm.cas_ok m c e d hm.1 hr
      cas_val := fun m c e d ret m' hm hr hok =>
        let ⟨hret, hs, hk⟩ := hadm.cas_val m c e d ret m' hm.1 hr hok
        let hwf := evalIntrinsicM_atomic_tb_wfLive rfl hm.2 hok.1
        ⟨hret, fun he => ⟨hs he, hwf⟩, fun hne => ⟨hk hne, hwf⟩⟩ }
  have h := tryUpdate_mr_always_safety hpre hrep hadm' ⟨hm₀, hwf₀⟩ hs₀
  exact Always.mono (fun _ hi => ⟨⟨hi.1.1, hi.1.2⟩, hi.2⟩)
    (fun _ _ hq => ⟨⟨hq.1.1, hq.1.2⟩, hq.2⟩) h

/--
**Machine-backed Streett liveness (`tryUpdate_mr_fairInfOften`)**: on every
coupled-admissible MiniRust cell, along every run on which a weak CAS *wins*
infinitely often (`□◇ CasWon`), `tryUpdateLoop` returns through real
`evalIntrinsicM` steps with the machine still holding the logical cell and the
full `creusot#2386` contract — for any accepting edges. Lifts §6's
`tryUpdate_fairInfOften` from the abstract environment to MiniRust machines.
-/
theorem tryUpdate_mr_fairInfOften {M FState G : Type} [Memory M] [MemoryOps M]
    {A : AtomicEnv Nat FState G} {Rel : Nat → Nat → Prop}
    {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»} {t : IntType}
    {mRely : Machine M → Machine M → Prop} {MInv : Machine M → Nat → Prop}
    {init : Nat} {f₀ : FState} {g₀ : G} {comm₀ : OneShotCommitter Nat}
    (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    (hrep : ∀ f₂ x f₃ (n : Nat), A.fSpec.hist_inv f₀ f₂ → A.fSpec.post_mut f₂ x f₃ (some n) →
      Rel init x → IntType.can_represent t (n : Int) = true)
    (hadm : MrCellAdmissible A ptr pty t mRely MInv)
    {m₀ : Machine M} {s₀ : AtomicSt Nat FState G}
    (hm₀ : MInv m₀ s₀.cell) (hs₀ : InitSt init f₀ g₀ comm₀ s₀)
    (AccEdge : (i : (AtomicCellE Nat).I) → (AtomicCellE Nat).O i →
      MrAtomicSt M FState G → MrAtomicSt M FState G → Prop) :
    FairInfOften (mrCellWP A ptr pty t mRely) AccEdge CasWon
      (fun r ms => MInv ms.1 ms.2.cell ∧ CreusotPost A Rel init f₀ g₀ comm₀ r ms.2)
      (tryUpdateLoop Nat) (m₀, s₀) := by
  refine FairInfOften.vis fun m₁ hm₁ => ?_
  obtain ⟨c₁, _, hmc₁⟩ := hadm.rely_pres m₀ _ m₁ hm₀ hm₁
  refine ⟨hadm.load_ok m₁ c₁ hmc₁, fun v m₂ hload => ?_⟩
  obtain ⟨hv, hm2⟩ := mr_observe hadm hm₀ hm₁ hload
  refine ⟨hv, fun b => ?_⟩
  dsimp only [loadAns]
  refine FairInfOften.iter_fair tryBody
    (fun (prev : Nat) (ms : MrAtomicSt M FState G) =>
      MInv ms.1 ms.2.cell ∧ LoopInv A Rel init f₀ g₀ comm₀ prev ms.2)
    (fun prev ms hms => ?_) (init := v.toNat) (s := (m₂, { s₀ with cell := v.toNat, budget := b }))
    ⟨hm2, loopInv_of_init hpre hs₀ hv b⟩
  obtain ⟨m, s⟩ := ms
  obtain ⟨hm, hl⟩ := hms
  refine (fairIter.vis_iff _ _ _ _ _ _ _ _).2
    ⟨loopInv_pre hpre hl, fun f' r hpost => Or.inr ⟨fun h => h, ?_⟩⟩
  have hinv := loopInv_call hpre hl hpost
  cases r with
  | none =>
    dsimp only
    change fairIter (mrCellWP A ptr pty t mRely) CasWon _ _ true
      (tryCallK prev (callOut prev none)) _
    rw [tryCallK_none]
    refine (fairIter.vis_iff _ _ _ _ _ _ _ _).2 fun m₁' hm₁' => ?_
    obtain ⟨c', _, hmc'⟩ := hadm.rely_pres m _ m₁' hm hm₁'
    refine ⟨hadm.load_ok m₁' c' hmc', fun v' m₂' hload' => ?_⟩
    obtain ⟨hv', hm2'⟩ := mr_observe hadm hm hm₁' hload'
    exact ⟨hv', fun b' hres => Or.inr ⟨fun h => h, (fairIter.ret_inr_iff _ _ _ _ _ _ _).2
      ⟨hm2', loopInv_err_post hpre hl hpost hv' b' hres⟩⟩⟩
  | some next =>
    dsimp only
    change fairIter (mrCellWP A ptr pty t mRely) CasWon _ _ true
      (tryCallK prev (callOut prev (some next))) _
    rw [tryCallK_some]
    have hnext_rep : IntType.can_represent t next = true :=
      hrep s.fst prev f' next hl.2.2.1 hpost hl.1
    refine (fairIter.vis_iff _ _ _ _ _ _ _ _).2 fun m₁' hm₁' => ?_
    obtain ⟨c', hc', hmc'⟩ := hadm.rely_pres m _ m₁' hm hm₁'
    refine ⟨hadm.cas_ok m₁' c' prev next hmc' hnext_rep, fun ret m₂' hcas => ?_⟩
    obtain ⟨hret, hstore, hkeep⟩ := hadm.cas_val m₁' c' prev next ret m₂' hmc' hnext_rep hcas
    have hrel : A.rely s.cell ret.toNat := hret ▸ hc'
    refine ⟨hrel, fun b' => ⟨fun hne => ?_, fun heq => ?_⟩⟩
    · refine Or.inr ⟨fun h => Bool.noConfusion h, ?_⟩
      dsimp only
      change fairIter (mrCellWP A ptr pty t mRely) CasWon _ _ true
        (tryCasK prev next (casOut prev next false ret.toNat)) _
      rw [tryCasK_false]
      have hm2' : MInv m₂' ret.toNat := hret ▸ hkeep (hret ▸ hne)
      exact (fairIter.ret_inl_iff _ _ _ _ _ _ _).2
        ⟨rfl, hm2', loopInv_fail hpre hl hpost hrel b'⟩
    · refine ⟨⟨loopInv_unshot (s := s) hpre hl, loopInv_win_pre (s := s) hpre hl hpost,
        fun g' hg' => Or.inl ⟨rfl, ?_⟩⟩,
        fun mFail hfail => Or.inr ⟨fun h => Bool.noConfusion h, ?_⟩⟩
      · dsimp only
        rw [tryCasK_true]
        have hm2' : MInv m₂' next := hstore (hret ▸ heq)
        refine DWP.vis fun m₁'' hm₁'' => ?_
        obtain ⟨c'', _, hmc''⟩ := hadm.rely_pres m₂' next m₁'' hm2' hm₁''
        refine ⟨hadm.load_ok m₁'' c'' hmc'', fun v'' m₂'' hload'' => ?_⟩
        obtain ⟨hv'', hm2''⟩ := mr_observe hadm hm2' hm₁'' hload''
        refine ⟨hv'', fun b'' hres => DWP.ret ⟨hm2'', ?_⟩⟩
        have hok := loopInv_ok_post hpre hl hpost hg' hv'' b' b'' hres
        simpa only [heq] using hok
      · dsimp only
        change fairIter (mrCellWP A ptr pty t mRely) CasWon _ _ true
          (tryCasK prev next (casOut prev next false ret.toNat)) _
        rw [tryCasK_false]
        have hmf : MInv mFail ret.toNat := by
          have := (hadm.load_val m₁' c' ret mFail hmc' hfail)
          exact this.1 ▸ this.2
        exact (fairIter.ret_inl_iff _ _ _ _ _ _ _).2
          ⟨rfl, hmf, loopInv_fail hpre hl hpost hrel b'⟩

/--
**Machine-backed enabledness (`tryUpdate_mr_infOften_attemptCas`)**: pairs with
`tryUpdate_mr_fairInfOften` so CAS fairness on `mrCellWP` cannot be satisfied
vacuously by a load-spinning loop (`mrLoadStutter` via `FairInfOften.of_never_fair`).
Every non-terminating MiniRust execution attempts a real `AtomicCompareExchange`
infinitely often.
-/
theorem tryUpdate_mr_infOften_attemptCas {M FState G : Type} [Memory M] [MemoryOps M]
    {A : AtomicEnv Nat FState G} {Rel : Nat → Nat → Prop}
    {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»} {t : IntType}
    {mRely : Machine M → Machine M → Prop} {MInv : Machine M → Nat → Prop}
    {init : Nat} {f₀ : FState} {g₀ : G} {comm₀ : OneShotCommitter Nat}
    (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    (hrep : ∀ f₂ x f₃ (n : Nat), A.fSpec.hist_inv f₀ f₂ → A.fSpec.post_mut f₂ x f₃ (some n) →
      Rel init x → IntType.can_represent t (n : Int) = true)
    (hadm : MrCellAdmissible A ptr pty t mRely MInv)
    {m₀ : Machine M} {s₀ : AtomicSt Nat FState G}
    (hm₀ : MInv m₀ s₀.cell) (hs₀ : InitSt init f₀ g₀ comm₀ s₀) :
    InfOften (mrCellWP A ptr pty t mRely) CasAttempt
      (fun r ms => MInv ms.1 ms.2.cell ∧ CreusotPost A Rel init f₀ g₀ comm₀ r ms.2)
      (tryUpdateLoop Nat) (m₀, s₀) := by
  refine InfOften.vis fun m₁ hm₁ => ?_
  obtain ⟨c₁, _, hmc₁⟩ := hadm.rely_pres m₀ _ m₁ hm₀ hm₁
  refine ⟨hadm.load_ok m₁ c₁ hmc₁, fun v m₂ hload => ?_⟩
  obtain ⟨hv, hm2⟩ := mr_observe hadm hm₀ hm₁ hload
  refine ⟨hv, fun b => ?_⟩
  dsimp only [loadAns]
  refine InfOften.iter_progress tryBody
    (fun (prev : Nat) (ms : MrAtomicSt M FState G) =>
      MInv ms.1 ms.2.cell ∧ LoopInv A Rel init f₀ g₀ comm₀ prev ms.2)
    (fun prev ms hms => ?_) ⟨hm2, loopInv_of_init hpre hs₀ hv b⟩
  obtain ⟨m, s⟩ := ms
  obtain ⟨hm, hl⟩ := hms
  refine buchiProgress.vis_skip ⟨loopInv_pre hpre hl, fun f' r hpost => ?_⟩
  cases r with
  | none =>
    dsimp only
    change buchiProgress (mrCellWP A ptr pty t mRely) CasAttempt _ _
      (tryCallK prev (callOut prev none)) _
    rw [tryCallK_none]
    refine buchiProgress.vis_skip fun m₁' hm₁' => ?_
    obtain ⟨c', _, hmc'⟩ := hadm.rely_pres m _ m₁' hm hm₁'
    refine ⟨hadm.load_ok m₁' c' hmc', fun v' m₂' hload' => ?_⟩
    obtain ⟨hv', hm2'⟩ := mr_observe hadm hm hm₁' hload'
    exact ⟨hv', fun b' hres => (buchiProgress.ret_iff _ _ _ _ _ _).2
      ⟨hm2', loopInv_err_post hpre hl hpost hv' b' hres⟩⟩
  | some next =>
    dsimp only
    change buchiProgress (mrCellWP A ptr pty t mRely) CasAttempt _ _
      (tryCallK prev (callOut prev (some next))) _
    rw [tryCallK_some]
    have hnext_rep : IntType.can_represent t next = true :=
      hrep s.fst prev f' next hl.2.2.1 hpost hl.1
    refine buchiProgress.vis_accept fun m₁' hm₁' => ?_
    obtain ⟨c', hc', hmc'⟩ := hadm.rely_pres m _ m₁' hm hm₁'
    refine ⟨hadm.cas_ok m₁' c' prev next hmc' hnext_rep, fun ret m₂' hcas => ?_⟩
    obtain ⟨hret, hstore, hkeep⟩ := hadm.cas_val m₁' c' prev next ret m₂' hmc' hnext_rep hcas
    have hrel : A.rely s.cell ret.toNat := hret ▸ hc'
    refine ⟨hrel, fun b' => ⟨fun hne => ⟨trivial, ?_⟩, fun heq => ?_⟩⟩
    · dsimp only
      change InfOften (mrCellWP A ptr pty t mRely) CasAttempt _
        (tryCasK prev next (casOut prev next false ret.toNat)) _
      rw [tryCasK_false]
      have hm2' : MInv m₂' ret.toNat := hret ▸ hkeep (hret ▸ hne)
      exact InfOften.ret ⟨hm2', loopInv_fail hpre hl hpost hrel b'⟩
    · refine ⟨⟨loopInv_unshot (s := s) hpre hl, loopInv_win_pre (s := s) hpre hl hpost,
        fun g' hg' => ⟨trivial, ?_⟩⟩,
        fun mFail hfail => ⟨trivial, ?_⟩⟩
      · dsimp only
        rw [tryCasK_true]
        have hm2' : MInv m₂' next := hstore (hret ▸ heq)
        refine InfOften.vis fun m₁'' hm₁'' => ?_
        obtain ⟨c'', _, hmc''⟩ := hadm.rely_pres m₂' next m₁'' hm2' hm₁''
        refine ⟨hadm.load_ok m₁'' c'' hmc'', fun v'' m₂'' hload'' => ?_⟩
        obtain ⟨hv'', hm2''⟩ := mr_observe hadm hm2' hm₁'' hload''
        refine ⟨hv'', fun b'' hres => InfOften.ret ⟨hm2'', ?_⟩⟩
        have hok := loopInv_ok_post hpre hl hpost hg' hv'' b' b'' hres
        simpa only [heq] using hok
      · dsimp only
        change InfOften (mrCellWP A ptr pty t mRely) CasAttempt _
          (tryCasK prev next (casOut prev next false ret.toNat)) _
        rw [tryCasK_false]
        have hmf : MInv mFail ret.toNat := by
          have := (hadm.load_val m₁' c' ret mFail hmc' hfail)
          exact this.1 ▸ this.2
        exact InfOften.ret ⟨hmf, loopInv_fail hpre hl hpost hrel b'⟩

/--
**Tree Borrows `MachTB.wfLive` Streett liveness + enabledness**: enriches any
coupled `MachTB` admissibility invariant with `MachTB.wfLive` across both
`FairInfOften` (`CoBuchi CasWon`) and `InfOften CasAttempt`.
-/
theorem tryUpdate_mr_tb_wfLive_fair {FState G : Type}
    {A : AtomicEnv Nat FState G} {Rel : Nat → Nat → Prop}
    {ptr : ThinPointer TreeBorrowsProvenance} {pty : «Type»} {t : IntType}
    {mRely : MachTB → MachTB → Prop} {MInv : MachTB → Nat → Prop}
    {init : Nat} {f₀ : FState} {g₀ : G} {comm₀ : OneShotCommitter Nat}
    (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    (hrep : ∀ f₂ x f₃ (n : Nat), A.fSpec.hist_inv f₀ f₂ → A.fSpec.post_mut f₂ x f₃ (some n) →
      Rel init x → IntType.can_represent t (n : Int) = true)
    (hadm : MrCellAdmissible A ptr pty t mRely MInv)
    (hrely_wf : ∀ m m', MiniRustSpec.Correspondence.MachTB.wfLive m → mRely m m' →
      MiniRustSpec.Correspondence.MachTB.wfLive m')
    {m₀ : MachTB} {s₀ : AtomicSt Nat FState G}
    (hm₀ : MInv m₀ s₀.cell) (hwf₀ : MiniRustSpec.Correspondence.MachTB.wfLive m₀)
    (hs₀ : InitSt init f₀ g₀ comm₀ s₀)
    (AccEdge : (i : (AtomicCellE Nat).I) → (AtomicCellE Nat).O i →
      MrAtomicSt TBM FState G → MrAtomicSt TBM FState G → Prop) :
    FairInfOften (mrCellWP A ptr pty t mRely) AccEdge CasWon
      (fun r ms => (MInv ms.1 ms.2.cell ∧ MiniRustSpec.Correspondence.MachTB.wfLive ms.1) ∧
        CreusotPost A Rel init f₀ g₀ comm₀ r ms.2)
      (tryUpdateLoop Nat) (m₀, s₀) ∧
    InfOften (mrCellWP A ptr pty t mRely) CasAttempt
      (fun r ms => (MInv ms.1 ms.2.cell ∧ MiniRustSpec.Correspondence.MachTB.wfLive ms.1) ∧
        CreusotPost A Rel init f₀ g₀ comm₀ r ms.2)
      (tryUpdateLoop Nat) (m₀, s₀) := by
  let hadm' : MrCellAdmissible A ptr pty t mRely
      (fun m c => MInv m c ∧ MiniRustSpec.Correspondence.MachTB.wfLive m) :=
    { rely_refl := fun m c hm => hadm.rely_refl m c hm.1
      rely_pres := fun m c m' hm hrel =>
        let ⟨c', hc', hm'⟩ := hadm.rely_pres m c m' hm.1 hrel
        ⟨c', hc', hm', hrely_wf m m' hm.2 hrel⟩
      load_ok := fun m c hm => hadm.load_ok m c hm.1
      load_val := fun m c v m' hm hok =>
        let ⟨hv, hm'⟩ := hadm.load_val m c v m' hm.1 hok
        ⟨hv, hm', evalIntrinsicM_atomic_tb_wfLive rfl hm.2 hok.1⟩
      cas_ok := fun m c e d hm hr => hadm.cas_ok m c e d hm.1 hr
      cas_val := fun m c e d ret m' hm hr hok =>
        let ⟨hret, hs, hk⟩ := hadm.cas_val m c e d ret m' hm.1 hr hok
        let hwf := evalIntrinsicM_atomic_tb_wfLive rfl hm.2 hok.1
        ⟨hret, fun he => ⟨hs he, hwf⟩, fun hne => ⟨hk hne, hwf⟩⟩ }
  exact ⟨tryUpdate_mr_fairInfOften hpre hrep hadm' ⟨hm₀, hwf₀⟩ hs₀ AccEdge,
    tryUpdate_mr_infOften_attemptCas hpre hrep hadm' ⟨hm₀, hwf₀⟩ hs₀⟩

/--
**General Streett / `CoBuchi` non-vacuity on `mrCellWP`** (strictly stronger than
`¬ DWP … False`): for ANY memory model `M`, ANY `Realizable A`, ANY coupled
`MrCellAdmissible`, and EVERY `AccEdge`/`Fair` (in particular `CoBuchi … CasWon`),
a finite returning MiniRust execution witnesses that `mrCellWP` cannot discharge
`FairInfOften … False` from any admissible initial state `(m₀, s₀)`.
-/
theorem tryUpdate_mr_fairInfOften_nonvacuous {M FState G : Type} [Memory M] [MemoryOps M]
    {A : AtomicEnv Nat FState G} {Rel : Nat → Nat → Prop}
    {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»} {t : IntType}
    {mRely : Machine M → Machine M → Prop} {MInv : Machine M → Nat → Prop}
    {init : Nat} {f₀ : FState} {g₀ : G} {comm₀ : OneShotCommitter Nat}
    (hR : A.Realizable)
    (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    (hrep : ∀ f₂ x f₃ (n : Nat), A.fSpec.hist_inv f₀ f₂ → A.fSpec.post_mut f₂ x f₃ (some n) →
      Rel init x → IntType.can_represent t (n : Int) = true)
    (hadm : MrCellAdmissible A ptr pty t mRely MInv)
    {m₀ : Machine M} {s₀ : AtomicSt Nat FState G}
    (hm₀ : MInv m₀ s₀.cell) (hs₀ : InitSt init f₀ g₀ comm₀ s₀)
    (AccEdge Fair : (i : (AtomicCellE Nat).I) → (AtomicCellE Nat).O i →
      MrAtomicSt M FState G → MrAtomicSt M FState G → Prop) :
    ¬ FairInfOften (mrCellWP A ptr pty t mRely) AccEdge Fair (fun _ _ => False)
      (tryUpdateLoop Nat) (m₀, s₀) := by
  intro hfi
  have hrf₀ := hadm.rely_refl m₀ s₀.cell hm₀
  obtain ⟨v₀, m₁, hl₀⟩ := hadm.load_ok m₀ s₀.cell hm₀
  obtain ⟨hv₀, hm₁⟩ := hadm.load_val m₀ s₀.cell v₀ m₁ hm₀ hl₀
  have h1 := (((FairInfOften.vis_iff _ _ _ _ _ _ _).1 hfi m₀ hrf₀).2 v₀ m₁ hl₀).2 0
  dsimp only [loadAns] at h1
  rw [iter_tryBody_eq] at h1
  have hcall := (FairInfOften.vis_iff _ _ _ _ _ _ _).1 h1
  obtain ⟨f', r, hpost⟩ := hR.post_mut_total _ _ hcall.1
  have h2 := hcall.2 f' r hpost
  cases r with
  | none =>
    change FairInfOften (mrCellWP A ptr pty t mRely) AccEdge Fair (fun _ _ => False)
      (tryCallK v₀.toNat (callOut v₀.toNat none) >>= _) _ at h2
    simp only [tryCallK_none, retAfterDrop, vis_bind] at h2
    have hrf₁ := hadm.rely_refl m₁ s₀.cell hm₁
    obtain ⟨v₁, m₂, hl₁⟩ := hadm.load_ok m₁ s₀.cell hm₁
    have h3 := (((FairInfOften.vis_iff _ _ _ _ _ _ _).1 h2 m₁ hrf₁).2 v₁ m₂ hl₁).2 0
      (hR.resolve_total f')
    simp only [ret_bind, Sum.elim_inr, FairInfOften.ret_iff] at h3
  | some next =>
    change FairInfOften (mrCellWP A ptr pty t mRely) AccEdge Fair (fun _ _ => False)
      (tryCallK v₀.toNat (callOut v₀.toNat (some next)) >>= _) _ at h2
    rw [tryCallK_some, vis_bind] at h2
    have hnext_rep : IntType.can_represent t (next : Int) = true := by
      have hrl : Rel init v₀.toNat := by
        rw [hv₀, hs₀.1]; exact hpre.cellInv.refl init
      have hf : A.fSpec.hist_inv f₀ s₀.fst := hs₀.2.1 ▸ A.fSpec.hist_inv_laws.refl f₀
      exact hrep s₀.fst v₀.toNat f' next hf hpost hrl
    have hrf₁ := hadm.rely_refl m₁ s₀.cell hm₁
    obtain ⟨ret, m₂, hcas⟩ := hadm.cas_ok m₁ s₀.cell v₀.toNat next hm₁ hnext_rep
    obtain ⟨hret, hstore, _⟩ := hadm.cas_val m₁ s₀.cell v₀.toNat next ret m₂ hm₁ hnext_rep hcas
    have heq : ret.toNat = v₀.toNat := hret.trans hv₀.symm
    have hwin := ((((FairInfOften.vis_iff _ _ _ _ _ _ _).1 h2 m₁ hrf₁).2 ret m₂ hcas).2 0).2 heq
    obtain ⟨g', hg'⟩ := hR.gc_post_total _ _ _ hwin.1.2.1
    have h3 := hwin.1.2.2 g' hg'
    simp only [tryCasK_true, retAfterDrop, vis_bind] at h3
    have hm₂ : MInv m₂ next := hstore hv₀.symm
    have hrf₂ := hadm.rely_refl m₂ next hm₂
    obtain ⟨v₂, m₃, hl₂⟩ := hadm.load_ok m₂ next hm₂
    have h4 := (((FairInfOften.vis_iff _ _ _ _ _ _ _).1 h3 m₂ hrf₂).2 v₂ m₃ hl₂).2 0
      (hR.resolve_total f')
    simp only [ret_bind, Sum.elim_inr, FairInfOften.ret_iff] at h4

/-- Load-only stutter loop (`loop { load(); }`) used to witness `CoBuchi` vacuity. -/
def mrLoadStutter : ITree (AtomicCellE Nat) PEmpty.{1} :=
  ITree.iter (fun _ => ITree.vis aLoad (fun _ => ITree.ret (Sum.inl PUnit.unit))) PUnit.unit

private theorem mrLoadStutter_eq :
    mrLoadStutter = ITree.vis aLoad (fun _ => ITree.tau mrLoadStutter) := by
  refine (iter_unfold _ PUnit.unit).trans ((vis_bind _ _ _).trans ?_)
  congr 1; funext _; exact ret_bind _ _

/--
**Why `CoBuchi CasWon` alone (without `InfOften CasAttempt` and `¬ CoBuchi False`)
is vacuous on `mrCellWP`**: on ANY coupled-admissible MiniRust cell, `mrLoadStutter`
simultaneously proves `CoBuchi CasWon False` (vacuously, via `FairInfOften.of_never_fair`)
AND `¬ DWP … False`, while refuting `InfOften CasAttempt Q` for every `Q`.
-/
theorem mrCellWP_loadStutter_cobuchi_vacuous {M FState G : Type} [Memory M] [MemoryOps M]
    {A : AtomicEnv Nat FState G}
    {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»} {t : IntType}
    {mRely : Machine M → Machine M → Prop} {MInv : Machine M → Nat → Prop}
    (hadm : MrCellAdmissible A ptr pty t mRely MInv)
    {m₀ : Machine M} {s₀ : AtomicSt Nat FState G} (hm₀ : MInv m₀ s₀.cell)
    (Q : PEmpty.{1} → MrAtomicSt M FState G → Prop) :
    CoBuchi (mrCellWP A ptr pty t mRely) CasWon (fun _ _ => False) mrLoadStutter (m₀, s₀) ∧
    ¬ DWP (mrCellWP A ptr pty t mRely) mrLoadStutter (fun _ _ => False) (m₀, s₀) ∧
    ¬ InfOften (mrCellWP A ptr pty t mRely) CasAttempt Q mrLoadStutter (m₀, s₀) := by
  have hnf : AlwaysStep (mrCellWP A ptr pty t mRely) (fun i o a b => ¬ CasWon i o a b)
      (fun _ _ => True) mrLoadStutter (m₀, s₀) := by
    refine AlwaysStep.iter_invariant _ (fun _ ms => MInv ms.1 ms.2.cell) (fun _ ms hm => ?_) hm₀
    refine (AlwaysStep.vis_iff _ _ _ _ _ _).2 fun m₁ hm₁ => ?_
    obtain ⟨c₁, _, hmc₁⟩ := hadm.rely_pres ms.1 _ m₁ hm hm₁
    refine ⟨hadm.load_ok m₁ c₁ hmc₁, fun v m₂ hload => ?_⟩
    obtain ⟨hv, hm₂⟩ := mr_observe hadm hm hm₁ hload
    exact ⟨hv, fun b => ⟨fun h => h, (AlwaysStep.ret_iff _ _ _ _ _).2 hm₂⟩⟩
  have hprod : InfOften (mrCellWP A ptr pty t mRely) (fun _ _ _ _ => True)
      (fun _ _ => False) mrLoadStutter (m₀, s₀) := by
    refine InfOften.iter_progress _ (fun _ ms => MInv ms.1 ms.2.cell) (fun _ ms hm => ?_) hm₀
    refine buchiProgress.vis_accept fun m₁ hm₁ => ?_
    obtain ⟨c₁, _, hmc₁⟩ := hadm.rely_pres ms.1 _ m₁ hm hm₁
    refine ⟨hadm.load_ok m₁ c₁ hmc₁, fun v m₂ hload => ?_⟩
    obtain ⟨hv, hm₂⟩ := mr_observe hadm hm hm₁ hload
    exact ⟨hv, fun b => ⟨trivial, InfOften.ret hm₂⟩⟩
  have hc : CoBuchi (mrCellWP A ptr pty t mRely) CasWon (fun _ _ => False)
      mrLoadStutter (m₀, s₀) := FairInfOften.of_never_fair hnf hprod
  have hnd : ¬ DWP (mrCellWP A ptr pty t mRely) mrLoadStutter (fun _ _ => False) (m₀, s₀) := by
    intro hd
    refine DWP.induct (fun x ms =>
        (x = mrLoadStutter ∨ x = ITree.tau mrLoadStutter) → MInv ms.1 ms.2.cell → False)
      ?_ hd (Or.inl rfl) hm₀
    rintro x ms hx (rfl | rfl) hm
    · have hobs : mrLoadStutter.observe = .vis aLoad (fun _ => ITree.tau mrLoadStutter) := by
        conv => lhs; rw [mrLoadStutter_eq, ITree.observe_vis]
      rw [hobs] at hx
      have hrf := hadm.rely_refl ms.1 ms.2.cell hm
      obtain ⟨v, m₂, hok⟩ := hadm.load_ok ms.1 ms.2.cell hm
      obtain ⟨hv, hm₂⟩ := hadm.load_val ms.1 ms.2.cell v m₂ hm hok
      exact ((hx ms.1 hrf).2 v m₂ hok).2 0 (Or.inr rfl) (hv ▸ hm₂)
    · rw [ITree.observe_tau] at hx
      exact hx (Or.inl rfl) hm
  have hni : ¬ InfOften (mrCellWP A ptr pty t mRely) CasAttempt Q mrLoadStutter (m₀, s₀) := by
    intro hi
    rw [InfOften.unfold_eq] at hi
    refine buchiProgress.induct (fun x ms =>
        (x = mrLoadStutter ∨ x = ITree.tau mrLoadStutter) → MInv ms.1 ms.2.cell → False)
      ?_ hi (Or.inl rfl) hm₀
    rintro x ms hx (rfl | rfl) hm
    · have hobs : mrLoadStutter.observe = .vis aLoad (fun _ => ITree.tau mrLoadStutter) := by
        conv => lhs; rw [mrLoadStutter_eq, ITree.observe_vis]
      rw [hobs] at hx
      have hrf := hadm.rely_refl ms.1 ms.2.cell hm
      obtain ⟨v, m₂, hok⟩ := hadm.load_ok ms.1 ms.2.cell hm
      obtain ⟨hv, hm₂⟩ := hadm.load_val ms.1 ms.2.cell v m₂ hm hok
      rcases ((hx ms.1 hrf).2 v m₂ hok).2 0 with ⟨ha, _⟩ | hskip
      · exact ha
      · exact hskip (Or.inr rfl) (hv ▸ hm₂)
    · rw [ITree.observe_tau] at hx
      exact hx (Or.inl rfl) hm
  exact ⟨hc, hnd, hni⟩

/--
**Bounded-contention MiniRust-backed `StateEffectWP` (`mrBudgetWP`)**: the
machine-level analogue of `atomicBudgetWP`. Every `load`/`cas`/`dropF` executes
real `MiniRustSpec.Interp.evalIntrinsicM` and proves `A.rely`; quiescent steps
keep `s.budget`, while interfering machine steps (`v.toNat ≠ s.cell`) or
spurious weak-CAS failures require `0 < s.budget` and strictly decrement
`s.budget - 1`. Refined by `mrCellWP` (`mrCellWP_refines_budget`).
-/
def mrBudgetWP {M FState G : Type} [Memory M] [MemoryOps M] (A : AtomicEnv Nat FState G)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (t : IntType)
    (mRely : Machine M → Machine M → Prop) :
    StateEffectWP (MrAtomicSt M FState G) (AtomicCellE Nat) where
  wp
    | .call .load, K, ms => ∀ m₁, mRely ms.1 m₁ →
        (∃ v m₂, mrLoadOk m₁ ptr pty t v m₂) ∧
        ∀ v m₂, mrLoadOk m₁ ptr pty t v m₂ → A.rely ms.2.cell v.toNat ∧
          (v.toNat = ms.2.cell → K v.toNat (m₂, { ms.2 with cell := v.toNat })) ∧
          (v.toNat ≠ ms.2.cell → 0 < ms.2.budget →
            K v.toNat (m₂, { ms.2 with cell := v.toNat, budget := ms.2.budget - 1 }))
    | .call (.cas e d), K, ms => ∀ m₁, mRely ms.1 m₁ →
        (∃ ret m₂, mrCasOk m₁ ptr pty t e d ret m₂) ∧
        ∀ ret m₂, mrCasOk m₁ ptr pty t e d ret m₂ → A.rely ms.2.cell ret.toNat ∧
          (ret.toNat = ms.2.cell →
            (ret.toNat ≠ e → K (false, ret.toNat) (m₂, { ms.2 with cell := ret.toNat })) ∧
            (ret.toNat = e →
              casWin A e d (fun o s' => K o (m₂, s')) { ms.2 with cell := ret.toNat } ms.2.budget ∧
              (0 < ms.2.budget → ∀ mFail, mrLoadOk m₁ ptr pty t ret mFail →
                K (false, ret.toNat)
                  (mFail, { ms.2 with cell := ret.toNat, budget := ms.2.budget - 1 })))) ∧
          (ret.toNat ≠ ms.2.cell → 0 < ms.2.budget →
            (ret.toNat ≠ e →
              K (false, ret.toNat)
                (m₂, { ms.2 with cell := ret.toNat, budget := ms.2.budget - 1 })) ∧
            (ret.toNat = e →
              casWin A e d (fun o s' => K o (m₂, s'))
                { ms.2 with cell := ret.toNat } (ms.2.budget - 1) ∧
              ∀ mFail, mrLoadOk m₁ ptr pty t ret mFail →
                K (false, ret.toNat)
                  (mFail, { ms.2 with cell := ret.toNat, budget := ms.2.budget - 1 })))
    | .call (.callF x), K, ms =>
        A.fSpec.pre ms.2.fst x ∧
        ∀ f' r, A.fSpec.post_mut ms.2.fst x f' r → K r (ms.1, { ms.2 with fst := f' })
    | .call .dropF, K, ms => ∀ m₁, mRely ms.1 m₁ →
        (∃ v m₂, mrLoadOk m₁ ptr pty t v m₂) ∧
        ∀ v m₂, mrLoadOk m₁ ptr pty t v m₂ → A.rely ms.2.cell v.toNat ∧
          (v.toNat = ms.2.cell → A.fSpec.resolve ms.2.fst →
            K PUnit.unit (m₂, { ms.2 with cell := v.toNat })) ∧
          (v.toNat ≠ ms.2.cell → 0 < ms.2.budget → A.fSpec.resolve ms.2.fst →
            K PUnit.unit (m₂, { ms.2 with cell := v.toNat, budget := ms.2.budget - 1 }))
    | .call .recv, K, ms =>
        ∀ b, K PUnit.unit (ms.1, { ms.2 with comm := .fresh ms.2.cell, fires := 0, budget := b })
  mono {i} _ _ _ h hw :=
    match i with
    | .call .load => fun m₁ hm =>
        ⟨(hw m₁ hm).1, fun v m₂ hok =>
          ⟨((hw m₁ hm).2 v m₂ hok).1,
           fun he => h _ _ (((hw m₁ hm).2 v m₂ hok).2.1 he),
           fun hne hp => h _ _ (((hw m₁ hm).2 v m₂ hok).2.2 hne hp)⟩⟩
    | .call (.cas _ _) => fun m₁ hm =>
        ⟨(hw m₁ hm).1, fun ret m₂ hok =>
          let hs := ((hw m₁ hm).2 ret m₂ hok).2
          ⟨((hw m₁ hm).2 ret m₂ hok).1,
           fun hc =>
            ⟨fun hne => h _ _ ((hs.1 hc).1 hne),
             fun he =>
              ⟨⟨((hs.1 hc).2 he).1.1, ((hs.1 hc).2 he).1.2.1,
                fun g' hg' => h _ _ (((hs.1 hc).2 he).1.2.2 g' hg')⟩,
               fun hp mFail hfail => h _ _ (((hs.1 hc).2 he).2 hp mFail hfail)⟩⟩,
           fun hc hp =>
            ⟨fun hne => h _ _ ((hs.2 hc hp).1 hne),
             fun he =>
              ⟨⟨((hs.2 hc hp).2 he).1.1, ((hs.2 hc hp).2 he).1.2.1,
                fun g' hg' => h _ _ (((hs.2 hc hp).2 he).1.2.2 g' hg')⟩,
               fun mFail hfail => h _ _ (((hs.2 hc hp).2 he).2 mFail hfail)⟩⟩⟩⟩
    | .call (.callF _) => ⟨hw.1, fun f' r hp => h _ _ (hw.2 f' r hp)⟩
    | .call .dropF => fun m₁ hm =>
        ⟨(hw m₁ hm).1, fun v m₂ hok =>
          ⟨((hw m₁ hm).2 v m₂ hok).1,
           fun he hr => h _ _ (((hw m₁ hm).2 v m₂ hok).2.1 he hr),
           fun hne hp hr => h _ _ (((hw m₁ hm).2 v m₂ hok).2.2 hne hp hr)⟩⟩
    | .call .recv => fun b => h _ _ (hw b)

instance {M FState G : Type} [Memory M] [MemoryOps M] (A : AtomicEnv Nat FState G)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (t : IntType)
    (mRely : Machine M → Machine M → Prop) :
    StateEffectWP.Conjunctive (mrBudgetWP A ptr pty t mRely) where
  conj {i} _ _ _ hp hq :=
    match i with
    | .call .load => fun m₁ hm =>
        ⟨(hp m₁ hm).1, fun v m₂ hok =>
          ⟨((hp m₁ hm).2 v m₂ hok).1,
           fun he => ⟨((hp m₁ hm).2 v m₂ hok).2.1 he, ((hq m₁ hm).2 v m₂ hok).2.1 he⟩,
           fun hne hpos =>
            ⟨((hp m₁ hm).2 v m₂ hok).2.2 hne hpos, ((hq m₁ hm).2 v m₂ hok).2.2 hne hpos⟩⟩⟩
    | .call (.cas _ _) => fun m₁ hm =>
        ⟨(hp m₁ hm).1, fun ret m₂ hok =>
          let sp := ((hp m₁ hm).2 ret m₂ hok).2
          let sq := ((hq m₁ hm).2 ret m₂ hok).2
          ⟨((hp m₁ hm).2 ret m₂ hok).1,
           fun hc =>
            ⟨fun hne => ⟨(sp.1 hc).1 hne, (sq.1 hc).1 hne⟩,
             fun he =>
              ⟨⟨((sp.1 hc).2 he).1.1, ((sp.1 hc).2 he).1.2.1,
                fun g' hg' => ⟨((sp.1 hc).2 he).1.2.2 g' hg', ((sq.1 hc).2 he).1.2.2 g' hg'⟩⟩,
               fun hpos mFail hfail =>
                ⟨((sp.1 hc).2 he).2 hpos mFail hfail, ((sq.1 hc).2 he).2 hpos mFail hfail⟩⟩⟩,
           fun hc hpos =>
            ⟨fun hne => ⟨(sp.2 hc hpos).1 hne, (sq.2 hc hpos).1 hne⟩,
             fun he =>
              ⟨⟨((sp.2 hc hpos).2 he).1.1, ((sp.2 hc hpos).2 he).1.2.1,
                fun g' hg' => ⟨((sp.2 hc hpos).2 he).1.2.2 g' hg',
                  ((sq.2 hc hpos).2 he).1.2.2 g' hg'⟩⟩,
               fun mFail hfail =>
                ⟨((sp.2 hc hpos).2 he).2 mFail hfail, ((sq.2 hc hpos).2 he).2 mFail hfail⟩⟩⟩⟩⟩
    | .call (.callF _) => ⟨hp.1, fun f' r h => ⟨hp.2 f' r h, hq.2 f' r h⟩⟩
    | .call .dropF => fun m₁ hm =>
        ⟨(hp m₁ hm).1, fun v m₂ hok =>
          ⟨((hp m₁ hm).2 v m₂ hok).1,
           fun he hr => ⟨((hp m₁ hm).2 v m₂ hok).2.1 he hr, ((hq m₁ hm).2 v m₂ hok).2.1 he hr⟩,
           fun hne hpos hr =>
            ⟨((hp m₁ hm).2 v m₂ hok).2.2 hne hpos hr,
             ((hq m₁ hm).2 v m₂ hok).2.2 hne hpos hr⟩⟩⟩
    | .call .recv => fun b => ⟨hp b, hq b⟩

/-- Every `mrCellWP` safety property transfers automatically to `mrBudgetWP`. -/
theorem mrCellWP_refines_budget {M FState G : Type} [Memory M] [MemoryOps M]
    (A : AtomicEnv Nat FState G)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (t : IntType)
    (mRely : Machine M → Machine M → Prop)
    (i : (AtomicCellE Nat).I)
    (K : (AtomicCellE Nat).O i → MrAtomicSt M FState G → Prop)
    (ms : MrAtomicSt M FState G)
    (hw : (mrCellWP A ptr pty t mRely).wp i K ms) :
    (mrBudgetWP A ptr pty t mRely).wp i K ms := by
  match i with
  | .call .load =>
    intro m₁ hm
    refine ⟨(hw m₁ hm).1, fun v m₂ hok =>
      ⟨((hw m₁ hm).2 v m₂ hok).1, fun _ => ((hw m₁ hm).2 v m₂ hok).2 ms.2.budget,
       fun _ _ => ((hw m₁ hm).2 v m₂ hok).2 (ms.2.budget - 1)⟩⟩
  | .call (.cas _ _) =>
    intro m₁ hm
    refine ⟨(hw m₁ hm).1, fun ret m₂ hok =>
      let hw0 := ((hw m₁ hm).2 ret m₂ hok).2 ms.2.budget
      let hw1 := ((hw m₁ hm).2 ret m₂ hok).2 (ms.2.budget - 1)
      ⟨((hw m₁ hm).2 ret m₂ hok).1,
       fun _ => ⟨hw0.1, fun he => ⟨(hw0.2 he).1, fun _ => (hw1.2 he).2⟩⟩,
       fun _ _ => ⟨hw1.1, fun he => ⟨(hw1.2 he).1, (hw1.2 he).2⟩⟩⟩⟩
  | .call (.callF _) => exact hw
  | .call .dropF =>
    intro m₁ hm
    refine ⟨(hw m₁ hm).1, fun v m₂ hok =>
      ⟨((hw m₁ hm).2 v m₂ hok).1, fun _ hr => ((hw m₁ hm).2 v m₂ hok).2 ms.2.budget hr,
       fun _ _ hr => ((hw m₁ hm).2 v m₂ hok).2 (ms.2.budget - 1) hr⟩⟩
  | .call .recv => exact hw

/--
**Machine-backed unconditional termination (`tryUpdate_mr_dwp_ranked`)**: under
bounded concurrent machine interference and bounded spurious weak-CAS failures
(`mrBudgetWP`), `tryUpdateLoop` terminates unconditionally through real
`evalIntrinsicM` steps with `MInv ms.1 ms.2.cell ∧ CreusotPost …` (proved by
well-founded induction on `s.budget` via `dwp_iter_ranked_lt`).
-/
theorem tryUpdate_mr_dwp_ranked {M FState G : Type} [Memory M] [MemoryOps M]
    {A : AtomicEnv Nat FState G} {Rel : Nat → Nat → Prop}
    {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»} {t : IntType}
    {mRely : Machine M → Machine M → Prop} {MInv : Machine M → Nat → Prop}
    {init : Nat} {f₀ : FState} {g₀ : G} {comm₀ : OneShotCommitter Nat}
    (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    (hrep : ∀ f₂ x f₃ (n : Nat), A.fSpec.hist_inv f₀ f₂ → A.fSpec.post_mut f₂ x f₃ (some n) →
      Rel init x → IntType.can_represent t (n : Int) = true)
    (hadm : MrCellAdmissible A ptr pty t mRely MInv)
    {m₀ : Machine M} {s₀ : AtomicSt Nat FState G}
    (hm₀ : MInv m₀ s₀.cell) (hs₀ : InitSt init f₀ g₀ comm₀ s₀) :
    DWP (mrBudgetWP A ptr pty t mRely) (tryUpdateLoop Nat)
      (fun r ms => MInv ms.1 ms.2.cell ∧ CreusotPost A Rel init f₀ g₀ comm₀ r ms.2)
      (m₀, s₀) := by
  have hstep : ∀ n prev (ms : MrAtomicSt M FState G),
      (MInv ms.1 ms.2.cell ∧ RankedInv A Rel init f₀ g₀ comm₀ n prev ms.2) →
      DWP (mrBudgetWP A ptr pty t mRely) (tryBody prev)
        (Sum.elim (fun next ms' => ∃ m, m < n ∧
            MInv ms'.1 ms'.2.cell ∧ RankedInv A Rel init f₀ g₀ comm₀ m next ms'.2)
          (fun r ms' =>
            MInv ms'.1 ms'.2.cell ∧ CreusotPost A Rel init f₀ g₀ comm₀ r ms'.2)) ms := by
    intro n prev ⟨m, s⟩ ⟨hm, hl, hb⟩
    dsimp only at hm hl hb
    refine DWP.vis ⟨loopInv_pre hpre hl, fun f' r hpost => ?_⟩
    cases r with
    | none =>
      dsimp only
      change DWP (mrBudgetWP A ptr pty t mRely) (tryCallK prev (callOut prev none)) _ _
      rw [tryCallK_none]
      refine DWP.vis fun m₁' hm₁' => ?_
      obtain ⟨c', _, hmc'⟩ := hadm.rely_pres m _ m₁' hm hm₁'
      refine ⟨hadm.load_ok m₁' c' hmc', fun v' m₂' hload' => ?_⟩
      obtain ⟨hv', hm2'⟩ := mr_observe hadm hm hm₁' hload'
      exact ⟨hv',
        fun _ hres => DWP.ret ⟨hm2', loopInv_err_post hpre hl hpost hv' s.budget hres⟩,
        fun _ _ hres => DWP.ret ⟨hm2', loopInv_err_post hpre hl hpost hv' (s.budget - 1) hres⟩⟩
    | some next =>
      dsimp only
      change DWP (mrBudgetWP A ptr pty t mRely) (tryCallK prev (callOut prev (some next))) _ _
      rw [tryCallK_some]
      have hnext_rep : IntType.can_represent t next = true :=
        hrep s.fst prev f' next hl.2.2.1 hpost hl.1
      refine DWP.vis fun m₁' hm₁' => ?_
      obtain ⟨c', hc', hmc'⟩ := hadm.rely_pres m _ m₁' hm hm₁'
      refine ⟨hadm.cas_ok m₁' c' prev next hmc' hnext_rep, fun ret m₂' hcas => ?_⟩
      obtain ⟨hret, hstore, hkeep⟩ := hadm.cas_val m₁' c' prev next ret m₂' hmc' hnext_rep hcas
      have hrel : A.rely s.cell ret.toNat := hret ▸ hc'
      have hwin : ∀ b (heq : ret.toNat = prev),
          casWin A prev next
            (fun o s' => DWP (mrBudgetWP A ptr pty t mRely) (tryCasK prev next o)
              (Sum.elim (fun next ms' => ∃ m, m < n ∧
                  MInv ms'.1 ms'.2.cell ∧ RankedInv A Rel init f₀ g₀ comm₀ m next ms'.2)
                (fun r ms' => MInv ms'.1 ms'.2.cell ∧
                  CreusotPost A Rel init f₀ g₀ comm₀ r ms'.2)) (m₂', s'))
            { s with fst := f', cell := ret.toNat } b := by
        intro b heq
        refine ⟨loopInv_unshot (s := s) hpre hl, loopInv_win_pre (s := s) hpre hl hpost,
          fun g' hg' => ?_⟩
        dsimp only
        rw [tryCasK_true]
        have hm2' : MInv m₂' next := hstore (hret ▸ heq)
        refine DWP.vis fun m₁'' hm₁'' => ?_
        obtain ⟨c'', _, hmc''⟩ := hadm.rely_pres m₂' next m₁'' hm2' hm₁''
        refine ⟨hadm.load_ok m₁'' c'' hmc'', fun v'' m₂'' hload'' => ?_⟩
        obtain ⟨hv'', hm2''⟩ := mr_observe hadm hm2' hm₁'' hload''
        refine ⟨hv'', fun _ hres => DWP.ret ⟨hm2'', ?_⟩, fun _ _ hres => DWP.ret ⟨hm2'', ?_⟩⟩
        · simpa only [heq, AtomicSt.commit] using loopInv_ok_post hpre hl hpost hg' hv'' b b hres
        · simpa only [heq, AtomicSt.commit] using
            loopInv_ok_post hpre hl hpost hg' hv'' b (b - 1) hres
      refine ⟨hrel, fun hsc => ⟨fun hne => absurd (hsc.trans hl.2.1) hne, fun heq => ?_⟩,
        fun _ hpos => ⟨fun hne => ?_, fun heq => ?_⟩⟩
      · refine ⟨hwin s.budget heq, fun hpos mFail hfail => ?_⟩
        dsimp only at hpos ⊢
        change DWP (mrBudgetWP A ptr pty t mRely)
          (tryCasK prev next (casOut prev next false ret.toNat)) _ _
        rw [tryCasK_false]
        have hmf : MInv mFail ret.toNat := by
          have := hadm.load_val m₁' c' ret mFail hmc' hfail; exact this.1 ▸ this.2
        exact DWP.ret ⟨n - 1, by omega, hmf, loopInv_fail hpre hl hpost hrel (s.budget - 1),
          show s.budget - 1 = n - 1 by omega⟩
      · dsimp only at hpos ⊢
        change DWP (mrBudgetWP A ptr pty t mRely)
          (tryCasK prev next (casOut prev next false ret.toNat)) _ _
        rw [tryCasK_false]
        have hm2' : MInv m₂' ret.toNat := hret ▸ hkeep (hret ▸ hne)
        exact DWP.ret ⟨n - 1, by omega, hm2', loopInv_fail hpre hl hpost hrel (s.budget - 1),
          show s.budget - 1 = n - 1 by omega⟩
      · refine ⟨hwin (s.budget - 1) heq, fun mFail hfail => ?_⟩
        dsimp only at hpos ⊢
        change DWP (mrBudgetWP A ptr pty t mRely)
          (tryCasK prev next (casOut prev next false ret.toNat)) _ _
        rw [tryCasK_false]
        have hmf : MInv mFail ret.toNat := by
          have := hadm.load_val m₁' c' ret mFail hmc' hfail; exact this.1 ▸ this.2
        exact DWP.ret ⟨n - 1, by omega, hmf, loopInv_fail hpre hl hpost hrel (s.budget - 1),
          show s.budget - 1 = n - 1 by omega⟩
  refine DWP.vis fun m₁ hm₁ => ?_
  obtain ⟨c₁, _, hmc₁⟩ := hadm.rely_pres m₀ _ m₁ hm₀ hm₁
  refine ⟨hadm.load_ok m₁ c₁ hmc₁, fun v m₂ hload => ?_⟩
  obtain ⟨hv, hm2⟩ := mr_observe hadm hm₀ hm₁ hload
  refine ⟨hv, fun _ => ?_, fun _ _ => ?_⟩
  · dsimp only [loadAns]
    exact dwp_iter_ranked_lt tryBody
      (fun n prev (ms : MrAtomicSt M FState G) =>
        MInv ms.1 ms.2.cell ∧ RankedInv A Rel init f₀ g₀ comm₀ n prev ms.2)
      hstep (n := s₀.budget) ⟨hm2, loopInv_of_init hpre hs₀ hv s₀.budget, rfl⟩
  · dsimp only [loadAns]
    exact dwp_iter_ranked_lt tryBody
      (fun n prev (ms : MrAtomicSt M FState G) =>
        MInv ms.1 ms.2.cell ∧ RankedInv A Rel init f₀ g₀ comm₀ n prev ms.2)
      hstep (n := s₀.budget - 1) ⟨hm2, loopInv_of_init hpre hs₀ hv (s₀.budget - 1), rfl⟩

/-- Machine-backed `Eventually` termination under bounded contention (`mrBudgetWP`). -/
theorem tryUpdate_mr_eventually {M FState G : Type} [Memory M] [MemoryOps M]
    {A : AtomicEnv Nat FState G} {Rel : Nat → Nat → Prop}
    {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»} {t : IntType}
    {mRely : Machine M → Machine M → Prop} {MInv : Machine M → Nat → Prop}
    {init : Nat} {f₀ : FState} {g₀ : G} {comm₀ : OneShotCommitter Nat}
    (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    (hrep : ∀ f₂ x f₃ (n : Nat), A.fSpec.hist_inv f₀ f₂ → A.fSpec.post_mut f₂ x f₃ (some n) →
      Rel init x → IntType.can_represent t (n : Int) = true)
    (hadm : MrCellAdmissible A ptr pty t mRely MInv)
    {m₀ : Machine M} {s₀ : AtomicSt Nat FState G}
    (hm₀ : MInv m₀ s₀.cell) (hs₀ : InitSt init f₀ g₀ comm₀ s₀)
    (Target : MrAtomicSt M FState G → Prop) :
    Eventually (mrBudgetWP A ptr pty t mRely) Target
      (fun r ms => MInv ms.1 ms.2.cell ∧ CreusotPost A Rel init f₀ g₀ comm₀ r ms.2)
      (tryUpdateLoop Nat) (m₀, s₀) :=
  eventually_of_dwp Target (tryUpdate_mr_dwp_ranked hpre hrep hadm hm₀ hs₀)

/-- Tree Borrows `MachTB.wfLive` unconditional termination (`DWP`) under `mrBudgetWP`. -/
theorem tryUpdate_mr_tb_wfLive_dwp {FState G : Type}
    {A : AtomicEnv Nat FState G} {Rel : Nat → Nat → Prop}
    {ptr : ThinPointer TreeBorrowsProvenance} {pty : «Type»} {t : IntType}
    {mRely : MachTB → MachTB → Prop} {MInv : MachTB → Nat → Prop}
    {init : Nat} {f₀ : FState} {g₀ : G} {comm₀ : OneShotCommitter Nat}
    (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    (hrep : ∀ f₂ x f₃ (n : Nat), A.fSpec.hist_inv f₀ f₂ → A.fSpec.post_mut f₂ x f₃ (some n) →
      Rel init x → IntType.can_represent t (n : Int) = true)
    (hadm : MrCellAdmissible A ptr pty t mRely MInv)
    (hrely_wf : ∀ m m', MiniRustSpec.Correspondence.MachTB.wfLive m → mRely m m' →
      MiniRustSpec.Correspondence.MachTB.wfLive m')
    {m₀ : MachTB} {s₀ : AtomicSt Nat FState G}
    (hm₀ : MInv m₀ s₀.cell) (hwf₀ : MiniRustSpec.Correspondence.MachTB.wfLive m₀)
    (hs₀ : InitSt init f₀ g₀ comm₀ s₀) :
    DWP (mrBudgetWP A ptr pty t mRely) (tryUpdateLoop Nat)
      (fun r ms => (MInv ms.1 ms.2.cell ∧ MiniRustSpec.Correspondence.MachTB.wfLive ms.1) ∧
        CreusotPost A Rel init f₀ g₀ comm₀ r ms.2)
      (m₀, s₀) := by
  let hadm' : MrCellAdmissible A ptr pty t mRely
      (fun m c => MInv m c ∧ MiniRustSpec.Correspondence.MachTB.wfLive m) :=
    { rely_refl := fun m c hm => hadm.rely_refl m c hm.1
      rely_pres := fun m c m' hm hrel =>
        let ⟨c', hc', hm'⟩ := hadm.rely_pres m c m' hm.1 hrel
        ⟨c', hc', hm', hrely_wf m m' hm.2 hrel⟩
      load_ok := fun m c hm => hadm.load_ok m c hm.1
      load_val := fun m c v m' hm hok =>
        let ⟨hv, hm'⟩ := hadm.load_val m c v m' hm.1 hok
        ⟨hv, hm', evalIntrinsicM_atomic_tb_wfLive rfl hm.2 hok.1⟩
      cas_ok := fun m c e d hm hr => hadm.cas_ok m c e d hm.1 hr
      cas_val := fun m c e d ret m' hm hr hok =>
        let ⟨hret, hs, hk⟩ := hadm.cas_val m c e d ret m' hm.1 hr hok
        let hwf := evalIntrinsicM_atomic_tb_wfLive rfl hm.2 hok.1
        ⟨hret, fun he => ⟨hs he, hwf⟩, fun hne => ⟨hk hne, hwf⟩⟩ }
  exact tryUpdate_mr_dwp_ranked hpre hrep hadm' ⟨hm₀, hwf₀⟩ hs₀

/--
**General non-vacuity of `mrBudgetWP`**: for ANY memory model `M`, ANY
`Realizable A`, and ANY coupled `MrCellAdmissible`, `mrBudgetWP` cannot
discharge `DWP … False` from any admissible initial state `(m₀, s₀)`.
-/
theorem mrBudgetWP_nonvacuous_not_false {M FState G : Type} [Memory M] [MemoryOps M]
    {A : AtomicEnv Nat FState G} {Rel : Nat → Nat → Prop}
    {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»} {t : IntType}
    {mRely : Machine M → Machine M → Prop} {MInv : Machine M → Nat → Prop}
    {init : Nat} {f₀ : FState} {g₀ : G} {comm₀ : OneShotCommitter Nat}
    (hR : A.Realizable)
    (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    (hrep : ∀ f₂ x f₃ (n : Nat), A.fSpec.hist_inv f₀ f₂ → A.fSpec.post_mut f₂ x f₃ (some n) →
      Rel init x → IntType.can_represent t (n : Int) = true)
    (hadm : MrCellAdmissible A ptr pty t mRely MInv)
    {m₀ : Machine M} {s₀ : AtomicSt Nat FState G}
    (hm₀ : MInv m₀ s₀.cell) (hs₀ : InitSt init f₀ g₀ comm₀ s₀) :
    ¬ DWP (mrBudgetWP A ptr pty t mRely) (tryUpdateLoop Nat) (fun _ _ => False) (m₀, s₀) := by
  intro hd
  have hrf₀ := hadm.rely_refl m₀ s₀.cell hm₀
  obtain ⟨v₀, m₁, hl₀⟩ := hadm.load_ok m₀ s₀.cell hm₀
  obtain ⟨hv₀, hm₁⟩ := hadm.load_val m₀ s₀.cell v₀ m₁ hm₀ hl₀
  have h1 := (((DWP.vis_iff _ _ _ _ _).1 hd m₀ hrf₀).2 v₀ m₁ hl₀).2.1 hv₀
  dsimp only [loadAns] at h1
  rw [iter_tryBody_eq] at h1
  have hcall := (DWP.vis_iff _ _ _ _ _).1 h1
  obtain ⟨f', r, hpost⟩ := hR.post_mut_total _ _ hcall.1
  have h2 := hcall.2 f' r hpost
  cases r with
  | none =>
    change DWP (mrBudgetWP A ptr pty t mRely)
      (tryCallK v₀.toNat (callOut v₀.toNat none) >>= _) _ _ at h2
    simp only [tryCallK_none, retAfterDrop, vis_bind] at h2
    have hrf₁ := hadm.rely_refl m₁ s₀.cell hm₁
    obtain ⟨v₁, m₂, hl₁⟩ := hadm.load_ok m₁ s₀.cell hm₁
    obtain ⟨hv₁, _⟩ := hadm.load_val m₁ s₀.cell v₁ m₂ hm₁ hl₁
    have h3 := (((DWP.vis_iff _ _ _ _ _).1 h2 m₁ hrf₁).2 v₁ m₂ hl₁).2.1
      (hv₁.trans hv₀.symm) (hR.resolve_total f')
    simp only [ret_bind, Sum.elim_inr, DWP.ret_iff] at h3
  | some next =>
    change DWP (mrBudgetWP A ptr pty t mRely)
      (tryCallK v₀.toNat (callOut v₀.toNat (some next)) >>= _) _ _ at h2
    rw [tryCallK_some, vis_bind] at h2
    have hnext_rep : IntType.can_represent t (next : Int) = true := by
      have hrl : Rel init v₀.toNat := by
        rw [hv₀, hs₀.1]; exact hpre.cellInv.refl init
      have hf : A.fSpec.hist_inv f₀ s₀.fst := hs₀.2.1 ▸ A.fSpec.hist_inv_laws.refl f₀
      exact hrep s₀.fst v₀.toNat f' next hf hpost hrl
    have hrf₁ := hadm.rely_refl m₁ s₀.cell hm₁
    obtain ⟨ret, m₂, hcas⟩ := hadm.cas_ok m₁ s₀.cell v₀.toNat next hm₁ hnext_rep
    obtain ⟨hret, hstore, _⟩ := hadm.cas_val m₁ s₀.cell v₀.toNat next ret m₂ hm₁ hnext_rep hcas
    have heq : ret.toNat = v₀.toNat := hret.trans hv₀.symm
    have hwin := (((((DWP.vis_iff _ _ _ _ _).1 h2 m₁ hrf₁).2 ret m₂ hcas).2.1 heq).2 heq).1
    obtain ⟨g', hg'⟩ := hR.gc_post_total _ _ _ hwin.2.1
    have h3 := hwin.2.2 g' hg'
    simp only [tryCasK_true, retAfterDrop, vis_bind] at h3
    have hm₂ : MInv m₂ next := hstore hv₀.symm
    have hrf₂ := hadm.rely_refl m₂ next hm₂
    obtain ⟨v₂, m₃, hl₂⟩ := hadm.load_ok m₂ next hm₂
    obtain ⟨hv₂, _⟩ := hadm.load_val m₂ next v₂ m₃ hm₂ hl₂
    have h4 := (((DWP.vis_iff _ _ _ _ _).1 h3 m₂ hrf₂).2 v₂ m₃ hl₂).2.1
      hv₂ (hR.resolve_total f')
    simp only [ret_bind, Sum.elim_inr, DWP.ret_iff] at h4

/--
**General non-vacuity of `mrCellWP`**: for ANY memory model `M`, ANY
`Realizable A`, and ANY coupled `MrCellAdmissible` invariant, `mrCellWP` cannot
discharge `DWP … False` from any admissible state (`MInv m₀ s₀.cell`) — every
operation has a live successor keeping `MInv`.
-/
theorem mrCellWP_nonvacuous_not_false {M FState G : Type} [Memory M] [MemoryOps M]
    {A : AtomicEnv Nat FState G} {Rel : Nat → Nat → Prop}
    {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»} {t : IntType}
    {mRely : Machine M → Machine M → Prop} {MInv : Machine M → Nat → Prop}
    {init : Nat} {f₀ : FState} {g₀ : G} {comm₀ : OneShotCommitter Nat}
    (hR : A.Realizable)
    (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    (hrep : ∀ f₂ x f₃ (n : Nat), A.fSpec.hist_inv f₀ f₂ → A.fSpec.post_mut f₂ x f₃ (some n) →
      Rel init x → IntType.can_represent t (n : Int) = true)
    (hadm : MrCellAdmissible A ptr pty t mRely MInv)
    {m₀ : Machine M} {s₀ : AtomicSt Nat FState G}
    (hm₀ : MInv m₀ s₀.cell) (hs₀ : InitSt init f₀ g₀ comm₀ s₀) :
    ¬ DWP (mrCellWP A ptr pty t mRely) (tryUpdateLoop Nat) (fun _ _ => False) (m₀, s₀) := by
  intro hd
  have hsafe := tryUpdate_mr_always_safety hpre hrep hadm hm₀ hs₀
  refine DWP.induct (fun x ms =>
      Always (mrCellWP A ptr pty t mRely)
        (fun ms' => MInv ms'.1 ms'.2.cell ∧ HistInvSt A Rel init f₀ ms'.2)
        (fun r ms' => MInv ms'.1 ms'.2.cell ∧ CreusotPost A Rel init f₀ g₀ comm₀ r ms'.2)
        x ms → False) ?_ hd hsafe
  intro x ms hx ha
  have hm : MInv ms.1 ms.2.cell := ha.inv.1
  cases hobs : x.observe with
  | ret r => rw [hobs] at hx; exact hx
  | tau x' =>
    rw [hobs] at hx
    rw [Always.unfold_eq, hobs] at ha
    exact hx ha.2
  | vis i k =>
    rw [hobs] at hx
    rw [Always.unfold_eq, hobs] at ha
    have ha' := ha.2
    cases i with
    | call req =>
      cases req with
      | load =>
        have hrf := hadm.rely_refl ms.1 ms.2.cell hm
        obtain ⟨v, m₂, hok⟩ := hadm.load_ok ms.1 ms.2.cell hm
        exact ((hx ms.1 hrf).2 v m₂ hok).2 0 (((ha' ms.1 hrf).2 v m₂ hok).2 0)
      | cas e d =>
        have hrf := hadm.rely_refl ms.1 ms.2.cell hm
        obtain ⟨ret, m₂, hok⟩ := (ha' ms.1 hrf).1
        have hstepD := ((hx ms.1 hrf).2 ret m₂ hok).2 0
        have hstepA := ((ha' ms.1 hrf).2 ret m₂ hok).2 0
        by_cases he : ret.toNat = e
        · obtain ⟨_, hgp, hcont⟩ := (hstepD.2 he).1
          obtain ⟨g', hg'⟩ := hR.gc_post_total _ _ _ hgp
          exact hcont g' hg' ((hstepA.2 he).1.2.2 g' hg')
        · exact hstepD.1 he (hstepA.1 he)
      | callF arg =>
        obtain ⟨f', r, hpost⟩ := hR.post_mut_total _ _ hx.1
        exact hx.2 f' r hpost (ha'.2 f' r hpost)
      | dropF =>
        have hrf := hadm.rely_refl ms.1 ms.2.cell hm
        obtain ⟨v, m₂, hok⟩ := hadm.load_ok ms.1 ms.2.cell hm
        exact ((hx ms.1 hrf).2 v m₂ hok).2 0 (hR.resolve_total _)
          (((ha' ms.1 hrf).2 v m₂ hok).2 0 (hR.resolve_total _))
      | recv =>
        exact hx 0 (ha' 0)

/--
**Fail-closed width-representability boundary**: on any machine where `load`
reads `c`, an out-of-range `desired` (`IntType.can_represent t d = false`, e.g.
`d = 256` on `u8` even though `c ≤ d`) causes MiniRust `AtomicCompareExchange`
to emit `Stop.specPanic`, refuting `∃ ret m', mrCasOk …`. This is why
`MrCellAdmissible.cas_ok` must require `IntType.can_represent t d = true`
rather than an unbounded `Rel e d`.
-/
theorem mr_cas_out_of_range_specPanic_canary {M : Type} [Memory M] [MemoryOps M]
    {m m₁ : Machine M} {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»}
    {t : IntType} {al : Align} {c d : Nat}
    (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .ok (.Int c, m₁))
    (hout : IntType.can_represent t d = false) :
    ¬ ∃ ret m', mrCasOk m ptr pty t c d ret m' := by
  rintro ⟨ret, m', hok, _⟩
  have hsp := atomicCompareExchange_next_out_of_range_specPanic pty hal hsz hload hout
  rw [hsp] at hok; cases hok

/--
Generic fail-closed helper for `mrCellWP`: if `load` returns `v` (advancing
`m₀ ↦ m₁`) and the subsequent `cas(v, v + 1)` stops with an error (`ub` or
`specPanic`), `tryUpdateLoop` under `ticketEnv` refutes `DWLP`.
-/
theorem mrCellWP_rejects_load_then_cas_error {M : Type} [Memory M] [MemoryOps M]
    {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»} {t : IntType}
    {m₀ m₁ : Machine M} {v : Nat} {e : Stop}
    (hL : evalIntrinsicM m₀ .AtomicLoad [(.Ptr ⟨ptr, none⟩, pty)] (.Int t) = .ok (.Int v, m₁))
    (hC : evalIntrinsicM m₁ .AtomicCompareExchange
      [(.Ptr ⟨ptr, none⟩, pty), (.Int v, .Int t), (.Int ((v + 1 : Nat) : Int), .Int t)]
      (.Int t) = .error e)
    (s₀ : AtomicSt Nat PUnit PUnit)
    (Q : Except Nat Nat → MrAtomicSt M PUnit PUnit → Prop) :
    ¬ DWLP (mrCellWP ticketEnv ptr pty t Eq) (tryUpdateLoop Nat) Q (m₀, s₀) := by
  intro h
  have h1 := (((DWLP.vis_iff _ _ _ _ _).1 h m₀ rfl).2 v m₁ ⟨hL, Int.natCast_nonneg v⟩).2 0
  rw [Int.toNat_natCast] at h1
  dsimp only [loadAns] at h1
  rw [iter_tryBody_eq] at h1
  have h2 := ((DWLP.vis_iff _ _ _ _ _).1 h1).2 PUnit.unit (some (v + 1)) rfl
  change DWLP (mrCellWP ticketEnv ptr pty t Eq)
    (tryCallK v (callOut v (some (v + 1))) >>=
      Sum.elim (fun next => ITree.tau (ITree.iter tryBody next)) ITree.ret) Q _ at h2
  rw [tryCallK_some, vis_bind] at h2
  obtain ⟨_, _, hcas, _⟩ := ((DWLP.vis_iff _ _ _ _ _).1 h2 m₁ rfl).1
  rw [hC] at hcas; cases hcas

private theorem tb_frozen_load_then_cas_ub :
    (match tbLoad tbShared tbSharedPtr (.Int itU32) with
     | .ok (.Int 5, m1) =>
       match tbCas m1 tbSharedPtr 5 6 itU32 with
       | .error (.ub _) => true
       | _ => false
     | _ => false) = true := by decide +kernel

/--
**Fail-closed MiniRust UB rejection inside `mrCellWP`**: on `bmFive` with a
misaligned `u32` pointer (`case 17`), on `bmFive` with oversized `u128`
(`case 18`), and on `tbShared` through the Tree Borrows `Frozen` reference
(`case 27`, where `load` succeeds with `5` and `cas 5 6` faults UB),
`tryUpdateLoop` refutes `DWLP` for every postcondition.
-/
theorem mrCellWP_rejects_misaligned_u128_frozen
    (s₀ : AtomicSt Nat PUnit PUnit)
    (Qbm : Except Nat Nat → MrAtomicSt BM PUnit PUnit → Prop)
    (Qtb : Except Nat Nat → MrAtomicSt TBM PUnit PUnit → Prop) :
    ¬ DWLP (mrCellWP ticketEnv (bmPtr 1) tyRawPtr itU32 Eq) (tryUpdateLoop Nat) Qbm (bmFive, s₀) ∧
    ¬ DWLP (mrCellWP ticketEnv bmPtr tyRawPtr itU128 Eq) (tryUpdateLoop Nat) Qbm (bmFive, s₀) ∧
    ¬ DWLP (mrCellWP ticketEnv tbSharedPtr tyRawPtr itU32 Eq) (tryUpdateLoop Nat) Qtb
        (tbShared, s₀) := by
  refine ⟨fun h => ?_, fun h => ?_, ?_⟩
  · obtain ⟨v, m₂, hok, _⟩ := ((DWLP.vis_iff _ _ _ _ _).1 h bmFive rfl).1
    have hub := (atomic_u32_misaligned_ub_bm bmFive (bmPtr 1) tyRawPtr 0
      (.Int 0) (.Int 0) (.Int 0) .Add rfl (by decide)).2.1
    rw [hub] at hok; cases hok
  · obtain ⟨v, m₂, hok, _⟩ := ((DWLP.vis_iff _ _ _ _ _).1 h bmFive rfl).1
    have hub := (atomic_u128_size_too_big_ub bmFive bmPtr tyRawPtr (.Int 0) (.Int 0)
      (.Int itU128) .Add).2.1
    rw [hub] at hok; cases hok
  · have htb := tb_frozen_load_then_cas_ub
    cases hL : tbLoad tbShared tbSharedPtr (.Int itU32) with
    | error _ => rw [hL] at htb; cases htb
    | ok vm =>
      obtain ⟨val, m₁⟩ := vm
      cases val with
      | Int n =>
        by_cases hn : n = 5
        · subst hn
          rw [hL] at htb
          change (match tbCas m₁ tbSharedPtr 5 6 itU32 with
            | .error (.ub _) => true | _ => false) = true at htb
          cases hC : tbCas m₁ tbSharedPtr 5 6 itU32 with
          | ok _ => rw [hC] at htb; cases htb
          | error e => exact mrCellWP_rejects_load_then_cas_error hL hC s₀ Qtb
        · rw [hL] at htb
          cases n with
          | ofNat k =>
            match k with
            | 5 => exact absurd rfl hn
            | 0 | 1 | 2 | 3 | 4 | _ + 6 => cases htb
          | negSucc _ => cases htb
      | _ => rw [hL] at htb; cases htb

/--
**Fail-closed: an empty machine rely is miraculous.** If `mRely` admits no
machine step, `mrCellWP` discharges even `DWP … False`; `MrCellAdmissible`
therefore demands that interference may stutter (`rely_refl`).
-/
theorem mrCellWP_empty_rely_miracle {M FState G : Type} [Memory M] [MemoryOps M]
    (A : AtomicEnv Nat FState G) (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type»)
    (t : IntType) (ms : MrAtomicSt M FState G) :
    DWP (mrCellWP A ptr pty t (fun _ _ => False)) (tryUpdateLoop Nat) (fun _ _ => False) ms :=
  DWP.vis fun _ h => h.elim

private theorem tb_ticket_run :
    (match tbLoad tbFive tbPtr (.Int itU32) with
     | .ok (.Int 5, m1) =>
       match tbCas m1 tbPtr 5 6 itU32 with
       | .ok (.Int 5, m2) =>
         match tbLoad m2 tbPtr (.Int itU32) with
         | .ok (.Int 6, _) => true
         | _ => false
       | _ => false
     | _ => false) = true := by decide +kernel

private theorem tb_ticket_run_ex : ∃ m1 m2 m3,
    tbLoad tbFive tbPtr (.Int itU32) = .ok (.Int 5, m1) ∧
    tbCas m1 tbPtr 5 6 itU32 = .ok (.Int 5, m2) ∧
    tbLoad m2 tbPtr (.Int itU32) = .ok (.Int 6, m3) := by
  have h := tb_ticket_run
  split at h
  · rename_i m1 hL
    split at h
    · rename_i m2 hC
      split at h
      · rename_i m3 hL2
        exact ⟨m1, m2, m3, hL, hC, hL2⟩
      · cases h
    · cases h
  · cases h

/--
**Non-vacuity of `mrCellWP`**: on the real Tree Borrows cell `tbFive` (no
interference), the MiniRust execution `load = 5 → cas(5 → 6)✓ → load = 6`
drives the ticket `tryUpdateLoop` to a return, so `mrCellWP` cannot discharge
`DWP … False`.
-/
theorem mrCellWP_tb_ticket_nonvacuous (s₀ : AtomicSt Nat PUnit PUnit) :
    ¬ DWP (mrCellWP ticketEnv tbPtr tyRawPtr itU32 Eq) (tryUpdateLoop Nat) (fun _ _ => False)
      (tbFive, s₀) := by
  intro h
  obtain ⟨m1, m2, m3, hL, hC, hL2⟩ := tb_ticket_run_ex
  have hx : mrLoadOk tbFive tbPtr tyRawPtr itU32 5 m1 := ⟨hL, by decide⟩
  have hy : mrCasOk m1 tbPtr tyRawPtr itU32 5 (5 + 1) 5 m2 := ⟨hC, by decide⟩
  have hz : mrLoadOk m2 tbPtr tyRawPtr itU32 6 m3 := ⟨hL2, by decide⟩
  have h1 := (((DWP.vis_iff _ _ _ _ _).1 h tbFive (rfl : tbFive = tbFive)).2 5 m1 hx).2 0
  dsimp only [loadAns] at h1
  rw [iter_tryBody_eq] at h1
  have h2 := ((DWP.vis_iff _ _ _ _ _).1 h1).2 PUnit.unit (some (5 + 1)) rfl
  simp only at h2
  rw [show tryCallK (Int.toNat 5) (some (5 + 1)) =
    ITree.vis (aCas (Int.toNat 5) (5 + 1)) (tryCasK (Int.toNat 5) (5 + 1)) from rfl,
    vis_bind] at h2
  have h3 := ((((DWP.vis_iff _ _ _ _ _).1 h2 m1 (rfl : m1 = m1)).2 5 m2 hy).2 0).2 rfl
  have h4 := h3.1.2.2 PUnit.unit trivial
  simp only [tryCasK_true, retAfterDrop, vis_bind] at h4
  have h5 := (((DWP.vis_iff _ _ _ _ _).1 h4 m2 (rfl : m2 = m2)).2 6 m3 hz).2 0 trivial
  simp only [ret_bind, Sum.elim_inr, DWP.ret_iff] at h5

/-! #### Positive universal symbolic `MrCellAdmissible` instances (`Mach` & `MachTB`) -/

private abbrev mrALoad1 : Access := MiniRustSpec.AtomicIntrinsicsMR.aLoad 1
private abbrev mrAStore1 : Access := MiniRustSpec.AtomicIntrinsicsMR.aStore 1

/-- A `Mach` (`BasicMemory<x86_64>`) holding `u8` byte `b` with arbitrary access log `acc`. -/
def bmU8Mach (b : UInt8) (acc : List Access) : Mach :=
  bmMach [bmCell (.Init b none :: uninitBytes 7)] acc

/--
A `MachTB` (`TreeBorrowsMemory<x86_64>`) holding `u8` byte `b` with arbitrary access log `acc`.
-/
def tbU8Mach (b : UInt8) (acc : List Access) : MachTB :=
  let m0 := tbWith [.Init b none]
  { m0 with mem := { m0.mem with accesses := acc } }

theorem u8_inBounds (b : UInt8) : inBounds (b.toNat : Int) .Unsigned ⟨1⟩ = true := by
  have hb : b.toNat < 256 := b.toNat_lt
  simp [inBounds, Size.bits]; omega

theorem u8_can_represent_iff (n : Nat) :
    IntType.can_represent itU8 (n : Int) = true ↔ n < 256 := by
  simp [IntType.can_represent, inBounds, Size.bits]; omega

theorem u8_encodeM {M : Type} [Memory M] (d : UInt8) :
    Type.encodeM (M := M) (.Int itU8) (.Int d.toNat) = .ok [.Init d none] := by
  have hrep := u8_inBounds d
  have hd : d.toNat < 256 := d.toNat_lt
  simp only [Type.encodeM, Type.encodeIntM, Endianness.encode, x86_64.ENDIANNESS,
    hrep, ↓reduceIte, pure, Except.pure, leBytes, Size.bits]
  have hbyte : UInt8.ofNat (((d.toNat : Int) % 2 ^ (1 * 8)).toNat % 256) = d := by
    have hm : ((d.toNat : Int) % 2 ^ (1 * 8)).toNat % 256 = d.toNat := by omega
    rw [hm]; exact UInt8.ofNat_toNat
  simp only [List.map, hbyte]

theorem u8_decodeM {M : Type} [Memory M] [MemoryOps M] (b : UInt8) :
    Type.decodeM (M := M) (.Int itU8) [.Init b none] = .ok (some (.Int b.toNat)) := by
  simp [Type.decodeM, Type.decodeIntM, Endianness.decode, x86_64.ENDIANNESS,
    AbstractByte.dataM, leValue, pure, Except.pure]

theorem u8_layout : Type.layout (.Int itU8) = .ok (.Sized ⟨1⟩ ⟨1⟩) := rfl

/-- Symbolic MiniRust `typedLoadM` on `bmU8Mach b acc` for arbitrary `b : UInt8` and `acc`. -/
theorem bmU8_typedLoad (b : UInt8) (acc : List Access) :
    typedLoadM (M := BM) (bmU8Mach b acc) bmPtr (.Int itU8) ⟨1⟩ .Atomic =
      .ok (.Int b.toNat, bmU8Mach b (acc ++ [mrALoad1])) := by
  have hmem : MemoryOps.load (M := BM) (bmU8Mach b acc).mem.memory bmPtr ⟨1⟩ ⟨1⟩ =
      .ok ([.Init b none], (bmU8Mach b acc).mem.memory) := rfl
  unfold typedLoadM ConcurrentMemory.load
  rw [u8_layout, interp_ok_bind]
  change (pure (⟨1⟩ : Size) >>= fun size => _) = _
  rw [interp_pure_bind, hmem, interp_ok_bind, interp_pure_bind]
  dsimp only
  rw [u8_decodeM b, interp_ok_bind]
  simp only [checkValueM, IntType.can_represent, u8_inBounds b, ensureElseUb,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, interp_pure_bind]
  rfl

/-- Symbolic MiniRust `typedStoreM` on `bmU8Mach b acc` for arbitrary `b d : UInt8` and `acc`. -/
theorem bmU8_typedStore (b d : UInt8) (acc : List Access) :
    typedStoreM (M := BM) (bmU8Mach b acc) bmPtr (.Int d.toNat) (.Int itU8) ⟨1⟩ .Atomic =
      .ok (bmU8Mach d (acc ++ [mrAStore1])) := by
  have hmem : MemoryOps.store (M := BM) (bmU8Mach b acc).mem.memory bmPtr [.Init d none] ⟨1⟩ =
      .ok (bmU8Mach d acc).mem.memory := rfl
  unfold typedStoreM ConcurrentMemory.store
  simp only [checkValueM, IntType.can_represent, u8_inBounds d, ensureElseUb,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
    u8_encodeM d, interp_ok_bind]
  rw [hmem, interp_ok_bind, interp_ok_bind]
  rfl

/-- Symbolic MiniRust `typedLoadM` on `tbU8Mach b acc` for arbitrary `b : UInt8` and `acc`. -/
theorem tbU8_typedLoad (b : UInt8) (acc : List Access) :
    typedLoadM (M := TBM) (tbU8Mach b acc) tbPtr (.Int itU8) ⟨1⟩ .Atomic =
      .ok (.Int b.toNat, tbU8Mach b (acc ++ [mrALoad1])) := by
  have hmem : MemoryOps.load (M := TBM) (tbU8Mach b acc).mem.memory tbPtr ⟨1⟩ ⟨1⟩ =
      .ok ([.Init b none], (tbU8Mach b acc).mem.memory) := rfl
  unfold typedLoadM ConcurrentMemory.load
  rw [u8_layout, interp_ok_bind]
  change (pure (⟨1⟩ : Size) >>= fun size => _) = _
  rw [interp_pure_bind, hmem, interp_ok_bind, interp_pure_bind]
  dsimp only
  rw [u8_decodeM b, interp_ok_bind]
  simp only [checkValueM, IntType.can_represent, u8_inBounds b, ensureElseUb,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, interp_pure_bind]
  rfl

/-- Symbolic MiniRust `typedStoreM` on `tbU8Mach b acc` for arbitrary `b d : UInt8` and `acc`. -/
theorem tbU8_typedStore (b d : UInt8) (acc : List Access) :
    typedStoreM (M := TBM) (tbU8Mach b acc) tbPtr (.Int d.toNat) (.Int itU8) ⟨1⟩ .Atomic =
      .ok (tbU8Mach d (acc ++ [mrAStore1])) := by
  have hmem : MemoryOps.store (M := TBM) (tbU8Mach b acc).mem.memory tbPtr [.Init d none] ⟨1⟩ =
      .ok (tbU8Mach d acc).mem.memory := rfl
  unfold typedStoreM ConcurrentMemory.store
  simp only [checkValueM, IntType.can_represent, u8_inBounds d, ensureElseUb,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
    u8_encodeM d, interp_ok_bind]
  rw [hmem, interp_ok_bind, interp_ok_bind]
  rfl

/-- Every `tbU8Mach b acc` is `MachTB.wfLive` (derived via `evalIntrinsicM_atomic_tb_wfLive`). -/
theorem tbU8_wfLive (b : UInt8) (acc : List Access) :
    MiniRustSpec.Correspondence.MachTB.wfLive (tbU8Mach b acc) := by
  have h0 : MiniRustSpec.Correspondence.MachTB.wfLive (tbWith []) :=
    ep1_minirust_atomic_intrinsics_capstone.2.1.2
  have hmem : MemoryOps.store (M := TBM) (tbWith []).mem.memory tbPtr [.Init b none] ⟨1⟩ =
      .ok (tbU8Mach b []).mem.memory := rfl
  have hst : evalIntrinsicM (M := TBM) (tbWith []) .AtomicStore
      [(.Ptr ⟨tbPtr, none⟩, tyRawPtr), (.Int b.toNat, .Int itU8)] unitType =
      .ok (unitValueM, tbU8Mach b [mrAStore1]) := by
    rw [atomicStore_eq_typedStoreM (tbWith []) tbPtr tyRawPtr (.Int b.toNat) (.Int itU8)
      u8_layout rfl (by decide)]
    unfold typedStoreM ConcurrentMemory.store
    simp only [checkValueM, IntType.can_represent, u8_inBounds b, ensureElseUb,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      u8_encodeM b, interp_ok_bind, Int.toNat_natCast]
    rw [hmem, interp_ok_bind, interp_ok_bind, interp_ok_bind]
    rfl
  change MiniRustSpec.Correspondence.MachTB.wfLive (tbU8Mach b [mrAStore1])
  exact evalIntrinsicM_atomic_tb_wfLive rfl h0 hst

/-- Coupled invariant on `Mach`: the heap cell holds `u8` byte `c` (arbitrary access log). -/
def bmU8MInv (m : Mach) (c : Nat) : Prop :=
  ∃ (b : UInt8) (acc : List Access), b.toNat = c ∧ m = bmU8Mach b acc

/-- Coupled invariant on `MachTB`: the Tree Borrows cell holds `u8` byte `c` (arbitrary log). -/
def tbU8MInv (m : MachTB) (c : Nat) : Prop :=
  ∃ (b : UInt8) (acc : List Access), b.toNat = c ∧ m = tbU8Mach b acc

/-- Concurrent machine rely on `Mach`: other threads advance the `u8` byte along `rely`. -/
def bmU8MRely (rely : Nat → Nat → Prop) (m m' : Mach) : Prop :=
  ∃ (b b' : UInt8) (acc acc' : List Access),
    rely b.toNat b'.toNat ∧ m = bmU8Mach b acc ∧ m' = bmU8Mach b' acc'

/-- Concurrent machine rely on `MachTB`: other threads advance the `u8` byte along `rely`. -/
def tbU8MRely (rely : Nat → Nat → Prop) (m m' : MachTB) : Prop :=
  ∃ (b b' : UInt8) (acc acc' : List Access),
    rely b.toNat b'.toNat ∧ m = tbU8Mach b acc ∧ m' = tbU8Mach b' acc'

private theorem bmU8Mach_byte_inj {b₁ b₂ : UInt8} {acc₁ acc₂ : List Access}
    (h : bmU8Mach b₁ acc₁ = bmU8Mach b₂ acc₂) : b₁ = b₂ := by
  have h1 := congrArg (fun m => m.mem.memory.allocations) h
  dsimp [bmU8Mach, bmMach, bmCell] at h1
  have h2 := congrArg (fun a => a.data) (List.cons.inj h1).1
  exact (AbstractByte.Init.inj (List.cons.inj h2).1).1

private theorem tbU8Mach_byte_inj {b₁ b₂ : UInt8} {acc₁ acc₂ : List Access}
    (h : tbU8Mach b₁ acc₁ = tbU8Mach b₂ acc₂) : b₁ = b₂ := by
  have h1 := congrArg (fun m => m.mem.memory.mem.allocations) h
  dsimp [tbU8Mach, tbWith, tbMach, tbCell] at h1
  have h2 := congrArg (fun a => a.data) (List.cons.inj h1).1
  exact (AbstractByte.Init.inj (List.cons.inj h2).1).1

private theorem nat_to_u8_of_rep {d : Nat} (hd : IntType.can_represent itU8 (d : Int) = true) :
    ∃ db : UInt8, db.toNat = d := by
  have hlt : d < 256 := (u8_can_represent_iff d).1 hd
  exact ⟨UInt8.ofNat d, by simp [Nat.mod_eq_of_lt hlt]⟩

/--
**Positive universal `MrCellAdmissible` on `Mach` (`BasicMemory<x86_64>`)**:
holds for EVERY `AtomicEnv` with reflexive `A.rely`, arbitrary `u8` cell values
`0..255`, arbitrary access logs `acc`, and arbitrary `A.rely`-respecting
concurrent interference `bmU8MRely A.rely`.
-/
theorem bmU8_mrCellAdmissible {FState G : Type} (A : AtomicEnv Nat FState G)
    (hrefl : ∀ v, A.rely v v) :
    MrCellAdmissible A bmPtr tyRawPtr itU8 (bmU8MRely A.rely) bmU8MInv where
  rely_refl m c hm := by
    obtain ⟨b, acc, _, rfl⟩ := hm
    exact ⟨b, b, acc, acc, hrefl _, rfl, rfl⟩
  rely_pres m c m' hm hr := by
    obtain ⟨b, acc, rfl, rfl⟩ := hm
    obtain ⟨b₁, b', acc₁, acc', hrel, heq, rfl⟩ := hr
    have hb : b = b₁ := bmU8Mach_byte_inj heq
    subst hb
    exact ⟨b'.toNat, hrel, b', acc', rfl, rfl⟩
  load_ok m c hm := by
    obtain ⟨b, acc, rfl, rfl⟩ := hm
    refine ⟨b.toNat, bmU8Mach b (acc ++ [mrALoad1]), ?_, Int.natCast_nonneg _⟩
    rw [atomicLoad_eq_typedLoadM (bmU8Mach b acc) bmPtr tyRawPtr (.Int itU8) u8_layout rfl
      (by decide)]
    exact bmU8_typedLoad b acc
  load_val m c v m' hm hok := by
    obtain ⟨b, acc, rfl, rfl⟩ := hm
    obtain ⟨hok1, _⟩ := hok
    have hL : evalIntrinsicM (M := BM) (bmU8Mach b acc) .AtomicLoad
        [(.Ptr ⟨bmPtr, none⟩, tyRawPtr)] (.Int itU8) =
        .ok (.Int b.toNat, bmU8Mach b (acc ++ [mrALoad1])) := by
      rw [atomicLoad_eq_typedLoadM (bmU8Mach b acc) bmPtr tyRawPtr (.Int itU8) u8_layout rfl
        (by decide)]
      exact bmU8_typedLoad b acc
    rw [hL] at hok1
    obtain ⟨hv, rfl⟩ := Prod.mk.inj (Except.ok.inj hok1)
    cases hv
    exact ⟨Int.toNat_natCast _, b, acc ++ [mrALoad1], rfl, rfl⟩
  cas_ok m c e d hm hd := by
    obtain ⟨b, acc, rfl, rfl⟩ := hm
    obtain ⟨db, hdb⟩ := nat_to_u8_of_rep hd
    by_cases he : b.toNat = e
    · refine ⟨b.toNat, bmU8Mach db ((acc ++ [mrALoad1]) ++ [mrAStore1]), ?_,
        Int.natCast_nonneg _⟩
      have hst := bmU8_typedStore b db (acc ++ [mrALoad1])
      rw [hdb] at hst
      rw [← he]
      exact atomicCompareExchange_success tyRawPtr (al := ⟨1⟩) rfl (by decide)
        (bmU8_typedLoad b acc) hst
    · refine ⟨b.toNat, bmU8Mach b (acc ++ [mrALoad1]), ?_, Int.natCast_nonneg _⟩
      refine atomicCompareExchange_failure tyRawPtr (.Int d) (al := ⟨1⟩) rfl (by decide)
        (bmU8_typedLoad b acc) ?_
      intro hEq; exact he (Int.ofNat.inj (Value.Int.inj hEq)).symm
  cas_val m c e d ret m' hm hd hok := by
    obtain ⟨b, acc, rfl, rfl⟩ := hm
    obtain ⟨db, hdb⟩ := nat_to_u8_of_rep hd
    obtain ⟨hok1, _⟩ := hok
    by_cases he : b.toNat = e
    · have hst := bmU8_typedStore b db (acc ++ [mrALoad1])
      rw [hdb] at hst
      have hC : evalIntrinsicM (M := BM) (bmU8Mach b acc) .AtomicCompareExchange
          [(.Ptr ⟨bmPtr, none⟩, tyRawPtr), (.Int e, .Int itU8), (.Int d, .Int itU8)] (.Int itU8) =
          .ok (.Int b.toNat, bmU8Mach db ((acc ++ [mrALoad1]) ++ [mrAStore1])) := by
        rw [← he]
        exact atomicCompareExchange_success tyRawPtr (al := ⟨1⟩) rfl (by decide)
          (bmU8_typedLoad b acc) hst
      rw [hC] at hok1
      obtain ⟨hv, rfl⟩ := Prod.mk.inj (Except.ok.inj hok1)
      cases hv
      exact ⟨Int.toNat_natCast _, fun _ => ⟨db, (acc ++ [mrALoad1]) ++ [mrAStore1], hdb, rfl⟩,
        fun hne => absurd he hne⟩
    · have hC : evalIntrinsicM (M := BM) (bmU8Mach b acc) .AtomicCompareExchange
          [(.Ptr ⟨bmPtr, none⟩, tyRawPtr), (.Int e, .Int itU8), (.Int d, .Int itU8)] (.Int itU8) =
          .ok (.Int b.toNat, bmU8Mach b (acc ++ [mrALoad1])) := by
        refine atomicCompareExchange_failure tyRawPtr (.Int d) (al := ⟨1⟩) rfl (by decide)
          (bmU8_typedLoad b acc) ?_
        intro hEq; exact he (Int.ofNat.inj (Value.Int.inj hEq)).symm
      rw [hC] at hok1
      obtain ⟨hv, rfl⟩ := Prod.mk.inj (Except.ok.inj hok1)
      cases hv
      exact ⟨Int.toNat_natCast _, fun hEq => absurd hEq he,
        fun _ => ⟨b, acc ++ [mrALoad1], rfl, rfl⟩⟩

/--
**Positive universal `MrCellAdmissible` on `MachTB` (`TreeBorrowsMemory<x86_64>`)**:
holds for EVERY `AtomicEnv` with reflexive `A.rely`, arbitrary `u8` cell values
`0..255`, arbitrary access logs `acc`, and arbitrary `A.rely`-respecting
concurrent interference `tbU8MRely A.rely`, with `tbU8_wfLive` supplying
`MachTB.wfLive` at every configuration.
-/
theorem tbU8_mrCellAdmissible {FState G : Type} (A : AtomicEnv Nat FState G)
    (hrefl : ∀ v, A.rely v v) :
    MrCellAdmissible A tbPtr tyRawPtr itU8 (tbU8MRely A.rely) tbU8MInv where
  rely_refl m c hm := by
    obtain ⟨b, acc, _, rfl⟩ := hm
    exact ⟨b, b, acc, acc, hrefl _, rfl, rfl⟩
  rely_pres m c m' hm hr := by
    obtain ⟨b, acc, rfl, rfl⟩ := hm
    obtain ⟨b₁, b', acc₁, acc', hrel, heq, rfl⟩ := hr
    have hb : b = b₁ := tbU8Mach_byte_inj heq
    subst hb
    exact ⟨b'.toNat, hrel, b', acc', rfl, rfl⟩
  load_ok m c hm := by
    obtain ⟨b, acc, rfl, rfl⟩ := hm
    refine ⟨b.toNat, tbU8Mach b (acc ++ [mrALoad1]), ?_, Int.natCast_nonneg _⟩
    rw [atomicLoad_eq_typedLoadM (tbU8Mach b acc) tbPtr tyRawPtr (.Int itU8) u8_layout rfl
      (by decide)]
    exact tbU8_typedLoad b acc
  load_val m c v m' hm hok := by
    obtain ⟨b, acc, rfl, rfl⟩ := hm
    obtain ⟨hok1, _⟩ := hok
    have hL : evalIntrinsicM (M := TBM) (tbU8Mach b acc) .AtomicLoad
        [(.Ptr ⟨tbPtr, none⟩, tyRawPtr)] (.Int itU8) =
        .ok (.Int b.toNat, tbU8Mach b (acc ++ [mrALoad1])) := by
      rw [atomicLoad_eq_typedLoadM (tbU8Mach b acc) tbPtr tyRawPtr (.Int itU8) u8_layout rfl
        (by decide)]
      exact tbU8_typedLoad b acc
    rw [hL] at hok1
    obtain ⟨hv, rfl⟩ := Prod.mk.inj (Except.ok.inj hok1)
    cases hv
    exact ⟨Int.toNat_natCast _, b, acc ++ [mrALoad1], rfl, rfl⟩
  cas_ok m c e d hm hd := by
    obtain ⟨b, acc, rfl, rfl⟩ := hm
    obtain ⟨db, hdb⟩ := nat_to_u8_of_rep hd
    by_cases he : b.toNat = e
    · refine ⟨b.toNat, tbU8Mach db ((acc ++ [mrALoad1]) ++ [mrAStore1]), ?_,
        Int.natCast_nonneg _⟩
      have hst := tbU8_typedStore b db (acc ++ [mrALoad1])
      rw [hdb] at hst
      rw [← he]
      exact atomicCompareExchange_success tyRawPtr (al := ⟨1⟩) rfl (by decide)
        (tbU8_typedLoad b acc) hst
    · refine ⟨b.toNat, tbU8Mach b (acc ++ [mrALoad1]), ?_, Int.natCast_nonneg _⟩
      refine atomicCompareExchange_failure tyRawPtr (.Int d) (al := ⟨1⟩) rfl (by decide)
        (tbU8_typedLoad b acc) ?_
      intro hEq; exact he (Int.ofNat.inj (Value.Int.inj hEq)).symm
  cas_val m c e d ret m' hm hd hok := by
    obtain ⟨b, acc, rfl, rfl⟩ := hm
    obtain ⟨db, hdb⟩ := nat_to_u8_of_rep hd
    obtain ⟨hok1, _⟩ := hok
    by_cases he : b.toNat = e
    · have hst := tbU8_typedStore b db (acc ++ [mrALoad1])
      rw [hdb] at hst
      have hC : evalIntrinsicM (M := TBM) (tbU8Mach b acc) .AtomicCompareExchange
          [(.Ptr ⟨tbPtr, none⟩, tyRawPtr), (.Int e, .Int itU8), (.Int d, .Int itU8)] (.Int itU8) =
          .ok (.Int b.toNat, tbU8Mach db ((acc ++ [mrALoad1]) ++ [mrAStore1])) := by
        rw [← he]
        exact atomicCompareExchange_success tyRawPtr (al := ⟨1⟩) rfl (by decide)
          (tbU8_typedLoad b acc) hst
      rw [hC] at hok1
      obtain ⟨hv, rfl⟩ := Prod.mk.inj (Except.ok.inj hok1)
      cases hv
      exact ⟨Int.toNat_natCast _, fun _ => ⟨db, (acc ++ [mrALoad1]) ++ [mrAStore1], hdb, rfl⟩,
        fun hne => absurd he hne⟩
    · have hC : evalIntrinsicM (M := TBM) (tbU8Mach b acc) .AtomicCompareExchange
          [(.Ptr ⟨tbPtr, none⟩, tyRawPtr), (.Int e, .Int itU8), (.Int d, .Int itU8)] (.Int itU8) =
          .ok (.Int b.toNat, tbU8Mach b (acc ++ [mrALoad1])) := by
        refine atomicCompareExchange_failure tyRawPtr (.Int d) (al := ⟨1⟩) rfl (by decide)
          (tbU8_typedLoad b acc) ?_
        intro hEq; exact he (Int.ofNat.inj (Value.Int.inj hEq)).symm
      rw [hC] at hok1
      obtain ⟨hv, rfl⟩ := Prod.mk.inj (Except.ok.inj hok1)
      cases hv
      exact ⟨Int.toNat_natCast _, fun hEq => absurd hEq he,
        fun _ => ⟨b, acc ++ [mrALoad1], rfl, rfl⟩⟩

/--
**End-to-end positive Tree Borrows `MachTB` witness**: for ANY `Realizable`
bounded `u8` environment (`hrep`), `tryUpdateLoop` executed directly over
MiniRust `TreeBorrowsMemory` (`mrCellWP`) under concurrent `tbU8MRely A.rely`
interference preserves `tbU8MInv ∧ MachTB.wfLive ∧ HistInvSt` at every step,
satisfies `CreusotPost` upon return, and is provably non-vacuous (`¬ DWP … False`).
-/
theorem tryUpdate_mr_tb_u8_safety {FState G : Type} {A : AtomicEnv Nat FState G}
    {Rel : Nat → Nat → Prop} {init : Nat} {f₀ : FState} {g₀ : G}
    {comm₀ : OneShotCommitter Nat}
    (hR : A.Realizable)
    (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    (hrep : ∀ f₂ x f₃ n, A.fSpec.hist_inv f₀ f₂ → A.fSpec.post_mut f₂ x f₃ (some n) →
      Rel init x → n < 256)
    (b₀ : UInt8) (acc₀ : List Access) {s₀ : AtomicSt Nat FState G}
    (hb₀ : b₀.toNat = init) (hs₀ : InitSt init f₀ g₀ comm₀ s₀) :
    Always (mrCellWP A tbPtr tyRawPtr itU8 (tbU8MRely A.rely))
      (fun ms => (tbU8MInv ms.1 ms.2.cell ∧ MiniRustSpec.Correspondence.MachTB.wfLive ms.1) ∧
        HistInvSt A Rel init f₀ ms.2)
      (fun r ms => (tbU8MInv ms.1 ms.2.cell ∧ MiniRustSpec.Correspondence.MachTB.wfLive ms.1) ∧
        CreusotPost A Rel init f₀ g₀ comm₀ r ms.2)
      (tryUpdateLoop Nat) (tbU8Mach b₀ acc₀, s₀) ∧
    ¬ DWP (mrCellWP A tbPtr tyRawPtr itU8 (tbU8MRely A.rely))
      (tryUpdateLoop Nat) (fun _ _ => False) (tbU8Mach b₀ acc₀, s₀) := by
  have hadm := tbU8_mrCellAdmissible A hR.rely_refl
  have hrep' : ∀ f₂ x f₃ n, A.fSpec.hist_inv f₀ f₂ → A.fSpec.post_mut f₂ x f₃ (some n) →
      Rel init x → IntType.can_represent itU8 (n : Int) = true :=
    fun f₂ x f₃ n hf hp hr => (u8_can_represent_iff n).2 (hrep f₂ x f₃ n hf hp hr)
  have hm₀ : tbU8MInv (tbU8Mach b₀ acc₀) s₀.cell := ⟨b₀, acc₀, hb₀.trans hs₀.1.symm, rfl⟩
  have hrely_wf : ∀ m m', MiniRustSpec.Correspondence.MachTB.wfLive m →
      tbU8MRely A.rely m m' → MiniRustSpec.Correspondence.MachTB.wfLive m' := by
    rintro m m' _ ⟨_, b', _, acc', _, _, rfl⟩
    exact tbU8_wfLive b' acc'
  exact ⟨tryUpdate_mr_tb_wfLive_safety hpre hrep' hadm hrely_wf hm₀ (tbU8_wfLive b₀ acc₀) hs₀,
    mrCellWP_nonvacuous_not_false hR hpre hrep' hadm hm₀ hs₀⟩

/--
**End-to-end positive `BasicMemory` `Mach` witness**: for ANY `Realizable`
bounded `u8` environment (`hrep`), `tryUpdateLoop` executed directly over
MiniRust `BasicMemory` (`mrCellWP`) under concurrent `bmU8MRely A.rely`
interference preserves `bmU8MInv ∧ HistInvSt` at every step, satisfies
`CreusotPost`, and is provably non-vacuous (`¬ DWP … False`).
-/
theorem tryUpdate_mr_bm_u8_safety {FState G : Type} {A : AtomicEnv Nat FState G}
    {Rel : Nat → Nat → Prop} {init : Nat} {f₀ : FState} {g₀ : G}
    {comm₀ : OneShotCommitter Nat}
    (hR : A.Realizable)
    (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    (hrep : ∀ f₂ x f₃ n, A.fSpec.hist_inv f₀ f₂ → A.fSpec.post_mut f₂ x f₃ (some n) →
      Rel init x → n < 256)
    (b₀ : UInt8) (acc₀ : List Access) {s₀ : AtomicSt Nat FState G}
    (hb₀ : b₀.toNat = init) (hs₀ : InitSt init f₀ g₀ comm₀ s₀) :
    Always (mrCellWP A bmPtr tyRawPtr itU8 (bmU8MRely A.rely))
      (fun ms => bmU8MInv ms.1 ms.2.cell ∧ HistInvSt A Rel init f₀ ms.2)
      (fun r ms => bmU8MInv ms.1 ms.2.cell ∧ CreusotPost A Rel init f₀ g₀ comm₀ r ms.2)
      (tryUpdateLoop Nat) (bmU8Mach b₀ acc₀, s₀) ∧
    ¬ DWP (mrCellWP A bmPtr tyRawPtr itU8 (bmU8MRely A.rely))
      (tryUpdateLoop Nat) (fun _ _ => False) (bmU8Mach b₀ acc₀, s₀) := by
  have hadm := bmU8_mrCellAdmissible A hR.rely_refl
  have hrep' : ∀ f₂ x f₃ n, A.fSpec.hist_inv f₀ f₂ → A.fSpec.post_mut f₂ x f₃ (some n) →
      Rel init x → IntType.can_represent itU8 (n : Int) = true :=
    fun f₂ x f₃ n hf hp hr => (u8_can_represent_iff n).2 (hrep f₂ x f₃ n hf hp hr)
  have hm₀ : bmU8MInv (bmU8Mach b₀ acc₀) s₀.cell := ⟨b₀, acc₀, hb₀.trans hs₀.1.symm, rfl⟩
  exact ⟨tryUpdate_mr_always_safety hpre hrep' hadm hm₀ hs₀,
    mrCellWP_nonvacuous_not_false hR hpre hrep' hadm hm₀ hs₀⟩

/--
**Streett liveness on a real symbolic `u8` `Mach` cell**: for every byte `b₀`,
every access log, and arbitrary `rely`-respecting concurrent interference, once
a weak CAS wins infinitely often `tryUpdateLoop` returns through MiniRust
`evalIntrinsicM` with the `creusot#2386` contract (`CoBuchi` form).
-/
theorem tryUpdate_mr_bm_u8_fair {FState G : Type} {A : AtomicEnv Nat FState G}
    {Rel : Nat → Nat → Prop} {init : Nat} {f₀ : FState} {g₀ : G}
    {comm₀ : OneShotCommitter Nat}
    (hrefl : ∀ v, A.rely v v)
    (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    (hrep : ∀ f₂ x f₃ n, A.fSpec.hist_inv f₀ f₂ → A.fSpec.post_mut f₂ x f₃ (some n) →
      Rel init x → n < 256)
    (b₀ : UInt8) (acc₀ : List Access) {s₀ : AtomicSt Nat FState G}
    (hb₀ : b₀.toNat = init) (hs₀ : InitSt init f₀ g₀ comm₀ s₀) :
    CoBuchi (mrCellWP A bmPtr tyRawPtr itU8 (bmU8MRely A.rely)) CasWon
      (fun r ms => bmU8MInv ms.1 ms.2.cell ∧ CreusotPost A Rel init f₀ g₀ comm₀ r ms.2)
      (tryUpdateLoop Nat) (bmU8Mach b₀ acc₀, s₀) :=
  tryUpdate_mr_fairInfOften hpre
    (fun f₂ x f₃ n hf hp hr => (u8_can_represent_iff n).2 (hrep f₂ x f₃ n hf hp hr))
    (bmU8_mrCellAdmissible A hrefl) ⟨b₀, acc₀, hb₀.trans hs₀.1.symm, rfl⟩ hs₀ _

/--
**Tree Borrows `u8` Streett liveness + enabledness + non-vacuity**: closes the
`MachTB` parity gap on `u8`, proving `CoBuchi CasWon`, `InfOften CasAttempt`,
and `¬ CoBuchi CasWon False` with `MachTB.wfLive` preserved at every step.
-/
theorem tryUpdate_mr_tb_u8_fair {FState G : Type} {A : AtomicEnv Nat FState G}
    {Rel : Nat → Nat → Prop} {init : Nat} {f₀ : FState} {g₀ : G}
    {comm₀ : OneShotCommitter Nat}
    (hR : A.Realizable)
    (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    (hrep : ∀ f₂ x f₃ n, A.fSpec.hist_inv f₀ f₂ → A.fSpec.post_mut f₂ x f₃ (some n) →
      Rel init x → n < 256)
    (b₀ : UInt8) (acc₀ : List Access) {s₀ : AtomicSt Nat FState G}
    (hb₀ : b₀.toNat = init) (hs₀ : InitSt init f₀ g₀ comm₀ s₀) :
    CoBuchi (mrCellWP A tbPtr tyRawPtr itU8 (tbU8MRely A.rely)) CasWon
      (fun r ms => (tbU8MInv ms.1 ms.2.cell ∧ MiniRustSpec.Correspondence.MachTB.wfLive ms.1) ∧
        CreusotPost A Rel init f₀ g₀ comm₀ r ms.2)
      (tryUpdateLoop Nat) (tbU8Mach b₀ acc₀, s₀) ∧
    InfOften (mrCellWP A tbPtr tyRawPtr itU8 (tbU8MRely A.rely)) CasAttempt
      (fun r ms => (tbU8MInv ms.1 ms.2.cell ∧ MiniRustSpec.Correspondence.MachTB.wfLive ms.1) ∧
        CreusotPost A Rel init f₀ g₀ comm₀ r ms.2)
      (tryUpdateLoop Nat) (tbU8Mach b₀ acc₀, s₀) ∧
    ¬ CoBuchi (mrCellWP A tbPtr tyRawPtr itU8 (tbU8MRely A.rely)) CasWon
      (fun _ _ => False) (tryUpdateLoop Nat) (tbU8Mach b₀ acc₀, s₀) := by
  have hadm := tbU8_mrCellAdmissible A hR.rely_refl
  have hrep' : ∀ f₂ x f₃ (n : Nat), A.fSpec.hist_inv f₀ f₂ →
      A.fSpec.post_mut f₂ x f₃ (some n) → Rel init x →
      IntType.can_represent itU8 (n : Int) = true :=
    fun f₂ x f₃ n hf hp hr => (u8_can_represent_iff n).2 (hrep f₂ x f₃ n hf hp hr)
  have hm₀ : tbU8MInv (tbU8Mach b₀ acc₀) s₀.cell := ⟨b₀, acc₀, hb₀.trans hs₀.1.symm, rfl⟩
  have hrely_wf : ∀ m m', MiniRustSpec.Correspondence.MachTB.wfLive m →
      tbU8MRely A.rely m m' → MiniRustSpec.Correspondence.MachTB.wfLive m' := by
    rintro m m' _ ⟨_, b', _, acc', _, _, rfl⟩
    exact tbU8_wfLive b' acc'
  have hf := tryUpdate_mr_tb_wfLive_fair hpre hrep' hadm hrely_wf hm₀ (tbU8_wfLive b₀ acc₀) hs₀
    (fun _ _ _ _ => False)
  exact ⟨hf.1, hf.2, tryUpdate_mr_fairInfOften_nonvacuous hR hpre hrep' hadm hm₀ hs₀ _ _⟩

/-!
#### Positive universal symbolic 8-byte little-endian `u64` instances (`Mach` & `MachTB`)

Unlike 1-byte `u8` (`Align 1`), `itU64` exercises real multi-byte little-endian
encoding/decoding (`leBytes` / `leValue` across all 8 bytes of the 8-aligned
`bmCell` / `tbCell` allocation) and `Align 8` checks on both `BasicMemory` and
`TreeBorrowsMemory` (`MachTB.wfLive`).
-/

private abbrev mrALoad8 : Access := MiniRustSpec.AtomicIntrinsicsMR.aLoad 8
private abbrev mrAStore8 : Access := MiniRustSpec.AtomicIntrinsicsMR.aStore 8

/-- Little-endian byte round-trip for every byte width `n` and unsigned integer `u`. -/
theorem leValue_leBytes (n : Nat) : ∀ u : Nat, leValue (leBytes u n) = u % 256 ^ n := by
  induction n with
  | zero => intro u; simp [leBytes, leValue, Nat.mod_one]
  | succ n ih =>
    intro u
    simp only [leBytes, leValue, ih (u / 256)]
    have hlt : u % 256 < 256 := Nat.mod_lt u (by decide)
    have hu8 : (UInt8.ofNat (u % 256)).toNat = u % 256 := by
      simp [Nat.mod_eq_of_lt hlt]
    rw [hu8, Nat.pow_succ, Nat.mul_comm (256 ^ n) 256]
    have hpow : 0 < 256 ^ n := Nat.pow_pos (by decide)
    have hlt2 : (u / 256) % 256 ^ n < 256 ^ n := Nat.mod_lt _ hpow
    have hbound : u % 256 + 256 * ((u / 256) % 256 ^ n) < 256 * 256 ^ n := by
      have := Nat.mul_le_mul_left 256 (Nat.le_sub_one_of_lt hlt2)
      omega
    have hdecomp : u = (256 * 256 ^ n) * ((u / 256) / 256 ^ n) +
        (u % 256 + 256 * ((u / 256) % 256 ^ n)) := by
      have h1 : u = 256 * (u / 256) + u % 256 := (Nat.div_add_mod u 256).symm
      have h2 : u / 256 = 256 ^ n * ((u / 256) / 256 ^ n) + (u / 256) % 256 ^ n :=
        (Nat.div_add_mod (u / 256) (256 ^ n)).symm
      calc u = 256 * (256 ^ n * ((u / 256) / 256 ^ n) + (u / 256) % 256 ^ n) + u % 256 := by
            conv => lhs; rw [h1, h2]
        _ = (256 * 256 ^ n) * ((u / 256) / 256 ^ n) +
              (u % 256 + 256 * ((u / 256) % 256 ^ n)) := by
            rw [Nat.mul_add, ← Nat.mul_assoc]; omega
    conv => rhs; rw [hdecomp]
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hbound]

/-- The 8 initialized little-endian bytes of a `UInt64`. -/
def u64InitBytes {P : Type} (x : UInt64) : List (AbstractByte P) :=
  (leBytes x.toNat 8).map (AbstractByte.Init · none)

/-- A `Mach` (`BasicMemory<x86_64>`) holding 8-byte little-endian `x : UInt64` and log `acc`. -/
def bmU64Mach (x : UInt64) (acc : List Access) : Mach :=
  bmMach [bmCell (u64InitBytes x)] acc

/--
A `MachTB` (`TreeBorrowsMemory<x86_64>`) holding 8-byte little-endian `x : UInt64` and log `acc`.
-/
def tbU64Mach (x : UInt64) (acc : List Access) : MachTB :=
  let m0 := tbWith (u64InitBytes x)
  { m0 with mem := { m0.mem with accesses := acc } }

private theorem int_two_pow_64 : (2 : Int) ^ (8 * 8) = ((2 ^ 64 : Nat) : Int) := by
  rw [show 8 * 8 = 64 from rfl]
  exact (Int.natCast_pow 2 64).symm

private theorem pow256_8_eq : (256 : Nat) ^ 8 = 2 ^ 64 := by
  rw [show (256 : Nat) = 2 ^ 8 from by decide, ← Nat.pow_mul]

theorem u64_inBounds (x : UInt64) : inBounds (x.toNat : Int) .Unsigned ⟨8⟩ = true := by
  have hx : x.toNat < 2 ^ 64 := x.toNat_lt
  unfold inBounds Size.bits; dsimp only
  rw [int_two_pow_64]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.2 hx⟩

theorem u64_can_represent_iff (n : Nat) :
    IntType.can_represent itU64 (n : Int) = true ↔ n < 2 ^ 64 := by
  unfold IntType.can_represent itU64 inBounds Size.bits; dsimp only
  rw [int_two_pow_64]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Int.natCast_nonneg, true_and, Int.ofNat_lt]

private theorem u64_endianness_encode (x : UInt64) :
    Endianness.encode x86_64.ENDIANNESS .Unsigned ⟨8⟩ (x.toNat : Int) =
      some (leBytes x.toNat 8) := by
  have hx : x.toNat < 2 ^ 64 := x.toNat_lt
  have hmod : ((x.toNat : Int) % (2 : Int) ^ Size.bits ⟨8⟩).toNat = x.toNat := by
    change ((x.toNat : Int) % (2 : Int) ^ (8 * 8)).toNat = x.toNat
    rw [int_two_pow_64, ← Int.natCast_emod, Nat.mod_eq_of_lt hx, Int.toNat_natCast]
  unfold Endianness.encode
  rw [u64_inBounds x]
  simp only [↓reduceIte, x86_64.ENDIANNESS, hmod]

theorem u64_encodeM {M : Type} [Memory M] (x : UInt64) :
    Type.encodeM (M := M) (.Int itU64) (.Int x.toNat) = .ok (u64InitBytes x) := by
  rw [Type.encodeM, Type.encodeIntM, u64_endianness_encode x]
  rfl

private theorem u64_checkValueM {M : Type} [Memory M] [MemoryOps M]
    (x : UInt64) (m : Option (Machine M)) :
    checkValueM (M := M) (.Int x.toNat) (.Int itU64) m = .ok () := by
  rw [checkValueM]
  unfold IntType.can_represent
  dsimp only [itU64]
  rw [u64_inBounds x]
  rfl

private theorem mapM_init_dataM_8 {P : Type} (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    List.mapM (AbstractByte.dataM (Provenance := P))
      ([b0, b1, b2, b3, b4, b5, b6, b7].map (AbstractByte.Init · none)) =
      some [b0, b1, b2, b3, b4, b5, b6, b7] := rfl

theorem u64_decodeM {M : Type} [Memory M] [MemoryOps M] (x : UInt64) :
    Type.decodeM (M := M) (.Int itU64) (u64InitBytes x) = .ok (some (.Int x.toNat)) := by
  have hlt : x.toNat < 256 ^ 8 := pow256_8_eq ▸ x.toNat_lt
  have hlen : (u64InitBytes (P := Memory.Provenance M) x).length = 8 := rfl
  have hmap : List.mapM (AbstractByte.dataM (Provenance := Memory.Provenance M))
      (u64InitBytes x) = some (leBytes x.toNat 8) :=
    mapM_init_dataM_8 _ _ _ _ _ _ _ _
  unfold Type.decodeM Type.decodeIntM Endianness.decode
  simp only [x86_64.ENDIANNESS, hlen, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [hmap]
  dsimp only [pure, Except.pure]
  rw [leValue_leBytes, Nat.mod_eq_of_lt hlt]

theorem u64_layout : Type.layout (.Int itU64) = .ok (.Sized ⟨8⟩ ⟨8⟩) := rfl

/-- Symbolic 8-byte MiniRust `typedLoadM` on `bmU64Mach x acc` for arbitrary `x : UInt64`. -/
theorem bmU64_typedLoad (x : UInt64) (acc : List Access) :
    typedLoadM (M := BM) (bmU64Mach x acc) bmPtr (.Int itU64) ⟨8⟩ .Atomic =
      .ok (.Int x.toNat, bmU64Mach x (acc ++ [mrALoad8])) := by
  have hmem : MemoryOps.load (M := BM) (bmU64Mach x acc).mem.memory bmPtr ⟨8⟩ ⟨8⟩ =
      .ok (u64InitBytes x, (bmU64Mach x acc).mem.memory) := rfl
  unfold typedLoadM ConcurrentMemory.load
  rw [u64_layout, interp_ok_bind]
  change (pure (⟨8⟩ : Size) >>= fun size => _) = _
  rw [interp_pure_bind, hmem, interp_ok_bind, interp_pure_bind]
  dsimp only
  rw [u64_decodeM x, interp_ok_bind]
  simp only [checkValueM, IntType.can_represent, u64_inBounds x, ensureElseUb,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, interp_pure_bind]
  rfl

private theorem typedStoreM_of_ok {M : Type} [Memory M] [MemoryOps M]
    {m : Machine M} {ptr : ThinPointer (Memory.Provenance M)}
    {val : Value M} {ty : «Type»} {align : Align} {atomicity : Atomicity}
    {bytes : List (AbstractByte (Memory.Provenance M))} {mem' : M}
    (hchk : checkValueM val ty (some m) = .ok ())
    (henc : Type.encodeM (M := M) ty val = .ok bytes)
    (hmem : MemoryOps.store m.mem.memory ptr bytes align = .ok mem') :
    typedStoreM m ptr val ty align atomicity =
      .ok { m with mem := ConcurrentMemory.mk mem' (m.mem.accesses ++
        [{ ty := .Store, atomicity := atomicity, addr := ptr.addr,
           len := ⟨bytes.length⟩ }]) } := by
  unfold typedStoreM ConcurrentMemory.store
  rw [hchk]
  dsimp only
  rw [henc, interp_ok_bind, hmem, interp_ok_bind, interp_pure_bind]
  rfl

/-- Symbolic 8-byte MiniRust `typedStoreM` on `bmU64Mach x acc` for arbitrary `x y : UInt64`. -/
theorem bmU64_typedStore (x y : UInt64) (acc : List Access) :
    typedStoreM (M := BM) (bmU64Mach x acc) bmPtr (.Int y.toNat) (.Int itU64) ⟨8⟩ .Atomic =
      .ok (bmU64Mach y (acc ++ [mrAStore8])) := by
  have hmem : MemoryOps.store (M := BM) (bmU64Mach x acc).mem.memory bmPtr (u64InitBytes y) ⟨8⟩ =
      .ok (bmU64Mach y acc).mem.memory := rfl
  exact typedStoreM_of_ok (u64_checkValueM y _) (u64_encodeM y) hmem

/-- Symbolic 8-byte MiniRust `typedLoadM` on `tbU64Mach x acc` for arbitrary `x : UInt64`. -/
theorem tbU64_typedLoad (x : UInt64) (acc : List Access) :
    typedLoadM (M := TBM) (tbU64Mach x acc) tbPtr (.Int itU64) ⟨8⟩ .Atomic =
      .ok (.Int x.toNat, tbU64Mach x (acc ++ [mrALoad8])) := by
  have hmem : MemoryOps.load (M := TBM) (tbU64Mach x acc).mem.memory tbPtr ⟨8⟩ ⟨8⟩ =
      .ok (u64InitBytes x, (tbU64Mach x acc).mem.memory) := rfl
  unfold typedLoadM ConcurrentMemory.load
  rw [u64_layout, interp_ok_bind]
  change (pure (⟨8⟩ : Size) >>= fun size => _) = _
  rw [interp_pure_bind, hmem, interp_ok_bind, interp_pure_bind]
  dsimp only
  rw [u64_decodeM x, interp_ok_bind]
  simp only [checkValueM, IntType.can_represent, u64_inBounds x, ensureElseUb,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, interp_pure_bind]
  rfl

/-- Symbolic 8-byte MiniRust `typedStoreM` on `tbU64Mach x acc` for arbitrary `x y : UInt64`. -/
theorem tbU64_typedStore (x y : UInt64) (acc : List Access) :
    typedStoreM (M := TBM) (tbU64Mach x acc) tbPtr (.Int y.toNat) (.Int itU64) ⟨8⟩ .Atomic =
      .ok (tbU64Mach y (acc ++ [mrAStore8])) := by
  have hmem : MemoryOps.store (M := TBM) (tbU64Mach x acc).mem.memory tbPtr (u64InitBytes y) ⟨8⟩ =
      .ok (tbU64Mach y acc).mem.memory := rfl
  exact typedStoreM_of_ok (u64_checkValueM y _) (u64_encodeM y) hmem

/-- Every `tbU64Mach x acc` is `MachTB.wfLive` (derived via `evalIntrinsicM_atomic_tb_wfLive`). -/
theorem tbU64_wfLive (x : UInt64) (acc : List Access) :
    MiniRustSpec.Correspondence.MachTB.wfLive (tbU64Mach x acc) := by
  have h0 : MiniRustSpec.Correspondence.MachTB.wfLive (tbWith []) :=
    ep1_minirust_atomic_intrinsics_capstone.2.1.2
  have hmem : MemoryOps.store (M := TBM) (tbWith []).mem.memory tbPtr (u64InitBytes x) ⟨8⟩ =
      .ok (tbU64Mach x []).mem.memory := rfl
  have hst : evalIntrinsicM (M := TBM) (tbWith []) .AtomicStore
      [(.Ptr ⟨tbPtr, none⟩, tyRawPtr), (.Int x.toNat, .Int itU64)] unitType =
      .ok (unitValueM, tbU64Mach x [mrAStore8]) := by
    rw [atomicStore_eq_typedStoreM (tbWith []) tbPtr tyRawPtr (.Int x.toNat) (.Int itU64)
      u64_layout rfl (by decide)]
    have hts : typedStoreM (M := TBM) (tbWith []) tbPtr (.Int x.toNat) (.Int itU64)
        ⟨((8 : Nat) : Int).toNat⟩ .Atomic = .ok (tbU64Mach x [mrAStore8]) :=
      typedStoreM_of_ok (u64_checkValueM x _) (u64_encodeM x) hmem
    rw [hts, interp_ok_bind]
    rfl
  change MiniRustSpec.Correspondence.MachTB.wfLive (tbU64Mach x [mrAStore8])
  exact evalIntrinsicM_atomic_tb_wfLive rfl h0 hst

/-- Coupled invariant on `Mach`: the 8-byte heap cell holds little-endian `u64` `c`. -/
def bmU64MInv (m : Mach) (c : Nat) : Prop :=
  ∃ (x : UInt64) (acc : List Access), x.toNat = c ∧ m = bmU64Mach x acc

/-- Coupled invariant on `MachTB`: the 8-byte Tree Borrows cell holds little-endian `u64` `c`. -/
def tbU64MInv (m : MachTB) (c : Nat) : Prop :=
  ∃ (x : UInt64) (acc : List Access), x.toNat = c ∧ m = tbU64Mach x acc

/-- Concurrent 8-byte machine rely on `Mach`. -/
def bmU64MRely (rely : Nat → Nat → Prop) (m m' : Mach) : Prop :=
  ∃ (x x' : UInt64) (acc acc' : List Access),
    rely x.toNat x'.toNat ∧ m = bmU64Mach x acc ∧ m' = bmU64Mach x' acc'

/-- Concurrent 8-byte machine rely on `MachTB`. -/
def tbU64MRely (rely : Nat → Nat → Prop) (m m' : MachTB) : Prop :=
  ∃ (x x' : UInt64) (acc acc' : List Access),
    rely x.toNat x'.toNat ∧ m = tbU64Mach x acc ∧ m' = tbU64Mach x' acc'

private theorem list_map_inj {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b) :
    ∀ {l₁ l₂ : List α}, l₁.map f = l₂.map f → l₁ = l₂
  | [], [], _ => rfl
  | _ :: _, [], h => nomatch h
  | [], _ :: _, h => nomatch h
  | a :: as, b :: bs, h => by
    have ⟨h1, h2⟩ := List.cons.inj h
    rw [hf a b h1, list_map_inj hf h2]

private theorem u64InitBytes_inj {P : Type} {x₁ x₂ : UInt64}
    (h : u64InitBytes (P := P) x₁ = u64InitBytes (P := P) x₂) : x₁ = x₂ := by
  have hmap : leBytes x₁.toNat 8 = leBytes x₂.toNat 8 :=
    list_map_inj (fun _ _ he => (AbstractByte.Init.inj he).1) h
  have hval := congrArg leValue hmap
  rw [leValue_leBytes, leValue_leBytes] at hval
  have h1 : x₁.toNat < 256 ^ 8 := pow256_8_eq ▸ x₁.toNat_lt
  have h2 : x₂.toNat < 256 ^ 8 := pow256_8_eq ▸ x₂.toNat_lt
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hval
  cases x₁; cases x₂
  congr 1
  exact BitVec.eq_of_toNat_eq hval

private theorem bmU64Mach_val_inj {x₁ x₂ : UInt64} {acc₁ acc₂ : List Access}
    (h : bmU64Mach x₁ acc₁ = bmU64Mach x₂ acc₂) : x₁ = x₂ := by
  have h1 := congrArg (fun m => m.mem.memory.allocations) h
  dsimp [bmU64Mach, bmMach, bmCell] at h1
  exact u64InitBytes_inj (congrArg (fun a => a.data) (List.cons.inj h1).1)

private theorem tbU64Mach_val_inj {x₁ x₂ : UInt64} {acc₁ acc₂ : List Access}
    (h : tbU64Mach x₁ acc₁ = tbU64Mach x₂ acc₂) : x₁ = x₂ := by
  have h1 := congrArg (fun m => m.mem.memory.mem.allocations) h
  dsimp [tbU64Mach, tbWith, tbMach, tbCell] at h1
  have h2 := congrArg (fun a => a.data) (List.cons.inj h1).1
  have hlen : (u64InitBytes (P := TreeBorrowsProvenance) x₁).length = 8 := rfl
  have hlen2 : (u64InitBytes (P := TreeBorrowsProvenance) x₂).length = 8 := rfl
  simp only [hlen, hlen2, Nat.sub_self, uninitBytes] at h2
  exact u64InitBytes_inj (by simpa using h2)

private theorem nat_to_u64_of_rep {d : Nat} (hd : IntType.can_represent itU64 (d : Int) = true) :
    ∃ dx : UInt64, dx.toNat = d := by
  have hlt : d < 2 ^ 64 := (u64_can_represent_iff d).1 hd
  exact ⟨UInt64.ofNat d, by simp [Nat.mod_eq_of_lt hlt]⟩

/--
**Positive universal 8-byte little-endian `u64` `MrCellAdmissible` on `Mach`**:
holds for EVERY `AtomicEnv` with reflexive `A.rely`, EVERY 64-bit word
`x : UInt64`, EVERY access log `acc`, and arbitrary `A.rely`-respecting
concurrent interference `bmU64MRely A.rely`.
-/
theorem bmU64_mrCellAdmissible {FState G : Type} (A : AtomicEnv Nat FState G)
    (hrefl : ∀ v, A.rely v v) :
    MrCellAdmissible A bmPtr tyRawPtr itU64 (bmU64MRely A.rely) bmU64MInv where
  rely_refl m c hm := by
    obtain ⟨x, acc, _, rfl⟩ := hm
    exact ⟨x, x, acc, acc, hrefl _, rfl, rfl⟩
  rely_pres m c m' hm hr := by
    obtain ⟨x, acc, rfl, rfl⟩ := hm
    obtain ⟨x₁, x', acc₁, acc', hrel, heq, rfl⟩ := hr
    have hx : x = x₁ := bmU64Mach_val_inj heq
    subst hx
    exact ⟨x'.toNat, hrel, x', acc', rfl, rfl⟩
  load_ok m c hm := by
    obtain ⟨x, acc, rfl, rfl⟩ := hm
    refine ⟨x.toNat, bmU64Mach x (acc ++ [mrALoad8]), ?_, Int.natCast_nonneg _⟩
    rw [atomicLoad_eq_typedLoadM (bmU64Mach x acc) bmPtr tyRawPtr (.Int itU64) u64_layout rfl
      (by decide)]
    exact bmU64_typedLoad x acc
  load_val m c v m' hm hok := by
    obtain ⟨x, acc, rfl, rfl⟩ := hm
    obtain ⟨hok1, _⟩ := hok
    have hL : evalIntrinsicM (M := BM) (bmU64Mach x acc) .AtomicLoad
        [(.Ptr ⟨bmPtr, none⟩, tyRawPtr)] (.Int itU64) =
        .ok (.Int x.toNat, bmU64Mach x (acc ++ [mrALoad8])) := by
      rw [atomicLoad_eq_typedLoadM (bmU64Mach x acc) bmPtr tyRawPtr (.Int itU64) u64_layout rfl
        (by decide)]
      exact bmU64_typedLoad x acc
    rw [hL] at hok1
    obtain ⟨hv, rfl⟩ := Prod.mk.inj (Except.ok.inj hok1)
    cases hv
    exact ⟨Int.toNat_natCast _, x, acc ++ [mrALoad8], rfl, rfl⟩
  cas_ok m c e d hm hd := by
    obtain ⟨x, acc, rfl, rfl⟩ := hm
    obtain ⟨dx, hdx⟩ := nat_to_u64_of_rep hd
    by_cases he : x.toNat = e
    · refine ⟨x.toNat, bmU64Mach dx ((acc ++ [mrALoad8]) ++ [mrAStore8]), ?_,
        Int.natCast_nonneg _⟩
      have hst := bmU64_typedStore x dx (acc ++ [mrALoad8])
      rw [hdx] at hst
      rw [← he]
      exact atomicCompareExchange_success tyRawPtr (al := ⟨8⟩) rfl (by decide)
        (bmU64_typedLoad x acc) hst
    · refine ⟨x.toNat, bmU64Mach x (acc ++ [mrALoad8]), ?_, Int.natCast_nonneg _⟩
      refine atomicCompareExchange_failure tyRawPtr (.Int d) (al := ⟨8⟩) rfl (by decide)
        (bmU64_typedLoad x acc) ?_
      intro hEq; exact he (Int.ofNat.inj (Value.Int.inj hEq)).symm
  cas_val m c e d ret m' hm hd hok := by
    obtain ⟨x, acc, rfl, rfl⟩ := hm
    obtain ⟨dx, hdx⟩ := nat_to_u64_of_rep hd
    obtain ⟨hok1, _⟩ := hok
    by_cases he : x.toNat = e
    · have hst := bmU64_typedStore x dx (acc ++ [mrALoad8])
      rw [hdx] at hst
      have hC : evalIntrinsicM (M := BM) (bmU64Mach x acc) .AtomicCompareExchange
          [(.Ptr ⟨bmPtr, none⟩, tyRawPtr), (.Int e, .Int itU64), (.Int d, .Int itU64)]
          (.Int itU64) =
          .ok (.Int x.toNat, bmU64Mach dx ((acc ++ [mrALoad8]) ++ [mrAStore8])) := by
        rw [← he]
        exact atomicCompareExchange_success tyRawPtr (al := ⟨8⟩) rfl (by decide)
          (bmU64_typedLoad x acc) hst
      rw [hC] at hok1
      obtain ⟨hv, rfl⟩ := Prod.mk.inj (Except.ok.inj hok1)
      cases hv
      exact ⟨Int.toNat_natCast _, fun _ => ⟨dx, (acc ++ [mrALoad8]) ++ [mrAStore8], hdx, rfl⟩,
        fun hne => absurd he hne⟩
    · have hC : evalIntrinsicM (M := BM) (bmU64Mach x acc) .AtomicCompareExchange
          [(.Ptr ⟨bmPtr, none⟩, tyRawPtr), (.Int e, .Int itU64), (.Int d, .Int itU64)]
          (.Int itU64) =
          .ok (.Int x.toNat, bmU64Mach x (acc ++ [mrALoad8])) := by
        refine atomicCompareExchange_failure tyRawPtr (.Int d) (al := ⟨8⟩) rfl (by decide)
          (bmU64_typedLoad x acc) ?_
        intro hEq; exact he (Int.ofNat.inj (Value.Int.inj hEq)).symm
      rw [hC] at hok1
      obtain ⟨hv, rfl⟩ := Prod.mk.inj (Except.ok.inj hok1)
      cases hv
      exact ⟨Int.toNat_natCast _, fun hEq => absurd hEq he,
        fun _ => ⟨x, acc ++ [mrALoad8], rfl, rfl⟩⟩

/--
**Positive universal 8-byte little-endian `u64` `MrCellAdmissible` on `MachTB`**:
holds for EVERY `AtomicEnv` with reflexive `A.rely`, EVERY 64-bit word
`x : UInt64`, EVERY access log `acc`, and arbitrary `A.rely`-respecting
concurrent interference `tbU64MRely A.rely`, with `tbU64_wfLive` supplying
`MachTB.wfLive` at every configuration.
-/
theorem tbU64_mrCellAdmissible {FState G : Type} (A : AtomicEnv Nat FState G)
    (hrefl : ∀ v, A.rely v v) :
    MrCellAdmissible A tbPtr tyRawPtr itU64 (tbU64MRely A.rely) tbU64MInv where
  rely_refl m c hm := by
    obtain ⟨x, acc, _, rfl⟩ := hm
    exact ⟨x, x, acc, acc, hrefl _, rfl, rfl⟩
  rely_pres m c m' hm hr := by
    obtain ⟨x, acc, rfl, rfl⟩ := hm
    obtain ⟨x₁, x', acc₁, acc', hrel, heq, rfl⟩ := hr
    have hx : x = x₁ := tbU64Mach_val_inj heq
    subst hx
    exact ⟨x'.toNat, hrel, x', acc', rfl, rfl⟩
  load_ok m c hm := by
    obtain ⟨x, acc, rfl, rfl⟩ := hm
    refine ⟨x.toNat, tbU64Mach x (acc ++ [mrALoad8]), ?_, Int.natCast_nonneg _⟩
    rw [atomicLoad_eq_typedLoadM (tbU64Mach x acc) tbPtr tyRawPtr (.Int itU64) u64_layout rfl
      (by decide)]
    exact tbU64_typedLoad x acc
  load_val m c v m' hm hok := by
    obtain ⟨x, acc, rfl, rfl⟩ := hm
    obtain ⟨hok1, _⟩ := hok
    have hL : evalIntrinsicM (M := TBM) (tbU64Mach x acc) .AtomicLoad
        [(.Ptr ⟨tbPtr, none⟩, tyRawPtr)] (.Int itU64) =
        .ok (.Int x.toNat, tbU64Mach x (acc ++ [mrALoad8])) := by
      rw [atomicLoad_eq_typedLoadM (tbU64Mach x acc) tbPtr tyRawPtr (.Int itU64) u64_layout rfl
        (by decide)]
      exact tbU64_typedLoad x acc
    rw [hL] at hok1
    obtain ⟨hv, rfl⟩ := Prod.mk.inj (Except.ok.inj hok1)
    cases hv
    exact ⟨Int.toNat_natCast _, x, acc ++ [mrALoad8], rfl, rfl⟩
  cas_ok m c e d hm hd := by
    obtain ⟨x, acc, rfl, rfl⟩ := hm
    obtain ⟨dx, hdx⟩ := nat_to_u64_of_rep hd
    by_cases he : x.toNat = e
    · refine ⟨x.toNat, tbU64Mach dx ((acc ++ [mrALoad8]) ++ [mrAStore8]), ?_,
        Int.natCast_nonneg _⟩
      have hst := tbU64_typedStore x dx (acc ++ [mrALoad8])
      rw [hdx] at hst
      rw [← he]
      exact atomicCompareExchange_success tyRawPtr (al := ⟨8⟩) rfl (by decide)
        (tbU64_typedLoad x acc) hst
    · refine ⟨x.toNat, tbU64Mach x (acc ++ [mrALoad8]), ?_, Int.natCast_nonneg _⟩
      refine atomicCompareExchange_failure tyRawPtr (.Int d) (al := ⟨8⟩) rfl (by decide)
        (tbU64_typedLoad x acc) ?_
      intro hEq; exact he (Int.ofNat.inj (Value.Int.inj hEq)).symm
  cas_val m c e d ret m' hm hd hok := by
    obtain ⟨x, acc, rfl, rfl⟩ := hm
    obtain ⟨dx, hdx⟩ := nat_to_u64_of_rep hd
    obtain ⟨hok1, _⟩ := hok
    by_cases he : x.toNat = e
    · have hst := tbU64_typedStore x dx (acc ++ [mrALoad8])
      rw [hdx] at hst
      have hC : evalIntrinsicM (M := TBM) (tbU64Mach x acc) .AtomicCompareExchange
          [(.Ptr ⟨tbPtr, none⟩, tyRawPtr), (.Int e, .Int itU64), (.Int d, .Int itU64)]
          (.Int itU64) =
          .ok (.Int x.toNat, tbU64Mach dx ((acc ++ [mrALoad8]) ++ [mrAStore8])) := by
        rw [← he]
        exact atomicCompareExchange_success tyRawPtr (al := ⟨8⟩) rfl (by decide)
          (tbU64_typedLoad x acc) hst
      rw [hC] at hok1
      obtain ⟨hv, rfl⟩ := Prod.mk.inj (Except.ok.inj hok1)
      cases hv
      exact ⟨Int.toNat_natCast _, fun _ => ⟨dx, (acc ++ [mrALoad8]) ++ [mrAStore8], hdx, rfl⟩,
        fun hne => absurd he hne⟩
    · have hC : evalIntrinsicM (M := TBM) (tbU64Mach x acc) .AtomicCompareExchange
          [(.Ptr ⟨tbPtr, none⟩, tyRawPtr), (.Int e, .Int itU64), (.Int d, .Int itU64)]
          (.Int itU64) =
          .ok (.Int x.toNat, tbU64Mach x (acc ++ [mrALoad8])) := by
        refine atomicCompareExchange_failure tyRawPtr (.Int d) (al := ⟨8⟩) rfl (by decide)
          (tbU64_typedLoad x acc) ?_
        intro hEq; exact he (Int.ofNat.inj (Value.Int.inj hEq)).symm
      rw [hC] at hok1
      obtain ⟨hv, rfl⟩ := Prod.mk.inj (Except.ok.inj hok1)
      cases hv
      exact ⟨Int.toNat_natCast _, fun hEq => absurd hEq he,
        fun _ => ⟨x, acc ++ [mrALoad8], rfl, rfl⟩⟩

/--
**End-to-end 8-byte `u64` `BasicMemory` capstone**: for ANY `Realizable`
64-bit-bounded environment (`hrep`), ANY `x₀ : UInt64`, and ANY `acc₀`, proves
unbounded safety (`Always` + `¬ DWP … False`), Streett liveness + enabledness +
CoBuchi non-vacuity (`CoBuchi CasWon` + `InfOften CasAttempt` +
`¬ CoBuchi CasWon False`), and bounded-contention unconditional termination
(`mrBudgetWP` `DWP` + `Eventually` + `¬ DWP … False`).
-/
theorem tryUpdate_mr_bm_u64_complete {FState G : Type} {A : AtomicEnv Nat FState G}
    {Rel : Nat → Nat → Prop} {init : Nat} {f₀ : FState} {g₀ : G}
    {comm₀ : OneShotCommitter Nat}
    (hR : A.Realizable)
    (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    (hrep : ∀ f₂ x f₃ (n : Nat), A.fSpec.hist_inv f₀ f₂ → A.fSpec.post_mut f₂ x f₃ (some n) →
      Rel init x → n < 2 ^ 64)
    (x₀ : UInt64) (acc₀ : List Access) {s₀ : AtomicSt Nat FState G}
    (hx₀ : x₀.toNat = init) (hs₀ : InitSt init f₀ g₀ comm₀ s₀) :
    Always (mrCellWP A bmPtr tyRawPtr itU64 (bmU64MRely A.rely))
      (fun ms => bmU64MInv ms.1 ms.2.cell ∧ HistInvSt A Rel init f₀ ms.2)
      (fun r ms => bmU64MInv ms.1 ms.2.cell ∧ CreusotPost A Rel init f₀ g₀ comm₀ r ms.2)
      (tryUpdateLoop Nat) (bmU64Mach x₀ acc₀, s₀) ∧
    CoBuchi (mrCellWP A bmPtr tyRawPtr itU64 (bmU64MRely A.rely)) CasWon
      (fun r ms => bmU64MInv ms.1 ms.2.cell ∧ CreusotPost A Rel init f₀ g₀ comm₀ r ms.2)
      (tryUpdateLoop Nat) (bmU64Mach x₀ acc₀, s₀) ∧
    InfOften (mrCellWP A bmPtr tyRawPtr itU64 (bmU64MRely A.rely)) CasAttempt
      (fun r ms => bmU64MInv ms.1 ms.2.cell ∧ CreusotPost A Rel init f₀ g₀ comm₀ r ms.2)
      (tryUpdateLoop Nat) (bmU64Mach x₀ acc₀, s₀) ∧
    ¬ CoBuchi (mrCellWP A bmPtr tyRawPtr itU64 (bmU64MRely A.rely)) CasWon
      (fun _ _ => False) (tryUpdateLoop Nat) (bmU64Mach x₀ acc₀, s₀) ∧
    DWP (mrBudgetWP A bmPtr tyRawPtr itU64 (bmU64MRely A.rely)) (tryUpdateLoop Nat)
      (fun r ms => bmU64MInv ms.1 ms.2.cell ∧ CreusotPost A Rel init f₀ g₀ comm₀ r ms.2)
      (bmU64Mach x₀ acc₀, s₀) ∧
    ¬ DWP (mrBudgetWP A bmPtr tyRawPtr itU64 (bmU64MRely A.rely)) (tryUpdateLoop Nat)
      (fun _ _ => False) (bmU64Mach x₀ acc₀, s₀) := by
  have hadm := bmU64_mrCellAdmissible A hR.rely_refl
  have hrep' : ∀ f₂ x f₃ (n : Nat), A.fSpec.hist_inv f₀ f₂ →
      A.fSpec.post_mut f₂ x f₃ (some n) → Rel init x →
      IntType.can_represent itU64 (n : Int) = true :=
    fun f₂ x f₃ n hf hp hr => (u64_can_represent_iff n).2 (hrep f₂ x f₃ n hf hp hr)
  have hm₀ : bmU64MInv (bmU64Mach x₀ acc₀) s₀.cell := ⟨x₀, acc₀, hx₀.trans hs₀.1.symm, rfl⟩
  exact ⟨tryUpdate_mr_always_safety hpre hrep' hadm hm₀ hs₀,
    tryUpdate_mr_fairInfOften hpre hrep' hadm hm₀ hs₀ _,
    tryUpdate_mr_infOften_attemptCas hpre hrep' hadm hm₀ hs₀,
    tryUpdate_mr_fairInfOften_nonvacuous hR hpre hrep' hadm hm₀ hs₀ _ _,
    tryUpdate_mr_dwp_ranked hpre hrep' hadm hm₀ hs₀,
    mrBudgetWP_nonvacuous_not_false hR hpre hrep' hadm hm₀ hs₀⟩

/--
**End-to-end 8-byte `u64` Tree Borrows `MachTB` capstone**: for ANY `Realizable`
64-bit-bounded environment (`hrep`), ANY `x₀ : UInt64`, and ANY `acc₀`, proves
unbounded safety (`Always` + `MachTB.wfLive`), Streett liveness + enabledness +
CoBuchi non-vacuity (`CoBuchi CasWon` + `InfOften CasAttempt` +
`¬ CoBuchi CasWon False` + `MachTB.wfLive`), and bounded-contention unconditional
termination (`mrBudgetWP` `DWP` + `MachTB.wfLive` + `¬ DWP … False`).
-/
theorem tryUpdate_mr_tb_u64_complete {FState G : Type} {A : AtomicEnv Nat FState G}
    {Rel : Nat → Nat → Prop} {init : Nat} {f₀ : FState} {g₀ : G}
    {comm₀ : OneShotCommitter Nat}
    (hR : A.Realizable)
    (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    (hrep : ∀ f₂ x f₃ (n : Nat), A.fSpec.hist_inv f₀ f₂ → A.fSpec.post_mut f₂ x f₃ (some n) →
      Rel init x → n < 2 ^ 64)
    (x₀ : UInt64) (acc₀ : List Access) {s₀ : AtomicSt Nat FState G}
    (hx₀ : x₀.toNat = init) (hs₀ : InitSt init f₀ g₀ comm₀ s₀) :
    Always (mrCellWP A tbPtr tyRawPtr itU64 (tbU64MRely A.rely))
      (fun ms => (tbU64MInv ms.1 ms.2.cell ∧ MiniRustSpec.Correspondence.MachTB.wfLive ms.1) ∧
        HistInvSt A Rel init f₀ ms.2)
      (fun r ms => (tbU64MInv ms.1 ms.2.cell ∧ MiniRustSpec.Correspondence.MachTB.wfLive ms.1) ∧
        CreusotPost A Rel init f₀ g₀ comm₀ r ms.2)
      (tryUpdateLoop Nat) (tbU64Mach x₀ acc₀, s₀) ∧
    CoBuchi (mrCellWP A tbPtr tyRawPtr itU64 (tbU64MRely A.rely)) CasWon
      (fun r ms => (tbU64MInv ms.1 ms.2.cell ∧ MiniRustSpec.Correspondence.MachTB.wfLive ms.1) ∧
        CreusotPost A Rel init f₀ g₀ comm₀ r ms.2)
      (tryUpdateLoop Nat) (tbU64Mach x₀ acc₀, s₀) ∧
    InfOften (mrCellWP A tbPtr tyRawPtr itU64 (tbU64MRely A.rely)) CasAttempt
      (fun r ms => (tbU64MInv ms.1 ms.2.cell ∧ MiniRustSpec.Correspondence.MachTB.wfLive ms.1) ∧
        CreusotPost A Rel init f₀ g₀ comm₀ r ms.2)
      (tryUpdateLoop Nat) (tbU64Mach x₀ acc₀, s₀) ∧
    ¬ CoBuchi (mrCellWP A tbPtr tyRawPtr itU64 (tbU64MRely A.rely)) CasWon
      (fun _ _ => False) (tryUpdateLoop Nat) (tbU64Mach x₀ acc₀, s₀) ∧
    DWP (mrBudgetWP A tbPtr tyRawPtr itU64 (tbU64MRely A.rely)) (tryUpdateLoop Nat)
      (fun r ms => (tbU64MInv ms.1 ms.2.cell ∧ MiniRustSpec.Correspondence.MachTB.wfLive ms.1) ∧
        CreusotPost A Rel init f₀ g₀ comm₀ r ms.2)
      (tbU64Mach x₀ acc₀, s₀) ∧
    ¬ DWP (mrBudgetWP A tbPtr tyRawPtr itU64 (tbU64MRely A.rely)) (tryUpdateLoop Nat)
      (fun _ _ => False) (tbU64Mach x₀ acc₀, s₀) := by
  have hadm := tbU64_mrCellAdmissible A hR.rely_refl
  have hrep' : ∀ f₂ x f₃ (n : Nat), A.fSpec.hist_inv f₀ f₂ →
      A.fSpec.post_mut f₂ x f₃ (some n) → Rel init x →
      IntType.can_represent itU64 (n : Int) = true :=
    fun f₂ x f₃ n hf hp hr => (u64_can_represent_iff n).2 (hrep f₂ x f₃ n hf hp hr)
  have hm₀ : tbU64MInv (tbU64Mach x₀ acc₀) s₀.cell := ⟨x₀, acc₀, hx₀.trans hs₀.1.symm, rfl⟩
  have hrely_wf : ∀ m m', MiniRustSpec.Correspondence.MachTB.wfLive m →
      tbU64MRely A.rely m m' → MiniRustSpec.Correspondence.MachTB.wfLive m' := by
    rintro m m' _ ⟨_, x', _, acc', _, _, rfl⟩
    exact tbU64_wfLive x' acc'
  have hf := tryUpdate_mr_tb_wfLive_fair hpre hrep' hadm hrely_wf hm₀ (tbU64_wfLive x₀ acc₀) hs₀
    (fun _ _ _ _ => False)
  exact ⟨tryUpdate_mr_tb_wfLive_safety hpre hrep' hadm hrely_wf hm₀ (tbU64_wfLive x₀ acc₀) hs₀,
    hf.1, hf.2,
    tryUpdate_mr_fairInfOften_nonvacuous hR hpre hrep' hadm hm₀ hs₀ _ _,
    tryUpdate_mr_tb_wfLive_dwp hpre hrep' hadm hrely_wf hm₀ (tbU64_wfLive x₀ acc₀) hs₀,
    mrBudgetWP_nonvacuous_not_false hR hpre hrep' hadm hm₀ hs₀⟩

/-! #### Weak vs. strong CAS on MiniRust machines -/

/--
**Strong-CAS MiniRust transformer (`mrStrongCellWP`)**: identical to `mrCellWP`
except that a CAS whose observed value equals `expected` must commit — exactly
MiniRust's `AtomicCompareExchange` (strong `compare_exchange`), with no
`compare_exchange_weak` spurious-failure branch.
-/
def mrStrongCellWP {M FState G : Type} [Memory M] [MemoryOps M] (A : AtomicEnv Nat FState G)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (t : IntType)
    (mRely : Machine M → Machine M → Prop) :
    StateEffectWP (MrAtomicSt M FState G) (AtomicCellE Nat) where
  wp
    | .call (.cas e d), K, ms => ∀ m₁, mRely ms.1 m₁ →
        (∃ ret m₂, mrCasOk m₁ ptr pty t e d ret m₂) ∧
        ∀ ret m₂, mrCasOk m₁ ptr pty t e d ret m₂ → A.rely ms.2.cell ret.toNat ∧ ∀ b,
          (ret.toNat ≠ e →
            K (false, ret.toNat) (m₂, { ms.2 with cell := ret.toNat, budget := b })) ∧
          (ret.toNat = e →
            casWin A e d (fun o s' => K o (m₂, s')) { ms.2 with cell := ret.toNat } b)
    | i, K, ms => (mrCellWP A ptr pty t mRely).wp i K ms
  mono {i} _ _ _ h hw :=
    match i with
    | .call (.cas _ _) => fun m₁ hm =>
        ⟨(hw m₁ hm).1, fun ret m₂ hok =>
          ⟨((hw m₁ hm).2 ret m₂ hok).1, fun b =>
          ⟨fun hne => h _ _ ((((hw m₁ hm).2 ret m₂ hok).2 b).1 hne),
           fun heq =>
            ⟨((((hw m₁ hm).2 ret m₂ hok).2 b).2 heq).1,
             ((((hw m₁ hm).2 ret m₂ hok).2 b).2 heq).2.1,
             fun g' hg' => h _ _ (((((hw m₁ hm).2 ret m₂ hok).2 b).2 heq).2.2 g' hg')⟩⟩⟩⟩
    | .call .load => (mrCellWP A ptr pty t mRely).mono h hw
    | .call (.callF _) => (mrCellWP A ptr pty t mRely).mono h hw
    | .call .dropF => (mrCellWP A ptr pty t mRely).mono h hw
    | .call .recv => (mrCellWP A ptr pty t mRely).mono h hw

/-- `ITree` continuation of the unfolded `try_update` loop. -/
private abbrev mrIterK : Nat ⊕ Except Nat Nat → ITree (AtomicCellE Nat) (Except Nat Nat) :=
  Sum.elim (fun next => ITree.tau (ITree.iter tryBody next)) ITree.ret

/--
**Strong CAS terminates on a quiescent MiniRust cell**: if no other thread
writes (`A.rely` is equality), MiniRust's strong `AtomicCompareExchange` makes
`tryUpdateLoop` commit or abort on its first iteration, so it is totally
correct (`DWP`) with the full contract — no budget, no fairness needed.
-/
theorem tryUpdate_mr_strong_quiescent_dwp {M FState G : Type} [Memory M] [MemoryOps M]
    {A : AtomicEnv Nat FState G} {Rel : Nat → Nat → Prop}
    {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»} {t : IntType}
    {mRely : Machine M → Machine M → Prop} {MInv : Machine M → Nat → Prop}
    {init : Nat} {f₀ : FState} {g₀ : G} {comm₀ : OneShotCommitter Nat}
    (hq : ∀ a b, A.rely a b → a = b)
    (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    (hrep : ∀ f₂ x f₃ (n : Nat), A.fSpec.hist_inv f₀ f₂ → A.fSpec.post_mut f₂ x f₃ (some n) →
      Rel init x → IntType.can_represent t (n : Int) = true)
    (hadm : MrCellAdmissible A ptr pty t mRely MInv)
    {m₀ : Machine M} {s₀ : AtomicSt Nat FState G}
    (hm₀ : MInv m₀ s₀.cell) (hs₀ : InitSt init f₀ g₀ comm₀ s₀) :
    DWP (mrStrongCellWP A ptr pty t mRely) (tryUpdateLoop Nat)
      (fun r ms => MInv ms.1 ms.2.cell ∧ CreusotPost A Rel init f₀ g₀ comm₀ r ms.2)
      (m₀, s₀) := by
  refine DWP.vis fun m₁ hm₁ => ?_
  obtain ⟨c₁, _, hmc₁⟩ := hadm.rely_pres m₀ _ m₁ hm₀ hm₁
  refine ⟨hadm.load_ok m₁ c₁ hmc₁, fun v m₂ hload => ?_⟩
  obtain ⟨hv, hm2⟩ := mr_observe hadm hm₀ hm₁ hload
  refine ⟨hv, fun b => ?_⟩
  dsimp only [loadAns]
  refine dwp_iter_ranked_lt tryBody
    (fun (n : Nat) (prev : Nat) (ms : MrAtomicSt M FState G) =>
      n = 0 ∧ MInv ms.1 ms.2.cell ∧ LoopInv A Rel init f₀ g₀ comm₀ prev ms.2)
    (fun n prev ms hms => ?_) (n := 0) (init := v.toNat)
    (s := (m₂, { s₀ with cell := v.toNat, budget := b }))
    ⟨rfl, hm2, loopInv_of_init hpre hs₀ hv b⟩
  obtain ⟨m, s⟩ := ms
  obtain ⟨_, hm, hl⟩ := hms
  refine DWP.vis ⟨loopInv_pre hpre hl, fun f' r hpost => ?_⟩
  cases r with
  | none =>
    dsimp only
    change DWP (mrStrongCellWP A ptr pty t mRely) (tryCallK prev (callOut prev none)) _ _
    rw [tryCallK_none, retAfterDrop]
    refine DWP.vis fun m₁' hm₁' => ?_
    obtain ⟨c', _, hmc'⟩ := hadm.rely_pres m _ m₁' hm hm₁'
    refine ⟨hadm.load_ok m₁' c' hmc', fun v' m₂' hload' => ?_⟩
    obtain ⟨hv', hm2'⟩ := mr_observe hadm hm hm₁' hload'
    exact ⟨hv', fun b' hres => DWP.ret ⟨hm2', loopInv_err_post hpre hl hpost hv' b' hres⟩⟩
  | some next =>
    dsimp only
    change DWP (mrStrongCellWP A ptr pty t mRely) (tryCallK prev (callOut prev (some next))) _ _
    rw [tryCallK_some]
    have hnext_rep : IntType.can_represent t next = true :=
      hrep s.fst prev f' next hl.2.2.1 hpost hl.1
    refine DWP.vis fun m₁' hm₁' => ?_
    obtain ⟨c', hc', hmc'⟩ := hadm.rely_pres m _ m₁' hm hm₁'
    refine ⟨hadm.cas_ok m₁' c' prev next hmc' hnext_rep, fun ret m₂' hcas => ?_⟩
    obtain ⟨hret, hstore, _⟩ := hadm.cas_val m₁' c' prev next ret m₂' hmc' hnext_rep hcas
    have hrel : A.rely s.cell ret.toNat := hret ▸ hc'
    have heq : ret.toNat = prev := (hq _ _ hrel).symm.trans hl.2.1
    refine ⟨hrel, fun b' => ⟨fun hne => absurd heq hne, fun _ => ?_⟩⟩
    refine ⟨loopInv_unshot (s := s) hpre hl, loopInv_win_pre (s := s) hpre hl hpost,
      fun g' hg' => ?_⟩
    dsimp only
    rw [tryCasK_true, retAfterDrop]
    have hm2' : MInv m₂' next := hstore (hret ▸ heq)
    refine DWP.vis fun m₁'' hm₁'' => ?_
    obtain ⟨c'', _, hmc''⟩ := hadm.rely_pres m₂' next m₁'' hm2' hm₁''
    refine ⟨hadm.load_ok m₁'' c'' hmc'', fun v'' m₂'' hload'' => ?_⟩
    obtain ⟨hv'', hm2''⟩ := mr_observe hadm hm2' hm₁'' hload''
    refine ⟨hv'', fun b'' hres => DWP.ret ⟨hm2'', ?_⟩⟩
    have hok := loopInv_ok_post hpre hl hpost hg' hv'' b' b'' hres
    simpa only [heq] using hok

/-- Shapes reached by an everlasting spurious-failure run of `tryUpdateLoop`. -/
private def SpuriousShape {M FState G : Type} [Memory M] (t : IntType)
    (MInv : Machine M → Nat → Prop) (x : ITree (AtomicCellE Nat) (Except Nat Nat))
    (ms : MrAtomicSt M FState G) : Prop :=
  MInv ms.1 ms.2.cell ∧
    ((x = ITree.iter tryBody ms.2.cell) ∨ (x = ITree.tau (ITree.iter tryBody ms.2.cell)) ∨
      ∃ n : Nat, IntType.can_represent t (n : Int) = true ∧
        x = ITree.vis (aCas ms.2.cell n) (fun o => tryCasK ms.2.cell n o >>= mrIterK))

/--
**Weak CAS need not terminate on a quiescent MiniRust cell**: even with no
interference at all, `compare_exchange_weak`'s spurious failures (each one a
real MiniRust atomic load leaving the cell unchanged) can repeat forever, so
`mrCellWP` refutes `DWP` for every postcondition — the machine-level
counterpart of `weak_vs_strong_cas_separation`.
-/
theorem tryUpdate_mr_weak_quiescent_not_dwp {M FState G : Type} [Memory M] [MemoryOps M]
    {A : AtomicEnv Nat FState G}
    {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»} {t : IntType}
    {mRely : Machine M → Machine M → Prop} {MInv : Machine M → Nat → Prop}
    (hadm : MrCellAdmissible A ptr pty t mRely MInv)
    (hsome : ∀ f x, ∃ f' n, A.fSpec.post_mut f x f' (some n) ∧
      IntType.can_represent t (n : Int) = true)
    {m₀ : Machine M} {s₀ : AtomicSt Nat FState G} (hm₀ : MInv m₀ s₀.cell)
    (Q : Except Nat Nat → MrAtomicSt M FState G → Prop) :
    ¬ DWP (mrCellWP A ptr pty t mRely) (tryUpdateLoop Nat) Q (m₀, s₀) := by
  intro h
  obtain ⟨v, m₂, hload⟩ := hadm.load_ok m₀ _ hm₀
  have h1 := (((DWP.vis_iff _ _ _ _ _).1 h m₀ (hadm.rely_refl _ _ hm₀)).2 v m₂ hload).2 0
  obtain ⟨hv, hm2⟩ := hadm.load_val m₀ _ v m₂ hm₀ hload
  refine DWP.induct (fun x ms => SpuriousShape t MInv x ms → False) ?_ h1
    ⟨hv ▸ hm2, Or.inl rfl⟩
  rintro x ⟨m, s⟩ hx ⟨hm, hshape⟩
  dsimp only at hm hshape
  rcases hshape with rfl | rfl | ⟨n, hn, rfl⟩
  · rw [iter_tryBody_observe] at hx
    obtain ⟨f', n, hpost, hn⟩ := hsome s.fst s.cell
    refine hx.2 f' (some n) hpost ⟨hm, Or.inr (Or.inr ⟨n, hn, ?_⟩)⟩
    exact (congrArg (· >>= mrIterK) (tryCallK_some s.cell n)).trans (vis_bind _ _ _)
  · rw [ITree.observe_tau] at hx
    exact hx ⟨hm, Or.inl rfl⟩
  · rw [ITree.observe_vis] at hx
    obtain ⟨ret, m₂', hcas⟩ := hadm.cas_ok m _ s.cell n hm hn
    obtain ⟨hret, _, _⟩ := hadm.cas_val m _ s.cell n ret m₂' hm hn hcas
    obtain ⟨w, mF, hw⟩ := hadm.load_ok m _ hm
    obtain ⟨hwv, hmF⟩ := hadm.load_val m _ w mF hm hw
    have hwr : w = ret := by
      have h1 := hw.2; have h2 := hcas.2; omega
    subst hwr
    have hk := ((((hx m (hadm.rely_refl _ _ hm)).2 w m₂' hcas).2 0).2 hret).2 mF hw
    refine hk ⟨?_, Or.inr (Or.inl ?_)⟩
    · show MInv mF w.toNat
      rw [hret]; exact hmF
    · show tryCasK s.cell n (false, w.toNat) >>= mrIterK = _
      rw [show (false, w.toNat) = casOut s.cell n false w.toNat from rfl, tryCasK_false,
        ret_bind]
      rfl

/-- Every `mrCellWP` safety property transfers automatically to `mrStrongCellWP`. -/
theorem mrCellWP_refines_strong {M FState G : Type} [Memory M] [MemoryOps M]
    (A : AtomicEnv Nat FState G)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (t : IntType)
    (mRely : Machine M → Machine M → Prop)
    (i : (AtomicCellE Nat).I)
    (K : (AtomicCellE Nat).O i → MrAtomicSt M FState G → Prop)
    (ms : MrAtomicSt M FState G)
    (hw : (mrCellWP A ptr pty t mRely).wp i K ms) :
    (mrStrongCellWP A ptr pty t mRely).wp i K ms := by
  match i with
  | .call (.cas _ _) =>
    intro m₁ hm
    refine ⟨(hw m₁ hm).1, fun ret m₂ hok =>
      ⟨((hw m₁ hm).2 ret m₂ hok).1, fun b =>
        ⟨(((hw m₁ hm).2 ret m₂ hok).2 b).1, fun he => ((((hw m₁ hm).2 ret m₂ hok).2 b).2 he).1⟩⟩⟩
  | .call .load => exact hw
  | .call (.callF _) => exact hw
  | .call .dropF => exact hw
  | .call .recv => exact hw

/--
**General non-vacuity of `mrStrongCellWP`**: for ANY memory model `M`, ANY
`Realizable A`, and ANY coupled `MrCellAdmissible`, `mrStrongCellWP` cannot
discharge `DWP … False` from any admissible initial state `(m₀, s₀)`.
-/
theorem mrStrongCellWP_nonvacuous_not_false {M FState G : Type} [Memory M] [MemoryOps M]
    {A : AtomicEnv Nat FState G} {Rel : Nat → Nat → Prop}
    {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»} {t : IntType}
    {mRely : Machine M → Machine M → Prop} {MInv : Machine M → Nat → Prop}
    {init : Nat} {f₀ : FState} {g₀ : G} {comm₀ : OneShotCommitter Nat}
    (hR : A.Realizable)
    (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    (hrep : ∀ f₂ x f₃ (n : Nat), A.fSpec.hist_inv f₀ f₂ → A.fSpec.post_mut f₂ x f₃ (some n) →
      Rel init x → IntType.can_represent t (n : Int) = true)
    (hadm : MrCellAdmissible A ptr pty t mRely MInv)
    {m₀ : Machine M} {s₀ : AtomicSt Nat FState G}
    (hm₀ : MInv m₀ s₀.cell) (hs₀ : InitSt init f₀ g₀ comm₀ s₀) :
    ¬ DWP (mrStrongCellWP A ptr pty t mRely) (tryUpdateLoop Nat) (fun _ _ => False) (m₀, s₀) := by
  intro hd
  have hrf₀ := hadm.rely_refl m₀ s₀.cell hm₀
  obtain ⟨v₀, m₁, hl₀⟩ := hadm.load_ok m₀ s₀.cell hm₀
  obtain ⟨hv₀, hm₁⟩ := hadm.load_val m₀ s₀.cell v₀ m₁ hm₀ hl₀
  have h1 := (((DWP.vis_iff _ _ _ _ _).1 hd m₀ hrf₀).2 v₀ m₁ hl₀).2 0
  dsimp only [loadAns] at h1
  rw [iter_tryBody_eq] at h1
  have hcall := (DWP.vis_iff _ _ _ _ _).1 h1
  obtain ⟨f', r, hpost⟩ := hR.post_mut_total _ _ hcall.1
  have h2 := hcall.2 f' r hpost
  cases r with
  | none =>
    change DWP (mrStrongCellWP A ptr pty t mRely)
      (tryCallK v₀.toNat (callOut v₀.toNat none) >>= _) _ _ at h2
    simp only [tryCallK_none, retAfterDrop, vis_bind] at h2
    have hrf₁ := hadm.rely_refl m₁ s₀.cell hm₁
    obtain ⟨v₁, m₂, hl₁⟩ := hadm.load_ok m₁ s₀.cell hm₁
    have h3 := (((DWP.vis_iff _ _ _ _ _).1 h2 m₁ hrf₁).2 v₁ m₂ hl₁).2 0 (hR.resolve_total f')
    simp only [ret_bind, Sum.elim_inr, DWP.ret_iff] at h3
  | some next =>
    change DWP (mrStrongCellWP A ptr pty t mRely)
      (tryCallK v₀.toNat (callOut v₀.toNat (some next)) >>= _) _ _ at h2
    rw [tryCallK_some, vis_bind] at h2
    have hnext_rep : IntType.can_represent t (next : Int) = true := by
      have hrl : Rel init v₀.toNat := by
        rw [hv₀, hs₀.1]; exact hpre.cellInv.refl init
      have hf : A.fSpec.hist_inv f₀ s₀.fst := hs₀.2.1 ▸ A.fSpec.hist_inv_laws.refl f₀
      exact hrep s₀.fst v₀.toNat f' next hf hpost hrl
    have hrf₁ := hadm.rely_refl m₁ s₀.cell hm₁
    obtain ⟨ret, m₂, hcas⟩ := hadm.cas_ok m₁ s₀.cell v₀.toNat next hm₁ hnext_rep
    obtain ⟨hret, hstore, _⟩ := hadm.cas_val m₁ s₀.cell v₀.toNat next ret m₂ hm₁ hnext_rep hcas
    have heq : ret.toNat = v₀.toNat := hret.trans hv₀.symm
    have hwin := ((((DWP.vis_iff _ _ _ _ _).1 h2 m₁ hrf₁).2 ret m₂ hcas).2 0).2 heq
    obtain ⟨g', hg'⟩ := hR.gc_post_total _ _ _ hwin.2.1
    have h3 := hwin.2.2 g' hg'
    simp only [tryCasK_true, retAfterDrop, vis_bind] at h3
    have hm₂ : MInv m₂ next := hstore hv₀.symm
    have hrf₂ := hadm.rely_refl m₂ next hm₂
    obtain ⟨v₂, m₃, hl₂⟩ := hadm.load_ok m₂ next hm₂
    have h4 := (((DWP.vis_iff _ _ _ _ _).1 h3 m₂ hrf₂).2 v₂ m₃ hl₂).2 0 (hR.resolve_total f')
    simp only [ret_bind, Sum.elim_inr, DWP.ret_iff] at h4

/--
**Second axis of MiniRust strong-CAS separation**: under unbounded concurrent
machine interference where other threads can always advance the cell to a
distinct value (`hstep_diff`), even **strong** `compare_exchange`
(`mrStrongCellWP`, zero spurious failures) suffers an infinite stream of genuine
MiniRust value-mismatch CAS failures (`atomicCompareExchange_failure`), refuting
`DWP` for every postcondition `Q`.
-/
theorem tryUpdate_mr_strong_contention_not_dwp {M FState G : Type} [Memory M] [MemoryOps M]
    {A : AtomicEnv Nat FState G}
    {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»} {t : IntType}
    {mRely : Machine M → Machine M → Prop} {MInv : Machine M → Nat → Prop}
    (hadm : MrCellAdmissible A ptr pty t mRely MInv)
    (hsome : ∀ f x, ∃ f' n, A.fSpec.post_mut f x f' (some n) ∧
      IntType.can_represent t (n : Int) = true)
    (hstep_diff : ∀ m c, MInv m c → ∃ m₁ c₁, mRely m m₁ ∧ MInv m₁ c₁ ∧ c₁ ≠ c)
    {m₀ : Machine M} {s₀ : AtomicSt Nat FState G} (hm₀ : MInv m₀ s₀.cell)
    (Q : Except Nat Nat → MrAtomicSt M FState G → Prop) :
    ¬ DWP (mrStrongCellWP A ptr pty t mRely) (tryUpdateLoop Nat) Q (m₀, s₀) := by
  intro h
  obtain ⟨v, m₂, hload⟩ := hadm.load_ok m₀ _ hm₀
  have h1 := (((DWP.vis_iff _ _ _ _ _).1 h m₀ (hadm.rely_refl _ _ hm₀)).2 v m₂ hload).2 0
  obtain ⟨hv, hm2⟩ := hadm.load_val m₀ _ v m₂ hm₀ hload
  refine DWP.induct (fun x ms => SpuriousShape t MInv x ms → False) ?_ h1
    ⟨hv ▸ hm2, Or.inl rfl⟩
  rintro x ⟨m, s⟩ hx ⟨hm, hshape⟩
  dsimp only at hm hshape
  rcases hshape with rfl | rfl | ⟨n, hn, rfl⟩
  · rw [iter_tryBody_observe] at hx
    obtain ⟨f', n, hpost, hn⟩ := hsome s.fst s.cell
    refine hx.2 f' (some n) hpost ⟨hm, Or.inr (Or.inr ⟨n, hn, ?_⟩)⟩
    exact (congrArg (· >>= mrIterK) (tryCallK_some s.cell n)).trans (vis_bind _ _ _)
  · rw [ITree.observe_tau] at hx
    exact hx ⟨hm, Or.inl rfl⟩
  · rw [ITree.observe_vis] at hx
    obtain ⟨m₁, c₁, hrel₁, hm₁, hne₁⟩ := hstep_diff m s.cell hm
    obtain ⟨ret, m₂', hcas⟩ := hadm.cas_ok m₁ c₁ s.cell n hm₁ hn
    obtain ⟨hret, _, hkeep⟩ := hadm.cas_val m₁ c₁ s.cell n ret m₂' hm₁ hn hcas
    have hne : ret.toNat ≠ s.cell := hret ▸ hne₁
    have hk := ((((hx m₁ hrel₁).2 ret m₂' hcas).2 0).1 hne)
    refine hk ⟨?_, Or.inr (Or.inl ?_)⟩
    · show MInv m₂' ret.toNat
      rw [hret]; exact hkeep hne₁
    · show tryCasK s.cell n (false, ret.toNat) >>= mrIterK = _
      rw [show (false, ret.toNat) = casOut s.cell n false ret.toNat from rfl, tryCasK_false,
        ret_bind]
      rfl

/-! #### Machine-backed one-shot committer `FairBuchiSat` monitor -/

/--
Deterministic one-shot `Committer` monitor directly over MiniRust `mrCellWP`:
`QState = Bool` (`shot?`), moving `false → true` strictly on a winning MiniRust
`AtomicCompareExchange`, while pinning the invariant to `MInv ∧ HistInvSt` and
`q = ms.2.comm.shot_store`.
-/
def mrCommitterSpec {M FState G : Type} [Memory M] [MemoryOps M]
    (A : AtomicEnv Nat FState G) (Rel : Nat → Nat → Prop)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (t : IntType)
    (mRely : Machine M → Machine M → Prop) (MInv : Machine M → Nat → Prop)
    (init : Nat) (f₀ : FState) (g₀ : G) (comm₀ : OneShotCommitter Nat) :
    BuchiSpec (MrAtomicSt M FState G) Bool (AtomicCellE Nat) (Except Nat Nat) where
  ewp := mrCellWP A ptr pty t mRely
  step q i o ms ms' q' :=
    (CasWon i o ms ms' → q = false ∧ q' = true) ∧ (¬ CasWon i o ms ms' → q' = q)
  accept _ _ _ _ _ _ := False
  inv q ms := MInv ms.1 ms.2.cell ∧ HistInvSt A Rel init f₀ ms.2 ∧ q = ms.2.comm.shot_store
  terminal q r ms :=
    MInv ms.1 ms.2.cell ∧ CreusotPost A Rel init f₀ g₀ comm₀ r ms.2 ∧ q = ms.2.comm.shot_store

/--
**Machine-backed `FairBuchiSat` one-shot committer monitor**: for ANY memory
model `M` (including `MachTB` with `MInv ∧ MachTB.wfLive`) and coupled
`MrCellAdmissible`, `tryUpdateLoop` satisfies `mrCommitterSpec` under weak-CAS
fairness (`□◇ CasWon`) through real `evalIntrinsicM` steps.
-/
theorem tryUpdate_mr_fairBuchiSat_committer {M FState G : Type} [Memory M] [MemoryOps M]
    {A : AtomicEnv Nat FState G} {Rel : Nat → Nat → Prop}
    {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»} {t : IntType}
    {mRely : Machine M → Machine M → Prop} {MInv : Machine M → Nat → Prop}
    {init : Nat} {f₀ : FState} {g₀ : G} {comm₀ : OneShotCommitter Nat}
    (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    (hrep : ∀ f₂ x f₃ (n : Nat), A.fSpec.hist_inv f₀ f₂ → A.fSpec.post_mut f₂ x f₃ (some n) →
      Rel init x → IntType.can_represent t (n : Int) = true)
    (hadm : MrCellAdmissible A ptr pty t mRely MInv)
    {m₀ : Machine M} {s₀ : AtomicSt Nat FState G}
    (hm₀ : MInv m₀ s₀.cell) (hs₀ : InitSt init f₀ g₀ comm₀ s₀) :
    FairBuchiSat (mrCommitterSpec A Rel ptr pty t mRely MInv init f₀ g₀ comm₀)
      (fun _ i o ms ms' _ => CasWon i o ms ms') (tryUpdateLoop Nat) false (m₀, s₀) := by
  let spec := mrCommitterSpec A Rel ptr pty t mRely MInv init f₀ g₀ comm₀
  have h0 : s₀.comm.shot_store = false := by rw [hs₀.2.2.1, hpre.comm_unshot]
  refine (fairBuchiSat_iff_fairInfOften spec _ (tryUpdateLoop Nat) false (m₀, s₀)).2
    ⟨⟨hm₀, histInvSt_of_init hpre hs₀, h0.symm⟩, ?_⟩
  refine FairInfOften.vis ((BuchiSpec.monitorWP_wp _ _ _ _ _).2 fun m₁ hm₁ => ?_)
  obtain ⟨c₁, _, hmc₁⟩ := hadm.rely_pres m₀ _ m₁ hm₀ hm₁
  refine ⟨hadm.load_ok m₁ c₁ hmc₁, fun v m₂ hload => ?_⟩
  obtain ⟨hv, hm2⟩ := mr_observe hadm hm₀ hm₁ hload
  refine ⟨hv, fun b => ⟨false, ⟨fun h => False.elim h, fun _ => rfl⟩,
    ⟨hm2, histInvSt_of_loopInv hpre (loopInv_of_init hpre hs₀ hv b), h0.symm⟩, ?_⟩⟩
  dsimp only [loadAns]
  refine FairInfOften.iter_fair tryBody
    (fun (prev : Nat) (qms : Bool × MrAtomicSt M FState G) =>
      qms.1 = false ∧ MInv qms.2.1 qms.2.2.cell ∧ LoopInv A Rel init f₀ g₀ comm₀ prev qms.2.2)
    (fun prev qms hqms => ?_)
    ⟨rfl, hm2, loopInv_of_init hpre hs₀ hv b⟩
  obtain ⟨q, m, s⟩ := qms
  obtain ⟨hq, hm, hl⟩ := hqms
  dsimp only at hq hm hl
  subst hq
  have hunshot : s.comm.shot_store = false := loopInv_unshot hpre hl
  refine (fairIter.vis_iff _ _ _ _ _ _ _ _).2 ((BuchiSpec.monitorWP_wp _ _ _ _ _).2
    ⟨loopInv_pre hpre hl, fun f' r hpost =>
      ⟨false, ⟨fun h => False.elim h, fun _ => rfl⟩,
        ⟨hm, loopInv_call hpre hl hpost, hunshot.symm⟩, Or.inr ⟨fun h => h, ?_⟩⟩⟩)
  cases r with
  | none =>
    dsimp only
    change fairIter spec.monitorWP _ _ _ true (tryCallK prev (callOut prev none)) _
    rw [tryCallK_none]
    refine (fairIter.vis_iff _ _ _ _ _ _ _ _).2 ((BuchiSpec.monitorWP_wp _ _ _ _ _).2
      fun m₁' hm₁' => ?_)
    obtain ⟨c', _, hmc'⟩ := hadm.rely_pres m _ m₁' hm hm₁'
    refine ⟨hadm.load_ok m₁' c' hmc', fun v' m₂' hload' => ?_⟩
    obtain ⟨hv', hm2'⟩ := mr_observe hadm hm hm₁' hload'
    refine ⟨hv', fun b' hres => ⟨false, ⟨fun h => False.elim h, fun _ => rfl⟩,
      ⟨hm2', loopInv_drop_inv hpre (loopInv_call hpre hl hpost) hv' b', hunshot.symm⟩,
      Or.inr ⟨fun h => h, (fairIter.ret_inr_iff _ _ _ _ _ _ _).2
        ⟨hm2', loopInv_err_post hpre hl hpost hv' b' hres, hunshot.symm⟩⟩⟩⟩
  | some next =>
    dsimp only
    change fairIter spec.monitorWP _ _ _ true (tryCallK prev (callOut prev (some next))) _
    rw [tryCallK_some]
    have hnext_rep : IntType.can_represent t next = true :=
      hrep s.fst prev f' next hl.2.2.1 hpost hl.1
    refine (fairIter.vis_iff _ _ _ _ _ _ _ _).2 ((BuchiSpec.monitorWP_wp _ _ _ _ _).2
      fun m₁' hm₁' => ?_)
    obtain ⟨c', hc', hmc'⟩ := hadm.rely_pres m _ m₁' hm hm₁'
    refine ⟨hadm.cas_ok m₁' c' prev next hmc' hnext_rep, fun ret m₂' hcas => ?_⟩
    obtain ⟨hret, hstore, hkeep⟩ := hadm.cas_val m₁' c' prev next ret m₂' hmc' hnext_rep hcas
    have hrel : A.rely s.cell ret.toNat := hret ▸ hc'
    refine ⟨hrel, fun b' => ⟨fun hne => ?_, fun heq => ?_⟩⟩
    · have hm2' : MInv m₂' ret.toNat := hret ▸ hkeep (hret ▸ hne)
      have hl' := loopInv_fail hpre hl hpost hrel b'
      refine ⟨false, ⟨fun h => Bool.noConfusion h, fun _ => rfl⟩,
        ⟨hm2', histInvSt_of_loopInv hpre hl', hunshot.symm⟩,
        Or.inr ⟨fun h => Bool.noConfusion h, ?_⟩⟩
      dsimp only
      change fairIter spec.monitorWP _ _ _ true
        (tryCasK prev next (casOut prev next false ret.toNat)) _
      rw [tryCasK_false]
      exact (fairIter.ret_inl_iff _ _ _ _ _ _ _).2 ⟨rfl, rfl, hm2', hl'⟩
    · refine ⟨⟨hunshot, loopInv_win_pre (s := s) hpre hl hpost, fun g' hg' => ?_⟩,
        fun mFail hfail => ?_⟩
      · have hm2' : MInv m₂' next := hstore (hret ▸ heq)
        have hwin : HistInvSt A Rel init f₀
            (AtomicSt.commit { s with fst := f', cell := ret.toNat } prev next g' b') := by
          simpa only [heq] using loopInv_win_inv hpre hl hpost g' b'
        refine ⟨true, ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd rfl h⟩, ⟨hm2', hwin, rfl⟩,
          Or.inl ⟨rfl, ?_⟩⟩
        dsimp only
        rw [tryCasK_true]
        refine DWP.vis ((BuchiSpec.monitorWP_wp _ _ _ _ _).2 fun m₁'' hm₁'' => ?_)
        obtain ⟨c'', _, hmc''⟩ := hadm.rely_pres m₂' next m₁'' hm2' hm₁''
        refine ⟨hadm.load_ok m₁'' c'' hmc'', fun v'' m₂'' hload'' => ?_⟩
        obtain ⟨hv'', hm2''⟩ := mr_observe hadm hm2' hm₁'' hload''
        refine ⟨hv'', fun b'' hres => ⟨true, ⟨fun h => False.elim h, fun _ => rfl⟩,
          ⟨hm2'', loopInv_drop_inv hpre hwin hv'' b'', rfl⟩, DWP.ret ⟨hm2'', ?_, rfl⟩⟩⟩
        simpa only [heq] using loopInv_ok_post hpre hl hpost hg' hv'' b' b'' hres
      · have hmf : MInv mFail ret.toNat := by
          have := hadm.load_val m₁' c' ret mFail hmc' hfail; exact this.1 ▸ this.2
        have hl' := loopInv_fail hpre hl hpost hrel b'
        refine ⟨false, ⟨fun h => Bool.noConfusion h, fun _ => rfl⟩,
          ⟨hmf, histInvSt_of_loopInv hpre hl', hunshot.symm⟩,
          Or.inr ⟨fun h => Bool.noConfusion h, ?_⟩⟩
        dsimp only
        change fairIter spec.monitorWP _ _ _ true
          (tryCasK prev next (casOut prev next false ret.toNat)) _
        rw [tryCasK_false]
        exact (fairIter.ret_inl_iff _ _ _ _ _ _ _).2 ⟨rfl, rfl, hmf, hl'⟩

/-! #### Finite-width saturation canary & `#4162` wrapping `u64` Tree Borrows service -/

private theorem ticketService_eq (k : Nat) :
    ticketService k = ITree.vis aRecv (fun _ =>
      ((tryUpdateLoop Nat >>= fun _ => ITree.ret (k + 1)) >>=
        fun x => ITree.ret (Sum.inl x)) >>=
        Sum.elim (fun n' => ITree.tau (ticketService n')) ITree.ret) := by
  change ITree.iter (fun a => Sum.inl <$> serviceBody a) k = _
  rw [iter_unfold]
  change (serviceBody k >>= fun x => ITree.ret (Sum.inl x)) >>= _ = _
  rw [serviceBody, vis_bind, vis_bind]
  rfl

/--
**Fail-closed finite-width saturation canary**: on ANY finite-width MiniRust
cell whose current value `c` sits at the top of `t` (`can_represent t (c + 1) = false`,
e.g. `255` on `u8` or `2^64 - 1` on `u64`), the unbounded `ticketService`
(`|x| Some(x + 1)`) fails closed (`¬ DWLP`) under `mrBudgetWP` because MiniRust
`AtomicCompareExchange` emits `Stop.specPanic` on `c + 1`.
-/
theorem mr_ticketService_overflow_canary {M : Type} [Memory M] [MemoryOps M]
    {m₀ m₁ : Machine M} {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»}
    {t : IntType} {al : Align} {c : Nat}
    {mRely : Machine M → Machine M → Prop}
    (hlay : Type.layout (.Int t) = .ok (.Sized ⟨al.bytes⟩ al))
    (hal : alignFromBytes t.size.bytes = some al)
    (hmax : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hsize : al.bytes = 1 ∨ al.bytes = 2 ∨ al.bytes = 4 ∨ al.bytes = 8)
    (hrefl₀ : mRely m₀ m₀) (hrefl₁ : mRely m₁ m₁)
    (hload₀ : typedLoadM (M := M) m₀ ptr (.Int t) al .Atomic = .ok (.Int c, m₁))
    (hload₁ : ∃ m₂, typedLoadM (M := M) m₁ ptr (.Int t) al .Atomic = .ok (.Int c, m₂))
    (hout : IntType.can_represent t ((c + 1 : Nat) : Int) = false)
    (s₀ : AtomicSt Nat PUnit PUnit) (hs : s₀.cell = c)
    (Q : PEmpty.{1} → MrAtomicSt M PUnit PUnit → Prop) :
    ¬ DWLP (mrBudgetWP ticketEnv ptr pty t mRely) (ticketService 0) Q (m₀, s₀) := by
  intro hd
  rw [ticketService_eq 0, DWLP.vis_iff] at hd
  have h1 := hd 0
  rw [tryUpdateLoop, bind_assoc, bind_assoc, vis_bind] at h1
  have hl₀ : mrLoadOk m₀ ptr pty t c m₁ := by
    refine ⟨?_, Int.natCast_nonneg _⟩
    cases al with
    | mk ab =>
      dsimp only at hlay hsize hload₀
      have halign : alignFromBytesInt (ab : Int) = some ⟨ab⟩ := by
        rcases hsize with rfl | rfl | rfl | rfl <;> rfl
      have hmax' : ab ≤ x86_64.MAX_ATOMIC_SIZE.bytes := by
        rcases hsize with rfl | rfl | rfl | rfl <;> decide
      rw [atomicLoad_eq_typedLoadM m₀ ptr pty (.Int t) hlay halign hmax']
      exact hload₀
  have h2 := (((DWLP.vis_iff _ _ _ _ _).1 h1 m₀ hrefl₀).2 c m₁ hl₀).2.1
    (by simp [hs])
  dsimp only [loadAns] at h2
  rw [iter_tryBody_eq] at h2
  simp only [bind_assoc, vis_bind] at h2
  have h3 := ((DWLP.vis_iff _ _ _ _ _).1 h2).2 PUnit.unit (some (c + 1)) rfl
  change DWLP (mrBudgetWP ticketEnv ptr pty t mRely)
    (tryCallK c (callOut c (some (c + 1))) >>= _) _ _ at h3
  simp only [tryCallK_some, vis_bind] at h3
  have hcas_ex := ((DWLP.vis_iff _ _ _ _ _).1 h3 m₁ hrefl₁).1
  obtain ⟨m₂, htl₁⟩ := hload₁
  exact mr_cas_out_of_range_specPanic_canary hal hmax htl₁ hout hcas_ex

/-- Wrapping 64-bit ticket closure `|x| Some((x + 1) % 2^64)`. -/
def u64WrapTicketSpec : FnMutSpec PUnit Nat Nat where
  hist_inv _ _ := True
  hist_inv_laws := ⟨fun _ => trivial, fun _ _ => trivial⟩
  pre _ _ := True
  post_mut _ x _ r := r = some ((x + 1) % 2 ^ 64)
  step_hist_inv _ _ _ _ _ := trivial
  resolve _ := True

/-- Wrapping 64-bit ticket environment (arbitrary modular interference). -/
def u64WrapTicketEnv : AtomicEnv Nat PUnit PUnit :=
  ⟨fun _ _ => True, u64WrapTicketSpec, trivialGC⟩

theorem u64WrapTicket_realizable : u64WrapTicketEnv.Realizable where
  rely_refl _ := trivial
  post_mut_total _ x _ := ⟨PUnit.unit, some ((x + 1) % 2 ^ 64), rfl⟩
  gc_post_total _ _ _ _ := ⟨PUnit.unit, trivial⟩
  resolve_total _ := trivial

theorem u64WrapTicket_pre (c : Nat) :
    TryUpdatePre u64WrapTicketEnv (fun _ _ => True) c PUnit.unit PUnit.unit (.fresh c) where
  cellInv := ⟨fun _ => trivial, fun _ _ => trivial⟩
  closure_pre _ _ _ _ := trivial
  closure_step _ _ _ _ _ _ _ := ⟨trivial, trivial⟩
  rely_sound _ _ _ := trivial
  comm_unshot := rfl

/-- Safety invariant for the 8-byte Tree Borrows wrapping `u64` `#4162` service. -/
def MrWrapSvcInv (ms : MrAtomicSt TBM PUnit PUnit) : Prop :=
  (tbU64MInv ms.1 ms.2.cell ∧ MiniRustSpec.Correspondence.MachTB.wfLive ms.1) ∧
    ms.2.fires ≤ 1 ∧ (ms.2.comm.shot_store = true ↔ ms.2.fires = 1)

/-- Accepting edge: a real 8-byte Tree Borrows winning CAS advancing the `u64` ticket mod `2^64`. -/
def MrWrapTicketCommit : (i : (AtomicCellE Nat).I) → (AtomicCellE Nat).O i →
    MrAtomicSt TBM PUnit PUnit → MrAtomicSt TBM PUnit PUnit → Prop :=
  fun i o ms ms' => CasWon i o ms ms' ∧ ms'.2.cell = (ms.2.cell + 1) % 2 ^ 64 ∧
    ms.2.comm.shot_store = false ∧ ms'.2.comm.shot_store = true

/--
**Positive real MiniRust `#4162` `-> !` reactive service on 8-byte Tree Borrows `u64`**:
for EVERY initial 64-bit word `x₀ : UInt64` and EVERY access log `acc₀`,
`ticketService 0` executed directly on `TreeBorrowsMemory` (`mrBudgetWP`) with
modular `u64` wrapping preserves `tbU64MInv ∧ MachTB.wfLive` and one-shot
per-request committer discipline (`Always`), commits infinitely many real 8-byte
little-endian `AtomicCompareExchange` ticket updates (`InfOften`), and is
genuinely non-terminating (`¬ DWP`).
-/
theorem tryUpdate_mr_tb_u64_wrapping_service (x₀ : UInt64) (acc₀ : List Access)
    (Q : PEmpty.{1} → MrAtomicSt TBM PUnit PUnit → Prop) :
    let m₀ := tbU64Mach x₀ acc₀
    let s₀ : AtomicSt Nat PUnit PUnit := ⟨x₀.toNat, PUnit.unit, .fresh x₀.toNat, 0, PUnit.unit, 0⟩
    Always (mrBudgetWP u64WrapTicketEnv tbPtr tyRawPtr itU64 (tbU64MRely (fun _ _ => True)))
        MrWrapSvcInv Q (ticketService 0) (m₀, s₀) ∧
      InfOften (mrBudgetWP u64WrapTicketEnv tbPtr tyRawPtr itU64 (tbU64MRely (fun _ _ => True)))
        MrWrapTicketCommit Q (ticketService 0) (m₀, s₀) ∧
      ¬ DWP (mrBudgetWP u64WrapTicketEnv tbPtr tyRawPtr itU64 (tbU64MRely (fun _ _ => True)))
        (ticketService 0) Q (m₀, s₀) := by
  intro m₀ s₀
  let ewp := mrBudgetWP u64WrapTicketEnv tbPtr tyRawPtr itU64 (tbU64MRely (fun _ _ => True))
  have hadm := tbU64_mrCellAdmissible u64WrapTicketEnv (fun _ => trivial)
  have hrely_wf : ∀ m m', MiniRustSpec.Correspondence.MachTB.wfLive m →
      tbU64MRely (fun _ _ => True) m m' → MiniRustSpec.Correspondence.MachTB.wfLive m' := by
    rintro m m' _ ⟨_, x', _, acc', _, _, rfl⟩; exact tbU64_wfLive x' acc'
  have hrep : ∀ f₂ x f₃ (n : Nat), u64WrapTicketEnv.fSpec.hist_inv PUnit.unit f₂ →
      u64WrapTicketEnv.fSpec.post_mut f₂ x f₃ (some n) → True →
      IntType.can_represent itU64 (n : Int) = true := by
    intro _ x _ n _ hr _
    have heq : some n = some ((x + 1) % 2 ^ 64) := hr
    cases heq
    exact (u64_can_represent_iff _).2 (Nat.mod_lt _ (Nat.pow_pos (by decide)))
  have hbody_always : ∀ (n : Nat) (ms : MrAtomicSt TBM PUnit PUnit), MrWrapSvcInv ms →
      Always ewp MrWrapSvcInv (fun _ ms' => MrWrapSvcInv ms') (serviceBody n) ms := by
    intro n ⟨m, s⟩ ⟨⟨hm, hwf⟩, hfires, hshot⟩
    refine Always.vis ⟨⟨hm, hwf⟩, hfires, hshot⟩ fun b => Always.bind ?_
    have hreq := Always.mono_wp (mrCellWP_refines_budget _ _ _ _ _)
      (tryUpdate_mr_tb_wfLive_safety (u64WrapTicket_pre s.cell) hrep hadm hrely_wf hm hwf
        (s₀ := { s with comm := .fresh s.cell, fires := 0, budget := b }) ⟨rfl, rfl, rfl, rfl, rfl⟩)
    exact Always.mono (fun _ hi => ⟨hi.1, hi.2.2.2⟩)
      (fun _ _ hq => Always.ret ⟨hq.1.1, hq.1.2.2.2⟩ ⟨hq.1.1, hq.1.2.2.2⟩) hreq.post_inv
  have hbody_live : ∀ (n : Nat) (ms : MrAtomicSt TBM PUnit PUnit), MrWrapSvcInv ms →
      buchiProgress ewp MrWrapTicketCommit (fun _ _ => False)
        (InfOften ewp MrWrapTicketCommit (fun _ ms' => MrWrapSvcInv ms')) (serviceBody n) ms := by
    intro n ⟨m, s⟩ ⟨⟨hm, hwf⟩, _, _⟩
    refine buchiProgress.vis_skip fun b => ?_
    refine buchiProgress.bind ?_
    refine buchiProgress.vis_skip fun m₁ hm₁ => ?_
    obtain ⟨c₁, _, hmc₁⟩ := hadm.rely_pres m _ m₁ hm hm₁
    refine ⟨hadm.load_ok m₁ c₁ hmc₁, fun v m₂ hload => ?_⟩
    obtain ⟨hv, hm₂⟩ := mr_observe hadm hm hm₁ hload
    have hwf₁ := hrely_wf m m₁ hwf hm₁
    have hwf₂ := evalIntrinsicM_atomic_tb_wfLive rfl hwf₁ hload.1
    let RInv : Nat → Nat → MrAtomicSt TBM PUnit PUnit → Prop := fun k prev ms' =>
      (tbU64MInv ms'.1 ms'.2.cell ∧ MiniRustSpec.Correspondence.MachTB.wfLive ms'.1) ∧
      ms'.2.cell = prev ∧ ms'.2.comm.shot_store = false ∧ ms'.2.fires = 0 ∧ ms'.2.budget = k
    have hiter : ∀ (Qex : Except Nat Nat → MrAtomicSt TBM PUnit PUnit → Prop)
        k prev (ms' : MrAtomicSt TBM PUnit PUnit), RInv k prev ms' →
        buchiProgress ewp MrWrapTicketCommit
          (Sum.elim (fun next ms'' => ∃ k', k' < k ∧ RInv k' next ms'') Qex)
          (fun t' ms'' => InfOften ewp MrWrapTicketCommit (fun _ ms''' => MrWrapSvcInv ms''')
            ((t' >>= mrIterK) >>= fun _ => ITree.ret (n + 1)) ms'') (tryBody prev) ms' := by
      intro Qex k prev ⟨m', s'⟩ ⟨⟨hm', hwf'⟩, hcell', hunshot', hfires', hbud'⟩
      dsimp only at hm' hwf' hcell' hunshot' hfires' hbud'
      refine buchiProgress.vis_skip ⟨trivial, fun _ r hr => ?_⟩
      have hreq : r = some ((prev + 1) % 2 ^ 64) := hr
      subst hreq
      dsimp only
      change buchiProgress ewp MrWrapTicketCommit _ _ (tryCallK prev (callOut prev (some _))) _
      rw [tryCallK_some]
      let next := (prev + 1) % 2 ^ 64
      have hnext_rep : IntType.can_represent itU64 (next : Int) = true :=
        (u64_can_represent_iff _).2 (Nat.mod_lt _ (Nat.pow_pos (by decide)))
      refine (buchiProgress.vis_iff _ _ _ _ _ _ _).2 fun m₁' hm₁' => ?_
      obtain ⟨c', _, hmc'⟩ := hadm.rely_pres m' _ m₁' hm' hm₁'
      refine ⟨hadm.cas_ok m₁' c' prev next hmc' hnext_rep, fun ret m₂' hcas => ?_⟩
      obtain ⟨hret, hstore, hkeep⟩ := hadm.cas_val m₁' c' prev next ret m₂' hmc' hnext_rep hcas
      have hwf₁' := hrely_wf m' m₁' hwf' hm₁'
      have hwf₂' := evalIntrinsicM_atomic_tb_wfLive rfl hwf₁' hcas.1
      have hwin : ∀ (b' : Nat) (heq : ret.toNat = prev),
          casWin u64WrapTicketEnv prev next
            (fun o s'' => (MrWrapTicketCommit (aCas prev next) o
                (m', { s' with fst := PUnit.unit }) (m₂', s'') ∧
              InfOften ewp MrWrapTicketCommit (fun _ ms''' => MrWrapSvcInv ms''')
                ((tryCasK prev next o >>= mrIterK) >>= fun _ => ITree.ret (n + 1)) (m₂', s'')) ∨
              buchiProgress ewp MrWrapTicketCommit
                (Sum.elim (fun next ms'' => ∃ k', k' < k ∧ RInv k' next ms'') Qex)
                (fun t' ms'' => InfOften ewp MrWrapTicketCommit (fun _ ms''' => MrWrapSvcInv ms''')
                  ((t' >>= mrIterK) >>= fun _ => ITree.ret (n + 1)) ms'')
                (tryCasK prev next o) (m₂', s''))
            { s' with fst := PUnit.unit, cell := ret.toNat } b' := by
        intro b' heq
        refine ⟨hunshot', trivial, fun _ _ => Or.inl ⟨⟨rfl, by
          show next = (s'.cell + 1) % 2 ^ 64; rw [hcell'], hunshot', rfl⟩, ?_⟩⟩
        simp only [tryCasK_true, retAfterDrop, vis_bind, ret_bind, Sum.elim_inr]
        have hm₂' : tbU64MInv m₂' next := hstore (hret ▸ heq)
        refine InfOften.vis fun m₁'' hm₁'' => ?_
        obtain ⟨c'', _, hmc''⟩ := hadm.rely_pres m₂' next m₁'' hm₂' hm₁''
        refine ⟨hadm.load_ok m₁'' c'' hmc'', fun v'' m₂'' hload'' => ?_⟩
        obtain ⟨_, hm₂''⟩ := mr_observe hadm hm₂' hm₁'' hload''
        have hwf₂'' := evalIntrinsicM_atomic_tb_wfLive rfl (hrely_wf m₂' m₁'' hwf₂' hm₁'') hload''.1
        have hfin : s'.fires + 1 ≤ 1 ∧ (true = true ↔ s'.fires + 1 = 1) := by
          simp [hfires']
        exact ⟨trivial, fun _ _ => InfOften.ret ⟨⟨hm₂'', hwf₂''⟩, hfin⟩,
          fun _ _ _ => InfOften.ret ⟨⟨hm₂'', hwf₂''⟩, hfin⟩⟩
      refine ⟨trivial, fun hsc => ⟨fun hne => absurd (hsc.trans hcell') hne, fun heq => ?_⟩,
        fun _ hpos => ⟨fun hne => Or.inr ?_, fun heq => ?_⟩⟩
      · refine ⟨hwin s'.budget heq, fun hpos mFail hfail => Or.inr ?_⟩
        dsimp only at hpos ⊢
        change buchiProgress ewp MrWrapTicketCommit _ _
          (tryCasK prev next (casOut prev next false ret.toNat)) _
        rw [tryCasK_false]
        have hmf : tbU64MInv mFail ret.toNat := by
          have := hadm.load_val m₁' c' ret mFail hmc' hfail; exact this.1 ▸ this.2
        have hwff := evalIntrinsicM_atomic_tb_wfLive rfl hwf₁' hfail.1
        exact (buchiProgress.ret_iff _ _ _ _ _ _).2
          ⟨k - 1, by omega, ⟨hmf, hwff⟩, rfl, hunshot', hfires',
            show s'.budget - 1 = k - 1 by omega⟩
      · dsimp only at hpos ⊢
        change buchiProgress ewp MrWrapTicketCommit _ _
          (tryCasK prev next (casOut prev next false ret.toNat)) _
        rw [tryCasK_false]
        have hm₂' : tbU64MInv m₂' ret.toNat := hret ▸ hkeep (hret ▸ hne)
        exact (buchiProgress.ret_iff _ _ _ _ _ _).2
          ⟨k - 1, by omega, ⟨hm₂', hwf₂'⟩, rfl, hunshot', hfires',
            show s'.budget - 1 = k - 1 by omega⟩
      · refine ⟨hwin (s'.budget - 1) heq, fun mFail hfail => Or.inr ?_⟩
        dsimp only at hpos ⊢
        change buchiProgress ewp MrWrapTicketCommit _ _
          (tryCasK prev next (casOut prev next false ret.toNat)) _
        rw [tryCasK_false]
        have hmf : tbU64MInv mFail ret.toNat := by
          have := hadm.load_val m₁' c' ret mFail hmc' hfail; exact this.1 ▸ this.2
        have hwff := evalIntrinsicM_atomic_tb_wfLive rfl hwf₁' hfail.1
        exact (buchiProgress.ret_iff _ _ _ _ _ _).2
          ⟨k - 1, by omega, ⟨hmf, hwff⟩, rfl, hunshot', hfires',
            show s'.budget - 1 = k - 1 by omega⟩
    refine ⟨trivial, fun _ => ?_, fun _ _ => ?_⟩
    · dsimp only [loadAns]
      exact buchiProgress.iter_ranked tryBody RInv (hiter _) (n := b)
        ⟨⟨hm₂, hwf₂⟩, rfl, rfl, rfl, rfl⟩
    · dsimp only [loadAns]
      exact buchiProgress.iter_ranked tryBody RInv (hiter _) (n := b - 1)
        ⟨⟨hm₂, hwf₂⟩, rfl, rfl, rfl, rfl⟩
  have hinit : MrWrapSvcInv (m₀, s₀) :=
    ⟨⟨⟨x₀, acc₀, rfl, rfl⟩, tbU64_wfLive x₀ acc₀⟩, Nat.zero_le 1, by simp [s₀]⟩
  have hrule := buchi_diverging_loop_rule serviceBody (fun _ ms => MrWrapSvcInv ms)
    hbody_always hbody_live (init := 0) hinit Q
  have hnd : ¬ DWP ewp (ticketService 0) Q (m₀, s₀) := by
    intro hd
    refine DWP.induct (fun x ms => Always ewp MrWrapSvcInv Q x ms → False) ?_ hd hrule.1
    intro x ms hx ha
    have hm : tbU64MInv ms.1 ms.2.cell := ha.inv.1.1
    cases hobs : x.observe with
    | ret r => exact nomatch r
    | tau x' =>
      rw [hobs] at hx; rw [Always.unfold_eq, hobs] at ha; exact hx ha.2
    | vis i k =>
      rw [hobs] at hx; rw [Always.unfold_eq, hobs] at ha
      have ha' := ha.2
      cases i with
      | call req =>
        cases req with
        | load =>
          have hrf := hadm.rely_refl ms.1 ms.2.cell hm
          obtain ⟨v, m₂, hok⟩ := hadm.load_ok ms.1 ms.2.cell hm
          obtain ⟨hv, _⟩ := hadm.load_val ms.1 ms.2.cell v m₂ hm hok
          exact ((hx ms.1 hrf).2 v m₂ hok).2.1 hv (((ha' ms.1 hrf).2 v m₂ hok).2.1 hv)
        | cas e d =>
          have hrf := hadm.rely_refl ms.1 ms.2.cell hm
          obtain ⟨ret, m₂, hok⟩ := (ha' ms.1 hrf).1
          have hret : ret.toNat = ms.2.cell := by
            obtain ⟨xcur, acc, hxcur, hmeq⟩ := hm
            rw [hmeq] at hok
            obtain ⟨ptr', pty', _, _, t', al', m₁', hargs, hty, hal, _, htl, _⟩ :=
              atomicCompareExchange_ok_iff.1 hok.1
            cases «Type».Int.inj hty
            have hptr' : ptr' = tbPtr :=
              (congrArg (fun p => p.thin_pointer)
                (Value.Ptr.inj (Prod.mk.inj (List.cons.inj hargs).1).1)).symm
            subst hptr'
            have hal' : al' = ⟨8⟩ := Option.some.inj hal.symm
            subst hal'
            rw [tbU64_typedLoad] at htl
            have hv := Value.Int.inj (Prod.mk.inj (Except.ok.inj htl)).1
            rw [← hv, Int.toNat_natCast, hxcur]
          have hstepD := ((hx ms.1 hrf).2 ret m₂ hok).2.1 hret
          have hstepA := ((ha' ms.1 hrf).2 ret m₂ hok).2.1 hret
          by_cases he : ret.toNat = e
          · exact (hstepD.2 he).1.2.2 PUnit.unit trivial ((hstepA.2 he).1.2.2 PUnit.unit trivial)
          · exact hstepD.1 he (hstepA.1 he)
        | callF arg =>
          obtain ⟨f', r, hpost⟩ := u64WrapTicket_realizable.post_mut_total _ _ hx.1
          exact hx.2 f' r hpost (ha'.2 f' r hpost)
        | dropF =>
          have hrf := hadm.rely_refl ms.1 ms.2.cell hm
          obtain ⟨v, m₂, hok⟩ := hadm.load_ok ms.1 ms.2.cell hm
          obtain ⟨hv, _⟩ := hadm.load_val ms.1 ms.2.cell v m₂ hm hok
          exact ((hx ms.1 hrf).2 v m₂ hok).2.1 hv trivial
            (((ha' ms.1 hrf).2 v m₂ hok).2.1 hv trivial)
        | recv => exact hx 0 (ha' 0)
  exact ⟨hrule.1, hrule.2, hnd⟩

end MrBridge

end DualAuthority

/-! ## 9. Fail-Closed Soundness Boundaries of the `creusot#2386` Contract -/

section FailClosed

/-- `K` of the unfolded `try_update` loop. -/
local notation "iterK" =>
  (Sum.elim (fun next => ITree.tau (ITree.iter tryBody next)) ITree.ret :
    Nat ⊕ Except Nat Nat → ITree (AtomicCellE Nat) (Except Nat Nat))

/-- Abort-only closure `|_| None`. -/
def abortSpec : FnMutSpec PUnit Nat Nat where
  hist_inv _ _ := True
  hist_inv_laws := ⟨fun _ => trivial, fun _ _ => trivial⟩
  pre _ _ := True
  post_mut _ _ _ r := r = none
  step_hist_inv _ _ _ _ _ := trivial
  resolve _ := True

/-- Strictly increasing interference with an aborting closure. -/
def strictEnv : AtomicEnv Nat PUnit PUnit := ⟨(· < ·), abortSpec, trivialGC⟩

/-- Quiescent environment (`rely := Eq`) with the strictly-advancing ticket closure. -/
def quiescentTicketEnv : AtomicEnv Nat PUnit PUnit := ⟨Eq, ticketSpec, trivialGC⟩

theorem quiescentTicket_pre (c : Nat) :
    TryUpdatePre quiescentTicketEnv (· ≤ ·) c PUnit.unit PUnit.unit (.fresh c) where
  cellInv := AtomicHistInv.nat_le
  closure_pre _ _ _ _ := trivial
  closure_step _ x _ n _ h _ := by
    have h' : some n = some (x + 1) := h
    cases h'; exact ⟨Nat.le_succ x, trivial⟩
  rely_sound _ _ h := h ▸ Nat.le_refl _
  comm_unshot := rfl

/--
**Fail-closed (1a): reflexivity is necessary on the zero-write `Err` path.**
For the irreflexive relation `x < y` (not an `AtomicHistInv`), even with
strictly increasing interference the zero-write `f(prev) = None` step of the
`Err` path leaves the cell unchanged and violates `HistStep`.
-/
theorem irreflexive_breaks_zero_write (s₀ : AtomicSt Nat PUnit PUnit)
    (Q : Except Nat Nat → AtomicSt Nat PUnit PUnit → Prop) :
    ¬ AtomicHistInv Nat (· < ·) ∧
      ¬ AlwaysStep (atomicHistWP strictEnv) (HistStep strictEnv (· < ·)) Q
        (tryUpdateLoop Nat) s₀ := by
  refine ⟨fun h => Nat.lt_irrefl 0 (h.refl 0), fun h => ?_⟩
  have h1 := ((histWP_load strictEnv _ _).1 ((AlwaysStep.vis_iff _ _ _ _ _ _).1 h)
    (s₀.cell + 1) (Nat.lt_succ_self _) 0).2
  rw [iter_tryBody_eq] at h1
  have h2 := (((histWP_call strictEnv _ _ _).1 ((AlwaysStep.vis_iff _ _ _ _ _ _).1 h1)).2
    PUnit.unit none rfl).1.1
  exact Nat.lt_irrefl _ h2

/-- Step predicate constraining only `cas` operations (`load`/`callF`/`dropF` unconstrained). -/
def CasOnlyHistStep {Val FState G : Type} (Rel : Val → Val → Prop) :
    (i : (AtomicCellE Val).I) → (AtomicCellE Val).O i →
    AtomicSt Val FState G → AtomicSt Val FState G → Prop
  | .call (.cas _ _), _, s, s' => Rel s.cell s'.cell
  | _, _, _, _ => True

/--
**Fail-closed (1b): reflexivity is necessary on a failed CAS retry.** Even when
`load`/`callF`/`dropF` are unconstrained (`CasOnlyHistStep`) and every
`Some (x + 1)` proposal strictly satisfies `x < x + 1`, a failed weak CAS under
quiescent interference performs no write (`cell ↦ cell`) and violates
`AlwaysStep (CasOnlyHistStep (· < ·))` on the failed-CAS branch itself.
-/
theorem irreflexive_breaks_failed_cas (s₀ : AtomicSt Nat PUnit PUnit)
    (Q : Except Nat Nat → AtomicSt Nat PUnit PUnit → Prop) :
    (∀ x, x < x + 1) ∧
      ¬ AlwaysStep (atomicHistWP quiescentTicketEnv) (CasOnlyHistStep (· < ·)) Q
        (tryUpdateLoop Nat) s₀ := by
  refine ⟨Nat.lt_succ_self, fun h => ?_⟩
  have h1 := ((histWP_load quiescentTicketEnv _ _).1 ((AlwaysStep.vis_iff _ _ _ _ _ _).1 h)
    s₀.cell rfl 0).2
  dsimp only [loadAns] at h1
  rw [iter_tryBody_eq] at h1
  have h2 := (((histWP_call quiescentTicketEnv _ _ _).1 ((AlwaysStep.vis_iff _ _ _ _ _ _).1 h1)).2
    PUnit.unit (some (s₀.cell + 1)) rfl).2
  rw [tryCallK_some, vis_bind] at h2
  have h3 := ((histWP_cas quiescentTicketEnv _ _ _ _).1 ((AlwaysStep.vis_iff _ _ _ _ _ _).1 h2)
    s₀.cell rfl 0).1.1
  exact Nat.lt_irrefl _ h3

/-- Bounded-jump relation `y ≤ x + 1`: reflexive but **not** transitive. -/
def BumpRel (x y : Nat) : Prop := y ≤ x + 1

/-- Interference and closure both make single bumps. -/
def bumpEnv : AtomicEnv Nat PUnit PUnit := ⟨BumpRel, ticketSpec, trivialGC⟩

/--
**Fail-closed (2): transitivity is necessary.** With the reflexive but
non-transitive `y ≤ x + 1`, interference `0 → 1` followed by the closure's
committed `1 → 2` respects the relation at every single step, yet breaks the
initial-to-current history `R 0 2`, so the safety theorem's `Always` fails.
-/
theorem nontransitive_breaks_history (s₀ : AtomicSt Nat PUnit PUnit) (hs₀ : s₀.cell = 0)
    (Q : Except Nat Nat → AtomicSt Nat PUnit PUnit → Prop) :
    (BumpRel 0 1 ∧ BumpRel 1 2 ∧ ¬ BumpRel 0 2) ∧ ¬ AtomicHistInv Nat BumpRel ∧
      ¬ Always (atomicHistWP bumpEnv) (fun s => BumpRel 0 s.cell) Q (tryUpdateLoop Nat) s₀ := by
  have hb : BumpRel 0 1 ∧ BumpRel 1 2 ∧ ¬ BumpRel 0 2 := by
    unfold BumpRel; omega
  refine ⟨hb, fun h => hb.2.2 (h.trans hb.1 hb.2.1), fun h => ?_⟩
  have h1 := (histWP_load bumpEnv _ _).1 ((Always.vis_iff _ _ _ _ _ _).1 h).2 1
    (show BumpRel s₀.cell 1 by rw [hs₀]; exact hb.1) 0
  rw [iter_tryBody_eq] at h1
  have h2 := ((histWP_call bumpEnv _ _ _).1 ((Always.vis_iff _ _ _ _ _ _).1 h1).2).2
    PUnit.unit (some 2) rfl
  rw [tryCallK_some, vis_bind] at h2
  have h3 := ((histWP_cas bumpEnv _ _ _ _).1 ((Always.vis_iff _ _ _ _ _ _).1 h2).2 1
    (show BumpRel 1 1 by unfold BumpRel; omega) 0).2 rfl
  have h4 := ((casWin_iff bumpEnv _ _ _ _ _).1 h3).2.2 PUnit.unit trivial
  exact hb.2.2 h4.inv

/-- A closure whose precondition holds only on its initial state `0`. -/
def onceSpec : FnMutSpec Nat Nat Nat where
  hist_inv f f' := f ≤ f'
  hist_inv_laws := AtomicHistInv.nat_le
  pre f _ := f = 0
  post_mut f x f' r := f' = f + 1 ∧ r = some (x + 1)
  step_hist_inv _ _ _ _ h := h.1 ▸ Nat.le_succ _
  resolve _ := True

/-- Monotone interference with the once-only closure. -/
def onceEnv : AtomicEnv Nat Nat PUnit := ⟨(· ≤ ·), onceSpec, trivialGC⟩

/--
**Fail-closed (3): the closure precondition must be `hist_inv`-closed.** The
closure's precondition holds at its initial state (`∀ x, pre f₀ x`), but not on
its `hist_inv`-successors; after one (possibly spurious) failed weak CAS the
retry calls the mutated closure outside its precondition, so even the liberal
precondition `DWLP` fails.
-/
theorem broken_closure_hist_inv (s₀ : AtomicSt Nat Nat PUnit) (hf : s₀.fst = 0)
    (Q : Except Nat Nat → AtomicSt Nat Nat PUnit → Prop) :
    (∀ x, onceSpec.pre 0 x) ∧ ¬ (∀ x f₂, onceSpec.hist_inv 0 f₂ → onceSpec.pre f₂ x) ∧
      ¬ DWLP (atomicHistWP onceEnv) (tryUpdateLoop Nat) Q s₀ := by
  refine ⟨fun _ => rfl, fun h => Nat.one_ne_zero (h 0 1 (Nat.zero_le 1)), fun h => ?_⟩
  have h1 := (histWP_load onceEnv _ _).1 ((DWLP.vis_iff _ _ _ _ _).1 h) s₀.cell
    (Nat.le_refl _) 0
  rw [iter_tryBody_eq] at h1
  have h2 := ((histWP_call onceEnv _ _ _).1 ((DWLP.vis_iff _ _ _ _ _).1 h1)).2 1
    (some (s₀.cell + 1)) ⟨by show 1 = s₀.fst + 1; rw [hf], rfl⟩
  rw [tryCallK_some, vis_bind] at h2
  have h3 := ((histWP_cas onceEnv _ _ _ _).1 ((DWLP.vis_iff _ _ _ _ _).1 h2) s₀.cell
    (Nat.le_refl _) 0).1
  rw [tryCasK_false, ret_bind, Sum.elim_inl, DWLP.tau_iff, iter_tryBody_eq] at h3
  exact absurd ((histWP_call onceEnv _ _ _).1 ((DWLP.vis_iff _ _ _ _ _).1 h3)).1 (by
    show ¬ (1 = 0); decide)

/-- Buggy program running two `try_update` loops without resetting the one-shot committer. -/
def doubleTryUpdate : ITree (AtomicCellE Nat) (Except Nat Nat) :=
  tryUpdateLoop Nat >>= fun _ => tryUpdateLoop Nat

/--
**Fail-closed (4): one-shot `Committer` rejects double-firing.** Running a
second winning CAS without acquiring a fresh `OneShotCommitter` violates
`casWin`'s `s.comm.shot_store = false` precondition, refuting `DWLP`.
-/
theorem double_cas_violates_oneshot_committer (s₀ : AtomicSt Nat PUnit PUnit)
    (Q : Except Nat Nat → AtomicSt Nat PUnit PUnit → Prop) :
    ¬ DWLP (atomicHistWP ticketEnv) doubleTryUpdate Q s₀ := by
  intro h
  unfold doubleTryUpdate tryUpdateLoop at h
  rw [vis_bind] at h
  have h1 := (histWP_load ticketEnv _ _).1 ((DWLP.vis_iff _ _ _ _ _).1 h) s₀.cell
    (Nat.le_refl _) 0
  dsimp only [loadAns] at h1
  rw [iter_tryBody_eq, vis_bind] at h1
  have h2 := ((histWP_call ticketEnv _ _ _).1 ((DWLP.vis_iff _ _ _ _ _).1 h1)).2
    PUnit.unit (some (s₀.cell + 1)) rfl
  rw [tryCallK_some, vis_bind, vis_bind] at h2
  have h3 := ((histWP_cas ticketEnv _ _ _ _).1 ((DWLP.vis_iff _ _ _ _ _).1 h2) s₀.cell
    (Nat.le_refl _) 0).2 rfl
  have h4 := ((casWin_iff ticketEnv _ _ _ _ _).1 h3).2.2 PUnit.unit trivial
  rw [tryCasK_true, retAfterDrop, vis_bind, vis_bind] at h4
  have h5 := (histWP_drop ticketEnv _ _).1 ((DWLP.vis_iff _ _ _ _ _).1 h4) (s₀.cell + 1)
    (Nat.le_refl _) 0 trivial
  rw [ret_bind, Sum.elim_inr, ret_bind] at h5
  have h6 := (histWP_load ticketEnv _ _).1 ((DWLP.vis_iff _ _ _ _ _).1 h5) (s₀.cell + 1)
    (Nat.le_refl _) 0
  dsimp only [loadAns] at h6
  rw [iter_tryBody_eq] at h6
  have h7 := ((histWP_call ticketEnv _ _ _).1 ((DWLP.vis_iff _ _ _ _ _).1 h6)).2
    PUnit.unit (some (s₀.cell + 2)) rfl
  rw [tryCallK_some, vis_bind] at h7
  have h8 := ((histWP_cas ticketEnv _ _ _ _).1 ((DWLP.vis_iff _ _ _ _ _).1 h7) (s₀.cell + 1)
    (Nat.le_refl _) 0).2 rfl
  exact Bool.noConfusion ((casWin_iff ticketEnv _ _ _ _ _).1 h8).1

private def ContShape (x : ITree (AtomicCellE Nat) (Except Nat Nat)) : Prop :=
  (∃ v, x = ITree.iter tryBody v) ∨ (∃ v, x = ITree.tau (ITree.iter tryBody v)) ∨
    (∃ v, x = ITree.vis (aCas v (v + 1)) (fun o => tryCasK v (v + 1) o >>= iterK))

/--
**Fail-closed (5): unbounded contention refutes termination (even for strong CAS).**
If the environment increments the ticket counter before every CAS, `tryUpdateLoop`
never terminates under either weak or strong CAS.
-/
theorem unbounded_contention_refutes_dwp (Q : Except Nat Nat → AtomicSt Nat PUnit PUnit → Prop)
    (s₀ : AtomicSt Nat PUnit PUnit) :
    ¬ DWP (atomicHistWP ticketEnv) (tryUpdateLoop Nat) Q s₀ := by
  intro h
  have h1 := (histWP_load ticketEnv _ _).1 ((DWP.vis_iff _ _ _ _ _).1 h) s₀.cell
    (Nat.le_refl _) 0
  refine DWP.induct (fun x _ => ContShape x → False) ?_ h1 (Or.inl ⟨_, rfl⟩)
  intro x s hx hshape
  rcases hshape with ⟨v, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩
  · rw [iter_tryBody_observe] at hx
    exact ((histWP_call ticketEnv v _ s).1 hx).2 PUnit.unit (some (v + 1)) rfl
      (Or.inr (Or.inr ⟨v, by simp only [tryCallK_some, vis_bind]⟩))
  · rw [ITree.observe_tau] at hx
    exact hx (Or.inl ⟨v, rfl⟩)
  · rw [ITree.observe_vis] at hx
    exact ((histWP_cas ticketEnv v (v + 1) _ s).1 hx (s.cell + 1) (Nat.le_succ _) 0).1
      (Or.inr (Or.inl ⟨s.cell + 1, by simp only [tryCasK_false, ret_bind, Sum.elim_inl]⟩))

theorem strong_cas_unbounded_contention_refutes_dwp
    (Q : Except Nat Nat → AtomicSt Nat PUnit PUnit → Prop)
    (s₀ : AtomicSt Nat PUnit PUnit) :
    ¬ DWP (atomicStrongHistWP ticketEnv) (tryUpdateLoop Nat) Q s₀ := by
  intro h
  have h1 := (strongWP_load ticketEnv _ _).1 ((DWP.vis_iff _ _ _ _ _).1 h) s₀.cell
    (Nat.le_refl _) 0
  refine DWP.induct (fun x s => s.cell ≥ 0 → (∃ v, x = ITree.iter tryBody v ∧ s.cell = v) ∨
      (∃ v, x = ITree.tau (ITree.iter tryBody v) ∧ s.cell = v) ∨
      (∃ v, x = ITree.vis (aCas v (v + 1)) (fun o => tryCasK v (v + 1) o >>= iterK) ∧
        s.cell = v) → False) ?_ h1 (Nat.zero_le _) (Or.inl ⟨_, rfl, rfl⟩)
  intro x s hx _ hshape
  rcases hshape with ⟨v, rfl, hsv⟩ | ⟨v, rfl, hsv⟩ | ⟨v, rfl, hsv⟩
  · rw [iter_tryBody_observe] at hx
    exact ((strongWP_call ticketEnv v _ s).1 hx).2 PUnit.unit (some (v + 1)) rfl
      (Nat.zero_le _) (Or.inr (Or.inr ⟨v, by simp only [tryCallK_some, vis_bind], hsv⟩))
  · rw [ITree.observe_tau] at hx
    exact hx (Nat.zero_le _) (Or.inl ⟨v, rfl, hsv⟩)
  · rw [ITree.observe_vis] at hx
    have hne : s.cell + 1 ≠ v := by omega
    exact ((strongWP_cas ticketEnv v (v + 1) _ s).1 hx (s.cell + 1) (Nat.le_succ _) 0).1 hne
      (Nat.zero_le _) (Or.inr (Or.inl ⟨s.cell + 1, by
        simp only [tryCasK_false, ret_bind, Sum.elim_inl], rfl⟩))

/--
**Fail-closed (6): spurious weak-CAS failures refute `DWP` even under quiescence.**
With zero interfering threads (`rely := Eq`), weak `compare_exchange_weak` may
spuriously fail forever, whereas strong `compare_exchange` terminates in one step.
-/
theorem weak_cas_quiescent_refutes_dwp (Q : Except Nat Nat → AtomicSt Nat PUnit PUnit → Prop)
    (s₀ : AtomicSt Nat PUnit PUnit) :
    ¬ DWP (atomicHistWP quiescentTicketEnv) (tryUpdateLoop Nat) Q s₀ := by
  intro h
  have h1 := (histWP_load quiescentTicketEnv _ _).1 ((DWP.vis_iff _ _ _ _ _).1 h) s₀.cell rfl 0
  refine DWP.induct (fun x _ => ContShape x → False) ?_ h1 (Or.inl ⟨_, rfl⟩)
  intro x s hx hshape
  rcases hshape with ⟨v, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩
  · rw [iter_tryBody_observe] at hx
    exact ((histWP_call quiescentTicketEnv v _ s).1 hx).2 PUnit.unit (some (v + 1)) rfl
      (Or.inr (Or.inr ⟨v, by simp only [tryCallK_some, vis_bind]⟩))
  · rw [ITree.observe_tau] at hx
    exact hx (Or.inl ⟨v, rfl⟩)
  · rw [ITree.observe_vis] at hx
    exact ((histWP_cas quiescentTicketEnv v (v + 1) _ s).1 hx s.cell rfl 0).1
      (Or.inr (Or.inl ⟨s.cell, by simp only [tryCasK_false, ret_bind, Sum.elim_inl]⟩))

/--
**2-axis separation (`compare_exchange` strong vs `compare_exchange_weak`)**:
under quiescence strong CAS terminates (`DWP`) while weak CAS refutes `DWP`;
under unbounded contention even strong CAS refutes `DWP` while keeping safety.
-/
theorem weak_vs_strong_cas_separation (s₀ : AtomicSt Nat PUnit PUnit)
    (hs : InitSt s₀.cell PUnit.unit PUnit.unit (.fresh s₀.cell) s₀) :
    DWP (atomicStrongHistWP quiescentTicketEnv) (tryUpdateLoop Nat)
        (CreusotPost quiescentTicketEnv (· ≤ ·) s₀.cell PUnit.unit PUnit.unit (.fresh s₀.cell))
        s₀ ∧
      ¬ DWP (atomicHistWP quiescentTicketEnv) (tryUpdateLoop Nat)
        (CreusotPost quiescentTicketEnv (· ≤ ·) s₀.cell PUnit.unit PUnit.unit (.fresh s₀.cell))
        s₀ ∧
      Always (atomicStrongHistWP ticketEnv) (HistInvSt ticketEnv (· ≤ ·) s₀.cell PUnit.unit)
        (CreusotPost ticketEnv (· ≤ ·) s₀.cell PUnit.unit PUnit.unit (.fresh s₀.cell))
        (tryUpdateLoop Nat) s₀ ∧
      ¬ DWP (atomicStrongHistWP ticketEnv) (tryUpdateLoop Nat)
        (CreusotPost ticketEnv (· ≤ ·) s₀.cell PUnit.unit PUnit.unit (.fresh s₀.cell)) s₀ :=
  ⟨tryUpdate_strong_quiescent_dwp (quiescentTicket_pre s₀.cell) (fun _ _ h => h.symm) hs,
   weak_cas_quiescent_refutes_dwp _ s₀,
   tryUpdate_strong_always_safety (ticket_pre s₀.cell) hs,
   strong_cas_unbounded_contention_refutes_dwp _ s₀⟩

/-- Closure with an unsatisfiable `resolve := False` (violating `AtomicEnv.Realizable`). -/
def falseResolveSpec : FnMutSpec PUnit Nat Nat where
  hist_inv _ _ := True
  hist_inv_laws := ⟨fun _ => trivial, fun _ _ => trivial⟩
  pre _ _ := True
  post_mut _ _ _ r := r = none
  step_hist_inv _ _ _ _ _ := trivial
  resolve _ := False

/-- Environment with unrealizable `resolve` (miracle canary). -/
def falseResolveEnv : AtomicEnv Nat PUnit PUnit := ⟨(· ≤ ·), falseResolveSpec, trivialGC⟩

/--
**Fail-closed (7): unrealizable `resolve` breaks `ExcludedMiracle` (miracle canary).**
Because `dropF` assumes `resolve` (prophetic drop), an unsatisfiable `resolve :=
False` discharges even `DWP ... (fun _ _ => False)`. This explains why
`AtomicEnv.Realizable` (`tryUpdate_nonvacuous_not_false`) is required for
non-vacuous termination claims.
-/
theorem unrealizable_resolve_miracle (s₀ : AtomicSt Nat PUnit PUnit) :
    ¬ falseResolveEnv.Realizable ∧
      DWP (atomicBudgetWP falseResolveEnv) (tryUpdateLoop Nat) (fun _ _ => False) s₀ := by
  refine ⟨fun hR => hR.resolve_total PUnit.unit, ?_⟩
  refine DWP.vis ((budgetWP_load falseResolveEnv _ s₀).2 fun v _ => ⟨fun _ => ?_, fun _ _ => ?_⟩)
  · rw [iter_tryBody_eq]
    refine DWP.vis ((budgetWP_call falseResolveEnv _ _ _).2 ⟨trivial, fun _ r hr => ?_⟩)
    have hr' : r = none := hr; subst hr'
    rw [tryCallK_none, retAfterDrop, vis_bind]
    exact DWP.vis ((budgetWP_drop falseResolveEnv _ _).2 fun _ _ =>
      ⟨fun _ hres => False.elim hres, fun _ _ hres => False.elim hres⟩)
  · rw [iter_tryBody_eq]
    refine DWP.vis ((budgetWP_call falseResolveEnv _ _ _).2 ⟨trivial, fun _ r hr => ?_⟩)
    have hr' : r = none := hr; subst hr'
    rw [tryCallK_none, retAfterDrop, vis_bind]
    exact DWP.vis ((budgetWP_drop falseResolveEnv _ _).2 fun _ _ =>
      ⟨fun _ hres => False.elim hres, fun _ _ hres => False.elim hres⟩)

/--
Unbounded contention: safety (`Always` + `DWLP`) holds while `DWP` and
`Eventually`-termination fail — the strict separation that motivates the
bounded-contention and fairness liveness theorems.
-/
theorem unbounded_contention_safe_but_not_live (s₀ : AtomicSt Nat PUnit PUnit)
    (hs : InitSt s₀.cell PUnit.unit PUnit.unit (.fresh s₀.cell) s₀) :
    Always (atomicHistWP ticketEnv) (HistInvSt ticketEnv (· ≤ ·) s₀.cell PUnit.unit)
        (CreusotPost ticketEnv (· ≤ ·) s₀.cell PUnit.unit PUnit.unit (.fresh s₀.cell))
        (tryUpdateLoop Nat) s₀ ∧
      DWLP (atomicHistWP ticketEnv) (tryUpdateLoop Nat)
        (CreusotPost ticketEnv (· ≤ ·) s₀.cell PUnit.unit PUnit.unit (.fresh s₀.cell)) s₀ ∧
      ¬ DWP (atomicHistWP ticketEnv) (tryUpdateLoop Nat)
        (CreusotPost ticketEnv (· ≤ ·) s₀.cell PUnit.unit PUnit.unit (.fresh s₀.cell)) s₀ ∧
      ¬ Eventually (atomicHistWP ticketEnv) (fun _ => False)
        (CreusotPost ticketEnv (· ≤ ·) s₀.cell PUnit.unit PUnit.unit (.fresh s₀.cell))
        (tryUpdateLoop Nat) s₀ := by
  have hsafe := tryUpdate_always_safety (ticket_pre s₀.cell) hs
  exact ⟨hsafe, hsafe.toDWLP, unbounded_contention_refutes_dwp _ s₀,
    fun he => unbounded_contention_refutes_dwp _ s₀ ((dwp_iff_eventually _ _ _ _).2 he)⟩

end FailClosed

/-! ## 10. Episode 2 Capstone -/

section Capstone

variable {Val FState G : Type} {A : AtomicEnv Val FState G} {Rel : Val → Val → Prop}
  {init : Val} {f₀ : FState} {g₀ : G} {comm₀ : OneShotCommitter Val}

/--
**Episode 2 capstone (`creusot#2386` `Atomic::try_update`)**: under the
`creusot#2386` preconditions, from any initial state, the single program
`tryUpdateLoop` simultaneously satisfies

1. `Always` history safety with the exact `creusot#2386` postcondition and its
   `DWLP` form, under unbounded rely-respecting contention and spurious weak-CAS
   failures;
2. transition safety (`AlwaysStep` with `HistStep`: zero-write failed CAS,
   one-shot committer firing);
3. `DWP` termination with the contract under bounded contention;
4. Streett liveness under CAS fairness (`FairInfOften … CasWon`) with
   non-vacuous CAS enabledness (`InfOften CasAttempt`) and the one-shot committer
   monitor (`FairBuchiSat`);
5. operational termination against every strongly fair `EnvStrategy`;

and every `AtomicDualContract` rejects the UB / spec-panic / `Frozen`-write
steps that would otherwise be abstracted as atomic-cell transitions.
-/
theorem ep2_creusot_try_update_capstone (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    {s₀ : AtomicSt Val FState G} (hs : InitSt init f₀ g₀ comm₀ s₀) :
    (Always (atomicHistWP A) (HistInvSt A Rel init f₀) (CreusotPost A Rel init f₀ g₀ comm₀)
        (tryUpdateLoop Val) s₀ ∧
      DWLP (guardInvWP (atomicHistWP A) (HistInvSt A Rel init f₀)) (tryUpdateLoop Val)
        (fun r s => HistInvSt A Rel init f₀ s ∧ CreusotPost A Rel init f₀ g₀ comm₀ r s) s₀) ∧
    AlwaysStep (atomicHistWP A) (HistStep A Rel) (CreusotPost A Rel init f₀ g₀ comm₀)
      (tryUpdateLoop Val) s₀ ∧
    DWP (atomicBudgetWP A) (tryUpdateLoop Val)
      (fun r s => HistInvSt A Rel init f₀ s ∧ CreusotPost A Rel init f₀ g₀ comm₀ r s) s₀ ∧
    (FairInfOften (atomicHistWP A) (fun _ _ _ _ => False) CasWon
        (CreusotPost A Rel init f₀ g₀ comm₀) (tryUpdateLoop Val) s₀ ∧
      InfOften (atomicHistWP A) CasAttempt (CreusotPost A Rel init f₀ g₀ comm₀)
        (tryUpdateLoop Val) s₀ ∧
      FairBuchiSat (committerSpec A Rel init f₀ g₀ comm₀) (fun _ i o s s' _ => CasWon i o s s')
        (tryUpdateLoop Val) false s₀) ∧
    (∀ (σ : EnvStrategy (AtomicCellE Val)) (tr₀ : List (Event (AtomicCellE Val))),
      (∀ ev : Stream' (Event (AtomicCellE Val)),
        InfRunWithStrategy σ tr₀ (tryUpdateLoop Val) ev →
        (∀ k, ∃ n, k ≤ n ∧ CasAttempt (ev n).req (ev n).ans (tr₀ ++ takePrefix ev n)
          (tr₀ ++ takePrefix ev (n + 1))) →
        (∀ k, ∃ n, k ≤ n ∧ CasWon (ev n).req (ev n).ans (tr₀ ++ takePrefix ev n)
          (tr₀ ++ takePrefix ev (n + 1)))) →
      ∃ tr r, RetWithStrategy σ tr₀ (tryUpdateLoop Val) tr r ∧ TracePost r (tr₀ ++ tr)) ∧
    (∀ (c : Anneal.Mir.AtomicIntrinsicsDualSpec.AtomicDualContract)
      (m : Anneal.Mir.AtomicIntrinsicsDualSpec.AtomicMemoryMode),
      ¬ AdmissibleAtomicStep (Anneal.Mir.AtomicIntrinsicsDualSpec.mrAtomicObserve m 17) ∧
      ¬ AdmissibleAtomicStep (Anneal.Mir.AtomicIntrinsicsDualSpec.mrAtomicObserve m 18) ∧
      ¬ AdmissibleAtomicStep (Anneal.Mir.AtomicIntrinsicsDualSpec.mrAtomicObserve m 19) ∧
      ¬ AdmissibleAtomicStep (c.lm.observe true 27)) :=
  ⟨⟨tryUpdate_always_safety hpre hs, tryUpdate_dwlp_creusot_spec hpre hs⟩,
   tryUpdate_alwaysStep_safety hpre hs, (tryUpdate_bounded_spec hpre hs).2,
   ⟨tryUpdate_fairInfOften hpre hs _, tryUpdate_infOften_attemptCas hpre hs,
    tryUpdate_fairBuchiSat_committer hpre hs⟩,
   fun σ tr₀ h_sf => tryUpdate_trace_strongFair_terminates σ tr₀ h_sf,
   fun c m => let h := admissible_fail_closed c m
     ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1⟩⟩

end Capstone

end Anneal.AtomicHistInv
