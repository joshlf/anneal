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
* **§6** Liveness: `DWP` / `Eventually` under bounded contention, unconditional
  strong-CAS termination under quiescence, non-vacuity (`¬ DWP ... False`),
  Streett `FairInfOften` / `CoBuchi` under CAS fairness, `InfOften` CAS
  enabledness, a one-shot committer `FairBuchiSat` monitor, and operational
  termination against every strongly fair `EnvStrategy`
  (`trace_strongFair_terminates` over `eventTraceWP`).
* **§7** A `#4162` diverging `-> !` ticket service composing `tryUpdateLoop`
  (`Always` with one-shot per-request committer + `InfOften TicketCommit` +
  `¬ DWP`, via `buchi_diverging_loop_rule`).
* **§8** Dual-authority & MiniRust grounding: all integer widths
  (`u8`/`u16`/`u32`/`u64`/`usize`), universal MiniRust CAS success/failure/
  frame/no-data-race/`MachTB.wfLive` laws, threaded traces, `AdmissibleAtomicStep`,
  and a direct `evalIntrinsicM`-backed transformer `mrCellWP` transporting
  `tryUpdateLoop` safety to `MachTB` while failing closed on misaligned / `u128`
  / `Frozen` UB.
* **§9** Fail-closed boundaries: irreflexive relations (on both `Err` and failed
  CAS), non-transitive relations, non-`hist_inv`-closed closure preconditions,
  one-shot committer double-fire rejection, weak-vs-strong CAS 2-axis
  separation, unbounded contention, and unrealizable `resolve` miracle canary.
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

/--
Operational admissibility of a MiniRust cell `(ptr, pty, t)` under machine-level
interference `mRely`, **coupled** to the logical cell: `MInv m c` says machine
`m` holds value `c` in the cell. Interference may stutter (so the bridge cannot
be discharged by an empty, miraculous `mRely`, cf. `mrCellWP_empty_rely_miracle`)
and moves the held value along
`A.rely`; loads return exactly the held value and write nothing; a CAS returns
the held value and stores `desired` exactly when the held value equals
`expected` (the shape of `atomicCompareExchange_ok_iff`).
-/
structure MrCellAdmissible {M FState G : Type} [Memory M] [MemoryOps M]
    (A : AtomicEnv Nat FState G)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (t : IntType)
    (mRely : Machine M → Machine M → Prop) (MInv : Machine M → Nat → Prop)
    (Rel : Nat → Nat → Prop) : Prop where
  rely_refl : ∀ m c, MInv m c → mRely m m
  rely_pres : ∀ m c m', MInv m c → mRely m m' → ∃ c', A.rely c c' ∧ MInv m' c'
  load_ok : ∀ m c, MInv m c → ∃ v m', mrLoadOk m ptr pty t v m'
  load_val : ∀ m c v m', MInv m c → mrLoadOk m ptr pty t v m' → v.toNat = c ∧ MInv m' c
  cas_ok : ∀ m c e d, MInv m c → Rel e d → ∃ ret m', mrCasOk m ptr pty t e d ret m'
  cas_val : ∀ m c e d ret m', MInv m c → Rel e d → mrCasOk m ptr pty t e d ret m' →
    ret.toNat = c ∧ (c = e → MInv m' d) ∧ (c ≠ e → MInv m' c)

/-- Machine interference followed by a load: the observed value is `rely`-related. -/
private theorem mr_observe {M FState G : Type} [Memory M] [MemoryOps M]
    {A : AtomicEnv Nat FState G} {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»}
    {t : IntType} {mRely : Machine M → Machine M → Prop} {MInv : Machine M → Nat → Prop}
    {Rel : Nat → Nat → Prop} (hadm : MrCellAdmissible A ptr pty t mRely MInv Rel)
    {m m₁ m₂ : Machine M} {c : Nat} {v : Int} (hm : MInv m c) (hr : mRely m m₁)
    (hl : mrLoadOk m₁ ptr pty t v m₂) : A.rely c v.toNat ∧ MInv m₂ v.toNat := by
  obtain ⟨c', hc', hm₁⟩ := hadm.rely_pres m c m₁ hm hr
  obtain ⟨hv, hm₂⟩ := hadm.load_val m₁ c' v m₂ hm₁ hl
  exact ⟨hv ▸ hc', hv ▸ hm₂⟩

/--
**Machine-backed safety (`tryUpdate_mr_always_safety`)**: for any memory model
`M` and coupled MiniRust admissibility invariant `MInv`, `tryUpdateLoop`
executes without UB/specPanic on `mrCellWP`, every machine observation is
*proved* `rely`-related to the logical history, the machine keeps holding the
logical cell value, `HistInvSt` holds at every step, and every return
establishes the exact `creusot#2386` postcondition.
-/
theorem tryUpdate_mr_always_safety {M FState G : Type} [Memory M] [MemoryOps M]
    {A : AtomicEnv Nat FState G} {Rel : Nat → Nat → Prop}
    {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»} {t : IntType}
    {mRely : Machine M → Machine M → Prop} {MInv : Machine M → Nat → Prop}
    {init : Nat} {f₀ : FState} {g₀ : G} {comm₀ : OneShotCommitter Nat}
    (hpre : TryUpdatePre A Rel init f₀ g₀ comm₀)
    (hadm : MrCellAdmissible A ptr pty t mRely MInv Rel)
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
    have hrn := (loopInv_rel_next hpre hl hpost).1
    refine Always.vis ⟨hm, hinv⟩ fun m₁' hm₁' => ?_
    obtain ⟨c', hc', hmc'⟩ := hadm.rely_pres m _ m₁' hm hm₁'
    refine ⟨hadm.cas_ok m₁' c' prev next hmc' hrn, fun ret m₂' hcas => ?_⟩
    obtain ⟨hret, hstore, hkeep⟩ := hadm.cas_val m₁' c' prev next ret m₂' hmc' hrn hcas
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
    (hadm : MrCellAdmissible A ptr pty t mRely MInv Rel)
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
      (fun m c => MInv m c ∧ MiniRustSpec.Correspondence.MachTB.wfLive m) Rel :=
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
  have h := tryUpdate_mr_always_safety hpre hadm' ⟨hm₀, hwf₀⟩ hs₀
  exact Always.mono (fun _ hi => ⟨⟨hi.1.1, hi.1.2⟩, hi.2⟩)
    (fun _ _ hq => ⟨⟨hq.1.1, hq.1.2⟩, hq.2⟩) h

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

end Anneal.AtomicHistInv
