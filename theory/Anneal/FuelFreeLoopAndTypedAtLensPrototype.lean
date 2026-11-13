-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.PureMirExec
import Anneal.MirLiftCore
import Anneal.MirFuelFree
import Anneal.MirLoops
import Anneal.SepLogicLenses
import Anneal.ByteCodec

/-!
# Track P prototype: fuel-free loop lifting, `forcePureEnv`, `TypedAt` lenses,
# and pre-release `reborrowFootprint` protector specs

Prototype-only module (not imported by `Anneal.lean`) validating four
proof-ergonomics components against the live signatures of
`Anneal.PureMirExec`, `Anneal.MirLiftCore`, `Anneal.MirFuelFree`,
`Anneal.MirLoops`, `Anneal.SepLogicLenses`, and `Anneal.ByteCodec`:

1. **Fuel-free loop lifting** (Sections 1–6): a generic deterministic small-step
   machine with Kleene fuel monotonicity (`evalFuel_mono`), fuel-free
   convergence (`WpConverges`, `StepsTo.bind_wp`), header-targeted stepping
   (`runToTarget` / `runCfgToBlock`) that distinguishes `.reached`, `.halted`,
   `.stuck`, and `.outOfFuel` and provably stops at the *first* target re-entry,
   structural `[lo, hi)` loops (`forRangeUp`, proven equal to the live
   `Anneal.MirLoops.forRangeUp`), the impossibility of a uniform fuel constant
   for a multi-block `countUp` CFG (`no_uniform_fuel_countUp`), and fuel-free
   total correctness for every symbolic bound (`countUp_wpConverges_all_n`).
   Bridges transport these results to the live MIR predicates
   (`mirWpConverges_of_wpConverges`, `mirStepsConverges_of_stepsTo`) and relate
   toy CFG shapes to the live `MirFragment` classifier
   (`inferMinFragment_toMirShape`).
2. **`forcePureEnv` slot-list normalization** (Section 7): spine-forcing
   normalization of `List α` frames (specialized to the live
   `Anneal.MirLiftCore.PureEnv`).
3. **`TypedAt` / `DisjointSlice` byte lenses** (Section 8) over the *trusted*
   byte primitives `sliceAbstractBytes` / `writeAbstractBytesAt` and live
   `Anneal.ByteCodec.FixedByteCodec` codecs, with live
   `Anneal.FunctionalTranslation.LawfulMutLens` and
   `Anneal.SepLogicLenses.IndependentLenses` witnesses.
4. **Two-stage Tree Borrows protector release with a pre-release
   `reborrowFootprint`** (Section 9), including a concrete callee semantics,
   a declarative `TrustedFnSpec`, their equivalence, and a negative control.

Every exported theorem is audited by a `#guard_msgs in #print axioms` block in
Section 10 (constructive axioms `propext` / `Quot.sound` only).
-/

namespace Anneal.FuelFreeLoopAndTypedAtLensPrototype

/-! ## 1. Generic deterministic small-step machine and the Kleene fuel order -/

/-- Outcome of one deterministic small step. -/
inductive Step (σ α : Type) where
  /-- Continue at `next`. -/
  | cont (next : σ)
  /-- Halt returning `ret`. -/
  | done (ret : α)
  /-- Stuck / undefined behavior. -/
  | fault

/-- Outcome of a bounded-fuel evaluation: running out of fuel is *not* a fault
and is never conflated with halting. -/
inductive FuelResult (α : Type) where
  | outOfFuel
  | halted (v : α)
  | faulted
  deriving DecidableEq, Repr

/-- Flat Kleene information order: `outOfFuel` is bottom; `halted v` and
`faulted` are maximal. -/
def FuelOrder {α : Type} : FuelResult α → FuelResult α → Prop
  | .outOfFuel, _ => True
  | .halted v₁, .halted v₂ => v₁ = v₂
  | .faulted, .faulted => True
  | _, _ => False

theorem FuelOrder.refl {α : Type} (r : FuelResult α) : FuelOrder r r := by
  cases r with
  | outOfFuel => exact trivial
  | halted v => exact rfl
  | faulted => exact trivial

theorem FuelOrder.trans {α : Type} {r₁ r₂ r₃ : FuelResult α}
    (h₁₂ : FuelOrder r₁ r₂) (h₂₃ : FuelOrder r₂ r₃) : FuelOrder r₁ r₃ := by
  cases r₁ <;> cases r₂ <;> cases r₃ <;> simp_all [FuelOrder]

theorem FuelOrder.halted_stable {α : Type} {v : α} {r : FuelResult α}
    (h : FuelOrder (.halted v) r) : r = .halted v := by
  cases r <;> simp_all [FuelOrder]

theorem FuelOrder.faulted_stable {α : Type} {r : FuelResult α}
    (h : FuelOrder .faulted r) : r = .faulted := by
  cases r <;> simp_all [FuelOrder]

/-- Fueled evaluator by structural recursion on the fuel. -/
def evalFuel {σ α : Type} (step : σ → Step σ α) : Nat → σ → FuelResult α
  | 0, _ => .outOfFuel
  | k + 1, s =>
    match step s with
    | .cont s' => evalFuel step k s'
    | .done v => .halted v
    | .fault => .faulted

/-- **Kleene fuel monotonicity**: adding fuel preserves every terminal outcome. -/
theorem evalFuel_mono {σ α : Type} (step : σ → Step σ α) :
    ∀ {k₁ k₂ : Nat} (s : σ), k₁ ≤ k₂ →
      FuelOrder (evalFuel step k₁ s) (evalFuel step k₂ s)
  | 0, _, _, _ => trivial
  | k₁ + 1, 0, _, hle => absurd hle (Nat.not_succ_le_zero k₁)
  | k₁ + 1, k₂ + 1, s, hle => by
    unfold evalFuel
    cases step s with
    | cont s' => exact evalFuel_mono step s' (Nat.le_of_succ_le_succ hle)
    | done v => exact rfl
    | fault => exact trivial

theorem evalFuel_halted_mono {σ α : Type} {step : σ → Step σ α} {k₁ k₂ : Nat}
    {s : σ} {v : α} (h : evalFuel step k₁ s = .halted v) (hle : k₁ ≤ k₂) :
    evalFuel step k₂ s = .halted v := by
  have hm := evalFuel_mono step s hle
  rw [h] at hm
  exact FuelOrder.halted_stable hm

theorem evalFuel_faulted_mono {σ α : Type} {step : σ → Step σ α} {k₁ k₂ : Nat}
    {s : σ} (h : evalFuel step k₁ s = .faulted) (hle : k₁ ≤ k₂) :
    evalFuel step k₂ s = .faulted := by
  have hm := evalFuel_mono step s hle
  rw [h] at hm
  exact FuelOrder.faulted_stable hm

/-- Halting results are fuel-independent (determinism). -/
theorem evalFuel_halted_deterministic {σ α : Type} {step : σ → Step σ α}
    {k₁ k₂ : Nat} {s : σ} {v₁ v₂ : α}
    (h₁ : evalFuel step k₁ s = .halted v₁) (h₂ : evalFuel step k₂ s = .halted v₂) :
    v₁ = v₂ := by
  have e₁ := evalFuel_halted_mono h₁ (Nat.le_max_left k₁ k₂)
  have e₂ := evalFuel_halted_mono h₂ (Nat.le_max_right k₁ k₂)
  rw [e₁] at e₂
  exact FuelResult.halted.inj e₂

/-- A state that faults under some fuel never halts under any fuel: faults are
never conflated with termination. -/
theorem evalFuel_faulted_ne_halted {σ α : Type} {step : σ → Step σ α}
    {k₁ k₂ : Nat} {s : σ} {v : α}
    (hf : evalFuel step k₁ s = .faulted) : evalFuel step k₂ s ≠ .halted v := by
  intro hh
  have e₁ := evalFuel_faulted_mono hf (Nat.le_max_left k₁ k₂)
  have e₂ := evalFuel_halted_mono hh (Nat.le_max_right k₁ k₂)
  rw [e₁] at e₂
  cases e₂

/-- Fuel-free total-correctness predicate: some finite budget halts in `post`. -/
def WpConverges {σ α : Type} (step : σ → Step σ α) (s : σ) (post : α → Prop) : Prop :=
  ∃ k v, evalFuel step k s = .halted v ∧ post v

theorem WpConverges.of_done {σ α : Type} {step : σ → Step σ α} {s : σ} {v : α}
    {post : α → Prop} (hd : step s = .done v) (hp : post v) :
    WpConverges step s post :=
  ⟨1, v, by simp [evalFuel, hd], hp⟩

theorem WpConverges.of_cont {σ α : Type} {step : σ → Step σ α} {s s' : σ}
    {post : α → Prop} (hs : step s = .cont s') (h : WpConverges step s' post) :
    WpConverges step s post := by
  obtain ⟨k, v, hk, hp⟩ := h
  exact ⟨k + 1, v, by simp [evalFuel, hs, hk], hp⟩

theorem WpConverges.mono {σ α : Type} {step : σ → Step σ α} {s : σ}
    {P Q : α → Prop} (himp : ∀ v, P v → Q v) (h : WpConverges step s P) :
    WpConverges step s Q := by
  obtain ⟨k, v, hk, hp⟩ := h
  exact ⟨k, v, hk, himp v hp⟩

/-- Fault soundness: a faulting state never converges. -/
theorem not_wpConverges_of_faulted {σ α : Type} {step : σ → Step σ α} {s : σ}
    {k : Nat} {post : α → Prop} (hf : evalFuel step k s = .faulted) :
    ¬ WpConverges step s post := by
  rintro ⟨k', v, hk', _⟩
  exact evalFuel_faulted_ne_halted hf hk'

/-- Converged return values are unique. -/
theorem WpConverges.deterministic {σ α : Type} {step : σ → Step σ α} {s : σ}
    {v₁ v₂ : α} (h₁ : WpConverges step s (· = v₁)) (h₂ : WpConverges step s (· = v₂)) :
    v₁ = v₂ := by
  obtain ⟨k₁, w₁, hk₁, hw₁⟩ := h₁
  obtain ⟨k₂, w₂, hk₂, hw₂⟩ := h₂
  subst hw₁ hw₂
  exact evalFuel_halted_deterministic hk₁ hk₂

/-- Multi-step segment reachability of an intermediate predicate `mid`. -/
inductive StepsTo {σ α : Type} (step : σ → Step σ α) : σ → (σ → Prop) → Prop where
  | refl {s : σ} {mid : σ → Prop} (h : mid s) : StepsTo step s mid
  | step {s s' : σ} {mid : σ → Prop}
      (hstep : step s = .cont s') (hrest : StepsTo step s' mid) : StepsTo step s mid

/-- **Sequential bind rule**: fuel budgets are synthesized existentially across
segments, so user proofs never mention fuel numerals. -/
theorem StepsTo.bind_wp {σ α : Type} {step : σ → Step σ α} {s : σ}
    {mid : σ → Prop} {post : α → Prop}
    (hseg : StepsTo step s mid)
    (hcont : ∀ s₁, mid s₁ → WpConverges step s₁ post) :
    WpConverges step s post := by
  induction hseg with
  | refl hm => exact hcont _ hm
  | step hs _ ih => exact WpConverges.of_cont hs (ih hcont)

theorem StepsTo.trans {σ α : Type} {step : σ → Step σ α} {s : σ}
    {mid₁ mid₂ : σ → Prop}
    (h₁ : StepsTo step s mid₁) (h₂ : ∀ s₁, mid₁ s₁ → StepsTo step s₁ mid₂) :
    StepsTo step s mid₂ := by
  induction h₁ with
  | refl hm => exact h₂ _ hm
  | step hs _ ih => exact StepsTo.step hs (ih h₂)

theorem StepsTo.mono {σ α : Type} {step : σ → Step σ α} {s : σ}
    {mid₁ mid₂ : σ → Prop} (himp : ∀ s₁, mid₁ s₁ → mid₂ s₁)
    (h : StepsTo step s mid₁) : StepsTo step s mid₂ :=
  h.trans (fun s₁ hm => StepsTo.refl (himp s₁ hm))

/-! ## 2. Header-targeted stepping (`runToTarget` / `runCfgToBlock`) -/

/-- Outcome of a header-targeted segment run.  The four outcomes are pairwise
distinct constructors: reaching the target, halting, getting stuck, and running
out of the internal step ceiling are never conflated. -/
inductive TargetOutcome (σ α : Type) where
  | reached (s : σ)
  | halted (v : α)
  | stuck
  | outOfFuel

/-- Zero-or-more-step search for the next target state. -/
def runUntilTarget {σ α : Type} (step : σ → Step σ α) (atTarget : σ → Bool) :
    Nat → σ → TargetOutcome σ α
  | 0, s => if atTarget s then .reached s else .outOfFuel
  | bound + 1, s =>
    if atTarget s then .reached s
    else
      match step s with
      | .cont s' => runUntilTarget step atTarget bound s'
      | .done v => .halted v
      | .fault => .stuck

/-- One mandatory step (so starting *at* a loop header advances through the
body) followed by the search for the next target entry within `bound` extra
steps. -/
def runToTarget {σ α : Type} (step : σ → Step σ α) (atTarget : σ → Bool)
    (bound : Nat) (s : σ) : TargetOutcome σ α :=
  match step s with
  | .cont s' => runUntilTarget step atTarget bound s'
  | .done v => .halted v
  | .fault => .stuck

theorem runUntilTarget_reached_atTarget {σ α : Type} (step : σ → Step σ α)
    (atTarget : σ → Bool) :
    ∀ (bound : Nat) (s s_hit : σ),
      runUntilTarget step atTarget bound s = .reached s_hit → atTarget s_hit = true
  | 0, s, s_hit, h => by
    unfold runUntilTarget at h
    cases ht : atTarget s with
    | true => rw [ht] at h; cases h; exact ht
    | false => rw [ht] at h; cases h
  | bound + 1, s, s_hit, h => by
    unfold runUntilTarget at h
    cases ht : atTarget s with
    | true => rw [ht] at h; cases h; exact ht
    | false =>
      rw [ht] at h
      cases hs : step s with
      | cont s' =>
        rw [hs] at h
        exact runUntilTarget_reached_atTarget step atTarget bound s' s_hit h
      | done _ => rw [hs] at h; cases h
      | fault => rw [hs] at h; cases h

/-- A `.reached` outcome always lands on a target state. -/
theorem runToTarget_reached_atTarget {σ α : Type} {step : σ → Step σ α}
    {atTarget : σ → Bool} {bound : Nat} {s s_hit : σ}
    (h : runToTarget step atTarget bound s = .reached s_hit) : atTarget s_hit = true := by
  unfold runToTarget at h
  cases hs : step s with
  | cont s' => rw [hs] at h; exact runUntilTarget_reached_atTarget step atTarget bound s' s_hit h
  | done _ => rw [hs] at h; cases h
  | fault => rw [hs] at h; cases h

theorem stepsTo_of_runUntilTarget_reached {σ α : Type} (step : σ → Step σ α)
    (atTarget : σ → Bool) :
    ∀ (bound : Nat) (s s_hit : σ),
      runUntilTarget step atTarget bound s = .reached s_hit → StepsTo step s (· = s_hit)
  | 0, s, s_hit, h => by
    unfold runUntilTarget at h
    cases ht : atTarget s with
    | true => rw [ht] at h; cases h; exact StepsTo.refl rfl
    | false => rw [ht] at h; cases h
  | bound + 1, s, s_hit, h => by
    unfold runUntilTarget at h
    cases ht : atTarget s with
    | true => rw [ht] at h; cases h; exact StepsTo.refl rfl
    | false =>
      rw [ht] at h
      cases hs : step s with
      | cont s' =>
        rw [hs] at h
        exact StepsTo.step hs (stepsTo_of_runUntilTarget_reached step atTarget bound s' s_hit h)
      | done _ => rw [hs] at h; cases h
      | fault => rw [hs] at h; cases h

/-- **Target arrival soundness** (generic form). -/
theorem stepsTo_of_runToTarget_reached {σ α : Type} {step : σ → Step σ α}
    {atTarget : σ → Bool} {bound : Nat} {s s_hit : σ}
    (h : runToTarget step atTarget bound s = .reached s_hit) :
    StepsTo step s (· = s_hit) := by
  unfold runToTarget at h
  cases hs : step s with
  | cont s' =>
    rw [hs] at h
    exact StepsTo.step hs (stepsTo_of_runUntilTarget_reached step atTarget bound s' s_hit h)
  | done _ => rw [hs] at h; cases h
  | fault => rw [hs] at h; cases h

theorem wpConverges_of_runUntilTarget_halted {σ α : Type} (step : σ → Step σ α)
    (atTarget : σ → Bool) {post : α → Prop} :
    ∀ (bound : Nat) (s : σ) (v : α),
      runUntilTarget step atTarget bound s = .halted v → post v → WpConverges step s post
  | 0, s, _, h, _ => by
    unfold runUntilTarget at h
    cases ht : atTarget s <;> rw [ht] at h <;> cases h
  | bound + 1, s, v, h, hp => by
    unfold runUntilTarget at h
    cases ht : atTarget s with
    | true => rw [ht] at h; cases h
    | false =>
      rw [ht] at h
      cases hs : step s with
      | cont s' =>
        rw [hs] at h
        exact WpConverges.of_cont hs
          (wpConverges_of_runUntilTarget_halted step atTarget bound s' v h hp)
      | done v₀ => rw [hs] at h; cases h; exact WpConverges.of_done hs hp
      | fault => rw [hs] at h; cases h

/-- **Halting soundness** (generic form). -/
theorem wpConverges_of_runToTarget_halted {σ α : Type} {step : σ → Step σ α}
    {atTarget : σ → Bool} {bound : Nat} {s : σ} {v : α} {post : α → Prop}
    (h : runToTarget step atTarget bound s = .halted v) (hp : post v) :
    WpConverges step s post := by
  unfold runToTarget at h
  cases hs : step s with
  | cont s' =>
    rw [hs] at h
    exact WpConverges.of_cont hs (wpConverges_of_runUntilTarget_halted step atTarget bound s' v h hp)
  | done v₀ => rw [hs] at h; cases h; exact WpConverges.of_done hs hp
  | fault => rw [hs] at h; cases h

theorem faulted_of_runUntilTarget_stuck {σ α : Type} (step : σ → Step σ α)
    (atTarget : σ → Bool) :
    ∀ (bound : Nat) (s : σ),
      runUntilTarget step atTarget bound s = .stuck → ∃ k, evalFuel step k s = .faulted
  | 0, s, h => by
    unfold runUntilTarget at h
    cases ht : atTarget s <;> rw [ht] at h <;> cases h
  | bound + 1, s, h => by
    unfold runUntilTarget at h
    cases ht : atTarget s with
    | true => rw [ht] at h; cases h
    | false =>
      rw [ht] at h
      cases hs : step s with
      | cont s' =>
        rw [hs] at h
        obtain ⟨k, hk⟩ := faulted_of_runUntilTarget_stuck step atTarget bound s' h
        exact ⟨k + 1, by simp [evalFuel, hs, hk]⟩
      | done _ => rw [hs] at h; cases h
      | fault => exact ⟨1, by simp [evalFuel, hs]⟩

/-- **Stuck soundness**: a `.stuck` outcome is a genuine fault, so the state can
never converge (stuck is never conflated with halting). -/
theorem not_wpConverges_of_runToTarget_stuck {σ α : Type} {step : σ → Step σ α}
    {atTarget : σ → Bool} {bound : Nat} {s : σ} {post : α → Prop}
    (h : runToTarget step atTarget bound s = .stuck) : ¬ WpConverges step s post := by
  unfold runToTarget at h
  cases hs : step s with
  | cont s' =>
    rw [hs] at h
    obtain ⟨k, hk⟩ := faulted_of_runUntilTarget_stuck step atTarget bound s' h
    exact not_wpConverges_of_faulted (k := k + 1) (by simp [evalFuel, hs, hk])
  | done _ => rw [hs] at h; cases h
  | fault => exact not_wpConverges_of_faulted (k := 1) (by simp [evalFuel, hs])

theorem runUntilTarget_mono_bound {σ α : Type} (step : σ → Step σ α)
    (atTarget : σ → Bool) :
    ∀ {b₁ b₂ : Nat} (s : σ),
      runUntilTarget step atTarget b₁ s ≠ .outOfFuel → b₁ ≤ b₂ →
      runUntilTarget step atTarget b₂ s = runUntilTarget step atTarget b₁ s
  | 0, 0, _, _, _ => rfl
  | 0, b₂ + 1, s, hne, _ => by
    unfold runUntilTarget at hne ⊢
    cases ht : atTarget s with
    | true => rfl
    | false => rw [ht] at hne; exact absurd rfl hne
  | _ + 1, 0, _, _, hle => absurd hle (Nat.not_succ_le_zero _)
  | b₁ + 1, b₂ + 1, s, hne, hle => by
    unfold runUntilTarget at hne ⊢
    cases ht : atTarget s with
    | true => rfl
    | false =>
      rw [ht] at hne
      cases hs : step s with
      | cont s' =>
        rw [hs] at hne
        exact runUntilTarget_mono_bound step atTarget s' hne (Nat.le_of_succ_le_succ hle)
      | done _ => rfl
      | fault => rfl

/-- **Ceiling monotonicity**: once a run is conclusive (`≠ .outOfFuel`) under
`b₁`, every larger ceiling returns the identical outcome. -/
theorem runToTarget_mono_bound {σ α : Type} {step : σ → Step σ α}
    {atTarget : σ → Bool} {b₁ b₂ : Nat} {s : σ}
    (hne : runToTarget step atTarget b₁ s ≠ .outOfFuel) (hle : b₁ ≤ b₂) :
    runToTarget step atTarget b₂ s = runToTarget step atTarget b₁ s := by
  unfold runToTarget at hne ⊢
  cases hs : step s with
  | cont s' =>
    rw [hs] at hne
    exact runUntilTarget_mono_bound step atTarget s' hne hle
  | done _ => rfl
  | fault => rfl

/-- `FirstHitIn n s s_hit`: after one mandatory step and `n` further silent
steps through non-target states, `s` reaches the target state `s_hit`, and no
earlier visited state (other than possibly `s` itself) is a target. -/
inductive FirstHitIn {σ α : Type} (step : σ → Step σ α) (atTarget : σ → Bool) :
    Nat → σ → σ → Prop where
  | here {s s' : σ} (hs : step s = .cont s') (ht : atTarget s' = true) :
      FirstHitIn step atTarget 0 s s'
  | later {n : Nat} {s s' s_hit : σ} (hs : step s = .cont s') (hnt : atTarget s' = false)
      (hrest : FirstHitIn step atTarget n s' s_hit) :
      FirstHitIn step atTarget (n + 1) s s_hit

/-- The first target re-entry is unique (and so is its step count). -/
theorem FirstHitIn.unique {σ α : Type} {step : σ → Step σ α} {atTarget : σ → Bool} :
    ∀ {n₁ n₂ : Nat} {s a b : σ},
      FirstHitIn step atTarget n₁ s a → FirstHitIn step atTarget n₂ s b → a = b ∧ n₁ = n₂
  | _, _, _, _, _, .here hs₁ ht₁, .here hs₂ _ => by
    rw [hs₁] at hs₂; cases hs₂; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, .here hs₁ ht₁, .later hs₂ hnt₂ _ => by
    rw [hs₁] at hs₂; cases hs₂; rw [ht₁] at hnt₂; cases hnt₂
  | _, _, _, _, _, .later hs₁ hnt₁ _, .here hs₂ ht₂ => by
    rw [hs₁] at hs₂; cases hs₂; rw [ht₂] at hnt₁; cases hnt₁
  | _, _, _, _, _, .later hs₁ _ h₁, .later hs₂ _ h₂ => by
    rw [hs₁] at hs₂; cases hs₂
    obtain ⟨hab, hn⟩ := FirstHitIn.unique h₁ h₂
    exact ⟨hab, congrArg (· + 1) hn⟩

theorem firstHitIn_of_runUntilTarget_reached {σ α : Type} (step : σ → Step σ α)
    (atTarget : σ → Bool) :
    ∀ (bound : Nat) (s₀ s s_hit : σ), step s₀ = .cont s →
      runUntilTarget step atTarget bound s = .reached s_hit →
      ∃ n, n ≤ bound ∧ FirstHitIn step atTarget n s₀ s_hit
  | 0, s₀, s, s_hit, h0, h => by
    unfold runUntilTarget at h
    cases ht : atTarget s with
    | true => rw [ht] at h; cases h; exact ⟨0, Nat.le_refl 0, .here h0 ht⟩
    | false => rw [ht] at h; cases h
  | bound + 1, s₀, s, s_hit, h0, h => by
    unfold runUntilTarget at h
    cases ht : atTarget s with
    | true => rw [ht] at h; cases h; exact ⟨0, Nat.zero_le _, .here h0 ht⟩
    | false =>
      rw [ht] at h
      cases hs : step s with
      | cont s' =>
        rw [hs] at h
        obtain ⟨n, hn, hfh⟩ := firstHitIn_of_runUntilTarget_reached step atTarget bound s s' s_hit hs h
        exact ⟨n + 1, Nat.succ_le_succ hn, .later h0 ht hfh⟩
      | done _ => rw [hs] at h; cases h
      | fault => rw [hs] at h; cases h

/-- **No overshoot**: a `.reached s_hit` outcome is exactly the *first* target
re-entry (within the ceiling); combined with `FirstHitIn.unique`, the stepper
can never skip past a loop header, even on self-loops. -/
theorem firstHitIn_of_runToTarget_reached {σ α : Type} {step : σ → Step σ α}
    {atTarget : σ → Bool} {bound : Nat} {s s_hit : σ}
    (h : runToTarget step atTarget bound s = .reached s_hit) :
    ∃ n, n ≤ bound ∧ FirstHitIn step atTarget n s s_hit := by
  unfold runToTarget at h
  cases hs : step s with
  | cont s' =>
    rw [hs] at h
    exact firstHitIn_of_runUntilTarget_reached step atTarget bound s s' s_hit hs h
  | done _ => rw [hs] at h; cases h
  | fault => rw [hs] at h; cases h

theorem runUntilTarget_of_firstHitIn {σ α : Type} {step : σ → Step σ α}
    {atTarget : σ → Bool} :
    ∀ {n : Nat} {s₀ s_hit : σ}, FirstHitIn step atTarget n s₀ s_hit →
      ∀ (s : σ), step s₀ = .cont s → ∀ (bound : Nat), n ≤ bound →
        runUntilTarget step atTarget bound s = .reached s_hit
  | _, _, _, .here hs ht, s, h0, bound, _ => by
    rw [hs] at h0; cases h0
    cases bound with
    | zero => unfold runUntilTarget; rw [ht]; rfl
    | succ b => unfold runUntilTarget; rw [ht]; rfl
  | _, _, _, .later (n := n) (s' := s') hs hnt hrest, s, h0, bound, hle => by
    rw [hs] at h0; cases h0
    cases bound with
    | zero => exact absurd hle (Nat.not_succ_le_zero n)
    | succ b =>
      unfold runUntilTarget
      rw [hnt]
      cases hrest with
      | here hs' ht' =>
        rw [hs']
        exact runUntilTarget_of_firstHitIn (.here hs' ht') _ hs' b (Nat.zero_le b)
      | later hs' hnt' hrest' =>
        rw [hs']
        exact runUntilTarget_of_firstHitIn (.later hs' hnt' hrest') _ hs' b
          (Nat.le_of_succ_le_succ hle)

/-- **Completeness**: the first target re-entry is found by every sufficiently
large ceiling, so the ceiling only affects completeness, never soundness. -/
theorem runToTarget_of_firstHitIn {σ α : Type} {step : σ → Step σ α}
    {atTarget : σ → Bool} {n bound : Nat} {s s_hit : σ}
    (h : FirstHitIn step atTarget n s s_hit) (hle : n ≤ bound) :
    runToTarget step atTarget bound s = .reached s_hit := by
  cases h with
  | here hs ht =>
    unfold runToTarget; rw [hs]
    exact runUntilTarget_of_firstHitIn (.here hs ht) _ hs bound hle
  | later hs hnt hrest =>
    unfold runToTarget; rw [hs]
    exact runUntilTarget_of_firstHitIn (.later hs hnt hrest) _ hs bound hle

/-! ## 3. Structural `[lo, hi)` range loops and the live `Anneal.MirLoops.forRangeUp` -/

/-- Structural range fold over `[i, hi)` indexed by the remaining trip count. -/
def forRangeUpAux {α : Type} (lo hi : Nat)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) :
    (i rem : Nat) → lo ≤ i → i + rem = hi → α → α
  | _, 0, _, _, acc => acc
  | i, rem + 1, hlo, hsum, acc =>
    forRangeUpAux lo hi step (i + 1) rem (Nat.le_succ_of_le hlo) (by omega)
      (step i hlo (by omega) acc)

/-- Structurally recursive `for i in lo..hi` fold (kernel-reducible, unlike the
well-founded live definition). -/
def forRangeUp {α : Type} (lo hi : Nat) (init : α)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) : α :=
  if h : lo ≤ hi then
    forRangeUpAux lo hi step lo (hi - lo) (Nat.le_refl lo) (by omega) init
  else
    init

theorem forRangeUpAux_eq_live {α : Type} (lo hi : Nat)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) :
    ∀ (i rem : Nat) (hlo : lo ≤ i) (hsum : i + rem = hi) (acc : α),
      forRangeUpAux lo hi step i rem hlo hsum acc =
        Anneal.MirLoops.forRangeUp i hi acc
          (fun j hj hlt a => step j (Nat.le_trans hlo hj) hlt a)
  | i, 0, hlo, hsum, acc => by
    rw [Anneal.MirLoops.forRangeUp_eq_init_of_ge _ _ _ _ (by omega)]
    rfl
  | i, rem + 1, hlo, hsum, acc => by
    rw [Anneal.MirLoops.forRangeUp_step_of_lt _ _ _ _ (by omega)]
    exact forRangeUpAux_eq_live lo hi step (i + 1) rem _ _ _

/-- **Bridge to the live `Anneal.MirLoops.forRangeUp`**: the structural fold is
extensionally identical to the live well-founded definition. -/
theorem forRangeUp_eq_live {α : Type} (lo hi : Nat) (init : α)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) :
    forRangeUp lo hi init step = Anneal.MirLoops.forRangeUp lo hi init step := by
  unfold forRangeUp
  split
  · next hle => exact forRangeUpAux_eq_live lo hi step lo (hi - lo) _ _ init
  · next hgt => rw [Anneal.MirLoops.forRangeUp_eq_init_of_ge _ _ _ _ (by omega)]

theorem forRangeUpAux_induction {α : Type} (lo hi : Nat)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) (inv : Nat → α → Prop) :
    ∀ (i rem : Nat) (hlo : lo ≤ i) (hsum : i + rem = hi) (acc : α),
      inv i acc →
      (∀ j (hjlo : lo ≤ j) (hjlt : j < hi) a, inv j a → inv (j + 1) (step j hjlo hjlt a)) →
      inv hi (forRangeUpAux lo hi step i rem hlo hsum acc)
  | i, 0, _, hsum, acc, hinv, _ => by
    have : i = hi := by omega
    subst this
    exact hinv
  | i, rem + 1, hlo, hsum, acc, hinv, hstep =>
    forRangeUpAux_induction lo hi step inv (i + 1) rem _ _ _ (hstep i hlo (by omega) acc hinv) hstep

/-- **Structural `[lo, hi)` loop induction**. -/
theorem forRangeUp_induction {α : Type} (lo hi : Nat) (init : α)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) (inv : Nat → α → Prop)
    (hle : lo ≤ hi) (hinit : inv lo init)
    (hstep : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a, inv i a → inv (i + 1) (step i hlo hlt a)) :
    inv hi (forRangeUp lo hi init step) := by
  unfold forRangeUp
  simp only [hle, ↓reduceDIte]
  exact forRangeUpAux_induction lo hi step inv lo (hi - lo) _ _ init hinit hstep

/-- Range induction transported to the live `Anneal.MirLoops.forRangeUp`
through `forRangeUp_eq_live` (agrees with the live `forRangeUp_induction`). -/
theorem live_forRangeUp_induction {α : Type} (lo hi : Nat) (init : α)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) (inv : Nat → α → Prop)
    (hle : lo ≤ hi) (hinit : inv lo init)
    (hstep : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a, inv i a → inv (i + 1) (step i hlo hlt a)) :
    inv hi (Anneal.MirLoops.forRangeUp lo hi init step) := by
  rw [← forRangeUp_eq_live]
  exact forRangeUp_induction lo hi init step inv hle hinit hstep

theorem wpConverges_forRangeUpAux {σ out α : Type} (stepOp : σ → Step σ out)
    (lo hi : Nat) (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (inv : Nat → α → σ → Prop) (post : out → Prop) :
    ∀ (i rem : Nat) (hlo : lo ≤ i) (hsum : i + rem = hi) (a : α) (s : σ),
      inv i a s →
      (∀ j (hjlo : lo ≤ j) (hjlt : j < hi) acc s₀,
        inv j acc s₀ → StepsTo stepOp s₀ (inv (j + 1) (f j hjlo hjlt acc))) →
      (∀ s_exit, inv hi (forRangeUpAux lo hi f i rem hlo hsum a) s_exit →
        WpConverges stepOp s_exit post) →
      WpConverges stepOp s post
  | i, 0, hlo, hsum, a, s, hinv, _, hexit => by
    have hi_eq : i = hi := by omega
    subst hi_eq
    exact hexit s hinv
  | i, rem + 1, hlo, hsum, a, s, hinv, hiter, hexit => by
    have hlt : i < hi := by omega
    exact StepsTo.bind_wp (hiter i hlo hlt a s hinv) (fun s₁ hinv₁ =>
      wpConverges_forRangeUpAux stepOp lo hi f inv post (i + 1) rem _ _
        (f i hlo hlt a) s₁ hinv₁ hiter hexit)

/-- **Fuel-free range-loop rule**: per-iteration segment reachability plus an
exit obligation imply convergence, with no step count or fuel numeral. -/
theorem wpConverges_forRangeUp {σ out α : Type} (stepOp : σ → Step σ out)
    (lo hi : Nat) (init : α) (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (inv : Nat → α → σ → Prop) (s₀ : σ) (post : out → Prop)
    (hle : lo ≤ hi) (hinit : inv lo init s₀)
    (hiter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a s,
      inv i a s → StepsTo stepOp s (inv (i + 1) (f i hlo hlt a)))
    (hexit : ∀ s_exit, inv hi (forRangeUp lo hi init f) s_exit → WpConverges stepOp s_exit post) :
    WpConverges stepOp s₀ post := by
  unfold forRangeUp at hexit
  simp only [hle, ↓reduceDIte] at hexit
  exact wpConverges_forRangeUpAux stepOp lo hi f inv post lo (hi - lo) _ _ init s₀ hinit hiter hexit

/-! ## 4. A concrete multi-block CFG language, `countUp`, and self-loops -/

/-- One instruction per basic block (block-granular steps). -/
inductive Instr where
  /-- `env[dst] := c; goto next`. -/
  | setConst (dst c next : Nat)
  /-- `env[dst] := env[src] + c; goto next`. -/
  | addConst (dst src c next : Nat)
  /-- `if env[lhs] < env[rhs] then goto thenBB else goto elseBB`. -/
  | branchLt (lhs rhs thenBB elseBB : Nat)
  /-- Self-loop header: `if env[ctr] < env[bnd] then (env[ctr] += 1; goto loopBB) else goto exitBB`. -/
  | incBranchLt (ctr bnd loopBB exitBB : Nat)
  /-- `goto next`. -/
  | goto (next : Nat)
  /-- `return env[slot]`. -/
  | ret (slot : Nat)
  deriving DecidableEq, Repr

/-- Toy CFG machine state: current block and a slot environment. -/
structure CfgState where
  bb : Nat
  env : List Nat
  deriving DecidableEq, Repr

/-- Honest concrete block semantics: out-of-range blocks, slots, and reads fault. -/
def stepCfg (cfg : List Instr) (s : CfgState) : Step CfgState Nat :=
  match cfg[s.bb]? with
  | none => .fault
  | some (.setConst dst c next) =>
    if dst < s.env.length then .cont ⟨next, s.env.set dst c⟩ else .fault
  | some (.addConst dst src c next) =>
    match s.env[src]? with
    | some v => if dst < s.env.length then .cont ⟨next, s.env.set dst (v + c)⟩ else .fault
    | none => .fault
  | some (.branchLt lhs rhs thenBB elseBB) =>
    match s.env[lhs]?, s.env[rhs]? with
    | some a, some b => .cont ⟨if a < b then thenBB else elseBB, s.env⟩
    | _, _ => .fault
  | some (.incBranchLt ctr bnd loopBB exitBB) =>
    match s.env[ctr]?, s.env[bnd]? with
    | some i, some n =>
      if i < n then .cont ⟨loopBB, s.env.set ctr (i + 1)⟩ else .cont ⟨exitBB, s.env⟩
    | _, _ => .fault
  | some (.goto next) => .cont ⟨next, s.env⟩
  | some (.ret slot) =>
    match s.env[slot]? with
    | some v => .done v
    | none => .fault

/-- **`runCfgToBlock`**: header-targeted block stepping whose internal ceiling is
derived from the CFG (`cfg.length`, an upper bound on the length of any
header-free acyclic segment), so call sites contain no step numerals. -/
def runCfgToBlock (cfg : List Instr) (target : Nat) (s : CfgState) :
    TargetOutcome CfgState Nat :=
  runToTarget (stepCfg cfg) (fun s' => s'.bb == target) cfg.length s

theorem runCfgToBlock_reached_bb {cfg : List Instr} {target : Nat} {s s' : CfgState}
    (h : runCfgToBlock cfg target s = .reached s') : s'.bb = target := by
  have ht := runToTarget_reached_atTarget h
  exact beq_iff_eq.mp ht

/-- **Target arrival soundness** for `runCfgToBlock`. -/
theorem stepsTo_of_runCfgToBlock_reached {cfg : List Instr} {target : Nat}
    {s s' : CfgState} (h : runCfgToBlock cfg target s = .reached s') :
    StepsTo (stepCfg cfg) s (· = s') :=
  stepsTo_of_runToTarget_reached h

/-- **Halting soundness** for `runCfgToBlock`. -/
theorem wpConverges_of_runCfgToBlock_halted {cfg : List Instr} {target : Nat}
    {s : CfgState} {v : Nat} {post : Nat → Prop}
    (h : runCfgToBlock cfg target s = .halted v) (hp : post v) :
    WpConverges (stepCfg cfg) s post :=
  wpConverges_of_runToTarget_halted h hp

/-- **Stuck soundness** for `runCfgToBlock`. -/
theorem not_wpConverges_of_runCfgToBlock_stuck {cfg : List Instr} {target : Nat}
    {s : CfgState} {post : Nat → Prop}
    (h : runCfgToBlock cfg target s = .stuck) : ¬ WpConverges (stepCfg cfg) s post :=
  not_wpConverges_of_runToTarget_stuck h

/-- Multi-block `countUp(n)` with a symbolic accumulator (slots `[n, i, acc]`):
```
bb0: i := 0;             goto bb1
bb1: if i < n then bb2 else bb4      -- loop header (re-entered via bb3)
bb2: acc := acc + 1;     goto bb3
bb3: i := i + 1;         goto bb1    -- back-edge
bb4: return acc
```
-/
def countUpCfg : List Instr :=
  [.setConst 1 0 1, .branchLt 1 0 2 4, .addConst 2 2 1 3, .addConst 1 1 1 1, .ret 2]

/-- Entry state of `countUp(n)` with accumulator `x` and arbitrary junk in `i`. -/
def countUpInit (n x junk : Nat) : CfgState := ⟨0, [n, junk, x]⟩

/-- Loop-header state of `countUp`. -/
def countUpHeader (n i acc : Nat) : CfgState := ⟨1, [n, i, acc]⟩

theorem countUp_entry_step (n x junk : Nat) :
    stepCfg countUpCfg (countUpInit n x junk) = .cont (countUpHeader n 0 x) := rfl

theorem countUp_header_exit_steps (n acc : Nat) :
    stepCfg countUpCfg (countUpHeader n n acc) = .cont ⟨4, [n, n, acc]⟩ ∧
      stepCfg countUpCfg ⟨4, [n, n, acc]⟩ = .done acc := by
  refine ⟨?_, rfl⟩
  simp [stepCfg, countUpCfg, countUpHeader]

theorem countUp_header_iter_steps (n i acc : Nat) (hlt : i < n) :
    stepCfg countUpCfg (countUpHeader n i acc) = .cont ⟨2, [n, i, acc]⟩ ∧
      stepCfg countUpCfg ⟨2, [n, i, acc]⟩ = .cont ⟨3, [n, i, acc + 1]⟩ ∧
      stepCfg countUpCfg ⟨3, [n, i, acc + 1]⟩ = .cont (countUpHeader n (i + 1) (acc + 1)) := by
  refine ⟨?_, rfl, rfl⟩
  simp [stepCfg, countUpCfg, countUpHeader, hlt]

/-- Exact fuel characterization of `countUp` from its header: with `d = n - i`
remaining iterations, `3 * d + 2` steps are necessary and sufficient. -/
theorem evalFuel_countUp_header :
    ∀ (d n i acc k : Nat), i + d = n →
      evalFuel (stepCfg countUpCfg) k (countUpHeader n i acc) =
        if 3 * d + 2 ≤ k then .halted (acc + d) else .outOfFuel
  | 0, n, i, acc, k, hd => by
    have hi : i = n := by omega
    subst hi
    obtain ⟨h1, h2⟩ := countUp_header_exit_steps i acc
    match k with
    | 0 => rfl
    | 1 => simp [evalFuel, h1]
    | k + 2 =>
      simp only [evalFuel, h1, h2]
      have hk : 3 * 0 + 2 ≤ k + 2 := by omega
      simp only [hk, ↓reduceIte, Nat.add_zero]
  | d + 1, n, i, acc, k, hd => by
    have hlt : i < n := by omega
    obtain ⟨h1, h2, h3⟩ := countUp_header_iter_steps n i acc hlt
    have ih := evalFuel_countUp_header d n (i + 1) (acc + 1)
    match k with
    | 0 => rfl
    | 1 => simp [evalFuel, h1]
    | 2 => simp [evalFuel, h1, h2]
    | k + 3 =>
      simp only [evalFuel, h1, h2, h3]
      rw [ih k (by omega)]
      by_cases hk : 3 * d + 2 ≤ k
      · have hk' : 3 * (d + 1) + 2 ≤ k + 3 := by omega
        simp only [hk, hk', ↓reduceIte, Nat.add_assoc, Nat.add_comm 1 d]
      · have hk' : ¬ 3 * (d + 1) + 2 ≤ k + 3 := by omega
        simp only [hk, hk', ↓reduceIte]

/-- Naive explicit-fuel verification of `countUp(n)` needs exactly `3 * n + 3`
steps (the numeral grows with `n`). -/
theorem countUp_halts_with_fuel (n x junk : Nat) :
    evalFuel (stepCfg countUpCfg) (3 * n + 3) (countUpInit n x junk) = .halted (x + n) := by
  have h := evalFuel_countUp_header n n 0 x (3 * n + 2) (by omega)
  simp only [Nat.le_refl, ↓reduceIte] at h
  show evalFuel (stepCfg countUpCfg) ((3 * n + 2) + 1) (countUpInit n x junk) = _
  simp only [evalFuel, countUp_entry_step]
  exact h

/-- **Impossibility of a uniform fuel constant**: for the multi-block
`countUp(n)` CFG, no fixed `F : Nat` halts the program for every bound `n`. -/
theorem no_uniform_fuel_countUp :
    ¬ ∃ F : Nat, ∀ n : Nat, ∃ v, evalFuel (stepCfg countUpCfg) F (countUpInit n 0 0) = .halted v := by
  rintro ⟨F, hF⟩
  obtain ⟨v, hv⟩ := hF F
  match F, hv with
  | 0, hv => cases hv
  | F + 1, hv =>
    simp only [evalFuel, countUp_entry_step] at hv
    have hlt : ¬ 3 * (F + 1) + 2 ≤ F := by omega
    rw [evalFuel_countUp_header (F + 1) (F + 1) 0 0 F (by omega)] at hv
    simp only [hlt, ↓reduceIte] at hv
    cases hv

/-- One loop iteration from the re-entrant header `bb1` back to `bb1`: the
stepper stops at the first re-entry (three block steps), never overshooting. -/
theorem runCfgToBlock_countUp_iter (n i acc : Nat) (hlt : i < n) :
    runCfgToBlock countUpCfg 1 (countUpHeader n i acc) =
      .reached (countUpHeader n (i + 1) (acc + 1)) := by
  obtain ⟨h1, _, _⟩ := countUp_header_iter_steps n i acc hlt
  simp only [runCfgToBlock, runToTarget, h1]
  rfl

/-- Exit from the header halts with the accumulator. -/
theorem runCfgToBlock_countUp_exit (n acc : Nat) :
    runCfgToBlock countUpCfg 1 (countUpHeader n n acc) = .halted acc := by
  obtain ⟨h1, _⟩ := countUp_header_exit_steps n acc
  simp only [runCfgToBlock, runToTarget, h1]
  rfl

/-- The entry block reaches the loop header in one step. -/
theorem runCfgToBlock_countUp_entry (n x junk : Nat) :
    runCfgToBlock countUpCfg 1 (countUpInit n x junk) = .reached (countUpHeader n 0 x) := rfl

/-- **Fuel-free total correctness of `countUp(n)` for every symbolic `n`** (and
symbolic accumulator `x`): the statement contains no fuel numeral, and the proof
composes `runCfgToBlock` segment soundness with `wpConverges_forRangeUp`. -/
theorem countUp_wpConverges_all_n (n x junk : Nat) :
    WpConverges (stepCfg countUpCfg) (countUpInit n x junk) (fun v => v = x + n) := by
  have hfold : forRangeUp 0 n x (fun _ _ _ acc => acc + 1) = x + n :=
    forRangeUp_induction 0 n x (fun _ _ _ acc => acc + 1) (fun i acc => acc = x + i)
      (Nat.zero_le n) rfl (fun _ _ _ _ h => by rw [h]; rfl)
  refine StepsTo.bind_wp (stepsTo_of_runCfgToBlock_reached (runCfgToBlock_countUp_entry n x junk))
    (fun s₁ hs₁ => ?_)
  subst hs₁
  refine wpConverges_forRangeUp (stepCfg countUpCfg) 0 n x (fun _ _ _ acc => acc + 1)
    (fun i acc s => s = countUpHeader n i acc) (countUpHeader n 0 x) (fun v => v = x + n)
    (Nat.zero_le n) rfl ?_ ?_
  · intro i _ hlt a s hs
    subst hs
    exact (stepsTo_of_runCfgToBlock_reached (runCfgToBlock_countUp_iter n i a hlt)).mono
      (fun _ h => h)
  · intro s_exit hs
    rw [hfold] at hs
    subst hs
    exact wpConverges_of_runCfgToBlock_halted (runCfgToBlock_countUp_exit n (x + n)) rfl

/-- Single-block self-loop (slots `[n, i]`): `bb0` re-enters itself directly. -/
def selfLoopCfg : List Instr := [.incBranchLt 1 0 0 1, .ret 1]

/-- **No overshoot on self-loops**: from the self-looping header, the stepper
stops after exactly one iteration even though `bb0` is re-entered immediately. -/
theorem selfLoop_iter_step (n i : Nat) (hlt : i < n) :
    stepCfg selfLoopCfg ⟨0, [n, i]⟩ = .cont ⟨0, [n, i + 1]⟩ := by
  simp [stepCfg, selfLoopCfg, hlt]

theorem selfLoop_exit_steps (n : Nat) :
    stepCfg selfLoopCfg ⟨0, [n, n]⟩ = .cont ⟨1, [n, n]⟩ ∧
      stepCfg selfLoopCfg ⟨1, [n, n]⟩ = .done n := by
  refine ⟨?_, rfl⟩
  simp [stepCfg, selfLoopCfg]

theorem runCfgToBlock_selfLoop_no_overshoot (n i : Nat) (hlt : i < n) :
    runCfgToBlock selfLoopCfg 0 ⟨0, [n, i]⟩ = .reached ⟨0, [n, i + 1]⟩ := by
  simp only [runCfgToBlock, runToTarget, selfLoop_iter_step n i hlt]
  rfl

/-- The first-hit characterization pins the self-loop successor uniquely. -/
theorem selfLoop_firstHit_unique (n i : Nat) (hlt : i < n) {m : Nat} {s' : CfgState}
    (h : FirstHitIn (stepCfg selfLoopCfg) (fun s => s.bb == 0) m ⟨0, [n, i]⟩ s') :
    s' = ⟨0, [n, i + 1]⟩ ∧ m = 0 := by
  exact FirstHitIn.unique h (.here (selfLoop_iter_step n i hlt) rfl)

/-- Fuel-free convergence of the self-loop for every symbolic bound. -/
theorem selfLoop_wpConverges_all_n (n : Nat) :
    WpConverges (stepCfg selfLoopCfg) ⟨0, [n, 0]⟩ (fun v => v = n) := by
  refine wpConverges_forRangeUp (stepCfg selfLoopCfg) 0 n () (fun _ _ _ u => u)
    (fun i _ s => s = ⟨0, [n, i]⟩) ⟨0, [n, 0]⟩ (fun v => v = n) (Nat.zero_le n) rfl ?_ ?_
  · intro i _ hlt _ s hs
    subst hs
    exact (stepsTo_of_runCfgToBlock_reached (runCfgToBlock_selfLoop_no_overshoot n i hlt)).mono
      (fun _ h => h)
  · intro s_exit hs
    subst hs
    have hexit : runCfgToBlock selfLoopCfg 0 ⟨0, [n, n]⟩ = .halted n := by
      simp only [runCfgToBlock, runToTarget, (selfLoop_exit_steps n).1]
      rfl
    exact wpConverges_of_runCfgToBlock_halted hexit rfl

/-- `.stuck` is reported for a jump to a missing block and soundly refutes
convergence. -/
theorem runCfgToBlock_stuck_example :
    runCfgToBlock [.goto 7] 0 ⟨0, []⟩ = .stuck ∧
      ¬ WpConverges (stepCfg [.goto 7]) ⟨0, []⟩ (fun _ => True) :=
  ⟨rfl, not_wpConverges_of_runCfgToBlock_stuck (target := 0) rfl⟩

/-- `.outOfFuel` is inconclusive and ceiling-sensitive: a zero ceiling stops a
three-step `countUp` iteration early, while a ceiling of two reaches the header. -/
theorem runToTarget_outOfFuel_vs_reached (n i acc : Nat) (hlt : i < n) :
    runToTarget (stepCfg countUpCfg) (fun s => s.bb == 1) 0 (countUpHeader n i acc) = .outOfFuel ∧
      runToTarget (stepCfg countUpCfg) (fun s => s.bb == 1) 2 (countUpHeader n i acc) =
        .reached (countUpHeader n (i + 1) (acc + 1)) := by
  obtain ⟨h1, h2, h3⟩ := countUp_header_iter_steps n i acc hlt
  refine ⟨?_, ?_⟩
  · simp only [runToTarget, h1, runUntilTarget]; rfl
  · simp only [runToTarget, h1, runUntilTarget, h2, h3]; rfl

/-! ## 5. Bridges to the live MIR fuel-free predicates (`Anneal.MirFuelFree`) -/

section LiveMirBridge

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-- Embedding of the live trusted step function `stepMirFn` into the generic
machine.  Silent transitions continue and root returns halt; every other node
(visible events, external calls, faults, and `.tau` into halted or faulted
states) is mapped conservatively to `.fault`, so only proofs about the silent
call-free fragment transfer, and they transfer soundly. -/
def mirStep (body : CapturedMir) (s : MachineState) : Step MachineState MirOutcome :=
  match stepMirFn body s with
  | .tau (.running s') => .cont s'
  | .ret out => .done out
  | _ => .fault

theorem stepMirFn_of_mirStep_cont {body : CapturedMir} {s s' : MachineState}
    (h : mirStep body s = .cont s') : stepMirFn body s = .tau (.running s') := by
  unfold mirStep at h
  split at h
  · rename_i s'' heq
    cases h
    exact heq
  · cases h
  · cases h

theorem stepMirFn_of_mirStep_done {body : CapturedMir} {s : MachineState} {out : MirOutcome}
    (h : mirStep body s = .done out) : stepMirFn body s = .ret out := by
  unfold mirStep at h
  split at h
  · cases h
  · rename_i out' heq
    cases h
    exact heq
  · cases h

/-- **Bridge to the live `Anneal.MirFuelFree.MirStepsConverges`**: generic
segment reachability over `mirStep` is live fuel-free reachability. -/
theorem mirStepsConverges_of_stepsTo {body : CapturedMir} {s : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h : StepsTo (mirStep body) s mid) :
    Anneal.MirFuelFree.MirStepsConverges body s mid post := by
  induction h with
  | refl hm => exact Anneal.MirFuelFree.MirStepsConverges.refl hm
  | step hs _ ih =>
    exact Anneal.MirFuelFree.MirStepsConverges.step_tau (stepMirFn_of_mirStep_cont hs) ih

theorem mirWpConverges_of_evalFuel {body : CapturedMir} {post : MirOutcome → Prop} :
    ∀ (k : Nat) (s : MachineState) (v : MirOutcome),
      evalFuel (mirStep body) k s = .halted v → post v →
      Anneal.MirFuelFree.MirWpConverges body s post
  | 0, _, _, h, _ => by cases h
  | k + 1, s, v, h, hp => by
    unfold evalFuel at h
    cases hs : mirStep body s with
    | cont s' =>
      rw [hs] at h
      exact Anneal.MirFuelFree.MirWpConverges.step_tau (stepMirFn_of_mirStep_cont hs)
        (mirWpConverges_of_evalFuel k s' v h hp)
    | done out =>
      rw [hs] at h
      cases h
      exact Anneal.MirFuelFree.MirWpConverges.ret_of_step (stepMirFn_of_mirStep_done hs) hp
    | fault =>
      rw [hs] at h
      cases h

/-- **Bridge to the live `Anneal.MirFuelFree.MirWpConverges`**. -/
theorem mirWpConverges_of_wpConverges {body : CapturedMir} {s : MachineState}
    {post : MirOutcome → Prop} (h : WpConverges (mirStep body) s post) :
    Anneal.MirFuelFree.MirWpConverges body s post := by
  obtain ⟨k, v, hk, hp⟩ := h
  exact mirWpConverges_of_evalFuel k s v hk hp

/-- Mixed composition: a generic segment followed by a live continuation
(through the live `MirWpConverges.bind`). -/
theorem mirWpConverges_of_stepsTo_bind {body : CapturedMir} {s : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h₁ : StepsTo (mirStep body) s mid)
    (h₂ : ∀ s', mid s' → Anneal.MirFuelFree.MirWpConverges body s' post) :
    Anneal.MirFuelFree.MirWpConverges body s post :=
  Anneal.MirFuelFree.MirWpConverges.bind (mirStepsConverges_of_stepsTo h₁) h₂

/-- Ceiling for live header-targeted stepping: the total number of statements
and terminators of the body (one live step each). -/
def mirSegmentBound (body : CapturedMir) : Nat :=
  body.basicBlocks.foldl (fun acc bb => acc + bb.statements.length + 1) 0

/-- Header-targeted stepping over live MIR: stops at the first statement of
basic block `target`. -/
def runMirToBlock (body : CapturedMir) (target : BasicBlockIdx) (s : MachineState) :
    TargetOutcome MachineState MirOutcome :=
  runToTarget (mirStep body)
    (fun ms => ms.frame.blockIdx == target && ms.frame.stmtIdx == 0) (mirSegmentBound body) s

theorem mirStepsConverges_of_runMirToBlock_reached {body : CapturedMir}
    {target : BasicBlockIdx} {s s' : MachineState} {post : MirOutcome → Prop}
    (h : runMirToBlock body target s = .reached s') :
    Anneal.MirFuelFree.MirStepsConverges body s (· = s') post :=
  mirStepsConverges_of_stepsTo (stepsTo_of_runToTarget_reached h)

theorem mirWpConverges_of_runMirToBlock_halted {body : CapturedMir}
    {target : BasicBlockIdx} {s : MachineState} {v : MirOutcome} {post : MirOutcome → Prop}
    (h : runMirToBlock body target s = .halted v) (hp : post v) :
    Anneal.MirFuelFree.MirWpConverges body s post :=
  mirWpConverges_of_wpConverges (wpConverges_of_runToTarget_halted h hp)

/-- **Fuel-free range-loop rule for live MIR**, stated with the live
`Anneal.MirLoops.forRangeUp`. -/
theorem mirWpConverges_forRangeUp {α : Type} (body : CapturedMir) (lo hi : Nat) (init : α)
    (f : (i : Nat) → lo ≤ i → i < hi → α → α) (inv : Nat → α → MachineState → Prop)
    (s₀ : MachineState) (post : MirOutcome → Prop) (hle : lo ≤ hi) (hinit : inv lo init s₀)
    (hiter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a s,
      inv i a s → StepsTo (mirStep body) s (inv (i + 1) (f i hlo hlt a)))
    (hexit : ∀ s_exit, inv hi (Anneal.MirLoops.forRangeUp lo hi init f) s_exit →
      WpConverges (mirStep body) s_exit post) :
    Anneal.MirFuelFree.MirWpConverges body s₀ post := by
  refine mirWpConverges_of_wpConverges
    (wpConverges_forRangeUp (mirStep body) lo hi init f inv s₀ post hle hinit hiter ?_)
  intro s_exit h
  rw [forRangeUp_eq_live] at h
  exact hexit s_exit h

end LiveMirBridge

/-! ## 6. Toy CFG shapes and the live `Anneal.PureMirExec.MirFragment` lattice -/

section FragmentBridge

open Trusted.Rustc.V2026_06_01.MirAst
open Anneal.PureMirExec

/-- Successor blocks of a toy instruction, in the live `terminatorTargets` order. -/
def Instr.targets : Instr → List Nat
  | .setConst _ _ next => [next]
  | .addConst _ _ _ next => [next]
  | .branchLt _ _ thenBB elseBB => [elseBB, thenBB]
  | .incBranchLt _ _ loopBB exitBB => [exitBB, loopBB]
  | .goto next => [next]
  | .ret _ => []

def instrBackedgeAux : Nat → List Instr → Bool
  | _, [] => false
  | i, ins :: rest =>
    ins.targets.any (fun succ => decide (succ ≤ i)) || instrBackedgeAux (i + 1) rest

/-- Index-order back-edge detector for toy CFGs (mirrors the live `hasCfgBackedge`). -/
def hasInstrBackedge (cfg : List Instr) : Bool := instrBackedgeAux 0 cfg

def shapeSpan : String := "fuel-free-proto"

def shapeU64Ty : Ty := { kind := .uint .u64, layoutIdx := 0 }

def shapeLocal (i : Nat) : Place := { local_ := i, projection := [] }

def shapeConst (c : Nat) : Operand :=
  .constant { ty := shapeU64Ty, val := .scalar (.int ⟨c, 8⟩) }

def shapeBranch (lhs rhs thenBB elseBB : Nat) : BasicBlockData :=
  { statements :=
      [{ kind := .assign (shapeLocal 0) (.binaryOp .lt (.copy (shapeLocal lhs)) (.copy (shapeLocal rhs))),
         span := shapeSpan }],
    terminator :=
      { kind := .switchInt (.copy (shapeLocal 0)) { branches := [(0, elseBB)], otherwise := thenBB },
        span := shapeSpan },
    isCleanup := false }

/-- Shape translation of a toy instruction to a live basic block: identical
successor structure and pure statement kinds.  This is a *shape* translation
used only for CFG-structure classification, not a semantic compilation. -/
def Instr.toMirBlock : Instr → BasicBlockData
  | .setConst dst c next =>
    { statements := [{ kind := .assign (shapeLocal dst) (.use (shapeConst c)), span := shapeSpan }],
      terminator := { kind := .goto next, span := shapeSpan }, isCleanup := false }
  | .addConst dst src c next =>
    { statements :=
        [{ kind := .assign (shapeLocal dst) (.binaryOp .add (.copy (shapeLocal src)) (shapeConst c)),
           span := shapeSpan }],
      terminator := { kind := .goto next, span := shapeSpan }, isCleanup := false }
  | .branchLt lhs rhs thenBB elseBB => shapeBranch lhs rhs thenBB elseBB
  | .incBranchLt ctr bnd loopBB exitBB => shapeBranch ctr bnd loopBB exitBB
  | .goto next =>
    { statements := [], terminator := { kind := .goto next, span := shapeSpan }, isCleanup := false }
  | .ret _ =>
    { statements := [], terminator := { kind := .return_, span := shapeSpan }, isCleanup := false }

/-- Live `CapturedMir` with the toy CFG's block shapes. -/
def toMirShape (cfg : List Instr) : CapturedMir :=
  { pureAdtMultiBlockBody with basicBlocks := cfg.map Instr.toMirBlock }

theorem blockTargets_toMirBlock (ins : Instr) : blockTargets ins.toMirBlock = ins.targets := by
  cases ins <;> rfl

theorem hasCfgBackedgeAux_map_toMirBlock :
    ∀ (i : Nat) (cfg : List Instr),
      hasCfgBackedgeAux i (cfg.map Instr.toMirBlock) = instrBackedgeAux i cfg
  | _, [] => rfl
  | i, ins :: rest => by
    simp only [List.map_cons, hasCfgBackedgeAux, instrBackedgeAux, hasBlockBackedge,
      blockTargets_toMirBlock, hasCfgBackedgeAux_map_toMirBlock (i + 1) rest]

/-- The live back-edge analysis of a translated shape equals the toy analysis. -/
theorem hasCfgBackedge_toMirShape (cfg : List Instr) :
    hasCfgBackedge (toMirShape cfg) = hasInstrBackedge cfg :=
  hasCfgBackedgeAux_map_toMirBlock 0 cfg

theorem checkBlockFragment_toMirBlock (f : MirFragment) (ins : Instr) :
    checkBlockFragment f ins.toMirBlock = true := by
  cases ins <;> rfl

theorem all_checkBlockFragment_toMirShape (f : MirFragment) (cfg : List Instr) :
    (cfg.map Instr.toMirBlock).all (checkBlockFragment f) = true := by
  induction cfg with
  | nil => rfl
  | cons ins rest ih =>
    simp only [List.map_cons, List.all_cons, checkBlockFragment_toMirBlock, ih, Bool.and_self]

/-- **`MirFragment` characterization**: the live minimal-fragment classifier
puts a toy CFG shape in `.pureBoundedLoop` exactly when it has a back-edge and
in `.pureLoopFree` otherwise; loop lifting (Pillar 1) therefore targets the two
lowest lattice levels, below `.treeBorrowsLocal` (Pillar 4). -/
theorem inferMinFragment_toMirShape (cfg : List Instr) :
    inferMinFragment (toMirShape cfg) =
      if hasInstrBackedge cfg then .pureBoundedLoop else .pureLoopFree := by
  have hall := all_checkBlockFragment_toMirShape
  have hbe := hasCfgBackedge_toMirShape cfg
  unfold inferMinFragment checkBodyFragment
  cases hb : hasInstrBackedge cfg with
  | true =>
    simp only [toMirShape] at hbe ⊢
    simp only [hall, hbe, hb, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  | false =>
    simp only [toMirShape] at hbe ⊢
    simp only [hall, hbe, hb, Bool.not_false, Bool.and_self, ↓reduceIte, Bool.false_eq_true]

theorem inferMinFragment_countUp :
    inferMinFragment (toMirShape countUpCfg) = .pureBoundedLoop := by
  rw [inferMinFragment_toMirShape]
  rfl

theorem inferMinFragment_selfLoop :
    inferMinFragment (toMirShape selfLoopCfg) = .pureBoundedLoop := by
  rw [inferMinFragment_toMirShape]
  rfl

/-- A loop-free straight-line CFG. -/
def straightLineCfg : List Instr := [.setConst 1 0 1, .addConst 1 1 2 2, .ret 1]

theorem inferMinFragment_straightLine :
    inferMinFragment (toMirShape straightLineCfg) = .pureLoopFree := by
  rw [inferMinFragment_toMirShape]
  rfl

/-- A straight-line shape whose first block takes `&mut _2` (a local borrow). -/
def refShapeBody : CapturedMir :=
  { toMirShape straightLineCfg with
    basicBlocks :=
      { statements :=
          [{ kind := .assign (shapeLocal 1) (.ref (.mut false) (shapeLocal 2)), span := shapeSpan }],
        terminator := { kind := .goto 1, span := shapeSpan }, isCleanup := false } ::
        (straightLineCfg.drop 1).map Instr.toMirBlock }

/-- Taking a local `&mut` borrow lifts the shape to `.treeBorrowsLocal`, the
Tree Borrows fragment targeted by Pillar 4. -/
theorem inferMinFragment_refShape : inferMinFragment refShapeBody = .treeBorrowsLocal := rfl

/-- The three characterized levels are strictly ordered in the live lattice. -/
theorem fragment_levels_strict :
    MirFragment.pureLoopFree < .pureBoundedLoop ∧
      MirFragment.pureBoundedLoop < .treeBorrowsLocal :=
  ⟨by decide, by decide⟩

end FragmentBridge

/-! ## 7. `forcePureEnv`: flat slot-list normalization -/

section ForcePureEnv

/-- Projection of the `n`-slot prefix of a frame, padding missing slots with `d`. -/
def forcePureEnvD {α : Type} (d : α) : Nat → List α → List α
  | 0, _ => []
  | n + 1, env => env.headD d :: forcePureEnvD d n env.tail

/-- **`forcePureEnv`**: projection-based normalization of the `n`-slot prefix. -/
def forcePureEnv {α : Type} [Inhabited α] (n : Nat) (env : List α) : List α :=
  forcePureEnvD default n env

theorem length_forcePureEnvD {α : Type} (d : α) :
    ∀ (n : Nat) (env : List α), (forcePureEnvD d n env).length = n
  | 0, _ => rfl
  | n + 1, env => by
    simp only [forcePureEnvD, List.length_cons, length_forcePureEnvD d n env.tail]

theorem forcePureEnvD_eq_self {α : Type} (d : α) :
    ∀ (n : Nat) (env : List α), env.length = n → forcePureEnvD d n env = env
  | 0, [], _ => rfl
  | 0, _ :: _, h => absurd h (Nat.succ_ne_zero _)
  | n + 1, [], h => absurd h.symm (Nat.succ_ne_zero n)
  | n + 1, x :: xs, h => by
    have h' : xs.length = n := Nat.succ.inj h
    simp only [forcePureEnvD, List.headD_cons, List.tail_cons, forcePureEnvD_eq_self d n xs h']

/-- **Exact identity on well-sized frames**. -/
theorem forcePureEnv_eq_self {α : Type} [Inhabited α] (n : Nat) (env : List α)
    (h : env.length = n) : forcePureEnv n env = env :=
  forcePureEnvD_eq_self default n env h

theorem getD_zero_eq_headD {α : Type} (env : List α) (d : α) : env.getD 0 d = env.headD d := by
  cases env <;> rfl

theorem getD_succ_eq_tail {α : Type} (env : List α) (i : Nat) (d : α) :
    env.getD (i + 1) d = env.tail.getD i d := by
  cases env <;> rfl

theorem getElem?_forcePureEnvD {α : Type} (d : α) :
    ∀ (n : Nat) (env : List α) (i : Nat),
      (forcePureEnvD d n env)[i]? = if i < n then some (env.getD i d) else none
  | 0, env, i => by simp [forcePureEnvD]
  | n + 1, env, 0 => by
    simp only [forcePureEnvD, List.getElem?_cons_zero, getD_zero_eq_headD, Nat.zero_lt_succ, ↓reduceIte]
  | n + 1, env, i + 1 => by
    simp only [forcePureEnvD, List.getElem?_cons_succ, getElem?_forcePureEnvD d n env.tail i,
      getD_succ_eq_tail, Nat.add_lt_add_iff_right]

/-- **Slot projection**: reads through `forcePureEnv` are slot reads. -/
theorem getElem?_forcePureEnv {α : Type} [Inhabited α] (n : Nat) (env : List α) (i : Nat) :
    (forcePureEnv n env)[i]? = if i < n then some (env.getD i default) else none :=
  getElem?_forcePureEnvD default n env i

theorem forcePureEnvD_set_comm {α : Type} (d : α) :
    ∀ (n : Nat) (env : List α) (i : Nat) (v : α), (i < env.length ∨ n ≤ i) →
      forcePureEnvD d n (env.set i v) = (forcePureEnvD d n env).set i v
  | 0, _, _, _, _ => rfl
  | n + 1, [], i, v, h => by
    have hi : n + 1 ≤ i := by
      rcases h with h | h
      · exact absurd h (Nat.not_lt_zero i)
      · exact h
    rw [List.set_eq_of_length_le (by simp), List.set_eq_of_length_le (by rw [length_forcePureEnvD]; exact hi)]
  | n + 1, x :: xs, 0, v, _ => rfl
  | n + 1, x :: xs, i + 1, v, h => by
    have h' : i < xs.length ∨ n ≤ i := by
      rcases h with h | h
      · left; simpa using h
      · right; omega
    simp only [List.set_cons_succ, forcePureEnvD, List.headD_cons, List.tail_cons,
      forcePureEnvD_set_comm d n xs i v h']

/-- **Projection commutes with in-range slot updates**.  The side condition is
necessary (see `forcePureEnv_set_comm_counterexample`). -/
theorem forcePureEnv_set_comm {α : Type} [Inhabited α] (n : Nat) (env : List α) (i : Nat) (v : α)
    (h : i < env.length ∨ n ≤ i) :
    forcePureEnv n (env.set i v) = (forcePureEnv n env).set i v :=
  forcePureEnvD_set_comm default n env i v h

/-- Without the side condition the commutation fails: updating a padding slot. -/
theorem forcePureEnv_set_comm_counterexample :
    forcePureEnv 2 (([] : List Nat).set 0 5) ≠ (forcePureEnv 2 ([] : List Nat)).set 0 5 := by
  decide

/-- Collapse lemma: a chain equals its projection-normal form. -/
theorem eq_of_forcePureEnv {α : Type} [Inhabited α] {n : Nat} {chain flat : List α}
    (hlen : chain.length = n) (h : forcePureEnv n chain = flat) : chain = flat := by
  rw [← h, forcePureEnv_eq_self n chain hlen]

/-- **Symbolic chained-update collapse by `rfl`**: four nested `List.set`
updates over symbolic slot values collapse to one flat list literal by kernel
reduction of the projection, without `List.set` commutation `simp` lemmas. -/
theorem chained_sets_collapse_rfl (a b c d x y z : Nat) :
    (((([a, b, c, d].set 0 x).set 2 y).set 0 z).set 3 (x + y)) = [z, b, y, x + y] :=
  eq_of_forcePureEnv (n := 4) rfl rfl

/-- Spine-forcing normalizer (the generic form of the live
`Anneal.MirLiftCore.forcePureEnv?`): reducing `forceSpine? l` to `some _`
materializes the whole list spine in one pass. -/
def forceSpine? {α : Type} : List α → Option (List α)
  | [] => some []
  | x :: xs =>
    match forceSpine? xs with
    | some ys => some (x :: ys)
    | none => none

theorem forceSpine?_eq_some {α : Type} : ∀ (l : List α), forceSpine? l = some l
  | [] => rfl
  | x :: xs => by simp only [forceSpine?, forceSpine?_eq_some xs]

theorem forceSpine?_eq_some_forcePureEnv {α : Type} [Inhabited α] (l : List α) :
    forceSpine? l = some (forcePureEnv l.length l) := by
  rw [forceSpine?_eq_some, forcePureEnv_eq_self l.length l rfl]

/-- Sequential local updates (`env[i₁] := v₁; …; env[i_K] := v_K`). -/
def applySlotUpdates {α : Type} (env : List α) (ups : List (Nat × α)) : List α :=
  ups.foldl (fun e u => e.set u.1 u.2) env

/-- Step-wise normalized execution: after every update the frame is re-forced,
so the next update always acts on a flat literal (the live
`evalPureStmtNorm` / `forcePureEnv?` discipline). -/
def applySlotUpdatesForced {α : Type} : List (Nat × α) → List α → Option (List α)
  | [], env => some env
  | u :: ups, env =>
    match forceSpine? (env.set u.1 u.2) with
    | some env' => applySlotUpdatesForced ups env'
    | none => none

theorem applySlotUpdatesForced_eq {α : Type} :
    ∀ (ups : List (Nat × α)) (env : List α),
      applySlotUpdatesForced ups env = some (applySlotUpdates env ups)
  | [], _ => rfl
  | u :: ups, env => by
    simp only [applySlotUpdatesForced, forceSpine?_eq_some, applySlotUpdates, List.foldl]
    exact applySlotUpdatesForced_eq ups _

/-- Soundness of step-wise normalization: a `rfl` proof of the forced run
proves the unnormalized update sequence. -/
theorem applySlotUpdates_eq_of_forced {α : Type} {env flat : List α} {ups : List (Nat × α)}
    (h : applySlotUpdatesForced ups env = some flat) : applySlotUpdates env ups = flat := by
  rw [applySlotUpdatesForced_eq] at h
  exact Option.some.inj h

theorem length_applySlotUpdates {α : Type} :
    ∀ (ups : List (Nat × α)) (env : List α), (applySlotUpdates env ups).length = env.length
  | [], _ => rfl
  | u :: ups, env => by
    simp only [applySlotUpdates, List.foldl] at *
    rw [show List.foldl (fun e u => e.set u.1 u.2) (env.set u.1 u.2) ups =
      applySlotUpdates (env.set u.1 u.2) ups from rfl, length_applySlotUpdates ups, List.length_set]

/-- Twelve symbolic updates collapse by `rfl` through step-wise forcing. -/
theorem slotUpdates_collapse_forced (a₀ a₁ a₂ a₃ a₄ a₅ x₁ x₂ x₃ x₄ x₅ x₆ : Nat) :
    applySlotUpdates [a₀, a₁, a₂, a₃, a₄, a₅]
      [(3, x₁), (0, x₂), (3, x₃), (5, x₄), (1, x₅), (0, x₆),
       (2, x₁ + x₂), (4, x₃), (5, x₆), (1, x₂), (3, x₄), (0, x₅)] =
      [x₅, x₂, x₁ + x₂, x₄, x₃, x₆] :=
  applySlotUpdates_eq_of_forced rfl

/-- Specialization of `forcePureEnv` to the live `Anneal.MirLiftCore.PureEnv`
(`List SlotState`), padding with `.uninit`. -/
def forcePureEnvSlots (n : Nat) (env : Anneal.MirLiftCore.PureEnv) : Anneal.MirLiftCore.PureEnv :=
  forcePureEnvD Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot.uninit n env

theorem forcePureEnvSlots_eq_self (env : Anneal.MirLiftCore.PureEnv) :
    forcePureEnvSlots env.length env = env :=
  forcePureEnvD_eq_self _ env.length env rfl

/-- **Bridge to the live `Anneal.MirLiftCore.forcePureEnv?`**: the generic
spine forcer agrees with the live normalizer on every `PureEnv`. -/
theorem forceSpine?_eq_live (env : Anneal.MirLiftCore.PureEnv) :
    forceSpine? env = Anneal.MirLiftCore.forcePureEnv? env := by
  rw [forceSpine?_eq_some, Anneal.MirLiftCore.forcePureEnv?_eq_some]

/-- Bridge to the live trusted `Trusted.Sequence.set?` used by `evalPureStmt`:
a successful live slot update commutes with the projection. -/
theorem forcePureEnvSlots_set? {env env' : Anneal.MirLiftCore.PureEnv} {loc : Nat}
    {s : Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot}
    (h : Trusted.Sequence.set? env loc s = some env') :
    forcePureEnvSlots env.length env' = (forcePureEnvSlots env.length env).set loc s := by
  unfold Trusted.Sequence.set? at h
  by_cases hlt : loc < env.length
  · rw [ite_eq_left hlt] at h
    cases h
    exact forcePureEnvD_set_comm _ env.length env loc s (Or.inl hlt)
  · rw [ite_eq_right hlt] at h
    cases h

end ForcePureEnv

/-! ## 8. Relational `TypedAt` / `DisjointSlice` lenses over trusted abstract bytes -/

section TypedAtLenses

open Trusted.Rustc.V2026_06_01.MirSemantics (AbstractByte sliceAbstractBytes writeAbstractBytesAt)
open Anneal.ByteCodec (FixedByteCodec)

/-- Byte-addressed memory of one allocation (trusted `AbstractByte`s). -/
abbrev Mem := List AbstractByte

/-- Pure splice `buf[off, off + w.length) := w`. -/
def splice {α : Type} (buf : List α) (off : Nat) (w : List α) : List α :=
  buf.take off ++ w ++ buf.drop (off + w.length)

theorem length_splice {α : Type} {buf w : List α} {off : Nat}
    (h : off + w.length ≤ buf.length) : (splice buf off w).length = buf.length := by
  simp only [splice, List.length_append, List.length_take, List.length_drop]
  omega

theorem getElem?_slice {α : Type} (buf : List α) (off len i : Nat) :
    ((buf.drop off).take len)[i]? = if i < len then buf[off + i]? else none := by
  by_cases hi : i < len
  · simp [hi, List.getElem?_drop]
  · simp [List.getElem?_take, hi]

theorem getElem?_splice {α : Type} {buf w : List α} {off : Nat}
    (h : off + w.length ≤ buf.length) (i : Nat) :
    (splice buf off w)[i]? =
      if i < off then buf[i]? else if i < off + w.length then w[i - off]? else buf[i]? := by
  unfold splice
  have htake : (buf.take off).length = off := by simp only [List.length_take]; omega
  by_cases h1 : i < off
  · rw [ite_eq_left h1, List.append_assoc, List.getElem?_append_left (by omega), List.getElem?_take]
    simp [h1]
  · rw [ite_eq_right h1]
    by_cases h2 : i < off + w.length
    · rw [ite_eq_left h2, List.getElem?_append_left (by simp only [List.length_append, htake]; omega),
        List.getElem?_append_right (by omega), htake]
    · rw [ite_eq_right h2, List.getElem?_append_right (by simp only [List.length_append, htake]; omega),
        List.getElem?_drop]
      simp only [List.length_append, htake]
      congr 1
      omega

/-- Constructive `drop`/`take` interchange (the core `List.drop_take` is classical). -/
theorem drop_take_add {α : Type} : ∀ (l : List α) (m k : Nat), (l.take (m + k)).drop m = (l.drop m).take k
  | l, 0, k => by rw [Nat.zero_add, List.drop_zero, List.drop_zero]
  | [], m + 1, k => by simp only [List.take_nil, List.drop_nil]
  | x :: xs, m + 1, k => by
    rw [Nat.add_right_comm, List.take_succ_cons, List.drop_succ_cons, List.drop_succ_cons]
    exact drop_take_add xs m k

/-- Reading back a spliced window returns the written bytes. -/
theorem slice_splice_same {α : Type} {buf w : List α} {off : Nat}
    (h : off + w.length ≤ buf.length) :
    ((splice buf off w).drop off).take w.length = w := by
  apply List.ext_getElem?
  intro i
  rw [getElem?_slice]
  by_cases hi : i < w.length
  · rw [ite_eq_left hi, getElem?_splice h, ite_eq_right (by omega), ite_eq_left (by omega)]
    congr 1
    omega
  · rw [ite_eq_right hi]
    exact (List.getElem?_eq_none (by omega)).symm

/-- Splicing preserves every disjoint window. -/
theorem slice_splice_disjoint {α : Type} {buf w : List α} {off₁ off₂ len₂ : Nat}
    (h : off₁ + w.length ≤ buf.length)
    (hd : w.length = 0 ∨ len₂ = 0 ∨ off₁ + w.length ≤ off₂ ∨ off₂ + len₂ ≤ off₁) :
    ((splice buf off₁ w).drop off₂).take len₂ = (buf.drop off₂).take len₂ := by
  apply List.ext_getElem?
  intro i
  rw [getElem?_slice, getElem?_slice]
  by_cases hi : i < len₂
  · rw [ite_eq_left hi, ite_eq_left hi, getElem?_splice h]
    by_cases h1 : off₂ + i < off₁
    · rw [ite_eq_left h1]
    · rw [ite_eq_right h1, ite_eq_right (by omega)]
  · rw [ite_eq_right hi, ite_eq_right hi]

/-- Writing back the bytes already present is the identity. -/
theorem splice_self {α : Type} {buf w : List α} {off : Nat}
    (h : off + w.length ≤ buf.length) (hw : (buf.drop off).take w.length = w) :
    splice buf off w = buf := by
  apply List.ext_getElem?
  intro i
  rw [getElem?_splice h]
  by_cases h1 : i < off
  · rw [ite_eq_left h1]
  · rw [ite_eq_right h1]
    by_cases h2 : i < off + w.length
    · rw [ite_eq_left h2, ← hw, getElem?_slice, ite_eq_left (by omega)]
      congr 1
      omega
    · rw [ite_eq_right h2]

/-- A second splice at the same window overrides the first. -/
theorem splice_splice_same {α : Type} {buf w₁ w₂ : List α} {off : Nat}
    (h : off + w₁.length ≤ buf.length) (hlen : w₂.length = w₁.length) :
    splice (splice buf off w₁) off w₂ = splice buf off w₂ := by
  have h₂ : off + w₂.length ≤ buf.length := by omega
  have h' : off + w₂.length ≤ (splice buf off w₁).length := by rw [length_splice h]; exact h₂
  apply List.ext_getElem?
  intro i
  rw [getElem?_splice h' i, getElem?_splice h₂ i, getElem?_splice h i, hlen]
  by_cases h1 : i < off <;> by_cases h2 : i < off + w₁.length <;> simp only [h1, h2, ↓reduceIte]

/-- Splices at disjoint windows commute. -/
theorem splice_comm {α : Type} {buf w₁ w₂ : List α} {off₁ off₂ : Nat}
    (h₁ : off₁ + w₁.length ≤ buf.length) (h₂ : off₂ + w₂.length ≤ buf.length)
    (hd : off₁ + w₁.length ≤ off₂ ∨ off₂ + w₂.length ≤ off₁) :
    splice (splice buf off₁ w₁) off₂ w₂ = splice (splice buf off₂ w₂) off₁ w₁ := by
  have h₂' : off₂ + w₂.length ≤ (splice buf off₁ w₁).length := by rw [length_splice h₁]; exact h₂
  have h₁' : off₁ + w₁.length ≤ (splice buf off₂ w₂).length := by rw [length_splice h₂]; exact h₁
  apply List.ext_getElem?
  intro i
  rw [getElem?_splice h₂', getElem?_splice h₁', getElem?_splice h₁, getElem?_splice h₂]
  by_cases a1 : i < off₁ <;> by_cases a2 : i < off₂ <;>
    by_cases b1 : i < off₁ + w₁.length <;> by_cases b2 : i < off₂ + w₂.length <;>
    simp only [a1, a2, b1, b2, ↓reduceIte] <;> (exfalso; omega)

/-- Closed form of the trusted `sliceAbstractBytes`. -/
theorem sliceAbstractBytes_eq (bytes : Mem) (off len : Nat) :
    sliceAbstractBytes bytes off len =
      if off + len ≤ bytes.length then some ((bytes.drop off).take len) else none := by
  unfold sliceAbstractBytes
  simp only [Anneal.BitValidity.takeAbstractBytes_eq_take, Anneal.BitValidity.dropAbstractBytes_eq_drop]
  split
  · next h =>
    have hgt : ¬ off + len ≤ bytes.length := fun hle => by
      have h2 : Nat.ble (Nat.add off len) (Trusted.Sequence.length bytes) = true :=
        Nat.ble_eq_true_of_le hle
      rw [h] at h2
      exact Bool.false_ne_true h2
    rw [ite_eq_right hgt]
  · next h =>
    have hle : off + len ≤ bytes.length := Nat.le_of_ble_eq_true h
    rw [ite_eq_left hle]

theorem writeAbstractBytesAt_nil (buf : Mem) (off : Nat) :
    writeAbstractBytesAt buf off [] = some buf := by
  cases buf <;> cases off <;> rfl

theorem writeAbstractBytesAt_cons :
    ∀ (buf : Mem) (off : Nat) (x : AbstractByte) (ws : Mem),
      writeAbstractBytesAt buf off (x :: ws) =
        if off + (ws.length + 1) ≤ buf.length then some (splice buf off (x :: ws)) else none
  | [], off, x, ws => by
    have : ¬ off + (ws.length + 1) ≤ ([] : Mem).length := by simp
    rw [ite_eq_right this]
  | b :: rest, 0, x, [] => by
    have : 0 + ([] : Mem).length + 1 ≤ (b :: rest).length := by simp
    show (match writeAbstractBytesAt rest 0 [] with
      | some tail' => some (x :: tail') | none => none) = _
    rw [writeAbstractBytesAt_nil, ite_eq_left (by simp)]
    rfl
  | b :: rest, 0, x, y :: ws => by
    show (match writeAbstractBytesAt rest 0 (y :: ws) with
      | some tail' => some (x :: tail') | none => none) = _
    rw [writeAbstractBytesAt_cons rest 0 y ws]
    by_cases hle : 0 + (ws.length + 1) ≤ rest.length
    · rw [ite_eq_left hle, ite_eq_left (by simp only [List.length_cons]; omega)]
      simp [splice]
    · rw [ite_eq_right hle, ite_eq_right (by simp only [List.length_cons]; omega)]
  | b :: rest, k + 1, x, ws => by
    show (match writeAbstractBytesAt rest k (x :: ws) with
      | some tail' => some (b :: tail') | none => none) = _
    rw [writeAbstractBytesAt_cons rest k x ws]
    by_cases hle : k + (ws.length + 1) ≤ rest.length
    · rw [ite_eq_left hle, ite_eq_left (by simp only [List.length_cons]; omega)]
      simp [splice, Nat.add_right_comm k 1]
    · rw [ite_eq_right hle, ite_eq_right (by simp only [List.length_cons]; omega)]

/-- In-bounds trusted writes are splices. -/
theorem writeAbstractBytesAt_eq_splice {buf w : Mem} {off : Nat}
    (h : off + w.length ≤ buf.length) :
    writeAbstractBytesAt buf off w = some (splice buf off w) := by
  cases w with
  | nil =>
    rw [writeAbstractBytesAt_nil]
    simp [splice, List.take_append_drop]
  | cons x ws =>
    rw [writeAbstractBytesAt_cons, ite_eq_left (by simpa using h)]

/-- Non-empty out-of-bounds trusted writes fail. -/
theorem writeAbstractBytesAt_eq_none {buf : Mem} {off : Nat} {x : AbstractByte} {ws : Mem}
    (h : buf.length < off + (ws.length + 1)) :
    writeAbstractBytesAt buf off (x :: ws) = none := by
  rw [writeAbstractBytesAt_cons, ite_eq_right (by omega)]

/-- Successful trusted writes are in bounds or empty, and are splices. -/
theorem writeAbstractBytesAt_some_inv {buf w mem' : Mem} {off : Nat}
    (hw : writeAbstractBytesAt buf off w = some mem') :
    (w.length = 0 ∧ mem' = buf) ∨ (off + w.length ≤ buf.length ∧ mem' = splice buf off w) := by
  cases w with
  | nil =>
    rw [writeAbstractBytesAt_nil] at hw
    exact Or.inl ⟨rfl, (Option.some.inj hw).symm⟩
  | cons x ws =>
    rw [writeAbstractBytesAt_cons] at hw
    by_cases hle : off + (ws.length + 1) ≤ buf.length
    · rw [ite_eq_left hle] at hw
      exact Or.inr ⟨by simpa using hle, (Option.some.inj hw).symm⟩
    · rw [ite_eq_right hle] at hw
      cases hw

/-- Typed read of a value through a live `FixedByteCodec`. -/
def readTyped {α : Type} {n : Nat} (c : FixedByteCodec α n) (base : Nat) (mem : Mem) : Option α :=
  (sliceAbstractBytes mem base n).bind c.decode

/-- Typed write through the trusted `writeAbstractBytesAt`. -/
def writeTyped {α : Type} {n : Nat} (c : FixedByteCodec α n) (base : Nat) (v : α) (mem : Mem) :
    Option Mem :=
  writeAbstractBytesAt mem base (c.encode v)

/-- **Relational `TypedAt`**: the `n`-byte window at `base` decodes to `v`
(padding bytes may hold anything the codec's decoder accepts). -/
def TypedAt {α : Type} {n : Nat} (c : FixedByteCodec α n) (base : Nat) (v : α) (mem : Mem) : Prop :=
  readTyped c base mem = some v

/-- **`DisjointSlice`**: empty windows are disjoint from everything; otherwise
the half-open windows do not overlap. -/
def DisjointSlice (base₁ len₁ base₂ len₂ : Nat) : Prop :=
  len₁ = 0 ∨ len₂ = 0 ∨ base₁ + len₁ ≤ base₂ ∨ base₂ + len₂ ≤ base₁

theorem DisjointSlice.symm {base₁ len₁ base₂ len₂ : Nat}
    (h : DisjointSlice base₁ len₁ base₂ len₂) : DisjointSlice base₂ len₂ base₁ len₁ := by
  unfold DisjointSlice at *
  omega

/-- **Adjacent-slice boundary**: `[b, b + l₁)` and `[b + l₁, b + l₁ + l₂)` are disjoint. -/
theorem DisjointSlice.adjacent (base len₁ len₂ : Nat) :
    DisjointSlice base len₁ (base + len₁) len₂ :=
  Or.inr (Or.inr (Or.inl (Nat.le_refl _)))

theorem typedAt_iff {α : Type} {n : Nat} (c : FixedByteCodec α n) (base : Nat) (v : α) (mem : Mem) :
    TypedAt c base v mem ↔ base + n ≤ mem.length ∧ c.decode ((mem.drop base).take n) = some v := by
  unfold TypedAt readTyped
  rw [sliceAbstractBytes_eq]
  by_cases h : base + n ≤ mem.length
  · rw [ite_eq_left h]
    exact ⟨fun hd => ⟨h, hd⟩, fun hd => hd.2⟩
  · rw [ite_eq_right h]
    exact ⟨(fun hd => nomatch hd), (fun hd => absurd hd.1 h)⟩

/-- Bridge to the live `FixedByteCodec.sliceAbstractBytes_append_encode`: an
encoding embedded at offset `pre.length` is `TypedAt` there. -/
theorem typedAt_append_encode {α : Type} {n : Nat} (c : FixedByteCodec α n) (pre post : Mem)
    (x : α) : TypedAt c pre.length x (pre ++ c.encode x ++ post) := by
  unfold TypedAt readTyped
  rw [Anneal.ByteCodec.FixedByteCodec.sliceAbstractBytes_append_encode]
  exact c.decode_encode x

theorem writeTyped_eq_splice {α : Type} {n : Nat} (c : FixedByteCodec α n) {base : Nat} (v : α)
    {mem : Mem} (h : base + n ≤ mem.length) :
    writeTyped c base v mem = some (splice mem base (c.encode v)) :=
  writeAbstractBytesAt_eq_splice (by rw [c.encode_length]; exact h)

theorem writeTyped_length {α : Type} {n : Nat} {c : FixedByteCodec α n} {base : Nat} {v : α}
    {mem mem' : Mem} (hw : writeTyped c base v mem = some mem') : mem'.length = mem.length := by
  rcases writeAbstractBytesAt_some_inv hw with ⟨_, rfl⟩ | ⟨hle, rfl⟩
  · rfl
  · exact length_splice hle

/-- **`TypedAt.read_write_same`**: an in-bounds typed write succeeds, preserves
the length, and establishes `TypedAt` for the written value. -/
theorem TypedAt.read_write_same {α : Type} {n : Nat} (c : FixedByteCodec α n) {base : Nat}
    (v : α) {mem : Mem} (h : base + n ≤ mem.length) :
    ∃ mem', writeTyped c base v mem = some mem' ∧ TypedAt c base v mem' ∧ mem'.length = mem.length := by
  have hlen : base + (c.encode v).length ≤ mem.length := by rw [c.encode_length]; exact h
  refine ⟨splice mem base (c.encode v), writeTyped_eq_splice c v h, ?_, length_splice hlen⟩
  rw [typedAt_iff]
  refine ⟨by rw [length_splice hlen]; exact h, ?_⟩
  have hs := slice_splice_same hlen
  rw [c.encode_length] at hs
  rw [hs, c.decode_encode]

/-- Raw-byte frame rule: a successful byte write leaves every disjoint `TypedAt`
intact (no unfolding of the codec or of the byte lists). -/
theorem TypedAt.frame_writeBytes {α : Type} {n₂ : Nat} {c₂ : FixedByteCodec α n₂}
    {base₂ off : Nat} {v₂ : α} {w mem mem' : Mem}
    (hd : DisjointSlice off w.length base₂ n₂)
    (hw : writeAbstractBytesAt mem off w = some mem')
    (h : TypedAt c₂ base₂ v₂ mem) : TypedAt c₂ base₂ v₂ mem' := by
  rcases writeAbstractBytesAt_some_inv hw with ⟨_, rfl⟩ | ⟨hle, rfl⟩
  · exact h
  · rw [typedAt_iff] at h ⊢
    refine ⟨by rw [length_splice hle]; exact h.1, ?_⟩
    rw [slice_splice_disjoint hle hd]
    exact h.2

/-- **`TypedAt.frame_write`** (`read_write_disjoint`): a successful typed write
at a disjoint window preserves `TypedAt`, in `O(1)` rewrite steps. -/
theorem TypedAt.frame_write {α β : Type} {n₁ n₂ : Nat} {c₁ : FixedByteCodec α n₁}
    {c₂ : FixedByteCodec β n₂} {base₁ base₂ : Nat} {v₁ : α} {v₂ : β} {mem mem' : Mem}
    (hd : DisjointSlice base₁ n₁ base₂ n₂)
    (hw : writeTyped c₁ base₁ v₁ mem = some mem')
    (h : TypedAt c₂ base₂ v₂ mem) : TypedAt c₂ base₂ v₂ mem' :=
  TypedAt.frame_writeBytes (by rw [c₁.encode_length]; exact hd) hw h

/-- Adjacent-window instance of the frame rule (boundary `base₁ + n₁ = base₂`). -/
theorem TypedAt.frame_write_adjacent {α β : Type} {n₁ n₂ : Nat} {c₁ : FixedByteCodec α n₁}
    {c₂ : FixedByteCodec β n₂} {base : Nat} {v₁ : α} {v₂ : β} {mem mem' : Mem}
    (hw : writeTyped c₁ base v₁ mem = some mem')
    (h : TypedAt c₂ (base + n₁) v₂ mem) : TypedAt c₂ (base + n₁) v₂ mem' :=
  TypedAt.frame_write (DisjointSlice.adjacent base n₁ n₂) hw h

/-- **Out-of-bounds write failure**: a non-zero-width write that does not fit fails. -/
theorem writeTyped_eq_none_of_oob {α : Type} {n : Nat} (c : FixedByteCodec α n) {base : Nat}
    (v : α) {mem : Mem} (hn : 0 < n) (h : mem.length < base + n) :
    writeTyped c base v mem = none := by
  unfold writeTyped
  have hl := c.encode_length v
  cases he : c.encode v with
  | nil => rw [he] at hl; simp at hl; omega
  | cons x ws =>
    rw [he] at hl
    exact writeAbstractBytesAt_eq_none (by simp at hl; omega)

/-- Characterization: a non-zero-width typed write succeeds iff it fits. -/
theorem writeTyped_isSome_iff {α : Type} {n : Nat} (c : FixedByteCodec α n) (base : Nat)
    (v : α) (mem : Mem) (hn : 0 < n) :
    (writeTyped c base v mem).isSome = true ↔ base + n ≤ mem.length := by
  constructor
  · intro hs
    by_cases h : base + n ≤ mem.length
    · exact h
    · rw [writeTyped_eq_none_of_oob c v hn (by omega)] at hs
      cases hs
  · intro h
    rw [writeTyped_eq_splice c v h]
    rfl

theorem not_typedAt_of_oob {α : Type} {n : Nat} (c : FixedByteCodec α n) {base : Nat} {v : α}
    {mem : Mem} (h : mem.length < base + n) : ¬ TypedAt c base v mem := by
  rw [typedAt_iff]
  intro hd
  omega

/-- **Zero-width boundary (writes)**: a zero-width typed write is a no-op at
*every* base, including out-of-bounds bases. -/
theorem writeTyped_zero_width {α : Type} (c : FixedByteCodec α 0) (base : Nat) (v : α) (mem : Mem) :
    writeTyped c base v mem = some mem := by
  unfold writeTyped
  have hl := c.encode_length v
  cases he : c.encode v with
  | nil => exact writeAbstractBytesAt_nil mem base
  | cons x ws => rw [he] at hl; simp at hl

/-- **Zero-width boundary (reads)**: a zero-width `TypedAt` additionally
requires `base ≤ mem.length`. -/
theorem typedAt_zero_width_iff {α : Type} (c : FixedByteCodec α 0) (base : Nat) (v : α)
    (mem : Mem) : TypedAt c base v mem ↔ base ≤ mem.length ∧ c.decode [] = some v := by
  rw [typedAt_iff]
  simp only [Nat.add_zero, List.take_zero]

/-- The zero-width read/write asymmetry of the trusted primitives, witnessed by
the live `FixedByteCodec.unit` codec one byte past the end. -/
theorem zeroWidth_write_read_asymmetry (mem : Mem) :
    writeTyped Anneal.ByteCodec.FixedByteCodec.unit (mem.length + 1) () mem = some mem ∧
      ¬ TypedAt Anneal.ByteCodec.FixedByteCodec.unit (mem.length + 1) () mem := by
  refine ⟨writeTyped_zero_width _ _ _ _, ?_⟩
  rw [typedAt_zero_width_iff]
  intro h
  omega

/-- `#[repr(C)]`-style padded pair `struct { a: A, _pad: [uninit; pad], b: B }`
built from the live `prod` / `padRight` combinators. -/
def laidOutPair {α β : Type} {n₁ n₂ : Nat} (c₁ : FixedByteCodec α n₁) (pad : Nat)
    (c₂ : FixedByteCodec β n₂) : FixedByteCodec (α × β) (n₁ + pad + n₂) :=
  Anneal.ByteCodec.FixedByteCodec.prod (Anneal.ByteCodec.FixedByteCodec.padRight c₁ pad) c₂

theorem prod_decode_eq_some_iff {α β : Type} {n₁ n₂ : Nat} (c₁ : FixedByteCodec α n₁)
    (c₂ : FixedByteCodec β n₂) (bs : Mem) (a : α) (b : β) (h : bs.length = n₁ + n₂) :
    (Anneal.ByteCodec.FixedByteCodec.prod c₁ c₂).decode bs = some (a, b) ↔
      c₁.decode (bs.take n₁) = some a ∧ c₂.decode (bs.drop n₁) = some b := by
  simp only [Anneal.ByteCodec.FixedByteCodec.prod, Anneal.ByteCodec.FixedByteCodec.ofRoundTrip, h,
    Nat.beq_refl]
  cases h₁ : c₁.decode (bs.take n₁) <;> cases h₂ : c₂.decode (bs.drop n₁) <;> simp

theorem padRight_decode_of_length {α : Type} {n : Nat} (c : FixedByteCodec α n) (pad : Nat)
    (bs : Mem) (h : bs.length = n + pad) :
    (Anneal.ByteCodec.FixedByteCodec.padRight c pad).decode bs = c.decode (bs.take n) := by
  have hpad : (bs.drop n).length = pad := by simp only [List.length_drop]; omega
  simp only [Anneal.ByteCodec.FixedByteCodec.padRight, Anneal.ByteCodec.FixedByteCodec.mapEquiv,
    Anneal.ByteCodec.FixedByteCodec.prod, Anneal.ByteCodec.FixedByteCodec.padUninit,
    Anneal.ByteCodec.FixedByteCodec.ofRoundTrip, h, hpad, Nat.beq_refl, ↓reduceIte]
  cases c.decode (bs.take n) <;> rfl

/-- **`TypedAt` across a padded codec**: a padded pair is typed at `base` iff
the window fits and both fields are typed at their offsets; the padding bytes
are unconstrained. -/
theorem typedAt_laidOutPair_iff {α β : Type} {n₁ n₂ : Nat} (c₁ : FixedByteCodec α n₁)
    (pad : Nat) (c₂ : FixedByteCodec β n₂) (base : Nat) (a : α) (b : β) (mem : Mem) :
    TypedAt (laidOutPair c₁ pad c₂) base (a, b) mem ↔
      base + (n₁ + pad + n₂) ≤ mem.length ∧ TypedAt c₁ base a mem ∧
        TypedAt c₂ (base + n₁ + pad) b mem := by
  rw [typedAt_iff, typedAt_iff, typedAt_iff]
  constructor
  · rintro ⟨hb, hd⟩
    have hlen : ((mem.drop base).take (n₁ + pad + n₂)).length = n₁ + pad + n₂ := by
      simp only [List.length_take, List.length_drop]; omega
    rw [laidOutPair, prod_decode_eq_some_iff _ _ _ _ _ hlen,
      padRight_decode_of_length _ _ _ (by simp only [List.length_take, List.length_drop]; omega)] at hd
    obtain ⟨h₁, h₂⟩ := hd
    rw [List.take_take, Nat.min_eq_left (by omega), List.take_take,
      Nat.min_eq_left (by omega)] at h₁
    rw [drop_take_add, List.drop_drop, ← Nat.add_assoc] at h₂
    exact ⟨hb, ⟨by omega, h₁⟩, ⟨by omega, h₂⟩⟩
  · rintro ⟨hb, ⟨_, h₁⟩, ⟨_, h₂⟩⟩
    refine ⟨hb, ?_⟩
    have hlen : ((mem.drop base).take (n₁ + pad + n₂)).length = n₁ + pad + n₂ := by
      simp only [List.length_take, List.length_drop]; omega
    rw [laidOutPair, prod_decode_eq_some_iff _ _ _ _ _ hlen,
      padRight_decode_of_length _ _ _ (by simp only [List.length_take, List.length_drop]; omega)]
    refine ⟨?_, ?_⟩
    · rw [List.take_take, Nat.min_eq_left (by omega), List.take_take, Nat.min_eq_left (by omega)]
      exact h₁
    · rw [drop_take_add, List.drop_drop, ← Nat.add_assoc]
      exact h₂

/-- Writing the second field of a padded pair updates the pair value in place. -/
theorem typedAt_laidOutPair_write_snd {α β : Type} {n₁ n₂ : Nat} {c₁ : FixedByteCodec α n₁}
    {pad : Nat} {c₂ : FixedByteCodec β n₂} {base : Nat} {a : α} {b b' : β} {mem mem' : Mem}
    (h : TypedAt (laidOutPair c₁ pad c₂) base (a, b) mem)
    (hw : writeTyped c₂ (base + n₁ + pad) b' mem = some mem') :
    TypedAt (laidOutPair c₁ pad c₂) base (a, b') mem' := by
  rw [typedAt_laidOutPair_iff] at h ⊢
  obtain ⟨hb, h₁, h₂⟩ := h
  have hlen := writeTyped_length hw
  obtain ⟨m₂, hw₂, ht₂, _⟩ := TypedAt.read_write_same c₂ b' ((typedAt_iff _ _ _ _).mp h₂).1
  rw [hw₂] at hw
  cases hw
  refine ⟨by omega, ?_, ht₂⟩
  exact TypedAt.frame_write (by unfold DisjointSlice; omega) hw₂ h₁

/-- **Padding is semantically irrelevant**: overwriting the padding window with
arbitrary (even initialized) bytes preserves the padded pair's `TypedAt`. -/
theorem typedAt_laidOutPair_padding_write {α β : Type} {n₁ n₂ : Nat} {c₁ : FixedByteCodec α n₁}
    {pad : Nat} {c₂ : FixedByteCodec β n₂} {base : Nat} {a : α} {b : β} {junk mem mem' : Mem}
    (hj : junk.length = pad)
    (h : TypedAt (laidOutPair c₁ pad c₂) base (a, b) mem)
    (hw : writeAbstractBytesAt mem (base + n₁) junk = some mem') :
    TypedAt (laidOutPair c₁ pad c₂) base (a, b) mem' := by
  rw [typedAt_laidOutPair_iff] at h ⊢
  obtain ⟨hb, h₁, h₂⟩ := h
  have hlen : mem'.length = mem.length := by
    rcases writeAbstractBytesAt_some_inv hw with ⟨_, rfl⟩ | ⟨hle, rfl⟩
    · rfl
    · exact length_splice hle
  refine ⟨by omega, ?_, ?_⟩
  · exact TypedAt.frame_writeBytes (by unfold DisjointSlice; omega) hw h₁
  · exact TypedAt.frame_writeBytes (by unfold DisjointSlice; omega) hw h₂

/-- The padded pair's *encoding* carries `.uninit` padding (live
`padRight_encode_eq`), so an exact-bytes predicate would reject the
initialized-padding memories that `TypedAt` (correctly) accepts. -/
theorem laidOutPair_encode_eq {α β : Type} {n₁ n₂ : Nat} (c₁ : FixedByteCodec α n₁) (pad : Nat)
    (c₂ : FixedByteCodec β n₂) (a : α) (b : β) :
    (laidOutPair c₁ pad c₂).encode (a, b) = c₁.encode a ++ List.replicate pad .uninit ++ c₂.encode b := by
  simp [laidOutPair, Anneal.ByteCodec.FixedByteCodec.prod, Anneal.ByteCodec.FixedByteCodec.ofRoundTrip,
    Anneal.ByteCodec.FixedByteCodec.padRight_encode_eq]

/-- Concrete witness: a `u8`/`u8` pair whose padding byte is *initialized* is
still typed (relational decode), even though it differs from the encoding. -/
theorem typedAt_laidOutPair_init_padding (a b p : UInt8) :
    TypedAt (laidOutPair Anneal.ByteCodec.FixedByteCodec.u8 1 Anneal.ByteCodec.FixedByteCodec.u8) 0
      (a, b) [.init a none, .init p none, .init b none] ∧
    (laidOutPair Anneal.ByteCodec.FixedByteCodec.u8 1 Anneal.ByteCodec.FixedByteCodec.u8).encode (a, b) ≠
      [.init a none, .init p none, .init b none] := by
  refine ⟨rfl, ?_⟩
  intro h
  rw [laidOutPair_encode_eq] at h
  simp [Anneal.ByteCodec.FixedByteCodec.u8, Anneal.ByteCodec.FixedByteCodec.ofRoundTrip] at h

/-- Canonical (exact) encoding of some value at a window. -/
def CanonicalAt {α : Type} {n : Nat} (c : FixedByteCodec α n) (base : Nat) (mem : Mem) : Prop :=
  ∃ v, sliceAbstractBytes mem base n = some (c.encode v)

/-- Lens validity for two struct fields: both windows hold canonical encodings. -/
def FieldsValid {α β : Type} {n₁ n₂ : Nat} (c₁ : FixedByteCodec α n₁) (base₁ : Nat)
    (c₂ : FixedByteCodec β n₂) (base₂ : Nat) (mem : Mem) : Prop :=
  CanonicalAt c₁ base₁ mem ∧ CanonicalAt c₂ base₂ mem

/-- Field lens over trusted memory (`Anneal.FunctionalTranslation.MutLens`):
reads decode the window, writes use the trusted `writeAbstractBytesAt`. -/
def fieldLens {α : Type} {n : Nat} (c : FixedByteCodec α n) (base : Nat) (dflt : α) :
    Anneal.FunctionalTranslation.MutLens Mem α where
  readView mem := (readTyped c base mem).getD dflt
  writeBack v mem := (writeTyped c base v mem).getD mem

theorem canonicalAt_iff {α : Type} {n : Nat} (c : FixedByteCodec α n) (base : Nat) (mem : Mem) :
    CanonicalAt c base mem ↔ base + n ≤ mem.length ∧ ∃ v, (mem.drop base).take n = c.encode v := by
  unfold CanonicalAt
  rw [sliceAbstractBytes_eq]
  by_cases h : base + n ≤ mem.length
  · rw [ite_eq_left h]
    exact ⟨(fun ⟨v, hv⟩ => ⟨h, v, Option.some.inj hv⟩), (fun ⟨_, v, hv⟩ => ⟨v, by rw [hv]⟩)⟩
  · rw [ite_eq_right h]
    exact ⟨(fun ⟨_, hv⟩ => nomatch hv), (fun hd => absurd hd.1 h)⟩

theorem fieldLens_writeBack_eq {α : Type} {n : Nat} (c : FixedByteCodec α n) {base : Nat}
    (dflt v : α) {mem : Mem} (h : base + n ≤ mem.length) :
    (fieldLens c base dflt).writeBack v mem = splice mem base (c.encode v) := by
  show (writeTyped c base v mem).getD mem = _
  rw [writeTyped_eq_splice c v h]
  rfl

theorem canonicalAt_splice_same {α : Type} {n : Nat} (c : FixedByteCodec α n) {base : Nat}
    (v : α) {mem : Mem} (h : base + n ≤ mem.length) :
    CanonicalAt c base (splice mem base (c.encode v)) := by
  have hlen : base + (c.encode v).length ≤ mem.length := by rw [c.encode_length]; exact h
  rw [canonicalAt_iff, length_splice hlen]
  refine ⟨h, v, ?_⟩
  have hs := slice_splice_same hlen
  rw [c.encode_length] at hs
  exact hs

theorem canonicalAt_splice_disjoint {α β : Type} {n₁ n₂ : Nat} (c₁ : FixedByteCodec α n₁)
    (c₂ : FixedByteCodec β n₂) {base₁ base₂ : Nat} (v : α) {mem : Mem}
    (h : base₁ + n₁ ≤ mem.length) (hd : DisjointSlice base₁ n₁ base₂ n₂)
    (hc : CanonicalAt c₂ base₂ mem) : CanonicalAt c₂ base₂ (splice mem base₁ (c₁.encode v)) := by
  have hlen : base₁ + (c₁.encode v).length ≤ mem.length := by rw [c₁.encode_length]; exact h
  rw [canonicalAt_iff] at hc ⊢
  obtain ⟨hb, w, hw⟩ := hc
  refine ⟨by rw [length_splice hlen]; exact hb, w, ?_⟩
  rw [slice_splice_disjoint hlen (by rw [c₁.encode_length]; exact hd)]
  exact hw

theorem readTyped_splice_same {α : Type} {n : Nat} (c : FixedByteCodec α n) {base : Nat}
    (v : α) {mem : Mem} (h : base + n ≤ mem.length) :
    readTyped c base (splice mem base (c.encode v)) = some v := by
  obtain ⟨m, hw, ht, _⟩ := TypedAt.read_write_same c v h
  rw [writeTyped_eq_splice c v h] at hw
  cases hw
  exact ht

theorem readTyped_splice_disjoint {α β : Type} {n₁ n₂ : Nat} (c₁ : FixedByteCodec α n₁)
    (c₂ : FixedByteCodec β n₂) {base₁ base₂ : Nat} (v : α) {mem : Mem}
    (h : base₁ + n₁ ≤ mem.length) (hd : DisjointSlice base₁ n₁ base₂ n₂) :
    readTyped c₂ base₂ (splice mem base₁ (c₁.encode v)) = readTyped c₂ base₂ mem := by
  have hlen : base₁ + (c₁.encode v).length ≤ mem.length := by rw [c₁.encode_length]; exact h
  unfold readTyped
  rw [sliceAbstractBytes_eq, sliceAbstractBytes_eq, length_splice hlen,
    slice_splice_disjoint hlen (by rw [c₁.encode_length]; exact hd)]

/-- Lawfulness of one field lens on `FieldsValid` states. -/
theorem fieldLens_lawful {α β : Type} {n₁ n₂ : Nat} (c₁ : FixedByteCodec α n₁)
    (c₂ : FixedByteCodec β n₂) (base₁ base₂ : Nat) (d₁ : α)
    (hd : DisjointSlice base₁ n₁ base₂ n₂) :
    Anneal.FunctionalTranslation.LawfulMutLens (fieldLens c₁ base₁ d₁)
      (FieldsValid c₁ base₁ c₂ base₂) where
  valid_writeBack a mem hv := by
    obtain ⟨hb, _⟩ := (canonicalAt_iff c₁ base₁ mem).mp hv.1
    rw [fieldLens_writeBack_eq c₁ d₁ a hb]
    exact ⟨canonicalAt_splice_same c₁ a hb, canonicalAt_splice_disjoint c₁ c₂ a hb hd hv.2⟩
  readView_writeBack a mem hv := by
    obtain ⟨hb, _⟩ := (canonicalAt_iff c₁ base₁ mem).mp hv.1
    rw [fieldLens_writeBack_eq c₁ d₁ a hb]
    show (readTyped c₁ base₁ (splice mem base₁ (c₁.encode a))).getD d₁ = a
    rw [readTyped_splice_same c₁ a hb]
    rfl
  writeBack_readView mem hv := by
    obtain ⟨hb, v, hv₁⟩ := (canonicalAt_iff c₁ base₁ mem).mp hv.1
    have hr : (fieldLens c₁ base₁ d₁).readView mem = v := by
      show (readTyped c₁ base₁ mem).getD d₁ = v
      unfold readTyped
      rw [sliceAbstractBytes_eq, ite_eq_left hb, hv₁]
      show (c₁.decode (c₁.encode v)).getD d₁ = v
      rw [c₁.decode_encode]
      rfl
    rw [hr, fieldLens_writeBack_eq c₁ d₁ v hb]
    have hlen : base₁ + (c₁.encode v).length ≤ mem.length := by rw [c₁.encode_length]; exact hb
    exact splice_self hlen (by rw [c₁.encode_length]; exact hv₁)
  writeBack_writeBack a₁ a₂ mem hv := by
    obtain ⟨hb, _⟩ := (canonicalAt_iff c₁ base₁ mem).mp hv.1
    have hlen : base₁ + (c₁.encode a₁).length ≤ mem.length := by rw [c₁.encode_length]; exact hb
    have hb' : base₁ + n₁ ≤ (splice mem base₁ (c₁.encode a₁)).length := by
      rw [length_splice hlen]; exact hb
    rw [fieldLens_writeBack_eq c₁ d₁ a₁ hb, fieldLens_writeBack_eq c₁ d₁ a₂ hb',
      fieldLens_writeBack_eq c₁ d₁ a₂ hb,
      splice_splice_same hlen (by rw [c₁.encode_length, c₁.encode_length])]

theorem fieldsValid_symm {α β : Type} {n₁ n₂ : Nat} {c₁ : FixedByteCodec α n₁}
    {c₂ : FixedByteCodec β n₂} {base₁ base₂ : Nat} {mem : Mem} :
    FieldsValid c₁ base₁ c₂ base₂ mem ↔ FieldsValid c₂ base₂ c₁ base₁ mem :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- **`subplaceFieldLens_disjoint`**: two struct fields at disjoint windows give
live `LawfulMutLens` witnesses for both field lenses and a live
`Anneal.SepLogicLenses.IndependentLenses` witness for the pair. -/
theorem subplaceFieldLens_disjoint {α β : Type} {n₁ n₂ : Nat} (c₁ : FixedByteCodec α n₁)
    (c₂ : FixedByteCodec β n₂) (base₁ base₂ : Nat) (d₁ : α) (d₂ : β)
    (hd : DisjointSlice base₁ n₁ base₂ n₂) :
    Anneal.FunctionalTranslation.LawfulMutLens (fieldLens c₁ base₁ d₁)
        (FieldsValid c₁ base₁ c₂ base₂) ∧
      Anneal.FunctionalTranslation.LawfulMutLens (fieldLens c₂ base₂ d₂)
        (FieldsValid c₁ base₁ c₂ base₂) ∧
      Anneal.SepLogicLenses.IndependentLenses (fieldLens c₁ base₁ d₁) (fieldLens c₂ base₂ d₂)
        (FieldsValid c₁ base₁ c₂ base₂) := by
  have hL₁ := fieldLens_lawful c₁ c₂ base₁ base₂ d₁ hd
  have hL₂' := fieldLens_lawful c₂ c₁ base₂ base₁ d₂ hd.symm
  have hL₂ : Anneal.FunctionalTranslation.LawfulMutLens (fieldLens c₂ base₂ d₂)
      (FieldsValid c₁ base₁ c₂ base₂) :=
    { valid_writeBack := fun b m hv =>
        fieldsValid_symm.mpr (hL₂'.valid_writeBack b m (fieldsValid_symm.mp hv))
      readView_writeBack := fun b m hv => hL₂'.readView_writeBack b m (fieldsValid_symm.mp hv)
      writeBack_readView := fun m hv => hL₂'.writeBack_readView m (fieldsValid_symm.mp hv)
      writeBack_writeBack := fun b₁ b₂ m hv =>
        hL₂'.writeBack_writeBack b₁ b₂ m (fieldsValid_symm.mp hv) }
  refine ⟨hL₁, hL₂, ?_⟩
  refine
    { valid_writeBack_left := hL₁.valid_writeBack
      valid_writeBack_right := hL₂.valid_writeBack
      readView_right_of_writeBack_left := ?_
      readView_left_of_writeBack_right := ?_
      writeBack_comm := ?_ }
  · intro a m hv
    obtain ⟨hb, _⟩ := (canonicalAt_iff c₁ base₁ m).mp hv.1
    rw [fieldLens_writeBack_eq c₁ d₁ a hb]
    show (readTyped c₂ base₂ _).getD d₂ = (readTyped c₂ base₂ m).getD d₂
    rw [readTyped_splice_disjoint c₁ c₂ a hb hd]
  · intro b m hv
    obtain ⟨hb, _⟩ := (canonicalAt_iff c₂ base₂ m).mp hv.2
    rw [fieldLens_writeBack_eq c₂ d₂ b hb]
    show (readTyped c₁ base₁ _).getD d₁ = (readTyped c₁ base₁ m).getD d₁
    rw [readTyped_splice_disjoint c₂ c₁ b hb hd.symm]
  · intro a b m hv
    obtain ⟨hb₁, _⟩ := (canonicalAt_iff c₁ base₁ m).mp hv.1
    obtain ⟨hb₂, _⟩ := (canonicalAt_iff c₂ base₂ m).mp hv.2
    have hl₁ : base₁ + (c₁.encode a).length ≤ m.length := by rw [c₁.encode_length]; exact hb₁
    have hl₂ : base₂ + (c₂.encode b).length ≤ m.length := by rw [c₂.encode_length]; exact hb₂
    rw [fieldLens_writeBack_eq c₁ d₁ a hb₁, fieldLens_writeBack_eq c₂ d₂ b hb₂,
      fieldLens_writeBack_eq c₂ d₂ b (by rw [length_splice hl₁]; exact hb₂),
      fieldLens_writeBack_eq c₁ d₁ a (by rw [length_splice hl₂]; exact hb₁)]
    unfold DisjointSlice at hd
    rcases hd with h0 | h0 | h0 | h0
    · have he : c₁.encode a = [] := List.eq_nil_of_length_eq_zero (by rw [c₁.encode_length]; exact h0)
      rw [he]
      simp only [splice, List.length_nil, Nat.add_zero, List.append_nil, List.take_append_drop]
    · have he : c₂.encode b = [] := List.eq_nil_of_length_eq_zero (by rw [c₂.encode_length]; exact h0)
      rw [he]
      simp only [splice, List.length_nil, Nat.add_zero, List.append_nil, List.take_append_drop]
    · exact splice_comm hl₁ hl₂ (by rw [c₁.encode_length]; left; exact h0)
    · exact splice_comm hl₁ hl₂ (by rw [c₂.encode_length]; right; exact h0)

/-- The whole-struct product lens (live `prodMutLens`) is lawful by the live
`prodMutLens_lawful`. -/
theorem structLens_lawful {α β : Type} {n₁ n₂ : Nat} (c₁ : FixedByteCodec α n₁)
    (c₂ : FixedByteCodec β n₂) (base₁ base₂ : Nat) (d₁ : α) (d₂ : β)
    (hd : DisjointSlice base₁ n₁ base₂ n₂) :
    Anneal.FunctionalTranslation.LawfulMutLens
      (Anneal.SepLogicLenses.prodMutLens (fieldLens c₁ base₁ d₁) (fieldLens c₂ base₂ d₂))
      (FieldsValid c₁ base₁ c₂ base₂) :=
  let ⟨hL₁, hL₂, hI⟩ := subplaceFieldLens_disjoint c₁ c₂ base₁ base₂ d₁ d₂ hd
  Anneal.SepLogicLenses.prodMutLens_lawful hL₁ hL₂ hI

/-- `K` sequential field mutations (`.inl` writes field 1, `.inr` field 2). -/
def applyFieldWrites {α β : Type} (L₁ : Anneal.FunctionalTranslation.MutLens Mem α)
    (L₂ : Anneal.FunctionalTranslation.MutLens Mem β) : List (α ⊕ β) → Mem → Mem
  | [], m => m
  | .inl a :: ws, m => applyFieldWrites L₁ L₂ ws (L₁.writeBack a m)
  | .inr b :: ws, m => applyFieldWrites L₁ L₂ ws (L₂.writeBack b m)

/-- Last value written to field 1 (or `a` if none). -/
def lastLeft {α β : Type} : List (α ⊕ β) → α → α
  | [], a => a
  | .inl a :: ws, _ => lastLeft ws a
  | .inr _ :: ws, a => lastLeft ws a

/-- Last value written to field 2 (or `b` if none). -/
def lastRight {α β : Type} : List (α ⊕ β) → β → β
  | [], b => b
  | .inl _ :: ws, b => lastRight ws b
  | .inr b :: ws, _ => lastRight ws b

/-- **`K` sequential struct-field mutations in `O(1)` lens steps each**: each
mutation is discharged by one lens law; no byte list is ever unfolded. -/
theorem applyFieldWrites_spec {α β : Type} {L₁ : Anneal.FunctionalTranslation.MutLens Mem α}
    {L₂ : Anneal.FunctionalTranslation.MutLens Mem β} {V : Mem → Prop}
    (hL₁ : Anneal.FunctionalTranslation.LawfulMutLens L₁ V)
    (hL₂ : Anneal.FunctionalTranslation.LawfulMutLens L₂ V)
    (hI : Anneal.SepLogicLenses.IndependentLenses L₁ L₂ V) :
    ∀ (ws : List (α ⊕ β)) (m : Mem), V m →
      V (applyFieldWrites L₁ L₂ ws m) ∧
        L₁.readView (applyFieldWrites L₁ L₂ ws m) = lastLeft ws (L₁.readView m) ∧
        L₂.readView (applyFieldWrites L₁ L₂ ws m) = lastRight ws (L₂.readView m)
  | [], _, hv => ⟨hv, rfl, rfl⟩
  | .inl a :: ws, m, hv => by
    have ih := applyFieldWrites_spec hL₁ hL₂ hI ws (L₁.writeBack a m) (hL₁.valid_writeBack a m hv)
    refine ⟨ih.1, ?_, ?_⟩
    · rw [show applyFieldWrites L₁ L₂ (.inl a :: ws) m = applyFieldWrites L₁ L₂ ws (L₁.writeBack a m)
        from rfl, ih.2.1, hL₁.readView_writeBack a m hv]
      rfl
    · rw [show applyFieldWrites L₁ L₂ (.inl a :: ws) m = applyFieldWrites L₁ L₂ ws (L₁.writeBack a m)
        from rfl, ih.2.2, hI.readView_right_of_writeBack_left a m hv]
      rfl
  | .inr b :: ws, m, hv => by
    have ih := applyFieldWrites_spec hL₁ hL₂ hI ws (L₂.writeBack b m) (hL₂.valid_writeBack b m hv)
    refine ⟨ih.1, ?_, ?_⟩
    · rw [show applyFieldWrites L₁ L₂ (.inr b :: ws) m = applyFieldWrites L₁ L₂ ws (L₂.writeBack b m)
        from rfl, ih.2.1, hI.readView_left_of_writeBack_right b m hv]
      rfl
    · rw [show applyFieldWrites L₁ L₂ (.inr b :: ws) m = applyFieldWrites L₁ L₂ ws (L₂.writeBack b m)
        from rfl, ih.2.2, hL₂.readView_writeBack b m hv]
      rfl

/-- Two `u8` fields of a padded struct `{ a: u8, _pad, b: u8 }` (offsets `0` and `2`). -/
def u8FieldA : Anneal.FunctionalTranslation.MutLens Mem UInt8 :=
  fieldLens Anneal.ByteCodec.FixedByteCodec.u8 0 0

def u8FieldB : Anneal.FunctionalTranslation.MutLens Mem UInt8 :=
  fieldLens Anneal.ByteCodec.FixedByteCodec.u8 2 0

def u8FieldsValid : Mem → Prop :=
  FieldsValid Anneal.ByteCodec.FixedByteCodec.u8 0 Anneal.ByteCodec.FixedByteCodec.u8 2

theorem u8Fields_lenses :
    Anneal.FunctionalTranslation.LawfulMutLens u8FieldA u8FieldsValid ∧
      Anneal.FunctionalTranslation.LawfulMutLens u8FieldB u8FieldsValid ∧
      Anneal.SepLogicLenses.IndependentLenses u8FieldA u8FieldB u8FieldsValid :=
  subplaceFieldLens_disjoint _ _ 0 2 0 0 (Or.inr (Or.inr (Or.inl (by decide))))

theorem u8FieldsValid_init (a p b : UInt8) :
    u8FieldsValid [.init a none, .init p none, .init b none] :=
  ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩

/-- Six symbolic field mutations on trusted bytes, discharged by
`applyFieldWrites_spec` (no byte-list unfolding). -/
theorem u8Fields_six_mutations (a p b x₁ x₂ x₃ x₄ x₅ x₆ : UInt8) :
    let m := applyFieldWrites u8FieldA u8FieldB
      [.inl x₁, .inr x₂, .inl x₃, .inl x₄, .inr x₅, .inr x₆] [.init a none, .init p none, .init b none]
    u8FieldA.readView m = x₄ ∧ u8FieldB.readView m = x₆ := by
  obtain ⟨hL₁, hL₂, hI⟩ := u8Fields_lenses
  obtain ⟨_, h₁, h₂⟩ := applyFieldWrites_spec hL₁ hL₂ hI
    [.inl x₁, .inr x₂, .inl x₃, .inl x₄, .inr x₅, .inr x₆] _ (u8FieldsValid_init a p b)
  exact ⟨h₁, h₂⟩

end TypedAtLenses

/-! ## 9. Two-stage Tree Borrows protector release with a pre-release `reborrowFootprint` -/

section TreeBorrows

open Trusted.Rustc.V2026_06_01.MirAst (Mutability)

abbrev BorTag := Nat
abbrev CallId := Nat

/-- Half-open byte range `[lo, hi)`. -/
structure ByteRange where
  lo : Nat
  hi : Nat
  deriving DecidableEq, Repr

def ByteRange.contains (r : ByteRange) (b : Nat) : Bool :=
  Nat.ble r.lo b && Nat.blt b r.hi

theorem ByteRange.contains_iff (r : ByteRange) (b : Nat) :
    r.contains b = true ↔ r.lo ≤ b ∧ b < r.hi := by
  simp only [ByteRange.contains, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]

theorem ByteRange.contains_eq_false (r : ByteRange) (b : Nat) (h : ¬ (r.lo ≤ b ∧ b < r.hi)) :
    r.contains b = false := by
  cases hc : r.contains b with
  | false => rfl
  | true => exact absurd ((r.contains_iff b).mp hc) h

def ByteRange.Sub (r₁ r₂ : ByteRange) : Prop :=
  ∀ b, r₁.contains b = true → r₂.contains b = true

def ByteRange.Disjoint (r₁ r₂ : ByteRange) : Prop :=
  ∀ b, r₁.contains b = true → r₂.contains b = false

theorem ByteRange.Sub.refl (r : ByteRange) : r.Sub r := fun _ h => h

theorem ByteRange.Disjoint.symm {r₁ r₂ : ByteRange} (h : r₁.Disjoint r₂) : r₂.Disjoint r₁ := by
  intro b hb2
  cases hb1 : r₁.contains b with
  | false => rfl
  | true =>
    have h2 := h b hb1
    rw [hb2] at h2
    cases h2

/-- Argument range of `slice::split_at_mut` on `[base, base + len)`. -/
def wholeRange (base len : Nat) : ByteRange := ⟨base, base + len⟩

/-- Left half `[base, base + mid)`. -/
def splitLeft (base mid : Nat) : ByteRange := ⟨base, base + mid⟩

/-- Right half `[base + mid, base + len)`. -/
def splitRight (base mid len : Nat) : ByteRange := ⟨base + mid, base + len⟩

theorem split_disjoint (base mid len : Nat) : (splitLeft base mid).Disjoint (splitRight base mid len) := by
  intro b hb
  rw [ByteRange.contains_iff] at hb
  apply ByteRange.contains_eq_false
  simp only [splitRight, splitLeft] at hb ⊢
  omega

theorem splitLeft_sub {base mid len : Nat} (hmid : mid ≤ len) :
    (splitLeft base mid).Sub (wholeRange base len) := by
  intro b hb
  rw [ByteRange.contains_iff] at hb ⊢
  simp only [splitLeft, wholeRange] at hb ⊢
  exact ⟨by omega, by omega⟩

theorem splitRight_sub (base mid len : Nat) : (splitRight base mid len).Sub (wholeRange base len) := by
  intro b hb
  rw [ByteRange.contains_iff] at hb ⊢
  simp only [splitRight, wholeRange] at hb ⊢
  exact ⟨by omega, by omega⟩

/-- The two halves cover the whole argument range (for `mid ≤ len`). -/
theorem split_cover (base mid len : Nat) (b : Nat)
    (hb : (wholeRange base len).contains b = true) :
    (splitLeft base mid).contains b = true ∨ (splitRight base mid len).contains b = true := by
  rw [ByteRange.contains_iff] at hb
  simp only [wholeRange] at hb
  by_cases h : b < base + mid
  · left; rw [ByteRange.contains_iff]; simp only [splitLeft]; exact ⟨by omega, by omega⟩
  · right; rw [ByteRange.contains_iff]; simp only [splitRight]; exact ⟨by omega, by omega⟩

/-- Tree Borrows permissions: `ReservedFrz`, `ReservedIM`, `Active` (Miri's
`Unique`), `Frozen`, `Disabled` (`Cell` is out of scope: no interior mutability). -/
inductive Permission where
  | reservedFrz (conflicted : Bool)
  | reservedIM
  | active
  | frozen
  | disabled
  deriving DecidableEq, Repr

/-- Per-byte state of a tag: permission and the `accessed` (initialized) flag. -/
structure LocationState where
  perm : Permission
  accessed : Bool
  deriving DecidableEq, Repr

inductive AccessKind where
  | read
  | write
  deriving DecidableEq, Repr

inductive AccessRelatedness where
  | localAccess
  | foreignAccess
  deriving DecidableEq, Repr

inductive ProtectorKind where
  | weak (callId : CallId)
  | strong (callId : CallId)
  deriving DecidableEq, Repr

def ProtectorKind.callId : ProtectorKind → CallId
  | .weak c => c
  | .strong c => c

/-- Implicit access performed at protector end for an accessed location. -/
def Permission.associatedAccess : Permission → AccessKind
  | .active => .write
  | _ => .read

/-- Per-location transition; `none` is undefined behavior. -/
def performTransition (kind : AccessKind) (rel : AccessRelatedness) (isProtected : Bool)
    (st : LocationState) : Option LocationState :=
  match rel, kind with
  | .localAccess, .read =>
    match st.perm with
    | .disabled => none
    | p => some ⟨p, true⟩
  | .localAccess, .write =>
    match st.perm with
    | .reservedFrz true => if isProtected then none else some ⟨.active, true⟩
    | .reservedFrz false => some ⟨.active, true⟩
    | .reservedIM => some ⟨.active, true⟩
    | .active => some ⟨.active, true⟩
    | .frozen => none
    | .disabled => none
  | .foreignAccess, .read =>
    match st.perm with
    | .reservedFrz c => some ⟨.reservedFrz (isProtected || c), st.accessed⟩
    | .reservedIM => some ⟨.reservedIM, st.accessed⟩
    | .active => if isProtected then none else some ⟨.frozen, st.accessed⟩
    | .frozen => some ⟨.frozen, st.accessed⟩
    | .disabled => some ⟨.disabled, st.accessed⟩
  | .foreignAccess, .write =>
    match st.perm with
    | .reservedIM =>
      if isProtected then (if st.accessed then none else some ⟨.disabled, st.accessed⟩)
      else some ⟨.reservedIM, st.accessed⟩
    | _ => if isProtected && st.accessed then none else some ⟨.disabled, st.accessed⟩

inductive ChildrenVisitMode where
  | visitChildrenOfAccessed
  | skipChildrenOfAccessed
  deriving DecidableEq, Repr

/-- Arbitrary-depth, arbitrary-branching borrow tree of one allocation. -/
structure BorrowTree where
  present : BorTag → Bool
  isAnc : BorTag → BorTag → Bool
  protector : BorTag → Option ProtectorKind
  locState : BorTag → Nat → LocationState

/-- Well-formed ancestry (a forest order with linearly ordered ancestors). -/
structure TreeWF (tree : BorrowTree) : Prop where
  isAnc_refl : ∀ t, tree.present t = true → tree.isAnc t t = true
  isAnc_trans : ∀ a b c, tree.isAnc a b = true → tree.isAnc b c = true → tree.isAnc a c = true
  isAnc_antisymm : ∀ a b, tree.isAnc a b = true → tree.isAnc b a = true → a = b
  isAnc_present_left : ∀ a b, tree.isAnc a b = true → tree.present a = true
  isAnc_present_right : ∀ a b, tree.isAnc a b = true → tree.present b = true
  anc_linear : ∀ a b c, tree.isAnc a c = true → tree.isAnc b c = true →
    tree.isAnc a b = true ∨ tree.isAnc b a = true

/-- Set of active call ids (`GlobalState` protector frames). -/
abbrev ActiveProtectors := CallId → Bool

def BorrowTree.isTagProtected (tree : BorrowTree) (t : BorTag) (active : ActiveProtectors) : Bool :=
  match tree.protector t with
  | some p => active p.callId
  | none => false

/-- Relatedness of node `n` to an access at `start`; `skipChildrenOfAccessed`
skips strict descendants of `start` (`none`). -/
def nodeAccessRelatedness (tree : BorrowTree) (start : BorTag) (mode : ChildrenVisitMode)
    (n : BorTag) : Option AccessRelatedness :=
  if tree.isAnc n start then some .localAccess
  else
    match mode with
    | .visitChildrenOfAccessed => some .foreignAccess
    | .skipChildrenOfAccessed => if tree.isAnc start n then none else some .foreignAccess

/-- No node traps on an access of `kind` at `start` over `range`. -/
def TreeAccessNoUB (tree : BorrowTree) (start : BorTag) (kind : AccessKind) (range : ByteRange)
    (active : ActiveProtectors) (mode : ChildrenVisitMode) : Prop :=
  ∀ n b, tree.present n = true → range.contains b = true →
    match nodeAccessRelatedness tree start mode n with
    | some rel =>
      (performTransition kind rel (tree.isTagProtected n active) (tree.locState n b)).isSome = true
    | none => True

/-- Tree update for an access (paired with `TreeAccessNoUB` for UB-freedom). -/
def applyTreeAccess (tree : BorrowTree) (start : BorTag) (kind : AccessKind) (range : ByteRange)
    (active : ActiveProtectors) (mode : ChildrenVisitMode) : BorrowTree :=
  { tree with
    locState := fun n b =>
      if tree.present n && range.contains b then
        match nodeAccessRelatedness tree start mode n with
        | some rel =>
          match performTransition kind rel (tree.isTagProtected n active) (tree.locState n b) with
          | some st' => st'
          | none => tree.locState n b
        | none => tree.locState n b
      else tree.locState n b }

theorem applyTreeAccess_locState_in (tree : BorrowTree) (start : BorTag) (kind : AccessKind)
    (range : ByteRange) (active : ActiveProtectors) (mode : ChildrenVisitMode) (n : BorTag)
    (b : Nat) (hPres : tree.present n = true) (hb : range.contains b = true) :
    (applyTreeAccess tree start kind range active mode).locState n b =
      match nodeAccessRelatedness tree start mode n with
      | some rel =>
        match performTransition kind rel (tree.isTagProtected n active) (tree.locState n b) with
        | some st' => st'
        | none => tree.locState n b
      | none => tree.locState n b := by
  simp only [applyTreeAccess, hPres, hb, Bool.and_self, ↓reduceIte]

theorem applyTreeAccess_locState_out (tree : BorrowTree) (start : BorTag) (kind : AccessKind)
    (range : ByteRange) (active : ActiveProtectors) (mode : ChildrenVisitMode) (n : BorTag)
    (b : Nat) (hb : range.contains b = false) :
    (applyTreeAccess tree start kind range active mode).locState n b = tree.locState n b := by
  simp only [applyTreeAccess, hb, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

/-- Insert a fresh child node (before the retag's initial child read). -/
def insertChildNode (tree : BorrowTree) (t_parent t_child : BorTag) (prot : Option ProtectorKind)
    (initPerm : Permission) : BorrowTree where
  present t := decide (t = t_child) || tree.present t
  isAnc a d :=
    if d = t_child then decide (a = t_child) || tree.isAnc a t_parent
    else if a = t_child then false
    else tree.isAnc a d
  protector t := if t = t_child then prot else tree.protector t
  locState t b := if t = t_child then ⟨initPerm, false⟩ else tree.locState t b

/-- Retag (`Miri` `RetagMode::Default` / `FnEntry`): insert a child and perform
the initial child read over `range`. -/
def retagChild (tree : BorrowTree) (t_parent t_child : BorTag) (prot : Option ProtectorKind)
    (initPerm : Permission) (range : ByteRange) (active : ActiveProtectors) : BorrowTree :=
  applyTreeAccess (insertChildNode tree t_parent t_child prot initPerm) t_child .read range active
    .visitChildrenOfAccessed

/-- Stage 1 of protector release is UB-free (implicit access with
`skipChildrenOfAccessed` while the call id is still active). -/
def releaseProtectorNoUB (tree : BorrowTree) (t_rel : BorTag) (active : ActiveProtectors) : Prop :=
  ∀ n b, tree.present n = true → (tree.locState t_rel b).accessed = true →
    match nodeAccessRelatedness tree t_rel .skipChildrenOfAccessed n with
    | some rel =>
      (performTransition (tree.locState t_rel b).perm.associatedAccess rel
        (tree.isTagProtected n active) (tree.locState n b)).isSome = true
    | none => True

/-- Stage 1 of protector release (`ChildrenVisitMode.SkipChildrenOfAccessed`
while the call id is active). -/
def applyReleaseProtector (tree : BorrowTree) (t_rel : BorTag) (active : ActiveProtectors) :
    BorrowTree :=
  { tree with
    locState := fun n b =>
      if tree.present n && (tree.locState t_rel b).accessed then
        match nodeAccessRelatedness tree t_rel .skipChildrenOfAccessed n with
        | some rel =>
          match performTransition (tree.locState t_rel b).perm.associatedAccess rel
              (tree.isTagProtected n active) (tree.locState n b) with
          | some st' => st'
          | none => tree.locState n b
        | none => tree.locState n b
      else tree.locState n b }

theorem applyReleaseProtector_locState_acc (tree : BorrowTree) (t_rel : BorTag)
    (active : ActiveProtectors) (n : BorTag) (b : Nat) (hPres : tree.present n = true)
    (hAcc : (tree.locState t_rel b).accessed = true) :
    (applyReleaseProtector tree t_rel active).locState n b =
      match nodeAccessRelatedness tree t_rel .skipChildrenOfAccessed n with
      | some rel =>
        match performTransition (tree.locState t_rel b).perm.associatedAccess rel
            (tree.isTagProtected n active) (tree.locState n b) with
        | some st' => st'
        | none => tree.locState n b
      | none => tree.locState n b := by
  simp only [applyReleaseProtector, hPres, hAcc, Bool.and_self, ↓reduceIte]

theorem applyReleaseProtector_locState_unacc (tree : BorrowTree) (t_rel : BorTag)
    (active : ActiveProtectors) (n : BorTag) (b : Nat)
    (hAcc : (tree.locState t_rel b).accessed = false) :
    (applyReleaseProtector tree t_rel active).locState n b = tree.locState n b := by
  simp only [applyReleaseProtector, hAcc, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

/-- Stage 2 of protector release (`GlobalState.endCall`): drop the call id. -/
def removeActiveProtector (active : ActiveProtectors) (callId : CallId) : ActiveProtectors :=
  fun c => if c = callId then false else active c

/-- Function entry pushes a fresh call id. -/
def insertActiveProtector (active : ActiveProtectors) (callId : CallId) : ActiveProtectors :=
  fun c => decide (c = callId) || active c

/-- Ancestor states that support local reads and writes without protector UB. -/
def AncestorWritable (st : LocationState) : Prop :=
  st.perm = .active ∨ st.perm = .reservedFrz false ∨ st.perm = .reservedIM

instance (st : LocationState) : Decidable (AncestorWritable st) :=
  inferInstanceAs (Decidable (st.perm = .active ∨ st.perm = .reservedFrz false ∨ st.perm = .reservedIM))

/-- Non-ancestor states that never trap under foreign reads or writes. -/
def NonAncestorSafe (st : LocationState) (isProt : Bool) : Prop :=
  isProt = false ∨ (st.accessed = false ∧ st.perm ≠ .active)

instance (st : LocationState) (isProt : Bool) : Decidable (NonAncestorSafe st isProt) :=
  inferInstanceAs (Decidable (isProt = false ∨ (st.accessed = false ∧ st.perm ≠ .active)))

/-- **`HasUniqueWritePerm`**: every ancestor of `tag` is writable on `range` and
every non-ancestor is isolated (`NonAncestorSafe`). -/
structure HasUniqueWritePerm (tree : BorrowTree) (tag : BorTag) (range : ByteRange)
    (active : ActiveProtectors) : Prop where
  wf : TreeWF tree
  tag_present : tree.present tag = true
  ancestors_writable : ∀ anc b, tree.isAnc anc tag = true → range.contains b = true →
    AncestorWritable (tree.locState anc b)
  non_ancestors_safe : ∀ other b, tree.present other = true → tree.isAnc other tag = false →
    range.contains b = true → NonAncestorSafe (tree.locState other b) (tree.isTagProtected other active)

theorem performTransition_local_of_ancestorWritable (kind : AccessKind) (isProt : Bool)
    (st : LocationState) (h : AncestorWritable st) :
    ∃ st', performTransition kind .localAccess isProt st = some st' ∧
      AncestorWritable st' ∧ st'.accessed = true := by
  rcases st with ⟨perm, acc⟩
  rcases h with h | h | h <;> (simp only at h; subst h) <;> cases kind <;> cases acc <;>
    exact ⟨_, rfl, by decide, rfl⟩

theorem performTransition_local_write_of_ancestorWritable (isProt : Bool) (st : LocationState)
    (h : AncestorWritable st) :
    performTransition .write .localAccess isProt st = some ⟨.active, true⟩ := by
  rcases st with ⟨perm, acc⟩
  rcases h with h | h | h <;> (simp only at h; subst h) <;> rfl

theorem performTransition_foreign_of_nonAncestorSafe (kind : AccessKind) (isProt : Bool)
    (st : LocationState) (h : NonAncestorSafe st isProt) :
    ∃ st', performTransition kind .foreignAccess isProt st = some st' ∧
      NonAncestorSafe st' isProt ∧ st'.accessed = st.accessed := by
  rcases st with ⟨perm, acc⟩
  rcases perm with (_ | _) | _ | _ | _ | _ <;> cases kind <;> cases isProt <;> cases acc <;>
    first
    | exact ⟨_, rfl, by decide, rfl⟩
    | exact absurd h (by decide)

theorem nonAncestorSafe_mono_unprotect (st : LocationState) (isProt1 isProt2 : Bool)
    (hSafe : NonAncestorSafe st isProt1) (hImp : isProt2 = true → isProt1 = true) :
    NonAncestorSafe st isProt2 := by
  rcases hSafe with hUnprot | hUnacc
  · left
    cases h2 : isProt2 with
    | false => rfl
    | true =>
      have h1 := hImp h2
      rw [hUnprot] at h1
      cases h1
  · exact Or.inr hUnacc

theorem insertChildNode_present (tree : BorrowTree) (t_parent t_child : BorTag)
    (prot : Option ProtectorKind) (initPerm : Permission) (t : BorTag) :
    (insertChildNode tree t_parent t_child prot initPerm).present t =
      (decide (t = t_child) || tree.present t) := rfl

theorem insertChildNode_isAnc_child (tree : BorrowTree) (t_parent t_child : BorTag)
    (prot : Option ProtectorKind) (initPerm : Permission) (a : BorTag) :
    (insertChildNode tree t_parent t_child prot initPerm).isAnc a t_child =
      (decide (a = t_child) || tree.isAnc a t_parent) := by
  show (if t_child = t_child then _ else _) = _
  rw [ite_eq_left rfl]

theorem insertChildNode_isAnc_of_ne (tree : BorrowTree) (t_parent t_child : BorTag)
    (prot : Option ProtectorKind) (initPerm : Permission) {a d : BorTag}
    (hd : d ≠ t_child) (ha : a ≠ t_child) :
    (insertChildNode tree t_parent t_child prot initPerm).isAnc a d = tree.isAnc a d := by
  show (if d = t_child then _ else if a = t_child then false else _) = _
  rw [ite_eq_right hd, ite_eq_right ha]

theorem insertChildNode_isAnc_from_child (tree : BorrowTree) (t_parent t_child : BorTag)
    (prot : Option ProtectorKind) (initPerm : Permission) {d : BorTag} (hd : d ≠ t_child) :
    (insertChildNode tree t_parent t_child prot initPerm).isAnc t_child d = false := by
  show (if d = t_child then _ else if t_child = t_child then false else _) = _
  rw [ite_eq_right hd, ite_eq_left rfl]

theorem insertChildNode_locState_of_ne (tree : BorrowTree) (t_parent t_child : BorTag)
    (prot : Option ProtectorKind) (initPerm : Permission) {t : BorTag} (ht : t ≠ t_child) (b : Nat) :
    (insertChildNode tree t_parent t_child prot initPerm).locState t b = tree.locState t b := by
  show (if t = t_child then _ else _) = _
  rw [ite_eq_right ht]

theorem insertChildNode_locState_child (tree : BorrowTree) (t_parent t_child : BorTag)
    (prot : Option ProtectorKind) (initPerm : Permission) (b : Nat) :
    (insertChildNode tree t_parent t_child prot initPerm).locState t_child b = ⟨initPerm, false⟩ := by
  show (if t_child = t_child then _ else _) = _
  rw [ite_eq_left rfl]

theorem insertChildNode_isTagProtected_of_ne (tree : BorrowTree) (t_parent t_child : BorTag)
    (prot : Option ProtectorKind) (initPerm : Permission) {t : BorTag} (ht : t ≠ t_child)
    (active : ActiveProtectors) :
    (insertChildNode tree t_parent t_child prot initPerm).isTagProtected t active =
      tree.isTagProtected t active := by
  unfold BorrowTree.isTagProtected
  show (match (if t = t_child then prot else tree.protector t) with
    | some p => active p.callId | none => false) = _
  rw [ite_eq_right ht]

theorem insertChildNode_isTagProtected_child_none (tree : BorrowTree) (t_parent t_child : BorTag)
    (initPerm : Permission) (active : ActiveProtectors) :
    (insertChildNode tree t_parent t_child none initPerm).isTagProtected t_child active = false := by
  unfold BorrowTree.isTagProtected
  show (match (if t_child = t_child then none else tree.protector t_child) with
    | some p => active p.callId | none => false) = _
  rw [ite_eq_left rfl]

theorem ne_of_present_of_fresh {tree : BorrowTree} {x t : BorTag}
    (hx : tree.present x = true) (hFresh : tree.present t = false) : x ≠ t := by
  intro hEq
  rw [hEq, hFresh] at hx
  cases hx

theorem insertChildNode_wf (tree : BorrowTree) (t_parent t_child : BorTag)
    (prot : Option ProtectorKind) (initPerm : Permission) (hwf : TreeWF tree)
    (hFresh : tree.present t_child = false) :
    TreeWF (insertChildNode tree t_parent t_child prot initPerm) := by
  have hNe : ∀ x, tree.present x = true → x ≠ t_child := fun x hx => ne_of_present_of_fresh hx hFresh
  -- ancestry into the child: `a` is the child or an ancestor of the parent
  have hIntoChild : ∀ a, (insertChildNode tree t_parent t_child prot initPerm).isAnc a t_child = true →
      a = t_child ∨ tree.isAnc a t_parent = true := by
    intro a h
    rw [insertChildNode_isAnc_child, Bool.or_eq_true, decide_eq_true_iff] at h
    exact h
  -- ancestry not involving the child is the old ancestry
  have hOld : ∀ a d, d ≠ t_child →
      (insertChildNode tree t_parent t_child prot initPerm).isAnc a d = true →
      a ≠ t_child ∧ tree.isAnc a d = true := by
    intro a d hd h
    by_cases ha : a = t_child
    · subst ha
      rw [insertChildNode_isAnc_from_child _ _ _ _ _ hd] at h
      cases h
    · exact ⟨ha, by rwa [insertChildNode_isAnc_of_ne _ _ _ _ _ hd ha] at h⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    by_cases htc : t = t_child
    · subst htc
      rw [insertChildNode_isAnc_child, decide_eq_true rfl, Bool.true_or]
    · rw [insertChildNode_isAnc_of_ne _ _ _ _ _ htc htc]
      rw [insertChildNode_present, decide_eq_false htc, Bool.false_or] at ht
      exact hwf.isAnc_refl t ht
  · intro a b c hab hbc
    by_cases hct : c = t_child
    · subst hct
      rw [insertChildNode_isAnc_child, Bool.or_eq_true, decide_eq_true_iff]
      rcases hIntoChild b hbc with hb | hb
      · subst hb
        rcases hIntoChild a hab with ha | ha
        · exact Or.inl ha
        · exact Or.inr ha
      · have hbne : b ≠ c := hNe b (hwf.isAnc_present_left b t_parent hb)
        obtain ⟨_, hab'⟩ := hOld a b hbne hab
        exact Or.inr (hwf.isAnc_trans a b t_parent hab' hb)
    · obtain ⟨hbne, hbc'⟩ := hOld b c hct hbc
      obtain ⟨hane, hab'⟩ := hOld a b hbne hab
      rw [insertChildNode_isAnc_of_ne _ _ _ _ _ hct hane]
      exact hwf.isAnc_trans a b c hab' hbc'
  · intro a b hab hba
    by_cases hbt : b = t_child
    · subst hbt
      by_cases hat : a = b
      · exact hat
      · obtain ⟨hbne, _⟩ := hOld b a hat hba
        exact absurd rfl hbne
    · obtain ⟨hane, hab'⟩ := hOld a b hbt hab
      obtain ⟨_, hba'⟩ := hOld b a hane hba
      exact hwf.isAnc_antisymm a b hab' hba'
  · intro a b hab
    rw [insertChildNode_present, Bool.or_eq_true, decide_eq_true_iff]
    by_cases hbt : b = t_child
    · subst hbt
      rcases hIntoChild a hab with ha | ha
      · exact Or.inl ha
      · exact Or.inr (hwf.isAnc_present_left a t_parent ha)
    · obtain ⟨_, hab'⟩ := hOld a b hbt hab
      exact Or.inr (hwf.isAnc_present_left a b hab')
  · intro a b hab
    rw [insertChildNode_present, Bool.or_eq_true, decide_eq_true_iff]
    by_cases hbt : b = t_child
    · exact Or.inl hbt
    · obtain ⟨_, hab'⟩ := hOld a b hbt hab
      exact Or.inr (hwf.isAnc_present_right a b hab')
  · intro a b c hac hbc
    by_cases hct : c = t_child
    · rw [hct] at hac hbc
      rcases hIntoChild a hac with ha | ha
      · right
        rw [ha]
        exact hbc
      · rcases hIntoChild b hbc with hb | hb
        · left
          rw [hb]
          exact hac
        · have hane := hNe a (hwf.isAnc_present_left a t_parent ha)
          have hbne := hNe b (hwf.isAnc_present_left b t_parent hb)
          rw [insertChildNode_isAnc_of_ne _ _ _ _ _ hbne hane,
            insertChildNode_isAnc_of_ne _ _ _ _ _ hane hbne]
          exact hwf.anc_linear a b t_parent ha hb
    · obtain ⟨hane, hac'⟩ := hOld a c hct hac
      obtain ⟨hbne, hbc'⟩ := hOld b c hct hbc
      rw [insertChildNode_isAnc_of_ne _ _ _ _ _ hbne hane,
        insertChildNode_isAnc_of_ne _ _ _ _ _ hane hbne]
      exact hwf.anc_linear a b c hac' hbc'

theorem applyTreeAccess_wf (tree : BorrowTree) (start : BorTag) (kind : AccessKind)
    (range : ByteRange) (active : ActiveProtectors) (mode : ChildrenVisitMode)
    (hwf : TreeWF tree) : TreeWF (applyTreeAccess tree start kind range active mode) :=
  ⟨hwf.isAnc_refl, hwf.isAnc_trans, hwf.isAnc_antisymm,
   hwf.isAnc_present_left, hwf.isAnc_present_right, hwf.anc_linear⟩

theorem applyReleaseProtector_wf (tree : BorrowTree) (t_rel : BorTag) (active : ActiveProtectors)
    (hwf : TreeWF tree) : TreeWF (applyReleaseProtector tree t_rel active) :=
  ⟨hwf.isAnc_refl, hwf.isAnc_trans, hwf.isAnc_antisymm,
   hwf.isAnc_present_left, hwf.isAnc_present_right, hwf.anc_linear⟩

theorem nodeAccessRelatedness_anc {tree : BorrowTree} {start n : BorTag} {mode : ChildrenVisitMode}
    (h : tree.isAnc n start = true) : nodeAccessRelatedness tree start mode n = some .localAccess := by
  unfold nodeAccessRelatedness
  rw [ite_eq_left h]

theorem nodeAccessRelatedness_visit_foreign {tree : BorrowTree} {start n : BorTag}
    (h : tree.isAnc n start = false) :
    nodeAccessRelatedness tree start .visitChildrenOfAccessed n = some .foreignAccess := by
  unfold nodeAccessRelatedness
  rw [ite_eq_right (by rw [h]; exact Bool.false_ne_true)]

theorem nodeAccessRelatedness_skip_desc {tree : BorrowTree} {start n : BorTag}
    (h : tree.isAnc n start = false) (hd : tree.isAnc start n = true) :
    nodeAccessRelatedness tree start .skipChildrenOfAccessed n = none := by
  unfold nodeAccessRelatedness
  rw [ite_eq_right (by rw [h]; exact Bool.false_ne_true)]
  show (if tree.isAnc start n = true then none else some AccessRelatedness.foreignAccess) = none
  rw [ite_eq_left hd]

theorem nodeAccessRelatedness_skip_foreign {tree : BorrowTree} {start n : BorTag}
    (h : tree.isAnc n start = false) (hd : tree.isAnc start n = false) :
    nodeAccessRelatedness tree start .skipChildrenOfAccessed n = some .foreignAccess := by
  unfold nodeAccessRelatedness
  rw [ite_eq_right (by rw [h]; exact Bool.false_ne_true)]
  show (if tree.isAnc start n = true then none else some AccessRelatedness.foreignAccess) = _
  rw [ite_eq_right (by rw [hd]; exact Bool.false_ne_true)]

theorem hasUniqueWritePerm_narrow {tree : BorrowTree} {tag : BorTag} {r₁ r₂ : ByteRange}
    {active : ActiveProtectors} (hPerm : HasUniqueWritePerm tree tag r₂ active) (hSub : r₁.Sub r₂) :
    HasUniqueWritePerm tree tag r₁ active where
  wf := hPerm.wf
  tag_present := hPerm.tag_present
  ancestors_writable := fun anc b hAnc hb => hPerm.ancestors_writable anc b hAnc (hSub b hb)
  non_ancestors_safe := fun other b hPres hNotAnc hb =>
    hPerm.non_ancestors_safe other b hPres hNotAnc (hSub b hb)

/-- Local accesses through `tag` inside its range are UB-free and preserve
`HasUniqueWritePerm`. -/
theorem local_access_preserves_hasUniqueWritePerm {tree : BorrowTree} {tag : BorTag}
    {range subRange : ByteRange} {active : ActiveProtectors} (kind : AccessKind)
    (hPerm : HasUniqueWritePerm tree tag range active) (hSub : subRange.Sub range) :
    TreeAccessNoUB tree tag kind subRange active .visitChildrenOfAccessed ∧
      HasUniqueWritePerm (applyTreeAccess tree tag kind subRange active .visitChildrenOfAccessed)
        tag range active := by
  constructor
  · intro n b hPres hbSub
    have hbRange := hSub b hbSub
    cases hAnc : tree.isAnc n tag with
    | true =>
      rw [nodeAccessRelatedness_anc hAnc]
      obtain ⟨st', hEq, _⟩ := performTransition_local_of_ancestorWritable kind
        (tree.isTagProtected n active) (tree.locState n b) (hPerm.ancestors_writable n b hAnc hbRange)
      show (performTransition kind .localAccess _ _).isSome = true
      rw [hEq]; rfl
    | false =>
      rw [nodeAccessRelatedness_visit_foreign hAnc]
      obtain ⟨st', hEq, _⟩ := performTransition_foreign_of_nonAncestorSafe kind
        (tree.isTagProtected n active) (tree.locState n b)
        (hPerm.non_ancestors_safe n b hPres hAnc hbRange)
      show (performTransition kind .foreignAccess _ _).isSome = true
      rw [hEq]; rfl
  · refine ⟨applyTreeAccess_wf tree tag kind subRange active .visitChildrenOfAccessed hPerm.wf,
      hPerm.tag_present, ?_, ?_⟩
    · intro anc b hAnc hbRange
      have hAncOrig : tree.isAnc anc tag = true := hAnc
      have hPresAnc : tree.present anc = true := hPerm.wf.isAnc_present_left anc tag hAncOrig
      cases hbSub : subRange.contains b with
      | true =>
        rw [applyTreeAccess_locState_in tree tag kind subRange active .visitChildrenOfAccessed
          anc b hPresAnc hbSub, nodeAccessRelatedness_anc hAncOrig]
        obtain ⟨st', hEq, hAw, _⟩ := performTransition_local_of_ancestorWritable kind
          (tree.isTagProtected anc active) (tree.locState anc b)
          (hPerm.ancestors_writable anc b hAncOrig hbRange)
        show AncestorWritable (match performTransition kind .localAccess _ _ with
          | some st' => st' | none => _)
        rw [hEq]
        exact hAw
      | false =>
        rw [applyTreeAccess_locState_out tree tag kind subRange active .visitChildrenOfAccessed
          anc b hbSub]
        exact hPerm.ancestors_writable anc b hAncOrig hbRange
    · intro other b hPres hNotAnc hbRange
      have hPresOrig : tree.present other = true := hPres
      have hNotAncOrig : tree.isAnc other tag = false := hNotAnc
      show NonAncestorSafe _ (tree.isTagProtected other active)
      cases hbSub : subRange.contains b with
      | true =>
        rw [applyTreeAccess_locState_in tree tag kind subRange active .visitChildrenOfAccessed
          other b hPresOrig hbSub, nodeAccessRelatedness_visit_foreign hNotAncOrig]
        obtain ⟨st', hEq, hSafe, _⟩ := performTransition_foreign_of_nonAncestorSafe kind
          (tree.isTagProtected other active) (tree.locState other b)
          (hPerm.non_ancestors_safe other b hPresOrig hNotAncOrig hbRange)
        show NonAncestorSafe (match performTransition kind .foreignAccess _ _ with
          | some st' => st' | none => _) _
        rw [hEq]
        exact hSafe
      | false =>
        rw [applyTreeAccess_locState_out tree tag kind subRange active .visitChildrenOfAccessed
          other b hbSub]
        exact hPerm.non_ancestors_safe other b hPresOrig hNotAncOrig hbRange

/-- A local write through `tag` activates `tag` and all its ancestors on the
written bytes. -/
theorem local_write_activates_ancestors {tree : BorrowTree} {tag anc : BorTag}
    {range subRange : ByteRange} {active : ActiveProtectors} {b : Nat}
    (hPerm : HasUniqueWritePerm tree tag range active) (hSub : subRange.Sub range)
    (hAnc : tree.isAnc anc tag = true) (hb : subRange.contains b = true) :
    (applyTreeAccess tree tag .write subRange active .visitChildrenOfAccessed).locState anc b =
      ⟨.active, true⟩ := by
  have hPresAnc : tree.present anc = true := hPerm.wf.isAnc_present_left anc tag hAnc
  rw [applyTreeAccess_locState_in tree tag .write subRange active .visitChildrenOfAccessed
    anc b hPresAnc hb, nodeAccessRelatedness_anc hAnc]
  show (match performTransition .write .localAccess _ _ with | some st' => st' | none => _) = _
  rw [performTransition_local_write_of_ancestorWritable _ _
    (hPerm.ancestors_writable anc b hAnc (hSub b hb))]

/-- Retagging a fresh child `t_child` (with a writable initial permission) under
`t_parent` on `childRange ⊆ parentRange` is UB-free and establishes
`HasUniqueWritePerm` for the child. -/
theorem retagChild_hasUniqueWritePerm {tree : BorrowTree} {t_parent t_child : BorTag}
    {parentRange childRange : ByteRange} {active : ActiveProtectors}
    (prot : Option ProtectorKind) {initPerm : Permission}
    (hInit : AncestorWritable ⟨initPerm, false⟩)
    (hPerm : HasUniqueWritePerm tree t_parent parentRange active)
    (hSub : childRange.Sub parentRange) (hFresh : tree.present t_child = false) :
    TreeAccessNoUB (insertChildNode tree t_parent t_child prot initPerm) t_child .read childRange
        active .visitChildrenOfAccessed ∧
      HasUniqueWritePerm (retagChild tree t_parent t_child prot initPerm childRange active)
        t_child childRange active := by
  have hwf1 := insertChildNode_wf tree t_parent t_child prot initPerm hPerm.wf hFresh
  have hPre : HasUniqueWritePerm (insertChildNode tree t_parent t_child prot initPerm) t_child
      childRange active := by
    refine ⟨hwf1, by rw [insertChildNode_present, decide_eq_true rfl, Bool.true_or], ?_, ?_⟩
    · intro anc b hAnc hbChild
      rw [insertChildNode_isAnc_child, Bool.or_eq_true, decide_eq_true_iff] at hAnc
      by_cases hac : anc = t_child
      · rw [hac, insertChildNode_locState_child]
        exact hInit
      · rw [insertChildNode_locState_of_ne _ _ _ _ _ hac]
        rcases hAnc with h | h
        · exact absurd h hac
        · exact hPerm.ancestors_writable anc b h (hSub b hbChild)
    · intro other b hPres hNotAnc hbChild
      rw [insertChildNode_isAnc_child, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hNotAnc
      obtain ⟨hOtherNe, hNotAncOrig⟩ := hNotAnc
      rw [insertChildNode_present, decide_eq_false hOtherNe, Bool.false_or] at hPres
      rw [insertChildNode_isTagProtected_of_ne _ _ _ _ _ hOtherNe,
        insertChildNode_locState_of_ne _ _ _ _ _ hOtherNe]
      exact hPerm.non_ancestors_safe other b hPres hNotAncOrig (hSub b hbChild)
  exact local_access_preserves_hasUniqueWritePerm .read hPre (ByteRange.Sub.refl _)

/-- Retagging an unprotected child keeps the parent's `HasUniqueWritePerm`. -/
theorem retagUnprotectedChild_preserves_parent_hasUniqueWritePerm {tree : BorrowTree}
    {t_parent t_child : BorTag} {parentRange childRange : ByteRange} {active : ActiveProtectors}
    {initPerm : Permission}
    (hPerm : HasUniqueWritePerm tree t_parent parentRange active)
    (hFresh : tree.present t_child = false) :
    HasUniqueWritePerm (retagChild tree t_parent t_child none initPerm childRange active)
      t_parent parentRange active := by
  have hParentNe : t_parent ≠ t_child := ne_of_present_of_fresh hPerm.tag_present hFresh
  let tree1 := insertChildNode tree t_parent t_child none initPerm
  have hwf1 : TreeWF tree1 := insertChildNode_wf tree t_parent t_child none initPerm hPerm.wf hFresh
  refine ⟨applyTreeAccess_wf tree1 t_child .read childRange active .visitChildrenOfAccessed hwf1,
    ?_, ?_, ?_⟩
  · show tree1.present t_parent = true
    rw [insertChildNode_present, hPerm.tag_present, Bool.or_true]
  · intro anc b hAnc hbParent
    have hAnc1 : tree1.isAnc anc t_parent = true := hAnc
    have hAncNe : anc ≠ t_child := by
      intro hEq
      rw [hEq] at hAnc1
      have : tree1.isAnc t_child t_parent = false :=
        insertChildNode_isAnc_from_child _ _ _ _ _ hParentNe
      rw [this] at hAnc1
      cases hAnc1
    have hAncOrig : tree.isAnc anc t_parent = true := by
      rwa [insertChildNode_isAnc_of_ne _ _ _ _ _ hParentNe hAncNe] at hAnc1
    have hPresAnc : tree.present anc = true := hPerm.wf.isAnc_present_left anc t_parent hAncOrig
    have hPres1 : tree1.present anc = true := by
      rw [insertChildNode_present, hPresAnc, Bool.or_true]
    have hAncChild1 : tree1.isAnc anc t_child = true := by
      rw [insertChildNode_isAnc_child, hAncOrig, Bool.or_true]
    have hLoc1 : tree1.locState anc b = tree.locState anc b :=
      insertChildNode_locState_of_ne _ _ _ _ _ hAncNe b
    show AncestorWritable ((applyTreeAccess tree1 t_child .read childRange active
      .visitChildrenOfAccessed).locState anc b)
    cases hbChild : childRange.contains b with
    | true =>
      rw [applyTreeAccess_locState_in tree1 t_child .read childRange active .visitChildrenOfAccessed
        anc b hPres1 hbChild, nodeAccessRelatedness_anc hAncChild1, hLoc1]
      obtain ⟨st', hEq, hAw, _⟩ := performTransition_local_of_ancestorWritable .read
        (tree1.isTagProtected anc active) (tree.locState anc b)
        (hPerm.ancestors_writable anc b hAncOrig hbParent)
      show AncestorWritable (match performTransition .read .localAccess _ _ with
        | some st' => st' | none => _)
      rw [hEq]
      exact hAw
    | false =>
      rw [applyTreeAccess_locState_out tree1 t_child .read childRange active .visitChildrenOfAccessed
        anc b hbChild, hLoc1]
      exact hPerm.ancestors_writable anc b hAncOrig hbParent
  · intro other b hPres hNotAnc hbParent
    have hPres1 : tree1.present other = true := hPres
    have hNotAnc1 : tree1.isAnc other t_parent = false := hNotAnc
    show NonAncestorSafe _ (tree1.isTagProtected other active)
    by_cases hOther : other = t_child
    · left
      rw [hOther]
      exact insertChildNode_isTagProtected_child_none _ _ _ _ _
    · have hPresOrig : tree.present other = true := by
        rwa [insertChildNode_present, decide_eq_false hOther, Bool.false_or] at hPres1
      have hNotAncOrig : tree.isAnc other t_parent = false := by
        rwa [insertChildNode_isAnc_of_ne _ _ _ _ _ hParentNe hOther] at hNotAnc1
      have hNotAncChild1 : tree1.isAnc other t_child = false := by
        rw [insertChildNode_isAnc_child, decide_eq_false hOther, hNotAncOrig, Bool.false_or]
      have hLoc1 : tree1.locState other b = tree.locState other b :=
        insertChildNode_locState_of_ne _ _ _ _ _ hOther b
      have hProt1 : tree1.isTagProtected other active = tree.isTagProtected other active :=
        insertChildNode_isTagProtected_of_ne _ _ _ _ _ hOther active
      rw [hProt1]
      show NonAncestorSafe ((applyTreeAccess tree1 t_child .read childRange active
        .visitChildrenOfAccessed).locState other b) (tree.isTagProtected other active)
      cases hbChild : childRange.contains b with
      | true =>
        rw [applyTreeAccess_locState_in tree1 t_child .read childRange active .visitChildrenOfAccessed
          other b hPres1 hbChild, nodeAccessRelatedness_visit_foreign hNotAncChild1, hLoc1, hProt1]
        obtain ⟨st', hEq, hSafe, _⟩ := performTransition_foreign_of_nonAncestorSafe .read
          (tree.isTagProtected other active) (tree.locState other b)
          (hPerm.non_ancestors_safe other b hPresOrig hNotAncOrig hbParent)
        show NonAncestorSafe (match performTransition .read .foreignAccess _ _ with
          | some st' => st' | none => _) _
        rw [hEq]
        exact hSafe
      | false =>
        rw [applyTreeAccess_locState_out tree1 t_child .read childRange active .visitChildrenOfAccessed
          other b hbChild, hLoc1]
        exact hPerm.non_ancestors_safe other b hPresOrig hNotAncOrig hbParent

theorem retagChild_present (tree : BorrowTree) (t_parent t_child : BorTag)
    (prot : Option ProtectorKind) (initPerm : Permission) (range : ByteRange)
    (active : ActiveProtectors) (t : BorTag) :
    (retagChild tree t_parent t_child prot initPerm range active).present t =
      (decide (t = t_child) || tree.present t) := rfl

theorem retagChild_isAnc (tree : BorrowTree) (t_parent t_child : BorTag)
    (prot : Option ProtectorKind) (initPerm : Permission) (range : ByteRange)
    (active : ActiveProtectors) :
    (retagChild tree t_parent t_child prot initPerm range active).isAnc =
      (insertChildNode tree t_parent t_child prot initPerm).isAnc := rfl

theorem retagChild_isTagProtected (tree : BorrowTree) (t_parent t_child : BorTag)
    (prot : Option ProtectorKind) (initPerm : Permission) (range : ByteRange)
    (active act2 : ActiveProtectors) (t : BorTag) :
    (retagChild tree t_parent t_child prot initPerm range active).isTagProtected t act2 =
      (insertChildNode tree t_parent t_child prot initPerm).isTagProtected t act2 := rfl

theorem retagChild_locState_out (tree : BorrowTree) (t_parent t_child : BorTag)
    (prot : Option ProtectorKind) (initPerm : Permission) (range : ByteRange)
    (active : ActiveProtectors) (n : BorTag) (b : Nat) (hbOut : range.contains b = false) :
    (retagChild tree t_parent t_child prot initPerm range active).locState n b =
      (insertChildNode tree t_parent t_child prot initPerm).locState n b :=
  applyTreeAccess_locState_out _ _ _ _ _ _ n b hbOut

/-- The retagged child is accessed exactly on its range. -/
theorem retagChild_child_accessed {tree : BorrowTree} {t_parent t_child : BorTag}
    {prot : Option ProtectorKind} {initPerm : Permission} {range : ByteRange}
    {active : ActiveProtectors} (hInit : initPerm ≠ .disabled) (b : Nat) :
    ((retagChild tree t_parent t_child prot initPerm range active).locState t_child b).accessed =
      range.contains b := by
  cases hb : range.contains b with
  | true =>
    rw [show retagChild tree t_parent t_child prot initPerm range active =
      applyTreeAccess (insertChildNode tree t_parent t_child prot initPerm) t_child .read range
        active .visitChildrenOfAccessed from rfl,
      applyTreeAccess_locState_in _ _ _ _ _ _ _ _
        (by rw [insertChildNode_present, decide_eq_true rfl, Bool.true_or]) hb,
      nodeAccessRelatedness_anc (by rw [insertChildNode_isAnc_child, decide_eq_true rfl, Bool.true_or]),
      insertChildNode_locState_child]
    cases initPerm with
    | disabled => exact absurd rfl hInit
    | _ => rfl
  | false =>
    rw [retagChild_locState_out _ _ _ _ _ _ _ _ _ hb, insertChildNode_locState_child]

/-- State during a call: `FnEntry`-protected `t_arg` on `parentRange` and an
unprotected descendant `t_ret` on `subRange ⊆ parentRange`. -/
structure CalleeReborrowState (tree : BorrowTree) (t_arg t_ret : BorTag)
    (parentRange subRange : ByteRange) (activeCaller : ActiveProtectors) (callId : CallId) : Prop where
  sub_range : subRange.Sub parentRange
  arg_perm : HasUniqueWritePerm tree t_arg parentRange (insertActiveProtector activeCaller callId)
  ret_present : tree.present t_ret = true
  arg_anc_ret : tree.isAnc t_arg t_ret = true
  ret_ne_arg : t_ret ≠ t_arg
  arg_accessed_in_parent : ∀ b, (tree.locState t_arg b).accessed = true → parentRange.contains b = true
  ret_ancestors_writable : ∀ anc b, tree.isAnc anc t_ret = true → subRange.contains b = true →
    AncestorWritable (tree.locState anc b)
  descendants_unprotected_in_caller : ∀ d, tree.isAnc t_arg d = true → d ≠ t_arg →
    tree.isTagProtected d activeCaller = false

theorem isTagProtected_insert_of_caller {tree : BorrowTree} {t : BorTag}
    {activeCaller : ActiveProtectors} {callId : CallId}
    (h : tree.isTagProtected t activeCaller = true) :
    tree.isTagProtected t (insertActiveProtector activeCaller callId) = true := by
  unfold BorrowTree.isTagProtected at h ⊢
  cases hp : tree.protector t with
  | none => rw [hp] at h; cases h
  | some p =>
    rw [hp] at h
    change activeCaller p.callId = true at h
    show (decide (p.callId = callId) || activeCaller p.callId) = true
    rw [h, Bool.or_true]

/-- **Two-stage release preserves a pre-release reborrow**: stage 1
(`skipChildrenOfAccessed` while `callId` is active) is UB-free, skips the
descendant `t_ret` entirely, and stage 2 (`endCall`) leaves `t_ret` with
`HasUniqueWritePerm` in the caller. -/
theorem releaseProtector_preserves_reborrow_child {tree : BorrowTree} {t_arg t_ret : BorTag}
    {parentRange subRange : ByteRange} {activeCaller : ActiveProtectors} {callId : CallId}
    (hState : CalleeReborrowState tree t_arg t_ret parentRange subRange activeCaller callId) :
    releaseProtectorNoUB tree t_arg (insertActiveProtector activeCaller callId) ∧
      (∀ b, (applyReleaseProtector tree t_arg (insertActiveProtector activeCaller callId)).locState
        t_ret b = tree.locState t_ret b) ∧
      HasUniqueWritePerm (applyReleaseProtector tree t_arg (insertActiveProtector activeCaller callId))
        t_ret subRange activeCaller := by
  have hwf := hState.arg_perm.wf
  have hRetNotAncArg : tree.isAnc t_ret t_arg = false := by
    cases h : tree.isAnc t_ret t_arg with
    | false => rfl
    | true => exact absurd (hwf.isAnc_antisymm t_ret t_arg h hState.arg_anc_ret) hState.ret_ne_arg
  have hArgAw : ∀ b, parentRange.contains b = true → AncestorWritable (tree.locState t_arg b) :=
    fun b hb => hState.arg_perm.ancestors_writable t_arg b (hwf.isAnc_refl t_arg hState.arg_perm.tag_present) hb
  refine ⟨?_, ?_, ?_⟩
  · intro n b hPres hAcc
    have hbParent := hState.arg_accessed_in_parent b hAcc
    cases hAnc : tree.isAnc n t_arg with
    | true =>
      rw [nodeAccessRelatedness_anc hAnc]
      obtain ⟨st', hEq, _⟩ := performTransition_local_of_ancestorWritable
        (tree.locState t_arg b).perm.associatedAccess _ (tree.locState n b)
        (hState.arg_perm.ancestors_writable n b hAnc hbParent)
      show (performTransition _ .localAccess _ _).isSome = true
      rw [hEq]; rfl
    | false =>
      cases hDesc : tree.isAnc t_arg n with
      | true => rw [nodeAccessRelatedness_skip_desc hAnc hDesc]; trivial
      | false =>
        rw [nodeAccessRelatedness_skip_foreign hAnc hDesc]
        obtain ⟨st', hEq, _⟩ := performTransition_foreign_of_nonAncestorSafe
          (tree.locState t_arg b).perm.associatedAccess _ (tree.locState n b)
          (hState.arg_perm.non_ancestors_safe n b hPres hAnc hbParent)
        show (performTransition _ .foreignAccess _ _).isSome = true
        rw [hEq]; rfl
  · intro b
    cases hAcc : (tree.locState t_arg b).accessed with
    | false => exact applyReleaseProtector_locState_unacc tree t_arg _ t_ret b hAcc
    | true =>
      rw [applyReleaseProtector_locState_acc tree t_arg _ t_ret b hState.ret_present hAcc,
        nodeAccessRelatedness_skip_desc hRetNotAncArg hState.arg_anc_ret]
  · refine ⟨applyReleaseProtector_wf tree t_arg _ hwf, hState.ret_present, ?_, ?_⟩
    · intro anc b hAncRet hbSub
      have hPresAnc : tree.present anc = true := hwf.isAnc_present_left anc t_ret hAncRet
      have hbParent : parentRange.contains b = true := hState.sub_range b hbSub
      cases hAcc : (tree.locState t_arg b).accessed with
      | true =>
        rw [applyReleaseProtector_locState_acc tree t_arg _ anc b hPresAnc hAcc]
        cases hAncArg : tree.isAnc anc t_arg with
        | true =>
          rw [nodeAccessRelatedness_anc hAncArg]
          obtain ⟨st', hEq, hAw, _⟩ := performTransition_local_of_ancestorWritable
            (tree.locState t_arg b).perm.associatedAccess _ (tree.locState anc b)
            (hState.arg_perm.ancestors_writable anc b hAncArg hbParent)
          show AncestorWritable (match performTransition _ .localAccess _ _ with
            | some st' => st' | none => _)
          rw [hEq]
          exact hAw
        | false =>
          have hDescArg : tree.isAnc t_arg anc = true := by
            rcases hwf.anc_linear anc t_arg t_ret hAncRet hState.arg_anc_ret with h1 | h2
            · rw [hAncArg] at h1; cases h1
            · exact h2
          rw [nodeAccessRelatedness_skip_desc hAncArg hDescArg]
          exact hState.ret_ancestors_writable anc b hAncRet hbSub
      | false =>
        rw [applyReleaseProtector_locState_unacc tree t_arg _ anc b hAcc]
        exact hState.ret_ancestors_writable anc b hAncRet hbSub
    · intro other b hPres hNotAncRet hbSub
      have hPresOrig : tree.present other = true := hPres
      have hNotAncRetOrig : tree.isAnc other t_ret = false := hNotAncRet
      have hbParent : parentRange.contains b = true := hState.sub_range b hbSub
      show NonAncestorSafe _ (tree.isTagProtected other activeCaller)
      cases hDescArg : tree.isAnc t_arg other with
      | true =>
        have hOtherNeArg : other ≠ t_arg := by
          intro hEq
          rw [hEq, hState.arg_anc_ret] at hNotAncRetOrig
          cases hNotAncRetOrig
        exact Or.inl (hState.descendants_unprotected_in_caller other hDescArg hOtherNeArg)
      | false =>
        have hNotAncArg : tree.isAnc other t_arg = false := by
          cases h : tree.isAnc other t_arg with
          | false => rfl
          | true =>
            have hAncRet := hwf.isAnc_trans other t_arg t_ret h hState.arg_anc_ret
            rw [hNotAncRetOrig] at hAncRet
            cases hAncRet
        have hSafePre := hState.arg_perm.non_ancestors_safe other b hPresOrig hNotAncArg hbParent
        have hImp : tree.isTagProtected other activeCaller = true →
            tree.isTagProtected other (insertActiveProtector activeCaller callId) = true :=
          isTagProtected_insert_of_caller
        cases hAcc : (tree.locState t_arg b).accessed with
        | true =>
          rw [applyReleaseProtector_locState_acc tree t_arg _ other b hPresOrig hAcc,
            nodeAccessRelatedness_skip_foreign hNotAncArg hDescArg]
          obtain ⟨st', hEq, hSafePost, _⟩ := performTransition_foreign_of_nonAncestorSafe
            (tree.locState t_arg b).perm.associatedAccess _ (tree.locState other b) hSafePre
          show NonAncestorSafe (match performTransition _ .foreignAccess _ _ with
            | some st' => st' | none => _) _
          rw [hEq]
          exact nonAncestorSafe_mono_unprotect st' _ _ hSafePost hImp
        | false =>
          rw [applyReleaseProtector_locState_unacc tree t_arg _ other b hAcc]
          exact nonAncestorSafe_mono_unprotect _ _ _ hSafePre hImp

/-- Initial permission of a reborrow: `&mut` starts unconflicted `ReservedFrz`,
`&` starts `Frozen`. -/
def initPermOf : Mutability → Permission
  | .mut => .reservedFrz false
  | .not => .frozen

theorem initPermOf_mut_writable : AncestorWritable ⟨initPermOf .mut, false⟩ :=
  Or.inr (Or.inl rfl)

theorem fnEntry_writable : AncestorWritable ⟨.reservedFrz false, false⟩ := Or.inr (Or.inl rfl)

/-- Adding a fresh call id does not change the protection of existing tags. -/
theorem hasUniqueWritePerm_insert_fresh_callId {tree : BorrowTree} {tag : BorTag}
    {range : ByteRange} {activeCaller : ActiveProtectors} {callId : CallId}
    (hFreshCallId : ∀ n, tree.present n = true → ∀ p, tree.protector n = some p → p.callId ≠ callId)
    (hPerm : HasUniqueWritePerm tree tag range activeCaller) :
    HasUniqueWritePerm tree tag range (insertActiveProtector activeCaller callId) := by
  refine ⟨hPerm.wf, hPerm.tag_present, hPerm.ancestors_writable, ?_⟩
  intro other b hPres hNotAnc hb
  have hEq : tree.isTagProtected other (insertActiveProtector activeCaller callId) =
      tree.isTagProtected other activeCaller := by
    unfold BorrowTree.isTagProtected
    cases hp : tree.protector other with
    | none => rfl
    | some p =>
      show (decide (p.callId = callId) || activeCaller p.callId) = activeCaller p.callId
      rw [decide_eq_false (hFreshCallId other hPres p hp), Bool.false_or]
  rw [hEq]
  exact hPerm.non_ancestors_safe other b hPres hNotAnc hb

/-- Stage 2 with a call id that was fresh for the caller restores the caller's set. -/
theorem removeActiveProtector_insert {active : ActiveProtectors} {callId : CallId}
    (h : active callId = false) :
    removeActiveProtector (insertActiveProtector active callId) callId = active := by
  funext c
  unfold removeActiveProtector insertActiveProtector
  by_cases hc : c = callId
  · rw [ite_eq_left hc, hc, h]
  · rw [ite_eq_right hc, decide_eq_false hc, Bool.false_or]

theorem isAnc_child_of_retag {tree : BorrowTree} {t_parent t_child : BorTag}
    {prot : Option ProtectorKind} {initPerm : Permission} {range : ByteRange}
    {active : ActiveProtectors} (hwf : TreeWF tree) (hPres : tree.present t_parent = true) :
    (retagChild tree t_parent t_child prot initPerm range active).isAnc t_parent t_child = true := by
  rw [retagChild_isAnc, insertChildNode_isAnc_child, hwf.isAnc_refl t_parent hPres, Bool.or_true]

/-- In the tree after one call-entry retag and pre-release child retags, only
the minted children descend from the argument tag. -/
theorem retag_desc_cases {tree : BorrowTree} {t_parent t_child : BorTag}
    {prot : Option ProtectorKind} {initPerm : Permission} {range : ByteRange}
    {active : ActiveProtectors} {a d : BorTag}
    (h : (retagChild tree t_parent t_child prot initPerm range active).isAnc a d = true)
    (hd : d ≠ t_child) (ha : a ≠ t_child) : tree.isAnc a d = true := by
  rwa [retagChild_isAnc, insertChildNode_isAnc_of_ne _ _ _ _ _ hd ha] at h

theorem retag_not_desc_of_new {tree : BorrowTree} {t_parent t_child : BorTag}
    {prot : Option ProtectorKind} {initPerm : Permission} {range : ByteRange}
    {active : ActiveProtectors} {d : BorTag} (hd : d ≠ t_child) :
    (retagChild tree t_parent t_child prot initPerm range active).isAnc t_child d = false := by
  rw [retagChild_isAnc]
  exact insertChildNode_isAnc_from_child _ _ _ _ _ hd

/-- **`reborrow_return_unique_write_perm`** (`get_mut`): entry retag of the
argument with a strong protector, a pre-release `&mut` sub-range reborrow, and
two-stage release leave the returned reference with `HasUniqueWritePerm`
(including `NonAncestorSafe` isolation) for the caller's post-call protector
set; the caller's subsequent write through it is UB-free and preserves it. -/
theorem reborrow_return_unique_write_perm {tree0 : BorrowTree} {t_parent t_arg t_ret : BorTag}
    {parentRange subRange : ByteRange} {activeCaller : ActiveProtectors} {callId : CallId}
    (hPerm0 : HasUniqueWritePerm tree0 t_parent parentRange activeCaller)
    (hSub : subRange.Sub parentRange)
    (hFreshArg : tree0.present t_arg = false) (hFreshRet : tree0.present t_ret = false)
    (hRetNeArg : t_ret ≠ t_arg)
    (hFreshCallId : ∀ n, tree0.present n = true → ∀ p, tree0.protector n = some p → p.callId ≠ callId)
    (hCallFresh : activeCaller callId = false) :
    let active1 := insertActiveProtector activeCaller callId
    let tree1 := retagChild tree0 t_parent t_arg (some (.strong callId)) (.reservedFrz false)
      parentRange active1
    let tree2 := retagChild tree1 t_arg t_ret none (initPermOf .mut) subRange active1
    let tree_post := applyReleaseProtector tree2 t_arg active1
    let active_post := removeActiveProtector active1 callId
    releaseProtectorNoUB tree2 t_arg active1 ∧
      HasUniqueWritePerm tree_post t_ret subRange active_post ∧
      TreeAccessNoUB tree_post t_ret .write subRange active_post .visitChildrenOfAccessed ∧
      HasUniqueWritePerm (applyTreeAccess tree_post t_ret .write subRange active_post
        .visitChildrenOfAccessed) t_ret subRange active_post := by
  intro active1 tree1 tree2 tree_post active_post
  have hAct : active_post = activeCaller := removeActiveProtector_insert hCallFresh
  have hPerm0' := hasUniqueWritePerm_insert_fresh_callId hFreshCallId hPerm0
  have hTree1Perm : HasUniqueWritePerm tree1 t_arg parentRange active1 :=
    (retagChild_hasUniqueWritePerm (some (.strong callId)) fnEntry_writable hPerm0'
      (ByteRange.Sub.refl _) hFreshArg).2
  have hFreshRet1 : tree1.present t_ret = false := by
    rw [retagChild_present, decide_eq_false hRetNeArg, Bool.false_or]; exact hFreshRet
  have hTree2ArgPerm : HasUniqueWritePerm tree2 t_arg parentRange active1 :=
    retagUnprotectedChild_preserves_parent_hasUniqueWritePerm hTree1Perm hFreshRet1
  have hTree2RetPerm : HasUniqueWritePerm tree2 t_ret subRange active1 :=
    (retagChild_hasUniqueWritePerm none initPermOf_mut_writable hTree1Perm hSub hFreshRet1).2
  have hState : CalleeReborrowState tree2 t_arg t_ret parentRange subRange activeCaller callId := by
    refine ⟨hSub, hTree2ArgPerm, hTree2RetPerm.tag_present,
      isAnc_child_of_retag hTree1Perm.wf hTree1Perm.tag_present, hRetNeArg, ?_,
      hTree2RetPerm.ancestors_writable, ?_⟩
    · intro b hAcc
      cases hbP : parentRange.contains b with
      | true => rfl
      | false =>
        have hbS : subRange.contains b = false := by
          cases h : subRange.contains b with
          | false => rfl
          | true => have := hSub b h; rw [hbP] at this; cases this
        have h2 : (tree2.locState t_arg b) = tree1.locState t_arg b := by
          show (retagChild tree1 t_arg t_ret none (initPermOf .mut) subRange active1).locState t_arg b = _
          rw [retagChild_locState_out _ _ _ _ _ _ _ _ _ hbS,
            insertChildNode_locState_of_ne _ _ _ _ _ (Ne.symm hRetNeArg)]
        have h1 : (tree1.locState t_arg b).accessed = parentRange.contains b :=
          retagChild_child_accessed (by intro h; cases h) b
        rw [h2, h1, hbP] at hAcc
        cases hAcc
    · intro d hDesc hdNe
      by_cases hdRet : d = t_ret
      · rw [hdRet]
        show (insertChildNode tree1 t_arg t_ret none (initPermOf .mut)).isTagProtected t_ret activeCaller = false
        exact insertChildNode_isTagProtected_child_none _ _ _ _ _
      · have h1 : tree1.isAnc t_arg d = true :=
          retag_desc_cases hDesc hdRet (Ne.symm hRetNeArg)
        rw [retag_not_desc_of_new hdNe] at h1
        cases h1
  obtain ⟨hRelNoUB, _, hPostPerm⟩ := releaseProtector_preserves_reborrow_child hState
  rw [hAct]
  obtain ⟨hWriteNoUB, hAfter⟩ :=
    local_access_preserves_hasUniqueWritePerm .write hPostPerm (ByteRange.Sub.refl _)
  exact ⟨hRelNoUB, hPostPerm, hWriteNoUB, hAfter⟩

/-- **`reborrow_return_after_callee_write_unique_write_perm`**: the same holds
when the callee writes through the returned child before returning (so the
argument is `Active` on the sub-range and emits an implicit write at release). -/
theorem reborrow_return_after_callee_write_unique_write_perm {tree0 : BorrowTree}
    {t_parent t_arg t_ret : BorTag} {parentRange subRange : ByteRange}
    {activeCaller : ActiveProtectors} {callId : CallId}
    (hPerm0 : HasUniqueWritePerm tree0 t_parent parentRange activeCaller)
    (hSub : subRange.Sub parentRange)
    (hFreshArg : tree0.present t_arg = false) (hFreshRet : tree0.present t_ret = false)
    (hRetNeArg : t_ret ≠ t_arg)
    (hFreshCallId : ∀ n, tree0.present n = true → ∀ p, tree0.protector n = some p → p.callId ≠ callId)
    (hCallFresh : activeCaller callId = false) :
    let active1 := insertActiveProtector activeCaller callId
    let tree1 := retagChild tree0 t_parent t_arg (some (.strong callId)) (.reservedFrz false)
      parentRange active1
    let tree2 := retagChild tree1 t_arg t_ret none (initPermOf .mut) subRange active1
    let tree3 := applyTreeAccess tree2 t_ret .write subRange active1 .visitChildrenOfAccessed
    let tree_post := applyReleaseProtector tree3 t_arg active1
    let active_post := removeActiveProtector active1 callId
    TreeAccessNoUB tree2 t_ret .write subRange active1 .visitChildrenOfAccessed ∧
      releaseProtectorNoUB tree3 t_arg active1 ∧
      HasUniqueWritePerm tree_post t_ret subRange active_post := by
  intro active1 tree1 tree2 tree3 tree_post active_post
  have hAct : active_post = activeCaller := removeActiveProtector_insert hCallFresh
  have hPerm0' := hasUniqueWritePerm_insert_fresh_callId hFreshCallId hPerm0
  have hTree1Perm : HasUniqueWritePerm tree1 t_arg parentRange active1 :=
    (retagChild_hasUniqueWritePerm (some (.strong callId)) fnEntry_writable hPerm0'
      (ByteRange.Sub.refl _) hFreshArg).2
  have hFreshRet1 : tree1.present t_ret = false := by
    rw [retagChild_present, decide_eq_false hRetNeArg, Bool.false_or]; exact hFreshRet
  have hTree2ArgPerm : HasUniqueWritePerm tree2 t_arg parentRange active1 :=
    retagUnprotectedChild_preserves_parent_hasUniqueWritePerm hTree1Perm hFreshRet1
  have hTree2RetPerm : HasUniqueWritePerm tree2 t_ret subRange active1 :=
    (retagChild_hasUniqueWritePerm none initPermOf_mut_writable hTree1Perm hSub hFreshRet1).2
  obtain ⟨hWriteNoUB, hTree3RetPerm⟩ :=
    local_access_preserves_hasUniqueWritePerm .write hTree2RetPerm (ByteRange.Sub.refl _)
  have hArgAncRet : tree2.isAnc t_arg t_ret = true :=
    isAnc_child_of_retag hTree1Perm.wf hTree1Perm.tag_present
  have hTree3ArgPerm : HasUniqueWritePerm tree3 t_arg parentRange active1 := by
    refine ⟨applyTreeAccess_wf _ _ _ _ _ _ hTree2ArgPerm.wf, hTree2ArgPerm.tag_present, ?_, ?_⟩
    · intro anc b hAncArg hbParent
      have hAncArg2 : tree2.isAnc anc t_arg = true := hAncArg
      have hAncRet : tree2.isAnc anc t_ret = true :=
        hTree2ArgPerm.wf.isAnc_trans anc t_arg t_ret hAncArg2 hArgAncRet
      cases hbSub : subRange.contains b with
      | true => exact hTree3RetPerm.ancestors_writable anc b hAncRet hbSub
      | false =>
        show AncestorWritable ((applyTreeAccess tree2 t_ret .write subRange active1
          .visitChildrenOfAccessed).locState anc b)
        rw [applyTreeAccess_locState_out _ _ _ _ _ _ anc b hbSub]
        exact hTree2ArgPerm.ancestors_writable anc b hAncArg2 hbParent
    · intro other b hPres hNotAncArg hbParent
      have hPres2 : tree2.present other = true := hPres
      have hNotAncArg2 : tree2.isAnc other t_arg = false := hNotAncArg
      by_cases hOther : other = t_ret
      · left
        rw [hOther]
        show (insertChildNode tree1 t_arg t_ret none (initPermOf .mut)).isTagProtected t_ret active1 = false
        exact insertChildNode_isTagProtected_child_none _ _ _ _ _
      · have hNotAncRet : tree2.isAnc other t_ret = false := by
          show (insertChildNode tree1 t_arg t_ret none (initPermOf .mut)).isAnc other t_ret = false
          rw [insertChildNode_isAnc_child, decide_eq_false hOther, Bool.false_or]
          have : tree2.isAnc other t_arg =
              (insertChildNode tree1 t_arg t_ret none (initPermOf .mut)).isAnc other t_arg := rfl
          rw [this, insertChildNode_isAnc_of_ne _ _ _ _ _ (Ne.symm hRetNeArg) hOther] at hNotAncArg2
          exact hNotAncArg2
        cases hbSub : subRange.contains b with
        | true => exact hTree3RetPerm.non_ancestors_safe other b hPres2 hNotAncRet hbSub
        | false =>
          show NonAncestorSafe ((applyTreeAccess tree2 t_ret .write subRange active1
            .visitChildrenOfAccessed).locState other b) (tree2.isTagProtected other active1)
          rw [applyTreeAccess_locState_out _ _ _ _ _ _ other b hbSub]
          exact hTree2ArgPerm.non_ancestors_safe other b hPres2 hNotAncArg2 hbParent
  have hState : CalleeReborrowState tree3 t_arg t_ret parentRange subRange activeCaller callId := by
    refine ⟨hSub, hTree3ArgPerm, hTree3RetPerm.tag_present, hArgAncRet, hRetNeArg, ?_,
      hTree3RetPerm.ancestors_writable, ?_⟩
    · intro b hAcc
      cases hbP : parentRange.contains b with
      | true => rfl
      | false =>
        have hbS : subRange.contains b = false := by
          cases h : subRange.contains b with
          | false => rfl
          | true => have := hSub b h; rw [hbP] at this; cases this
        have h3 : tree3.locState t_arg b = tree2.locState t_arg b :=
          applyTreeAccess_locState_out _ _ _ _ _ _ _ _ hbS
        have h2 : tree2.locState t_arg b = tree1.locState t_arg b := by
          show (retagChild tree1 t_arg t_ret none (initPermOf .mut) subRange active1).locState t_arg b = _
          rw [retagChild_locState_out _ _ _ _ _ _ _ _ _ hbS,
            insertChildNode_locState_of_ne _ _ _ _ _ (Ne.symm hRetNeArg)]
        have h1 : (tree1.locState t_arg b).accessed = parentRange.contains b :=
          retagChild_child_accessed (by intro h; cases h) b
        rw [h3, h2, h1, hbP] at hAcc
        cases hAcc
    · intro d hDesc hdNe
      have hDesc2 : tree2.isAnc t_arg d = true := hDesc
      by_cases hdRet : d = t_ret
      · rw [hdRet]
        show (insertChildNode tree1 t_arg t_ret none (initPermOf .mut)).isTagProtected t_ret activeCaller = false
        exact insertChildNode_isTagProtected_child_none _ _ _ _ _
      · have h1 : tree1.isAnc t_arg d = true := retag_desc_cases hDesc2 hdRet (Ne.symm hRetNeArg)
        rw [retag_not_desc_of_new hdNe] at h1
        cases h1
  obtain ⟨hRelNoUB, _, hPostPerm⟩ := releaseProtector_preserves_reborrow_child hState
  rw [hAct]
  exact ⟨hWriteNoUB, hRelNoUB, hPostPerm⟩

/-- Frame rule: an access over a disjoint range preserves `HasUniqueWritePerm`. -/
theorem disjoint_access_preserves_hasUniqueWritePerm {tree : BorrowTree} {t_right : BorTag}
    {leftRange rightRange : ByteRange} {active : ActiveProtectors}
    (t_left : BorTag) (kind : AccessKind) (mode : ChildrenVisitMode)
    (hRightPerm : HasUniqueWritePerm tree t_right rightRange active)
    (hDisj : leftRange.Disjoint rightRange) :
    HasUniqueWritePerm (applyTreeAccess tree t_left kind leftRange active mode) t_right rightRange active := by
  have hDisjRL := hDisj.symm
  refine ⟨applyTreeAccess_wf _ _ _ _ _ _ hRightPerm.wf, hRightPerm.tag_present, ?_, ?_⟩
  · intro anc b hAnc hbRight
    show AncestorWritable ((applyTreeAccess tree t_left kind leftRange active mode).locState anc b)
    rw [applyTreeAccess_locState_out _ _ _ _ _ _ anc b (hDisjRL b hbRight)]
    exact hRightPerm.ancestors_writable anc b hAnc hbRight
  · intro other b hPres hNotAnc hbRight
    show NonAncestorSafe ((applyTreeAccess tree t_left kind leftRange active mode).locState other b)
      (tree.isTagProtected other active)
    rw [applyTreeAccess_locState_out _ _ _ _ _ _ other b (hDisjRL b hbRight)]
    exact hRightPerm.non_ancestors_safe other b hPres hNotAnc hbRight

/-- Retagging a fresh child under a sibling over a disjoint range preserves
`HasUniqueWritePerm` of `t_right`. -/
theorem disjoint_retagChild_preserves_hasUniqueWritePerm {tree : BorrowTree}
    {t_left t_child t_right : BorTag} {leftRange rightRange : ByteRange} {active : ActiveProtectors}
    (prot : Option ProtectorKind) (initPerm : Permission) (hInit : initPerm ≠ .active)
    (hRightPerm : HasUniqueWritePerm tree t_right rightRange active)
    (hDisj : leftRange.Disjoint rightRange) (hFresh : tree.present t_child = false) :
    HasUniqueWritePerm (retagChild tree t_left t_child prot initPerm leftRange active)
      t_right rightRange active := by
  have hRightNe : t_right ≠ t_child := ne_of_present_of_fresh hRightPerm.tag_present hFresh
  let tree1 := insertChildNode tree t_left t_child prot initPerm
  have hwf1 : TreeWF tree1 := insertChildNode_wf tree t_left t_child prot initPerm hRightPerm.wf hFresh
  have hRightPerm1 : HasUniqueWritePerm tree1 t_right rightRange active := by
    refine ⟨hwf1, by rw [insertChildNode_present, hRightPerm.tag_present, Bool.or_true], ?_, ?_⟩
    · intro anc b hAnc hbRight
      have hAncNe : anc ≠ t_child := by
        intro hEq
        rw [hEq] at hAnc
        have : tree1.isAnc t_child t_right = false := insertChildNode_isAnc_from_child _ _ _ _ _ hRightNe
        rw [this] at hAnc
        cases hAnc
      have hAncOrig : tree.isAnc anc t_right = true := by
        rwa [show tree1.isAnc anc t_right = tree.isAnc anc t_right from
          insertChildNode_isAnc_of_ne _ _ _ _ _ hRightNe hAncNe] at hAnc
      rw [insertChildNode_locState_of_ne _ _ _ _ _ hAncNe]
      exact hRightPerm.ancestors_writable anc b hAncOrig hbRight
    · intro other b hPres hNotAnc hbRight
      by_cases hOther : other = t_child
      · rw [hOther, insertChildNode_locState_child]
        exact Or.inr ⟨rfl, hInit⟩
      · have hPresOrig : tree.present other = true := by
          rwa [insertChildNode_present, decide_eq_false hOther, Bool.false_or] at hPres
        have hNotAncOrig : tree.isAnc other t_right = false := by
          rwa [show tree1.isAnc other t_right = tree.isAnc other t_right from
            insertChildNode_isAnc_of_ne _ _ _ _ _ hRightNe hOther] at hNotAnc
        rw [insertChildNode_isTagProtected_of_ne _ _ _ _ _ hOther,
          insertChildNode_locState_of_ne _ _ _ _ _ hOther]
        exact hRightPerm.non_ancestors_safe other b hPresOrig hNotAncOrig hbRight
  exact disjoint_access_preserves_hasUniqueWritePerm t_child .read .visitChildrenOfAccessed
    hRightPerm1 hDisj

/-- **`split_at_mut_unique_write_perm`** for `[base, base + len)` split at any
`mid ≤ len` (including `mid = 0` and `mid = len`): entry retag, two pre-release
`&mut` reborrows `[base, base + mid)` / `[base + mid, base + len)`, and two-stage
release yield distinct child tags with unique write permission; writing either
half preserves the other's permission; after both writes the halves are
`Active` on disjoint footprints; and a cross-half write through the left slice
into the right half is undefined behavior. -/
theorem split_at_mut_unique_write_perm {tree0 : BorrowTree} {t_parent t_arg t_left t_right : BorTag}
    {base mid len : Nat} {activeCaller : ActiveProtectors} {callId : CallId}
    (hmid : mid ≤ len)
    (hPerm0 : HasUniqueWritePerm tree0 t_parent (wholeRange base len) activeCaller)
    (hFreshArg : tree0.present t_arg = false) (hFreshLeft : tree0.present t_left = false)
    (hFreshRight : tree0.present t_right = false)
    (hLeftNeArg : t_left ≠ t_arg) (hRightNeArg : t_right ≠ t_arg) (hRightNeLeft : t_right ≠ t_left)
    (hFreshCallId : ∀ n, tree0.present n = true → ∀ p, tree0.protector n = some p → p.callId ≠ callId)
    (hCallFresh : activeCaller callId = false) :
    let active1 := insertActiveProtector activeCaller callId
    let tree1 := retagChild tree0 t_parent t_arg (some (.strong callId)) (.reservedFrz false)
      (wholeRange base len) active1
    let tree2 := retagChild tree1 t_arg t_left none (initPermOf .mut) (splitLeft base mid) active1
    let tree3 := retagChild tree2 t_arg t_right none (initPermOf .mut) (splitRight base mid len) active1
    let tree_post := applyReleaseProtector tree3 t_arg active1
    let active_post := removeActiveProtector active1 callId
    let tree_wl := applyTreeAccess tree_post t_left .write (splitLeft base mid) active_post
      .visitChildrenOfAccessed
    let tree_w := applyTreeAccess tree_wl t_right .write (splitRight base mid len) active_post
      .visitChildrenOfAccessed
    releaseProtectorNoUB tree3 t_arg active1 ∧
      HasUniqueWritePerm tree_post t_left (splitLeft base mid) active_post ∧
      HasUniqueWritePerm tree_post t_right (splitRight base mid len) active_post ∧
      TreeAccessNoUB tree_post t_left .write (splitLeft base mid) active_post .visitChildrenOfAccessed ∧
      HasUniqueWritePerm tree_wl t_right (splitRight base mid len) active_post ∧
      HasUniqueWritePerm (applyTreeAccess tree_post t_right .write (splitRight base mid len)
        active_post .visitChildrenOfAccessed) t_left (splitLeft base mid) active_post ∧
      TreeAccessNoUB tree_wl t_right .write (splitRight base mid len) active_post
        .visitChildrenOfAccessed ∧
      (∀ b, (splitLeft base mid).contains b = true → tree_w.locState t_left b = ⟨.active, true⟩) ∧
      (∀ b, (splitRight base mid len).contains b = true → tree_w.locState t_right b = ⟨.active, true⟩) ∧
      (∀ b, (splitRight base mid len).contains b = true →
        ¬ TreeAccessNoUB tree_w t_left .write ⟨b, b + 1⟩ active_post .visitChildrenOfAccessed) := by
  intro active1 tree1 tree2 tree3 tree_post active_post tree_wl tree_w
  have hAct : active_post = activeCaller := removeActiveProtector_insert hCallFresh
  have hDisj := split_disjoint base mid len
  have hDisjSymm := hDisj.symm
  have hSubL := splitLeft_sub (base := base) hmid
  have hSubR := splitRight_sub base mid len
  have hPerm0' := hasUniqueWritePerm_insert_fresh_callId hFreshCallId hPerm0
  have hTree1Perm : HasUniqueWritePerm tree1 t_arg (wholeRange base len) active1 :=
    (retagChild_hasUniqueWritePerm (some (.strong callId)) fnEntry_writable hPerm0'
      (ByteRange.Sub.refl _) hFreshArg).2
  have hFreshLeft1 : tree1.present t_left = false := by
    rw [retagChild_present, decide_eq_false hLeftNeArg, Bool.false_or]; exact hFreshLeft
  have hTree2ArgPerm : HasUniqueWritePerm tree2 t_arg (wholeRange base len) active1 :=
    retagUnprotectedChild_preserves_parent_hasUniqueWritePerm hTree1Perm hFreshLeft1
  have hTree2LeftPerm : HasUniqueWritePerm tree2 t_left (splitLeft base mid) active1 :=
    (retagChild_hasUniqueWritePerm none initPermOf_mut_writable hTree1Perm hSubL hFreshLeft1).2
  have hFreshRight2 : tree2.present t_right = false := by
    rw [retagChild_present, decide_eq_false hRightNeLeft, Bool.false_or, retagChild_present,
      decide_eq_false hRightNeArg, Bool.false_or]
    exact hFreshRight
  have hTree3ArgPerm : HasUniqueWritePerm tree3 t_arg (wholeRange base len) active1 :=
    retagUnprotectedChild_preserves_parent_hasUniqueWritePerm hTree2ArgPerm hFreshRight2
  have hTree3RightPerm : HasUniqueWritePerm tree3 t_right (splitRight base mid len) active1 :=
    (retagChild_hasUniqueWritePerm none initPermOf_mut_writable hTree2ArgPerm hSubR hFreshRight2).2
  have hTree3LeftPerm : HasUniqueWritePerm tree3 t_left (splitLeft base mid) active1 :=
    disjoint_retagChild_preserves_hasUniqueWritePerm none (initPermOf .mut) (by intro h; cases h)
      hTree2LeftPerm hDisjSymm hFreshRight2
  have hArgAcc : ∀ b, (tree3.locState t_arg b).accessed = true → (wholeRange base len).contains b = true := by
    intro b hAcc
    cases hbP : (wholeRange base len).contains b with
    | true => rfl
    | false =>
      have hbL : (splitLeft base mid).contains b = false := by
        cases h : (splitLeft base mid).contains b with
        | false => rfl
        | true => have := hSubL b h; rw [hbP] at this; cases this
      have hbR : (splitRight base mid len).contains b = false := by
        cases h : (splitRight base mid len).contains b with
        | false => rfl
        | true => have := hSubR b h; rw [hbP] at this; cases this
      have h3 : tree3.locState t_arg b = tree2.locState t_arg b := by
        show (retagChild tree2 t_arg t_right none (initPermOf .mut) (splitRight base mid len) active1).locState t_arg b = _
        rw [retagChild_locState_out _ _ _ _ _ _ _ _ _ hbR,
          insertChildNode_locState_of_ne _ _ _ _ _ (Ne.symm hRightNeArg)]
      have h2 : tree2.locState t_arg b = tree1.locState t_arg b := by
        show (retagChild tree1 t_arg t_left none (initPermOf .mut) (splitLeft base mid) active1).locState t_arg b = _
        rw [retagChild_locState_out _ _ _ _ _ _ _ _ _ hbL,
          insertChildNode_locState_of_ne _ _ _ _ _ (Ne.symm hLeftNeArg)]
      have h1 : (tree1.locState t_arg b).accessed = (wholeRange base len).contains b :=
        retagChild_child_accessed (by intro h; cases h) b
      rw [h3, h2, h1, hbP] at hAcc
      cases hAcc
  have hDescUnprot : ∀ d, tree3.isAnc t_arg d = true → d ≠ t_arg →
      tree3.isTagProtected d activeCaller = false := by
    intro d hDesc hdNe
    by_cases hdR : d = t_right
    · rw [hdR]
      show (insertChildNode tree2 t_arg t_right none (initPermOf .mut)).isTagProtected t_right activeCaller = false
      exact insertChildNode_isTagProtected_child_none _ _ _ _ _
    · by_cases hdL : d = t_left
      · rw [hdL]
        show (insertChildNode tree2 t_arg t_right none (initPermOf .mut)).isTagProtected t_left activeCaller = false
        rw [insertChildNode_isTagProtected_of_ne _ _ _ _ _ (Ne.symm hRightNeLeft)]
        show (insertChildNode tree1 t_arg t_left none (initPermOf .mut)).isTagProtected t_left activeCaller = false
        exact insertChildNode_isTagProtected_child_none _ _ _ _ _
      · have h2 : tree2.isAnc t_arg d = true := retag_desc_cases hDesc hdR (Ne.symm hRightNeArg)
        have h1 : tree1.isAnc t_arg d = true := retag_desc_cases h2 hdL (Ne.symm hLeftNeArg)
        rw [retag_not_desc_of_new hdNe] at h1
        cases h1
  have hArgAncLeft3 : tree3.isAnc t_arg t_left = true := by
    show (insertChildNode tree2 t_arg t_right none (initPermOf .mut)).isAnc t_arg t_left = true
    rw [insertChildNode_isAnc_of_ne _ _ _ _ _ (Ne.symm hRightNeLeft) (Ne.symm hRightNeArg)]
    exact isAnc_child_of_retag hTree1Perm.wf hTree1Perm.tag_present
  have hArgAncRight3 : tree3.isAnc t_arg t_right = true :=
    isAnc_child_of_retag hTree2ArgPerm.wf hTree2ArgPerm.tag_present
  have hStateL : CalleeReborrowState tree3 t_arg t_left (wholeRange base len) (splitLeft base mid)
      activeCaller callId :=
    ⟨hSubL, hTree3ArgPerm, hTree3LeftPerm.tag_present, hArgAncLeft3, hLeftNeArg, hArgAcc,
      hTree3LeftPerm.ancestors_writable, hDescUnprot⟩
  have hStateR : CalleeReborrowState tree3 t_arg t_right (wholeRange base len) (splitRight base mid len)
      activeCaller callId :=
    ⟨hSubR, hTree3ArgPerm, hTree3RightPerm.tag_present, hArgAncRight3, hRightNeArg, hArgAcc,
      hTree3RightPerm.ancestors_writable, hDescUnprot⟩
  obtain ⟨hRelNoUB, hSkipL, hPostL0⟩ := releaseProtector_preserves_reborrow_child hStateL
  obtain ⟨_, _, hPostR0⟩ := releaseProtector_preserves_reborrow_child hStateR
  have hPostL : HasUniqueWritePerm tree_post t_left (splitLeft base mid) active_post := by
    rw [hAct]; exact hPostL0
  have hPostR : HasUniqueWritePerm tree_post t_right (splitRight base mid len) active_post := by
    rw [hAct]; exact hPostR0
  have hWLNoUB := (local_access_preserves_hasUniqueWritePerm .write hPostL (ByteRange.Sub.refl _)).1
  have hWLL := (local_access_preserves_hasUniqueWritePerm .write hPostL (ByteRange.Sub.refl _)).2
  have hWLR : HasUniqueWritePerm tree_wl t_right (splitRight base mid len) active_post :=
    disjoint_access_preserves_hasUniqueWritePerm t_left .write .visitChildrenOfAccessed hPostR hDisj
  have hWRL := disjoint_access_preserves_hasUniqueWritePerm (kind := .write)
    (mode := .visitChildrenOfAccessed) t_right hPostL hDisjSymm
  have hWRNoUB := (local_access_preserves_hasUniqueWritePerm .write hWLR (ByteRange.Sub.refl _)).1
  refine ⟨hRelNoUB, hPostL, hPostR, hWLNoUB, hWLR, hWRL, hWRNoUB, ?_, ?_, ?_⟩
  · intro b hb
    show (applyTreeAccess tree_wl t_right .write (splitRight base mid len) active_post
      .visitChildrenOfAccessed).locState t_left b = _
    rw [applyTreeAccess_locState_out _ _ _ _ _ _ _ _ (hDisj b hb)]
    exact local_write_activates_ancestors hPostL (ByteRange.Sub.refl _)
      (hPostL.wf.isAnc_refl t_left hPostL.tag_present) hb
  · intro b hb
    exact local_write_activates_ancestors hWLR (ByteRange.Sub.refl _)
      (hWLR.wf.isAnc_refl t_right hWLR.tag_present) hb
  · intro b hb hNoUB
    have hbL : (splitLeft base mid).contains b = false := hDisjSymm b hb
    -- `t_left` is a strict sibling of `t_right` and unprotected
    have hLnotAncR : tree3.isAnc t_left t_right = false := by
      show (insertChildNode tree2 t_arg t_right none (initPermOf .mut)).isAnc t_left t_right = false
      rw [insertChildNode_isAnc_child, decide_eq_false (Ne.symm hRightNeLeft), Bool.false_or]
      exact retag_not_desc_of_new (Ne.symm hLeftNeArg)
    have hLprot : ∀ act, tree3.isTagProtected t_left act = false := by
      intro act
      show (insertChildNode tree2 t_arg t_right none (initPermOf .mut)).isTagProtected t_left act = false
      rw [insertChildNode_isTagProtected_of_ne _ _ _ _ _ (Ne.symm hRightNeLeft)]
      show (insertChildNode tree1 t_arg t_left none (initPermOf .mut)).isTagProtected t_left act = false
      exact insertChildNode_isTagProtected_child_none _ _ _ _ _
    have hLpres : tree3.present t_left = true := hTree3LeftPerm.tag_present
    have hL2 : tree2.locState t_left b = ⟨.reservedFrz false, false⟩ := by
      show (retagChild tree1 t_arg t_left none (initPermOf .mut) (splitLeft base mid) active1).locState t_left b = _
      rw [retagChild_locState_out _ _ _ _ _ _ _ _ _ hbL, insertChildNode_locState_child]
      rfl
    have hLpresI : (insertChildNode tree2 t_arg t_right none (initPermOf .mut)).present t_left = true :=
      hLpres
    have hLnotAncRI : (insertChildNode tree2 t_arg t_right none (initPermOf .mut)).isAnc t_left t_right =
        false := hLnotAncR
    have hL3 : tree3.locState t_left b = ⟨.reservedFrz false, false⟩ := by
      show (applyTreeAccess (insertChildNode tree2 t_arg t_right none (initPermOf .mut)) t_right .read
        (splitRight base mid len) active1 .visitChildrenOfAccessed).locState t_left b = _
      rw [applyTreeAccess_locState_in _ _ _ _ _ _ _ _ hLpresI hb,
        nodeAccessRelatedness_visit_foreign hLnotAncRI]
      show (match performTransition .read .foreignAccess (tree3.isTagProtected t_left active1)
        ((insertChildNode tree2 t_arg t_right none (initPermOf .mut)).locState t_left b) with
        | some st' => st' | none => _) = _
      rw [hLprot active1, insertChildNode_locState_of_ne _ _ _ _ _ (Ne.symm hRightNeLeft), hL2]
      rfl
    have hLpost : tree_post.locState t_left b = ⟨.reservedFrz false, false⟩ := by
      rw [hSkipL b, hL3]
    have hLwl : tree_wl.locState t_left b = ⟨.reservedFrz false, false⟩ := by
      show (applyTreeAccess tree_post t_left .write (splitLeft base mid) active_post
        .visitChildrenOfAccessed).locState t_left b = _
      rw [applyTreeAccess_locState_out _ _ _ _ _ _ _ _ hbL, hLpost]
    have hLpresWl : tree_wl.present t_left = true := hLpres
    have hLnotAncRWl : tree_wl.isAnc t_left t_right = false := hLnotAncR
    have hLw : tree_w.locState t_left b = ⟨.disabled, false⟩ := by
      show (applyTreeAccess tree_wl t_right .write (splitRight base mid len) active_post
        .visitChildrenOfAccessed).locState t_left b = _
      rw [applyTreeAccess_locState_in _ _ _ _ _ _ _ _ hLpresWl hb,
        nodeAccessRelatedness_visit_foreign hLnotAncRWl]
      show (match performTransition .write .foreignAccess (tree3.isTagProtected t_left active_post)
        (tree_wl.locState t_left b) with | some st' => st' | none => _) = _
      rw [hLprot active_post, hLwl]
      rfl
    have hLpresW : tree_w.present t_left = true := hLpres
    have hReflW : tree_w.isAnc t_left t_left = true := hTree3LeftPerm.wf.isAnc_refl t_left hLpres
    have hAt := hNoUB t_left b hLpresW
      ((ByteRange.contains_iff _ _).mpr ⟨Nat.le_refl b, Nat.lt_succ_self b⟩)
    rw [nodeAccessRelatedness_anc hReflW] at hAt
    change (performTransition .write .localAccess _ (tree_w.locState t_left b)).isSome = true at hAt
    rw [hLw] at hAt
    cases hAt

/-- Boundary `mid = 0`: the right slice owns the whole range, the left is empty. -/
theorem split_at_mut_mid_zero {tree0 : BorrowTree} {t_parent t_arg t_left t_right : BorTag}
    {base len : Nat} {activeCaller : ActiveProtectors} {callId : CallId}
    (hPerm0 : HasUniqueWritePerm tree0 t_parent (wholeRange base len) activeCaller)
    (hFreshArg : tree0.present t_arg = false) (hFreshLeft : tree0.present t_left = false)
    (hFreshRight : tree0.present t_right = false)
    (hLeftNeArg : t_left ≠ t_arg) (hRightNeArg : t_right ≠ t_arg) (hRightNeLeft : t_right ≠ t_left)
    (hFreshCallId : ∀ n, tree0.present n = true → ∀ p, tree0.protector n = some p → p.callId ≠ callId)
    (hCallFresh : activeCaller callId = false) :
    let active1 := insertActiveProtector activeCaller callId
    let tree1 := retagChild tree0 t_parent t_arg (some (.strong callId)) (.reservedFrz false)
      (wholeRange base len) active1
    let tree2 := retagChild tree1 t_arg t_left none (initPermOf .mut) (splitLeft base 0) active1
    let tree3 := retagChild tree2 t_arg t_right none (initPermOf .mut) (splitRight base 0 len) active1
    let tree_post := applyReleaseProtector tree3 t_arg active1
    HasUniqueWritePerm tree_post t_right (wholeRange base len) (removeActiveProtector active1 callId) ∧
      (∀ b, (splitLeft base 0).contains b = false) := by
  intro active1 tree1 tree2 tree3 tree_post
  obtain ⟨_, _, hR, _⟩ := split_at_mut_unique_write_perm (Nat.zero_le len) hPerm0 hFreshArg hFreshLeft
    hFreshRight hLeftNeArg hRightNeArg hRightNeLeft hFreshCallId hCallFresh
  refine ⟨hR, fun b => ByteRange.contains_eq_false _ _ ?_⟩
  simp only [splitLeft, Nat.add_zero]
  omega

/-- Boundary `mid = len`: the left slice owns the whole range, the right is empty. -/
theorem split_at_mut_mid_len {tree0 : BorrowTree} {t_parent t_arg t_left t_right : BorTag}
    {base len : Nat} {activeCaller : ActiveProtectors} {callId : CallId}
    (hPerm0 : HasUniqueWritePerm tree0 t_parent (wholeRange base len) activeCaller)
    (hFreshArg : tree0.present t_arg = false) (hFreshLeft : tree0.present t_left = false)
    (hFreshRight : tree0.present t_right = false)
    (hLeftNeArg : t_left ≠ t_arg) (hRightNeArg : t_right ≠ t_arg) (hRightNeLeft : t_right ≠ t_left)
    (hFreshCallId : ∀ n, tree0.present n = true → ∀ p, tree0.protector n = some p → p.callId ≠ callId)
    (hCallFresh : activeCaller callId = false) :
    let active1 := insertActiveProtector activeCaller callId
    let tree1 := retagChild tree0 t_parent t_arg (some (.strong callId)) (.reservedFrz false)
      (wholeRange base len) active1
    let tree2 := retagChild tree1 t_arg t_left none (initPermOf .mut) (splitLeft base len) active1
    let tree3 := retagChild tree2 t_arg t_right none (initPermOf .mut) (splitRight base len len) active1
    let tree_post := applyReleaseProtector tree3 t_arg active1
    HasUniqueWritePerm tree_post t_left (wholeRange base len) (removeActiveProtector active1 callId) ∧
      (∀ b, (splitRight base len len).contains b = false) := by
  intro active1 tree1 tree2 tree3 tree_post
  obtain ⟨_, hL, _⟩ := split_at_mut_unique_write_perm (Nat.le_refl len) hPerm0 hFreshArg hFreshLeft
    hFreshRight hLeftNeArg hRightNeArg hRightNeLeft hFreshCallId hCallFresh
  refine ⟨hL, fun b => ByteRange.contains_eq_false _ _ ?_⟩
  simp only [splitRight]
  omega

/-- Two-stage release keeps the released tag itself uniquely writable for the
caller when it has no protected strict descendants. -/
theorem releaseProtector_preserves_self {tree : BorrowTree} {t_arg : BorTag} {range : ByteRange}
    {activeCaller : ActiveProtectors} {callId : CallId}
    (hPerm : HasUniqueWritePerm tree t_arg range (insertActiveProtector activeCaller callId))
    (hAccIn : ∀ b, (tree.locState t_arg b).accessed = true → range.contains b = true)
    (hDescUnprot : ∀ d, tree.isAnc t_arg d = true → d ≠ t_arg →
      tree.isTagProtected d activeCaller = false) :
    releaseProtectorNoUB tree t_arg (insertActiveProtector activeCaller callId) ∧
      HasUniqueWritePerm (applyReleaseProtector tree t_arg (insertActiveProtector activeCaller callId))
        t_arg range activeCaller := by
  have hwf := hPerm.wf
  refine ⟨?_, ?_⟩
  · intro n b hPres hAcc
    have hb := hAccIn b hAcc
    cases hAnc : tree.isAnc n t_arg with
    | true =>
      rw [nodeAccessRelatedness_anc hAnc]
      obtain ⟨st', hEq, _⟩ := performTransition_local_of_ancestorWritable
        (tree.locState t_arg b).perm.associatedAccess _ (tree.locState n b)
        (hPerm.ancestors_writable n b hAnc hb)
      show (performTransition _ .localAccess _ _).isSome = true
      rw [hEq]; rfl
    | false =>
      cases hDesc : tree.isAnc t_arg n with
      | true => rw [nodeAccessRelatedness_skip_desc hAnc hDesc]; trivial
      | false =>
        rw [nodeAccessRelatedness_skip_foreign hAnc hDesc]
        obtain ⟨st', hEq, _⟩ := performTransition_foreign_of_nonAncestorSafe
          (tree.locState t_arg b).perm.associatedAccess _ (tree.locState n b)
          (hPerm.non_ancestors_safe n b hPres hAnc hb)
        show (performTransition _ .foreignAccess _ _).isSome = true
        rw [hEq]; rfl
  · refine ⟨applyReleaseProtector_wf _ _ _ hwf, hPerm.tag_present, ?_, ?_⟩
    · intro anc b hAnc hb
      have hAnc' : tree.isAnc anc t_arg = true := hAnc
      have hPresAnc : tree.present anc = true := hwf.isAnc_present_left anc t_arg hAnc'
      cases hAcc : (tree.locState t_arg b).accessed with
      | true =>
        rw [applyReleaseProtector_locState_acc tree t_arg _ anc b hPresAnc hAcc,
          nodeAccessRelatedness_anc hAnc']
        obtain ⟨st', hEq, hAw, _⟩ := performTransition_local_of_ancestorWritable
          (tree.locState t_arg b).perm.associatedAccess _ (tree.locState anc b)
          (hPerm.ancestors_writable anc b hAnc' hb)
        show AncestorWritable (match performTransition _ .localAccess _ _ with
          | some st' => st' | none => _)
        rw [hEq]
        exact hAw
      | false =>
        rw [applyReleaseProtector_locState_unacc tree t_arg _ anc b hAcc]
        exact hPerm.ancestors_writable anc b hAnc' hb
    · intro other b hPres hNotAnc hb
      have hPres' : tree.present other = true := hPres
      have hNotAnc' : tree.isAnc other t_arg = false := hNotAnc
      show NonAncestorSafe _ (tree.isTagProtected other activeCaller)
      have hImp : tree.isTagProtected other activeCaller = true →
          tree.isTagProtected other (insertActiveProtector activeCaller callId) = true :=
        isTagProtected_insert_of_caller
      cases hDesc : tree.isAnc t_arg other with
      | true =>
        have hNe : other ≠ t_arg := by
          intro hEq
          rw [hEq, hwf.isAnc_refl t_arg hPerm.tag_present] at hNotAnc'
          cases hNotAnc'
        exact Or.inl (hDescUnprot other hDesc hNe)
      | false =>
        have hSafe := hPerm.non_ancestors_safe other b hPres' hNotAnc' hb
        cases hAcc : (tree.locState t_arg b).accessed with
        | true =>
          rw [applyReleaseProtector_locState_acc tree t_arg _ other b hPres' hAcc,
            nodeAccessRelatedness_skip_foreign hNotAnc' hDesc]
          obtain ⟨st', hEq, hSafePost, _⟩ := performTransition_foreign_of_nonAncestorSafe
            (tree.locState t_arg b).perm.associatedAccess _ (tree.locState other b) hSafe
          show NonAncestorSafe (match performTransition _ .foreignAccess _ _ with
            | some st' => st' | none => _) _
          rw [hEq]
          exact nonAncestorSafe_mono_unprotect st' _ _ hSafePost hImp
        | false =>
          rw [applyReleaseProtector_locState_unacc tree t_arg _ other b hAcc]
          exact nonAncestorSafe_mono_unprotect _ _ _ hSafe hImp

/-- **`TrustedFnSpec`**: a declarative trusted-function contract carrying the
argument range and an explicit pre-release `reborrowFootprint`. -/
structure TrustedFnSpec where
  argRange : ByteRange
  reborrowFootprint : List (ByteRange × Mutability)

/-- Pre-release footprint: mint fresh tags `next, next + 1, …` as unprotected
children of the (still protected) argument tag. -/
def applyFootprint (t_arg : BorTag) (active : ActiveProtectors) :
    BorrowTree → BorTag → List (ByteRange × Mutability) → BorrowTree × List BorTag
  | tree, _, [] => (tree, [])
  | tree, next, (r, m) :: rest =>
    let res := applyFootprint t_arg active (retagChild tree t_arg next none (initPermOf m) r active)
      (next + 1) rest
    (res.1, next :: res.2)

/-- Outcome of a call: post-release tree, post-call protector set, returned tags. -/
structure CallOutcome where
  tree : BorrowTree
  active : ActiveProtectors
  rets : List BorTag

/-- Spec execution: `FnEntry` retag, **pre-release** footprint, stage-1 release
(`skipChildrenOfAccessed` while `callId` is active), stage-2 `endCall`. -/
def TrustedFnSpec.run (spec : TrustedFnSpec) (tree₀ : BorrowTree) (activeCaller : ActiveProtectors)
    (t_parent t_arg : BorTag) (callId : CallId) : CallOutcome :=
  let active₁ := insertActiveProtector activeCaller callId
  let tree₁ := retagChild tree₀ t_parent t_arg (some (.strong callId)) (.reservedFrz false)
    spec.argRange active₁
  let fp := applyFootprint t_arg active₁ tree₁ (t_arg + 1) spec.reborrowFootprint
  { tree := applyReleaseProtector fp.1 t_arg active₁
    active := removeActiveProtector active₁ callId
    rets := fp.2 }

/-- Negative-control semantics that *omits* the footprint: no tag is minted
before release, so every declared output aliases the argument tag. -/
def TrustedFnSpec.runNoFootprint (spec : TrustedFnSpec) (tree₀ : BorrowTree)
    (activeCaller : ActiveProtectors) (t_parent t_arg : BorTag) (callId : CallId) : CallOutcome :=
  let active₁ := insertActiveProtector activeCaller callId
  let tree₁ := retagChild tree₀ t_parent t_arg (some (.strong callId)) (.reservedFrz false)
    spec.argRange active₁
  { tree := applyReleaseProtector tree₁ t_arg active₁
    active := removeActiveProtector active₁ callId
    rets := spec.reborrowFootprint.map (fun _ => t_arg) }

/-- Declarative contract of `slice::split_at_mut(&mut [T; base..base+len], mid)`. -/
def splitAtMutSpec (base mid len : Nat) : TrustedFnSpec :=
  ⟨wholeRange base len, [(splitLeft base mid, .mut), (splitRight base mid len, .mut)]⟩

/-- Declarative contract of a `get_mut`-style projection `&mut x[off..off+sz]`. -/
def getMutSpec (argRange : ByteRange) (off sz : Nat) : TrustedFnSpec :=
  ⟨argRange, [(⟨off, off + sz⟩, .mut)]⟩

/-- **`same_tag_split_unsound_control`**: omitting the pre-release
`reborrowFootprint` returns two `&mut` slices that alias the argument tag, and a
cross-slice write after writing the other slice is UB-free in that model, while
the faithful pre-release footprint mints distinct tags under which the identical
access is undefined behavior (so the footprint-less spec is unsound). -/
theorem same_tag_split_unsound_control {tree0 : BorrowTree} {t_parent t_arg : BorTag}
    {base mid len : Nat} {activeCaller : ActiveProtectors} {callId : CallId}
    (hmid : mid ≤ len)
    (hPerm0 : HasUniqueWritePerm tree0 t_parent (wholeRange base len) activeCaller)
    (hFresh : ∀ t, t_arg ≤ t → tree0.present t = false)
    (hFreshCallId : ∀ n, tree0.present n = true → ∀ p, tree0.protector n = some p → p.callId ≠ callId)
    (hCallFresh : activeCaller callId = false) (b : Nat)
    (hb : (splitRight base mid len).contains b = true) :
    let naive := (splitAtMutSpec base mid len).runNoFootprint tree0 activeCaller t_parent t_arg callId
    let faithful := (splitAtMutSpec base mid len).run tree0 activeCaller t_parent t_arg callId
    naive.rets = [t_arg, t_arg] ∧
      TreeAccessNoUB
        (applyTreeAccess
          (applyTreeAccess naive.tree t_arg .write (splitLeft base mid) naive.active
            .visitChildrenOfAccessed)
          t_arg .write (splitRight base mid len) naive.active .visitChildrenOfAccessed)
        t_arg .write ⟨b, b + 1⟩ naive.active .visitChildrenOfAccessed ∧
      faithful.rets = [t_arg + 1, t_arg + 1 + 1] ∧
      ¬ TreeAccessNoUB
        (applyTreeAccess
          (applyTreeAccess faithful.tree (t_arg + 1) .write (splitLeft base mid) faithful.active
            .visitChildrenOfAccessed)
          (t_arg + 1 + 1) .write (splitRight base mid len) faithful.active .visitChildrenOfAccessed)
        (t_arg + 1) .write ⟨b, b + 1⟩ faithful.active .visitChildrenOfAccessed := by
  intro naive faithful
  have hAct : removeActiveProtector (insertActiveProtector activeCaller callId) callId = activeCaller :=
    removeActiveProtector_insert hCallFresh
  refine ⟨rfl, ?_, rfl, ?_⟩
  · -- footprint omitted: the argument tag keeps unique write permission over the whole range
    have hPerm0' := hasUniqueWritePerm_insert_fresh_callId hFreshCallId hPerm0
    have hFreshArg : tree0.present t_arg = false := hFresh t_arg (Nat.le_refl _)
    have hT1 := (retagChild_hasUniqueWritePerm (some (.strong callId)) fnEntry_writable hPerm0'
      (ByteRange.Sub.refl (wholeRange base len)) hFreshArg).2
    have hAccIn : ∀ b', ((retagChild tree0 t_parent t_arg (some (.strong callId)) (.reservedFrz false)
        (wholeRange base len) (insertActiveProtector activeCaller callId)).locState t_arg b').accessed = true →
        (wholeRange base len).contains b' = true := by
      intro b' h
      rwa [retagChild_child_accessed (by intro h; cases h) b'] at h
    have hDesc : ∀ d, (retagChild tree0 t_parent t_arg (some (.strong callId)) (.reservedFrz false)
        (wholeRange base len) (insertActiveProtector activeCaller callId)).isAnc t_arg d = true →
        d ≠ t_arg → (retagChild tree0 t_parent t_arg (some (.strong callId)) (.reservedFrz false)
        (wholeRange base len) (insertActiveProtector activeCaller callId)).isTagProtected d
          activeCaller = false := by
      intro d hd hne
      rw [retag_not_desc_of_new hne] at hd
      cases hd
    obtain ⟨_, hPost⟩ := releaseProtector_preserves_self hT1 hAccIn hDesc
    have hPostN : HasUniqueWritePerm naive.tree t_arg (wholeRange base len) naive.active := by
      show HasUniqueWritePerm _ t_arg (wholeRange base len)
        (removeActiveProtector (insertActiveProtector activeCaller callId) callId)
      rw [hAct]
      exact hPost
    have hW1 := (local_access_preserves_hasUniqueWritePerm .write hPostN
      (splitLeft_sub (base := base) hmid)).2
    have hW2 := (local_access_preserves_hasUniqueWritePerm .write hW1 (splitRight_sub base mid len)).2
    have hSubB : (ByteRange.mk b (b + 1)).Sub (wholeRange base len) := by
      intro b' hb'
      rw [ByteRange.contains_iff] at hb' hb ⊢
      dsimp only at hb'
      simp only [splitRight, wholeRange] at hb ⊢
      exact ⟨by omega, by omega⟩
    exact (local_access_preserves_hasUniqueWritePerm .write hW2 hSubB).1
  · -- faithful footprint: exactly the split-at-mut cross-half fault
    have hFreshArg : tree0.present t_arg = false := hFresh t_arg (Nat.le_refl _)
    have hFreshL : tree0.present (t_arg + 1) = false := hFresh (t_arg + 1) (Nat.le_succ _)
    have hle2 : t_arg ≤ t_arg + 1 + 1 := Nat.le_succ_of_le (Nat.le_succ t_arg)
    have hFreshR : tree0.present (t_arg + 1 + 1) = false := hFresh (t_arg + 1 + 1) hle2
    have hne1 : t_arg + 1 ≠ t_arg := Nat.succ_ne_self t_arg
    have hne2 : t_arg + 1 + 1 ≠ t_arg := Nat.ne_of_gt (Nat.lt_succ_of_lt (Nat.lt_succ_self t_arg))
    have hne3 : t_arg + 1 + 1 ≠ t_arg + 1 := Nat.succ_ne_self (t_arg + 1)
    obtain ⟨_, _, _, _, _, _, _, _, _, hCross⟩ := split_at_mut_unique_write_perm hmid hPerm0
      hFreshArg hFreshL hFreshR hne1 hne2 hne3 hFreshCallId hCallFresh
    exact hCross b hb

/-- Concrete callee instructions (the MIR shape of `split_at_mut` / `get_mut`). -/
inductive CalleeOp where
  /-- `assert!(a <= b)` (the call panics otherwise). -/
  | assertLe (a b : Nat)
  /-- `dst = src as *mut _`: raw pointers keep the source tag. -/
  | rawPtr (dst src : Nat)
  /-- `dst = &mut (*src)[r]` (or `&`), retagged with a fresh tag (`RetagMode::Default`). -/
  | reborrow (dst src : Nat) (r : ByteRange) (m : Mutability)

/-- Callee machine state: borrow tree, tag registers, and the tag counter. -/
structure CalleeState where
  tree : BorrowTree
  regs : List (Option BorTag)
  nextTag : BorTag

/-- Concrete UB-checked callee step relation (no derivation = stuck/UB/panic). -/
inductive CalleeStep (active : ActiveProtectors) : CalleeState → CalleeOp → CalleeState → Prop
  | assertLe {st : CalleeState} {a b : Nat} (h : a ≤ b) : CalleeStep active st (.assertLe a b) st
  | rawPtr {st : CalleeState} {dst src : Nat} {t : BorTag}
      (hsrc : st.regs[src]? = some (some t)) (hdst : dst < st.regs.length) :
      CalleeStep active st (.rawPtr dst src) ⟨st.tree, st.regs.set dst (some t), st.nextTag⟩
  | reborrow {st : CalleeState} {dst src : Nat} {r : ByteRange} {m : Mutability} {t : BorTag}
      (hsrc : st.regs[src]? = some (some t)) (hdst : dst < st.regs.length)
      (hfresh : st.tree.present st.nextTag = false)
      (hnoUB : TreeAccessNoUB (insertChildNode st.tree t st.nextTag none (initPermOf m)) st.nextTag
        .read r active .visitChildrenOfAccessed) :
      CalleeStep active st (.reborrow dst src r m)
        ⟨retagChild st.tree t st.nextTag none (initPermOf m) r active,
          st.regs.set dst (some st.nextTag), st.nextTag + 1⟩

inductive CalleeRun (active : ActiveProtectors) : CalleeState → List CalleeOp → CalleeState → Prop
  | nil {st : CalleeState} : CalleeRun active st [] st
  | cons {st st' st'' : CalleeState} {op : CalleeOp} {ops : List CalleeOp}
      (h : CalleeStep active st op st') (hrest : CalleeRun active st' ops st'') :
      CalleeRun active st (op :: ops) st''

/-- Read the returned registers. -/
def collectRegs (regs : List (Option BorTag)) : List Nat → Option (List BorTag)
  | [] => some []
  | i :: is =>
    match regs[i]?, collectRegs regs is with
    | some (some t), some ts => some (t :: ts)
    | _, _ => none

/-- Callee entry state: register `0` holds the `FnEntry`-retagged argument tag. -/
def calleeEntryState (tree₀ : BorrowTree) (activeCaller : ActiveProtectors) (t_parent t_arg : BorTag)
    (argRange : ByteRange) (callId : CallId) : CalleeState :=
  ⟨retagChild tree₀ t_parent t_arg (some (.strong callId)) (.reservedFrz false) argRange
      (insertActiveProtector activeCaller callId), [some t_arg, none, none, none], t_arg + 1⟩

/-- **Concrete MIR callee execution**: UB-checked entry retag, the callee body,
the returned registers, and the UB-checked two-stage protector release. -/
inductive ConcreteCall (tree₀ : BorrowTree) (activeCaller : ActiveProtectors) (t_parent t_arg : BorTag)
    (argRange : ByteRange) (callId : CallId) (body : List CalleeOp) (retRegs : List Nat) :
    CallOutcome → Prop
  | mk {stEnd : CalleeState} {rets : List BorTag}
      (hfresh : tree₀.present t_arg = false)
      (hentry : TreeAccessNoUB (insertChildNode tree₀ t_parent t_arg (some (.strong callId))
        (.reservedFrz false)) t_arg .read argRange (insertActiveProtector activeCaller callId)
        .visitChildrenOfAccessed)
      (hrun : CalleeRun (insertActiveProtector activeCaller callId)
        (calleeEntryState tree₀ activeCaller t_parent t_arg argRange callId) body stEnd)
      (hrets : collectRegs stEnd.regs retRegs = some rets)
      (hrel : releaseProtectorNoUB stEnd.tree t_arg (insertActiveProtector activeCaller callId)) :
      ConcreteCall tree₀ activeCaller t_parent t_arg argRange callId body retRegs
        ⟨applyReleaseProtector stEnd.tree t_arg (insertActiveProtector activeCaller callId),
          removeActiveProtector (insertActiveProtector activeCaller callId) callId, rets⟩

/-- `split_at_mut`: `assert!(mid <= len); let p = self.as_mut_ptr();
(from_raw_parts_mut(p, mid), from_raw_parts_mut(p.add(mid), len - mid))`. -/
def splitAtMutBody (base mid len : Nat) : List CalleeOp :=
  [.assertLe mid len, .rawPtr 1 0, .reborrow 2 1 (splitLeft base mid) .mut,
    .reborrow 3 1 (splitRight base mid len) .mut]

/-- `get_mut`-style projection: `&mut (*self)[off..off + sz]`. -/
def getMutBody (off sz : Nat) : List CalleeOp := [.reborrow 1 0 ⟨off, off + sz⟩ .mut]

/-- The concrete `split_at_mut` body panics unless `mid ≤ len`. -/
theorem concreteSplitAtMut_requires_mid_le {tree0 : BorrowTree} {activeCaller : ActiveProtectors}
    {t_parent t_arg : BorTag} {base mid len : Nat} {callId : CallId} {out : CallOutcome}
    (h : ConcreteCall tree0 activeCaller t_parent t_arg (wholeRange base len) callId
      (splitAtMutBody base mid len) [2, 3] out) : mid ≤ len := by
  cases h with
  | mk _ _ hrun _ _ =>
    cases hrun with
    | cons h1 _ =>
      cases h1 with
      | assertLe hle => exact hle

/-- **`trustedSpec_reborrow_equivalence`**: the declarative `TrustedFnSpec`
with a pre-release `reborrowFootprint` is equivalent to concrete callee
execution for both `split_at_mut` and `get_mut`: the concrete call succeeds and
produces exactly the spec's outcome (progress), and every concrete outcome is
the spec's outcome (determinism); hence concrete executions inherit the spec's
`HasUniqueWritePerm` postconditions. -/
theorem trustedSpec_reborrow_equivalence {tree0 : BorrowTree} {t_parent t_arg : BorTag}
    {base mid len off sz : Nat} {activeCaller : ActiveProtectors} {callId : CallId}
    (hmid : mid ≤ len) (hsub : base ≤ off ∧ off + sz ≤ base + len)
    (hPerm0 : HasUniqueWritePerm tree0 t_parent (wholeRange base len) activeCaller)
    (hFresh : ∀ t, t_arg ≤ t → tree0.present t = false)
    (hFreshCallId : ∀ n, tree0.present n = true → ∀ p, tree0.protector n = some p → p.callId ≠ callId)
    (hCallFresh : activeCaller callId = false) :
    let splitSpec := (splitAtMutSpec base mid len).run tree0 activeCaller t_parent t_arg callId
    let getSpec := (getMutSpec (wholeRange base len) off sz).run tree0 activeCaller t_parent t_arg callId
    (ConcreteCall tree0 activeCaller t_parent t_arg (wholeRange base len) callId
        (splitAtMutBody base mid len) [2, 3] splitSpec ∧
      ∀ out, ConcreteCall tree0 activeCaller t_parent t_arg (wholeRange base len) callId
        (splitAtMutBody base mid len) [2, 3] out → out = splitSpec) ∧
    (ConcreteCall tree0 activeCaller t_parent t_arg (wholeRange base len) callId
        (getMutBody off sz) [1] getSpec ∧
      ∀ out, ConcreteCall tree0 activeCaller t_parent t_arg (wholeRange base len) callId
        (getMutBody off sz) [1] out → out = getSpec) ∧
    HasUniqueWritePerm splitSpec.tree (t_arg + 1) (splitLeft base mid) splitSpec.active ∧
    HasUniqueWritePerm splitSpec.tree (t_arg + 1 + 1) (splitRight base mid len) splitSpec.active ∧
    HasUniqueWritePerm getSpec.tree (t_arg + 1) ⟨off, off + sz⟩ getSpec.active := by
  intro splitSpec getSpec
  have hFreshArg : tree0.present t_arg = false := hFresh t_arg (Nat.le_refl _)
  have hFreshL : tree0.present (t_arg + 1) = false := hFresh (t_arg + 1) (Nat.le_succ _)
  have hFreshR : tree0.present (t_arg + 1 + 1) = false :=
    hFresh (t_arg + 1 + 1) (Nat.le_succ_of_le (Nat.le_succ t_arg))
  have hne1 : t_arg + 1 ≠ t_arg := Nat.succ_ne_self t_arg
  have hne2 : t_arg + 1 + 1 ≠ t_arg := Nat.ne_of_gt (Nat.lt_succ_of_lt (Nat.lt_succ_self t_arg))
  have hne3 : t_arg + 1 + 1 ≠ t_arg + 1 := Nat.succ_ne_self (t_arg + 1)
  have hSubG : (ByteRange.mk off (off + sz)).Sub (wholeRange base len) := by
    intro b hb
    rw [ByteRange.contains_iff] at hb ⊢
    dsimp only at hb
    simp only [wholeRange]
    exact ⟨by omega, by omega⟩
  have hPerm0' := hasUniqueWritePerm_insert_fresh_callId hFreshCallId hPerm0
  obtain ⟨hEntryNoUB, hTree1Perm⟩ := retagChild_hasUniqueWritePerm (some (.strong callId))
    fnEntry_writable hPerm0' (ByteRange.Sub.refl (wholeRange base len)) hFreshArg
  have hFreshL1 : (retagChild tree0 t_parent t_arg (some (.strong callId)) (.reservedFrz false)
      (wholeRange base len) (insertActiveProtector activeCaller callId)).present (t_arg + 1) = false := by
    rw [retagChild_present, decide_eq_false hne1, Bool.false_or]; exact hFreshL
  obtain ⟨hNoUBL, _⟩ := retagChild_hasUniqueWritePerm none initPermOf_mut_writable hTree1Perm
    (splitLeft_sub (base := base) hmid) hFreshL1
  obtain ⟨hNoUBG, _⟩ := retagChild_hasUniqueWritePerm none initPermOf_mut_writable hTree1Perm
    hSubG hFreshL1
  have hTree2ArgPerm := retagUnprotectedChild_preserves_parent_hasUniqueWritePerm
    (childRange := splitLeft base mid) (initPerm := initPermOf .mut) hTree1Perm hFreshL1
  have hFreshR2 : (retagChild (retagChild tree0 t_parent t_arg (some (.strong callId))
      (.reservedFrz false) (wholeRange base len) (insertActiveProtector activeCaller callId))
      t_arg (t_arg + 1) none (initPermOf .mut) (splitLeft base mid)
      (insertActiveProtector activeCaller callId)).present (t_arg + 1 + 1) = false := by
    rw [retagChild_present, decide_eq_false hne3, Bool.false_or, retagChild_present,
      decide_eq_false hne2, Bool.false_or]
    exact hFreshR
  obtain ⟨hNoUBR, _⟩ := retagChild_hasUniqueWritePerm none initPermOf_mut_writable hTree2ArgPerm
    (splitRight_sub base mid len) hFreshR2
  obtain ⟨hRelS, hLS, hRS, _⟩ := split_at_mut_unique_write_perm hmid hPerm0 hFreshArg hFreshL hFreshR
    hne1 hne2 hne3 hFreshCallId hCallFresh
  obtain ⟨hRelG, hPostG, _⟩ := reborrow_return_unique_write_perm hPerm0 hSubG hFreshArg hFreshL hne1
    hFreshCallId hCallFresh
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, hLS, hRS, hPostG⟩
  · exact ConcreteCall.mk hFreshArg hEntryNoUB
      (CalleeRun.cons (CalleeStep.assertLe hmid)
        (CalleeRun.cons (CalleeStep.rawPtr rfl (show (1 : Nat) < 4 from by decide))
          (CalleeRun.cons (CalleeStep.reborrow rfl (show (2 : Nat) < 4 from by decide) hFreshL1 hNoUBL)
            (CalleeRun.cons (CalleeStep.reborrow rfl (show (3 : Nat) < 4 from by decide) hFreshR2 hNoUBR)
              CalleeRun.nil))))
      rfl hRelS
  · intro out hout
    cases hout with
    | mk _ _ hrun hrets _ =>
      cases hrun with
      | cons h1 hr1 =>
        cases h1 with
        | assertLe _ =>
          cases hr1 with
          | cons h2 hr2 =>
            cases h2 with
            | rawPtr hsrc2 _ =>
              simp only [calleeEntryState, List.getElem?_cons_zero, Option.some.injEq] at hsrc2
              subst hsrc2
              cases hr2 with
              | cons h3 hr3 =>
                cases h3 with
                | reborrow hsrc3 _ _ _ =>
                  simp only [calleeEntryState, List.set_cons_succ, List.set_cons_zero,
                    List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hsrc3
                  subst hsrc3
                  cases hr3 with
                  | cons h4 hr4 =>
                    cases h4 with
                    | reborrow hsrc4 _ _ _ =>
                      simp only [calleeEntryState, List.set_cons_succ, List.set_cons_zero,
                        List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hsrc4
                      subst hsrc4
                      cases hr4 with
                      | nil =>
                        simp only [calleeEntryState, collectRegs, List.set_cons_succ,
                          List.set_cons_zero, List.getElem?_cons_succ, List.getElem?_cons_zero,
                          Option.some.injEq] at hrets
                        subst hrets
                        rfl
  · exact ConcreteCall.mk hFreshArg hEntryNoUB
      (CalleeRun.cons (CalleeStep.reborrow rfl (show (1 : Nat) < 4 from by decide) hFreshL1 hNoUBG)
        CalleeRun.nil) rfl hRelG
  · intro out hout
    cases hout with
    | mk _ _ hrun hrets _ =>
      cases hrun with
      | cons h1 hr1 =>
        cases h1 with
        | reborrow hsrc1 _ _ _ =>
          simp only [calleeEntryState, List.getElem?_cons_zero, Option.some.injEq] at hsrc1
          subst hsrc1
          cases hr1 with
          | nil =>
            simp only [calleeEntryState, collectRegs, List.set_cons_succ, List.set_cons_zero,
              List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hrets
            subst hrets
            rfl

/-- A one-tag allocation: the root tag is `Active` everywhere and unprotected. -/
def rootTree (root : BorTag) : BorrowTree where
  present t := decide (t = root)
  isAnc a d := decide (a = root) && decide (d = root)
  protector _ := none
  locState _ _ := ⟨.active, true⟩

theorem rootTree_hasUniqueWritePerm (root : BorTag) (range : ByteRange) (active : ActiveProtectors) :
    HasUniqueWritePerm (rootTree root) root range active := by
  have hIsAnc : ∀ a d, (rootTree root).isAnc a d = true → a = root ∧ d = root := by
    intro a d h
    simp only [rootTree, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro t ht
    simp only [rootTree, decide_eq_true_eq] at ht
    simp only [rootTree, ht, decide_true, Bool.and_self]
  · intro a b c hab hbc
    obtain ⟨ha, _⟩ := hIsAnc a b hab
    obtain ⟨_, hc⟩ := hIsAnc b c hbc
    simp only [rootTree, ha, hc, decide_true, Bool.and_self]
  · intro a b hab _
    obtain ⟨ha, hb⟩ := hIsAnc a b hab
    rw [ha, hb]
  · intro a b hab
    obtain ⟨ha, _⟩ := hIsAnc a b hab
    simp only [rootTree, ha, decide_true]
  · intro a b hab
    obtain ⟨_, hb⟩ := hIsAnc a b hab
    simp only [rootTree, hb, decide_true]
  · intro a b c hac hbc
    left
    obtain ⟨ha, _⟩ := hIsAnc a c hac
    obtain ⟨hb, _⟩ := hIsAnc b c hbc
    simp only [rootTree, ha, hb, decide_true, Bool.and_self]
  · simp only [rootTree, decide_true]
  · intro anc b _ _
    exact Or.inl rfl
  · intro other b hPres hNotAnc _
    simp only [rootTree, decide_eq_true_eq] at hPres
    simp only [rootTree, hPres, decide_true, Bool.and_self] at hNotAnc
    cases hNotAnc

/-- **Non-vacuity**: the hypotheses of `split_at_mut_unique_write_perm` are
satisfiable for every `mid ≤ len` (including both boundaries) on a concrete
one-tag allocation, yielding both halves' unique write permissions and the
cross-half fault. -/
theorem split_at_mut_rootTree_nonvacuous (base mid len : Nat) (hmid : mid ≤ len) :
    let active1 := insertActiveProtector (fun _ => false) 0
    let tree1 := retagChild (rootTree 0) 0 1 (some (.strong 0)) (.reservedFrz false)
      (wholeRange base len) active1
    let tree2 := retagChild tree1 1 2 none (initPermOf .mut) (splitLeft base mid) active1
    let tree3 := retagChild tree2 1 3 none (initPermOf .mut) (splitRight base mid len) active1
    let tree_post := applyReleaseProtector tree3 1 active1
    let active_post := removeActiveProtector active1 0
    let tree_w := applyTreeAccess (applyTreeAccess tree_post 2 .write (splitLeft base mid) active_post
      .visitChildrenOfAccessed) 3 .write (splitRight base mid len) active_post .visitChildrenOfAccessed
    HasUniqueWritePerm tree_post 2 (splitLeft base mid) active_post ∧
      HasUniqueWritePerm tree_post 3 (splitRight base mid len) active_post ∧
      (∀ b, (splitRight base mid len).contains b = true →
        ¬ TreeAccessNoUB tree_w 2 .write ⟨b, b + 1⟩ active_post .visitChildrenOfAccessed) := by
  intro active1 tree1 tree2 tree3 tree_post active_post tree_w
  obtain ⟨_, hL, hR, _, _, _, _, _, _, hX⟩ := split_at_mut_unique_write_perm
    (t_parent := 0) (t_arg := 1) (t_left := 2) (t_right := 3) (callId := 0)
    (activeCaller := fun _ => false) hmid (rootTree_hasUniqueWritePerm 0 _ _) rfl rfl rfl
    (by decide) (by decide) (by decide) (fun _ _ _ hp => nomatch hp) rfl
  exact ⟨hL, hR, hX⟩

end TreeBorrows

/-! ## 10. Kernel axiom audit (`#guard_msgs in #print axioms`) -/

/-! Every exported theorem above depends only on a subset of `{propext, Quot.sound}`. -/

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.FuelOrder.refl' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FuelOrder.refl

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.FuelOrder.trans' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FuelOrder.trans

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.FuelOrder.halted_stable' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FuelOrder.halted_stable

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.FuelOrder.faulted_stable' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FuelOrder.faulted_stable

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.evalFuel_mono' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms evalFuel_mono

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.evalFuel_halted_mono' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms evalFuel_halted_mono

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.evalFuel_faulted_mono' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms evalFuel_faulted_mono

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.evalFuel_halted_deterministic' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms evalFuel_halted_deterministic

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.evalFuel_faulted_ne_halted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms evalFuel_faulted_ne_halted

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.WpConverges.of_done' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms WpConverges.of_done

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.WpConverges.of_cont' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms WpConverges.of_cont

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.WpConverges.mono' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms WpConverges.mono

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.not_wpConverges_of_faulted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms not_wpConverges_of_faulted

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.WpConverges.deterministic' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms WpConverges.deterministic

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.StepsTo.bind_wp' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms StepsTo.bind_wp

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.StepsTo.trans' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms StepsTo.trans

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.StepsTo.mono' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms StepsTo.mono

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.runUntilTarget_reached_atTarget' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms runUntilTarget_reached_atTarget

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.runToTarget_reached_atTarget' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms runToTarget_reached_atTarget

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.stepsTo_of_runUntilTarget_reached' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms stepsTo_of_runUntilTarget_reached

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.stepsTo_of_runToTarget_reached' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms stepsTo_of_runToTarget_reached

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.wpConverges_of_runUntilTarget_halted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms wpConverges_of_runUntilTarget_halted

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.wpConverges_of_runToTarget_halted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms wpConverges_of_runToTarget_halted

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.faulted_of_runUntilTarget_stuck' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms faulted_of_runUntilTarget_stuck

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.not_wpConverges_of_runToTarget_stuck' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms not_wpConverges_of_runToTarget_stuck

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.runUntilTarget_mono_bound' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms runUntilTarget_mono_bound

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.runToTarget_mono_bound' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms runToTarget_mono_bound

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.FirstHitIn.unique' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FirstHitIn.unique

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.firstHitIn_of_runUntilTarget_reached' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms firstHitIn_of_runUntilTarget_reached

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.firstHitIn_of_runToTarget_reached' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms firstHitIn_of_runToTarget_reached

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.runUntilTarget_of_firstHitIn' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms runUntilTarget_of_firstHitIn

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.runToTarget_of_firstHitIn' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms runToTarget_of_firstHitIn

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.forRangeUpAux_eq_live' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forRangeUpAux_eq_live

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.forRangeUp_eq_live' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forRangeUp_eq_live

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.forRangeUpAux_induction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forRangeUpAux_induction

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.forRangeUp_induction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forRangeUp_induction

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.live_forRangeUp_induction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms live_forRangeUp_induction

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.wpConverges_forRangeUpAux' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wpConverges_forRangeUpAux

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.wpConverges_forRangeUp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wpConverges_forRangeUp

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.runCfgToBlock_reached_bb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runCfgToBlock_reached_bb

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.stepsTo_of_runCfgToBlock_reached' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms stepsTo_of_runCfgToBlock_reached

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.wpConverges_of_runCfgToBlock_halted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms wpConverges_of_runCfgToBlock_halted

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.not_wpConverges_of_runCfgToBlock_stuck' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms not_wpConverges_of_runCfgToBlock_stuck

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.countUp_entry_step' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms countUp_entry_step

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.countUp_header_exit_steps' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms countUp_header_exit_steps

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.countUp_header_iter_steps' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms countUp_header_iter_steps

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.evalFuel_countUp_header' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalFuel_countUp_header

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.countUp_halts_with_fuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms countUp_halts_with_fuel

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.no_uniform_fuel_countUp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms no_uniform_fuel_countUp

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.runCfgToBlock_countUp_iter' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms runCfgToBlock_countUp_iter

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.runCfgToBlock_countUp_exit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms runCfgToBlock_countUp_exit

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.runCfgToBlock_countUp_entry' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms runCfgToBlock_countUp_entry

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.countUp_wpConverges_all_n' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms countUp_wpConverges_all_n

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.selfLoop_iter_step' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms selfLoop_iter_step

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.selfLoop_exit_steps' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms selfLoop_exit_steps

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.runCfgToBlock_selfLoop_no_overshoot' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms runCfgToBlock_selfLoop_no_overshoot

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.selfLoop_firstHit_unique' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms selfLoop_firstHit_unique

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.selfLoop_wpConverges_all_n' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selfLoop_wpConverges_all_n

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.runCfgToBlock_stuck_example' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms runCfgToBlock_stuck_example

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.runToTarget_outOfFuel_vs_reached' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms runToTarget_outOfFuel_vs_reached

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.stepMirFn_of_mirStep_cont' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stepMirFn_of_mirStep_cont

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.stepMirFn_of_mirStep_done' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stepMirFn_of_mirStep_done

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.mirStepsConverges_of_stepsTo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mirStepsConverges_of_stepsTo

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.mirWpConverges_of_evalFuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mirWpConverges_of_evalFuel

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.mirWpConverges_of_wpConverges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mirWpConverges_of_wpConverges

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.mirWpConverges_of_stepsTo_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mirWpConverges_of_stepsTo_bind

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.mirStepsConverges_of_runMirToBlock_reached' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mirStepsConverges_of_runMirToBlock_reached

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.mirWpConverges_of_runMirToBlock_halted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mirWpConverges_of_runMirToBlock_halted

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.mirWpConverges_forRangeUp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mirWpConverges_forRangeUp

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.blockTargets_toMirBlock' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms blockTargets_toMirBlock

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.hasCfgBackedgeAux_map_toMirBlock' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms hasCfgBackedgeAux_map_toMirBlock

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.hasCfgBackedge_toMirShape' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms hasCfgBackedge_toMirShape

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.checkBlockFragment_toMirBlock' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms checkBlockFragment_toMirBlock

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.all_checkBlockFragment_toMirShape' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms all_checkBlockFragment_toMirShape

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.inferMinFragment_toMirShape' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms inferMinFragment_toMirShape

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.inferMinFragment_countUp' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms inferMinFragment_countUp

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.inferMinFragment_selfLoop' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms inferMinFragment_selfLoop

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.inferMinFragment_straightLine' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms inferMinFragment_straightLine

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.inferMinFragment_refShape' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms inferMinFragment_refShape

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.fragment_levels_strict' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms fragment_levels_strict

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.length_forcePureEnvD' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms length_forcePureEnvD

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.forcePureEnvD_eq_self' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms forcePureEnvD_eq_self

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.forcePureEnv_eq_self' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms forcePureEnv_eq_self

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.getD_zero_eq_headD' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms getD_zero_eq_headD

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.getD_succ_eq_tail' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms getD_succ_eq_tail

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.getElem?_forcePureEnvD' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms getElem?_forcePureEnvD

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.getElem?_forcePureEnv' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms getElem?_forcePureEnv

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.forcePureEnvD_set_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forcePureEnvD_set_comm

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.forcePureEnv_set_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forcePureEnv_set_comm

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.forcePureEnv_set_comm_counterexample' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms forcePureEnv_set_comm_counterexample

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.eq_of_forcePureEnv' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms eq_of_forcePureEnv

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.chained_sets_collapse_rfl' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms chained_sets_collapse_rfl

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.forceSpine?_eq_some' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms forceSpine?_eq_some

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.forceSpine?_eq_some_forcePureEnv' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms forceSpine?_eq_some_forcePureEnv

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applySlotUpdatesForced_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applySlotUpdatesForced_eq

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applySlotUpdates_eq_of_forced' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applySlotUpdates_eq_of_forced

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.length_applySlotUpdates' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms length_applySlotUpdates

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.slotUpdates_collapse_forced' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms slotUpdates_collapse_forced

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.forcePureEnvSlots_eq_self' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms forcePureEnvSlots_eq_self

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.forceSpine?_eq_live' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms forceSpine?_eq_live

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.forcePureEnvSlots_set?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forcePureEnvSlots_set?

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.length_splice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms length_splice

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.getElem?_slice' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms getElem?_slice

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.getElem?_splice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms getElem?_splice

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.drop_take_add' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms drop_take_add

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.slice_splice_same' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slice_splice_same

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.slice_splice_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slice_splice_disjoint

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.splice_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms splice_self

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.splice_splice_same' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms splice_splice_same

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.splice_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms splice_comm

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.sliceAbstractBytes_eq' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sliceAbstractBytes_eq

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.writeAbstractBytesAt_nil' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms writeAbstractBytesAt_nil

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.writeAbstractBytesAt_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms writeAbstractBytesAt_cons

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.writeAbstractBytesAt_eq_splice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms writeAbstractBytesAt_eq_splice

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.writeAbstractBytesAt_eq_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms writeAbstractBytesAt_eq_none

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.writeAbstractBytesAt_some_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms writeAbstractBytesAt_some_inv

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.DisjointSlice.symm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DisjointSlice.symm

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.DisjointSlice.adjacent' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms DisjointSlice.adjacent

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.typedAt_iff' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms typedAt_iff

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.typedAt_append_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms typedAt_append_encode

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.writeTyped_eq_splice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms writeTyped_eq_splice

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.writeTyped_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms writeTyped_length

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.TypedAt.read_write_same' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TypedAt.read_write_same

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.TypedAt.frame_writeBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TypedAt.frame_writeBytes

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.TypedAt.frame_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TypedAt.frame_write

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.TypedAt.frame_write_adjacent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TypedAt.frame_write_adjacent

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.writeTyped_eq_none_of_oob' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms writeTyped_eq_none_of_oob

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.writeTyped_isSome_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms writeTyped_isSome_iff

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.not_typedAt_of_oob' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_typedAt_of_oob

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.writeTyped_zero_width' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms writeTyped_zero_width

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.typedAt_zero_width_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms typedAt_zero_width_iff

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.zeroWidth_write_read_asymmetry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zeroWidth_write_read_asymmetry

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.prod_decode_eq_some_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms prod_decode_eq_some_iff

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.padRight_decode_of_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms padRight_decode_of_length

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.typedAt_laidOutPair_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms typedAt_laidOutPair_iff

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.typedAt_laidOutPair_write_snd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms typedAt_laidOutPair_write_snd

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.typedAt_laidOutPair_padding_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms typedAt_laidOutPair_padding_write

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.laidOutPair_encode_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms laidOutPair_encode_eq

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.typedAt_laidOutPair_init_padding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms typedAt_laidOutPair_init_padding

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.canonicalAt_iff' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canonicalAt_iff

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.fieldLens_writeBack_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fieldLens_writeBack_eq

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.canonicalAt_splice_same' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canonicalAt_splice_same

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.canonicalAt_splice_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canonicalAt_splice_disjoint

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.readTyped_splice_same' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms readTyped_splice_same

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.readTyped_splice_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms readTyped_splice_disjoint

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.fieldLens_lawful' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fieldLens_lawful

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.fieldsValid_symm' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms fieldsValid_symm

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.subplaceFieldLens_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms subplaceFieldLens_disjoint

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.structLens_lawful' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms structLens_lawful

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applyFieldWrites_spec' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms applyFieldWrites_spec

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.u8Fields_lenses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms u8Fields_lenses

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.u8FieldsValid_init' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms u8FieldsValid_init

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.u8Fields_six_mutations' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms u8Fields_six_mutations

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.ByteRange.contains_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteRange.contains_iff

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.ByteRange.contains_eq_false' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteRange.contains_eq_false

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.ByteRange.Sub.refl' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ByteRange.Sub.refl

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.ByteRange.Disjoint.symm' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ByteRange.Disjoint.symm

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.split_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms split_disjoint

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.splitLeft_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms splitLeft_sub

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.splitRight_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms splitRight_sub

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.split_cover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms split_cover

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applyTreeAccess_locState_in' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applyTreeAccess_locState_in

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applyTreeAccess_locState_out' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applyTreeAccess_locState_out

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applyReleaseProtector_locState_acc' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applyReleaseProtector_locState_acc

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applyReleaseProtector_locState_unacc' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applyReleaseProtector_locState_unacc

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.performTransition_local_of_ancestorWritable' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms performTransition_local_of_ancestorWritable

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.performTransition_local_write_of_ancestorWritable' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms performTransition_local_write_of_ancestorWritable

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.performTransition_foreign_of_nonAncestorSafe' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms performTransition_foreign_of_nonAncestorSafe

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.nonAncestorSafe_mono_unprotect' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms nonAncestorSafe_mono_unprotect

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.insertChildNode_present' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms insertChildNode_present

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.insertChildNode_isAnc_child' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms insertChildNode_isAnc_child

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.insertChildNode_isAnc_of_ne' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms insertChildNode_isAnc_of_ne

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.insertChildNode_isAnc_from_child' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms insertChildNode_isAnc_from_child

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.insertChildNode_locState_of_ne' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms insertChildNode_locState_of_ne

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.insertChildNode_locState_child' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms insertChildNode_locState_child

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.insertChildNode_isTagProtected_of_ne' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms insertChildNode_isTagProtected_of_ne

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.insertChildNode_isTagProtected_child_none' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms insertChildNode_isTagProtected_child_none

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.ne_of_present_of_fresh' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ne_of_present_of_fresh

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.insertChildNode_wf' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms insertChildNode_wf

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applyTreeAccess_wf' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applyTreeAccess_wf

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applyReleaseProtector_wf' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applyReleaseProtector_wf

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.nodeAccessRelatedness_anc' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms nodeAccessRelatedness_anc

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.nodeAccessRelatedness_visit_foreign' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms nodeAccessRelatedness_visit_foreign

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.nodeAccessRelatedness_skip_desc' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms nodeAccessRelatedness_skip_desc

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.nodeAccessRelatedness_skip_foreign' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms nodeAccessRelatedness_skip_foreign

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.hasUniqueWritePerm_narrow' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms hasUniqueWritePerm_narrow

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.local_access_preserves_hasUniqueWritePerm' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms local_access_preserves_hasUniqueWritePerm

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.local_write_activates_ancestors' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms local_write_activates_ancestors

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.retagChild_hasUniqueWritePerm' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms retagChild_hasUniqueWritePerm

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.retagUnprotectedChild_preserves_parent_hasUniqueWritePerm' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms retagUnprotectedChild_preserves_parent_hasUniqueWritePerm

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.retagChild_present' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms retagChild_present

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.retagChild_isAnc' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms retagChild_isAnc

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.retagChild_isTagProtected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms retagChild_isTagProtected

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.retagChild_locState_out' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms retagChild_locState_out

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.retagChild_child_accessed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms retagChild_child_accessed

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.isTagProtected_insert_of_caller' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms isTagProtected_insert_of_caller

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.releaseProtector_preserves_reborrow_child' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms releaseProtector_preserves_reborrow_child

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.initPermOf_mut_writable' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms initPermOf_mut_writable

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.fnEntry_writable' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms fnEntry_writable

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.hasUniqueWritePerm_insert_fresh_callId' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms hasUniqueWritePerm_insert_fresh_callId

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.removeActiveProtector_insert' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms removeActiveProtector_insert

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.isAnc_child_of_retag' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms isAnc_child_of_retag

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.retag_desc_cases' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms retag_desc_cases

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.retag_not_desc_of_new' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms retag_not_desc_of_new

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.reborrow_return_unique_write_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reborrow_return_unique_write_perm

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.reborrow_return_after_callee_write_unique_write_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reborrow_return_after_callee_write_unique_write_perm

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.disjoint_access_preserves_hasUniqueWritePerm' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms disjoint_access_preserves_hasUniqueWritePerm

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.disjoint_retagChild_preserves_hasUniqueWritePerm' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms disjoint_retagChild_preserves_hasUniqueWritePerm

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.split_at_mut_unique_write_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms split_at_mut_unique_write_perm

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.split_at_mut_mid_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms split_at_mut_mid_zero

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.split_at_mut_mid_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms split_at_mut_mid_len

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.releaseProtector_preserves_self' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms releaseProtector_preserves_self

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.same_tag_split_unsound_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms same_tag_split_unsound_control

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.concreteSplitAtMut_requires_mid_le' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms concreteSplitAtMut_requires_mid_le

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.trustedSpec_reborrow_equivalence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trustedSpec_reborrow_equivalence

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.rootTree_hasUniqueWritePerm' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms rootTree_hasUniqueWritePerm

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.split_at_mut_rootTree_nonvacuous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms split_at_mut_rootTree_nonvacuous

end Anneal.FuelFreeLoopAndTypedAtLensPrototype
