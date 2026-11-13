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

/-- Non-terminating single-block self-loop (`bb0: goto bb0`). -/
def infiniteLoopCfg : List Instr := [.goto 0]

theorem stepCfg_infiniteLoop (env : List Nat) :
    stepCfg infiniteLoopCfg ⟨0, env⟩ = .cont ⟨0, env⟩ := rfl

/-- **Non-terminating loop fuel characterization**: under every finite fuel
budget `k`, `infiniteLoopCfg` returns `.outOfFuel` (never `.halted` or `.faulted`). -/
theorem evalFuel_infiniteLoop_outOfFuel :
    ∀ (k : Nat) (env : List Nat),
      evalFuel (stepCfg infiniteLoopCfg) k ⟨0, env⟩ = .outOfFuel
  | 0, _ => rfl
  | k + 1, env => evalFuel_infiniteLoop_outOfFuel k env

/-- **Non-terminating loop refutes `WpConverges`**. -/
theorem not_wpConverges_infiniteLoop (env : List Nat) (post : Nat → Prop) :
    ¬ WpConverges (stepCfg infiniteLoopCfg) ⟨0, env⟩ post := by
  rintro ⟨k, v, hk, _⟩
  rw [evalFuel_infiniteLoop_outOfFuel k env] at hk
  cases hk

theorem runUntilTarget_infiniteLoop_unreached :
    ∀ (bound : Nat) (env : List Nat),
      runUntilTarget (stepCfg infiniteLoopCfg) (fun s => s.bb == 1) bound ⟨0, env⟩ = .outOfFuel
  | 0, _ => rfl
  | bound + 1, env => runUntilTarget_infiniteLoop_unreached bound env

/-- Targeting an unreachable exit block (`bb1`) on `infiniteLoopCfg` returns
`.outOfFuel` for every ceiling `bound`, whereas targeting the loop header (`bb0`)
stops after one step without overshooting. -/
theorem runToTarget_infiniteLoop_outOfFuel (bound : Nat) (env : List Nat) :
    runToTarget (stepCfg infiniteLoopCfg) (fun s => s.bb == 1) bound ⟨0, env⟩ = .outOfFuel ∧
      runCfgToBlock infiniteLoopCfg 0 ⟨0, env⟩ = .reached ⟨0, env⟩ :=
  ⟨runUntilTarget_infiniteLoop_unreached bound env, rfl⟩

/-! ## 5. Bridges to the live MIR fuel-free predicates (`Anneal.MirFuelFree`) -/

section LiveMirBridge

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-- Embedding of the live trusted step function `stepMirFn` into the generic
machine.  Both silent `.tau` transitions and `MirObsE` observation steps
(`.vis (.inr (.inl (.emit _)))`, including `.event _` emitted by live
`.switchInt` terminators and `.silent`) continue, and root returns halt;
external calls and faults are mapped conservatively to `.fault`, matching live
`Anneal.FunctionalTranslation.runMirToBlock`. -/
def mirStep (body : CapturedMir) (s : MachineState) : Step MachineState MirOutcome :=
  match stepMirFn body s with
  | .tau (.running s') => .cont s'
  | .vis (.inr (.inl (.emit _))) k =>
    match k PUnit.unit with
    | .running s' => .cont s'
    | _ => .fault
  | .ret out => .done out
  | _ => .fault

theorem stepMirFn_of_mirStep_cont {body : CapturedMir} {s s' : MachineState}
    (h : mirStep body s = .cont s') :
    stepMirFn body s = .tau (.running s') ∨
      ∃ obs k, stepMirFn body s = .vis (.inr (.inl (.emit obs))) k ∧ k PUnit.unit = .running s' := by
  unfold mirStep at h
  split at h
  · rename_i s'' heq
    cases h
    exact Or.inl heq
  · rename_i obs k heq
    split at h
    · rename_i s'' hk
      cases h
      exact Or.inr ⟨obs, k, heq, hk⟩
    · cases h
  · cases h
  · cases h

theorem stepMirFn_of_mirStep_done {body : CapturedMir} {s : MachineState} {out : MirOutcome}
    (h : mirStep body s = .done out) : stepMirFn body s = .ret out := by
  unfold mirStep at h
  split at h
  · cases h
  · split at h <;> cases h
  · rename_i out' heq
    cases h
    exact heq
  · cases h

theorem mirStepsConverges_of_mirStep_cont {body : CapturedMir} {s s' : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (hs : mirStep body s = .cont s')
    (hnext : Anneal.MirFuelFree.MirStepsConverges body s' mid post) :
    Anneal.MirFuelFree.MirStepsConverges body s mid post := by
  rcases stepMirFn_of_mirStep_cont hs with htau | ⟨obs, k, hvis, hk⟩
  · exact Anneal.MirFuelFree.MirStepsConverges.step_tau htau hnext
  · rcases hnext with ⟨fuel, h_wp⟩
    refine ⟨fuel + 1, ?_⟩
    unfold Anneal.MirFuelFree.wpMirStepsSym
      Anneal.MirFuelFree.wpMirExecStepsSym
    rw [Anneal.Rustc.V2026_06_01.SymbolicEval.evalSymNodeTreeNoCall_eq,
      Anneal.Rustc.V2026_06_01.SymbolicEval.stepMirExecSymTree_eval,
      Anneal.Rustc.V2026_06_01.SymbolicEval.evalNodeNoCallWP_eq]
    dsimp only [stepMirState]
    cases obs <;> (
      rw [hvis]
      change Anneal.MirFuelFree.wpMirExecStepsSym fuel body (k PUnit.unit) _ post
      rw [hk]
      exact h_wp)

/-- **Bridge to the live `Anneal.MirFuelFree.MirStepsConverges`**: generic
segment reachability over `mirStep` is live fuel-free reachability (including
across all `MirObsE` observation steps). -/
theorem mirStepsConverges_of_stepsTo {body : CapturedMir} {s : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h : StepsTo (mirStep body) s mid) :
    Anneal.MirFuelFree.MirStepsConverges body s mid post := by
  induction h with
  | refl hm => exact Anneal.MirFuelFree.MirStepsConverges.refl hm
  | step hs _ ih => exact mirStepsConverges_of_mirStep_cont hs ih

theorem mirWpConverges_of_mirStep_cont {body : CapturedMir} {s s' : MachineState}
    {post : MirOutcome → Prop}
    (hs : mirStep body s = .cont s')
    (hnext : Anneal.MirFuelFree.MirWpConverges body s' post) :
    Anneal.MirFuelFree.MirWpConverges body s post := by
  rcases stepMirFn_of_mirStep_cont hs with htau | ⟨obs, k, hvis, hk⟩
  · exact Anneal.MirFuelFree.MirWpConverges.step_tau htau hnext
  · rcases hnext with ⟨fuel, h_wp⟩
    refine ⟨fuel + 1, ?_⟩
    unfold Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirSym
      Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym
    rw [Anneal.Rustc.V2026_06_01.SymbolicEval.evalSymNodeTree_eq,
      Anneal.Rustc.V2026_06_01.SymbolicEval.stepMirExecSymTree_eval,
      Anneal.Rustc.V2026_06_01.SymbolicEval.evalNodeWP_eq]
    dsimp only [stepMirState]
    cases obs <;> (
      rw [hvis]
      change Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body (k PUnit.unit) post
      rw [hk]
      exact h_wp)

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
      exact mirWpConverges_of_mirStep_cont hs
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

/-- Entry segment of the live `Anneal.MirLoops.countToNBody n` executed through
`runMirToBlock` (reaches loop header `bb1` in two steps). -/
theorem runMirToBlock_countToN_entry (n : Nat) :
    runMirToBlock (Anneal.MirLoops.countToNBody n) 1
      (Anneal.MirLoops.countStateMem 0 0 0 emptyMemory) =
      .reached (Anneal.MirLoops.countStateMem 1 0 0 emptyMemory) := rfl

/-- Loop-body iteration segment of the live `Anneal.MirLoops.countToNBody n`
executed through `runMirToBlock`: steps across `bb1`'s `.switchInt` (`.emitStep`)
and `bb2`'s increment + `goto 1` back to `bb1` without overshooting. -/
theorem runMirToBlock_countToN_iter (n i : Nat) (hlt : i < n) (hn : n < 4294967296) :
    runMirToBlock (Anneal.MirLoops.countToNBody n) 1
      (Anneal.MirLoops.countStateMem 1 0 i emptyMemory) =
      .reached (Anneal.MirLoops.countStateMem 1 0 (i + 1) emptyMemory) := by
  have hbeq : Nat.beq i n = false := (Bool.not_eq_true _).mp (Nat.ne_of_lt hlt ∘ Nat.eq_of_beq_eq_true)
  have hs1 : mirStep (Anneal.MirLoops.countToNBody n) (Anneal.MirLoops.countStateMem 1 0 i emptyMemory) =
      .cont (Anneal.MirLoops.countStateMem (match Nat.beq i n with | true => 3 | false => 2) 0 i emptyMemory) := rfl
  rw [hbeq] at hs1
  have hs2 : mirStep (Anneal.MirLoops.countToNBody n) (Anneal.MirLoops.countStateMem 2 0 i emptyMemory) =
      .cont (Anneal.MirLoops.countStateMem 2 1 (i + 1) emptyMemory) := by
    have hmod : (i + 1) % 4294967296 = i + 1 := Nat.mod_eq_of_lt (by omega)
    unfold mirStep stepMirFn
    dsimp [Anneal.MirLoops.countStateMem, emptyMemory]
    simp [Anneal.MirLoops.countToNBody, Anneal.MirLoops.mkMirBody,
      Anneal.MirLoops.constU32, Trusted.Sequence.get?, evalStmt, evalOperand,
      readProjectedValue, evalRvalue, evalConstValue, advanceStmt, Trusted.Sequence.set?,
      invalidateConflictingBorrows, hmod]
    rfl
  have hs3 : mirStep (Anneal.MirLoops.countToNBody n)
      (Anneal.MirLoops.countStateMem 2 1 (i + 1) emptyMemory) =
      .cont (Anneal.MirLoops.countStateMem 1 0 (i + 1) emptyMemory) := rfl
  unfold runMirToBlock
  have hmb : mirSegmentBound (Anneal.MirLoops.countToNBody n) = 7 := rfl
  rw [hmb]
  simp only [runToTarget, hs1, runUntilTarget, hs2, hs3]
  rfl

/-- Loop-exit segment of the live `Anneal.MirLoops.countToNBody n` executed
through `runMirToBlock`: steps from `bb1` (`i = n`) through `bb3` to `.halted`. -/
theorem runMirToBlock_countToN_exit (n : Nat) :
    runMirToBlock (Anneal.MirLoops.countToNBody n) 1
      (Anneal.MirLoops.countStateMem 1 0 n emptyMemory) =
      .halted (.normal (.scalar ⟨n, 4⟩, emptyMemory)) := by
  have hs1 : mirStep (Anneal.MirLoops.countToNBody n) (Anneal.MirLoops.countStateMem 1 0 n emptyMemory) =
      .cont (Anneal.MirLoops.countStateMem (match Nat.beq n n with | true => 3 | false => 2) 0 n emptyMemory) := rfl
  rw [Nat.beq_refl] at hs1
  have hs2 : mirStep (Anneal.MirLoops.countToNBody n) (Anneal.MirLoops.countStateMem 3 0 n emptyMemory) =
      .cont (Anneal.MirLoops.countStateMemRet 3 1 n emptyMemory) := rfl
  have hs3 : mirStep (Anneal.MirLoops.countToNBody n)
      (Anneal.MirLoops.countStateMemRet 3 1 n emptyMemory) =
      .done (.normal (.scalar ⟨n, 4⟩, emptyMemory)) := rfl
  unfold runMirToBlock
  have hmb : mirSegmentBound (Anneal.MirLoops.countToNBody n) = 7 := rfl
  rw [hmb]
  simp only [runToTarget, hs1, runUntilTarget, hs2, hs3]
  rfl

/-- **End-to-end live `CapturedMir` fuel-free loop verification**:
`Anneal.MirLoops.countToNBody n` converges for every symbolic `n < 2^32` via
`runMirToBlock` + `mirWpConverges_forRangeUp` with zero fuel numerals. -/
theorem live_countToN_mirWpConverges_all_n (n : Nat) (hn : n < 4294967296) :
    Anneal.MirFuelFree.MirWpConverges (Anneal.MirLoops.countToNBody n)
      (Anneal.MirLoops.countStateMem 0 0 0 emptyMemory)
      (fun out => out = .normal (.scalar ⟨n, 4⟩, emptyMemory)) := by
  refine mirWpConverges_of_stepsTo_bind
    (stepsTo_of_runToTarget_reached (runMirToBlock_countToN_entry n)) (fun s₁ hs₁ => ?_)
  subst hs₁
  refine mirWpConverges_forRangeUp (Anneal.MirLoops.countToNBody n) 0 n () (fun _ _ _ u => u)
    (fun i _ s => s = Anneal.MirLoops.countStateMem 1 0 i emptyMemory)
    (Anneal.MirLoops.countStateMem 1 0 0 emptyMemory)
    (fun out => out = .normal (.scalar ⟨n, 4⟩, emptyMemory))
    (Nat.zero_le n) rfl ?_ ?_
  · intro i _ hlt _ s hs
    subst hs
    exact stepsTo_of_runToTarget_reached (runMirToBlock_countToN_iter n i hlt hn)
  · intro s_exit hs
    subst hs
    exact wpConverges_of_runToTarget_halted (runMirToBlock_countToN_exit n) rfl

/-- **Stationary-at-header limitation of live `Anneal.FunctionalTranslation.runMirToBlock`**:
because the live stepper checks `blockIdx == target && stmtIdx == 0` *before*
stepping, calling it from a loop header `(target, 0)` immediately returns `some s`
in zero steps without advancing through the loop body. -/
theorem live_runMirToBlock_stationary_at_target (body : CapturedMir)
    (target : BasicBlockIdx) (bound : Nat) (s : MachineState)
    (hbb : s.frame.blockIdx = target) (hstmt : s.frame.stmtIdx = 0) :
    Anneal.FunctionalTranslation.runMirToBlock (bound + 1) body target s = some s := by
  unfold Anneal.FunctionalTranslation.runMirToBlock
  have hcond : (Nat.beq s.frame.blockIdx target && Nat.beq s.frame.stmtIdx 0) = true := by
    rw [hbb, hstmt, Nat.beq_refl, Nat.beq_refl]; rfl
  rw [ite_eq_left hcond]

theorem live_runMirToBlock_step_of_not_target (body : CapturedMir)
    (target : BasicBlockIdx) (bound : Nat) (s : MachineState)
    (hnt : (s.frame.blockIdx == target && s.frame.stmtIdx == 0) = false) :
    Anneal.FunctionalTranslation.runMirToBlock (bound + 1) body target s =
      match mirStep body s with
      | .cont s' => Anneal.FunctionalTranslation.runMirToBlock bound body target s'
      | _ => none := by
  have hnt' : (Nat.beq s.frame.blockIdx target && Nat.beq s.frame.stmtIdx 0) = false := by
    simpa [BEq.beq] using hnt
  conv => lhs; unfold Anneal.FunctionalTranslation.runMirToBlock
  unfold mirStep
  rw [ite_eq_right (by rw [hnt']; exact Bool.false_ne_true)]
  cases hstep : stepMirFn body s with
  | ret _ => rfl
  | tau st =>
    cases st <;> rfl
  | vis req k =>
    rcases req with _ | (e | _)
    · rfl
    · cases e
      cases hk : k PUnit.unit <;> simp only [hk]
    · rfl

/-- **Exact bridge between `runUntilTarget (mirStep body)` and live
`Anneal.FunctionalTranslation.runMirToBlock`**: `runUntilTarget` reaches `s_hit`
within `bound` steps iff the live `runMirToBlock (bound + 1)` returns `some s_hit`. -/
theorem runUntilTarget_reached_iff_live_runMirToBlock (body : CapturedMir)
    (target : BasicBlockIdx) :
    ∀ (bound : Nat) (s s_hit : MachineState),
      runUntilTarget (mirStep body)
        (fun ms => ms.frame.blockIdx == target && ms.frame.stmtIdx == 0) bound s = .reached s_hit ↔
        Anneal.FunctionalTranslation.runMirToBlock (bound + 1) body target s = some s_hit
  | 0, s, s_hit => by
    unfold runUntilTarget
    cases ht : (s.frame.blockIdx == target && s.frame.stmtIdx == 0) with
    | true =>
      have ht' : (Nat.beq s.frame.blockIdx target && Nat.beq s.frame.stmtIdx 0) = true := by
        simpa [BEq.beq] using ht
      conv => rhs; lhs; unfold Anneal.FunctionalTranslation.runMirToBlock
      simp only [↓reduceIte, ht']
      exact Iff.intro (fun h => by cases h; rfl) (fun h => by cases h; rfl)
    | false =>
      rw [live_runMirToBlock_step_of_not_target body target 0 s ht]
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases mirStep body s <;> exact Iff.intro (fun h => by cases h) (fun h => by cases h)
  | bound + 1, s, s_hit => by
    unfold runUntilTarget
    cases ht : (s.frame.blockIdx == target && s.frame.stmtIdx == 0) with
    | true =>
      have ht' : (Nat.beq s.frame.blockIdx target && Nat.beq s.frame.stmtIdx 0) = true := by
        simpa [BEq.beq] using ht
      conv => rhs; lhs; unfold Anneal.FunctionalTranslation.runMirToBlock
      simp only [↓reduceIte, ht']
      exact Iff.intro (fun h => by cases h; rfl) (fun h => by cases h; rfl)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [live_runMirToBlock_step_of_not_target body target (bound + 1) s ht]
      cases hs : mirStep body s with
      | cont s' =>
        exact runUntilTarget_reached_iff_live_runMirToBlock body target bound s' s_hit
      | done _ => exact Iff.intro (fun h => by cases h) (fun h => by cases h)
      | fault => exact Iff.intro (fun h => by cases h) (fun h => by cases h)

/-- **Exact bridge from header-advancing `runMirToBlock` to live
`Anneal.FunctionalTranslation.runMirToBlock`**: the prototype's `runMirToBlock`
reaches `s_hit` iff taking one mandatory `mirStep` (`mirStep body s = .cont s₁`)
followed by the live `Anneal.FunctionalTranslation.runMirToBlock` reaches `s_hit`. -/
theorem runMirToBlock_reached_iff_step_and_live (body : CapturedMir)
    (target : BasicBlockIdx) (s s_hit : MachineState) :
    runMirToBlock body target s = .reached s_hit ↔
      ∃ s₁, mirStep body s = .cont s₁ ∧
        Anneal.FunctionalTranslation.runMirToBlock (mirSegmentBound body + 1) body target s₁ = some s_hit := by
  unfold runMirToBlock runToTarget
  cases hs : mirStep body s with
  | cont s₁ =>
    rw [runUntilTarget_reached_iff_live_runMirToBlock]
    exact Iff.intro (fun h => ⟨s₁, rfl, h⟩) (fun ⟨s₂, hs₂, h⟩ => by cases hs₂; exact h)
  | done _ =>
    exact Iff.intro (fun h => by cases h) (fun ⟨_, hs₁, _⟩ => by cases hs₁)
  | fault =>
    exact Iff.intro (fun h => by cases h) (fun ⟨_, hs₁, _⟩ => by cases hs₁)

/-- **Outcome-collapse characterization of live `Anneal.FunctionalTranslation.runMirToBlock`**:
the live stepper returns `none` iff `runUntilTarget` does not return `.reached _`,
thereby collapsing `.halted`, `.stuck`, and `.outOfFuel` into a single `none`. -/
theorem runUntilTarget_not_reached_iff_live_runMirToBlock_none (body : CapturedMir)
    (target : BasicBlockIdx) (bound : Nat) (s : MachineState) :
    (∀ s_hit, runUntilTarget (mirStep body)
      (fun ms => ms.frame.blockIdx == target && ms.frame.stmtIdx == 0) bound s ≠ .reached s_hit) ↔
      Anneal.FunctionalTranslation.runMirToBlock (bound + 1) body target s = none := by
  cases hlive : Anneal.FunctionalTranslation.runMirToBlock (bound + 1) body target s with
  | none =>
    refine Iff.intro (fun _ => rfl) (fun _ s_hit hreach => ?_)
    have hsome := (runUntilTarget_reached_iff_live_runMirToBlock body target bound s s_hit).mp hreach
    rw [hlive] at hsome
    cases hsome
  | some s_hit =>
    refine Iff.intro (fun hall => ?_) (fun hnone => by cases hnone)
    have hreach := (runUntilTarget_reached_iff_live_runMirToBlock body target bound s s_hit).mpr hlive
    exact absurd hreach (hall s_hit)

/-- **Concrete witness that live `Anneal.FunctionalTranslation.runMirToBlock` conflates
normal halting, faulting, and out-of-fuel**: on the live `Anneal.MirLoops.countToNBody n`,
stepping from the return block `bb3`, from an invalid block `bb99`, and from `bb0` with
insufficient fuel all evaluate to `none` in the live stepper, whereas `runUntilTarget`
distinguishes `.halted`, `.stuck`, and `.outOfFuel`. -/
theorem live_runMirToBlock_conflates_halt_stuck_outOfFuel (n : Nat) :
    let body := Anneal.MirLoops.countToNBody n
    let atHdr := fun (ms : MachineState) => ms.frame.blockIdx == 1 && ms.frame.stmtIdx == 0
    let sHalt := Anneal.MirLoops.countStateMem 3 0 n emptyMemory
    let sFault := Anneal.MirLoops.countStateMem 99 0 0 emptyMemory
    let sOOF := Anneal.MirLoops.countStateMem 0 0 0 emptyMemory
    runUntilTarget (mirStep body) atHdr 7 sHalt = .halted (.normal (.scalar ⟨n, 4⟩, emptyMemory)) ∧
      Anneal.FunctionalTranslation.runMirToBlock 8 body 1 sHalt = none ∧
      runUntilTarget (mirStep body) atHdr 7 sFault = .stuck ∧
      Anneal.FunctionalTranslation.runMirToBlock 8 body 1 sFault = none ∧
      runUntilTarget (mirStep body) atHdr 1 sOOF = .outOfFuel ∧
      Anneal.FunctionalTranslation.runMirToBlock 2 body 1 sOOF = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

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

/-- Projection of the `n`-slot prefix of a frame, padding missing slots with `d`.
Pattern-matches on `env` once per slot so symbolic frames are never duplicated
across `headD`/`tail` projections. -/
def forcePureEnvD {α : Type} (d : α) : Nat → List α → List α
  | 0, _ => []
  | n + 1, [] => d :: forcePureEnvD d n []
  | n + 1, x :: xs => x :: forcePureEnvD d n xs

/-- **`forcePureEnv`**: projection-based normalization of the `n`-slot prefix. -/
def forcePureEnv {α : Type} [Inhabited α] (n : Nat) (env : List α) : List α :=
  forcePureEnvD default n env

theorem length_forcePureEnvD {α : Type} (d : α) :
    ∀ (n : Nat) (env : List α), (forcePureEnvD d n env).length = n
  | 0, _ => rfl
  | n + 1, [] => by simp only [forcePureEnvD, List.length_cons, length_forcePureEnvD d n []]
  | n + 1, _ :: xs => by simp only [forcePureEnvD, List.length_cons, length_forcePureEnvD d n xs]

theorem forcePureEnvD_eq_self {α : Type} (d : α) :
    ∀ (n : Nat) (env : List α), env.length = n → forcePureEnvD d n env = env
  | 0, [], _ => rfl
  | 0, _ :: _, h => absurd h (Nat.succ_ne_zero _)
  | n + 1, [], h => absurd h.symm (Nat.succ_ne_zero n)
  | n + 1, x :: xs, h => by
    have h' : xs.length = n := Nat.succ.inj h
    simp only [forcePureEnvD, forcePureEnvD_eq_self d n xs h']

/-- **Exact identity on well-sized frames**. -/
theorem forcePureEnv_eq_self {α : Type} [Inhabited α] (n : Nat) (env : List α)
    (h : env.length = n) : forcePureEnv n env = env :=
  forcePureEnvD_eq_self default n env h

/-- Closed form under arbitrary frame lengths (truncates when `n < env.length`
and pads with `n - env.length` copies of `d` when `env.length < n`). -/
theorem forcePureEnvD_eq_take_append_replicate {α : Type} (d : α) :
    ∀ (n : Nat) (env : List α),
      forcePureEnvD d n env = env.take n ++ List.replicate (n - env.length) d
  | 0, env => by
    simp only [forcePureEnvD, List.take_zero, Nat.zero_sub, List.replicate_zero, List.append_nil]
  | n + 1, [] => by
    simp only [forcePureEnvD, List.take_nil, List.nil_append, List.length_nil, Nat.sub_zero,
      List.replicate_succ, forcePureEnvD_eq_take_append_replicate d n []]
  | n + 1, x :: xs => by
    simp only [forcePureEnvD, List.take_succ_cons, List.cons_append, List.length_cons,
      Nat.succ_sub_succ_eq_sub, forcePureEnvD_eq_take_append_replicate d n xs]

/-- **Length-mismatch failure**: when `env.length ≠ n`, `forcePureEnv n env`
differs from `env`. -/
theorem forcePureEnv_ne_self_of_length_ne {α : Type} [Inhabited α] {n : Nat} {env : List α}
    (hne : env.length ≠ n) : forcePureEnv n env ≠ env := by
  intro heq
  have hlen := congrArg List.length heq
  rw [forcePureEnv, length_forcePureEnvD] at hlen
  exact hne hlen.symm

/-- **Exact biconditional**: `forcePureEnv n env = env` iff `env.length = n`. -/
theorem forcePureEnv_eq_self_iff {α : Type} [Inhabited α] (n : Nat) (env : List α) :
    forcePureEnv n env = env ↔ env.length = n :=
  ⟨fun h => by
    have hlen := congrArg List.length h
    rw [forcePureEnv, length_forcePureEnvD] at hlen
    exact hlen.symm,
   forcePureEnv_eq_self n env⟩

theorem getD_zero_eq_headD {α : Type} (env : List α) (d : α) : env.getD 0 d = env.headD d := by
  cases env <;> rfl

theorem getD_succ_eq_tail {α : Type} (env : List α) (i : Nat) (d : α) :
    env.getD (i + 1) d = env.tail.getD i d := by
  cases env <;> rfl

theorem getElem?_forcePureEnvD {α : Type} (d : α) :
    ∀ (n : Nat) (env : List α) (i : Nat),
      (forcePureEnvD d n env)[i]? = if i < n then some (env.getD i d) else none
  | 0, _, _ => by simp [forcePureEnvD]
  | n + 1, [], 0 => by
    simp only [forcePureEnvD, List.getElem?_cons_zero, List.getD_nil, Nat.zero_lt_succ, ↓reduceIte]
  | n + 1, _ :: _, 0 => by
    simp only [forcePureEnvD, List.getElem?_cons_zero, List.getD_cons_zero, Nat.zero_lt_succ, ↓reduceIte]
  | n + 1, [], i + 1 => by
    simp only [forcePureEnvD, List.getElem?_cons_succ, getElem?_forcePureEnvD d n [] i,
      List.getD_nil, Nat.add_lt_add_iff_right]
  | n + 1, _ :: xs, i + 1 => by
    simp only [forcePureEnvD, List.getElem?_cons_succ, getElem?_forcePureEnvD d n xs i,
      List.getD_cons_succ, Nat.add_lt_add_iff_right]

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
    simp only [List.set_cons_succ, forcePureEnvD, forcePureEnvD_set_comm d n xs i v h']

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

/-- Single-pass spine-forcing slot update: forces the list spine up to index `i`
and stops at `0` (`some (v :: xs)`), avoiding a second full-list traversal over
the untouched suffix `xs`. -/
def setSpine? {α : Type} : List α → Nat → α → Option (List α)
  | [], _, _ => some []
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, i + 1, v =>
    match setSpine? xs i v with
    | some xs' => some (x :: xs')
    | none => none

theorem setSpine?_eq_some_set {α : Type} :
    ∀ (env : List α) (i : Nat) (v : α), setSpine? env i v = some (env.set i v)
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | x :: xs, i + 1, v => by simp only [setSpine?, setSpine?_eq_some_set xs i v, List.set_cons_succ]

theorem setSpine?_eq_forceSpine?_set {α : Type} (env : List α) (i : Nat) (v : α) :
    setSpine? env i v = forceSpine? (env.set i v) := by
  rw [setSpine?_eq_some_set, forceSpine?_eq_some]

/-- Sequential local updates (`env[i₁] := v₁; …; env[i_K] := v_K`). -/
def applySlotUpdates {α : Type} (env : List α) (ups : List (Nat × α)) : List α :=
  ups.foldl (fun e u => e.set u.1 u.2) env

/-- Step-wise normalized execution: after every update the modified prefix spine
is forced via `setSpine?`, so the next update always acts on a flat literal. -/
def applySlotUpdatesForced {α : Type} : List (Nat × α) → List α → Option (List α)
  | [], env => some env
  | u :: ups, env =>
    match setSpine? env u.1 u.2 with
    | some env' => applySlotUpdatesForced ups env'
    | none => none

theorem applySlotUpdatesForced_eq {α : Type} :
    ∀ (ups : List (Nat × α)) (env : List α),
      applySlotUpdatesForced ups env = some (applySlotUpdates env ups)
  | [], _ => rfl
  | u :: ups, env => by
    simp only [applySlotUpdatesForced, setSpine?_eq_some_set, applySlotUpdates, List.foldl]
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

/-- **Single-pass forcing is `forcePureEnv`-normalization of the update**:
`setSpine?` returns exactly the `forcePureEnv` normal form of `env.set i v`. -/
theorem setSpine?_eq_some_forcePureEnv_set {α : Type} [Inhabited α] (env : List α) (i : Nat)
    (v : α) : setSpine? env i v = some (forcePureEnv env.length (env.set i v)) := by
  rw [setSpine?_eq_some_set, forcePureEnv_eq_self env.length (env.set i v) List.length_set]

/-- **The step-wise run computes the `forcePureEnv` normal form** of the
unnormalized update sequence (`applySlotUpdates`). -/
theorem applySlotUpdatesForced_eq_forcePureEnv {α : Type} [Inhabited α] (ups : List (Nat × α))
    (env : List α) :
    applySlotUpdatesForced ups env = some (forcePureEnv env.length (applySlotUpdates env ups)) := by
  rw [applySlotUpdatesForced_eq, forcePureEnv_eq_self env.length _ (length_applySlotUpdates ups env)]

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

/-- **Bridge from the live trusted slot update `Trusted.Sequence.set?`** (used by
`Anneal.MirLiftCore.evalPureStmt`) to single-pass forcing: in range the live update
*is* `setSpine?`, out of range it fails. -/
theorem liveSet?_eq_setSpine? {α : Type} (env : List α) (loc : Nat) (v : α) :
    Trusted.Sequence.set? env loc v = if loc < env.length then setSpine? env loc v else none := by
  unfold Trusted.Sequence.set?
  rw [setSpine?_eq_some_set]

/-- Sequential live slot updates through `Trusted.Sequence.set?` (failing on the
first out-of-range slot). -/
def applySlotUpdatesLive? {α : Type} : List (Nat × α) → List α → Option (List α)
  | [], env => some env
  | u :: ups, env =>
    match Trusted.Sequence.set? env u.1 u.2 with
    | some env' => applySlotUpdatesLive? ups env'
    | none => none

/-- **Live update chains are computed by the step-wise forced run**: when every
updated slot is in range, the live `Trusted.Sequence.set?` chain equals
`applySlotUpdatesForced`, so the benchmarked `rfl` strategy proves live chains. -/
theorem applySlotUpdatesLive?_eq_forced {α : Type} :
    ∀ (ups : List (Nat × α)) (env : List α), (∀ u ∈ ups, u.1 < env.length) →
      applySlotUpdatesLive? ups env = applySlotUpdatesForced ups env
  | [], _, _ => rfl
  | u :: ups, env, h => by
    have hu : u.1 < env.length := h u (List.mem_cons_self ..)
    have hrest : ∀ w ∈ ups, w.1 < (env.set u.1 u.2).length := fun w hw => by
      rw [List.length_set]
      exact h w (List.mem_cons_of_mem _ hw)
    have hlive : Trusted.Sequence.set? env u.1 u.2 = some (env.set u.1 u.2) := by
      unfold Trusted.Sequence.set?
      rw [ite_eq_left hu]
    simp only [applySlotUpdatesLive?, applySlotUpdatesForced, hlive, setSpine?_eq_some_set]
    exact applySlotUpdatesLive?_eq_forced ups (env.set u.1 u.2) hrest

/-- An out-of-range live update makes the live chain fail (where `List.set` would
silently ignore it). -/
theorem applySlotUpdatesLive?_oob {α : Type} (u : Nat × α) (ups : List (Nat × α)) (env : List α)
    (h : env.length ≤ u.1) : applySlotUpdatesLive? (u :: ups) env = none := by
  have hlive : Trusted.Sequence.set? env u.1 u.2 = none := by
    unfold Trusted.Sequence.set?
    rw [ite_eq_right (Nat.not_lt.mpr h)]
  simp only [applySlotUpdatesLive?, hlive]

/-- Two-pass step-wise forcing with the structure of the live
`Anneal.MirLiftCore.evalPureStmtNorm` / `set?_of_forcePureEnv?` normalization: a
bounds-checked `Trusted.Sequence.set?` followed by a full spine-forcing pass
(`forceSpine?`, the generic form of `forcePureEnv?`, see `forceSpine?_eq_live`).
Benchmarked as `local_slots/live_two_pass_rfl`. -/
def applySlotUpdatesTwoPass {α : Type} : List (Nat × α) → List α → Option (List α)
  | [], env => some env
  | u :: ups, env =>
    match (Trusted.Sequence.set? env u.1 u.2).bind forceSpine? with
    | some env' => applySlotUpdatesTwoPass ups env'
    | none => none

/-- The two-pass run computes exactly the live `Trusted.Sequence.set?` chain. -/
theorem applySlotUpdatesTwoPass_eq_live? {α : Type} :
    ∀ (ups : List (Nat × α)) (env : List α),
      applySlotUpdatesTwoPass ups env = applySlotUpdatesLive? ups env
  | [], _ => rfl
  | u :: ups, env => by
    cases h : Trusted.Sequence.set? env u.1 u.2 with
    | none => simp only [applySlotUpdatesTwoPass, applySlotUpdatesLive?, h, Option.bind_none]
    | some e =>
      simp only [applySlotUpdatesTwoPass, applySlotUpdatesLive?, h, Option.bind_some, forceSpine?_eq_some]
      exact applySlotUpdatesTwoPass_eq_live? ups e

/-- **Soundness of the live two-pass strategy**: a successful run (which implies
that every update was in range) proves the unnormalized update sequence. -/
theorem applySlotUpdates_eq_of_twoPass {α : Type} :
    ∀ {ups : List (Nat × α)} {env flat : List α},
      applySlotUpdatesTwoPass ups env = some flat → applySlotUpdates env ups = flat
  | [], _, _, h => Option.some.inj h
  | u :: ups, env, flat, h => by
    have hset : ∀ e, Trusted.Sequence.set? env u.1 u.2 = some e → e = env.set u.1 u.2 := by
      intro e he
      unfold Trusted.Sequence.set? at he
      by_cases hlt : u.1 < env.length
      · rw [ite_eq_left hlt] at he
        exact (Option.some.inj he).symm
      · rw [ite_eq_right hlt] at he
        cases he
    cases hs : Trusted.Sequence.set? env u.1 u.2 with
    | none => simp only [applySlotUpdatesTwoPass, hs, Option.bind_none] at h; cases h
    | some e =>
      simp only [applySlotUpdatesTwoPass, hs, Option.bind_some, forceSpine?_eq_some] at h
      rw [show applySlotUpdates env (u :: ups) = applySlotUpdates (env.set u.1 u.2) ups from rfl,
        ← hset e hs]
      exact applySlotUpdates_eq_of_twoPass h

/-- Single-pass constructor-forcing slot update over live `PureEnv`
(`List LocalSlot`): checks bounds like `Trusted.Sequence.set?`, forces both the
`List` spine and `LocalSlot` constructors (`.dead`, `.uninit`, `.init v`) along
the prefix `[0..loc]`, and stops at `loc` without a second pass over the tail. -/
def setPureEnvSlot? :
    Anneal.MirLiftCore.PureEnv → Nat →
      Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot → Option Anneal.MirLiftCore.PureEnv
  | [], _, _ => none
  | _ :: rest, 0, .dead => some (.dead :: rest)
  | _ :: rest, 0, .uninit => some (.uninit :: rest)
  | _ :: rest, 0, .init v => some (.init v :: rest)
  | .dead :: rest, i + 1, s =>
    match setPureEnvSlot? rest i s with
    | some rest' => some (.dead :: rest')
    | none => none
  | .uninit :: rest, i + 1, s =>
    match setPureEnvSlot? rest i s with
    | some rest' => some (.uninit :: rest')
    | none => none
  | .init v :: rest, i + 1, s =>
    match setPureEnvSlot? rest i s with
    | some rest' => some (.init v :: rest')
    | none => none

/-- **Single-pass `setPureEnvSlot?` equals live `Trusted.Sequence.set?`**. -/
theorem setPureEnvSlot?_eq_set? :
    ∀ (env : Anneal.MirLiftCore.PureEnv) (loc : Nat)
      (s : Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot),
      setPureEnvSlot? env loc s = Trusted.Sequence.set? env loc s
  | [], loc, s => by
    simp [setPureEnvSlot?, Trusted.Sequence.set?]
  | x :: rest, 0, s => by
    unfold Trusted.Sequence.set?
    have h0 : 0 < (x :: rest).length := Nat.zero_lt_succ rest.length
    rw [ite_eq_left h0]
    cases s <;> rfl
  | x :: rest, i + 1, s => by
    have ih := setPureEnvSlot?_eq_set? rest i s
    unfold Trusted.Sequence.set? at ih ⊢
    by_cases hlt : i < rest.length
    · have hlt' : i + 1 < (x :: rest).length := Nat.succ_lt_succ hlt
      rw [ite_eq_left hlt] at ih
      rw [ite_eq_left hlt']
      cases x <;> simp only [setPureEnvSlot?, ih, List.set_cons_succ]
    · have hlt' : ¬ i + 1 < (x :: rest).length := fun h => hlt (Nat.lt_of_succ_lt_succ h)
      rw [ite_eq_right hlt] at ih
      rw [ite_eq_right hlt']
      cases x <;> simp only [setPureEnvSlot?, ih]

/-- **Drop-in single-pass replacement for live `Anneal.MirLiftCore.set?_of_forcePureEnv?`**:
`setPureEnvSlot?` equals the two-pass `(set? env loc s).bind forcePureEnv?` used
in `MirLiftCore.lean`, eliminating the second full-frame traversal over the suffix. -/
theorem setPureEnvSlot?_eq_live_bind_forcePureEnv? (env : Anneal.MirLiftCore.PureEnv)
    (loc : Nat) (s : Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot) :
    setPureEnvSlot? env loc s =
      (Trusted.Sequence.set? env loc s).bind Anneal.MirLiftCore.forcePureEnv? := by
  rw [setPureEnvSlot?_eq_set?]
  cases Trusted.Sequence.set? env loc s with
  | none => rfl
  | some env' => exact (Anneal.MirLiftCore.forcePureEnv?_eq_some env').symm

/-- **Bridge from live `Anneal.MirLiftCore.evalPureStmtNorm` to `forceSpine?`**:
the live statement normalizer in `MirLiftCore.lean` equals `evalPureStmt`
followed by `forceSpine?`. -/
theorem evalPureStmtNorm_eq_bind_forceSpine?
    (body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir)
    (bbIdx : Trusted.Rustc.V2026_06_01.MirAst.BasicBlockIdx) (stmtIdx : Nat)
    (env : Anneal.MirLiftCore.PureEnv)
    (stmt : Trusted.Rustc.V2026_06_01.MirAst.Statement) :
    Anneal.MirLiftCore.evalPureStmtNorm body bbIdx stmtIdx env stmt =
      (Anneal.MirLiftCore.evalPureStmt body bbIdx stmtIdx env stmt).bind forceSpine? := by
  unfold Anneal.MirLiftCore.evalPureStmtNorm
  cases Anneal.MirLiftCore.evalPureStmt body bbIdx stmtIdx env stmt with
  | none => rfl
  | some rawEnv => exact (forceSpine?_eq_live rawEnv).symm

/-- **Bounds-checked single-pass spine-forcing slot update**: unlike `setSpine?`
(which returns `some []` out of bounds, matching `List.set` rather than
`Trusted.Sequence.set?`), `setSpineChecked?` returns `none` out of bounds and
forces the modified prefix `[0..loc]` in a single pass without calling
`env.length` or traversing the suffix `[loc+1..)`, and without pattern-matching
on untouched `LocalSlot` elements.  Benchmarked as
`local_slots/checked_single_pass_rfl`. -/
def setSpineChecked? {α : Type} : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, i + 1, v =>
    match setSpineChecked? xs i v with
    | some xs' => some (x :: xs')
    | none => none

/-- **Exact unconditional agreement with live `Trusted.Sequence.set?`**:
`setSpineChecked?` equals `Trusted.Sequence.set?` on every list and index
(both in-bounds and out-of-bounds, with no `loc < env.length` side condition). -/
theorem setSpineChecked?_eq_live_set? {α : Type} :
    ∀ (env : List α) (loc : Nat) (v : α),
      setSpineChecked? env loc v = Trusted.Sequence.set? env loc v
  | [], loc, v => by
    simp [setSpineChecked?, Trusted.Sequence.set?]
  | x :: xs, 0, v => by
    unfold Trusted.Sequence.set?
    have h0 : 0 < (x :: xs).length := Nat.zero_lt_succ xs.length
    rw [ite_eq_left h0]
    rfl
  | x :: xs, i + 1, v => by
    have ih := setSpineChecked?_eq_live_set? xs i v
    unfold Trusted.Sequence.set? at ih ⊢
    by_cases hlt : i < xs.length
    · have hlt' : i + 1 < (x :: xs).length := Nat.succ_lt_succ hlt
      rw [ite_eq_left hlt] at ih
      rw [ite_eq_left hlt']
      simp only [setSpineChecked?, ih, List.set_cons_succ]
    · have hlt' : ¬ i + 1 < (x :: xs).length := fun h => hlt (Nat.lt_of_succ_lt_succ h)
      rw [ite_eq_right hlt] at ih
      rw [ite_eq_right hlt']
      simp only [setSpineChecked?, ih]

/-- **Drop-in single-pass replacement for live `(set? env loc s).bind forcePureEnv?`**
that also works when untouched prefix slots are symbolic `LocalSlot` variables. -/
theorem setSpineChecked?_eq_live_bind_forcePureEnv? (env : Anneal.MirLiftCore.PureEnv)
    (loc : Nat) (s : Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot) :
    setSpineChecked? env loc s =
      (Trusted.Sequence.set? env loc s).bind Anneal.MirLiftCore.forcePureEnv? := by
  rw [setSpineChecked?_eq_live_set?]
  cases Trusted.Sequence.set? env loc s with
  | none => rfl
  | some env' => exact (Anneal.MirLiftCore.forcePureEnv?_eq_some env').symm

/-- **Symbolic `LocalSlot` framing by `rfl`**: unlike live `forcePureEnv?` and
`setPureEnvSlot?` (both of which pattern-match on `.dead`/`.uninit`/`.init` at
every prefix element and get stuck when an untouched slot is a symbolic
`s₀ : LocalSlot`), `setSpineChecked?` reduces to `some [...]` by `rfl`. -/
theorem setSpineChecked?_symbolic_slot_rfl
    (s₀ s₁ : Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot)
    (v₂ v₂' : Trusted.Rustc.V2026_06_01.MirSemantics.Value) :
    setSpineChecked? [s₀, s₁, .init v₂] 2 (.init v₂') = some [s₀, s₁, .init v₂'] :=
  rfl

/-- Bounds-checked single-pass step-wise update chain (benchmarked as
`local_slots/checked_single_pass_rfl`). -/
def applySlotUpdatesChecked {α : Type} : List (Nat × α) → List α → Option (List α)
  | [], env => some env
  | u :: ups, env =>
    match setSpineChecked? env u.1 u.2 with
    | some env' => applySlotUpdatesChecked ups env'
    | none => none

/-- `applySlotUpdatesChecked` equals the live `Trusted.Sequence.set?` chain on
every update list (both in-bounds and out-of-bounds). -/
theorem applySlotUpdatesChecked_eq_live? {α : Type} :
    ∀ (ups : List (Nat × α)) (env : List α),
      applySlotUpdatesChecked ups env = applySlotUpdatesLive? ups env
  | [], _ => rfl
  | u :: ups, env => by
    simp only [applySlotUpdatesChecked, applySlotUpdatesLive?, setSpineChecked?_eq_live_set?]
    cases Trusted.Sequence.set? env u.1 u.2 with
    | none => rfl
    | some env' => exact applySlotUpdatesChecked_eq_live? ups env'

/-- **Soundness of bounds-checked single-pass normalization**: a `rfl` proof of
`applySlotUpdatesChecked` proves the unnormalized `applySlotUpdates` chain. -/
theorem applySlotUpdates_eq_of_checked {α : Type} {ups : List (Nat × α)} {env flat : List α}
    (h : applySlotUpdatesChecked ups env = some flat) : applySlotUpdates env ups = flat := by
  rw [applySlotUpdatesChecked_eq_live?, ← applySlotUpdatesTwoPass_eq_live?] at h
  exact applySlotUpdates_eq_of_twoPass h

/-- **Soundness of the bare live chain** (`Trusted.Sequence.set?` without the
`forcePureEnv?` pass of `evalPureStmtNorm`): benchmarked as
`local_slots/ablation_live_set_only_rfl` to test whether the bounds check's
`env.length` traversal alone keeps `rfl` linear, i.e. whether the live forcing pass is
necessary. -/
theorem applySlotUpdates_eq_of_live? {α : Type} {ups : List (Nat × α)} {env flat : List α}
    (h : applySlotUpdatesLive? ups env = some flat) : applySlotUpdates env ups = flat := by
  rw [← applySlotUpdatesTwoPass_eq_live?] at h
  exact applySlotUpdates_eq_of_twoPass h

/-- **Single-pass drop-in replacement for live `Anneal.MirLiftCore.set?_of_forcePureEnv?`**:
proves `Trusted.Sequence.set? env loc s = some env'` directly from `setSpineChecked?`. -/
theorem set?_of_setSpineChecked? {env env' : Anneal.MirLiftCore.PureEnv}
    {loc : Trusted.Rustc.V2026_06_01.MirAst.Local}
    {s : Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot}
    (h : setSpineChecked? env loc s = some env') :
    Trusted.Sequence.set? env loc s = some env' := by
  rwa [← setSpineChecked?_eq_live_set?]

/-- **Single-pass drop-in replacement for live
`Anneal.MirLiftCore.evalPureStmtNorm_assign_local_of_evalRvalue`**: replaces the
two-pass `(set? env dstLoc (.init val)).bind forcePureEnv? = some env'` premise
in untrusted `MirLiftCore.lean` with single-pass `setSpineChecked?` (without
modifying `trusted/lean/` and without getting stuck on symbolic `LocalSlot`
prefix entries). -/
theorem evalPureStmtNorm_assign_local_of_setSpineChecked?
    {body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir}
    {bbIdx : Trusted.Rustc.V2026_06_01.MirAst.BasicBlockIdx} {stmtIdx : Nat}
    {env env' : Anneal.MirLiftCore.PureEnv}
    {dstLoc : Trusted.Rustc.V2026_06_01.MirAst.Local}
    {rv : Trusted.Rustc.V2026_06_01.MirAst.Rvalue} {span : String}
    {val : Trusted.Rustc.V2026_06_01.MirSemantics.Value}
    {oldSlot : Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot}
    (h_pure : Anneal.PureMirExec.isPureStatement
      (.assign { local_ := dstLoc, projection := [] } rv) = true)
    (h_rv : Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue env rv
      Trusted.Rustc.V2026_06_01.MirSemantics.emptyMemory body.localDecls body.layouts =
      .ok val env Trusted.Rustc.V2026_06_01.MirSemantics.emptyMemory)
    (h_get : Trusted.Sequence.get? env dstLoc = some oldSlot)
    (h_live : oldSlot ≠ .dead)
    (h_set : setSpineChecked? env dstLoc (.init val) = some env') :
    Anneal.MirLiftCore.evalPureStmtNorm body bbIdx stmtIdx env
      { kind := .assign { local_ := dstLoc, projection := [] } rv, span := span } = some env' := by
  rw [setSpineChecked?_eq_live_bind_forcePureEnv?] at h_set
  exact Anneal.MirLiftCore.evalPureStmtNorm_assign_local_of_evalRvalue
    h_pure h_rv h_get h_live h_set

/-- Unforced multi-statement pure execution matching live
`Anneal.MirLiftCore.evalPureStmtsN` without the per-statement `forcePureEnv?` pass. -/
def evalPureStmtsUnforced
    (body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir)
    (bbIdx : Trusted.Rustc.V2026_06_01.MirAst.BasicBlockIdx)
    (stmts : List Trusted.Rustc.V2026_06_01.MirAst.Statement) :
    Nat → Nat → Anneal.MirLiftCore.PureEnv → Option Anneal.MirLiftCore.PureEnv
  | 0, _, env => some env
  | n + 1, stmtIdx, env =>
    match Trusted.Sequence.get? stmts stmtIdx with
    | some stmt =>
      match Anneal.MirLiftCore.evalPureStmt body bbIdx stmtIdx env stmt with
      | some env₁ => evalPureStmtsUnforced body bbIdx stmts n (stmtIdx + 1) env₁
      | none => none
    | none => none

/-- **Bridge from live multi-statement `Anneal.MirLiftCore.evalPureStmtsN` to
unforced `evalPureStmt` execution**: extensionally identical on every block
segment.  Computationally they differ: the per-statement `forcePureEnv?` pass of
`evalPureStmtsN` is what keeps `rfl` evaluation linear (without it the `set?` chain is
exponential, `local_slots/ablation_live_set_only_rfl`), so the unforced form is a
specification, not a faster evaluator. -/
theorem evalPureStmtsN_eq_unforced
    (body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir)
    (bbIdx : Trusted.Rustc.V2026_06_01.MirAst.BasicBlockIdx)
    (stmts : List Trusted.Rustc.V2026_06_01.MirAst.Statement) :
    ∀ (n stmtIdx : Nat) (env : Anneal.MirLiftCore.PureEnv),
      Anneal.MirLiftCore.evalPureStmtsN body bbIdx stmts n stmtIdx env =
        evalPureStmtsUnforced body bbIdx stmts n stmtIdx env
  | 0, _, env => Anneal.MirLiftCore.forcePureEnv?_eq_some env
  | n + 1, stmtIdx, env => by
    unfold Anneal.MirLiftCore.evalPureStmtsN evalPureStmtsUnforced
    cases Trusted.Sequence.get? stmts stmtIdx with
    | none => rfl
    | some stmt =>
      dsimp only
      rw [Anneal.MirLiftCore.evalPureStmtNorm_eq_evalPureStmt]
      cases Anneal.MirLiftCore.evalPureStmt body bbIdx stmtIdx env stmt with
      | none => rfl
      | some env₁ => exact evalPureStmtsN_eq_unforced body bbIdx stmts n (stmtIdx + 1) env₁

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

/-- `CanonicalAt` implies `TypedAt` for the lens view at `base`. -/
theorem typedAt_of_canonicalAt {α : Type} {n : Nat} {c : FixedByteCodec α n} {base : Nat}
    {mem : Mem} (hc : CanonicalAt c base mem) (dflt : α) :
    TypedAt c base ((fieldLens c base dflt).readView mem) mem := by
  obtain ⟨hb, v, hv⟩ := (canonicalAt_iff c base mem).mp hc
  have hr : readTyped c base mem = some v := by
    unfold readTyped
    rw [sliceAbstractBytes_eq, ite_eq_left hb, hv]
    exact c.decode_encode v
  show readTyped c base mem = some ((readTyped c base mem).getD dflt)
  rw [hr]
  rfl

/-- Writing the first field of a padded pair updates the pair value in place
without disturbing the padding or second field. -/
theorem typedAt_laidOutPair_write_fst {α β : Type} {n₁ n₂ : Nat} {c₁ : FixedByteCodec α n₁}
    {pad : Nat} {c₂ : FixedByteCodec β n₂} {base : Nat} {a a' : α} {b : β} {mem mem' : Mem}
    (h : TypedAt (laidOutPair c₁ pad c₂) base (a, b) mem)
    (hw : writeTyped c₁ base a' mem = some mem') :
    TypedAt (laidOutPair c₁ pad c₂) base (a', b) mem' := by
  rw [typedAt_laidOutPair_iff] at h ⊢
  obtain ⟨hb, h₁, h₂⟩ := h
  have hlen := writeTyped_length hw
  obtain ⟨m₁, hw₁, ht₁, _⟩ := TypedAt.read_write_same c₁ a' ((typedAt_iff _ _ _ _).mp h₁).1
  rw [hw₁] at hw
  cases hw
  refine ⟨by omega, ht₁, ?_⟩
  exact TypedAt.frame_write (by unfold DisjointSlice; omega) hw₁ h₂

/-- **`FieldsValid` implies whole-struct `TypedAt` across a padded `laidOutPair`**:
regardless of arbitrary initialized/uninitialized bytes in the padding window
`[base + n₁, base + n₁ + pad)`, `FieldsValid` at `base` and `base + n₁ + pad`
establishes `TypedAt (laidOutPair c₁ pad c₂)` for the pair of lens views. -/
theorem typedAt_laidOutPair_of_fieldsValid {α β : Type} {n₁ n₂ : Nat}
    (c₁ : FixedByteCodec α n₁) (pad : Nat) (c₂ : FixedByteCodec β n₂)
    (base : Nat) (d₁ : α) (d₂ : β) {mem : Mem}
    (hv : FieldsValid c₁ base c₂ (base + n₁ + pad) mem) :
    TypedAt (laidOutPair c₁ pad c₂) base
      ((fieldLens c₁ base d₁).readView mem, (fieldLens c₂ (base + n₁ + pad) d₂).readView mem) mem := by
  rw [typedAt_laidOutPair_iff]
  obtain ⟨hb₂, _⟩ := (canonicalAt_iff c₂ (base + n₁ + pad) mem).mp hv.2
  exact ⟨by omega, typedAt_of_canonicalAt hv.1 d₁, typedAt_of_canonicalAt hv.2 d₂⟩

/-- **End-to-end `applyFieldWrites` → whole-struct `TypedAt (laidOutPair …)`**:
after any sequence `ws` of field-lens writes on a padded struct, the resulting
memory satisfies `TypedAt (laidOutPair c₁ pad c₂)` for `(lastLeft ws a₀, lastRight ws b₀)`
across arbitrary padding bytes. -/
theorem typedAt_laidOutPair_applyFieldWrites {α β : Type} {n₁ n₂ : Nat}
    (c₁ : FixedByteCodec α n₁) (pad : Nat) (c₂ : FixedByteCodec β n₂)
    (base : Nat) (d₁ : α) (d₂ : β) (ws : List (α ⊕ β)) {mem : Mem}
    (hv : FieldsValid c₁ base c₂ (base + n₁ + pad) mem) :
    TypedAt (laidOutPair c₁ pad c₂) base
      (lastLeft ws ((fieldLens c₁ base d₁).readView mem),
       lastRight ws ((fieldLens c₂ (base + n₁ + pad) d₂).readView mem))
      (applyFieldWrites (fieldLens c₁ base d₁) (fieldLens c₂ (base + n₁ + pad) d₂) ws mem) := by
  have hd : DisjointSlice base n₁ (base + n₁ + pad) n₂ := by
    unfold DisjointSlice
    exact Or.inr (Or.inr (Or.inl (by omega)))
  obtain ⟨hL₁, hL₂, hI⟩ := subplaceFieldLens_disjoint c₁ c₂ base (base + n₁ + pad) d₁ d₂ hd
  obtain ⟨hv', h₁, h₂⟩ := applyFieldWrites_spec hL₁ hL₂ hI ws mem hv
  rw [← h₁, ← h₂]
  exact typedAt_laidOutPair_of_fieldsValid c₁ pad c₂ base d₁ d₂ hv'

/-- **Bridge from live `Anneal.SepLogicLenses.BorrowSubplace.disjointOn` to
`DisjointSlice`, `LawfulMutLens`, and `IndependentLenses`**: on a shared
aggregate allocation (`k₁.allocId = k₂.allocId`), `BorrowSubplace.disjointOn`
implies distinct field indices `f₁ ≠ f₂`, which under any non-overlapping
struct layout yields disjoint byte windows and independent field lenses. -/
theorem subplaceFieldLens_of_borrowSubplace_disjointOn
    {α β : Type} {subplaceOf : Anneal.UnsafeObligations.RawPtrVal → Anneal.SepLogicLenses.BorrowSubplace}
    {k₁ k₂ : Anneal.UnsafeObligations.RawPtrVal}
    (fieldOff fieldLen : Trusted.Rustc.V2026_06_01.MirAst.FieldIdx → Nat)
    (hLayout : ∀ f₁ f₂, f₁ ≠ f₂ →
      DisjointSlice (fieldOff f₁) (fieldLen f₁) (fieldOff f₂) (fieldLen f₂))
    (hDisj : Anneal.SepLogicLenses.BorrowSubplace.disjointOn subplaceOf k₁ k₂)
    (hSameAlloc : k₁.allocId = k₂.allocId) :
    ∃ f₁ ty₁ f₂ ty₂,
      subplaceOf k₁ = .field f₁ ty₁ ∧
      subplaceOf k₂ = .field f₂ ty₂ ∧
      f₁ ≠ f₂ ∧
      DisjointSlice (fieldOff f₁) (fieldLen f₁) (fieldOff f₂) (fieldLen f₂) ∧
      ∀ (c₁ : FixedByteCodec α (fieldLen f₁)) (c₂ : FixedByteCodec β (fieldLen f₂))
        (d₁ : α) (d₂ : β),
        Anneal.FunctionalTranslation.LawfulMutLens
          (fieldLens c₁ (fieldOff f₁) d₁)
          (FieldsValid c₁ (fieldOff f₁) c₂ (fieldOff f₂)) ∧
        Anneal.FunctionalTranslation.LawfulMutLens
          (fieldLens c₂ (fieldOff f₂) d₂)
          (FieldsValid c₁ (fieldOff f₁) c₂ (fieldOff f₂)) ∧
        Anneal.SepLogicLenses.IndependentLenses
          (fieldLens c₁ (fieldOff f₁) d₁) (fieldLens c₂ (fieldOff f₂) d₂)
          (FieldsValid c₁ (fieldOff f₁) c₂ (fieldOff f₂)) := by
  rcases hDisj.2 with hNeAlloc | ⟨f₁, ty₁, f₂, ty₂, hS₁, hS₂, hNeF⟩
  · exact absurd hSameAlloc hNeAlloc
  · have hSlice := hLayout f₁ f₂ hNeF
    exact ⟨f₁, ty₁, f₂, ty₂, hS₁, hS₂, hNeF, hSlice,
      fun c₁ c₂ d₁ d₂ => subplaceFieldLens_disjoint c₁ c₂ (fieldOff f₁) (fieldOff f₂) d₁ d₂ hSlice⟩

/-- Non-vacuity of `subplaceFieldLens_of_borrowSubplace_disjointOn`: the layout
hypothesis (quantified over *every* pair of distinct field indices) is satisfiable
by a concrete two-field layout (field `f` at offset `2 f`, one byte wide for
`f ≤ 1` and zero-width otherwise), and two distinctly tagged pointers into fields
`0` and `1` of one allocation satisfy the live `BorrowSubplace.disjointOn`. -/
theorem subplaceFieldLens_of_borrowSubplace_disjointOn_nonvacuous
    (ty : Trusted.Rustc.V2026_06_01.MirAst.Ty) :
    (∀ f₁ f₂ : Trusted.Rustc.V2026_06_01.MirAst.FieldIdx, f₁ ≠ f₂ →
      DisjointSlice (2 * f₁) (if f₁ ≤ 1 then 1 else 0) (2 * f₂) (if f₂ ≤ 1 then 1 else 0)) ∧
    Anneal.SepLogicLenses.BorrowSubplace.disjointOn (fun k => .field k.offset ty)
      { allocId := 0, offset := 0, tag := 1 } { allocId := 0, offset := 1, tag := 2 } := by
  refine ⟨fun f₁ f₂ hne => ?_, ⟨by decide, Or.inr ⟨0, ty, 1, ty, rfl, rfl, by decide⟩⟩⟩
  unfold DisjointSlice
  by_cases h₁ : f₁ ≤ 1
  · rw [ite_eq_left h₁]
    by_cases h₂ : f₂ ≤ 1
    · rw [ite_eq_left h₂]
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inr (Or.inr (Or.inl (by omega)))
      · exact Or.inr (Or.inr (Or.inr (by omega)))
    · rw [ite_eq_right h₂]
      exact Or.inr (Or.inl rfl)
  · rw [ite_eq_right h₁]
    exact Or.inl rfl

/-- Relational two-field validity (`TypedAt` at each field window, permitting
arbitrary initialized or uninitialized internal padding inside nested padded
field codecs, unlike `FieldsValid` / `CanonicalAt`). -/
def FieldsTyped {α β : Type} {n₁ n₂ : Nat} (c₁ : FixedByteCodec α n₁) (base₁ : Nat)
    (c₂ : FixedByteCodec β n₂) (base₂ : Nat) (mem : Mem) : Prop :=
  (∃ a, TypedAt c₁ base₁ a mem) ∧ (∃ b, TypedAt c₂ base₂ b mem)

theorem fieldsTyped_of_fieldsValid {α β : Type} {n₁ n₂ : Nat} (c₁ : FixedByteCodec α n₁)
    (base₁ : Nat) (c₂ : FixedByteCodec β n₂) (base₂ : Nat) {mem : Mem}
    (d₁ : α) (d₂ : β) (hv : FieldsValid c₁ base₁ c₂ base₂ mem) :
    FieldsTyped c₁ base₁ c₂ base₂ mem :=
  ⟨⟨_, typedAt_of_canonicalAt hv.1 d₁⟩, ⟨_, typedAt_of_canonicalAt hv.2 d₂⟩⟩

/-- **Nested padded sub-structs separate `FieldsTyped` from `FieldsValid`**:
when field 1 is itself a padded pair `laidOutPair u8 1 u8` with an initialized
padding byte `.init p none`, relational `FieldsTyped` holds while canonical
`FieldsValid` fails. -/
theorem fieldsTyped_nested_init_padding_not_fieldsValid (a b p c : UInt8) :
    let c₁ := laidOutPair Anneal.ByteCodec.FixedByteCodec.u8 1 Anneal.ByteCodec.FixedByteCodec.u8
    let c₂ := Anneal.ByteCodec.FixedByteCodec.u8
    let mem : Mem := [.init a none, .init p none, .init b none, .init c none]
    FieldsTyped c₁ 0 c₂ 3 mem ∧ ¬ FieldsValid c₁ 0 c₂ 3 mem := by
  intro c₁ c₂ mem
  refine ⟨⟨⟨(a, b), rfl⟩, ⟨c, rfl⟩⟩, ?_⟩
  rintro ⟨⟨⟨a', b'⟩, hslice⟩, _⟩
  have hsl : sliceAbstractBytes mem 0 3 = some [.init a none, .init p none, .init b none] := rfl
  rw [hsl, Option.some.injEq] at hslice
  have henc := laidOutPair_encode_eq Anneal.ByteCodec.FixedByteCodec.u8 1
    Anneal.ByteCodec.FixedByteCodec.u8 a' b'
  rw [← hslice] at henc
  simp [Anneal.ByteCodec.FixedByteCodec.u8, Anneal.ByteCodec.FixedByteCodec.ofRoundTrip] at henc

/-- **Exact obstruction to `LawfulMutLens` without `CanonicalAt`**: on a padded
codec `laidOutPair u8 1 u8`, `fieldLens` is *not* a `LawfulMutLens` over
relational `∃ ab, TypedAt … mem`, because `writeBack_readView` overwrites an
initialized padding byte `.init 1 none` with `.uninit`. -/
theorem not_lawfulMutLens_fieldLens_laidOutPair_typedAt (d : UInt8 × UInt8) :
    let c := laidOutPair Anneal.ByteCodec.FixedByteCodec.u8 1 Anneal.ByteCodec.FixedByteCodec.u8
    ¬ Anneal.FunctionalTranslation.LawfulMutLens (fieldLens c 0 d)
        (fun mem => ∃ ab, TypedAt c 0 ab mem) := by
  intro c hLaw
  have hv : ∃ ab, TypedAt c 0 ab ([.init 0 none, .init 1 none, .init 2 none] : Mem) := ⟨(0, 2), rfl⟩
  have hgetput := hLaw.writeBack_readView ([.init 0 none, .init 1 none, .init 2 none] : Mem) hv
  change ([.init 0 none, .uninit, .init 2 none] : Mem) = [.init 0 none, .init 1 none, .init 2 none] at hgetput
  injection hgetput with _ htl
  injection htl with hmid _
  cases hmid

/-- **Relational `FieldsTyped` suffices for `K` sequential `fieldLens` writes**:
because `applyFieldWrites` uses only put-get and disjoint-field framing (never
`writeBack_readView`), `applyFieldWrites` preserves `FieldsTyped` and computes
`lastLeft`/`lastRight` even when the field codecs contain internal padding with
non-canonical initialized bytes. -/
theorem applyFieldWrites_fieldsTyped_spec {α β : Type} {n₁ n₂ : Nat}
    (c₁ : FixedByteCodec α n₁) (c₂ : FixedByteCodec β n₂) (base₁ base₂ : Nat)
    (d₁ : α) (d₂ : β) (hd : DisjointSlice base₁ n₁ base₂ n₂) :
    ∀ (ws : List (α ⊕ β)) (mem : Mem),
      FieldsTyped c₁ base₁ c₂ base₂ mem →
      FieldsTyped c₁ base₁ c₂ base₂
          (applyFieldWrites (fieldLens c₁ base₁ d₁) (fieldLens c₂ base₂ d₂) ws mem) ∧
        (fieldLens c₁ base₁ d₁).readView
          (applyFieldWrites (fieldLens c₁ base₁ d₁) (fieldLens c₂ base₂ d₂) ws mem) =
          lastLeft ws ((fieldLens c₁ base₁ d₁).readView mem) ∧
        (fieldLens c₂ base₂ d₂).readView
          (applyFieldWrites (fieldLens c₁ base₁ d₁) (fieldLens c₂ base₂ d₂) ws mem) =
          lastRight ws ((fieldLens c₂ base₂ d₂).readView mem)
  | [], _, hv => ⟨hv, rfl, rfl⟩
  | .inl a :: ws, m, ⟨⟨a₀, ha₀⟩, ⟨b₀, hb₀⟩⟩ => by
    have hb₁ : base₁ + n₁ ≤ m.length := ((typedAt_iff c₁ base₁ a₀ m).mp ha₀).1
    have hwb : (fieldLens c₁ base₁ d₁).writeBack a m = splice m base₁ (c₁.encode a) :=
      fieldLens_writeBack_eq c₁ d₁ a hb₁
    have ha' : TypedAt c₁ base₁ a (splice m base₁ (c₁.encode a)) :=
      readTyped_splice_same c₁ a hb₁
    have hb' : TypedAt c₂ base₂ b₀ (splice m base₁ (c₁.encode a)) := by
      show readTyped c₂ base₂ (splice m base₁ (c₁.encode a)) = some b₀
      rw [readTyped_splice_disjoint c₁ c₂ a hb₁ hd]
      exact hb₀
    have ih := applyFieldWrites_fieldsTyped_spec c₁ c₂ base₁ base₂ d₁ d₂ hd ws
      (splice m base₁ (c₁.encode a)) ⟨⟨a, ha'⟩, ⟨b₀, hb'⟩⟩
    rw [show applyFieldWrites (fieldLens c₁ base₁ d₁) (fieldLens c₂ base₂ d₂) (.inl a :: ws) m =
        applyFieldWrites (fieldLens c₁ base₁ d₁) (fieldLens c₂ base₂ d₂) ws (splice m base₁ (c₁.encode a))
      from by simp only [applyFieldWrites, hwb]]
    refine ⟨ih.1, ?_, ?_⟩
    · rw [ih.2.1]
      have hr : (fieldLens c₁ base₁ d₁).readView (splice m base₁ (c₁.encode a)) = a := by
        show (readTyped c₁ base₁ (splice m base₁ (c₁.encode a))).getD d₁ = a
        rw [ha']
        rfl
      rw [hr]
      rfl
    · rw [ih.2.2]
      have hr : (fieldLens c₂ base₂ d₂).readView (splice m base₁ (c₁.encode a)) =
          (fieldLens c₂ base₂ d₂).readView m := by
        show (readTyped c₂ base₂ (splice m base₁ (c₁.encode a))).getD d₂ =
          (readTyped c₂ base₂ m).getD d₂
        rw [readTyped_splice_disjoint c₁ c₂ a hb₁ hd]
      rw [hr]
      rfl
  | .inr b :: ws, m, ⟨⟨a₀, ha₀⟩, ⟨b₀, hb₀⟩⟩ => by
    have hb₂ : base₂ + n₂ ≤ m.length := ((typedAt_iff c₂ base₂ b₀ m).mp hb₀).1
    have hwb : (fieldLens c₂ base₂ d₂).writeBack b m = splice m base₂ (c₂.encode b) :=
      fieldLens_writeBack_eq c₂ d₂ b hb₂
    have hb' : TypedAt c₂ base₂ b (splice m base₂ (c₂.encode b)) :=
      readTyped_splice_same c₂ b hb₂
    have ha' : TypedAt c₁ base₁ a₀ (splice m base₂ (c₂.encode b)) := by
      show readTyped c₁ base₁ (splice m base₂ (c₂.encode b)) = some a₀
      rw [readTyped_splice_disjoint c₂ c₁ b hb₂ hd.symm]
      exact ha₀
    have ih := applyFieldWrites_fieldsTyped_spec c₁ c₂ base₁ base₂ d₁ d₂ hd ws
      (splice m base₂ (c₂.encode b)) ⟨⟨a₀, ha'⟩, ⟨b, hb'⟩⟩
    rw [show applyFieldWrites (fieldLens c₁ base₁ d₁) (fieldLens c₂ base₂ d₂) (.inr b :: ws) m =
        applyFieldWrites (fieldLens c₁ base₁ d₁) (fieldLens c₂ base₂ d₂) ws (splice m base₂ (c₂.encode b))
      from by simp only [applyFieldWrites, hwb]]
    refine ⟨ih.1, ?_, ?_⟩
    · rw [ih.2.1]
      have hr : (fieldLens c₁ base₁ d₁).readView (splice m base₂ (c₂.encode b)) =
          (fieldLens c₁ base₁ d₁).readView m := by
        show (readTyped c₁ base₁ (splice m base₂ (c₂.encode b))).getD d₁ =
          (readTyped c₁ base₁ m).getD d₁
        rw [readTyped_splice_disjoint c₂ c₁ b hb₂ hd.symm]
      rw [hr]
      rfl
    · rw [ih.2.2]
      have hr : (fieldLens c₂ base₂ d₂).readView (splice m base₂ (c₂.encode b)) = b := by
        show (readTyped c₂ base₂ (splice m base₂ (c₂.encode b))).getD d₂ = b
        rw [hb']
        rfl
      rw [hr]
      rfl

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

/-- Per-location transition; `none` is undefined behavior.  This is Miri's
`perform_access` (per-permission transition, then the `ProtectedDisabled`
protector check guarded by `accessed`), with Miri's `skip_if_known_noop` rule that
a foreign access to a `Disabled` node is a no-op, and with a protected
`ReservedIM` (an invariant violation that Miri asserts away) failing closed.
`performTransition_accessed_eq_live` / `performTransition_unaccessed_eq_live`
prove it equal to the live trusted `treeBorrowNodeAccess` /
`treeBorrowPermTransition`. -/
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
    | .reservedIM => if isProtected then none else some ⟨.reservedIM, st.accessed⟩
    | .active =>
      if isProtected then (if st.accessed then none else some ⟨.disabled, st.accessed⟩)
      else some ⟨.frozen, st.accessed⟩
    | .frozen => some ⟨.frozen, st.accessed⟩
    | .disabled => some ⟨.disabled, st.accessed⟩
  | .foreignAccess, .write =>
    match st.perm with
    | .reservedIM => if isProtected then none else some ⟨.reservedIM, st.accessed⟩
    | .disabled => some ⟨.disabled, st.accessed⟩
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

/-- Non-ancestor states that never trap under foreign reads or writes: unprotected,
or unaccessed (Miri's `accessed` guard on the protector check) and not the
fail-closed protected `ReservedIM`. -/
def NonAncestorSafe (st : LocationState) (isProt : Bool) : Prop :=
  isProt = false ∨ (st.accessed = false ∧ st.perm ≠ .reservedIM)

instance (st : LocationState) (isProt : Bool) : Decidable (NonAncestorSafe st isProt) :=
  inferInstanceAs (Decidable (isProt = false ∨ (st.accessed = false ∧ st.perm ≠ .reservedIM)))

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
    (prot : Option ProtectorKind) (initPerm : Permission) (hInit : initPerm ≠ .reservedIM)
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

/-- **Parent-write-before-reborrow soundness**: when the callee writes through
the protected argument `t_arg` on `parentRange` *before* reborrowing `t_ret` on
`subRange ⊆ parentRange`, `t_arg` becomes `Active` across all of `parentRange`
and emits an implicit write at two-stage release under `skipChildrenOfAccessed`,
yet `t_ret` still retains `HasUniqueWritePerm` after release. -/
theorem reborrow_return_after_parent_write_unique_write_perm {tree0 : BorrowTree}
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
    let tree2 := applyTreeAccess tree1 t_arg .write parentRange active1 .visitChildrenOfAccessed
    let tree3 := retagChild tree2 t_arg t_ret none (initPermOf .mut) subRange active1
    let tree_post := applyReleaseProtector tree3 t_arg active1
    let active_post := removeActiveProtector active1 callId
    TreeAccessNoUB tree1 t_arg .write parentRange active1 .visitChildrenOfAccessed ∧
      releaseProtectorNoUB tree3 t_arg active1 ∧
      HasUniqueWritePerm tree_post t_ret subRange active_post ∧
      TreeAccessNoUB tree_post t_ret .write subRange active_post .visitChildrenOfAccessed := by
  intro active1 tree1 tree2 tree3 tree_post active_post
  have hAct : active_post = activeCaller := removeActiveProtector_insert hCallFresh
  have hPerm0' := hasUniqueWritePerm_insert_fresh_callId hFreshCallId hPerm0
  have hTree1Perm : HasUniqueWritePerm tree1 t_arg parentRange active1 :=
    (retagChild_hasUniqueWritePerm (some (.strong callId)) fnEntry_writable hPerm0'
      (ByteRange.Sub.refl _) hFreshArg).2
  obtain ⟨hParentWriteNoUB, hTree2ArgPerm⟩ :=
    local_access_preserves_hasUniqueWritePerm .write hTree1Perm (ByteRange.Sub.refl _)
  have hFreshRet2 : tree2.present t_ret = false := by
    show tree1.present t_ret = false
    rw [retagChild_present, decide_eq_false hRetNeArg, Bool.false_or]
    exact hFreshRet
  have hTree3ArgPerm : HasUniqueWritePerm tree3 t_arg parentRange active1 :=
    retagUnprotectedChild_preserves_parent_hasUniqueWritePerm hTree2ArgPerm hFreshRet2
  have hTree3RetPerm : HasUniqueWritePerm tree3 t_ret subRange active1 :=
    (retagChild_hasUniqueWritePerm none initPermOf_mut_writable hTree2ArgPerm hSub hFreshRet2).2
  have hState : CalleeReborrowState tree3 t_arg t_ret parentRange subRange activeCaller callId := by
    refine ⟨hSub, hTree3ArgPerm, hTree3RetPerm.tag_present,
      isAnc_child_of_retag hTree2ArgPerm.wf hTree2ArgPerm.tag_present, hRetNeArg, ?_,
      hTree3RetPerm.ancestors_writable, ?_⟩
    · intro b hAcc
      cases hbP : parentRange.contains b with
      | true => rfl
      | false =>
        have hbS : subRange.contains b = false := by
          cases h : subRange.contains b with
          | false => rfl
          | true => have := hSub b h; rw [hbP] at this; cases this
        have h3 : tree3.locState t_arg b = tree2.locState t_arg b := by
          show (retagChild tree2 t_arg t_ret none (initPermOf .mut) subRange active1).locState t_arg b = _
          rw [retagChild_locState_out _ _ _ _ _ _ _ _ _ hbS,
            insertChildNode_locState_of_ne _ _ _ _ _ (Ne.symm hRetNeArg)]
        have h2 : tree2.locState t_arg b = tree1.locState t_arg b :=
          applyTreeAccess_locState_out _ _ _ _ _ _ _ _ hbP
        have h1 : (tree1.locState t_arg b).accessed = parentRange.contains b :=
          retagChild_child_accessed (by intro h; cases h) b
        rw [h3, h2, h1, hbP] at hAcc
        cases hAcc
    · intro d hDesc hdNe
      by_cases hdRet : d = t_ret
      · rw [hdRet]
        show (insertChildNode tree2 t_arg t_ret none (initPermOf .mut)).isTagProtected t_ret activeCaller = false
        exact insertChildNode_isTagProtected_child_none _ _ _ _ _
      · have h2 : tree2.isAnc t_arg d = true :=
          retag_desc_cases hDesc hdRet (Ne.symm hRetNeArg)
        have h1 : tree1.isAnc t_arg d = true := h2
        rw [retag_not_desc_of_new hdNe] at h1
        cases h1
  obtain ⟨hRelNoUB, _, hPostPerm⟩ := releaseProtector_preserves_reborrow_child hState
  rw [hAct]
  obtain ⟨hCallerWriteNoUB, _⟩ :=
    local_access_preserves_hasUniqueWritePerm .write hPostPerm (ByteRange.Sub.refl _)
  exact ⟨hParentWriteNoUB, hRelNoUB, hPostPerm, hCallerWriteNoUB⟩

/-- **Parent-write-after-reborrow disables child**: if the callee writes through
`t_arg` on `subRange` *after* reborrowing `t_ret` under `t_arg`, the write is
foreign to `t_ret`, disabling `t_ret` at every byte `b ∈ subRange` so subsequent
writes through `t_ret` fault. -/
theorem callee_parent_write_after_reborrow_disables_child {tree0 : BorrowTree}
    {t_parent t_arg t_ret : BorTag} {parentRange subRange : ByteRange}
    {activeCaller : ActiveProtectors} {callId : CallId} {b : Nat}
    (hRetNeArg : t_ret ≠ t_arg)
    (hb : subRange.contains b = true) :
    let active1 := insertActiveProtector activeCaller callId
    let tree1 := retagChild tree0 t_parent t_arg (some (.strong callId)) (.reservedFrz false)
      parentRange active1
    let tree2 := retagChild tree1 t_arg t_ret none (initPermOf .mut) subRange active1
    let tree3 := applyTreeAccess tree2 t_arg .write subRange active1 .visitChildrenOfAccessed
    tree3.locState t_ret b = ⟨.disabled, true⟩ ∧
      ¬ TreeAccessNoUB tree3 t_ret .write ⟨b, b + 1⟩ active1 .visitChildrenOfAccessed := by
  intro active1 tree1 tree2 tree3
  have hRetPres2 : tree2.present t_ret = true := by
    rw [retagChild_present, decide_eq_true rfl, Bool.true_or]
  have hRetNotAncArg : tree2.isAnc t_ret t_arg = false :=
    retag_not_desc_of_new (tree := tree1) (t_parent := t_arg) (t_child := t_ret)
      (prot := none) (initPerm := initPermOf .mut) (range := subRange) (active := active1)
      (Ne.symm hRetNeArg)
  have hRetProt : tree2.isTagProtected t_ret active1 = false := by
    show (insertChildNode tree1 t_arg t_ret none (initPermOf .mut)).isTagProtected t_ret active1 = false
    exact insertChildNode_isTagProtected_child_none _ _ _ _ _
  have hRetLoc2 : tree2.locState t_ret b = ⟨.reservedFrz false, true⟩ := by
    show (applyTreeAccess (insertChildNode tree1 t_arg t_ret none (initPermOf .mut)) t_ret .read
      subRange active1 .visitChildrenOfAccessed).locState t_ret b = _
    rw [applyTreeAccess_locState_in _ _ _ _ _ _ _ _
      (by rw [insertChildNode_present, decide_eq_true rfl, Bool.true_or]) hb,
      nodeAccessRelatedness_anc (by rw [insertChildNode_isAnc_child, decide_eq_true rfl, Bool.true_or]),
      insertChildNode_locState_child]
    rfl
  have hRetLoc3 : tree3.locState t_ret b = ⟨.disabled, true⟩ := by
    show (applyTreeAccess tree2 t_arg .write subRange active1 .visitChildrenOfAccessed).locState t_ret b = _
    rw [applyTreeAccess_locState_in _ _ _ _ _ _ _ _ hRetPres2 hb,
      nodeAccessRelatedness_visit_foreign hRetNotAncArg]
    show (match performTransition .write .foreignAccess (tree2.isTagProtected t_ret active1)
      (tree2.locState t_ret b) with | some st' => st' | none => _) = _
    rw [hRetProt, hRetLoc2]
    rfl
  refine ⟨hRetLoc3, ?_⟩
  intro hNoUB
  have hRefl3 : tree3.isAnc t_ret t_ret = true := by
    show (insertChildNode tree1 t_arg t_ret none (initPermOf .mut)).isAnc t_ret t_ret = true
    rw [insertChildNode_isAnc_child, decide_eq_true rfl, Bool.true_or]
  have hAt := hNoUB t_ret b hRetPres2
    ((ByteRange.contains_iff _ _).mpr ⟨Nat.le_refl b, Nat.lt_succ_self b⟩)
  rw [nodeAccessRelatedness_anc hRefl3] at hAt
  change (performTransition .write .localAccess _ (tree3.locState t_ret b)).isSome = true at hAt
  rw [hRetLoc3] at hAt
  cases hAt

/-- **Overlapping `reborrowFootprint` failure**: if a `TrustedFnSpec` declares
two `&mut` reborrows `(r₁, .mut)` and `(r₂, .mut)` that overlap at byte `b`
(`r₁.contains b = true ∧ r₂.contains b = true`), writing through the first
returned reference (`t_arg + 1`) at `r₁` disables the second returned reference
(`t_arg + 1 + 1`) at `b`, refuting `HasUniqueWritePerm` and causing both reads
and writes through `t_arg + 1 + 1` at `⟨b, b + 1⟩` to fault. -/
theorem overlapping_reborrowFootprint_write_disables_sibling {tree0 : BorrowTree}
    {t_parent t_arg : BorTag} {argRange r₁ r₂ : ByteRange}
    {activeCaller : ActiveProtectors} {callId : CallId} {b : Nat}
    (hb1 : r₁.contains b = true) (hb2 : r₂.contains b = true) :
    let spec : TrustedFnSpec := ⟨argRange, [(r₁, .mut), (r₂, .mut)]⟩
    let out := spec.run tree0 activeCaller t_parent t_arg callId
    let tree_w1 := applyTreeAccess out.tree (t_arg + 1) .write r₁ out.active .visitChildrenOfAccessed
    out.rets = [t_arg + 1, t_arg + 1 + 1] ∧
      (tree_w1.locState (t_arg + 1 + 1) b).perm = .disabled ∧
      ¬ HasUniqueWritePerm tree_w1 (t_arg + 1 + 1) r₂ out.active ∧
      ¬ TreeAccessNoUB tree_w1 (t_arg + 1 + 1) .write ⟨b, b + 1⟩ out.active .visitChildrenOfAccessed ∧
      ¬ TreeAccessNoUB tree_w1 (t_arg + 1 + 1) .read ⟨b, b + 1⟩ out.active .visitChildrenOfAccessed := by
  intro spec out tree_w1
  have hne21 : t_arg + 1 + 1 ≠ t_arg + 1 := Nat.succ_ne_self (t_arg + 1)
  have hne20 : t_arg + 1 + 1 ≠ t_arg := Nat.ne_of_gt (Nat.lt_succ_of_lt (Nat.lt_succ_self t_arg))
  let active1 := insertActiveProtector activeCaller callId
  let tree1 := retagChild tree0 t_parent t_arg (some (.strong callId)) (.reservedFrz false)
    argRange active1
  let tree2 := retagChild tree1 t_arg (t_arg + 1) none (initPermOf .mut) r₁ active1
  let tree3 := retagChild tree2 t_arg (t_arg + 1 + 1) none (initPermOf .mut) r₂ active1
  have hRPres3 : tree3.present (t_arg + 1 + 1) = true := by
    rw [retagChild_present, decide_eq_true rfl, Bool.true_or]
  have hRNotAncArg3 : tree3.isAnc (t_arg + 1 + 1) t_arg = false :=
    retag_not_desc_of_new (Ne.symm hne20)
  have hArgAncR3 : tree3.isAnc t_arg (t_arg + 1 + 1) = true := by
    show (insertChildNode tree2 t_arg (t_arg + 1 + 1) none (initPermOf .mut)).isAnc t_arg (t_arg + 1 + 1) = true
    rw [insertChildNode_isAnc_child]
    have hArgPres2 : tree2.present t_arg = true := by
      rw [retagChild_present, retagChild_present, decide_eq_true rfl, Bool.true_or, Bool.or_true]
    have hArgRefl1 : (insertChildNode tree0 t_parent t_arg (some (.strong callId)) (.reservedFrz false)).isAnc
        t_arg t_arg = true := by
      rw [insertChildNode_isAnc_child, decide_eq_true rfl, Bool.true_or]
    have hArgRefl2 : tree2.isAnc t_arg t_arg = true := by
      show (insertChildNode tree1 t_arg (t_arg + 1) none (initPermOf .mut)).isAnc t_arg t_arg = true
      rw [insertChildNode_isAnc_of_ne _ _ _ _ _ (Ne.symm (Nat.succ_ne_self t_arg))
        (Ne.symm (Nat.succ_ne_self t_arg))]
      exact hArgRefl1
    rw [hArgRefl2, Bool.or_true]
  have hRLoc3 : tree3.locState (t_arg + 1 + 1) b = ⟨.reservedFrz false, true⟩ := by
    show (applyTreeAccess (insertChildNode tree2 t_arg (t_arg + 1 + 1) none (initPermOf .mut))
      (t_arg + 1 + 1) .read r₂ active1 .visitChildrenOfAccessed).locState (t_arg + 1 + 1) b = _
    rw [applyTreeAccess_locState_in _ _ _ _ _ _ _ _
      (by rw [insertChildNode_present, decide_eq_true rfl, Bool.true_or]) hb2,
      nodeAccessRelatedness_anc (by rw [insertChildNode_isAnc_child, decide_eq_true rfl, Bool.true_or]),
      insertChildNode_locState_child]
    rfl
  have hRLocPost : out.tree.locState (t_arg + 1 + 1) b = ⟨.reservedFrz false, true⟩ := by
    show (applyReleaseProtector tree3 t_arg active1).locState (t_arg + 1 + 1) b = _
    cases hAcc : (tree3.locState t_arg b).accessed with
    | false =>
      rw [applyReleaseProtector_locState_unacc tree3 t_arg active1 (t_arg + 1 + 1) b hAcc, hRLoc3]
    | true =>
      rw [applyReleaseProtector_locState_acc tree3 t_arg active1 (t_arg + 1 + 1) b hRPres3 hAcc,
        nodeAccessRelatedness_skip_desc hRNotAncArg3 hArgAncR3, hRLoc3]
  have hRNotAncL : out.tree.isAnc (t_arg + 1 + 1) (t_arg + 1) = false := by
    show tree3.isAnc (t_arg + 1 + 1) (t_arg + 1) = false
    exact retag_not_desc_of_new (tree := tree2) (t_parent := t_arg) (t_child := t_arg + 1 + 1)
      (prot := none) (initPerm := initPermOf .mut) (range := r₂) (active := active1)
      (Ne.symm hne21)
  have hRProt : out.tree.isTagProtected (t_arg + 1 + 1) out.active = false := by
    show (insertChildNode tree2 t_arg (t_arg + 1 + 1) none (initPermOf .mut)).isTagProtected
      (t_arg + 1 + 1) out.active = false
    exact insertChildNode_isTagProtected_child_none _ _ _ _ _
  have hRLocW1 : tree_w1.locState (t_arg + 1 + 1) b = ⟨.disabled, true⟩ := by
    show (applyTreeAccess out.tree (t_arg + 1) .write r₁ out.active
      .visitChildrenOfAccessed).locState (t_arg + 1 + 1) b = _
    rw [applyTreeAccess_locState_in out.tree _ _ _ _ _ _ _ hRPres3 hb1,
      nodeAccessRelatedness_visit_foreign hRNotAncL]
    show (match performTransition .write .foreignAccess
      (out.tree.isTagProtected (t_arg + 1 + 1) out.active)
      (out.tree.locState (t_arg + 1 + 1) b) with | some st' => st' | none => _) = _
    rw [hRProt, hRLocPost]
    rfl
  have hReflR : tree_w1.isAnc (t_arg + 1 + 1) (t_arg + 1 + 1) = true := by
    show (insertChildNode tree2 t_arg (t_arg + 1 + 1) none (initPermOf .mut)).isAnc
      (t_arg + 1 + 1) (t_arg + 1 + 1) = true
    rw [insertChildNode_isAnc_child, decide_eq_true rfl, Bool.true_or]
  have hInB : (ByteRange.mk b (b + 1)).contains b = true :=
    (ByteRange.contains_iff _ _).mpr ⟨Nat.le_refl b, Nat.lt_succ_self b⟩
  refine ⟨rfl, by rw [hRLocW1], ?_, ?_, ?_⟩
  · intro hPerm
    have hAw := hPerm.ancestors_writable (t_arg + 1 + 1) b hReflR hb2
    rw [hRLocW1] at hAw
    rcases hAw with h | h | h <;> cases h
  · intro hNoUB
    have hAt := hNoUB (t_arg + 1 + 1) b hRPres3 hInB
    rw [nodeAccessRelatedness_anc hReflR] at hAt
    change (performTransition .write .localAccess _ (tree_w1.locState (t_arg + 1 + 1) b)).isSome = true at hAt
    rw [hRLocW1] at hAt
    cases hAt
  · intro hNoUB
    have hAt := hNoUB (t_arg + 1 + 1) b hRPres3 hInB
    rw [nodeAccessRelatedness_anc hReflR] at hAt
    change (performTransition .read .localAccess _ (tree_w1.locState (t_arg + 1 + 1) b)).isSome = true at hAt
    rw [hRLocW1] at hAt
    cases hAt

/-- Embedding of `Permission` into the live trusted
`Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowPerm`. -/
def Permission.toLiveTreeBorrowPerm :
    Permission → Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowPerm
  | .reservedFrz c => .reservedFrz c
  | .reservedIM => .reservedIM
  | .active => .unique
  | .frozen => .frozen
  | .disabled => .disabled

/-- Partial inverse from the live `TreeBorrowPerm` (`Cell` is mapped to `none`). -/
def Permission.ofLiveTreeBorrowPerm? :
    Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowPerm → Option Permission
  | .cell => none
  | .reservedFrz c => some (.reservedFrz c)
  | .reservedIM => some .reservedIM
  | .unique => some .active
  | .frozen => some .frozen
  | .disabled => some .disabled

/-- **Bridge to the live `TreeBorrowPerm`**: `Permission` embeds injectively as
the exact non-`Cell` fragment of the live `TreeBorrowPerm`. -/
theorem ofLiveTreeBorrowPerm?_toLiveTreeBorrowPerm (p : Permission) :
    Permission.ofLiveTreeBorrowPerm? p.toLiveTreeBorrowPerm = some p := by
  cases p <;> rfl

theorem toLiveTreeBorrowPerm_ofLiveTreeBorrowPerm?
    {lp : Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowPerm} {p : Permission}
    (h : Permission.ofLiveTreeBorrowPerm? lp = some p) :
    p.toLiveTreeBorrowPerm = lp := by
  cases lp <;> simp [Permission.ofLiveTreeBorrowPerm?] at h <;> subst h <;> rfl

/-- Byte-range projection of a live `Trusted.Rustc.V2026_06_01.MirSemantics.BorrowEntry`. -/
def liveBorrowEntryRange (e : Trusted.Rustc.V2026_06_01.MirSemantics.BorrowEntry) : ByteRange :=
  ⟨e.rangeOffset, e.rangeOffset + e.rangeLen⟩

/-- Protector projection of a live `BorrowEntry`. -/
def liveBorrowEntryProtector (e : Trusted.Rustc.V2026_06_01.MirSemantics.BorrowEntry) :
    Option ProtectorKind :=
  e.protector.map ProtectorKind.strong

theorem liveBorrowEntryRange_contains_iff
    (e : Trusted.Rustc.V2026_06_01.MirSemantics.BorrowEntry) (b : Nat) :
    (liveBorrowEntryRange e).contains b = true ↔
      e.rangeOffset ≤ b ∧ b < e.rangeOffset + e.rangeLen :=
  ByteRange.contains_iff _ _

/-- Live access kind of a prototype access. -/
def AccessKind.toLive : AccessKind → Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowAccessKind
  | .read => .read
  | .write => .write

/-- Live relatedness of a prototype relatedness. -/
def AccessRelatedness.toLive :
    AccessRelatedness → Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowRelatedness
  | .localAccess => .localAccess
  | .foreignAccess => .foreignAccess

/-- Read a live per-node outcome back into the prototype: live UB (`.ub`) and the
fail-closed `.protectedReservedIM` become `none`; a live transition to a
non-`Cell` permission yields that permission with `accessed := acc`. -/
def ofLiveTransition (acc : Bool) :
    Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowTransition → Option LocationState
  | .transition q => (Permission.ofLiveTreeBorrowPerm? q).map (fun p => ⟨p, acc⟩)
  | .ub => none
  | .protectedReservedIM => none

/-- **Semantic bridge to the live trusted Tree Borrows automaton**: on every
accessed location (the live model's invariant: each live `BorrowEntry` stands for an
accessed location), `performTransition` *is* the live `treeBorrowNodeAccess`
(Miri's per-permission transition, the `ProtectedDisabled` protector check, and the
foreign-access skip of `Disabled` nodes), for all access kinds, relatednesses,
protector settings, and permissions. -/
theorem performTransition_accessed_eq_live (kind : AccessKind) (rel : AccessRelatedness)
    (isProt : Bool) (p : Permission) :
    performTransition kind rel isProt ⟨p, true⟩ =
      ofLiveTransition true
        (Trusted.Rustc.V2026_06_01.MirSemantics.treeBorrowNodeAccess kind.toLive rel.toLive
          p.toLiveTreeBorrowPerm isProt) := by
  cases kind <;> cases rel <;> cases isProt <;> rcases p with (_ | _) | _ | _ | _ | _ <;> rfl

/-- **Miri's `accessed` guard** on lazily initialized locations (which the live
model does not represent): on an unaccessed location, a child access is the live
per-permission transition (and marks the location accessed), and a foreign access is
the live per-permission transition *without* the `ProtectedDisabled` check. -/
theorem performTransition_unaccessed_eq_live (kind : AccessKind) (rel : AccessRelatedness)
    (isProt : Bool) (p : Permission) :
    performTransition kind rel isProt ⟨p, false⟩ =
      ofLiveTransition (match rel with | .localAccess => true | .foreignAccess => false)
        (Trusted.Rustc.V2026_06_01.MirSemantics.treeBorrowPermTransition kind.toLive rel.toLive
          p.toLiveTreeBorrowPerm isProt) := by
  cases kind <;> cases rel <;> cases isProt <;> rcases p with (_ | _) | _ | _ | _ | _ <;> rfl

/-- UB detection on accessed locations coincides with the live
`treeBorrowTransitionIsUB`. -/
theorem performTransition_accessed_isSome_eq_live (kind : AccessKind) (rel : AccessRelatedness)
    (isProt : Bool) (p : Permission) :
    (performTransition kind rel isProt ⟨p, true⟩).isSome =
      !Trusted.Rustc.V2026_06_01.MirSemantics.treeBorrowTransitionIsUB
        (Trusted.Rustc.V2026_06_01.MirSemantics.treeBorrowNodeAccess kind.toLive rel.toLive
          p.toLiveTreeBorrowPerm isProt) := by
  cases kind <;> cases rel <;> cases isProt <;> rcases p with (_ | _) | _ | _ | _ | _ <;> rfl

/-- Protector-status bridge: a tag carrying a live entry's protector is protected
under the active set `natListContainsBool l` exactly when the live
`isBorrowProtected l e` holds. -/
theorem isTagProtected_eq_live (tree : BorrowTree) (t : BorTag) (l : List Nat)
    (e : Trusted.Rustc.V2026_06_01.MirSemantics.BorrowEntry)
    (h : tree.protector t = liveBorrowEntryProtector e) :
    tree.isTagProtected t (Trusted.Rustc.V2026_06_01.MirSemantics.natListContainsBool l) =
      Trusted.Rustc.V2026_06_01.MirSemantics.isBorrowProtected l e := by
  unfold BorrowTree.isTagProtected Trusted.Rustc.V2026_06_01.MirSemantics.isBorrowProtected
  rw [h]
  unfold liveBorrowEntryProtector
  cases e.protector <;> rfl

/-- **Per-entry bridge**: for a tag mirroring a live `BorrowEntry` `e` (same
non-`Cell` permission and protector), the prototype's per-location update under the
live active-protector list `l` is the live per-entry outcome
`treeBorrowNodeAccess … e.perm (isBorrowProtected l e)`. -/
theorem performTransition_entry_eq_live (kind : AccessKind) (rel : AccessRelatedness)
    (tree : BorrowTree) (t : BorTag) (l : List Nat) (p : Permission)
    (e : Trusted.Rustc.V2026_06_01.MirSemantics.BorrowEntry)
    (hPerm : e.perm = p.toLiveTreeBorrowPerm) (hProt : tree.protector t = liveBorrowEntryProtector e) :
    performTransition kind rel
        (tree.isTagProtected t (Trusted.Rustc.V2026_06_01.MirSemantics.natListContainsBool l))
        ⟨p, true⟩ =
      ofLiveTransition true
        (Trusted.Rustc.V2026_06_01.MirSemantics.treeBorrowNodeAccess kind.toLive rel.toLive e.perm
          (Trusted.Rustc.V2026_06_01.MirSemantics.isBorrowProtected l e)) := by
  rw [isTagProtected_eq_live tree t l e hProt, hPerm]
  exact performTransition_accessed_eq_live kind rel _ p

/-- Regression (Round A1): a foreign write to a protected, accessed `Disabled`
location is a no-op (Miri `skip_if_known_noop`, live `treeBorrowNodeAccess`), not UB. -/
theorem foreign_write_disabled_protected_noop :
    performTransition .write .foreignAccess true ⟨.disabled, true⟩ = some ⟨.disabled, true⟩ := rfl

/-- Regression (Round A1): a protected `ReservedIM` fails closed under every foreign
access, accessed or not (live `.protectedReservedIM`). -/
theorem protected_reservedIM_foreign_fails_closed (kind : AccessKind) (acc : Bool) :
    performTransition kind .foreignAccess true ⟨.reservedIM, acc⟩ = none := by
  cases kind <;> rfl

/-- Unprotecting a call id preserves `HasUniqueWritePerm`. -/
theorem hasUniqueWritePerm_remove_callId {tree : BorrowTree} {tag : BorTag}
    {range : ByteRange} {activeCaller : ActiveProtectors} {callId : CallId}
    (hCallFresh : activeCaller callId = false)
    (hPerm : HasUniqueWritePerm tree tag range (insertActiveProtector activeCaller callId)) :
    HasUniqueWritePerm tree tag range
      (removeActiveProtector (insertActiveProtector activeCaller callId) callId) := by
  rw [removeActiveProtector_insert hCallFresh]
  refine ⟨hPerm.wf, hPerm.tag_present, hPerm.ancestors_writable, ?_⟩
  intro other b hPres hNotAnc hb
  exact nonAncestorSafe_mono_unprotect _ _ _
    (hPerm.non_ancestors_safe other b hPres hNotAnc hb) isTagProtected_insert_of_caller

/-- Stage-2-only spec execution (modeling the live `restoreCallerProtectors`
return path in `Terminators.lean`, which drops `callId` without stage-1
`applyReleaseProtector`). -/
def TrustedFnSpec.runStage2Only (spec : TrustedFnSpec) (tree₀ : BorrowTree)
    (activeCaller : ActiveProtectors) (t_parent t_arg : BorTag) (callId : CallId) : CallOutcome :=
  let active₁ := insertActiveProtector activeCaller callId
  let tree₁ := retagChild tree₀ t_parent t_arg (some (.strong callId)) (.reservedFrz false)
    spec.argRange active₁
  let fp := applyFootprint t_arg active₁ tree₁ (t_arg + 1) spec.reborrowFootprint
  { tree := fp.1
    active := removeActiveProtector active₁ callId
    rets := fp.2 }

/-- **`split_at_mut_stage2Only_unique_write_perm`**: under the live stage-2-only
return path (`TrustedFnSpec.runStage2Only`, matching `restoreCallerProtectors`),
`split_at_mut` still establishes `HasUniqueWritePerm` on both returned `&mut`
slices and still faults on cross-half writes after activating both halves. -/
theorem split_at_mut_stage2Only_unique_write_perm {tree0 : BorrowTree} {t_parent t_arg : BorTag}
    {base mid len : Nat} {activeCaller : ActiveProtectors} {callId : CallId}
    (hmid : mid ≤ len)
    (hPerm0 : HasUniqueWritePerm tree0 t_parent (wholeRange base len) activeCaller)
    (hFresh : ∀ t, t_arg ≤ t → tree0.present t = false)
    (hFreshCallId : ∀ n, tree0.present n = true → ∀ p, tree0.protector n = some p → p.callId ≠ callId)
    (hCallFresh : activeCaller callId = false) :
    let out := (splitAtMutSpec base mid len).runStage2Only tree0 activeCaller t_parent t_arg callId
    let tree_wl := applyTreeAccess out.tree (t_arg + 1) .write (splitLeft base mid) out.active
      .visitChildrenOfAccessed
    let tree_w := applyTreeAccess tree_wl (t_arg + 1 + 1) .write (splitRight base mid len) out.active
      .visitChildrenOfAccessed
    out.rets = [t_arg + 1, t_arg + 1 + 1] ∧
      HasUniqueWritePerm out.tree (t_arg + 1) (splitLeft base mid) out.active ∧
      HasUniqueWritePerm out.tree (t_arg + 1 + 1) (splitRight base mid len) out.active ∧
      (∀ b, (splitRight base mid len).contains b = true →
        ¬ TreeAccessNoUB tree_w (t_arg + 1) .write ⟨b, b + 1⟩ out.active .visitChildrenOfAccessed) := by
  intro out tree_wl tree_w
  have hFreshArg : tree0.present t_arg = false := hFresh t_arg (Nat.le_refl _)
  have hFreshL : tree0.present (t_arg + 1) = false := hFresh (t_arg + 1) (Nat.le_succ _)
  have hFreshR : tree0.present (t_arg + 1 + 1) = false :=
    hFresh (t_arg + 1 + 1) (Nat.le_succ_of_le (Nat.le_succ t_arg))
  have hne1 : t_arg + 1 ≠ t_arg := Nat.succ_ne_self t_arg
  have hne2 : t_arg + 1 + 1 ≠ t_arg := Nat.ne_of_gt (Nat.lt_succ_of_lt (Nat.lt_succ_self t_arg))
  have hne3 : t_arg + 1 + 1 ≠ t_arg + 1 := Nat.succ_ne_self (t_arg + 1)
  have hDisj := split_disjoint base mid len
  have hDisjSymm := hDisj.symm
  have hPerm0' := hasUniqueWritePerm_insert_fresh_callId hFreshCallId hPerm0
  let active1 := insertActiveProtector activeCaller callId
  let tree1 := retagChild tree0 t_parent t_arg (some (.strong callId)) (.reservedFrz false)
    (wholeRange base len) active1
  have hTree1Perm : HasUniqueWritePerm tree1 t_arg (wholeRange base len) active1 :=
    (retagChild_hasUniqueWritePerm (some (.strong callId)) fnEntry_writable hPerm0'
      (ByteRange.Sub.refl _) hFreshArg).2
  have hFreshL1 : tree1.present (t_arg + 1) = false := by
    rw [retagChild_present, decide_eq_false hne1, Bool.false_or]; exact hFreshL
  let tree2 := retagChild tree1 t_arg (t_arg + 1) none (initPermOf .mut) (splitLeft base mid) active1
  have hTree2ArgPerm : HasUniqueWritePerm tree2 t_arg (wholeRange base len) active1 :=
    retagUnprotectedChild_preserves_parent_hasUniqueWritePerm hTree1Perm hFreshL1
  have hTree2LPerm : HasUniqueWritePerm tree2 (t_arg + 1) (splitLeft base mid) active1 :=
    (retagChild_hasUniqueWritePerm none initPermOf_mut_writable hTree1Perm
      (splitLeft_sub (base := base) hmid) hFreshL1).2
  have hFreshR2 : tree2.present (t_arg + 1 + 1) = false := by
    rw [retagChild_present, decide_eq_false hne3, Bool.false_or, retagChild_present,
      decide_eq_false hne2, Bool.false_or]
    exact hFreshR
  have hTree3RPerm : HasUniqueWritePerm out.tree (t_arg + 1 + 1) (splitRight base mid len) active1 :=
    (retagChild_hasUniqueWritePerm none initPermOf_mut_writable hTree2ArgPerm
      (splitRight_sub base mid len) hFreshR2).2
  have hTree3LPerm : HasUniqueWritePerm out.tree (t_arg + 1) (splitLeft base mid) active1 :=
    disjoint_retagChild_preserves_hasUniqueWritePerm (t_left := t_arg) (t_child := t_arg + 1 + 1)
      none (initPermOf .mut) (by intro h; cases h) hTree2LPerm hDisjSymm hFreshR2
  have hPostL : HasUniqueWritePerm out.tree (t_arg + 1) (splitLeft base mid) out.active :=
    hasUniqueWritePerm_remove_callId hCallFresh hTree3LPerm
  have hPostR : HasUniqueWritePerm out.tree (t_arg + 1 + 1) (splitRight base mid len) out.active :=
    hasUniqueWritePerm_remove_callId hCallFresh hTree3RPerm
  refine ⟨rfl, hPostL, hPostR, ?_⟩
  intro b hb hNoUB
  have hbL : (splitLeft base mid).contains b = false := hDisjSymm b hb
  have hLnotAncR : out.tree.isAnc (t_arg + 1) (t_arg + 1 + 1) = false := by
    show (insertChildNode tree2 t_arg (t_arg + 1 + 1) none (initPermOf .mut)).isAnc
      (t_arg + 1) (t_arg + 1 + 1) = false
    rw [insertChildNode_isAnc_child, decide_eq_false (Ne.symm hne3), Bool.false_or]
    exact retag_not_desc_of_new (Ne.symm hne1)
  have hLprot : ∀ act, out.tree.isTagProtected (t_arg + 1) act = false := by
    intro act
    show (insertChildNode tree2 t_arg (t_arg + 1 + 1) none (initPermOf .mut)).isTagProtected
      (t_arg + 1) act = false
    rw [insertChildNode_isTagProtected_of_ne _ _ _ _ _ (Ne.symm hne3)]
    show (insertChildNode tree1 t_arg (t_arg + 1) none (initPermOf .mut)).isTagProtected
      (t_arg + 1) act = false
    exact insertChildNode_isTagProtected_child_none _ _ _ _ _
  have hLpres : out.tree.present (t_arg + 1) = true := hPostL.tag_present
  have hL2 : tree2.locState (t_arg + 1) b = ⟨.reservedFrz false, false⟩ := by
    show (retagChild tree1 t_arg (t_arg + 1) none (initPermOf .mut)
      (splitLeft base mid) active1).locState (t_arg + 1) b = _
    rw [retagChild_locState_out _ _ _ _ _ _ _ _ _ hbL, insertChildNode_locState_child]
    rfl
  have hLpresI : (insertChildNode tree2 t_arg (t_arg + 1 + 1) none (initPermOf .mut)).present
      (t_arg + 1) = true := hLpres
  have hLnotAncRI : (insertChildNode tree2 t_arg (t_arg + 1 + 1) none (initPermOf .mut)).isAnc
      (t_arg + 1) (t_arg + 1 + 1) = false := hLnotAncR
  have hL3 : out.tree.locState (t_arg + 1) b = ⟨.reservedFrz false, false⟩ := by
    show (applyTreeAccess (insertChildNode tree2 t_arg (t_arg + 1 + 1) none (initPermOf .mut))
      (t_arg + 1 + 1) .read (splitRight base mid len) active1 .visitChildrenOfAccessed).locState
      (t_arg + 1) b = _
    rw [applyTreeAccess_locState_in _ _ _ _ _ _ _ _ hLpresI hb,
      nodeAccessRelatedness_visit_foreign hLnotAncRI]
    show (match performTransition .read .foreignAccess (out.tree.isTagProtected (t_arg + 1) active1)
      ((insertChildNode tree2 t_arg (t_arg + 1 + 1) none (initPermOf .mut)).locState (t_arg + 1) b)
      with | some st' => st' | none => _) = _
    rw [hLprot active1, insertChildNode_locState_of_ne _ _ _ _ _ (Ne.symm hne3), hL2]
    rfl
  have hLwl : tree_wl.locState (t_arg + 1) b = ⟨.reservedFrz false, false⟩ := by
    show (applyTreeAccess out.tree (t_arg + 1) .write (splitLeft base mid) out.active
      .visitChildrenOfAccessed).locState (t_arg + 1) b = _
    rw [applyTreeAccess_locState_out _ _ _ _ _ _ _ _ hbL, hL3]
  have hLpresWl : tree_wl.present (t_arg + 1) = true := hLpres
  have hLnotAncRWl : tree_wl.isAnc (t_arg + 1) (t_arg + 1 + 1) = false := hLnotAncR
  have hLw : tree_w.locState (t_arg + 1) b = ⟨.disabled, false⟩ := by
    show (applyTreeAccess tree_wl (t_arg + 1 + 1) .write (splitRight base mid len) out.active
      .visitChildrenOfAccessed).locState (t_arg + 1) b = _
    rw [applyTreeAccess_locState_in _ _ _ _ _ _ _ _ hLpresWl hb,
      nodeAccessRelatedness_visit_foreign hLnotAncRWl]
    show (match performTransition .write .foreignAccess
      (out.tree.isTagProtected (t_arg + 1) out.active)
      (tree_wl.locState (t_arg + 1) b) with | some st' => st' | none => _) = _
    rw [hLprot out.active, hLwl]
    rfl
  have hReflL : tree_w.isAnc (t_arg + 1) (t_arg + 1) = true :=
    hPostL.wf.isAnc_refl (t_arg + 1) hLpres
  have hLpresW : tree_w.present (t_arg + 1) = true := hLpres
  have hAt := hNoUB (t_arg + 1) b hLpresW
    ((ByteRange.contains_iff _ _).mpr ⟨Nat.le_refl b, Nat.lt_succ_self b⟩)
  rw [nodeAccessRelatedness_anc hReflL] at hAt
  change (performTransition .write .localAccess _ (tree_w.locState (t_arg + 1) b)).isSome = true at hAt
  rw [hLw] at hAt
  cases hAt

/-- **Exact separation between Miri's stage-1 protector release and stage-2-only
release**: on a concrete UB-free two-argument call `foo(x, y)` receiving two
two-phase `&mut` borrows under `rootTree 0`, releasing `t_arg_x`'s protector in
stage 1 while `callId` is still active marks `t_arg_y` conflicted
(`⟨.reservedFrz true, true⟩`), whereas stage-2-only release leaves `t_arg_y`
unconflicted (`⟨.reservedFrz false, true⟩`). -/
theorem stage1_vs_stage2Only_two_arg_release_differs (r : ByteRange) (b : Nat)
    (hb : r.contains b = true) :
    let active1 := insertActiveProtector (fun _ => false) 0
    let tree1 := retagChild (rootTree 0) 0 1 (some (.strong 0)) (.reservedFrz false) r active1
    let tree2 := retagChild tree1 0 2 (some (.strong 0)) (.reservedFrz false) r active1
    TreeAccessNoUB (insertChildNode (rootTree 0) 0 1 (some (.strong 0)) (.reservedFrz false))
        1 .read r active1 .visitChildrenOfAccessed ∧
      TreeAccessNoUB (insertChildNode tree1 0 2 (some (.strong 0)) (.reservedFrz false))
        2 .read r active1 .visitChildrenOfAccessed ∧
      releaseProtectorNoUB tree2 1 active1 ∧
      (applyReleaseProtector tree2 1 active1).locState 2 b = ⟨.reservedFrz true, true⟩ ∧
      tree2.locState 2 b = ⟨.reservedFrz false, true⟩ := by
  intro active1 tree1 tree2
  have hPerm0 := rootTree_hasUniqueWritePerm 0 r active1
  obtain ⟨hNoUB1, _⟩ := retagChild_hasUniqueWritePerm (t_child := 1) (some (.strong 0)) fnEntry_writable
    hPerm0 (ByteRange.Sub.refl r) rfl
  have hNoUB2 : TreeAccessNoUB (insertChildNode tree1 0 2 (some (.strong 0)) (.reservedFrz false))
      2 .read r active1 .visitChildrenOfAccessed := by
    intro n b' hPres hb'
    let tI := insertChildNode tree1 0 2 (some (.strong 0)) (.reservedFrz false)
    by_cases hn2 : n = 2
    · subst hn2
      have hAnc : tI.isAnc 2 2 = true := rfl
      rw [nodeAccessRelatedness_anc hAnc]
      rfl
    · by_cases hn0 : n = 0
      · subst hn0
        have hAnc : tI.isAnc 0 2 = true := rfl
        rw [nodeAccessRelatedness_anc hAnc]
        have hLoc : tI.locState 0 b' = ⟨.active, true⟩ := by
          show tree1.locState 0 b' = _
          rw [show tree1 = applyTreeAccess (insertChildNode (rootTree 0) 0 1 (some (.strong 0))
            (.reservedFrz false)) 1 .read r active1 .visitChildrenOfAccessed from rfl,
            applyTreeAccess_locState_in _ _ _ _ _ _ 0 b' rfl hb',
            nodeAccessRelatedness_anc rfl]
          rfl
        show (performTransition .read .localAccess _ (tI.locState 0 b')).isSome = true
        rw [hLoc]
        rfl
      · have hn1 : n = 1 := by
          simp only [insertChildNode, tree1, retagChild, applyTreeAccess, rootTree,
            Bool.or_eq_true, decide_eq_true_eq] at hPres
          rcases hPres with rfl | rfl | rfl
          · exact absurd rfl hn2
          · rfl
          · exact absurd rfl hn0
        subst hn1
        have hNotAnc : tI.isAnc 1 2 = false := rfl
        rw [nodeAccessRelatedness_visit_foreign hNotAnc]
        have hLoc : tI.locState 1 b' = ⟨.reservedFrz false, true⟩ := by
          show tree1.locState 1 b' = _
          rw [show tree1 = applyTreeAccess (insertChildNode (rootTree 0) 0 1 (some (.strong 0))
            (.reservedFrz false)) 1 .read r active1 .visitChildrenOfAccessed from rfl,
            applyTreeAccess_locState_in _ _ _ _ _ _ 1 b' rfl hb',
            nodeAccessRelatedness_anc rfl]
          rfl
        show (performTransition .read .foreignAccess (tI.isTagProtected 1 active1)
          (tI.locState 1 b')).isSome = true
        rw [hLoc]
        rfl
  have hAcc1 : ∀ b', (tree2.locState 1 b').accessed = true → r.contains b' = true := by
    intro b' hAcc
    cases hb' : r.contains b' with
    | true => rfl
    | false =>
      have h2 : tree2.locState 1 b' = tree1.locState 1 b' := by
        show (retagChild tree1 0 2 (some (.strong 0)) (.reservedFrz false) r active1).locState 1 b' = _
        rw [retagChild_locState_out _ _ _ _ _ _ _ _ _ hb',
          insertChildNode_locState_of_ne _ _ _ _ _ (by decide)]
      have h1 : (tree1.locState 1 b').accessed = r.contains b' :=
        retagChild_child_accessed (tree := rootTree 0) (t_parent := 0) (t_child := 1)
          (prot := some (.strong 0)) (initPerm := .reservedFrz false) (range := r)
          (active := active1) (by decide) b'
      rw [h2, h1, hb'] at hAcc
      cases hAcc
  have hLoc1In : ∀ b', r.contains b' = true → tree2.locState 1 b' = ⟨.reservedFrz true, true⟩ := by
    intro b' hb'
    have h1 : tree1.locState 1 b' = ⟨.reservedFrz false, true⟩ := by
      rw [show tree1 = applyTreeAccess (insertChildNode (rootTree 0) 0 1 (some (.strong 0))
        (.reservedFrz false)) 1 .read r active1 .visitChildrenOfAccessed from rfl,
        applyTreeAccess_locState_in _ _ _ _ _ _ 1 b' rfl hb',
        nodeAccessRelatedness_anc rfl]
      rfl
    rw [show tree2 = applyTreeAccess (insertChildNode tree1 0 2 (some (.strong 0))
      (.reservedFrz false)) 2 .read r active1 .visitChildrenOfAccessed from rfl,
      applyTreeAccess_locState_in _ _ _ _ _ _ 1 b' rfl hb',
      nodeAccessRelatedness_visit_foreign rfl]
    show (match performTransition .read .foreignAccess true
      ((insertChildNode tree1 0 2 (some (.strong 0)) (.reservedFrz false)).locState 1 b')
      with | some st' => st' | none => _) = _
    rw [insertChildNode_locState_of_ne _ _ _ _ _ (by decide), h1]
    rfl
  have hLoc2In : ∀ b', r.contains b' = true → tree2.locState 2 b' = ⟨.reservedFrz false, true⟩ := by
    intro b' hb'
    rw [show tree2 = applyTreeAccess (insertChildNode tree1 0 2 (some (.strong 0))
      (.reservedFrz false)) 2 .read r active1 .visitChildrenOfAccessed from rfl,
      applyTreeAccess_locState_in _ _ _ _ _ _ 2 b' rfl hb',
      nodeAccessRelatedness_anc rfl]
    rfl
  have hLoc0In : ∀ b', r.contains b' = true → tree2.locState 0 b' = ⟨.active, true⟩ := by
    intro b' hb'
    have h1 : tree1.locState 0 b' = ⟨.active, true⟩ := by
      rw [show tree1 = applyTreeAccess (insertChildNode (rootTree 0) 0 1 (some (.strong 0))
        (.reservedFrz false)) 1 .read r active1 .visitChildrenOfAccessed from rfl,
        applyTreeAccess_locState_in _ _ _ _ _ _ 0 b' rfl hb',
        nodeAccessRelatedness_anc rfl]
      rfl
    rw [show tree2 = applyTreeAccess (insertChildNode tree1 0 2 (some (.strong 0))
      (.reservedFrz false)) 2 .read r active1 .visitChildrenOfAccessed from rfl,
      applyTreeAccess_locState_in _ _ _ _ _ _ 0 b' rfl hb',
      nodeAccessRelatedness_anc rfl]
    show (match performTransition .read .localAccess _
      ((insertChildNode tree1 0 2 (some (.strong 0)) (.reservedFrz false)).locState 0 b')
      with | some st' => st' | none => _) = _
    rw [insertChildNode_locState_of_ne _ _ _ _ _ (by decide), h1]
    rfl
  have hRelNoUB : releaseProtectorNoUB tree2 1 active1 := by
    intro n b' hPres hAcc
    have hb' := hAcc1 b' hAcc
    have h1 := hLoc1In b' hb'
    simp only [tree2, retagChild, applyTreeAccess, insertChildNode, tree1, rootTree,
      Bool.or_eq_true, decide_eq_true_eq] at hPres
    rcases hPres with rfl | rfl | rfl
    · rw [nodeAccessRelatedness_skip_foreign rfl rfl]
      show (performTransition (tree2.locState 1 b').perm.associatedAccess .foreignAccess
        (tree2.isTagProtected 2 active1) (tree2.locState 2 b')).isSome = true
      rw [h1, hLoc2In b' hb']
      rfl
    · rw [nodeAccessRelatedness_anc rfl]
      show (performTransition (tree2.locState 1 b').perm.associatedAccess .localAccess
        (tree2.isTagProtected 1 active1) (tree2.locState 1 b')).isSome = true
      rw [h1]
      rfl
    · rw [nodeAccessRelatedness_anc rfl]
      show (performTransition (tree2.locState 1 b').perm.associatedAccess .localAccess
        (tree2.isTagProtected 0 active1) (tree2.locState 0 b')).isSome = true
      rw [h1, hLoc0In b' hb']
      rfl
  refine ⟨hNoUB1, hNoUB2, hRelNoUB, ?_, hLoc2In b hb⟩
  have hAccB : (tree2.locState 1 b).accessed = true := by rw [hLoc1In b hb]
  rw [applyReleaseProtector_locState_acc tree2 1 active1 2 b rfl hAccB,
    nodeAccessRelatedness_skip_foreign rfl rfl]
  show (match performTransition (tree2.locState 1 b).perm.associatedAccess .foreignAccess
    (tree2.isTagProtected 2 active1) (tree2.locState 2 b) with | some st' => st' | none => _) = _
  rw [hLoc1In b hb, hLoc2In b hb]
  have hProt2 : tree2.isTagProtected 2 active1 = true := rfl
  rw [hProt2]
  rfl

/-! #### Conflict latches of unprotected tags are semantically inert (Round A2)

The state difference exhibited by `stage1_vs_stage2Only_two_arg_release_differs` is a
`ReservedFrz` conflict latch.  `LatchEquiv` relates trees that differ at most in the
latches of tags that are unprotected; it is preserved by every tree operation of the
model (accesses, retags, stage-1 release, call-id changes) and never changes a UB
verdict, so such a difference is unobservable. -/

/-- Erase the `ReservedFrz` conflict latch. -/
def LocationState.eraseLatch (st : LocationState) : LocationState :=
  match st.perm with
  | .reservedFrz _ => ⟨.reservedFrz false, st.accessed⟩
  | _ => st

theorem LocationState.eraseLatch_accessed (st : LocationState) :
    st.eraseLatch.accessed = st.accessed := by
  rcases st with ⟨(_ | _) | _ | _ | _ | _, _⟩ <;> rfl

theorem LocationState.eraseLatch_associatedAccess (st : LocationState) :
    st.eraseLatch.perm.associatedAccess = st.perm.associatedAccess := by
  rcases st with ⟨(_ | _) | _ | _ | _ | _, _⟩ <;> rfl

theorem LocationState.ne_active_of_eraseLatch_eq {st st' : LocationState}
    (h : st.eraseLatch = st'.eraseLatch) (h' : st'.perm ≠ .active) : st.perm ≠ .active := by
  rcases st with ⟨(_ | _) | _ | _ | _ | _, _⟩ <;> rcases st' with ⟨(_ | _) | _ | _ | _ | _, _⟩ <;>
    first
    | exact fun h₀ => Permission.noConfusion h₀
    | exact absurd rfl h'
    | exact absurd (congrArg LocationState.perm h) (fun h₀ => Permission.noConfusion h₀)

/-- **Per-location latch inertness**: on an unprotected location the conflict latch
changes neither the UB verdict nor the successor state (up to the latch). -/
theorem performTransition_unprotected_eraseLatch (kind : AccessKind) (rel : AccessRelatedness)
    (st : LocationState) :
    (performTransition kind rel false st).map LocationState.eraseLatch =
      (performTransition kind rel false st.eraseLatch).map LocationState.eraseLatch := by
  rcases st with ⟨(_ | _) | _ | _ | _ | _, _⟩ <;> cases kind <;> cases rel <;> rfl

theorem performTransition_unprotected_isSome_eraseLatch (kind : AccessKind)
    (rel : AccessRelatedness) (st : LocationState) :
    (performTransition kind rel false st).isSome =
      (performTransition kind rel false st.eraseLatch).isSome := by
  rcases st with ⟨(_ | _) | _ | _ | _ | _, _⟩ <;> cases kind <;> cases rel <;> rfl

theorem eraseLatch_update_unprotected (kind : AccessKind) (rel : AccessRelatedness)
    {st₁ st₂ : LocationState} (h : st₁.eraseLatch = st₂.eraseLatch) :
    (match performTransition kind rel false st₁ with
      | some st' => st' | none => st₁).eraseLatch =
    (match performTransition kind rel false st₂ with
      | some st' => st' | none => st₂).eraseLatch := by
  have hmap : (performTransition kind rel false st₁).map LocationState.eraseLatch =
      (performTransition kind rel false st₂).map LocationState.eraseLatch := by
    rw [performTransition_unprotected_eraseLatch kind rel st₁, h,
      ← performTransition_unprotected_eraseLatch kind rel st₂]
  cases h₁ : performTransition kind rel false st₁ with
  | none =>
    cases h₂ : performTransition kind rel false st₂ with
    | none => exact h
    | some b => rw [h₁, h₂] at hmap; cases hmap
  | some a =>
    cases h₂ : performTransition kind rel false st₂ with
    | none => rw [h₁, h₂] at hmap; cases hmap
    | some b => rw [h₁, h₂] at hmap; exact Option.some.inj hmap

theorem nodeAccessRelatedness_congr {t₁ t₂ : BorrowTree} (h : t₁.isAnc = t₂.isAnc)
    (start : BorTag) (mode : ChildrenVisitMode) (n : BorTag) :
    nodeAccessRelatedness t₁ start mode n = nodeAccessRelatedness t₂ start mode n := by
  unfold nodeAccessRelatedness
  rw [h]

theorem isTagProtected_congr {t₁ t₂ : BorrowTree} (h : t₁.protector = t₂.protector)
    (n : BorTag) (active : ActiveProtectors) :
    t₁.isTagProtected n active = t₂.isTagProtected n active := by
  unfold BorrowTree.isTagProtected
  rw [h]

theorem applyTreeAccess_locState_absent (tree : BorrowTree) (start : BorTag) (kind : AccessKind)
    (range : ByteRange) (active : ActiveProtectors) (mode : ChildrenVisitMode) (n : BorTag)
    (b : Nat) (h : tree.present n = false) :
    (applyTreeAccess tree start kind range active mode).locState n b = tree.locState n b := by
  simp only [applyTreeAccess, h, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

theorem applyReleaseProtector_locState_absent (tree : BorrowTree) (t_rel : BorTag)
    (active : ActiveProtectors) (n : BorTag) (b : Nat) (h : tree.present n = false) :
    (applyReleaseProtector tree t_rel active).locState n b = tree.locState n b := by
  simp only [applyReleaseProtector, h, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- Trees that agree except possibly on the conflict latches of tags that are
unprotected under `active`. -/
structure LatchEquiv (t₁ t₂ : BorrowTree) (active : ActiveProtectors) : Prop where
  present_eq : t₁.present = t₂.present
  isAnc_eq : t₁.isAnc = t₂.isAnc
  protector_eq : t₁.protector = t₂.protector
  erase_eq : ∀ n b, (t₁.locState n b).eraseLatch = (t₂.locState n b).eraseLatch
  protected_eq : ∀ n b, t₁.isTagProtected n active = true → t₁.locState n b = t₂.locState n b

theorem LatchEquiv.refl (t : BorrowTree) (active : ActiveProtectors) : LatchEquiv t t active :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- Fewer protected tags (e.g. `GlobalState.endCall`, or a fresh call id that no
existing tag uses) preserve the equivalence. -/
theorem LatchEquiv.of_active {t₁ t₂ : BorrowTree} {active active' : ActiveProtectors}
    (h : LatchEquiv t₁ t₂ active)
    (hact : ∀ n, t₁.isTagProtected n active' = true → t₁.isTagProtected n active = true) :
    LatchEquiv t₁ t₂ active' :=
  ⟨h.present_eq, h.isAnc_eq, h.protector_eq, h.erase_eq,
    fun n b hn => h.protected_eq n b (hact n hn)⟩

theorem LatchEquiv.transition_isSome {t₁ t₂ : BorrowTree} {active : ActiveProtectors}
    (h : LatchEquiv t₁ t₂ active) (kind : AccessKind) (rel : AccessRelatedness) (n : BorTag)
    (b : Nat) :
    (performTransition kind rel (t₁.isTagProtected n active) (t₁.locState n b)).isSome =
      (performTransition kind rel (t₂.isTagProtected n active) (t₂.locState n b)).isSome := by
  rw [← isTagProtected_congr h.protector_eq]
  cases hp : t₁.isTagProtected n active with
  | true => rw [h.protected_eq n b hp]
  | false =>
    rw [performTransition_unprotected_isSome_eraseLatch kind rel (t₁.locState n b), h.erase_eq n b,
      ← performTransition_unprotected_isSome_eraseLatch kind rel (t₂.locState n b)]

/-- **Every access has the same UB verdict** on latch-equivalent trees. -/
theorem LatchEquiv.noUB_iff {t₁ t₂ : BorrowTree} {active : ActiveProtectors}
    (h : LatchEquiv t₁ t₂ active) (start : BorTag) (kind : AccessKind) (range : ByteRange)
    (mode : ChildrenVisitMode) :
    TreeAccessNoUB t₁ start kind range active mode ↔
      TreeAccessNoUB t₂ start kind range active mode := by
  constructor
  · intro H n b hPres hb
    have H₁ := H n b (by rw [h.present_eq]; exact hPres) hb
    rw [nodeAccessRelatedness_congr h.isAnc_eq] at H₁
    revert H₁
    cases nodeAccessRelatedness t₂ start mode n with
    | none => exact fun _ => trivial
    | some rel =>
      intro H₁
      show (performTransition kind rel (t₂.isTagProtected n active) (t₂.locState n b)).isSome = true
      rw [← h.transition_isSome kind rel n b]
      exact H₁
  · intro H n b hPres hb
    have H₂ := H n b (by rw [← h.present_eq]; exact hPres) hb
    rw [← nodeAccessRelatedness_congr h.isAnc_eq] at H₂
    revert H₂
    cases nodeAccessRelatedness t₁ start mode n with
    | none => exact fun _ => trivial
    | some rel =>
      intro H₂
      show (performTransition kind rel (t₁.isTagProtected n active) (t₁.locState n b)).isSome = true
      rw [h.transition_isSome kind rel n b]
      exact H₂

/-- Accesses preserve latch equivalence. -/
theorem LatchEquiv.access {t₁ t₂ : BorrowTree} {active : ActiveProtectors}
    (h : LatchEquiv t₁ t₂ active) (start : BorTag) (kind : AccessKind) (range : ByteRange)
    (mode : ChildrenVisitMode) :
    LatchEquiv (applyTreeAccess t₁ start kind range active mode)
      (applyTreeAccess t₂ start kind range active mode) active := by
  have hstep : ∀ n b, t₁.present n = true → range.contains b = true →
      (applyTreeAccess t₂ start kind range active mode).locState n b =
        match nodeAccessRelatedness t₁ start mode n with
        | some rel =>
          match performTransition kind rel (t₁.isTagProtected n active) (t₂.locState n b) with
          | some st' => st'
          | none => t₂.locState n b
        | none => t₂.locState n b := by
    intro n b hP hb
    rw [applyTreeAccess_locState_in _ _ _ _ _ _ _ _ (by rw [← h.present_eq]; exact hP) hb,
      ← nodeAccessRelatedness_congr h.isAnc_eq, ← isTagProtected_congr h.protector_eq]
  refine ⟨h.present_eq, h.isAnc_eq, h.protector_eq, fun n b => ?_, fun n b hn => ?_⟩
  · cases hP : t₁.present n with
    | false =>
      rw [applyTreeAccess_locState_absent _ _ _ _ _ _ _ _ hP,
        applyTreeAccess_locState_absent _ _ _ _ _ _ _ _ (by rw [← h.present_eq]; exact hP)]
      exact h.erase_eq n b
    | true =>
      cases hb : range.contains b with
      | false =>
        rw [applyTreeAccess_locState_out _ _ _ _ _ _ _ _ hb,
          applyTreeAccess_locState_out _ _ _ _ _ _ _ _ hb]
        exact h.erase_eq n b
      | true =>
        rw [applyTreeAccess_locState_in _ _ _ _ _ _ _ _ hP hb, hstep n b hP hb]
        cases nodeAccessRelatedness t₁ start mode n with
        | none => exact h.erase_eq n b
        | some rel =>
          cases hx : t₁.isTagProtected n active with
          | true => rw [h.protected_eq n b hx]
          | false => exact eraseLatch_update_unprotected kind rel (h.erase_eq n b)
  · have hn' : t₁.isTagProtected n active = true := hn
    have hs := h.protected_eq n b hn'
    cases hP : t₁.present n with
    | false =>
      rw [applyTreeAccess_locState_absent _ _ _ _ _ _ _ _ hP,
        applyTreeAccess_locState_absent _ _ _ _ _ _ _ _ (by rw [← h.present_eq]; exact hP), hs]
    | true =>
      cases hb : range.contains b with
      | false =>
        rw [applyTreeAccess_locState_out _ _ _ _ _ _ _ _ hb,
          applyTreeAccess_locState_out _ _ _ _ _ _ _ _ hb, hs]
      | true => rw [applyTreeAccess_locState_in _ _ _ _ _ _ _ _ hP hb, hstep n b hP hb, hs]

/-- Inserting the same fresh node preserves latch equivalence. -/
theorem LatchEquiv.insert {t₁ t₂ : BorrowTree} {active : ActiveProtectors}
    (h : LatchEquiv t₁ t₂ active) (t_parent t_child : BorTag) (prot : Option ProtectorKind)
    (initPerm : Permission) :
    LatchEquiv (insertChildNode t₁ t_parent t_child prot initPerm)
      (insertChildNode t₂ t_parent t_child prot initPerm) active := by
  refine ⟨?_, ?_, ?_, fun n b => ?_, fun n b hn => ?_⟩
  · show (fun t => decide (t = t_child) || t₁.present t) = (fun t => decide (t = t_child) || t₂.present t)
    rw [h.present_eq]
  · show (fun a d => if d = t_child then decide (a = t_child) || t₁.isAnc a t_parent
        else if a = t_child then false else t₁.isAnc a d) =
      (fun a d => if d = t_child then decide (a = t_child) || t₂.isAnc a t_parent
        else if a = t_child then false else t₂.isAnc a d)
    rw [h.isAnc_eq]
  · show (fun t => if t = t_child then prot else t₁.protector t) =
      (fun t => if t = t_child then prot else t₂.protector t)
    rw [h.protector_eq]
  · by_cases hc : n = t_child
    · rw [hc, insertChildNode_locState_child, insertChildNode_locState_child]
    · rw [insertChildNode_locState_of_ne _ _ _ _ _ hc, insertChildNode_locState_of_ne _ _ _ _ _ hc]
      exact h.erase_eq n b
  · by_cases hc : n = t_child
    · rw [hc, insertChildNode_locState_child, insertChildNode_locState_child]
    · rw [insertChildNode_locState_of_ne _ _ _ _ _ hc, insertChildNode_locState_of_ne _ _ _ _ _ hc]
      rw [insertChildNode_isTagProtected_of_ne _ _ _ _ _ hc] at hn
      exact h.protected_eq n b hn

/-- Retags preserve latch equivalence. -/
theorem LatchEquiv.retag {t₁ t₂ : BorrowTree} {active : ActiveProtectors}
    (h : LatchEquiv t₁ t₂ active) (t_parent t_child : BorTag) (prot : Option ProtectorKind)
    (initPerm : Permission) (range : ByteRange) :
    LatchEquiv (retagChild t₁ t_parent t_child prot initPerm range active)
      (retagChild t₂ t_parent t_child prot initPerm range active) active :=
  (h.insert t_parent t_child prot initPerm).access t_child .read range
    .visitChildrenOfAccessed

theorem LatchEquiv.released_eq {t₁ t₂ : BorrowTree} {active : ActiveProtectors}
    (h : LatchEquiv t₁ t₂ active) (t_rel : BorTag) (b : Nat) :
    (t₂.locState t_rel b).accessed = (t₁.locState t_rel b).accessed ∧
      (t₂.locState t_rel b).perm.associatedAccess = (t₁.locState t_rel b).perm.associatedAccess := by
  refine ⟨?_, ?_⟩
  · rw [← LocationState.eraseLatch_accessed (t₂.locState t_rel b), ← h.erase_eq t_rel b,
      LocationState.eraseLatch_accessed]
  · rw [← LocationState.eraseLatch_associatedAccess (t₂.locState t_rel b), ← h.erase_eq t_rel b,
      LocationState.eraseLatch_associatedAccess]

/-- Stage-1 release preserves latch equivalence. -/
theorem LatchEquiv.release {t₁ t₂ : BorrowTree} {active : ActiveProtectors}
    (h : LatchEquiv t₁ t₂ active) (t_rel : BorTag) :
    LatchEquiv (applyReleaseProtector t₁ t_rel active)
      (applyReleaseProtector t₂ t_rel active) active := by
  have hstep : ∀ n b, t₁.present n = true → (t₁.locState t_rel b).accessed = true →
      (applyReleaseProtector t₂ t_rel active).locState n b =
        match nodeAccessRelatedness t₁ t_rel .skipChildrenOfAccessed n with
        | some rel =>
          match performTransition (t₁.locState t_rel b).perm.associatedAccess rel
              (t₁.isTagProtected n active) (t₂.locState n b) with
          | some st' => st'
          | none => t₂.locState n b
        | none => t₂.locState n b := by
    intro n b hP hA
    obtain ⟨hacc, hkind⟩ := h.released_eq t_rel b
    rw [applyReleaseProtector_locState_acc _ _ _ _ _ (by rw [← h.present_eq]; exact hP)
      (by rw [hacc]; exact hA), ← nodeAccessRelatedness_congr h.isAnc_eq,
      ← isTagProtected_congr h.protector_eq, hkind]
  have hunacc : ∀ n b, (t₁.locState t_rel b).accessed = false →
      (applyReleaseProtector t₂ t_rel active).locState n b = t₂.locState n b := by
    intro n b hA
    exact applyReleaseProtector_locState_unacc _ _ _ _ _
      (by rw [(h.released_eq t_rel b).1]; exact hA)
  refine ⟨h.present_eq, h.isAnc_eq, h.protector_eq, fun n b => ?_, fun n b hn => ?_⟩
  · cases hP : t₁.present n with
    | false =>
      rw [applyReleaseProtector_locState_absent _ _ _ _ _ hP,
        applyReleaseProtector_locState_absent _ _ _ _ _ (by rw [← h.present_eq]; exact hP)]
      exact h.erase_eq n b
    | true =>
      cases hA : (t₁.locState t_rel b).accessed with
      | false =>
        rw [applyReleaseProtector_locState_unacc _ _ _ _ _ hA, hunacc n b hA]
        exact h.erase_eq n b
      | true =>
        rw [applyReleaseProtector_locState_acc _ _ _ _ _ hP hA, hstep n b hP hA]
        cases nodeAccessRelatedness t₁ t_rel .skipChildrenOfAccessed n with
        | none => exact h.erase_eq n b
        | some rel =>
          cases hx : t₁.isTagProtected n active with
          | true => rw [h.protected_eq n b hx]
          | false => exact eraseLatch_update_unprotected _ rel (h.erase_eq n b)
  · have hn' : t₁.isTagProtected n active = true := hn
    have hs := h.protected_eq n b hn'
    cases hP : t₁.present n with
    | false =>
      rw [applyReleaseProtector_locState_absent _ _ _ _ _ hP,
        applyReleaseProtector_locState_absent _ _ _ _ _ (by rw [← h.present_eq]; exact hP), hs]
    | true =>
      cases hA : (t₁.locState t_rel b).accessed with
      | false => rw [applyReleaseProtector_locState_unacc _ _ _ _ _ hA, hunacc n b hA, hs]
      | true => rw [applyReleaseProtector_locState_acc _ _ _ _ _ hP hA, hstep n b hP hA, hs]

/-- Stage-1 release has the same UB verdict on latch-equivalent trees. -/
theorem LatchEquiv.releaseNoUB_iff {t₁ t₂ : BorrowTree} {active : ActiveProtectors}
    (h : LatchEquiv t₁ t₂ active) (t_rel : BorTag) :
    releaseProtectorNoUB t₁ t_rel active ↔ releaseProtectorNoUB t₂ t_rel active := by
  constructor
  · intro H n b hPres hA
    obtain ⟨hacc, hkind⟩ := h.released_eq t_rel b
    have H₁ := H n b (by rw [h.present_eq]; exact hPres) (by rw [← hacc]; exact hA)
    rw [nodeAccessRelatedness_congr h.isAnc_eq] at H₁
    revert H₁
    cases nodeAccessRelatedness t₂ t_rel .skipChildrenOfAccessed n with
    | none => exact fun _ => trivial
    | some rel =>
      intro H₁
      show (performTransition (t₂.locState t_rel b).perm.associatedAccess rel
        (t₂.isTagProtected n active) (t₂.locState n b)).isSome = true
      rw [hkind, ← h.transition_isSome _ rel n b]
      exact H₁
  · intro H n b hPres hA
    obtain ⟨hacc, hkind⟩ := h.released_eq t_rel b
    have H₂ := H n b (by rw [← h.present_eq]; exact hPres) (by rw [hacc]; exact hA)
    rw [← nodeAccessRelatedness_congr h.isAnc_eq] at H₂
    revert H₂
    cases nodeAccessRelatedness t₁ t_rel .skipChildrenOfAccessed n with
    | none => exact fun _ => trivial
    | some rel =>
      intro H₂
      show (performTransition (t₁.locState t_rel b).perm.associatedAccess rel
        (t₁.isTagProtected n active) (t₁.locState n b)).isSome = true
      rw [h.transition_isSome _ rel n b, ← hkind]
      exact H₂

theorem nodeAccessRelatedness_isAnc_of_local {tree : BorrowTree} {start n : BorTag}
    {mode : ChildrenVisitMode} (h : nodeAccessRelatedness tree start mode n = some .localAccess) :
    tree.isAnc n start = true := by
  cases hA : tree.isAnc n start with
  | true => rfl
  | false =>
    unfold nodeAccessRelatedness at h
    rw [ite_eq_right (by rw [hA]; exact Bool.false_ne_true)] at h
    cases mode with
    | visitChildrenOfAccessed => cases h
    | skipChildrenOfAccessed =>
      by_cases hd : tree.isAnc start n = true
      · rw [ite_eq_left hd] at h
        cases h
      · rw [ite_eq_right hd] at h
        cases h

theorem nodeAccessRelatedness_not_isAnc_of_foreign {tree : BorrowTree} {start n : BorTag}
    {mode : ChildrenVisitMode} (h : nodeAccessRelatedness tree start mode n = some .foreignAccess) :
    tree.isAnc n start = false := by
  cases hA : tree.isAnc n start with
  | false => rfl
  | true =>
    rw [nodeAccessRelatedness_anc hA] at h
    cases h

theorem Permission.associatedAccess_of_ne_active {p : Permission} (h : p ≠ .active) :
    p.associatedAccess = .read := by
  cases p <;> first | rfl | exact absurd rfl h

theorem eraseLatch_update_localRead (prot : Bool) {st : LocationState} (h : st.accessed = true) :
    (match performTransition .read .localAccess prot st with
      | some st' => st' | none => st).eraseLatch = st.eraseLatch := by
  rcases st with ⟨(_ | _) | _ | _ | _ | _, _ | _⟩ <;> first | (cases prot <;> rfl) | cases h

theorem eraseLatch_update_foreignRead (prot : Bool) {st : LocationState} (h : st.perm ≠ .active) :
    (match performTransition .read .foreignAccess prot st with
      | some st' => st' | none => st).eraseLatch = st.eraseLatch := by
  rcases st with ⟨(_ | _) | _ | _ | _ | _, _ | _⟩ <;> first | (cases prot <;> rfl) | exact absurd rfl h

theorem performTransition_update_accessed_mono (kind : AccessKind) (rel : AccessRelatedness)
    (prot : Bool) {st : LocationState} (h : st.accessed = true) :
    (match performTransition kind rel prot st with | some st' => st' | none => st).accessed = true := by
  rcases st with ⟨(_ | _) | _ | _ | _ | _, _ | _⟩ <;> cases kind <;> cases rel <;> cases prot <;>
    first | rfl | cases h

theorem performTransition_update_read_ne_active (rel : AccessRelatedness) (prot : Bool)
    {st : LocationState} (h : st.perm ≠ .active) :
    (match performTransition .read rel prot st with | some st' => st' | none => st).perm ≠ .active := by
  rcases st with ⟨(_ | _) | _ | _ | _ | _, _ | _⟩ <;> cases rel <;> cases prot <;>
    first | decide | exact absurd rfl h

/-- Accesses never clear the `accessed` flag. -/
theorem applyTreeAccess_accessed_mono (tree : BorrowTree) (start : BorTag) (kind : AccessKind)
    (range : ByteRange) (active : ActiveProtectors) (mode : ChildrenVisitMode) (n : BorTag)
    (b : Nat) (h : (tree.locState n b).accessed = true) :
    ((applyTreeAccess tree start kind range active mode).locState n b).accessed = true := by
  cases hP : tree.present n with
  | false => rw [applyTreeAccess_locState_absent _ _ _ _ _ _ _ _ hP]; exact h
  | true =>
    cases hb : range.contains b with
    | false => rw [applyTreeAccess_locState_out _ _ _ _ _ _ _ _ hb]; exact h
    | true =>
      rw [applyTreeAccess_locState_in _ _ _ _ _ _ _ _ hP hb]
      cases nodeAccessRelatedness tree start mode n with
      | none => exact h
      | some rel => exact performTransition_update_accessed_mono kind rel _ h

/-- Read accesses never create `Active`. -/
theorem applyTreeAccess_read_ne_active (tree : BorrowTree) (start : BorTag) (range : ByteRange)
    (active : ActiveProtectors) (mode : ChildrenVisitMode) (n : BorTag) (b : Nat)
    (h : (tree.locState n b).perm ≠ .active) :
    ((applyTreeAccess tree start .read range active mode).locState n b).perm ≠ .active := by
  cases hP : tree.present n with
  | false => rw [applyTreeAccess_locState_absent _ _ _ _ _ _ _ _ hP]; exact h
  | true =>
    cases hb : range.contains b with
    | false => rw [applyTreeAccess_locState_out _ _ _ _ _ _ _ _ hb]; exact h
    | true =>
      rw [applyTreeAccess_locState_in _ _ _ _ _ _ _ _ hP hb]
      cases nodeAccessRelatedness tree start mode n with
      | none => exact h
      | some rel => exact performTransition_update_read_ne_active rel _ h

theorem nodeAccessRelatedness_skip_not_desc_of_foreign {tree : BorrowTree} {start n : BorTag}
    (h : nodeAccessRelatedness tree start .skipChildrenOfAccessed n = some .foreignAccess) :
    tree.isAnc start n = false := by
  cases hd : tree.isAnc start n with
  | false => rfl
  | true =>
    cases hA : tree.isAnc n start with
    | true => rw [nodeAccessRelatedness_anc hA] at h; cases h
    | false => rw [nodeAccessRelatedness_skip_desc hA hd] at h; cases h

/-- **A protector-end read only flips conflict latches**: if the released tag is not
`Active` where it is accessed (so the implicit access is a read), every local node is
already accessed there, and no foreign *non-descendant* node is `Active` there
(descendants are skipped by `ChildrenVisitMode.skipChildrenOfAccessed`), then stage-1
release changes every location only up to its conflict latch. -/
theorem applyReleaseProtector_read_eraseLatch {tree : BorrowTree} {t_rel : BorTag}
    {active : ActiveProtectors}
    (hRead : ∀ b, (tree.locState t_rel b).accessed = true → (tree.locState t_rel b).perm ≠ .active)
    (hLocal : ∀ n b, tree.present n = true → (tree.locState t_rel b).accessed = true →
      tree.isAnc n t_rel = true → (tree.locState n b).accessed = true)
    (hForeign : ∀ n b, tree.present n = true → (tree.locState t_rel b).accessed = true →
      tree.isAnc n t_rel = false → tree.isAnc t_rel n = false → (tree.locState n b).perm ≠ .active)
    (n : BorTag) (b : Nat) :
    ((applyReleaseProtector tree t_rel active).locState n b).eraseLatch =
      (tree.locState n b).eraseLatch := by
  cases hP : tree.present n with
  | false => rw [applyReleaseProtector_locState_absent _ _ _ _ _ hP]
  | true =>
    cases hA : (tree.locState t_rel b).accessed with
    | false => rw [applyReleaseProtector_locState_unacc _ _ _ _ _ hA]
    | true =>
      rw [applyReleaseProtector_locState_acc _ _ _ _ _ hP hA,
        Permission.associatedAccess_of_ne_active (hRead b hA)]
      cases hR : nodeAccessRelatedness tree t_rel .skipChildrenOfAccessed n with
      | none => rfl
      | some rel =>
        cases rel with
        | localAccess =>
          exact eraseLatch_update_localRead _
            (hLocal n b hP hA (nodeAccessRelatedness_isAnc_of_local hR))
        | foreignAccess =>
          exact eraseLatch_update_foreignRead _
            (hForeign n b hP hA (nodeAccessRelatedness_not_isAnc_of_foreign hR)
              (nodeAccessRelatedness_skip_not_desc_of_foreign hR))

/-- **The stage-1 / stage-2-only separation of
`stage1_vs_stage2Only_two_arg_release_differs` is unobservable**: after Miri's complete
stage-1 release (both protected arguments, in order) and `GlobalState.endCall`, the tree
is latch-equivalent to the stage-2-only tree under the post-call protector set, so every
later access, retag, or release has the same UB verdict (`LatchEquiv.noUB_iff`,
`LatchEquiv.access`, `LatchEquiv.retag`, `LatchEquiv.release`,
`LatchEquiv.releaseNoUB_iff`). -/
theorem stage1_vs_stage2Only_two_arg_release_unobservable (r : ByteRange) :
    let active1 := insertActiveProtector (fun _ => false) 0
    let tree1 := retagChild (rootTree 0) 0 1 (some (.strong 0)) (.reservedFrz false) r active1
    let tree2 := retagChild tree1 0 2 (some (.strong 0)) (.reservedFrz false) r active1
    LatchEquiv (applyReleaseProtector (applyReleaseProtector tree2 1 active1) 2 active1) tree2
      (removeActiveProtector active1 0) := by
  intro active1 tree1 tree2
  have hPres : ∀ n, tree2.present n = true → n = 0 ∨ n = 1 ∨ n = 2 := by
    intro n hn
    simp only [tree2, tree1, retagChild, applyTreeAccess, insertChildNode, rootTree,
      Bool.or_eq_true, decide_eq_true_eq] at hn
    rcases hn with rfl | rfl | rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  have hAcc0 : ∀ b, (tree2.locState 0 b).accessed = true := by
    intro b
    show ((applyTreeAccess (insertChildNode tree1 0 2 (some (.strong 0)) (.reservedFrz false)) 2 .read
      r active1 .visitChildrenOfAccessed).locState 0 b).accessed = true
    apply applyTreeAccess_accessed_mono
    rw [insertChildNode_locState_of_ne _ _ _ _ _ (by decide : (0 : Nat) ≠ 2)]
    show ((applyTreeAccess (insertChildNode (rootTree 0) 0 1 (some (.strong 0)) (.reservedFrz false)) 1
      .read r active1 .visitChildrenOfAccessed).locState 0 b).accessed = true
    apply applyTreeAccess_accessed_mono
    rw [insertChildNode_locState_of_ne _ _ _ _ _ (by decide : (0 : Nat) ≠ 1)]
    rfl
  have hNA1 : ∀ b, (tree2.locState 1 b).perm ≠ .active := by
    intro b
    show ((applyTreeAccess (insertChildNode tree1 0 2 (some (.strong 0)) (.reservedFrz false)) 2 .read
      r active1 .visitChildrenOfAccessed).locState 1 b).perm ≠ .active
    apply applyTreeAccess_read_ne_active
    rw [insertChildNode_locState_of_ne _ _ _ _ _ (by decide : (1 : Nat) ≠ 2)]
    show ((applyTreeAccess (insertChildNode (rootTree 0) 0 1 (some (.strong 0)) (.reservedFrz false)) 1
      .read r active1 .visitChildrenOfAccessed).locState 1 b).perm ≠ .active
    apply applyTreeAccess_read_ne_active
    rw [insertChildNode_locState_child]
    decide
  have hNA2 : ∀ b, (tree2.locState 2 b).perm ≠ .active := by
    intro b
    show ((applyTreeAccess (insertChildNode tree1 0 2 (some (.strong 0)) (.reservedFrz false)) 2 .read
      r active1 .visitChildrenOfAccessed).locState 2 b).perm ≠ .active
    apply applyTreeAccess_read_ne_active
    rw [insertChildNode_locState_child]
    decide
  have hE1 : ∀ n b, ((applyReleaseProtector tree2 1 active1).locState n b).eraseLatch =
      (tree2.locState n b).eraseLatch := by
    refine applyReleaseProtector_read_eraseLatch (fun b _ => hNA1 b) ?_ ?_
    · intro n b hP hA hAnc
      rcases hPres n hP with rfl | rfl | rfl
      · exact hAcc0 b
      · exact hA
      · exact absurd hAnc (Bool.ne_true_of_eq_false rfl)
    · intro n b hP _ hAnc _
      rcases hPres n hP with rfl | rfl | rfl
      · exact absurd hAnc (Bool.ne_false_of_eq_true rfl)
      · exact absurd hAnc (Bool.ne_false_of_eq_true rfl)
      · exact hNA2 b
  let tree3 := applyReleaseProtector tree2 1 active1
  have hAcc3 : ∀ n b, (tree3.locState n b).accessed = (tree2.locState n b).accessed := by
    intro n b
    rw [← LocationState.eraseLatch_accessed (tree3.locState n b), hE1 n b,
      LocationState.eraseLatch_accessed]
  have hE2 : ∀ n b, ((applyReleaseProtector tree3 2 active1).locState n b).eraseLatch =
      (tree3.locState n b).eraseLatch := by
    refine applyReleaseProtector_read_eraseLatch
      (fun b _ => LocationState.ne_active_of_eraseLatch_eq (hE1 2 b) (hNA2 b)) ?_ ?_
    · intro n b hP hA hAnc
      rcases hPres n hP with rfl | rfl | rfl
      · rw [hAcc3]; exact hAcc0 b
      · exact absurd hAnc (Bool.ne_true_of_eq_false rfl)
      · exact hA
    · intro n b hP _ hAnc _
      rcases hPres n hP with rfl | rfl | rfl
      · exact absurd hAnc (Bool.ne_false_of_eq_true rfl)
      · exact LocationState.ne_active_of_eraseLatch_eq (hE1 1 b) (hNA1 b)
      · exact absurd hAnc (Bool.ne_false_of_eq_true rfl)
  have hNoProt : ∀ n, (applyReleaseProtector tree3 2 active1).isTagProtected n
      (removeActiveProtector active1 0) = false := by
    intro n
    rw [show removeActiveProtector active1 0 = (fun _ => false) from removeActiveProtector_insert rfl]
    unfold BorrowTree.isTagProtected
    cases (applyReleaseProtector tree3 2 active1).protector n <;> rfl
  exact ⟨rfl, rfl, rfl, fun n b => (hE2 n b).trans (hE1 n b),
    fun n b hn => by rw [hNoProt n] at hn; cases hn⟩

/-- Consequence of `stage1_vs_stage2Only_two_arg_release_unobservable`: every later access
has the same UB verdict after stage-1 + stage-2 release as after stage-2-only release. -/
theorem stage1_vs_stage2Only_two_arg_release_same_verdicts (r : ByteRange) (start : BorTag)
    (kind : AccessKind) (range : ByteRange) (mode : ChildrenVisitMode) :
    let active1 := insertActiveProtector (fun _ => false) 0
    let tree1 := retagChild (rootTree 0) 0 1 (some (.strong 0)) (.reservedFrz false) r active1
    let tree2 := retagChild tree1 0 2 (some (.strong 0)) (.reservedFrz false) r active1
    TreeAccessNoUB (applyReleaseProtector (applyReleaseProtector tree2 1 active1) 2 active1) start
        kind range (removeActiveProtector active1 0) mode ↔
      TreeAccessNoUB tree2 start kind range (removeActiveProtector active1 0) mode :=
  (stage1_vs_stage2Only_two_arg_release_unobservable r).noUB_iff start kind range mode

theorem update_localRead_eq_self (prot : Bool) {st : LocationState} (h : st.accessed = true) :
    (match performTransition .read .localAccess prot st with
      | some st' => st' | none => st) = st := by
  rcases st with ⟨(_ | _) | _ | _ | _ | _, _ | _⟩ <;> first | (cases prot <;> rfl) | cases h

theorem update_foreignRead_eq_self (prot : Bool) {st : LocationState} (h₁ : st.perm ≠ .active)
    (h₂ : st.perm ≠ .reservedFrz false) :
    (match performTransition .read .foreignAccess prot st with
      | some st' => st' | none => st) = st := by
  rcases st with ⟨(_ | _) | _ | _ | _ | _, _ | _⟩ <;>
    first | (cases prot <;> rfl) | exact absurd rfl h₁ | exact absurd rfl h₂

/-- **General read-release unobservability (Rounds A3–B4)**: if the released tag is not
`Active` wherever it is accessed (so stage 1 is an implicit *read*), its ancestors are
already accessed there, no foreign *non-descendant* tag is `Active` there, and no foreign
non-descendant tag that stays protected after the call (`active'`) is an unconflicted
`ReservedFrz` there, then stage-1 release is latch-equivalent under `active'` to skipping
it.  All four conditions are automatically discharged for every UB-free `TrustedFnSpec`
execution by `trustedFnSpec_run_latchEquiv_stage2Only`. -/
theorem applyReleaseProtector_read_latchEquiv {tree : BorrowTree} {t_rel : BorTag}
    {active active' : ActiveProtectors}
    (hRead : ∀ b, (tree.locState t_rel b).accessed = true → (tree.locState t_rel b).perm ≠ .active)
    (hLocal : ∀ n b, tree.present n = true → (tree.locState t_rel b).accessed = true →
      tree.isAnc n t_rel = true → (tree.locState n b).accessed = true)
    (hForeign : ∀ n b, tree.present n = true → (tree.locState t_rel b).accessed = true →
      tree.isAnc n t_rel = false → tree.isAnc t_rel n = false → (tree.locState n b).perm ≠ .active)
    (hOutlive : ∀ n b, tree.present n = true → (tree.locState t_rel b).accessed = true →
      tree.isAnc n t_rel = false → tree.isAnc t_rel n = false →
      tree.isTagProtected n active' = true → (tree.locState n b).perm ≠ .reservedFrz false) :
    LatchEquiv (applyReleaseProtector tree t_rel active) tree active' := by
  refine ⟨rfl, rfl, rfl, applyReleaseProtector_read_eraseLatch hRead hLocal hForeign, ?_⟩
  intro n b hn
  have hn' : tree.isTagProtected n active' = true := hn
  cases hP : tree.present n with
  | false => exact applyReleaseProtector_locState_absent _ _ _ _ _ hP
  | true =>
    cases hA : (tree.locState t_rel b).accessed with
    | false => exact applyReleaseProtector_locState_unacc _ _ _ _ _ hA
    | true =>
      rw [applyReleaseProtector_locState_acc _ _ _ _ _ hP hA,
        Permission.associatedAccess_of_ne_active (hRead b hA)]
      cases hR : nodeAccessRelatedness tree t_rel .skipChildrenOfAccessed n with
      | none => rfl
      | some rel =>
        cases rel with
        | localAccess =>
          exact update_localRead_eq_self _
            (hLocal n b hP hA (nodeAccessRelatedness_isAnc_of_local hR))
        | foreignAccess =>
          have hNotAnc := nodeAccessRelatedness_not_isAnc_of_foreign hR
          have hNotDesc := nodeAccessRelatedness_skip_not_desc_of_foreign hR
          exact update_foreignRead_eq_self _ (hForeign n b hP hA hNotAnc hNotDesc)
            (hOutlive n b hP hA hNotAnc hNotDesc hn')

/-- Consequence of `applyReleaseProtector_read_latchEquiv`: under its side conditions,
every later access has the same UB verdict after stage-1 release as without it. -/
theorem applyReleaseProtector_read_same_verdicts {tree : BorrowTree} {t_rel : BorTag}
    {active active' : ActiveProtectors}
    (hRead : ∀ b, (tree.locState t_rel b).accessed = true → (tree.locState t_rel b).perm ≠ .active)
    (hLocal : ∀ n b, tree.present n = true → (tree.locState t_rel b).accessed = true →
      tree.isAnc n t_rel = true → (tree.locState n b).accessed = true)
    (hForeign : ∀ n b, tree.present n = true → (tree.locState t_rel b).accessed = true →
      tree.isAnc n t_rel = false → tree.isAnc t_rel n = false → (tree.locState n b).perm ≠ .active)
    (hOutlive : ∀ n b, tree.present n = true → (tree.locState t_rel b).accessed = true →
      tree.isAnc n t_rel = false → tree.isAnc t_rel n = false →
      tree.isTagProtected n active' = true → (tree.locState n b).perm ≠ .reservedFrz false)
    (start : BorTag) (kind : AccessKind) (range : ByteRange) (mode : ChildrenVisitMode) :
    TreeAccessNoUB (applyReleaseProtector tree t_rel active) start kind range active' mode ↔
      TreeAccessNoUB tree start kind range active' mode :=
  (applyReleaseProtector_read_latchEquiv hRead hLocal hForeign hOutlive).noUB_iff start kind range mode

/-- **Shared (`Mutability.not`) `reborrowFootprint` soundness**: when a
`TrustedFnSpec` declares two overlapping shared `&` reborrows `[(r, .not), (r, .not)]`,
both returned references emerge `Frozen` (`⟨.frozen, true⟩`) on `r`, reading
through the first preserves the second's `Frozen` permission (unlike overlapping
`&mut` in `overlapping_reborrowFootprint_write_disables_sibling`), and writes
through either reference fault with UB. -/
theorem shared_reborrowFootprint_read_ok_write_ub {tree0 : BorrowTree}
    {t_parent t_arg : BorTag} {argRange r : ByteRange}
    {activeCaller : ActiveProtectors} {callId : CallId} {b : Nat}
    (hb : r.contains b = true) :
    let spec : TrustedFnSpec := ⟨argRange, [(r, .not), (r, .not)]⟩
    let out := spec.run tree0 activeCaller t_parent t_arg callId
    let tree_r1 := applyTreeAccess out.tree (t_arg + 1) .read r out.active .visitChildrenOfAccessed
    out.rets = [t_arg + 1, t_arg + 1 + 1] ∧
      out.tree.locState (t_arg + 1) b = ⟨.frozen, true⟩ ∧
      out.tree.locState (t_arg + 1 + 1) b = ⟨.frozen, true⟩ ∧
      tree_r1.locState (t_arg + 1 + 1) b = ⟨.frozen, true⟩ ∧
      ¬ TreeAccessNoUB out.tree (t_arg + 1) .write ⟨b, b + 1⟩ out.active .visitChildrenOfAccessed ∧
      ¬ TreeAccessNoUB tree_r1 (t_arg + 1 + 1) .write ⟨b, b + 1⟩ out.active .visitChildrenOfAccessed := by
  intro spec out tree_r1
  have hne10 : t_arg + 1 ≠ t_arg := Nat.succ_ne_self t_arg
  have hne21 : t_arg + 1 + 1 ≠ t_arg + 1 := Nat.succ_ne_self (t_arg + 1)
  have hne20 : t_arg + 1 + 1 ≠ t_arg := Nat.ne_of_gt (Nat.lt_succ_of_lt (Nat.lt_succ_self t_arg))
  let active1 := insertActiveProtector activeCaller callId
  let tree1 := retagChild tree0 t_parent t_arg (some (.strong callId)) (.reservedFrz false)
    argRange active1
  let tree2 := retagChild tree1 t_arg (t_arg + 1) none (initPermOf .not) r active1
  let tree3 := retagChild tree2 t_arg (t_arg + 1 + 1) none (initPermOf .not) r active1
  have hLPres2 : tree2.present (t_arg + 1) = true := by
    rw [retagChild_present, decide_eq_true rfl, Bool.true_or]
  have hLPres3 : tree3.present (t_arg + 1) = true := by
    rw [retagChild_present, hLPres2, Bool.or_true]
  have hRPres3 : tree3.present (t_arg + 1 + 1) = true := by
    rw [retagChild_present, decide_eq_true rfl, Bool.true_or]
  have hArgRefl1 : tree1.isAnc t_arg t_arg = true := by
    show (insertChildNode tree0 t_parent t_arg (some (.strong callId)) (.reservedFrz false)).isAnc
      t_arg t_arg = true
    rw [insertChildNode_isAnc_child, decide_eq_true rfl, Bool.true_or]
  have hArgAncL2 : tree2.isAnc t_arg (t_arg + 1) = true := by
    show (insertChildNode tree1 t_arg (t_arg + 1) none (initPermOf .not)).isAnc t_arg (t_arg + 1) = true
    rw [insertChildNode_isAnc_child, hArgRefl1, Bool.or_true]
  have hArgAncL3 : tree3.isAnc t_arg (t_arg + 1) = true := by
    show (insertChildNode tree2 t_arg (t_arg + 1 + 1) none (initPermOf .not)).isAnc t_arg (t_arg + 1) = true
    rw [insertChildNode_isAnc_of_ne _ _ _ _ _ (Ne.symm hne21) (Ne.symm hne20)]
    exact hArgAncL2
  have hArgRefl2 : tree2.isAnc t_arg t_arg = true := by
    show (insertChildNode tree1 t_arg (t_arg + 1) none (initPermOf .not)).isAnc t_arg t_arg = true
    rw [insertChildNode_isAnc_of_ne _ _ _ _ _ (Ne.symm hne10) (Ne.symm hne10)]
    exact hArgRefl1
  have hArgAncR3 : tree3.isAnc t_arg (t_arg + 1 + 1) = true := by
    show (insertChildNode tree2 t_arg (t_arg + 1 + 1) none (initPermOf .not)).isAnc
      t_arg (t_arg + 1 + 1) = true
    rw [insertChildNode_isAnc_child, hArgRefl2, Bool.or_true]
  have hLNotAncArg3 : tree3.isAnc (t_arg + 1) t_arg = false := by
    show (insertChildNode tree2 t_arg (t_arg + 1 + 1) none (initPermOf .not)).isAnc
      (t_arg + 1) t_arg = false
    rw [insertChildNode_isAnc_of_ne _ _ _ _ _ (Ne.symm hne20) (Ne.symm hne21)]
    exact retag_not_desc_of_new (Ne.symm hne10)
  have hRNotAncArg3 : tree3.isAnc (t_arg + 1 + 1) t_arg = false :=
    retag_not_desc_of_new (Ne.symm hne20)
  have hLNotAncR : (insertChildNode tree2 t_arg (t_arg + 1 + 1) none (initPermOf .not)).isAnc
      (t_arg + 1) (t_arg + 1 + 1) = false := by
    rw [insertChildNode_isAnc_child, decide_eq_false (Ne.symm hne21), Bool.false_or]
    exact retag_not_desc_of_new (Ne.symm hne10)
  have hLProtI : (insertChildNode tree2 t_arg (t_arg + 1 + 1) none (initPermOf .not)).isTagProtected
      (t_arg + 1) active1 = false := by
    rw [insertChildNode_isTagProtected_of_ne _ _ _ _ _ (Ne.symm hne21)]
    show (insertChildNode tree1 t_arg (t_arg + 1) none (initPermOf .not)).isTagProtected
      (t_arg + 1) active1 = false
    exact insertChildNode_isTagProtected_child_none _ _ _ _ _
  have hLLoc2 : tree2.locState (t_arg + 1) b = ⟨.frozen, true⟩ := by
    show (applyTreeAccess (insertChildNode tree1 t_arg (t_arg + 1) none (initPermOf .not))
      (t_arg + 1) .read r active1 .visitChildrenOfAccessed).locState (t_arg + 1) b = _
    rw [applyTreeAccess_locState_in _ _ _ _ _ _ _ _
      (by rw [insertChildNode_present, decide_eq_true rfl, Bool.true_or]) hb,
      nodeAccessRelatedness_anc (by rw [insertChildNode_isAnc_child, decide_eq_true rfl, Bool.true_or]),
      insertChildNode_locState_child]
    rfl
  have hLLoc3 : tree3.locState (t_arg + 1) b = ⟨.frozen, true⟩ := by
    show (applyTreeAccess (insertChildNode tree2 t_arg (t_arg + 1 + 1) none (initPermOf .not))
      (t_arg + 1 + 1) .read r active1 .visitChildrenOfAccessed).locState (t_arg + 1) b = _
    rw [applyTreeAccess_locState_in (insertChildNode tree2 t_arg (t_arg + 1 + 1) none (initPermOf .not))
      _ _ _ _ _ _ _ hLPres3 hb,
      nodeAccessRelatedness_visit_foreign hLNotAncR]
    show (match performTransition .read .foreignAccess _ _ with | some st' => st' | none => _) = _
    rw [hLProtI, insertChildNode_locState_of_ne _ _ _ _ _ (Ne.symm hne21), hLLoc2]
    rfl
  have hRLoc3 : tree3.locState (t_arg + 1 + 1) b = ⟨.frozen, true⟩ := by
    show (applyTreeAccess (insertChildNode tree2 t_arg (t_arg + 1 + 1) none (initPermOf .not))
      (t_arg + 1 + 1) .read r active1 .visitChildrenOfAccessed).locState (t_arg + 1 + 1) b = _
    rw [applyTreeAccess_locState_in _ _ _ _ _ _ _ _
      (by rw [insertChildNode_present, decide_eq_true rfl, Bool.true_or]) hb,
      nodeAccessRelatedness_anc (by rw [insertChildNode_isAnc_child, decide_eq_true rfl, Bool.true_or]),
      insertChildNode_locState_child]
    rfl
  have hLLocPost : out.tree.locState (t_arg + 1) b = ⟨.frozen, true⟩ := by
    show (applyReleaseProtector tree3 t_arg active1).locState (t_arg + 1) b = _
    cases hAcc : (tree3.locState t_arg b).accessed with
    | false => rw [applyReleaseProtector_locState_unacc tree3 t_arg active1 _ b hAcc, hLLoc3]
    | true =>
      rw [applyReleaseProtector_locState_acc tree3 t_arg active1 _ b hLPres3 hAcc,
        nodeAccessRelatedness_skip_desc hLNotAncArg3 hArgAncL3, hLLoc3]
  have hRLocPost : out.tree.locState (t_arg + 1 + 1) b = ⟨.frozen, true⟩ := by
    show (applyReleaseProtector tree3 t_arg active1).locState (t_arg + 1 + 1) b = _
    cases hAcc : (tree3.locState t_arg b).accessed with
    | false => rw [applyReleaseProtector_locState_unacc tree3 t_arg active1 _ b hAcc, hRLoc3]
    | true =>
      rw [applyReleaseProtector_locState_acc tree3 t_arg active1 _ b hRPres3 hAcc,
        nodeAccessRelatedness_skip_desc hRNotAncArg3 hArgAncR3, hRLoc3]
  have hRNotAncL : out.tree.isAnc (t_arg + 1 + 1) (t_arg + 1) = false :=
    retag_not_desc_of_new (tree := tree2) (t_parent := t_arg) (t_child := t_arg + 1 + 1)
      (prot := none) (initPerm := initPermOf .not) (range := r) (active := active1) (Ne.symm hne21)
  have hRProt : out.tree.isTagProtected (t_arg + 1 + 1) out.active = false := by
    show (insertChildNode tree2 t_arg (t_arg + 1 + 1) none (initPermOf .not)).isTagProtected
      (t_arg + 1 + 1) out.active = false
    exact insertChildNode_isTagProtected_child_none _ _ _ _ _
  have hRLocR1 : tree_r1.locState (t_arg + 1 + 1) b = ⟨.frozen, true⟩ := by
    show (applyTreeAccess out.tree (t_arg + 1) .read r out.active
      .visitChildrenOfAccessed).locState (t_arg + 1 + 1) b = _
    rw [applyTreeAccess_locState_in out.tree _ _ _ _ _ _ _ hRPres3 hb,
      nodeAccessRelatedness_visit_foreign hRNotAncL]
    show (match performTransition .read .foreignAccess
      (out.tree.isTagProtected (t_arg + 1 + 1) out.active)
      (out.tree.locState (t_arg + 1 + 1) b) with | some st' => st' | none => _) = _
    rw [hRProt, hRLocPost]
    rfl
  have hInB : (ByteRange.mk b (b + 1)).contains b = true :=
    (ByteRange.contains_iff _ _).mpr ⟨Nat.le_refl b, Nat.lt_succ_self b⟩
  have hReflL : out.tree.isAnc (t_arg + 1) (t_arg + 1) = true := by
    show (insertChildNode tree2 t_arg (t_arg + 1 + 1) none (initPermOf .not)).isAnc
      (t_arg + 1) (t_arg + 1) = true
    rw [insertChildNode_isAnc_of_ne _ _ _ _ _ (Ne.symm hne21) (Ne.symm hne21)]
    show (insertChildNode tree1 t_arg (t_arg + 1) none (initPermOf .not)).isAnc
      (t_arg + 1) (t_arg + 1) = true
    rw [insertChildNode_isAnc_child, decide_eq_true rfl, Bool.true_or]
  have hReflR : tree_r1.isAnc (t_arg + 1 + 1) (t_arg + 1 + 1) = true := by
    show (insertChildNode tree2 t_arg (t_arg + 1 + 1) none (initPermOf .not)).isAnc
      (t_arg + 1 + 1) (t_arg + 1 + 1) = true
    rw [insertChildNode_isAnc_child, decide_eq_true rfl, Bool.true_or]
  refine ⟨rfl, hLLocPost, hRLocPost, hRLocR1, ?_, ?_⟩
  · intro hNoUB
    have hAt := hNoUB (t_arg + 1) b hLPres3 hInB
    rw [nodeAccessRelatedness_anc hReflL] at hAt
    change (performTransition .write .localAccess _ (out.tree.locState (t_arg + 1) b)).isSome = true at hAt
    rw [hLLocPost] at hAt
    cases hAt
  · intro hNoUB
    have hAt := hNoUB (t_arg + 1 + 1) b hRPres3 hInB
    rw [nodeAccessRelatedness_anc hReflR] at hAt
    change (performTransition .write .localAccess _ (tree_r1.locState (t_arg + 1 + 1) b)).isSome = true at hAt
    rw [hRLocR1] at hAt
    cases hAt

/-- Reflexivity of the live `isBorrowDescendantOrSelf` hierarchy traversal. -/
theorem isBorrowDescendantOrSelf_refl
    (borrows : List Trusted.Rustc.V2026_06_01.MirSemantics.BorrowEntry) (tag : Nat) :
    Trusted.Rustc.V2026_06_01.MirSemantics.isBorrowDescendantOrSelf borrows tag tag = true := by
  unfold Trusted.Rustc.V2026_06_01.MirSemantics.isBorrowDescendantOrSelf
  cases Trusted.Sequence.length borrows with
  | zero => exact Nat.beq_refl tag
  | succ f =>
    unfold Trusted.Rustc.V2026_06_01.MirSemantics.isBorrowDescendantOrSelfAux
    rw [Nat.beq_refl]

/-- **Live hierarchy relatedness bridge**: when `tree.isAnc e.tag wTag` agrees
with live `isBorrowDescendantOrSelf allBorrows wTag e.tag`, the prototype's
`nodeAccessRelatedness` under `.visitChildrenOfAccessed` equals the live
`treeBorrowWriterRelatedness` after `resolveTreeBorrowWriterTag`. -/
theorem nodeAccessRelatedness_visit_eq_live_writer (tree : BorrowTree)
    (allBorrows : List Trusted.Rustc.V2026_06_01.MirSemantics.BorrowEntry)
    (e : Trusted.Rustc.V2026_06_01.MirSemantics.BorrowEntry) (wTag : BorTag)
    (hAnc : tree.isAnc e.tag wTag =
      Trusted.Rustc.V2026_06_01.MirSemantics.isBorrowDescendantOrSelf allBorrows wTag e.tag) :
    (nodeAccessRelatedness tree wTag .visitChildrenOfAccessed e.tag).map AccessRelatedness.toLive =
      some (Trusted.Rustc.V2026_06_01.MirSemantics.treeBorrowWriterRelatedness e
        (Trusted.Rustc.V2026_06_01.MirSemantics.resolveTreeBorrowWriterTag allBorrows e (some wTag))) := by
  unfold nodeAccessRelatedness
    Trusted.Rustc.V2026_06_01.MirSemantics.resolveTreeBorrowWriterTag
    Trusted.Rustc.V2026_06_01.MirSemantics.treeBorrowWriterRelatedness
  rw [hAnc]
  dsimp only
  cases hDesc : Trusted.Rustc.V2026_06_01.MirSemantics.isBorrowDescendantOrSelf allBorrows wTag e.tag with
  | true =>
    dsimp only
    rw [Nat.beq_refl]
    rfl
  | false =>
    have hNe : Nat.beq e.tag wTag = false := by
      cases hb : Nat.beq e.tag wTag with
      | false => rfl
      | true =>
        have heq := Nat.eq_of_beq_eq_true hb
        rw [heq, isBorrowDescendantOrSelf_refl] at hDesc
        cases hDesc
    dsimp only
    rw [hNe]
    rfl

/-- **Live protected-write conflict bridge**: on any live `BorrowEntry` `e`
matching permission `p`, `borrowEntryWriteConflicts` after
`resolveTreeBorrowWriterTag` equals `!(performTransition .write rel true ⟨p, true⟩).isSome`. -/
theorem borrowEntryWriteConflicts_eq_live (tree : BorrowTree)
    (allBorrows : List Trusted.Rustc.V2026_06_01.MirSemantics.BorrowEntry)
    (e : Trusted.Rustc.V2026_06_01.MirSemantics.BorrowEntry) (wTag : BorTag) (p : Permission)
    (hPerm : e.perm = p.toLiveTreeBorrowPerm)
    (hAnc : tree.isAnc e.tag wTag =
      Trusted.Rustc.V2026_06_01.MirSemantics.isBorrowDescendantOrSelf allBorrows wTag e.tag) :
    Trusted.Rustc.V2026_06_01.MirSemantics.borrowEntryWriteConflicts e
      (Trusted.Rustc.V2026_06_01.MirSemantics.resolveTreeBorrowWriterTag allBorrows e (some wTag)) =
      !(performTransition .write
        (if tree.isAnc e.tag wTag then .localAccess else .foreignAccess)
        true ⟨p, true⟩).isSome := by
  have hRel := nodeAccessRelatedness_visit_eq_live_writer tree allBorrows e wTag hAnc
  unfold nodeAccessRelatedness at hRel
  unfold Trusted.Rustc.V2026_06_01.MirSemantics.borrowEntryWriteConflicts
  rw [hPerm]
  cases hA : tree.isAnc e.tag wTag with
  | true =>
    rw [hA] at hRel
    simp only [↓reduceIte, Option.map, Option.some.injEq] at hRel ⊢
    rw [← hRel, performTransition_accessed_isSome_eq_live, Bool.not_not]
    rfl
  | false =>
    rw [hA] at hRel
    simp only [Bool.false_eq_true, ↓reduceIte, Option.map, Option.some.injEq] at hRel ⊢
    rw [← hRel, performTransition_accessed_isSome_eq_live, Bool.not_not]
    rfl

/-- **Live return-path protector bridge**: when `caller.callerProtector = none`
(as pushed by `pushCalleeFrame`), live `restoreCallerProtectors` equals
`removeActiveProtector (insertActiveProtector … callId) callId` for any fresh
callee protector `callId`. -/
theorem restoreCallerProtectors_eq_live
    (caller : Trusted.Rustc.V2026_06_01.MirSemantics.SavedCallerFrame)
    (hNoCallerProt : caller.callerProtector = none)
    (callId : CallId) (c : CallId)
    (hFresh : Trusted.Rustc.V2026_06_01.MirSemantics.natListContainsBool
      caller.calleeProtectors callId = false) :
    Trusted.Rustc.V2026_06_01.MirSemantics.natListContainsBool
      (Trusted.Rustc.V2026_06_01.MirSemantics.restoreCallerProtectors caller) c =
      removeActiveProtector
        (insertActiveProtector
          (Trusted.Rustc.V2026_06_01.MirSemantics.natListContainsBool caller.calleeProtectors)
          callId)
        callId c := by
  rw [removeActiveProtector_insert hFresh]
  unfold Trusted.Rustc.V2026_06_01.MirSemantics.restoreCallerProtectors
  rw [hNoCallerProt]

/-- **Observable post-return UB separation between Miri's stage-1 + stage-2
release and stage-2-only release under function-entry + LIFO protector
discipline**: on `rootTree 0`, a callee enters (`callId = 0`) with a protected
`&mut` argument `t_arg = 1` on `⟨0, 1⟩`, writes byte `0` through `t_arg`
(promoting `t_arg` to `Active` on byte `0`), and then reborrows an unprotected
sibling `t_sib = 2` from `0` on neighboring range `⟨1, 2⟩` before returning.
Every step in the callee and at return is UB-free, yet:
- under Miri's two-stage release (`applyReleaseProtector` + `endCall`),
  `t_arg`'s `Active` permission fires an implicit `AccessKind.write` at exit
  that disables `t_sib` on byte `0` (`⟨.disabled, false⟩`), so post-return
  caller reads and writes of byte `0` through `t_sib` fault with UB;
- under stage-2-only release (`removeActiveProtector` / `restoreCallerProtectors`
  without stage 1), `t_sib` remains `⟨.reservedFrz false, false⟩` on byte `0`,
  so the identical post-return caller reads and writes succeed UB-free. -/
theorem stage1_write_release_observable_ub_separation :
    let active0 : ActiveProtectors := fun _ => false
    let active1 := insertActiveProtector active0 0
    let r0 : ByteRange := ⟨0, 1⟩
    let r1 : ByteRange := ⟨1, 2⟩
    let tree0 := rootTree 0
    let tree1 := retagChild tree0 0 1 (some (.strong 0)) (.reservedFrz false) r0 active1
    let tree2 := applyTreeAccess tree1 1 .write r0 active1 .visitChildrenOfAccessed
    let tree3 := retagChild tree2 0 2 none (.reservedFrz false) r1 active1
    let activePost := removeActiveProtector active1 0
    let treeStage12 := applyReleaseProtector tree3 1 active1
    let treeStage2Only := tree3
    TreeAccessNoUB (insertChildNode tree0 0 1 (some (.strong 0)) (.reservedFrz false))
        1 .read r0 active1 .visitChildrenOfAccessed ∧
      TreeAccessNoUB tree1 1 .write r0 active1 .visitChildrenOfAccessed ∧
      TreeAccessNoUB (insertChildNode tree2 0 2 none (.reservedFrz false))
        2 .read r1 active1 .visitChildrenOfAccessed ∧
      releaseProtectorNoUB tree3 1 active1 ∧
      treeStage12.locState 2 0 = ⟨.disabled, false⟩ ∧
      treeStage2Only.locState 2 0 = ⟨.reservedFrz false, false⟩ ∧
      ¬ TreeAccessNoUB treeStage12 2 .read r0 activePost .visitChildrenOfAccessed ∧
      ¬ TreeAccessNoUB treeStage12 2 .write r0 activePost .visitChildrenOfAccessed ∧
      TreeAccessNoUB treeStage2Only 2 .read r0 activePost .visitChildrenOfAccessed ∧
      TreeAccessNoUB treeStage2Only 2 .write r0 activePost .visitChildrenOfAccessed := by
  intro active0 active1 r0 r1 tree0 tree1 tree2 tree3 activePost treeStage12 treeStage2Only
  have hb0 : ∀ b, r0.contains b = true → b = 0 := by
    intro b hb
    have h := (ByteRange.contains_iff r0 b).mp hb
    dsimp [r0] at h
    omega
  have hb1 : ∀ b, r1.contains b = true → b = 1 := by
    intro b hb
    have h := (ByteRange.contains_iff r1 b).mp hb
    dsimp [r1] at h
    omega
  have hPres1 : ∀ n, (insertChildNode tree0 0 1 (some (.strong 0)) (.reservedFrz false)).present n = true →
      n = 1 ∨ n = 0 := by
    intro n hn
    simp only [insertChildNode, tree0, rootTree, Bool.or_eq_true, decide_eq_true_eq] at hn
    exact hn
  have hPres2 : ∀ n, tree1.present n = true → n = 1 ∨ n = 0 := hPres1
  have hPres3I : ∀ n, (insertChildNode tree2 0 2 none (.reservedFrz false)).present n = true →
      n = 2 ∨ n = 1 ∨ n = 0 := by
    intro n hn
    simp only [insertChildNode, tree2, applyTreeAccess, tree1, retagChild, tree0, rootTree,
      Bool.or_eq_true, decide_eq_true_eq] at hn
    exact hn
  have hPres3 : ∀ n, tree3.present n = true → n = 2 ∨ n = 1 ∨ n = 0 := hPres3I
  have hAcc3 : ∀ b, (tree3.locState 1 b).accessed = true → b = 0 := by
    intro b hAcc
    by_cases hb : b = 0
    · exact hb
    · exfalso
      have hnr0 : r0.contains b = false := by
        cases hc : r0.contains b with
        | false => rfl
        | true => exact absurd (hb0 b hc) hb
      by_cases h1 : b = 1
      · subst h1
        cases hAcc
      · have hnr1 : r1.contains b = false := by
          cases hc : r1.contains b with
          | false => rfl
          | true => exact absurd (hb1 b hc) h1
        have h3 : tree3.locState 1 b = tree2.locState 1 b := by
          show (applyTreeAccess (insertChildNode tree2 0 2 none (.reservedFrz false)) 2 .read r1
            active1 .visitChildrenOfAccessed).locState 1 b = _
          rw [applyTreeAccess_locState_out _ _ _ _ _ _ _ _ hnr1,
            insertChildNode_locState_of_ne _ _ _ _ _ (by decide)]
        rw [h3] at hAcc
        have h2 : tree2.locState 1 b = tree1.locState 1 b :=
          applyTreeAccess_locState_out tree1 1 .write r0 active1 .visitChildrenOfAccessed 1 b hnr0
        rw [h2] at hAcc
        have h1' : tree1.locState 1 b = ⟨.reservedFrz false, false⟩ := by
          show (retagChild tree0 0 1 (some (.strong 0)) (.reservedFrz false) r0 active1).locState 1 b = _
          rw [retagChild_locState_out _ _ _ _ _ _ _ _ _ hnr0, insertChildNode_locState_child]
        rw [h1'] at hAcc
        cases hAcc
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro n b hP hb
    have h := hb0 b hb; subst h
    rcases hPres1 n hP with rfl | rfl <;> rfl
  · intro n b hP hb
    have h := hb0 b hb; subst h
    rcases hPres2 n hP with rfl | rfl <;> rfl
  · intro n b hP hb
    have h := hb1 b hb; subst h
    rcases hPres3I n hP with rfl | rfl | rfl <;> rfl
  · intro n b hP hAcc
    have h := hAcc3 b hAcc; subst h
    rcases hPres3 n hP with rfl | rfl | rfl <;> rfl
  · intro hNoUB
    have h := hNoUB 2 0 rfl rfl
    cases h
  · intro hNoUB
    have h := hNoUB 2 0 rfl rfl
    cases h
  · intro n b hP hb
    have h := hb0 b hb; subst h
    rcases hPres3 n hP with rfl | rfl | rfl <;> rfl
  · intro n b hP hb
    have h := hb0 b hb; subst h
    rcases hPres3 n hP with rfl | rfl | rfl <;> rfl

/-- **Child reborrows remain sound under stage-2-only release even after the
callee activates `t_arg`**: unlike foreign sibling tags (which separate stage-1
from stage-2-only in `stage1_write_release_observable_ub_separation`), a child
`t_ret` reborrowed *under* `t_arg` after the callee writes through `t_arg` is a
descendant skipped by `ChildrenVisitMode.skipChildrenOfAccessed` and retains
`HasUniqueWritePerm` under stage-2-only `removeActiveProtector`. -/
theorem reborrow_return_after_parent_write_stage2Only_unique_write_perm {tree0 : BorrowTree}
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
    let tree2 := applyTreeAccess tree1 t_arg .write parentRange active1 .visitChildrenOfAccessed
    let tree3 := retagChild tree2 t_arg t_ret none (initPermOf .mut) subRange active1
    let active_post := removeActiveProtector active1 callId
    TreeAccessNoUB tree1 t_arg .write parentRange active1 .visitChildrenOfAccessed ∧
      HasUniqueWritePerm tree3 t_ret subRange active_post ∧
      TreeAccessNoUB tree3 t_ret .write subRange active_post .visitChildrenOfAccessed := by
  intro active1 tree1 tree2 tree3 active_post
  have hPerm0' := hasUniqueWritePerm_insert_fresh_callId hFreshCallId hPerm0
  have hTree1Perm : HasUniqueWritePerm tree1 t_arg parentRange active1 :=
    (retagChild_hasUniqueWritePerm (some (.strong callId)) fnEntry_writable hPerm0'
      (ByteRange.Sub.refl _) hFreshArg).2
  obtain ⟨hParentWriteNoUB, hTree2ArgPerm⟩ :=
    local_access_preserves_hasUniqueWritePerm .write hTree1Perm (ByteRange.Sub.refl _)
  have hFreshRet2 : tree2.present t_ret = false := by
    show tree1.present t_ret = false
    rw [retagChild_present, decide_eq_false hRetNeArg, Bool.false_or]
    exact hFreshRet
  have hTree3RetPerm : HasUniqueWritePerm tree3 t_ret subRange active1 :=
    (retagChild_hasUniqueWritePerm none initPermOf_mut_writable hTree2ArgPerm hSub hFreshRet2).2
  have hPost : HasUniqueWritePerm tree3 t_ret subRange active_post :=
    hasUniqueWritePerm_remove_callId hCallFresh hTree3RetPerm
  exact ⟨hParentWriteNoUB, hPost,
    (local_access_preserves_hasUniqueWritePerm .write hPost (ByteRange.Sub.refl _)).1⟩

/-- **Descendant exclusion in `hForeign` is genuine**: on a 2-node tree where
child `1` under `t_rel = 0` is `Active` (violating A3's unguarded `isAnc n t_rel = false → perm ≠ .active`),
`ChildrenVisitMode.skipChildrenOfAccessed` skips `1` and `applyReleaseProtector_read_latchEquiv`
still establishes `LatchEquiv`. -/
theorem read_latchEquiv_ignores_active_descendant :
    let tree : BorrowTree :=
      { present := fun t => decide (t = 0) || decide (t = 1)
        isAnc := fun a d =>
          (decide (a = 0) && (decide (d = 0) || decide (d = 1))) || (decide (a = 1) && decide (d = 1))
        protector := fun _ => none
        locState := fun t _ => if t = 0 then ⟨.reservedFrz false, true⟩ else ⟨.active, true⟩ }
    let active : ActiveProtectors := fun _ => false
    (¬ ∀ n b, tree.present n = true → (tree.locState 0 b).accessed = true →
        tree.isAnc n 0 = false → (tree.locState n b).perm ≠ .active) ∧
      LatchEquiv (applyReleaseProtector tree 0 active) tree active := by
  intro tree active
  refine ⟨?_, ?_⟩
  · intro hOld
    exact hOld 1 0 rfl rfl rfl rfl
  · refine applyReleaseProtector_read_latchEquiv
      (fun _ _ h => nomatch h) ?_ ?_ (fun _ _ _ _ _ _ hn => by cases hn)
    · intro n b hP _ hAnc
      simp only [tree, Bool.or_eq_true, decide_eq_true_eq] at hP
      rcases hP with rfl | rfl
      · rfl
      · cases hAnc
    · intro n b hP _ hNotAnc hNotDesc
      simp only [tree, Bool.or_eq_true, decide_eq_true_eq] at hP
      rcases hP with rfl | rfl
      · cases hNotAnc
      · cases hNotDesc

/-- **Necessity of `hOutlive` in `applyReleaseProtector_read_latchEquiv`**: when
`hRead`, `hLocal`, and `hForeign` all hold, but a foreign sibling tag `2`
protected by an outliving caller protector (`0`) is still unconflicted
(`ReservedFrz false`) at an accessed byte of `t_rel = 1` (violating `hOutlive`),
stage-1 read release flips `2`'s latch to `ReservedFrz true`, making a subsequent
local write through `2` UB (`¬ TreeAccessNoUB`) under stage-1 release yet UB-free
(`TreeAccessNoUB`) without stage-1. -/
theorem stage1_read_release_outliving_unconflicted_separates :
    let active' : ActiveProtectors := insertActiveProtector (fun _ => false) 0
    let active : ActiveProtectors := insertActiveProtector active' 1
    let tree : BorrowTree :=
      { present := fun t => decide (t = 0) || decide (t = 1) || decide (t = 2)
        isAnc := fun a d =>
          (decide (a = 0) && (decide (d = 0) || decide (d = 1) || decide (d = 2))) ||
          (decide (a = 1) && decide (d = 1)) ||
          (decide (a = 2) && decide (d = 2))
        protector := fun t =>
          if t = 1 then some (.strong 1) else if t = 2 then some (.strong 0) else none
        locState := fun t b =>
          if b = 0 then
            if t = 0 then ⟨.active, true⟩ else ⟨.reservedFrz false, true⟩
          else ⟨.active, false⟩ }
    (∀ b, (tree.locState 1 b).accessed = true → (tree.locState 1 b).perm ≠ .active) ∧
      (∀ n b, tree.present n = true → (tree.locState 1 b).accessed = true →
        tree.isAnc n 1 = true → (tree.locState n b).accessed = true) ∧
      (∀ n b, tree.present n = true → (tree.locState 1 b).accessed = true →
        tree.isAnc n 1 = false → tree.isAnc 1 n = false → (tree.locState n b).perm ≠ .active) ∧
      releaseProtectorNoUB tree 1 active ∧
      ¬ TreeAccessNoUB (applyReleaseProtector tree 1 active) 2 .write ⟨0, 1⟩ active'
          .visitChildrenOfAccessed ∧
      TreeAccessNoUB tree 2 .write ⟨0, 1⟩ active' .visitChildrenOfAccessed := by
  intro active' active tree
  have hAcc0 : ∀ b, (tree.locState 1 b).accessed = true → b = 0 := by
    intro b hAcc
    by_cases hb : b = 0
    · exact hb
    · dsimp [tree] at hAcc
      rw [ite_eq_right hb] at hAcc
      cases hAcc
  have hPres : ∀ n, tree.present n = true → n = 0 ∨ n = 1 ∨ n = 2 := by
    intro n hn
    simp only [tree, Bool.or_eq_true, decide_eq_true_eq] at hn
    rcases hn with (rfl | rfl) | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hb0 : ∀ b, (ByteRange.mk 0 1).contains b = true → b = 0 := by
    intro b hb
    have h := (ByteRange.contains_iff ⟨0, 1⟩ b).mp hb
    dsimp at h
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hAcc
    have h := hAcc0 b hAcc; subst h
    decide
  · intro n b hP hAcc hAnc
    have h := hAcc0 b hAcc; subst h
    rcases hPres n hP with rfl | rfl | rfl <;> first | rfl | cases hAnc
  · intro n b hP hAcc hNotAnc _
    have h := hAcc0 b hAcc; subst h
    rcases hPres n hP with rfl | rfl | rfl <;> first | decide | cases hNotAnc
  · intro n b hP hAcc
    have h := hAcc0 b hAcc; subst h
    rcases hPres n hP with rfl | rfl | rfl <;> rfl
  · intro hNoUB
    have h := hNoUB 2 0 rfl rfl
    cases h
  · intro n b hP hb
    have h := hb0 b hb; subst h
    rcases hPres n hP with rfl | rfl | rfl <;> rfl

theorem performTransition_localRead_accessed_of_isSome (prot : Bool) {st : LocationState}
    (h : (performTransition .read .localAccess prot st).isSome = true) :
    (match performTransition .read .localAccess prot st with | some st' => st' | none => st).accessed =
      true := by
  rcases st with ⟨(_ | _) | _ | _ | _ | _, _ | _⟩ <;> cases prot <;> first | rfl | cases h

theorem performTransition_foreignRead_ne_active_of_isSome (prot : Bool) {st : LocationState}
    (h : (performTransition .read .foreignAccess prot st).isSome = true) :
    (match performTransition .read .foreignAccess prot st with | some st' => st' | none => st).perm ≠
      .active := by
  rcases st with ⟨(_ | _) | _ | _ | _ | _, _ | _⟩ <;> cases prot <;> first | decide | cases h

theorem performTransition_foreignRead_protected_ne_unconflicted_of_isSome {st : LocationState}
    (h : (performTransition .read .foreignAccess true st).isSome = true) :
    (match performTransition .read .foreignAccess true st with | some st' => st' | none => st).perm ≠
      .reservedFrz false := by
  rcases st with ⟨(_ | _) | _ | _ | _ | _, _ | _⟩ <;> first | decide | cases h

/-- Inductive invariant established by UB-free `FnEntry` retag and preserved by
every UB-free `reborrowFootprint` retag under `t_arg`, discharging all four side
conditions of `applyReleaseProtector_read_latchEquiv` under arbitrary outliving
caller protectors `activeCaller`. -/
structure ReadReleaseSafe (tree : BorrowTree) (t_arg : BorTag)
    (activeCaller : ActiveProtectors) : Prop where
  arg_present : tree.present t_arg = true
  arg_refl : tree.isAnc t_arg t_arg = true
  arg_ne_active : ∀ b, (tree.locState t_arg b).perm ≠ .active
  local_acc : ∀ n b, tree.present n = true → (tree.locState t_arg b).accessed = true →
    tree.isAnc n t_arg = true → (tree.locState n b).accessed = true
  foreign_ne_active : ∀ n b, tree.present n = true → (tree.locState t_arg b).accessed = true →
    tree.isAnc n t_arg = false → tree.isAnc t_arg n = false → (tree.locState n b).perm ≠ .active
  outlive_conflicted : ∀ n b, tree.present n = true → (tree.locState t_arg b).accessed = true →
    tree.isAnc n t_arg = false → tree.isAnc t_arg n = false →
    tree.isTagProtected n activeCaller = true → (tree.locState n b).perm ≠ .reservedFrz false

theorem readReleaseSafe_of_fnEntry {tree₀ : BorrowTree} {t_parent t_arg : BorTag}
    {argRange : ByteRange} {activeCaller : ActiveProtectors} {callId : CallId}
    (hEntryNoUB : TreeAccessNoUB
      (insertChildNode tree₀ t_parent t_arg (some (.strong callId)) (.reservedFrz false))
      t_arg .read argRange (insertActiveProtector activeCaller callId) .visitChildrenOfAccessed) :
    ReadReleaseSafe
      (retagChild tree₀ t_parent t_arg (some (.strong callId)) (.reservedFrz false) argRange
        (insertActiveProtector activeCaller callId))
      t_arg activeCaller := by
  let active₁ := insertActiveProtector activeCaller callId
  let treeI := insertChildNode tree₀ t_parent t_arg (some (.strong callId)) (.reservedFrz false)
  have hRefl : treeI.isAnc t_arg t_arg = true := by
    rw [insertChildNode_isAnc_child, decide_eq_true rfl, Bool.true_or]
  have hAccIn : ∀ b, ((retagChild tree₀ t_parent t_arg (some (.strong callId)) (.reservedFrz false)
      argRange active₁).locState t_arg b).accessed = true → argRange.contains b = true := by
    intro b hAcc
    cases hb : argRange.contains b with
    | true => rfl
    | false =>
      rw [retagChild_locState_out _ _ _ _ _ _ _ _ _ hb, insertChildNode_locState_child] at hAcc
      cases hAcc
  refine ⟨?_, hRefl, ?_, ?_, ?_, ?_⟩
  · rw [retagChild_present, decide_eq_true rfl, Bool.true_or]
  · intro b
    apply applyTreeAccess_read_ne_active
    rw [insertChildNode_locState_child]
    decide
  · intro n b hP hAcc hAnc
    have hb := hAccIn b hAcc
    have hP' : treeI.present n = true := hP
    have hAnc' : treeI.isAnc n t_arg = true := hAnc
    have hSome := hEntryNoUB n b hP' hb
    rw [nodeAccessRelatedness_anc hAnc'] at hSome
    show ((applyTreeAccess treeI t_arg .read argRange active₁ .visitChildrenOfAccessed).locState n b).accessed = true
    rw [applyTreeAccess_locState_in _ _ _ _ _ _ _ _ hP' hb, nodeAccessRelatedness_anc hAnc']
    exact performTransition_localRead_accessed_of_isSome _ hSome
  · intro n b hP hAcc hNotAnc _
    have hb := hAccIn b hAcc
    have hP' : treeI.present n = true := hP
    have hNotAnc' : treeI.isAnc n t_arg = false := hNotAnc
    have hSome := hEntryNoUB n b hP' hb
    rw [nodeAccessRelatedness_visit_foreign hNotAnc'] at hSome
    show ((applyTreeAccess treeI t_arg .read argRange active₁ .visitChildrenOfAccessed).locState n b).perm ≠ .active
    rw [applyTreeAccess_locState_in _ _ _ _ _ _ _ _ hP' hb, nodeAccessRelatedness_visit_foreign hNotAnc']
    exact performTransition_foreignRead_ne_active_of_isSome _ hSome
  · intro n b hP hAcc hNotAnc _ hProtCaller
    have hb := hAccIn b hAcc
    have hP' : treeI.present n = true := hP
    have hNotAnc' : treeI.isAnc n t_arg = false := hNotAnc
    have hProt₁ : treeI.isTagProtected n active₁ = true :=
      isTagProtected_insert_of_caller hProtCaller
    have hSome := hEntryNoUB n b hP' hb
    rw [nodeAccessRelatedness_visit_foreign hNotAnc', hProt₁] at hSome
    show ((applyTreeAccess treeI t_arg .read argRange active₁ .visitChildrenOfAccessed).locState n b).perm ≠
      .reservedFrz false
    rw [applyTreeAccess_locState_in _ _ _ _ _ _ _ _ hP' hb,
      nodeAccessRelatedness_visit_foreign hNotAnc', hProt₁]
    exact performTransition_foreignRead_protected_ne_unconflicted_of_isSome hSome

theorem readReleaseSafe_retagChild {tree : BorrowTree} {t_arg next : BorTag}
    {m : Mutability} {r : ByteRange} {activeCaller : ActiveProtectors} {callId : CallId}
    (hSafe : ReadReleaseSafe tree t_arg activeCaller)
    (hNe : next ≠ t_arg)
    (hStepNoUB : TreeAccessNoUB (insertChildNode tree t_arg next none (initPermOf m))
      next .read r (insertActiveProtector activeCaller callId) .visitChildrenOfAccessed) :
    ReadReleaseSafe
      (retagChild tree t_arg next none (initPermOf m) r (insertActiveProtector activeCaller callId))
      t_arg activeCaller := by
  let active₁ := insertActiveProtector activeCaller callId
  let treeI := insertChildNode tree t_arg next none (initPermOf m)
  have hArgAncNext : treeI.isAnc t_arg next = true := by
    rw [insertChildNode_isAnc_child, hSafe.arg_refl, Bool.or_true]
  have hNextNotAncArg : treeI.isAnc next t_arg = false :=
    insertChildNode_isAnc_from_child _ _ _ _ _ (Ne.symm hNe)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [retagChild_present, hSafe.arg_present, Bool.or_true]
  · show treeI.isAnc t_arg t_arg = true
    rw [insertChildNode_isAnc_of_ne _ _ _ _ _ (Ne.symm hNe) (Ne.symm hNe)]
    exact hSafe.arg_refl
  · intro b
    apply applyTreeAccess_read_ne_active
    rw [insertChildNode_locState_of_ne _ _ _ _ _ (Ne.symm hNe)]
    exact hSafe.arg_ne_active b
  · intro n b hP hAcc hAnc
    have hP' : treeI.present n = true := hP
    have hAnc' : treeI.isAnc n t_arg = true := hAnc
    have hnNe : n ≠ next := by
      intro heq
      rw [heq, hNextNotAncArg] at hAnc'
      cases hAnc'
    have hAncOld : tree.isAnc n t_arg = true := by
      rwa [insertChildNode_isAnc_of_ne _ _ _ _ _ (Ne.symm hNe) hnNe] at hAnc'
    cases hb : r.contains b with
    | false =>
      have hAccOld : (tree.locState t_arg b).accessed = true := by
        change ((applyTreeAccess treeI next .read r active₁ .visitChildrenOfAccessed).locState t_arg b).accessed = true at hAcc
        rw [applyTreeAccess_locState_out _ _ _ _ _ _ _ _ hb,
          insertChildNode_locState_of_ne _ _ _ _ _ (Ne.symm hNe)] at hAcc
        exact hAcc
      have hPresOld : tree.present n = true := by
        rw [insertChildNode_present, decide_eq_false hnNe, Bool.false_or] at hP'
        exact hP'
      show ((applyTreeAccess treeI next .read r active₁ .visitChildrenOfAccessed).locState n b).accessed = true
      rw [applyTreeAccess_locState_out _ _ _ _ _ _ _ _ hb,
        insertChildNode_locState_of_ne _ _ _ _ _ hnNe]
      exact hSafe.local_acc n b hPresOld hAccOld hAncOld
    | true =>
      have hAncNext : treeI.isAnc n next = true := by
        rw [insertChildNode_isAnc_child, hAncOld, Bool.or_true]
      have hSome := hStepNoUB n b hP' hb
      rw [nodeAccessRelatedness_anc hAncNext] at hSome
      show ((applyTreeAccess treeI next .read r active₁ .visitChildrenOfAccessed).locState n b).accessed = true
      rw [applyTreeAccess_locState_in _ _ _ _ _ _ _ _ hP' hb, nodeAccessRelatedness_anc hAncNext]
      exact performTransition_localRead_accessed_of_isSome _ hSome
  · intro n b hP hAcc hNotAnc hNotDesc
    have hP' : treeI.present n = true := hP
    have hNotAnc' : treeI.isAnc n t_arg = false := hNotAnc
    have hNotDesc' : treeI.isAnc t_arg n = false := hNotDesc
    have hnNe : n ≠ next := by
      intro heq
      rw [heq, hArgAncNext] at hNotDesc'
      cases hNotDesc'
    have hNotAncOld : tree.isAnc n t_arg = false := by
      rwa [insertChildNode_isAnc_of_ne _ _ _ _ _ (Ne.symm hNe) hnNe] at hNotAnc'
    have hNotDescOld : tree.isAnc t_arg n = false := by
      rwa [insertChildNode_isAnc_of_ne _ _ _ _ _ hnNe (Ne.symm hNe)] at hNotDesc'
    cases hb : r.contains b with
    | false =>
      have hAccOld : (tree.locState t_arg b).accessed = true := by
        change ((applyTreeAccess treeI next .read r active₁ .visitChildrenOfAccessed).locState t_arg b).accessed = true at hAcc
        rw [applyTreeAccess_locState_out _ _ _ _ _ _ _ _ hb,
          insertChildNode_locState_of_ne _ _ _ _ _ (Ne.symm hNe)] at hAcc
        exact hAcc
      have hPresOld : tree.present n = true := by
        rw [insertChildNode_present, decide_eq_false hnNe, Bool.false_or] at hP'
        exact hP'
      show ((applyTreeAccess treeI next .read r active₁ .visitChildrenOfAccessed).locState n b).perm ≠ .active
      rw [applyTreeAccess_locState_out _ _ _ _ _ _ _ _ hb,
        insertChildNode_locState_of_ne _ _ _ _ _ hnNe]
      exact hSafe.foreign_ne_active n b hPresOld hAccOld hNotAncOld hNotDescOld
    | true =>
      have hNotAncNext : treeI.isAnc n next = false := by
        rw [insertChildNode_isAnc_child, decide_eq_false hnNe, Bool.false_or]
        exact hNotAncOld
      have hSome := hStepNoUB n b hP' hb
      rw [nodeAccessRelatedness_visit_foreign hNotAncNext] at hSome
      show ((applyTreeAccess treeI next .read r active₁ .visitChildrenOfAccessed).locState n b).perm ≠ .active
      rw [applyTreeAccess_locState_in _ _ _ _ _ _ _ _ hP' hb,
        nodeAccessRelatedness_visit_foreign hNotAncNext]
      exact performTransition_foreignRead_ne_active_of_isSome _ hSome
  · intro n b hP hAcc hNotAnc hNotDesc hProtCaller
    have hP' : treeI.present n = true := hP
    have hNotAnc' : treeI.isAnc n t_arg = false := hNotAnc
    have hNotDesc' : treeI.isAnc t_arg n = false := hNotDesc
    have hnNe : n ≠ next := by
      intro heq
      rw [heq, hArgAncNext] at hNotDesc'
      cases hNotDesc'
    have hNotAncOld : tree.isAnc n t_arg = false := by
      rwa [insertChildNode_isAnc_of_ne _ _ _ _ _ (Ne.symm hNe) hnNe] at hNotAnc'
    have hNotDescOld : tree.isAnc t_arg n = false := by
      rwa [insertChildNode_isAnc_of_ne _ _ _ _ _ hnNe (Ne.symm hNe)] at hNotDesc'
    have hProtCallerI : treeI.isTagProtected n activeCaller = true := hProtCaller
    cases hb : r.contains b with
    | false =>
      have hAccOld : (tree.locState t_arg b).accessed = true := by
        change ((applyTreeAccess treeI next .read r active₁ .visitChildrenOfAccessed).locState t_arg b).accessed = true at hAcc
        rw [applyTreeAccess_locState_out _ _ _ _ _ _ _ _ hb,
          insertChildNode_locState_of_ne _ _ _ _ _ (Ne.symm hNe)] at hAcc
        exact hAcc
      have hPresOld : tree.present n = true := by
        rw [insertChildNode_present, decide_eq_false hnNe, Bool.false_or] at hP'
        exact hP'
      have hProtOld : tree.isTagProtected n activeCaller = true := by
        rwa [insertChildNode_isTagProtected_of_ne _ _ _ _ _ hnNe] at hProtCallerI
      show ((applyTreeAccess treeI next .read r active₁ .visitChildrenOfAccessed).locState n b).perm ≠
        .reservedFrz false
      rw [applyTreeAccess_locState_out _ _ _ _ _ _ _ _ hb,
        insertChildNode_locState_of_ne _ _ _ _ _ hnNe]
      exact hSafe.outlive_conflicted n b hPresOld hAccOld hNotAncOld hNotDescOld hProtOld
    | true =>
      have hNotAncNext : treeI.isAnc n next = false := by
        rw [insertChildNode_isAnc_child, decide_eq_false hnNe, Bool.false_or]
        exact hNotAncOld
      have hProt₁ : treeI.isTagProtected n active₁ = true :=
        isTagProtected_insert_of_caller hProtCallerI
      have hSome := hStepNoUB n b hP' hb
      rw [nodeAccessRelatedness_visit_foreign hNotAncNext, hProt₁] at hSome
      show ((applyTreeAccess treeI next .read r active₁ .visitChildrenOfAccessed).locState n b).perm ≠
        .reservedFrz false
      rw [applyTreeAccess_locState_in _ _ _ _ _ _ _ _ hP' hb,
        nodeAccessRelatedness_visit_foreign hNotAncNext, hProt₁]
      exact performTransition_foreignRead_protected_ne_unconflicted_of_isSome hSome

/-- Step-by-step UB-freedom of `applyFootprint`. -/
def ApplyFootprintNoUB (t_arg : BorTag) (active : ActiveProtectors) :
    BorrowTree → BorTag → List (ByteRange × Mutability) → Prop
  | _, _, [] => True
  | tree, next, (r, m) :: rest =>
    TreeAccessNoUB (insertChildNode tree t_arg next none (initPermOf m)) next .read r active
        .visitChildrenOfAccessed ∧
      ApplyFootprintNoUB t_arg active (retagChild tree t_arg next none (initPermOf m) r active)
        (next + 1) rest

/-- Pre-release UB-freedom of a `TrustedFnSpec` call (`FnEntry` retag plus all
`reborrowFootprint` retags). -/
def TrustedFnSpec.NoUB (spec : TrustedFnSpec) (tree₀ : BorrowTree)
    (activeCaller : ActiveProtectors) (t_parent t_arg : BorTag) (callId : CallId) : Prop :=
  let active₁ := insertActiveProtector activeCaller callId
  TreeAccessNoUB (insertChildNode tree₀ t_parent t_arg (some (.strong callId)) (.reservedFrz false))
      t_arg .read spec.argRange active₁ .visitChildrenOfAccessed ∧
    ApplyFootprintNoUB t_arg active₁
      (retagChild tree₀ t_parent t_arg (some (.strong callId)) (.reservedFrz false) spec.argRange active₁)
      (t_arg + 1) spec.reborrowFootprint

theorem applyFootprint_preserves_readReleaseSafe {t_arg : BorTag}
    {activeCaller : ActiveProtectors} {callId : CallId} :
    ∀ (fps : List (ByteRange × Mutability)) (tree : BorrowTree) (next : BorTag),
      t_arg < next →
      ReadReleaseSafe tree t_arg activeCaller →
      ApplyFootprintNoUB t_arg (insertActiveProtector activeCaller callId) tree next fps →
      ReadReleaseSafe
        (applyFootprint t_arg (insertActiveProtector activeCaller callId) tree next fps).1
        t_arg activeCaller
  | [], _, _, _, hSafe, _ => hSafe
  | (r, m) :: rest, tree, next, hlt, hSafe, ⟨hStep, hRest⟩ =>
    applyFootprint_preserves_readReleaseSafe rest
      (retagChild tree t_arg next none (initPermOf m) r (insertActiveProtector activeCaller callId))
      (next + 1) (Nat.lt_succ_of_lt hlt)
      (readReleaseSafe_retagChild hSafe (Nat.ne_of_gt hlt) hStep) hRest

/-- **Mechanized LIFO discharge of `applyReleaseProtector_read_latchEquiv` for
every UB-free `TrustedFnSpec` call**: for *any* `BorrowTree` `tree₀`, *any*
outliving caller protector set `activeCaller` (`activeCaller callId = false`),
and *any* `spec : TrustedFnSpec` whose `FnEntry` and `reborrowFootprint` retags
are UB-free (`spec.NoUB`), Miri's two-stage `spec.run` and the live stage-2-only
`spec.runStage2Only` produce `LatchEquiv` post-call trees (resolving Round A3's
unmechanized LIFO conjecture for non-activating reborrow specs). -/
theorem trustedFnSpec_run_latchEquiv_stage2Only (spec : TrustedFnSpec) (tree₀ : BorrowTree)
    (activeCaller : ActiveProtectors) (t_parent t_arg : BorTag) (callId : CallId)
    (hCallFresh : activeCaller callId = false)
    (hNoUB : spec.NoUB tree₀ activeCaller t_parent t_arg callId) :
    LatchEquiv
      (spec.run tree₀ activeCaller t_parent t_arg callId).tree
      (spec.runStage2Only tree₀ activeCaller t_parent t_arg callId).tree
      (spec.run tree₀ activeCaller t_parent t_arg callId).active := by
  obtain ⟨hEntry, hFp⟩ := hNoUB
  have hSafe := applyFootprint_preserves_readReleaseSafe spec.reborrowFootprint _ (t_arg + 1)
    (Nat.lt_succ_self t_arg) (readReleaseSafe_of_fnEntry hEntry) hFp
  show LatchEquiv (applyReleaseProtector _ t_arg _) _
    (removeActiveProtector (insertActiveProtector activeCaller callId) callId)
  rw [removeActiveProtector_insert hCallFresh]
  exact applyReleaseProtector_read_latchEquiv
    (fun b _ => hSafe.arg_ne_active b)
    hSafe.local_acc hSafe.foreign_ne_active hSafe.outlive_conflicted

/-- **Observational equivalence of `TrustedFnSpec.run` and `TrustedFnSpec.runStage2Only`
across all post-return accesses**: every subsequent read or write has the identical
`TreeAccessNoUB` verdict under Miri's two-stage release and under stage-2-only
`restoreCallerProtectors`. -/
theorem trustedFnSpec_run_stage2Only_same_verdicts (spec : TrustedFnSpec) (tree₀ : BorrowTree)
    (activeCaller : ActiveProtectors) (t_parent t_arg : BorTag) (callId : CallId)
    (hCallFresh : activeCaller callId = false)
    (hNoUB : spec.NoUB tree₀ activeCaller t_parent t_arg callId)
    (start : BorTag) (kind : AccessKind) (range : ByteRange) (mode : ChildrenVisitMode) :
    TreeAccessNoUB (spec.run tree₀ activeCaller t_parent t_arg callId).tree start kind range
        (spec.run tree₀ activeCaller t_parent t_arg callId).active mode ↔
      TreeAccessNoUB (spec.runStage2Only tree₀ activeCaller t_parent t_arg callId).tree start kind range
        (spec.runStage2Only tree₀ activeCaller t_parent t_arg callId).active mode :=
  (trustedFnSpec_run_latchEquiv_stage2Only spec tree₀ activeCaller t_parent t_arg callId
    hCallFresh hNoUB).noUB_iff start kind range mode

theorem performTransition_localRead_ne_disabled_of_isSome (prot : Bool) {st : LocationState}
    (h : (performTransition .read .localAccess prot st).isSome = true) :
    (match performTransition .read .localAccess prot st with | some st' => st' | none => st).perm ≠
      .disabled := by
  rcases st with ⟨(_ | _) | _ | _ | _ | _, _ | _⟩ <;> cases prot <;> first | decide | cases h

theorem performTransition_localRead_isSome_of_ne_disabled (prot : Bool) {st : LocationState}
    (h : st.perm ≠ .disabled) : (performTransition .read .localAccess prot st).isSome = true := by
  rcases st with ⟨(_ | _) | _ | _ | _ | _, _ | _⟩ <;> cases prot <;> first | rfl | exact absurd rfl h

/-- Foreign reads are UB-idempotent: a location that survived a foreign read survives
another one under the same protector status. -/
theorem performTransition_foreignRead_isSome_idem (prot : Bool) {st : LocationState}
    (h : (performTransition .read .foreignAccess prot st).isSome = true) :
    (performTransition .read .foreignAccess prot
      (match performTransition .read .foreignAccess prot st with
        | some st' => st' | none => st)).isSome = true := by
  rcases st with ⟨(_ | _) | _ | _ | _ | _, _ | _⟩ <;> cases prot <;> first | rfl | cases h

/-- Release-read UB-freedom invariant (Round A4): wherever `t_arg` is accessed, its
ancestors are not `Disabled` and every foreign non-descendant tag survives a foreign read
under the call's protector set `active₁`. -/
structure ReleaseReadable (tree : BorrowTree) (t_arg : BorTag) (active₁ : ActiveProtectors) :
    Prop where
  local_ne_disabled : ∀ n b, tree.present n = true → (tree.locState t_arg b).accessed = true →
    tree.isAnc n t_arg = true → (tree.locState n b).perm ≠ .disabled
  foreign_readable : ∀ n b, tree.present n = true → (tree.locState t_arg b).accessed = true →
    tree.isAnc n t_arg = false → tree.isAnc t_arg n = false →
    (performTransition .read .foreignAccess (tree.isTagProtected n active₁)
      (tree.locState n b)).isSome = true

theorem releaseReadable_of_fnEntry {tree₀ : BorrowTree} {t_parent t_arg : BorTag}
    {argRange : ByteRange} {activeCaller : ActiveProtectors} {callId : CallId}
    (hEntryNoUB : TreeAccessNoUB
      (insertChildNode tree₀ t_parent t_arg (some (.strong callId)) (.reservedFrz false))
      t_arg .read argRange (insertActiveProtector activeCaller callId) .visitChildrenOfAccessed) :
    ReleaseReadable
      (retagChild tree₀ t_parent t_arg (some (.strong callId)) (.reservedFrz false) argRange
        (insertActiveProtector activeCaller callId))
      t_arg (insertActiveProtector activeCaller callId) := by
  let active₁ := insertActiveProtector activeCaller callId
  let treeI := insertChildNode tree₀ t_parent t_arg (some (.strong callId)) (.reservedFrz false)
  have hAccIn : ∀ b, ((retagChild tree₀ t_parent t_arg (some (.strong callId)) (.reservedFrz false)
      argRange active₁).locState t_arg b).accessed = true → argRange.contains b = true := by
    intro b hAcc
    cases hb : argRange.contains b with
    | true => rfl
    | false =>
      rw [retagChild_locState_out _ _ _ _ _ _ _ _ _ hb, insertChildNode_locState_child] at hAcc
      cases hAcc
  refine ⟨?_, ?_⟩
  · intro n b hP hAcc hAnc
    have hb := hAccIn b hAcc
    have hP' : treeI.present n = true := hP
    have hAnc' : treeI.isAnc n t_arg = true := hAnc
    have hSome := hEntryNoUB n b hP' hb
    rw [nodeAccessRelatedness_anc hAnc'] at hSome
    show ((applyTreeAccess treeI t_arg .read argRange active₁ .visitChildrenOfAccessed).locState n b).perm ≠
      .disabled
    rw [applyTreeAccess_locState_in _ _ _ _ _ _ _ _ hP' hb, nodeAccessRelatedness_anc hAnc']
    exact performTransition_localRead_ne_disabled_of_isSome _ hSome
  · intro n b hP hAcc hNotAnc _
    have hb := hAccIn b hAcc
    have hP' : treeI.present n = true := hP
    have hNotAnc' : treeI.isAnc n t_arg = false := hNotAnc
    have hSome := hEntryNoUB n b hP' hb
    rw [nodeAccessRelatedness_visit_foreign hNotAnc'] at hSome
    show (performTransition .read .foreignAccess (treeI.isTagProtected n active₁)
      ((applyTreeAccess treeI t_arg .read argRange active₁ .visitChildrenOfAccessed).locState n b)).isSome =
      true
    rw [applyTreeAccess_locState_in _ _ _ _ _ _ _ _ hP' hb, nodeAccessRelatedness_visit_foreign hNotAnc']
    exact performTransition_foreignRead_isSome_idem _ hSome

theorem releaseReadable_retagChild {tree : BorrowTree} {t_arg next : BorTag}
    {m : Mutability} {r : ByteRange} {active₁ : ActiveProtectors}
    (hInv : ReleaseReadable tree t_arg active₁) (hArgRefl : tree.isAnc t_arg t_arg = true)
    (hNe : next ≠ t_arg)
    (hStepNoUB : TreeAccessNoUB (insertChildNode tree t_arg next none (initPermOf m))
      next .read r active₁ .visitChildrenOfAccessed) :
    ReleaseReadable (retagChild tree t_arg next none (initPermOf m) r active₁) t_arg active₁ := by
  let treeI := insertChildNode tree t_arg next none (initPermOf m)
  have hArgAncNext : treeI.isAnc t_arg next = true := by
    rw [insertChildNode_isAnc_child, hArgRefl, Bool.or_true]
  have hNextNotAncArg : treeI.isAnc next t_arg = false :=
    insertChildNode_isAnc_from_child _ _ _ _ _ (Ne.symm hNe)
  have hAccOld : ∀ b, r.contains b = false →
      ((retagChild tree t_arg next none (initPermOf m) r active₁).locState t_arg b).accessed = true →
      (tree.locState t_arg b).accessed = true := by
    intro b hb hAcc
    change ((applyTreeAccess treeI next .read r active₁ .visitChildrenOfAccessed).locState t_arg b).accessed =
      true at hAcc
    rw [applyTreeAccess_locState_out _ _ _ _ _ _ _ _ hb,
      insertChildNode_locState_of_ne _ _ _ _ _ (Ne.symm hNe)] at hAcc
    exact hAcc
  refine ⟨?_, ?_⟩
  · intro n b hP hAcc hAnc
    have hP' : treeI.present n = true := hP
    have hAnc' : treeI.isAnc n t_arg = true := hAnc
    have hnNe : n ≠ next := by
      intro heq
      rw [heq, hNextNotAncArg] at hAnc'
      cases hAnc'
    have hAncOld : tree.isAnc n t_arg = true := by
      rwa [insertChildNode_isAnc_of_ne _ _ _ _ _ (Ne.symm hNe) hnNe] at hAnc'
    cases hb : r.contains b with
    | false =>
      have hPresOld : tree.present n = true := by
        rw [insertChildNode_present, decide_eq_false hnNe, Bool.false_or] at hP'
        exact hP'
      show ((applyTreeAccess treeI next .read r active₁ .visitChildrenOfAccessed).locState n b).perm ≠
        .disabled
      rw [applyTreeAccess_locState_out _ _ _ _ _ _ _ _ hb, insertChildNode_locState_of_ne _ _ _ _ _ hnNe]
      exact hInv.local_ne_disabled n b hPresOld (hAccOld b hb hAcc) hAncOld
    | true =>
      have hAncNext : treeI.isAnc n next = true := by
        rw [insertChildNode_isAnc_child, hAncOld, Bool.or_true]
      have hSome := hStepNoUB n b hP' hb
      rw [nodeAccessRelatedness_anc hAncNext] at hSome
      show ((applyTreeAccess treeI next .read r active₁ .visitChildrenOfAccessed).locState n b).perm ≠
        .disabled
      rw [applyTreeAccess_locState_in _ _ _ _ _ _ _ _ hP' hb, nodeAccessRelatedness_anc hAncNext]
      exact performTransition_localRead_ne_disabled_of_isSome _ hSome
  · intro n b hP hAcc hNotAnc hNotDesc
    have hP' : treeI.present n = true := hP
    have hNotAnc' : treeI.isAnc n t_arg = false := hNotAnc
    have hNotDesc' : treeI.isAnc t_arg n = false := hNotDesc
    have hnNe : n ≠ next := by
      intro heq
      rw [heq, hArgAncNext] at hNotDesc'
      cases hNotDesc'
    have hNotAncOld : tree.isAnc n t_arg = false := by
      rwa [insertChildNode_isAnc_of_ne _ _ _ _ _ (Ne.symm hNe) hnNe] at hNotAnc'
    have hNotDescOld : tree.isAnc t_arg n = false := by
      rwa [insertChildNode_isAnc_of_ne _ _ _ _ _ hnNe (Ne.symm hNe)] at hNotDesc'
    have hProtEq : treeI.isTagProtected n active₁ = tree.isTagProtected n active₁ :=
      insertChildNode_isTagProtected_of_ne _ _ _ _ _ hnNe active₁
    cases hb : r.contains b with
    | false =>
      have hPresOld : tree.present n = true := by
        rw [insertChildNode_present, decide_eq_false hnNe, Bool.false_or] at hP'
        exact hP'
      show (performTransition .read .foreignAccess (treeI.isTagProtected n active₁)
        ((applyTreeAccess treeI next .read r active₁ .visitChildrenOfAccessed).locState n b)).isSome =
        true
      rw [applyTreeAccess_locState_out _ _ _ _ _ _ _ _ hb, insertChildNode_locState_of_ne _ _ _ _ _ hnNe,
        hProtEq]
      exact hInv.foreign_readable n b hPresOld (hAccOld b hb hAcc) hNotAncOld hNotDescOld
    | true =>
      have hNotAncNext : treeI.isAnc n next = false := by
        rw [insertChildNode_isAnc_child, decide_eq_false hnNe, Bool.false_or]
        exact hNotAncOld
      have hSome := hStepNoUB n b hP' hb
      rw [nodeAccessRelatedness_visit_foreign hNotAncNext] at hSome
      show (performTransition .read .foreignAccess (treeI.isTagProtected n active₁)
        ((applyTreeAccess treeI next .read r active₁ .visitChildrenOfAccessed).locState n b)).isSome =
        true
      rw [applyTreeAccess_locState_in _ _ _ _ _ _ _ _ hP' hb,
        nodeAccessRelatedness_visit_foreign hNotAncNext]
      exact performTransition_foreignRead_isSome_idem _ hSome

theorem applyFootprint_preserves_releaseReadable {t_arg : BorTag} {active₁ : ActiveProtectors} :
    ∀ (fps : List (ByteRange × Mutability)) (tree : BorrowTree) (next : BorTag),
      t_arg < next → tree.isAnc t_arg t_arg = true →
      ReleaseReadable tree t_arg active₁ →
      ApplyFootprintNoUB t_arg active₁ tree next fps →
      ReleaseReadable (applyFootprint t_arg active₁ tree next fps).1 t_arg active₁
  | [], _, _, _, _, hInv, _ => hInv
  | (r, m) :: rest, tree, next, hlt, hRefl, hInv, ⟨hStep, hRest⟩ =>
    applyFootprint_preserves_releaseReadable rest
      (retagChild tree t_arg next none (initPermOf m) r active₁) (next + 1) (Nat.lt_succ_of_lt hlt)
      (by
        show (insertChildNode tree t_arg next none (initPermOf m)).isAnc t_arg t_arg = true
        rw [insertChildNode_isAnc_of_ne _ _ _ _ _ (Ne.symm (Nat.ne_of_gt hlt))
          (Ne.symm (Nat.ne_of_gt hlt))]
        exact hRefl)
      (releaseReadable_retagChild hInv hRefl (Nat.ne_of_gt hlt) hStep) hRest

/-- The two invariants together make a stage-1 release UB-free. -/
theorem releaseProtectorNoUB_of_readReleaseSafe {tree : BorrowTree} {t_arg : BorTag}
    {activeCaller active₁ : ActiveProtectors} (hSafe : ReadReleaseSafe tree t_arg activeCaller)
    (hInv : ReleaseReadable tree t_arg active₁) : releaseProtectorNoUB tree t_arg active₁ := by
  intro n b hP hA
  rw [Permission.associatedAccess_of_ne_active (hSafe.arg_ne_active b)]
  cases hR : nodeAccessRelatedness tree t_arg .skipChildrenOfAccessed n with
  | none => trivial
  | some rel =>
    cases rel with
    | localAccess =>
      exact performTransition_localRead_isSome_of_ne_disabled _
        (hInv.local_ne_disabled n b hP hA (nodeAccessRelatedness_isAnc_of_local hR))
    | foreignAccess =>
      exact hInv.foreign_readable n b hP hA (nodeAccessRelatedness_not_isAnc_of_foreign hR)
        (nodeAccessRelatedness_skip_not_desc_of_foreign hR)

/-- **The stage-1 release of every UB-free `TrustedFnSpec` call is itself UB-free**
(Round A4).  Without this, `trustedFnSpec_run_latchEquiv_stage2Only` would leave open that
Miri's two-stage return reports UB at the release itself while the stage-2-only return
continues; with it, the two returns agree on every step, including the return. -/
theorem trustedFnSpec_release_noUB (spec : TrustedFnSpec) (tree₀ : BorrowTree)
    (activeCaller : ActiveProtectors) (t_parent t_arg : BorTag) (callId : CallId)
    (hNoUB : spec.NoUB tree₀ activeCaller t_parent t_arg callId) :
    releaseProtectorNoUB
      (applyFootprint t_arg (insertActiveProtector activeCaller callId)
        (retagChild tree₀ t_parent t_arg (some (.strong callId)) (.reservedFrz false) spec.argRange
          (insertActiveProtector activeCaller callId))
        (t_arg + 1) spec.reborrowFootprint).1
      t_arg (insertActiveProtector activeCaller callId) := by
  obtain ⟨hEntry, hFp⟩ := hNoUB
  have hSafe0 := readReleaseSafe_of_fnEntry hEntry
  exact releaseProtectorNoUB_of_readReleaseSafe
    (applyFootprint_preserves_readReleaseSafe spec.reborrowFootprint _ (t_arg + 1)
      (Nat.lt_succ_self t_arg) hSafe0 hFp)
    (applyFootprint_preserves_releaseReadable spec.reborrowFootprint _ (t_arg + 1)
      (Nat.lt_succ_self t_arg) hSafe0.arg_refl (releaseReadable_of_fnEntry hEntry) hFp)

/-- **Concrete MIR callee execution under the live stage-2-only return path**
(`restoreCallerProtectors`, without stage-1 `applyReleaseProtector`). -/
inductive ConcreteCallStage2Only (tree₀ : BorrowTree) (activeCaller : ActiveProtectors)
    (t_parent t_arg : BorTag) (argRange : ByteRange) (callId : CallId) (body : List CalleeOp)
    (retRegs : List Nat) : CallOutcome → Prop
  | mk {stEnd : CalleeState} {rets : List BorTag}
      (hfresh : tree₀.present t_arg = false)
      (hentry : TreeAccessNoUB (insertChildNode tree₀ t_parent t_arg (some (.strong callId))
        (.reservedFrz false)) t_arg .read argRange (insertActiveProtector activeCaller callId)
        .visitChildrenOfAccessed)
      (hrun : CalleeRun (insertActiveProtector activeCaller callId)
        (calleeEntryState tree₀ activeCaller t_parent t_arg argRange callId) body stEnd)
      (hrets : collectRegs stEnd.regs retRegs = some rets) :
      ConcreteCallStage2Only tree₀ activeCaller t_parent t_arg argRange callId body retRegs
        ⟨stEnd.tree, removeActiveProtector (insertActiveProtector activeCaller callId) callId, rets⟩

/-- **Stage-2-only concrete/declarative equivalence and `LatchEquiv` to two-stage
`ConcreteCall`**: for both `split_at_mut` and `get_mut`, `ConcreteCallStage2Only`
succeeds with `TrustedFnSpec.runStage2Only`, determines it uniquely, and is
`LatchEquiv` to Miri's two-stage `TrustedFnSpec.run`. -/
theorem trustedSpec_stage2Only_reborrow_equivalence {tree0 : BorrowTree} {t_parent t_arg : BorTag}
    {base mid len off sz : Nat} {activeCaller : ActiveProtectors} {callId : CallId}
    (hmid : mid ≤ len) (hsub : base ≤ off ∧ off + sz ≤ base + len)
    (hPerm0 : HasUniqueWritePerm tree0 t_parent (wholeRange base len) activeCaller)
    (hFresh : ∀ t, t_arg ≤ t → tree0.present t = false)
    (hFreshCallId : ∀ n, tree0.present n = true → ∀ p, tree0.protector n = some p → p.callId ≠ callId)
    (hCallFresh : activeCaller callId = false) :
    let splitS2 := (splitAtMutSpec base mid len).runStage2Only tree0 activeCaller t_parent t_arg callId
    let splitS12 := (splitAtMutSpec base mid len).run tree0 activeCaller t_parent t_arg callId
    let getS2 := (getMutSpec (wholeRange base len) off sz).runStage2Only tree0 activeCaller t_parent t_arg callId
    let getS12 := (getMutSpec (wholeRange base len) off sz).run tree0 activeCaller t_parent t_arg callId
    (ConcreteCallStage2Only tree0 activeCaller t_parent t_arg (wholeRange base len) callId
        (splitAtMutBody base mid len) [2, 3] splitS2 ∧
      ∀ out, ConcreteCallStage2Only tree0 activeCaller t_parent t_arg (wholeRange base len) callId
        (splitAtMutBody base mid len) [2, 3] out → out = splitS2) ∧
    (ConcreteCallStage2Only tree0 activeCaller t_parent t_arg (wholeRange base len) callId
        (getMutBody off sz) [1] getS2 ∧
      ∀ out, ConcreteCallStage2Only tree0 activeCaller t_parent t_arg (wholeRange base len) callId
        (getMutBody off sz) [1] out → out = getS2) ∧
    LatchEquiv splitS12.tree splitS2.tree splitS12.active ∧
    LatchEquiv getS12.tree getS2.tree getS12.active := by
  intro splitS2 splitS12 getS2 getS12
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
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩,
    trustedFnSpec_run_latchEquiv_stage2Only (splitAtMutSpec base mid len) tree0 activeCaller
      t_parent t_arg callId hCallFresh ⟨hEntryNoUB, hNoUBL, hNoUBR, trivial⟩,
    trustedFnSpec_run_latchEquiv_stage2Only (getMutSpec (wholeRange base len) off sz) tree0
      activeCaller t_parent t_arg callId hCallFresh ⟨hEntryNoUB, hNoUBG, trivial⟩⟩
  · exact ConcreteCallStage2Only.mk hFreshArg hEntryNoUB
      (CalleeRun.cons (CalleeStep.assertLe hmid)
        (CalleeRun.cons (CalleeStep.rawPtr rfl (show (1 : Nat) < 4 from by decide))
          (CalleeRun.cons (CalleeStep.reborrow rfl (show (2 : Nat) < 4 from by decide) hFreshL1 hNoUBL)
            (CalleeRun.cons (CalleeStep.reborrow rfl (show (3 : Nat) < 4 from by decide) hFreshR2 hNoUBR)
              CalleeRun.nil))))
      rfl
  · intro out hout
    cases hout with
    | mk _ _ hrun hrets =>
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
  · exact ConcreteCallStage2Only.mk hFreshArg hEntryNoUB
      (CalleeRun.cons (CalleeStep.reborrow rfl (show (1 : Nat) < 4 from by decide) hFreshL1 hNoUBG)
        CalleeRun.nil) rfl
  · intro out hout
    cases hout with
    | mk _ _ hrun hrets =>
      cases hrun with
      | cons h1 hr1 =>
        cases h1 with
        | reborrow hsrc1 _ _ _ =>
          simp only [calleeEntryState, List.getElem?_cons_zero, Option.some.injEq] at hsrc1
          subst hsrc1
          cases hr1 with
          | nil =>
            simp only [calleeEntryState, collectRegs, List.set_cons_succ,
              List.set_cons_zero, List.getElem?_cons_succ, List.getElem?_cons_zero,
              Option.some.injEq] at hrets
            subst hrets
            rfl

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

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.stepCfg_infiniteLoop' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms stepCfg_infiniteLoop

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.evalFuel_infiniteLoop_outOfFuel' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms evalFuel_infiniteLoop_outOfFuel

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.not_wpConverges_infiniteLoop' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms not_wpConverges_infiniteLoop

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.runUntilTarget_infiniteLoop_unreached' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms runUntilTarget_infiniteLoop_unreached

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.runToTarget_infiniteLoop_outOfFuel' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms runToTarget_infiniteLoop_outOfFuel

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.stepMirFn_of_mirStep_cont' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stepMirFn_of_mirStep_cont

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.stepMirFn_of_mirStep_done' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stepMirFn_of_mirStep_done

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.mirStepsConverges_of_mirStep_cont' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mirStepsConverges_of_mirStep_cont

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.mirStepsConverges_of_stepsTo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mirStepsConverges_of_stepsTo

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.mirWpConverges_of_mirStep_cont' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mirWpConverges_of_mirStep_cont

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

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.runMirToBlock_countToN_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runMirToBlock_countToN_entry

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.runMirToBlock_countToN_iter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runMirToBlock_countToN_iter

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.runMirToBlock_countToN_exit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runMirToBlock_countToN_exit

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.live_countToN_mirWpConverges_all_n' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms live_countToN_mirWpConverges_all_n

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.live_runMirToBlock_stationary_at_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms live_runMirToBlock_stationary_at_target

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.live_runMirToBlock_step_of_not_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms live_runMirToBlock_step_of_not_target

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.runUntilTarget_reached_iff_live_runMirToBlock' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runUntilTarget_reached_iff_live_runMirToBlock

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.runMirToBlock_reached_iff_step_and_live' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runMirToBlock_reached_iff_step_and_live

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.runUntilTarget_not_reached_iff_live_runMirToBlock_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runUntilTarget_not_reached_iff_live_runMirToBlock_none

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.live_runMirToBlock_conflates_halt_stuck_outOfFuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms live_runMirToBlock_conflates_halt_stuck_outOfFuel

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

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.forcePureEnvD_eq_take_append_replicate' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms forcePureEnvD_eq_take_append_replicate

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.forcePureEnv_ne_self_of_length_ne' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms forcePureEnv_ne_self_of_length_ne

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.forcePureEnv_eq_self_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms forcePureEnv_eq_self_iff

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

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.setSpine?_eq_some_set' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms setSpine?_eq_some_set

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.setSpine?_eq_forceSpine?_set' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms setSpine?_eq_forceSpine?_set

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applySlotUpdatesForced_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applySlotUpdatesForced_eq

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applySlotUpdates_eq_of_forced' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applySlotUpdates_eq_of_forced

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.length_applySlotUpdates' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms length_applySlotUpdates

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.setSpine?_eq_some_forcePureEnv_set' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms setSpine?_eq_some_forcePureEnv_set

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applySlotUpdatesForced_eq_forcePureEnv' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applySlotUpdatesForced_eq_forcePureEnv

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

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.liveSet?_eq_setSpine?' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms liveSet?_eq_setSpine?

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applySlotUpdatesLive?_eq_forced' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applySlotUpdatesLive?_eq_forced

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applySlotUpdatesLive?_oob' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applySlotUpdatesLive?_oob

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applySlotUpdatesTwoPass_eq_live?' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applySlotUpdatesTwoPass_eq_live?

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applySlotUpdates_eq_of_twoPass' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applySlotUpdates_eq_of_twoPass

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.setPureEnvSlot?_eq_set?' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms setPureEnvSlot?_eq_set?

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.setPureEnvSlot?_eq_live_bind_forcePureEnv?' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms setPureEnvSlot?_eq_live_bind_forcePureEnv?

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.evalPureStmtNorm_eq_bind_forceSpine?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalPureStmtNorm_eq_bind_forceSpine?

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.setSpineChecked?_eq_live_set?' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms setSpineChecked?_eq_live_set?

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.setSpineChecked?_eq_live_bind_forcePureEnv?' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms setSpineChecked?_eq_live_bind_forcePureEnv?

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.setSpineChecked?_symbolic_slot_rfl' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms setSpineChecked?_symbolic_slot_rfl

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applySlotUpdatesChecked_eq_live?' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applySlotUpdatesChecked_eq_live?

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applySlotUpdates_eq_of_checked' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applySlotUpdates_eq_of_checked

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applySlotUpdates_eq_of_live?' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applySlotUpdates_eq_of_live?

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.set?_of_setSpineChecked?' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms set?_of_setSpineChecked?

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.evalPureStmtNorm_assign_local_of_setSpineChecked?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalPureStmtNorm_assign_local_of_setSpineChecked?

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.evalPureStmtsN_eq_unforced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalPureStmtsN_eq_unforced

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

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.typedAt_of_canonicalAt' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms typedAt_of_canonicalAt

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.typedAt_laidOutPair_write_fst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms typedAt_laidOutPair_write_fst

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.typedAt_laidOutPair_of_fieldsValid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms typedAt_laidOutPair_of_fieldsValid

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.typedAt_laidOutPair_applyFieldWrites' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms typedAt_laidOutPair_applyFieldWrites

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.subplaceFieldLens_of_borrowSubplace_disjointOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms subplaceFieldLens_of_borrowSubplace_disjointOn

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.subplaceFieldLens_of_borrowSubplace_disjointOn_nonvacuous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms subplaceFieldLens_of_borrowSubplace_disjointOn_nonvacuous

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.fieldsTyped_of_fieldsValid' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fieldsTyped_of_fieldsValid

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.fieldsTyped_nested_init_padding_not_fieldsValid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fieldsTyped_nested_init_padding_not_fieldsValid

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.not_lawfulMutLens_fieldLens_laidOutPair_typedAt' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms not_lawfulMutLens_fieldLens_laidOutPair_typedAt

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applyFieldWrites_fieldsTyped_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyFieldWrites_fieldsTyped_spec

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

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.reborrow_return_after_parent_write_unique_write_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reborrow_return_after_parent_write_unique_write_perm

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.callee_parent_write_after_reborrow_disables_child' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms callee_parent_write_after_reborrow_disables_child

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.overlapping_reborrowFootprint_write_disables_sibling' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms overlapping_reborrowFootprint_write_disables_sibling

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.ofLiveTreeBorrowPerm?_toLiveTreeBorrowPerm' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ofLiveTreeBorrowPerm?_toLiveTreeBorrowPerm

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.toLiveTreeBorrowPerm_ofLiveTreeBorrowPerm?' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms toLiveTreeBorrowPerm_ofLiveTreeBorrowPerm?

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.liveBorrowEntryRange_contains_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms liveBorrowEntryRange_contains_iff

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.performTransition_accessed_eq_live' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms performTransition_accessed_eq_live

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.performTransition_unaccessed_eq_live' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms performTransition_unaccessed_eq_live

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.performTransition_accessed_isSome_eq_live' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms performTransition_accessed_isSome_eq_live

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.isTagProtected_eq_live' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms isTagProtected_eq_live

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.performTransition_entry_eq_live' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms performTransition_entry_eq_live

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.foreign_write_disabled_protected_noop' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms foreign_write_disabled_protected_noop

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.protected_reservedIM_foreign_fails_closed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms protected_reservedIM_foreign_fails_closed

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.hasUniqueWritePerm_remove_callId' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasUniqueWritePerm_remove_callId

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.split_at_mut_stage2Only_unique_write_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms split_at_mut_stage2Only_unique_write_perm

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.stage1_vs_stage2Only_two_arg_release_differs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stage1_vs_stage2Only_two_arg_release_differs

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.LocationState.eraseLatch_accessed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LocationState.eraseLatch_accessed

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.LocationState.eraseLatch_associatedAccess' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LocationState.eraseLatch_associatedAccess

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.LocationState.ne_active_of_eraseLatch_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LocationState.ne_active_of_eraseLatch_eq

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.performTransition_unprotected_eraseLatch' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms performTransition_unprotected_eraseLatch

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.performTransition_unprotected_isSome_eraseLatch' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms performTransition_unprotected_isSome_eraseLatch

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.eraseLatch_update_unprotected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms eraseLatch_update_unprotected

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.nodeAccessRelatedness_congr' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms nodeAccessRelatedness_congr

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.isTagProtected_congr' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms isTagProtected_congr

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applyTreeAccess_locState_absent' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applyTreeAccess_locState_absent

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applyReleaseProtector_locState_absent' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applyReleaseProtector_locState_absent

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.LatchEquiv.refl' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LatchEquiv.refl

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.LatchEquiv.of_active' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LatchEquiv.of_active

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.LatchEquiv.transition_isSome' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LatchEquiv.transition_isSome

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.LatchEquiv.noUB_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LatchEquiv.noUB_iff

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.LatchEquiv.access' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LatchEquiv.access

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.LatchEquiv.insert' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LatchEquiv.insert

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.LatchEquiv.retag' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LatchEquiv.retag

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.LatchEquiv.released_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LatchEquiv.released_eq

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.LatchEquiv.release' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LatchEquiv.release

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.LatchEquiv.releaseNoUB_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LatchEquiv.releaseNoUB_iff

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.nodeAccessRelatedness_isAnc_of_local' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms nodeAccessRelatedness_isAnc_of_local

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.nodeAccessRelatedness_not_isAnc_of_foreign' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms nodeAccessRelatedness_not_isAnc_of_foreign

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.Permission.associatedAccess_of_ne_active' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Permission.associatedAccess_of_ne_active

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.eraseLatch_update_localRead' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms eraseLatch_update_localRead

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.eraseLatch_update_foreignRead' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms eraseLatch_update_foreignRead

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.performTransition_update_accessed_mono' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms performTransition_update_accessed_mono

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.performTransition_update_read_ne_active' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms performTransition_update_read_ne_active

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applyTreeAccess_accessed_mono' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applyTreeAccess_accessed_mono

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applyTreeAccess_read_ne_active' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applyTreeAccess_read_ne_active

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.nodeAccessRelatedness_skip_not_desc_of_foreign' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms nodeAccessRelatedness_skip_not_desc_of_foreign

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applyReleaseProtector_read_eraseLatch' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applyReleaseProtector_read_eraseLatch

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.stage1_vs_stage2Only_two_arg_release_unobservable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stage1_vs_stage2Only_two_arg_release_unobservable

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.stage1_vs_stage2Only_two_arg_release_same_verdicts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stage1_vs_stage2Only_two_arg_release_same_verdicts

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.update_localRead_eq_self' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms update_localRead_eq_self

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.update_foreignRead_eq_self' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms update_foreignRead_eq_self

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applyReleaseProtector_read_latchEquiv' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applyReleaseProtector_read_latchEquiv

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applyReleaseProtector_read_same_verdicts' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applyReleaseProtector_read_same_verdicts

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.shared_reborrowFootprint_read_ok_write_ub' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms shared_reborrowFootprint_read_ok_write_ub

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.isBorrowDescendantOrSelf_refl' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms isBorrowDescendantOrSelf_refl

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.nodeAccessRelatedness_visit_eq_live_writer' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms nodeAccessRelatedness_visit_eq_live_writer

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.borrowEntryWriteConflicts_eq_live' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms borrowEntryWriteConflicts_eq_live

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.restoreCallerProtectors_eq_live' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms restoreCallerProtectors_eq_live

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.stage1_write_release_observable_ub_separation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stage1_write_release_observable_ub_separation

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.reborrow_return_after_parent_write_stage2Only_unique_write_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reborrow_return_after_parent_write_stage2Only_unique_write_perm

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.read_latchEquiv_ignores_active_descendant' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms read_latchEquiv_ignores_active_descendant

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.stage1_read_release_outliving_unconflicted_separates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stage1_read_release_outliving_unconflicted_separates

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.performTransition_localRead_accessed_of_isSome' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms performTransition_localRead_accessed_of_isSome

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.performTransition_foreignRead_ne_active_of_isSome' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms performTransition_foreignRead_ne_active_of_isSome

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.performTransition_foreignRead_protected_ne_unconflicted_of_isSome' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms performTransition_foreignRead_protected_ne_unconflicted_of_isSome

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.readReleaseSafe_of_fnEntry' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms readReleaseSafe_of_fnEntry

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.readReleaseSafe_retagChild' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms readReleaseSafe_retagChild

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applyFootprint_preserves_readReleaseSafe' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applyFootprint_preserves_readReleaseSafe

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.trustedFnSpec_run_latchEquiv_stage2Only' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trustedFnSpec_run_latchEquiv_stage2Only

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.trustedFnSpec_run_stage2Only_same_verdicts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trustedFnSpec_run_stage2Only_same_verdicts

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.performTransition_localRead_ne_disabled_of_isSome' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms performTransition_localRead_ne_disabled_of_isSome

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.performTransition_localRead_isSome_of_ne_disabled' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms performTransition_localRead_isSome_of_ne_disabled

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.performTransition_foreignRead_isSome_idem' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms performTransition_foreignRead_isSome_idem

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.releaseReadable_of_fnEntry' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms releaseReadable_of_fnEntry

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.releaseReadable_retagChild' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms releaseReadable_retagChild

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.applyFootprint_preserves_releaseReadable' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms applyFootprint_preserves_releaseReadable

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.releaseProtectorNoUB_of_readReleaseSafe' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms releaseProtectorNoUB_of_readReleaseSafe

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.trustedFnSpec_release_noUB' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms trustedFnSpec_release_noUB

/-- info: 'Anneal.FuelFreeLoopAndTypedAtLensPrototype.trustedSpec_stage2Only_reborrow_equivalence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trustedSpec_stage2Only_reborrow_equivalence

end Anneal.FuelFreeLoopAndTypedAtLensPrototype
