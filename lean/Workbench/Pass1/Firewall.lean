-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core

/-!
# WHNF and Rewrite Firewalls (`Workbench.Pass1.Firewall`)

Pass-1-portable (`prelude` + `Init.Core`, zero axioms, zero `._unsafe_rec`)
barriers that stop Lean's kernel `whnf` and tactic `rw` / `simp` traversals
from penetrating huge symbolic weakest-precondition or MIR state ASTs.

Two complementary mechanisms are provided:

1. **`Firewall tag P` (1-Field `Prop` Structure):**
   In Lean 4's C++ kernel, an `inductive` / `structure` type constructor has
   `has_value() == false`, so `is_def_eq` never delta-unfolds `Firewall tag P`
   against a mismatched head, whereas an `abbrev` or reducible `def` unfolds
   eagerly. Use `Firewall` to wrap intermediate symbolic obligations quickly.

2. **`IndexedCut` (Zero-`Prop`-Argument `@[irreducible]` Cut Pattern):**
   Even when `Firewall tag P` blocks head delta-unfolding, `P` still appears in
   the goal type's `Expr` arguments, so `rw [h]` traverses `P` searching for
   redexes (`+22–30%` overhead on 5,000-line MIR proofs). Binding a stepped
   predicate `stepPred : Nat → State → Prop` inside an `IndexedCut` (or marking
   a concrete `def myCut (k : Nat) (s : State) : Prop` `@[irreducible]` *after*
   proving its `seal`/`open`/`step` lemmas) removes the expanded `Prop` AST
   from the tactic goal completely.

3. **Goal-Directed `ite` Branch Eliminators (`ite_*_imp`, `ite_eq_*_imp`):**
   Elaborating an applied hypothesis `have h' := elim h` (or `rw [...] at h`)
   when `h : if P then T else F` forces Lean's elaborator to put `h`'s type in
   WHNF, evaluating expensive symbolic guards `P` (e.g., `15s+` on nested type
   normalization or `checkVal` evaluators). Using `revert h; refine
   ite_absurd_left_imp ... ?_; intro h` unifies `@ite` structurally against the
   goal without reducing `P`.
-/

namespace Workbench.Pass1.Firewall

/-! ## 1. Tagged 1-Field `Prop` Structure (`Firewall`) -/

structure Firewall (tag : Nat) (P : Prop) : Prop where
  val : P

theorem wrap (tag : Nat) {P : Prop} (h : P) : Firewall tag P :=
  ⟨h⟩

theorem unwrap {tag : Nat} {P : Prop} (h : Firewall tag P) : P :=
  h.val

theorem map (tag : Nat) {P Q : Prop} (f : P → Q) (h : Firewall tag P) :
    Firewall tag Q :=
  ⟨f h.val⟩

theorem map2 (tag : Nat) {P Q R : Prop} (f : P → Q → R)
    (hp : Firewall tag P) (hq : Firewall tag Q) : Firewall tag R :=
  ⟨f hp.val hq.val⟩

theorem trans_tag (tag1 tag2 : Nat) {P : Prop} (h : Firewall tag1 P) :
    Firewall tag2 P :=
  ⟨h.val⟩

/-! ## 2. Zero-`Prop`-Argument Indexed Step-Cut Combinator (`IndexedCut`) -/

/-- Wraps a state-indexed family of propositions `cutAt : Nat → σ → Prop`
without exposing expanded `Prop` bodies in the outer goal signature when `cutAt`
is bound to a top-level named definition. -/
structure IndexedCut {σ : Type u} (cutAt : Nat → σ → Prop)
    (stage : Nat) (st : σ) : Prop where
  runCut : cutAt stage st

theorem seal_cut {σ : Type u} {cutAt : Nat → σ → Prop}
    {stage : Nat} {st : σ} (h : cutAt stage st) :
    IndexedCut cutAt stage st :=
  ⟨h⟩

theorem open_cut {σ : Type u} {cutAt : Nat → σ → Prop}
    {stage : Nat} {st : σ} (h : IndexedCut cutAt stage st) :
    cutAt stage st :=
  h.runCut

theorem step_cut {σ : Type u} {cutAt : Nat → σ → Prop}
    {stage1 stage2 : Nat} {st1 st2 : σ}
    (hAdv : cutAt stage2 st2 → cutAt stage1 st1)
    (hNext : IndexedCut cutAt stage2 st2) :
    IndexedCut cutAt stage1 st1 :=
  ⟨hAdv hNext.runCut⟩

theorem finish_cut {σ : Type u} {cutAt : Nat → σ → Prop}
    {stage : Nat} {st : σ} {post : Prop}
    (hDone : cutAt stage st → post)
    (hCut : IndexedCut cutAt stage st) : post :=
  hDone hCut.runCut

/-! ## 3. Goal-Directed `ite` Branch Eliminators (No Guard WHNF Reduction) -/

/-- Goal-directed case split on `@ite Prop P inst T F` in the goal head. Use via
`revert h; refine ite_elim_imp ?_ ?_` when `P` is expensive to reduce so Lean
matches `@ite` structurally without forcing WHNF on `P`. -/
theorem ite_elim_imp {P : Prop} {inst : Decidable P} {T F G : Prop}
    (hT : P → T → G) (hF : ¬ P → F → G) : @ite Prop P inst T F → G :=
  @Decidable.casesOn P (fun d => @ite Prop P d T F → G) inst hF hT

theorem ite_true_imp {P : Prop} {inst : Decidable P} {T F G : Prop}
    (hP : P) (hT : T → G) : @ite Prop P inst T F → G :=
  ite_elim_imp (fun _ h => hT h) (fun hNP _ => False.elim (hNP hP))

theorem ite_false_imp {P : Prop} {inst : Decidable P} {T F G : Prop}
    (hNP : ¬ P) (hF : F → G) : @ite Prop P inst T F → G :=
  ite_elim_imp (fun hP _ => False.elim (hNP hP)) (fun _ h => hF h)

/-- Eliminate `@ite Prop P inst T F → G` when the `then`-branch `T` is absurd,
without reducing the guard `P`. -/
theorem ite_absurd_left_imp {P : Prop} {inst : Decidable P} {T F G : Prop}
    (hAbs : T → False) (hF : F → G) : @ite Prop P inst T F → G :=
  ite_elim_imp (fun _ h => False.elim (hAbs h)) (fun _ h => hF h)

/-- Eliminate `@ite Prop P inst T F → G` when the `else`-branch `F` is absurd,
without reducing the guard `P`. -/
theorem ite_absurd_right_imp {P : Prop} {inst : Decidable P} {T F G : Prop}
    (hT : T → G) (hAbs : F → False) : @ite Prop P inst T F → G :=
  ite_elim_imp (fun _ h => hT h) (fun _ h => False.elim (hAbs h))

/-- Value-level counterpart of `ite_elim_imp` for `@ite α P inst t f = r → G`,
useful for `Except` / `StepResult` / `Option` branch hypotheses. -/
theorem ite_eq_elim_imp {α : Type u} {P : Prop} {inst : Decidable P}
    {t f r : α} {G : Prop}
    (hT : P → t = r → G) (hF : ¬ P → f = r → G) :
    @ite α P inst t f = r → G :=
  @Decidable.casesOn P (fun d => @ite α P d t f = r → G) inst hF hT

theorem ite_eq_true_imp {α : Type u} {P : Prop} {inst : Decidable P}
    {t f r : α} {G : Prop} (hP : P) (hT : t = r → G) :
    @ite α P inst t f = r → G :=
  ite_eq_elim_imp (fun _ h => hT h) (fun hNP _ => False.elim (hNP hP))

theorem ite_eq_false_imp {α : Type u} {P : Prop} {inst : Decidable P}
    {t f r : α} {G : Prop} (hNP : ¬ P) (hF : f = r → G) :
    @ite α P inst t f = r → G :=
  ite_eq_elim_imp (fun hP _ => False.elim (hNP hP)) (fun _ h => hF h)

theorem ite_eq_absurd_left_imp {α : Type u} {P : Prop} {inst : Decidable P}
    {t f r : α} {G : Prop} (hNe : t ≠ r) (hF : f = r → G) :
    @ite α P inst t f = r → G :=
  ite_eq_elim_imp (fun _ h => False.elim (hNe h)) (fun _ h => hF h)

theorem ite_eq_absurd_right_imp {α : Type u} {P : Prop} {inst : Decidable P}
    {t f r : α} {G : Prop} (hT : t = r → G) (hNe : f ≠ r) :
    @ite α P inst t f = r → G :=
  ite_eq_elim_imp (fun _ h => hT h) (fun _ h => False.elim (hNe h))

end Workbench.Pass1.Firewall
