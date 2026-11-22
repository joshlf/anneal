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

end Workbench.Pass1.Firewall
