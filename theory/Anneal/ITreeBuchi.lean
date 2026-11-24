-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Std.Do
import Trusted
import Anneal.Refinement
import Anneal.Effect
import Anneal.ITree
import Anneal.EffectWP
import Anneal.ITreeWP

namespace Anneal.ITreeBuchi

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Anneal.Refinement
open Anneal.Effect
open Anneal.ITree
open Anneal.EffectWP
open Anneal.ITreeWP

/-!
# Shallow Büchi Temporal Specifications over Interaction Trees (`iBuchi`)

Shallowly embedded linear-time temporal modalities and Büchi acceptance over
`ITree E R` and the Dijkstra predicate-transformer calculi of `Anneal.ITreeWP`
(cf. `arXiv:2611.27553`, *Compositional Temporal Specifications for Interaction
Trees*):

- **`Always`** ($\Box$, `coinductive_fixpoint`): stateful invariance with a
  Hoare postcondition on `.ret`, characterised *exactly* as `DWLP` over the
  invariant-guarded transformer `guardInvWP` (`always_iff_dwlp_invariant`).
- **`Until`** / **`Eventually`** ($\mathcal{U}$, $\Diamond$,
  `inductive_fixpoint`): strong until and eventuality; `EventuallyStep` is the
  strict variant that needs a genuine accepting `.vis` edge (or a `.ret`).
- **`InfOften`** ($\Box\Diamond$): the nested $\nu X.\,\mu Y$ fixpoint built
  from the inner inductive transformer `buchiProgress`. It sits strictly
  between `DWP` and `DWLP`: it rejects `ITree.spin` unconditionally
  (`not_infOften_spin`) yet is satisfied by diverging `-> !` reactive loops that
  keep taking accepting edges (`buchi_diverging_loop_rule`), which `DWP` can
  never verify (`not_dwp_diverging_loop`).
- **`BuchiSpec`** / **`BuchiSat`**: a shallow Büchi monitor synchronised with the
  program through `BuchiSpec.monitorWP`, unifying `Always` safety, `InfOften`
  liveness and a terminal Hoare postcondition.
- **`iterChain`**: the finite-unfolding $\omega$-chain of `ITree.iter`, its
  convergence in the projective `CofixA` order (`ofITree_iterChain`), and the
  safety ($\bigwedge_n$) versus eventuality ($\bigvee_n$) continuity laws.

The continuity laws are stated under the one-step continuity classes
`DownContinuous` / `UpContinuous`. Neither can be dropped: `not_always_iter_continuity_angelic` and
`not_dwp_iter_continuity_unbounded` exhibit unboundedly angelic and unboundedly
demonic transformers for which the corresponding law is false.
-/

universe u

/-! ## 0. Observation Inversion Helpers -/

private theorem eq_ret_of_observe {E : Effect.{u}} {R : Type u}
    {t : ITree E R} {r : R} (h : t.observe = .ret r) : t = .ret r := by
  rw [← ITree.fold_observe t, h]; rfl

private theorem eq_tau_of_observe {E : Effect.{u}} {R : Type u}
    {t t' : ITree E R} (h : t.observe = .tau t') : t = .tau t' := by
  rw [← ITree.fold_observe t, h]; rfl

private theorem eq_vis_of_observe {E : Effect.{u}} {R : Type u}
    {t : ITree E R} {i : E.I} {k : E.O i → ITree E R}
    (h : t.observe = .vis i k) : t = .vis i k := by
  rw [← ITree.fold_observe t, h]; rfl

/-! ## 1. Stateful Invariance `Always` ($\Box$) -/

section Always

variable {S : Type u} {E : Effect.{u}} {R : Type u}

private def alwaysAux (ewp : StateEffectWP S E) (Inv : S → Prop)
    (Q : R → S → Prop) (t : ITree E R) (s : S) : Prop :=
  Inv s ∧
    match t.observe with
    | .ret r => Q r s
    | .tau t' => alwaysAux ewp Inv Q t' s
    | .vis i k => ewp.wp i (fun o s' => alwaysAux ewp Inv Q (k o) s') s
coinductive_fixpoint

/--
Coinductive stateful invariance ($\Box$): `Inv` holds at every configuration
`(x, s₀)` reachable from `(t, s)` along `ewp`, and `Q r s₀` holds at every
`.ret r`. Silent divergence is admitted (`Always.spin`).
-/
def Always (ewp : StateEffectWP S E) (Inv : S → Prop) (Q : R → S → Prop)
    (t : ITree E R) (s : S) : Prop :=
  alwaysAux ewp Inv Q t s

theorem Always.unfold_eq (ewp : StateEffectWP S E) (Inv : S → Prop)
    (Q : R → S → Prop) (t : ITree E R) (s : S) :
    Always ewp Inv Q t s =
      (Inv s ∧
        match t.observe with
        | .ret r => Q r s
        | .tau t' => Always ewp Inv Q t' s
        | .vis i k => ewp.wp i (fun o s' => Always ewp Inv Q (k o) s') s) :=
  alwaysAux.eq_def ewp Inv Q t s

/-- Park coinduction principle for `Always`. -/
theorem Always.coinduct {ewp : StateEffectWP S E} {Inv : S → Prop}
    {Q : R → S → Prop} (X : ITree E R → S → Prop)
    (h_step : ∀ x s₀, X x s₀ →
      Inv s₀ ∧
        match x.observe with
        | .ret r => Q r s₀
        | .tau x' => X x' s₀
        | .vis i k => ewp.wp i (fun o s' => X (k o) s') s₀)
    {t : ITree E R} {s : S} (h_init : X t s) :
    Always ewp Inv Q t s :=
  alwaysAux.coinduct ewp Inv Q X h_step t s h_init

/-- The invariant holds at the current configuration. -/
theorem Always.inv {ewp : StateEffectWP S E} {Inv : S → Prop}
    {Q : R → S → Prop} {t : ITree E R} {s : S}
    (h : Always ewp Inv Q t s) : Inv s := by
  rw [Always.unfold_eq] at h; exact h.1

@[simp]
theorem Always.ret_iff (ewp : StateEffectWP S E) (Inv : S → Prop)
    (Q : R → S → Prop) (r : R) (s : S) :
    Always ewp Inv Q (.ret r) s ↔ Inv s ∧ Q r s := by
  conv => lhs; rw [Always.unfold_eq, ITree.observe_ret]

@[simp]
theorem Always.tau_iff (ewp : StateEffectWP S E) (Inv : S → Prop)
    (Q : R → S → Prop) (t : ITree E R) (s : S) :
    Always ewp Inv Q (.tau t) s ↔ Always ewp Inv Q t s := by
  conv => lhs; rw [Always.unfold_eq, ITree.observe_tau]
  exact ⟨fun h => h.2, fun h => ⟨h.inv, h⟩⟩

@[simp]
theorem Always.vis_iff (ewp : StateEffectWP S E) (Inv : S → Prop)
    (Q : R → S → Prop) (i : E.I) (k : E.O i → ITree E R) (s : S) :
    Always ewp Inv Q (.vis i k) s ↔
      Inv s ∧ ewp.wp i (fun o s' => Always ewp Inv Q (k o) s') s := by
  conv => lhs; rw [Always.unfold_eq, ITree.observe_vis]

theorem Always.ret {ewp : StateEffectWP S E} {Inv : S → Prop}
    {Q : R → S → Prop} {r : R} {s : S} (h_inv : Inv s) (hq : Q r s) :
    Always ewp Inv Q (.ret r) s :=
  (Always.ret_iff ewp Inv Q r s).2 ⟨h_inv, hq⟩

theorem Always.tau {ewp : StateEffectWP S E} {Inv : S → Prop}
    {Q : R → S → Prop} {t : ITree E R} {s : S}
    (h : Always ewp Inv Q t s) : Always ewp Inv Q (.tau t) s :=
  (Always.tau_iff ewp Inv Q t s).2 h

theorem Always.vis {ewp : StateEffectWP S E} {Inv : S → Prop}
    {Q : R → S → Prop} {i : E.I} {k : E.O i → ITree E R} {s : S}
    (h_inv : Inv s)
    (hv : ewp.wp i (fun o s' => Always ewp Inv Q (k o) s') s) :
    Always ewp Inv Q (.vis i k) s :=
  (Always.vis_iff ewp Inv Q i k s).2 ⟨h_inv, hv⟩

/-- Silent divergence satisfies `Always` as soon as the invariant holds now. -/
theorem Always.spin (ewp : StateEffectWP S E) {Inv : S → Prop}
    (Q : R → S → Prop) {s : S} (h_inv : Inv s) :
    Always ewp Inv Q (ITree.spin (E := E) (R := R)) s :=
  Always.coinduct (fun x s₀ => x = ITree.spin ∧ Inv s₀)
    (fun _ _ ⟨hx, hi⟩ => by subst hx; rw [observe_spin]; exact ⟨hi, rfl, hi⟩)
    ⟨rfl, h_inv⟩

/-- `Always` on `ITree.spin` is exactly the invariant at the current state. -/
theorem Always.spin_iff (ewp : StateEffectWP S E) (Inv : S → Prop)
    (Q : R → S → Prop) (s : S) :
    Always ewp Inv Q (ITree.spin (E := E) (R := R)) s ↔ Inv s :=
  ⟨Always.inv, Always.spin ewp Q⟩

/-- Weakening of both the invariant and the postcondition. -/
theorem Always.mono {ewp : StateEffectWP S E} {Inv Inv' : S → Prop}
    {P Q : R → S → Prop} {t : ITree E R} {s : S}
    (h_inv : ∀ s', Inv s' → Inv' s') (h_post : ∀ r s', P r s' → Q r s')
    (h : Always ewp Inv P t s) : Always ewp Inv' Q t s := by
  refine Always.coinduct (fun x s₀ => Always ewp Inv P x s₀) ?_ h
  intro x s₀ hx
  rw [Always.unfold_eq] at hx
  obtain ⟨hi, hx⟩ := hx
  refine ⟨h_inv _ hi, ?_⟩
  cases h_obs : x.observe <;> simp only [h_obs] at hx
  · exact h_post _ _ hx
  · exact hx
  · exact hx

/-- Monotonicity of `Always` in the effect transformer. -/
theorem Always.mono_wp {ewp ewp' : StateEffectWP S E} {Inv : S → Prop}
    {Q : R → S → Prop} {t : ITree E R} {s : S}
    (h_wp : ∀ (i : E.I) (K : E.O i → S → Prop) (s₀ : S),
      ewp.wp i K s₀ → ewp'.wp i K s₀)
    (h : Always ewp Inv Q t s) : Always ewp' Inv Q t s := by
  refine Always.coinduct (fun x s₀ => Always ewp Inv Q x s₀) ?_ h
  intro x s₀ hx
  rw [Always.unfold_eq] at hx
  obtain ⟨hi, hx⟩ := hx
  refine ⟨hi, ?_⟩
  cases h_obs : x.observe <;> simp only [h_obs] at hx
  · exact hx
  · exact hx
  · exact h_wp _ _ _ hx

/-- Conjunction rule for `Always` under `[StateEffectWP.Conjunctive ewp]`. -/
theorem Always.conj {ewp : StateEffectWP S E}
    [h_conj : StateEffectWP.Conjunctive ewp]
    {Inv₁ Inv₂ : S → Prop} {P Q : R → S → Prop} {t : ITree E R} {s : S}
    (hp : Always ewp Inv₁ P t s) (hq : Always ewp Inv₂ Q t s) :
    Always ewp (fun s' => Inv₁ s' ∧ Inv₂ s')
      (fun r s' => P r s' ∧ Q r s') t s := by
  refine Always.coinduct
    (fun x s₀ => Always ewp Inv₁ P x s₀ ∧ Always ewp Inv₂ Q x s₀) ?_ ⟨hp, hq⟩
  intro x s₀ ⟨hpx, hqx⟩
  rw [Always.unfold_eq] at hpx hqx
  obtain ⟨hi₁, hpx⟩ := hpx
  obtain ⟨hi₂, hqx⟩ := hqx
  refine ⟨⟨hi₁, hi₂⟩, ?_⟩
  cases h_obs : x.observe <;> simp only [h_obs] at hpx hqx
  · exact ⟨hpx, hqx⟩
  · exact ⟨hpx, hqx⟩
  · exact h_conj.conj hpx hqx

theorem Always.conj_iff (ewp : StateEffectWP S E)
    [StateEffectWP.Conjunctive ewp]
    (Inv₁ Inv₂ : S → Prop) (P Q : R → S → Prop) (t : ITree E R) (s : S) :
    Always ewp (fun s' => Inv₁ s' ∧ Inv₂ s')
        (fun r s' => P r s' ∧ Q r s') t s ↔
      Always ewp Inv₁ P t s ∧ Always ewp Inv₂ Q t s :=
  ⟨fun h => ⟨Always.mono (fun _ hi => hi.1) (fun _ _ hpq => hpq.1) h,
             Always.mono (fun _ hi => hi.2) (fun _ _ hpq => hpq.2) h⟩,
   fun ⟨hp, hq⟩ => Always.conj hp hq⟩

/-- Exact monadic bind characterisation for `Always`. -/
theorem Always.bind_iff {A B : Type u} (ewp : StateEffectWP S E)
    (Inv : S → Prop) (Q : B → S → Prop)
    (t : ITree E A) (k : A → ITree E B) (s : S) :
    Always ewp Inv Q (t >>= k) s ↔
      Always ewp Inv (fun a s' => Always ewp Inv Q (k a) s') t s := by
  constructor
  · intro h
    refine Always.coinduct (fun t₀ s₀ => Always ewp Inv Q (t₀ >>= k) s₀) ?_ h
    intro t₀ s₀ ht₀
    refine ⟨ht₀.inv, ?_⟩
    cases h_obs : t₀.observe with
    | ret a =>
      rw [eq_ret_of_observe h_obs, ret_bind] at ht₀; exact ht₀
    | tau t₀' =>
      rw [eq_tau_of_observe h_obs, tau_bind, Always.tau_iff] at ht₀; exact ht₀
    | vis i c =>
      rw [eq_vis_of_observe h_obs, vis_bind, Always.vis_iff] at ht₀
      exact ht₀.2
  · intro h
    refine Always.coinduct
      (fun u s₀ => Always ewp Inv Q u s₀ ∨
        ∃ t₀ : ITree E A, u = (t₀ >>= k) ∧
          Always ewp Inv (fun a s' => Always ewp Inv Q (k a) s') t₀ s₀)
      ?_ (Or.inr ⟨t, rfl, h⟩)
    intro u s₀ h_inv
    rcases h_inv with hu | ⟨t₀, rfl, ht₀⟩
    · rw [Always.unfold_eq] at hu
      obtain ⟨hi, hu⟩ := hu
      refine ⟨hi, ?_⟩
      cases h_obs : u.observe <;> simp only [h_obs] at hu
      · exact hu
      · exact Or.inl hu
      · exact ewp.mono (fun _ _ hd => Or.inl hd) hu
    · rw [Always.unfold_eq] at ht₀
      obtain ⟨hi, ht₀⟩ := ht₀
      refine ⟨hi, ?_⟩
      cases h_obs : t₀.observe with
      | ret a =>
        simp only [h_obs] at ht₀
        rw [eq_ret_of_observe h_obs, ret_bind]
        rw [Always.unfold_eq] at ht₀
        obtain ⟨_, ht₀⟩ := ht₀
        cases hk : (k a).observe <;> simp only [hk] at ht₀
        · exact ht₀
        · exact Or.inl ht₀
        · exact ewp.mono (fun _ _ hd => Or.inl hd) ht₀
      | tau t₀' =>
        simp only [h_obs] at ht₀
        rw [eq_tau_of_observe h_obs, tau_bind, ITree.observe_tau]
        exact Or.inr ⟨t₀', rfl, ht₀⟩
      | vis i c =>
        simp only [h_obs] at ht₀
        rw [eq_vis_of_observe h_obs, vis_bind, ITree.observe_vis]
        exact ewp.mono (fun o _ hd => Or.inr ⟨c o, rfl, hd⟩) ht₀

/-- Monadic sequencing rule for `Always`. -/
theorem Always.bind {A B : Type u} {ewp : StateEffectWP S E} {Inv : S → Prop}
    {Q : B → S → Prop} {t : ITree E A} {k : A → ITree E B} {s : S}
    (h : Always ewp Inv (fun a s' => Always ewp Inv Q (k a) s') t s) :
    Always ewp Inv Q (t >>= k) s :=
  (Always.bind_iff ewp Inv Q t k s).2 h

/-- Coinductive loop-invariant rule for `Always` over `ITree.iter`. -/
theorem Always.iter_invariant {I : Type u} {ewp : StateEffectWP S E}
    {Inv : S → Prop} (body : I → ITree E (I ⊕ R))
    (LInv : I → S → Prop) {Q : R → S → Prop}
    (h_body : ∀ a s₀, LInv a s₀ →
      Always ewp Inv (Sum.elim LInv Q) (body a) s₀)
    {init : I} {s : S} (h_init : LInv init s) :
    Always ewp Inv Q (ITree.iter body init) s := by
  let cont : I ⊕ R → ITree E R :=
    Sum.elim (fun next => .tau (ITree.iter body next)) .ret
  refine Always.coinduct
    (fun u s₀ => ∃ cur : ITree E (I ⊕ R),
      u = (cur >>= cont) ∧ Always ewp Inv (Sum.elim LInv Q) cur s₀)
    ?_ ⟨body init, iter_unfold body init, h_body init s h_init⟩
  intro u s₀ ⟨cur, hu, h_cur⟩
  subst hu
  rw [Always.unfold_eq] at h_cur
  obtain ⟨hi, h_cur⟩ := h_cur
  refine ⟨hi, ?_⟩
  cases h_obs : cur.observe with
  | ret res =>
    simp only [h_obs] at h_cur
    rw [eq_ret_of_observe h_obs, ret_bind]
    cases res with
    | inl next =>
      dsimp only [cont, Sum.elim]; rw [ITree.observe_tau]
      exact ⟨body next, iter_unfold body next, h_body next s₀ h_cur⟩
    | inr r =>
      dsimp only [cont, Sum.elim]; rw [ITree.observe_ret]
      exact h_cur
  | tau cur' =>
    simp only [h_obs] at h_cur
    rw [eq_tau_of_observe h_obs, tau_bind, ITree.observe_tau]
    exact ⟨cur', rfl, h_cur⟩
  | vis i c =>
    simp only [h_obs] at h_cur
    rw [eq_vis_of_observe h_obs, vis_bind, ITree.observe_vis]
    exact ewp.mono (fun o _ hd => ⟨c o, rfl, hd⟩) h_cur

/-- The invariant may always be added to the postcondition. -/
theorem Always.post_inv {ewp : StateEffectWP S E} {Inv : S → Prop}
    {Q : R → S → Prop} {t : ITree E R} {s : S}
    (h : Always ewp Inv Q t s) :
    Always ewp Inv (fun r s' => Inv s' ∧ Q r s') t s := by
  refine Always.coinduct (fun x s₀ => Always ewp Inv Q x s₀) ?_ h
  intro x s₀ hx
  rw [Always.unfold_eq] at hx
  obtain ⟨hi, hx⟩ := hx
  refine ⟨hi, ?_⟩
  cases h_obs : x.observe <;> simp only [h_obs] at hx
  · exact ⟨hi, hx⟩
  · exact hx
  · exact hx

/-- `Always` is stable under silent `.tau` prefixes (`TauStar`). -/
theorem Always.tauStar {ewp : StateEffectWP S E} {Inv : S → Prop}
    {Q : R → S → Prop} {t u : ITree E R} {s : S}
    (h_tau : TauStar t u) (h : Always ewp Inv Q t s) :
    Always ewp Inv Q u s := by
  induction h_tau with
  | refl => exact h
  | step ht _ ih =>
    rw [Always.unfold_eq, ht] at h
    exact ih h.2

/-! ### 1.1 Exact `DWLP` Bridges (`guardInvWP`) -/

/--
Invariant-guarded effect transformer: every answer of every request must
re-establish `Inv` in addition to the continuation postcondition.
-/
def guardInvWP (ewp : StateEffectWP S E) (Inv : S → Prop) :
    StateEffectWP S E where
  wp i K s := ewp.wp i (fun o s' => Inv s' ∧ K o s') s
  mono h hw := ewp.mono (fun o s' hk => ⟨hk.1, h o s' hk.2⟩) hw

@[simp]
theorem guardInvWP_wp (ewp : StateEffectWP S E) (Inv : S → Prop)
    (i : E.I) (K : E.O i → S → Prop) (s : S) :
    (guardInvWP ewp Inv).wp i K s ↔
      ewp.wp i (fun o s' => Inv s' ∧ K o s') s :=
  Iff.rfl

instance (ewp : StateEffectWP S E) (Inv : S → Prop)
    [h : StateEffectWP.Conjunctive ewp] :
    StateEffectWP.Conjunctive (guardInvWP ewp Inv) where
  conj hp hq :=
    ewp.mono (fun _ _ hpq => ⟨hpq.1.1, hpq.1.2, hpq.2.2⟩) (h.conj hp hq)

instance (ewp : StateEffectWP S E) (Inv : S → Prop)
    [h : StateEffectWP.ExcludedMiracle ewp] :
    StateEffectWP.ExcludedMiracle (guardInvWP ewp Inv) where
  no_miracle hw := h.no_miracle (ewp.mono (fun _ _ hk => hk.2) hw)

instance (ewp : StateEffectWP S E) (Inv : S → Prop)
    [h : StateEffectWP.Disjunctive ewp] :
    StateEffectWP.Disjunctive (guardInvWP ewp Inv) where
  disj hw :=
    h.disj (ewp.mono
      (fun _ _ hk => hk.2.elim (fun hp => Or.inl ⟨hk.1, hp⟩)
        (fun hq => Or.inr ⟨hk.1, hq⟩)) hw)

instance {E : Effect.{u}} [FaultEffect E] (ewp : EffectWP E)
    (Inv : PUnit.{u + 1} → Prop) [h : PureSoundWP ewp] :
    PureSoundWP (guardInvWP ewp Inv) where
  sound hw := ⟨(h.sound hw).1, fun o => ((h.sound hw).2 o).2⟩

instance {E : Effect.{u}} [FaultEffect E]
    (ewp : StateEffectWP (List (Event E)) E)
    (Inv : List (Event E) → Prop) [h : TraceSoundWP ewp] :
    TraceSoundWP (guardInvWP ewp Inv) where
  sound hw := ⟨(h.sound hw).1, fun o => ((h.sound hw).2 o).2⟩

/-- Invariant guards distribute over effect-row coproducts. -/
theorem guardInvWP_sum_wp {E₁ E₂ : Effect.{u}} (w₁ : StateEffectWP S E₁)
    (w₂ : StateEffectWP S E₂) (Inv : S → Prop) (i : (SumE E₁ E₂).I)
    (K : (SumE E₁ E₂).O i → S → Prop) (s : S) :
    (guardInvWP (w₁.sum w₂) Inv).wp i K s ↔
      ((guardInvWP w₁ Inv).sum (guardInvWP w₂ Inv)).wp i K s := by
  cases i <;> exact Iff.rfl

/-- `guardInvWP ewp Inv` preserves `Inv` across every effect step. -/
theorem guardInvWP_preserves (ewp : StateEffectWP S E) (Inv : S → Prop)
    (i : E.I) (K : E.O i → S → Prop) (s₀ : S)
    (hw : (guardInvWP ewp Inv).wp i K s₀) :
    (guardInvWP ewp Inv).wp i (fun o s' => Inv s' ∧ K o s') s₀ :=
  ewp.mono (fun _ _ hk => ⟨hk.1, hk.1, hk.2⟩) hw

/--
**Exact `DWLP` bridge.** `Always ewp Inv Q` is precisely the invariant now
together with `DWLP` over the invariant-guarded transformer `guardInvWP`.
-/
theorem always_iff_dwlp_invariant (ewp : StateEffectWP S E) (Inv : S → Prop)
    (Q : R → S → Prop) (t : ITree E R) (s : S) :
    Always ewp Inv Q t s ↔
      Inv s ∧
        DWLP (guardInvWP ewp Inv) t (fun r s' => Inv s' ∧ Q r s') s := by
  constructor
  · intro h
    refine ⟨h.inv, DWLP.coinduct (fun x s₀ => Always ewp Inv Q x s₀) ?_ h⟩
    intro x s₀ hx
    rw [Always.unfold_eq] at hx
    obtain ⟨hi, hx⟩ := hx
    cases h_obs : x.observe <;> simp only [h_obs] at hx
    · exact ⟨hi, hx⟩
    · exact hx
    · exact ewp.mono (fun _ _ ha => ⟨ha.inv, ha⟩) hx
  · rintro ⟨hi, hd⟩
    refine Always.coinduct
      (fun x s₀ => Inv s₀ ∧
        DWLP (guardInvWP ewp Inv) x (fun r s' => Inv s' ∧ Q r s') s₀)
      ?_ ⟨hi, hd⟩
    intro x s₀ ⟨hi₀, hx⟩
    rw [DWLP.unfold_eq] at hx
    refine ⟨hi₀, ?_⟩
    cases h_obs : x.observe <;> simp only [h_obs] at hx
    · exact hx.2
    · exact ⟨hi₀, hx⟩
    · exact hx

/--
Variant of the exact `DWLP` bridge with an unstrengthened postcondition: the
guard already forces the invariant at every return state.
-/
theorem always_iff_dwlp_guard (ewp : StateEffectWP S E) (Inv : S → Prop)
    (Q : R → S → Prop) (t : ITree E R) (s : S) :
    Always ewp Inv Q t s ↔ Inv s ∧ DWLP (guardInvWP ewp Inv) t Q s := by
  constructor
  · intro h
    have h' := (always_iff_dwlp_invariant ewp Inv Q t s).1 h
    exact ⟨h'.1, DWLP.mono (fun _ _ hq => hq.2) h'.2⟩
  · rintro ⟨hi, hd⟩
    refine Always.coinduct
      (fun x s₀ => Inv s₀ ∧ DWLP (guardInvWP ewp Inv) x Q s₀) ?_ ⟨hi, hd⟩
    intro x s₀ ⟨hi₀, hx⟩
    rw [DWLP.unfold_eq] at hx
    refine ⟨hi₀, ?_⟩
    cases h_obs : x.observe <;> simp only [h_obs] at hx
    · exact hx
    · exact ⟨hi₀, hx⟩
    · exact hx

/-- With the trivial invariant, `Always` is exactly `DWLP`. -/
theorem always_true_iff_dwlp (ewp : StateEffectWP S E) (Q : R → S → Prop)
    (t : ITree E R) (s : S) :
    Always ewp (fun _ => True) Q t s ↔ DWLP ewp t Q s := by
  constructor
  · intro h
    refine DWLP.coinduct (fun x s₀ => Always ewp (fun _ => True) Q x s₀) ?_ h
    intro x s₀ hx
    rw [Always.unfold_eq] at hx
    obtain ⟨_, hx⟩ := hx
    cases h_obs : x.observe <;> simp only [h_obs] at hx <;> exact hx
  · intro h
    refine Always.coinduct (fun x s₀ => DWLP ewp x Q s₀) ?_ h
    intro x s₀ hx
    rw [DWLP.unfold_eq] at hx
    refine ⟨trivial, ?_⟩
    cases h_obs : x.observe <;> simp only [h_obs] at hx <;> exact hx

/-- `Always` implies plain partial correctness `DWLP` of the postcondition. -/
theorem Always.toDWLP {ewp : StateEffectWP S E} {Inv : S → Prop}
    {Q : R → S → Prop} {t : ITree E R} {s : S}
    (h : Always ewp Inv Q t s) : DWLP ewp t Q s :=
  (always_true_iff_dwlp ewp Q t s).1
    (Always.mono (fun _ _ => trivial) (fun _ _ hq => hq) h)

/--
When `ewp` itself preserves `Inv` across every step, `Always` collapses to the
invariant now plus ordinary `DWLP` with the invariant added to the
postcondition (no guard needed).
-/
theorem always_iff_dwlp_of_preserves {ewp : StateEffectWP S E}
    {Inv : S → Prop}
    (h_pres : ∀ (i : E.I) (K : E.O i → S → Prop) (s₀ : S),
      Inv s₀ → ewp.wp i K s₀ → ewp.wp i (fun o s' => Inv s' ∧ K o s') s₀)
    (Q : R → S → Prop) (t : ITree E R) (s : S) :
    Always ewp Inv Q t s ↔
      Inv s ∧ DWLP ewp t (fun r s' => Inv s' ∧ Q r s') s := by
  constructor
  · intro h
    exact ⟨h.inv, h.post_inv.toDWLP⟩
  · rintro ⟨hi, hd⟩
    refine Always.coinduct
      (fun x s₀ => Inv s₀ ∧ DWLP ewp x (fun r s' => Inv s' ∧ Q r s') s₀)
      ?_ ⟨hi, hd⟩
    intro x s₀ ⟨hi₀, hx⟩
    rw [DWLP.unfold_eq] at hx
    refine ⟨hi₀, ?_⟩
    cases h_obs : x.observe <;> simp only [h_obs] at hx
    · exact hx.2
    · exact ⟨hi₀, hx⟩
    · exact h_pres _ _ _ hi₀ hx

/-- Guarding by the very invariant being checked does not change `Always`. -/
theorem always_guardInvWP_iff (ewp : StateEffectWP S E) (Inv : S → Prop)
    (Q : R → S → Prop) (t : ITree E R) (s : S) :
    Always (guardInvWP ewp Inv) Inv Q t s ↔ Always ewp Inv Q t s := by
  constructor
  · intro h
    refine Always.coinduct
      (fun x s₀ => Always (guardInvWP ewp Inv) Inv Q x s₀) ?_ h
    intro x s₀ hx
    rw [Always.unfold_eq] at hx
    obtain ⟨hi, hx⟩ := hx
    refine ⟨hi, ?_⟩
    cases h_obs : x.observe <;> simp only [h_obs] at hx
    · exact hx
    · exact hx
    · exact ewp.mono (fun _ _ hk => hk.2) hx
  · intro h
    refine Always.coinduct (fun x s₀ => Always ewp Inv Q x s₀) ?_ h
    intro x s₀ hx
    rw [Always.unfold_eq] at hx
    obtain ⟨hi, hx⟩ := hx
    refine ⟨hi, ?_⟩
    cases h_obs : x.observe <;> simp only [h_obs] at hx
    · exact hx
    · exact hx
    · exact ewp.mono (fun _ _ ha => ⟨ha.inv, ha⟩) hx

/-! ### 1.2 State-Only and Transition-Relational Safety -/

/-- State invariance with no extra obligation on returned values. -/
def AlwaysState (ewp : StateEffectWP S E) (Inv : S → Prop)
    (t : ITree E R) (s : S) : Prop :=
  Always ewp Inv (fun _ s' => Inv s') t s

/-- `AlwaysState` carries no postcondition beyond the invariant itself. -/
theorem alwaysState_iff (ewp : StateEffectWP S E) (Inv : S → Prop)
    (t : ITree E R) (s : S) :
    AlwaysState ewp Inv t s ↔ Always ewp Inv (fun _ _ => True) t s :=
  ⟨Always.mono (fun _ hi => hi) (fun _ _ _ => trivial),
   fun h => Always.mono (fun _ hi => hi) (fun _ _ hq => hq.1) h.post_inv⟩

/-- Step-relation-guarded transformer: every answer must satisfy `StepRel`. -/
def guardStepWP (ewp : StateEffectWP S E)
    (StepRel : (i : E.I) → E.O i → S → S → Prop) : StateEffectWP S E where
  wp i K s := ewp.wp i (fun o s' => StepRel i o s s' ∧ K o s') s
  mono h hw := ewp.mono (fun o s' hk => ⟨hk.1, h o s' hk.2⟩) hw

@[simp]
theorem guardStepWP_wp (ewp : StateEffectWP S E)
    (StepRel : (i : E.I) → E.O i → S → S → Prop)
    (i : E.I) (K : E.O i → S → Prop) (s : S) :
    (guardStepWP ewp StepRel).wp i K s ↔
      ewp.wp i (fun o s' => StepRel i o s s' ∧ K o s') s :=
  Iff.rfl

instance (ewp : StateEffectWP S E)
    (StepRel : (i : E.I) → E.O i → S → S → Prop)
    [h : StateEffectWP.Conjunctive ewp] :
    StateEffectWP.Conjunctive (guardStepWP ewp StepRel) where
  conj hp hq :=
    ewp.mono (fun _ _ hpq => ⟨hpq.1.1, hpq.1.2, hpq.2.2⟩) (h.conj hp hq)

instance (ewp : StateEffectWP S E)
    (StepRel : (i : E.I) → E.O i → S → S → Prop)
    [h : StateEffectWP.ExcludedMiracle ewp] :
    StateEffectWP.ExcludedMiracle (guardStepWP ewp StepRel) where
  no_miracle hw := h.no_miracle (ewp.mono (fun _ _ hk => hk.2) hw)

private def alwaysStepAux (ewp : StateEffectWP S E)
    (StepRel : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (t : ITree E R) (s : S) : Prop :=
  match t.observe with
  | .ret r => Q r s
  | .tau t' => alwaysStepAux ewp StepRel Q t' s
  | .vis i k =>
    ewp.wp i
      (fun o s' => StepRel i o s s' ∧ alwaysStepAux ewp StepRel Q (k o) s') s
coinductive_fixpoint

/--
Transition-relational safety: every `.vis i k` step from state `s₀` to `s'`
with answer `o` satisfies `StepRel i o s₀ s'`, and `Q` holds on return.
-/
def AlwaysStep (ewp : StateEffectWP S E)
    (StepRel : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (t : ITree E R) (s : S) : Prop :=
  alwaysStepAux ewp StepRel Q t s

theorem AlwaysStep.unfold_eq (ewp : StateEffectWP S E)
    (StepRel : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (t : ITree E R) (s : S) :
    AlwaysStep ewp StepRel Q t s =
      match t.observe with
      | .ret r => Q r s
      | .tau t' => AlwaysStep ewp StepRel Q t' s
      | .vis i k =>
        ewp.wp i
          (fun o s' => StepRel i o s s' ∧ AlwaysStep ewp StepRel Q (k o) s') s :=
  alwaysStepAux.eq_def ewp StepRel Q t s

/-- Park coinduction principle for `AlwaysStep`. -/
theorem AlwaysStep.coinduct {ewp : StateEffectWP S E}
    {StepRel : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    (X : ITree E R → S → Prop)
    (h_step : ∀ x s₀, X x s₀ →
      match x.observe with
      | .ret r => Q r s₀
      | .tau x' => X x' s₀
      | .vis i k => ewp.wp i (fun o s' => StepRel i o s₀ s' ∧ X (k o) s') s₀)
    {t : ITree E R} {s : S} (h_init : X t s) :
    AlwaysStep ewp StepRel Q t s :=
  alwaysStepAux.coinduct ewp StepRel Q X h_step t s h_init

/-- **Exact `DWLP` bridge** for transition-relational safety. -/
theorem alwaysStep_iff_dwlp (ewp : StateEffectWP S E)
    (StepRel : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (t : ITree E R) (s : S) :
    AlwaysStep ewp StepRel Q t s ↔ DWLP (guardStepWP ewp StepRel) t Q s := by
  constructor
  · intro h
    refine DWLP.coinduct (fun x s₀ => AlwaysStep ewp StepRel Q x s₀) ?_ h
    intro x s₀ hx
    rw [AlwaysStep.unfold_eq] at hx
    cases h_obs : x.observe <;> simp only [h_obs] at hx <;> exact hx
  · intro h
    refine AlwaysStep.coinduct
      (fun x s₀ => DWLP (guardStepWP ewp StepRel) x Q s₀) ?_ h
    intro x s₀ hx
    rw [DWLP.unfold_eq] at hx
    cases h_obs : x.observe <;> simp only [h_obs] at hx <;> exact hx

/--
A step relation that preserves `Inv` turns transition-relational safety into
state invariance.
-/
theorem AlwaysStep.toAlways {ewp : StateEffectWP S E}
    {StepRel : (i : E.I) → E.O i → S → S → Prop} {Inv : S → Prop}
    {Q : R → S → Prop} {t : ITree E R} {s : S}
    (h_pres : ∀ i o s₀ s', Inv s₀ → StepRel i o s₀ s' → Inv s')
    (h_inv : Inv s) (h : AlwaysStep ewp StepRel Q t s) :
    Always ewp Inv Q t s := by
  refine Always.coinduct
    (fun x s₀ => Inv s₀ ∧ AlwaysStep ewp StepRel Q x s₀) ?_ ⟨h_inv, h⟩
  intro x s₀ ⟨hi, hx⟩
  rw [AlwaysStep.unfold_eq] at hx
  refine ⟨hi, ?_⟩
  cases h_obs : x.observe <;> simp only [h_obs] at hx
  · exact hx
  · exact ⟨hi, hx⟩
  · exact ewp.mono (fun _ _ hk => ⟨h_pres _ _ _ _ hi hk.1, hk.2⟩) hx

/-- Weakening of the step relation and the postcondition. -/
theorem AlwaysStep.mono {ewp : StateEffectWP S E}
    {StepRel StepRel' : (i : E.I) → E.O i → S → S → Prop}
    {P Q : R → S → Prop} {t : ITree E R} {s : S}
    (h_rel : ∀ i o s₀ s', StepRel i o s₀ s' → StepRel' i o s₀ s')
    (h_post : ∀ r s', P r s' → Q r s')
    (h : AlwaysStep ewp StepRel P t s) : AlwaysStep ewp StepRel' Q t s := by
  refine AlwaysStep.coinduct (fun x s₀ => AlwaysStep ewp StepRel P x s₀) ?_ h
  intro x s₀ hx
  rw [AlwaysStep.unfold_eq] at hx
  cases h_obs : x.observe <;> simp only [h_obs] at hx
  · exact h_post _ _ hx
  · exact hx
  · exact ewp.mono (fun _ _ hk => ⟨h_rel _ _ _ _ hk.1, hk.2⟩) hx

/-- Monadic sequencing rule for `AlwaysStep`. -/
theorem AlwaysStep.bind {A B : Type u} {ewp : StateEffectWP S E}
    {StepRel : (i : E.I) → E.O i → S → S → Prop}
    {Q : B → S → Prop} {t : ITree E A} {k : A → ITree E B} {s : S}
    (h : AlwaysStep ewp StepRel
      (fun a s' => AlwaysStep ewp StepRel Q (k a) s') t s) :
    AlwaysStep ewp StepRel Q (t >>= k) s :=
  (alwaysStep_iff_dwlp ewp StepRel Q (t >>= k) s).2
    (DWLP.bind (DWLP.mono
      (fun a s' ha => (alwaysStep_iff_dwlp ewp StepRel Q (k a) s').1 ha)
      ((alwaysStep_iff_dwlp ewp StepRel _ t s).1 h)))

/-- Coinductive loop-invariant rule for `AlwaysStep` over `ITree.iter`. -/
theorem AlwaysStep.iter_invariant {I : Type u} {ewp : StateEffectWP S E}
    {StepRel : (i : E.I) → E.O i → S → S → Prop}
    (body : I → ITree E (I ⊕ R)) (LInv : I → S → Prop) {Q : R → S → Prop}
    (h_body : ∀ a s₀, LInv a s₀ →
      AlwaysStep ewp StepRel (Sum.elim LInv Q) (body a) s₀)
    {init : I} {s : S} (h_init : LInv init s) :
    AlwaysStep ewp StepRel Q (ITree.iter body init) s :=
  (alwaysStep_iff_dwlp ewp StepRel Q (ITree.iter body init) s).2
    (DWLP.iter_invariant body LInv
      (fun a s₀ ha =>
        (alwaysStep_iff_dwlp ewp StepRel _ (body a) s₀).1 (h_body a s₀ ha))
      h_init)

end Always

/-! ### 1.3 Operational Adequacy and `Std.Do.Triple` Interoperability -/

section AlwaysAdequacy

variable {E : Effect.{u}} {R : Type u} [FaultEffect E]

/--
Stateless adequacy: `Always` over a `PureSoundWP` transformer guarantees
`TreeSafe t` and the postcondition on every return.
-/
theorem always_pure_adequacy {ewp : EffectWP E} [PureSoundWP ewp]
    {Inv : PUnit.{u + 1} → Prop} {t : ITree E R} {post : R → Prop}
    (h : Always ewp Inv (fun r _ => post r) t PUnit.unit) :
    Inv PUnit.unit ∧ TreeSafe t ∧ ∀ tr r, ReachesRet t tr r → post r :=
  ⟨h.inv, dwlp_pure_adequacy h.toDWLP⟩

/--
Bridge to the stateless coinductive modality `Anneal.ITree.CoAlways`: any tree
property implied by `Always` holds at every reachable residual.
-/
theorem always_coAlways_bridge {ewp : EffectWP E} [h_sound : PureSoundWP ewp]
    {Inv : PUnit.{u + 1} → Prop} {Q : R → PUnit.{u + 1} → Prop}
    {P : ITree E R → Prop}
    (h_P : ∀ x, Always ewp Inv Q x PUnit.unit → P x)
    {t : ITree E R} (h : Always ewp Inv Q t PUnit.unit) :
    CoAlways P t := by
  refine CoAlways.coinduct P (fun x => Always ewp Inv Q x PUnit.unit) ?_ t h
  intro x hx
  refine ⟨h_P x hx, ?_⟩
  rw [Always.unfold_eq] at hx
  obtain ⟨_, hx⟩ := hx
  cases h_obs : x.observe <;> simp only [h_obs] at hx
  · trivial
  · exact hx
  · exact (h_sound.sound hx).2

/-- Every residual reachable under `Always` is fault-free right now. -/
theorem always_coAlways_not_faultNow {ewp : EffectWP E}
    [h_sound : PureSoundWP ewp]
    {Inv : PUnit.{u + 1} → Prop} {Q : R → PUnit.{u + 1} → Prop}
    {t : ITree E R} (h : Always ewp Inv Q t PUnit.unit) :
    CoAlways (fun x => ¬ FaultNow x) t := by
  refine always_coAlways_bridge (fun x hx => ?_) h
  rintro ⟨x', i, k, h_tau, h_obs, h_fault⟩
  have hx' := Always.tauStar h_tau hx
  rw [Always.unfold_eq, h_obs] at hx'
  exact (h_sound.sound hx'.2).1 h_fault

private theorem always_trace_reaches
    {ewp : StateEffectWP (List (Event E)) E} [h_sound : TraceSoundWP ewp]
    {Inv : List (Event E) → Prop} {Q : R → List (Event E) → Prop}
    {t u : ITree E R} {tr : List (Event E)} (h_reach : Reaches t tr u) :
    ∀ {tr₀ : List (Event E)},
      Always ewp Inv Q t tr₀ → Always ewp Inv Q u (tr₀ ++ tr) := by
  induction h_reach with
  | refl => intro tr₀ h; simpa using h
  | tau ht _ ih =>
    intro tr₀ h; rw [Always.unfold_eq, ht] at h; exact ih h.2
  | vis hv _ o _ ih =>
    intro tr₀ h
    rw [Always.unfold_eq, hv] at h
    have h_next := ih ((h_sound.sound h.2).2 o)
    simpa [List.append_assoc] using h_next

/--
Event-trace adequacy: `Always` over a `TraceSoundWP` transformer guarantees
`TreeSafe t`, the invariant on **every** reachable finite trace prefix, and the
postcondition on every completed trace.
-/
theorem always_trace_adequacy
    {ewp : StateEffectWP (List (Event E)) E} [h_sound : TraceSoundWP ewp]
    {Inv : List (Event E) → Prop} {Q : R → List (Event E) → Prop}
    {t : ITree E R} {tr₀ : List (Event E)}
    (h : Always ewp Inv Q t tr₀) :
    TreeSafe t ∧ (∀ tr u, Reaches t tr u → Inv (tr₀ ++ tr)) ∧
      ∀ tr r, ReachesRet t tr r → Q r (tr₀ ++ tr) := by
  refine ⟨?_, ?_, ?_⟩
  · intro tr u h_reach ⟨u', i, k, h_tau, h_obs, h_fault⟩
    have hu' := Always.tauStar h_tau (always_trace_reaches h_reach h)
    rw [Always.unfold_eq, h_obs] at hu'
    exact (h_sound.sound hu'.2).1 h_fault
  · intro tr u h_reach
    exact (always_trace_reaches h_reach h).inv
  · intro tr r ⟨u, h_reach, h_ret⟩
    have hu := always_trace_reaches h_reach h
    rw [Always.unfold_eq, h_ret] at hu
    exact hu.2

/--
**Exact operational characterisation** of `Always` for the canonical
trace-recording transformer `eventTraceWP E`: it holds iff the tree is
fault-free, every reachable trace prefix satisfies the invariant, and every
completed trace satisfies the postcondition.
-/
theorem always_eventTrace_iff (Inv : List (Event E) → Prop)
    (Q : R → List (Event E) → Prop) (t : ITree E R)
    (tr₀ : List (Event E)) :
    Always (eventTraceWP E) Inv Q t tr₀ ↔
      TreeSafe t ∧ (∀ tr u, Reaches t tr u → Inv (tr₀ ++ tr)) ∧
        ∀ tr r, ReachesRet t tr r → Q r (tr₀ ++ tr) := by
  refine ⟨always_trace_adequacy, fun h => ?_⟩
  refine Always.coinduct
    (fun x tr₁ => TreeSafe x ∧ (∀ tr u, Reaches x tr u → Inv (tr₁ ++ tr)) ∧
      ∀ tr r, ReachesRet x tr r → Q r (tr₁ ++ tr)) ?_ h
  intro x tr₁ ⟨h_safe, h_inv, h_ret⟩
  refine ⟨by simpa using h_inv [] x (.refl x), ?_⟩
  cases h_obs : x.observe with
  | ret r => simpa using h_ret [] r ⟨x, .refl x, h_obs⟩
  | tau x' =>
    exact ⟨fun tr u hr => h_safe tr u (.tau h_obs hr),
      fun tr u hr => h_inv tr u (.tau h_obs hr),
      fun tr r ⟨u, hr, hu⟩ => h_ret tr r ⟨u, .tau h_obs hr, hu⟩⟩
  | vis i k =>
    have h_nf : ¬ FaultEffect.isFault i := fun hf =>
      h_safe [] x (.refl x) ⟨x, i, k, .refl x, h_obs, hf⟩
    refine ⟨h_nf, fun o => ⟨?_, ?_, ?_⟩⟩
    · exact fun tr u hr => h_safe _ u (.vis h_obs h_nf o hr)
    · intro tr u hr
      simpa [List.append_assoc] using h_inv _ u (.vis h_obs h_nf o hr)
    · rintro tr r ⟨u, hr, hu⟩
      simpa [List.append_assoc] using
        h_ret _ r ⟨u, .vis h_obs h_nf o hr, hu⟩

end AlwaysAdequacy

section AlwaysStdDo

open Std.Do

variable {E : Effect.{u}} {R : Type u}

/-- A `Std.Do.Triple` on `ITree E R` yields `Always` with the trivial invariant. -/
theorem Triple.toAlways [p : PureEffectWP E] {t : ITree E R} {P : Prop}
    {Q : R → Prop} (htriple : ⦃⌜P⌝⦄ t ⦃⇓ r => ⌜Q r⌝⦄) (hp : P) :
    Always p.ewp (fun _ => True) (fun r _ => Q r) t PUnit.unit :=
  (always_true_iff_dwlp p.ewp _ t PUnit.unit).2 (Triple.toDWLP htriple hp)

/-- `Always` (for any invariant) yields the corresponding `Std.Do.Triple`. -/
theorem Triple.of_always [p : PureEffectWP E] {t : ITree E R} {P : Prop}
    {Inv : PUnit.{u + 1} → Prop} {Q : R → Prop}
    (h : P → Always p.ewp Inv (fun r _ => Q r) t PUnit.unit) :
    ⦃⌜P⌝⦄ t ⦃⇓ r => ⌜Q r⌝⦄ := by
  intro hp
  exact (h hp).toDWLP

/-- `Std.Do.Triple` on `ITree E R` is exactly `Always` with a trivial invariant. -/
theorem triple_iff_always [p : PureEffectWP E] (t : ITree E R) (P : Prop)
    (Q : R → Prop) :
    ⦃⌜P⌝⦄ t ⦃⇓ r => ⌜Q r⌝⦄ ↔
      (P → Always p.ewp (fun _ => True) (fun r _ => Q r) t PUnit.unit) :=
  ⟨Triple.toAlways, Triple.of_always⟩

end AlwaysStdDo

/-! ## 2. Strong `Until` ($\mathcal{U}$) and `Eventually` ($\Diamond$) -/

section Until

variable {S : Type u} {E : Effect.{u}} {R : Type u}

private def untilAux (ewp : StateEffectWP S E) (Hold Target : S → Prop)
    (Q : R → S → Prop) (t : ITree E R) (s : S) : Prop :=
  Target s ∨ (Hold s ∧
    match t.observe with
    | .ret r => Q r s
    | .tau t' => untilAux ewp Hold Target Q t' s
    | .vis i k => ewp.wp i (fun o s' => untilAux ewp Hold Target Q (k o) s') s)
inductive_fixpoint

/--
Inductive strong until ($\mathcal{U}$): either `Target s` holds now, or `Hold s`
holds and the tree makes one step into configurations that again satisfy
`Until`; a `.ret r` must satisfy `Q r s`. Being a least fixed point, the target
(or a return) is reached after finitely many steps on every path.
-/
def Until (ewp : StateEffectWP S E) (Hold Target : S → Prop)
    (Q : R → S → Prop) (t : ITree E R) (s : S) : Prop :=
  untilAux ewp Hold Target Q t s

theorem Until.unfold_eq (ewp : StateEffectWP S E) (Hold Target : S → Prop)
    (Q : R → S → Prop) (t : ITree E R) (s : S) :
    Until ewp Hold Target Q t s =
      (Target s ∨ (Hold s ∧
        match t.observe with
        | .ret r => Q r s
        | .tau t' => Until ewp Hold Target Q t' s
        | .vis i k =>
          ewp.wp i (fun o s' => Until ewp Hold Target Q (k o) s') s)) :=
  untilAux.eq_def ewp Hold Target Q t s

/-- Park induction principle for `Until`. -/
theorem Until.induct {ewp : StateEffectWP S E} {Hold Target : S → Prop}
    {Q : R → S → Prop} (Pre : ITree E R → S → Prop)
    (h_closed : ∀ x s₀,
      (Target s₀ ∨ (Hold s₀ ∧
        match x.observe with
        | .ret r => Q r s₀
        | .tau x' => Pre x' s₀
        | .vis i k => ewp.wp i (fun o s' => Pre (k o) s') s₀)) →
      Pre x s₀)
    {t : ITree E R} {s : S} (h : Until ewp Hold Target Q t s) :
    Pre t s :=
  untilAux.induct ewp Hold Target Q Pre h_closed t s h

/--
Strengthened induction principle for `Until` that additionally provides
`Until` itself at the node under consideration.
-/
theorem Until.induct_strong {ewp : StateEffectWP S E} {Hold Target : S → Prop}
    {Q : R → S → Prop} (Pre : ITree E R → S → Prop)
    (h_closed : ∀ x s₀, Until ewp Hold Target Q x s₀ →
      (Target s₀ ∨ (Hold s₀ ∧
        match x.observe with
        | .ret r => Q r s₀
        | .tau x' => Pre x' s₀
        | .vis i k => ewp.wp i (fun o s' => Pre (k o) s') s₀)) →
      Pre x s₀)
    {t : ITree E R} {s : S} (h : Until ewp Hold Target Q t s) :
    Pre t s := by
  refine (Until.induct
    (fun x s₀ => Until ewp Hold Target Q x s₀ ∧ Pre x s₀) ?_ h).2
  intro x s₀ hx
  have hU : Until ewp Hold Target Q x s₀ := by
    rw [Until.unfold_eq]
    refine hx.imp id (And.imp id ?_)
    intro hm
    cases h_obs : x.observe <;> simp only [h_obs] at hm ⊢
    · exact hm
    · exact hm.1
    · exact ewp.mono (fun _ _ hp => hp.1) hm
  refine ⟨hU, h_closed x s₀ hU (hx.imp id (And.imp id ?_))⟩
  intro hm
  cases h_obs : x.observe <;> simp only [h_obs] at hm ⊢
  · exact hm
  · exact hm.2
  · exact ewp.mono (fun _ _ hp => hp.2) hm

/-- `Until` holds immediately when the target holds now. -/
theorem Until.here {ewp : StateEffectWP S E} {Hold Target : S → Prop}
    {Q : R → S → Prop} {t : ITree E R} {s : S} (h : Target s) :
    Until ewp Hold Target Q t s := by
  rw [Until.unfold_eq]; exact Or.inl h

/-- At every `Until` configuration the target or the hold condition holds. -/
theorem Until.now {ewp : StateEffectWP S E} {Hold Target : S → Prop}
    {Q : R → S → Prop} {t : ITree E R} {s : S}
    (h : Until ewp Hold Target Q t s) : Target s ∨ Hold s := by
  rw [Until.unfold_eq] at h; exact h.imp id And.left

@[simp]
theorem Until.ret_iff (ewp : StateEffectWP S E) (Hold Target : S → Prop)
    (Q : R → S → Prop) (r : R) (s : S) :
    Until ewp Hold Target Q (.ret r) s ↔ Target s ∨ (Hold s ∧ Q r s) := by
  conv => lhs; rw [Until.unfold_eq, ITree.observe_ret]

@[simp]
theorem Until.tau_iff (ewp : StateEffectWP S E) (Hold Target : S → Prop)
    (Q : R → S → Prop) (t : ITree E R) (s : S) :
    Until ewp Hold Target Q (.tau t) s ↔ Until ewp Hold Target Q t s := by
  conv => lhs; rw [Until.unfold_eq, ITree.observe_tau]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact Until.here h
    · exact h
  · intro h
    rcases h.now with ht | hh
    · exact Or.inl ht
    · exact Or.inr ⟨hh, h⟩

@[simp]
theorem Until.vis_iff (ewp : StateEffectWP S E) (Hold Target : S → Prop)
    (Q : R → S → Prop) (i : E.I) (k : E.O i → ITree E R) (s : S) :
    Until ewp Hold Target Q (.vis i k) s ↔
      Target s ∨
        (Hold s ∧ ewp.wp i (fun o s' => Until ewp Hold Target Q (k o) s') s) := by
  conv => lhs; rw [Until.unfold_eq, ITree.observe_vis]

theorem Until.ret {ewp : StateEffectWP S E} {Hold Target : S → Prop}
    {Q : R → S → Prop} {r : R} {s : S} (h_hold : Hold s) (hq : Q r s) :
    Until ewp Hold Target Q (.ret r) s :=
  (Until.ret_iff ewp Hold Target Q r s).2 (Or.inr ⟨h_hold, hq⟩)

theorem Until.tau {ewp : StateEffectWP S E} {Hold Target : S → Prop}
    {Q : R → S → Prop} {t : ITree E R} {s : S}
    (h : Until ewp Hold Target Q t s) :
    Until ewp Hold Target Q (.tau t) s :=
  (Until.tau_iff ewp Hold Target Q t s).2 h

theorem Until.vis {ewp : StateEffectWP S E} {Hold Target : S → Prop}
    {Q : R → S → Prop} {i : E.I} {k : E.O i → ITree E R} {s : S}
    (h_hold : Hold s)
    (hv : ewp.wp i (fun o s' => Until ewp Hold Target Q (k o) s') s) :
    Until ewp Hold Target Q (.vis i k) s :=
  (Until.vis_iff ewp Hold Target Q i k s).2 (Or.inr ⟨h_hold, hv⟩)

/-- Weakening of the hold condition, the target, and the postcondition. -/
theorem Until.mono {ewp : StateEffectWP S E}
    {Hold Hold' Target Target' : S → Prop} {P Q : R → S → Prop}
    {t : ITree E R} {s : S}
    (h_hold : ∀ s', Hold s' → Hold' s') (h_tgt : ∀ s', Target s' → Target' s')
    (h_post : ∀ r s', P r s' → Q r s')
    (h : Until ewp Hold Target P t s) : Until ewp Hold' Target' Q t s := by
  refine Until.induct (fun x s₀ => Until ewp Hold' Target' Q x s₀) ?_ h
  intro x s₀ hx
  rw [Until.unfold_eq]
  rcases hx with ht | ⟨hh, hx⟩
  · exact Or.inl (h_tgt _ ht)
  · refine Or.inr ⟨h_hold _ hh, ?_⟩
    cases h_obs : x.observe <;> simp only [h_obs] at hx ⊢
    · exact h_post _ _ hx
    · exact hx
    · exact hx

/-- Monotonicity of `Until` in the effect transformer. -/
theorem Until.mono_wp {ewp ewp' : StateEffectWP S E}
    {Hold Target : S → Prop} {Q : R → S → Prop} {t : ITree E R} {s : S}
    (h_wp : ∀ (i : E.I) (K : E.O i → S → Prop) (s₀ : S),
      ewp.wp i K s₀ → ewp'.wp i K s₀)
    (h : Until ewp Hold Target Q t s) : Until ewp' Hold Target Q t s := by
  refine Until.induct (fun x s₀ => Until ewp' Hold Target Q x s₀) ?_ h
  intro x s₀ hx
  rw [Until.unfold_eq]
  rcases hx with ht | ⟨hh, hx⟩
  · exact Or.inl ht
  · refine Or.inr ⟨hh, ?_⟩
    cases h_obs : x.observe <;> simp only [h_obs] at hx ⊢
    · exact hx
    · exact hx
    · exact h_wp _ _ _ hx

/-- The hold condition may always be added to the postcondition. -/
theorem Until.post_hold {ewp : StateEffectWP S E} {Hold Target : S → Prop}
    {Q : R → S → Prop} {t : ITree E R} {s : S}
    (h : Until ewp Hold Target Q t s) :
    Until ewp Hold Target (fun r s' => Hold s' ∧ Q r s') t s := by
  refine Until.induct
    (fun x s₀ => Until ewp Hold Target (fun r s' => Hold s' ∧ Q r s') x s₀) ?_ h
  intro x s₀ hx
  rw [Until.unfold_eq]
  rcases hx with ht | ⟨hh, hx⟩
  · exact Or.inl ht
  · refine Or.inr ⟨hh, ?_⟩
    cases h_obs : x.observe <;> simp only [h_obs] at hx ⊢
    · exact ⟨hh, hx⟩
    · exact hx
    · exact hx

/-- Monadic sequencing rule for `Until`. -/
theorem Until.bind {A B : Type u} {ewp : StateEffectWP S E}
    {Hold Target : S → Prop} {Q : B → S → Prop}
    {t : ITree E A} {k : A → ITree E B} {s : S}
    (h : Until ewp Hold Target
      (fun a s' => Until ewp Hold Target Q (k a) s') t s) :
    Until ewp Hold Target Q (t >>= k) s := by
  refine Until.induct
    (fun t₀ s₀ => Until ewp Hold Target Q (t₀ >>= k) s₀) ?_ h
  intro t₀ s₀ ht₀
  rcases ht₀ with h_tgt | ⟨h_hold, ht₀⟩
  · exact Until.here h_tgt
  · cases h_obs : t₀.observe with
    | ret a =>
      simp only [h_obs] at ht₀
      rw [eq_ret_of_observe h_obs, ret_bind]; exact ht₀
    | tau t₀' =>
      simp only [h_obs] at ht₀
      rw [eq_tau_of_observe h_obs, tau_bind]; exact Until.tau ht₀
    | vis i c =>
      simp only [h_obs] at ht₀
      rw [eq_vis_of_observe h_obs, vis_bind]; exact Until.vis h_hold ht₀

/-- Exact monadic bind characterisation for `Until`. -/
theorem Until.bind_iff {A B : Type u} (ewp : StateEffectWP S E)
    (Hold Target : S → Prop) (Q : B → S → Prop)
    (t : ITree E A) (k : A → ITree E B) (s : S) :
    Until ewp Hold Target Q (t >>= k) s ↔
      Until ewp Hold Target
        (fun a s' => Until ewp Hold Target Q (k a) s') t s := by
  refine ⟨fun h => ?_, Until.bind⟩
  refine Until.induct_strong
    (fun u s₀ => ∀ t₀ : ITree E A, u = (t₀ >>= k) →
      Until ewp Hold Target
        (fun a s' => Until ewp Hold Target Q (k a) s') t₀ s₀) ?_ h t rfl
  intro u s₀ hU hx t₀ h_eq
  subst h_eq
  rcases hx with ht | ⟨hh, hx⟩
  · exact Until.here ht
  · cases h_obs : t₀.observe with
    | ret a =>
      rw [eq_ret_of_observe h_obs, ret_bind] at hU
      rw [eq_ret_of_observe h_obs]
      exact Until.ret hh hU
    | tau t₀' =>
      rw [eq_tau_of_observe h_obs, tau_bind, ITree.observe_tau] at hx
      rw [eq_tau_of_observe h_obs]
      exact Until.tau (hx t₀' rfl)
    | vis i c =>
      rw [eq_vis_of_observe h_obs, vis_bind, ITree.observe_vis] at hx
      rw [eq_vis_of_observe h_obs]
      exact Until.vis hh (ewp.mono (fun o _ hp => hp (c o) rfl) hx)

/-- Conditional branching rule for `Until`. -/
theorem Until.ite {ewp : StateEffectWP S E} {Hold Target : S → Prop}
    {Q : R → S → Prop} {c : Prop} [Decidable c] {t₁ t₂ : ITree E R} {s : S}
    (h₁ : c → Until ewp Hold Target Q t₁ s)
    (h₂ : ¬ c → Until ewp Hold Target Q t₂ s) :
    Until ewp Hold Target Q (if c then t₁ else t₂) s := by
  split
  · exact h₁ ‹_›
  · exact h₂ ‹_›

/-- `Sum`-branching rule for `Until`. -/
theorem Until.sum_elim {A B : Type u} {ewp : StateEffectWP S E}
    {Hold Target : S → Prop} {Q : R → S → Prop}
    {f : A → ITree E R} {g : B → ITree E R} {s : S} (x : A ⊕ B)
    (h₁ : ∀ a, x = .inl a → Until ewp Hold Target Q (f a) s)
    (h₂ : ∀ b, x = .inr b → Until ewp Hold Target Q (g b) s) :
    Until ewp Hold Target Q (Sum.elim f g x) s := by
  cases x with
  | inl a => exact h₁ a rfl
  | inr b => exact h₂ b rfl

/--
Well-founded (`Acc`) loop rule for `Until`: the loop reaches the target or
exits with `Q` provided every iteration that continues decreases `R_lt`.
-/
theorem Until.iter_acc {I : Type u} {ewp : StateEffectWP S E}
    {Hold Target : S → Prop}
    (body : I → ITree E (I ⊕ R)) (R_lt : I → I → Prop)
    (LInv : I → S → Prop) {Q : R → S → Prop}
    (h_body : ∀ a s₀, LInv a s₀ →
      Until ewp Hold Target
        (Sum.elim (fun next s' => LInv next s' ∧ R_lt next a) Q) (body a) s₀)
    {init : I} (h_acc : Acc R_lt init) :
    ∀ {s : S}, LInv init s →
      Until ewp Hold Target Q (ITree.iter body init) s := by
  induction h_acc with
  | intro a _ ih =>
    intro s h_inv
    rw [iter_unfold]
    apply Until.bind
    refine Until.mono (fun _ h => h) (fun _ h => h) ?_
      (h_body a s h_inv).post_hold
    rintro (next | r) s' ⟨h_hold, h_post⟩
    · exact Until.tau (ih next h_post.2 h_post.1)
    · exact Until.ret h_hold h_post

/-- `Nat`-ranked loop rule for `Until` (bounded retry). -/
theorem Until.iter_ranked {I : Type u} {ewp : StateEffectWP S E}
    {Hold Target : S → Prop}
    (body : I → ITree E (I ⊕ R))
    (LInv : Nat → I → S → Prop) {Q : R → S → Prop}
    (h_zero : ∀ a s₀, LInv 0 a s₀ →
      Until ewp Hold Target (Sum.elim (fun _ _ => False) Q) (body a) s₀)
    (h_succ : ∀ n a s₀, LInv (n + 1) a s₀ →
      Until ewp Hold Target (Sum.elim (LInv n) Q) (body a) s₀) :
    (rank : Nat) → ∀ {a : I} {s : S},
      LInv rank a s → Until ewp Hold Target Q (ITree.iter body a) s
  | 0, a, s, h_inv => by
    rw [iter_unfold]; apply Until.bind
    refine Until.mono (fun _ h => h) (fun _ h => h) ?_
      (h_zero a s h_inv).post_hold
    rintro (_ | _) _ ⟨h_hold, hp⟩
    · exact False.elim hp
    · exact Until.ret h_hold hp
  | n + 1, a, s, h_inv => by
    rw [iter_unfold]; apply Until.bind
    refine Until.mono (fun _ h => h) (fun _ h => h) ?_
      (h_succ n a s h_inv).post_hold
    rintro (next | _) _ ⟨h_hold, hp⟩
    · exact Until.tau (Until.iter_ranked body LInv h_zero h_succ n hp)
    · exact Until.ret h_hold hp

/-- On `ITree.spin`, `Until` holds exactly when the target already holds. -/
theorem until_spin_iff (ewp : StateEffectWP S E) (Hold Target : S → Prop)
    (Q : R → S → Prop) (s : S) :
    Until ewp Hold Target Q (ITree.spin (E := E) (R := R)) s ↔ Target s := by
  refine ⟨fun h => ?_, Until.here⟩
  refine Until.induct (fun x s₀ => x = ITree.spin → Target s₀) ?_ h rfl
  rintro x s₀ (ht | ⟨_, hx⟩) rfl
  · exact ht
  · rw [observe_spin] at hx
    exact hx rfl

/-- `spin` refutation for `Until`: silent divergence never reaches the target. -/
theorem not_until_spin {ewp : StateEffectWP S E} {Hold Target : S → Prop}
    {Q : R → S → Prop} {s : S} (h : ¬ Target s) :
    ¬ Until ewp Hold Target Q (ITree.spin (E := E) (R := R)) s :=
  fun hu => h ((until_spin_iff ewp Hold Target Q s).1 hu)

/--
Total correctness yields `Until` whenever `ewp` maintains the hold condition
across every step.
-/
theorem until_of_dwp_invariant {ewp : StateEffectWP S E} {Hold : S → Prop}
    (h_pres : ∀ (i : E.I) (K : E.O i → S → Prop) (s₀ : S),
      Hold s₀ → ewp.wp i K s₀ → ewp.wp i (fun o s' => Hold s' ∧ K o s') s₀)
    (Target : S → Prop) {Q : R → S → Prop} {t : ITree E R} {s : S}
    (h_hold : Hold s) (h : DWP ewp t Q s) :
    Until ewp Hold Target Q t s := by
  refine DWP.induct
    (fun x s₀ => Hold s₀ → Until ewp Hold Target Q x s₀) ?_ h h_hold
  intro x s₀ hx hh
  rw [Until.unfold_eq]
  refine Or.inr ⟨hh, ?_⟩
  cases h_obs : x.observe <;> simp only [h_obs] at hx ⊢
  · exact hx
  · exact hx hh
  · exact ewp.mono (fun _ _ hp => hp.2 hp.1) (h_pres _ _ _ hh hx)

/--
Total correctness plus `Always` safety of the hold condition yields `Until`
under `[StateEffectWP.Conjunctive ewp]`.
-/
theorem until_of_dwp_always {ewp : StateEffectWP S E}
    [h_conj : StateEffectWP.Conjunctive ewp] {Hold : S → Prop}
    (Target : S → Prop) {P Q : R → S → Prop} {t : ITree E R} {s : S}
    (h_safe : Always ewp Hold P t s) (h : DWP ewp t Q s) :
    Until ewp Hold Target Q t s := by
  refine DWP.induct
    (fun x s₀ => Always ewp Hold P x s₀ → Until ewp Hold Target Q x s₀)
    ?_ h h_safe
  intro x s₀ hx ha
  rw [Always.unfold_eq] at ha
  obtain ⟨hh, ha⟩ := ha
  rw [Until.unfold_eq]
  refine Or.inr ⟨hh, ?_⟩
  cases h_obs : x.observe <;> simp only [h_obs] at hx ha ⊢
  · exact hx
  · exact hx ha
  · exact ewp.mono (fun _ _ hp => hp.1 hp.2) (h_conj.conj hx ha)

end Until

section Eventually

variable {S : Type u} {E : Effect.{u}} {R : Type u}

private def eventuallyAux (ewp : StateEffectWP S E) (Target : S → Prop)
    (Q : R → S → Prop) (t : ITree E R) (s : S) : Prop :=
  Target s ∨
    match t.observe with
    | .ret r => Q r s
    | .tau t' => eventuallyAux ewp Target Q t' s
    | .vis i k => ewp.wp i (fun o s' => eventuallyAux ewp Target Q (k o) s') s
inductive_fixpoint

/--
Inductive eventuality ($\Diamond$): on every path the target state predicate is
reached after finitely many steps, or the tree returns `r` with `Q r s`.
-/
def Eventually (ewp : StateEffectWP S E) (Target : S → Prop)
    (Q : R → S → Prop) (t : ITree E R) (s : S) : Prop :=
  eventuallyAux ewp Target Q t s

theorem Eventually.unfold_eq (ewp : StateEffectWP S E) (Target : S → Prop)
    (Q : R → S → Prop) (t : ITree E R) (s : S) :
    Eventually ewp Target Q t s =
      (Target s ∨
        match t.observe with
        | .ret r => Q r s
        | .tau t' => Eventually ewp Target Q t' s
        | .vis i k => ewp.wp i (fun o s' => Eventually ewp Target Q (k o) s') s) :=
  eventuallyAux.eq_def ewp Target Q t s

/-- Park induction principle for `Eventually`. -/
theorem Eventually.induct {ewp : StateEffectWP S E} {Target : S → Prop}
    {Q : R → S → Prop} (Pre : ITree E R → S → Prop)
    (h_closed : ∀ x s₀,
      (Target s₀ ∨
        match x.observe with
        | .ret r => Q r s₀
        | .tau x' => Pre x' s₀
        | .vis i k => ewp.wp i (fun o s' => Pre (k o) s') s₀) →
      Pre x s₀)
    {t : ITree E R} {s : S} (h : Eventually ewp Target Q t s) :
    Pre t s :=
  eventuallyAux.induct ewp Target Q Pre h_closed t s h

/-- `Eventually` is strong `Until` with a trivial hold condition. -/
theorem eventually_iff_until (ewp : StateEffectWP S E) (Target : S → Prop)
    (Q : R → S → Prop) (t : ITree E R) (s : S) :
    Eventually ewp Target Q t s ↔ Until ewp (fun _ => True) Target Q t s := by
  constructor
  · intro h
    refine Eventually.induct
      (fun x s₀ => Until ewp (fun _ => True) Target Q x s₀) ?_ h
    intro x s₀ hx
    rw [Until.unfold_eq]
    exact hx.imp id (fun hm => ⟨trivial, hm⟩)
  · intro h
    refine Until.induct (fun x s₀ => Eventually ewp Target Q x s₀) ?_ h
    intro x s₀ hx
    rw [Eventually.unfold_eq]
    exact hx.imp id And.right

/-- Every `Until` is in particular an `Eventually`. -/
theorem Until.toEventually {ewp : StateEffectWP S E} {Hold Target : S → Prop}
    {Q : R → S → Prop} {t : ITree E R} {s : S}
    (h : Until ewp Hold Target Q t s) : Eventually ewp Target Q t s :=
  (eventually_iff_until ewp Target Q t s).2
    (Until.mono (fun _ _ => trivial) (fun _ ht => ht) (fun _ _ hq => hq) h)

theorem Eventually.here {ewp : StateEffectWP S E} {Target : S → Prop}
    {Q : R → S → Prop} {t : ITree E R} {s : S} (h : Target s) :
    Eventually ewp Target Q t s := by
  rw [Eventually.unfold_eq]; exact Or.inl h

@[simp]
theorem Eventually.ret_iff (ewp : StateEffectWP S E) (Target : S → Prop)
    (Q : R → S → Prop) (r : R) (s : S) :
    Eventually ewp Target Q (.ret r) s ↔ Target s ∨ Q r s := by
  conv => lhs; rw [Eventually.unfold_eq, ITree.observe_ret]

@[simp]
theorem Eventually.tau_iff (ewp : StateEffectWP S E) (Target : S → Prop)
    (Q : R → S → Prop) (t : ITree E R) (s : S) :
    Eventually ewp Target Q (.tau t) s ↔ Eventually ewp Target Q t s := by
  conv => lhs; rw [Eventually.unfold_eq, ITree.observe_tau]
  exact ⟨fun h => h.elim Eventually.here id, Or.inr⟩

@[simp]
theorem Eventually.vis_iff (ewp : StateEffectWP S E) (Target : S → Prop)
    (Q : R → S → Prop) (i : E.I) (k : E.O i → ITree E R) (s : S) :
    Eventually ewp Target Q (.vis i k) s ↔
      Target s ∨ ewp.wp i (fun o s' => Eventually ewp Target Q (k o) s') s := by
  conv => lhs; rw [Eventually.unfold_eq, ITree.observe_vis]

theorem Eventually.ret {ewp : StateEffectWP S E} {Target : S → Prop}
    {Q : R → S → Prop} {r : R} {s : S} (hq : Q r s) :
    Eventually ewp Target Q (.ret r) s :=
  (Eventually.ret_iff ewp Target Q r s).2 (Or.inr hq)

theorem Eventually.tau {ewp : StateEffectWP S E} {Target : S → Prop}
    {Q : R → S → Prop} {t : ITree E R} {s : S}
    (h : Eventually ewp Target Q t s) : Eventually ewp Target Q (.tau t) s :=
  (Eventually.tau_iff ewp Target Q t s).2 h

theorem Eventually.vis {ewp : StateEffectWP S E} {Target : S → Prop}
    {Q : R → S → Prop} {i : E.I} {k : E.O i → ITree E R} {s : S}
    (hv : ewp.wp i (fun o s' => Eventually ewp Target Q (k o) s') s) :
    Eventually ewp Target Q (.vis i k) s :=
  (Eventually.vis_iff ewp Target Q i k s).2 (Or.inr hv)

/-- Weakening of the target and the postcondition. -/
theorem Eventually.mono {ewp : StateEffectWP S E} {Target Target' : S → Prop}
    {P Q : R → S → Prop} {t : ITree E R} {s : S}
    (h_tgt : ∀ s', Target s' → Target' s') (h_post : ∀ r s', P r s' → Q r s')
    (h : Eventually ewp Target P t s) : Eventually ewp Target' Q t s :=
  (eventually_iff_until ewp Target' Q t s).2
    (Until.mono (fun _ h => h) h_tgt h_post
      ((eventually_iff_until ewp Target P t s).1 h))

/-- Exact monadic bind characterisation for `Eventually`. -/
theorem Eventually.bind_iff {A B : Type u} (ewp : StateEffectWP S E)
    (Target : S → Prop) (Q : B → S → Prop)
    (t : ITree E A) (k : A → ITree E B) (s : S) :
    Eventually ewp Target Q (t >>= k) s ↔
      Eventually ewp Target
        (fun a s' => Eventually ewp Target Q (k a) s') t s := by
  refine (eventually_iff_until ewp Target Q (t >>= k) s).trans
    ((Until.bind_iff ewp _ Target Q t k s).trans
      (Iff.trans ?_ (eventually_iff_until ewp Target _ t s).symm))
  constructor <;>
    refine Until.mono (fun _ h => h) (fun _ h => h) fun a s' ha => ?_
  · exact (eventually_iff_until ewp Target Q (k a) s').2 ha
  · exact (eventually_iff_until ewp Target Q (k a) s').1 ha

/-- Monadic sequencing rule for `Eventually`. -/
theorem Eventually.bind {A B : Type u} {ewp : StateEffectWP S E}
    {Target : S → Prop} {Q : B → S → Prop}
    {t : ITree E A} {k : A → ITree E B} {s : S}
    (h : Eventually ewp Target
      (fun a s' => Eventually ewp Target Q (k a) s') t s) :
    Eventually ewp Target Q (t >>= k) s :=
  (Eventually.bind_iff ewp Target Q t k s).2 h

/-- Conditional branching rule for `Eventually`. -/
theorem Eventually.ite {ewp : StateEffectWP S E} {Target : S → Prop}
    {Q : R → S → Prop} {c : Prop} [Decidable c] {t₁ t₂ : ITree E R} {s : S}
    (h₁ : c → Eventually ewp Target Q t₁ s)
    (h₂ : ¬ c → Eventually ewp Target Q t₂ s) :
    Eventually ewp Target Q (if c then t₁ else t₂) s := by
  split
  · exact h₁ ‹_›
  · exact h₂ ‹_›

/-- `Sum`-branching rule for `Eventually`. -/
theorem Eventually.sum_elim {A B : Type u} {ewp : StateEffectWP S E}
    {Target : S → Prop} {Q : R → S → Prop}
    {f : A → ITree E R} {g : B → ITree E R} {s : S} (x : A ⊕ B)
    (h₁ : ∀ a, x = .inl a → Eventually ewp Target Q (f a) s)
    (h₂ : ∀ b, x = .inr b → Eventually ewp Target Q (g b) s) :
    Eventually ewp Target Q (Sum.elim f g x) s := by
  cases x with
  | inl a => exact h₁ a rfl
  | inr b => exact h₂ b rfl

/-- Total correctness implies eventuality of any target. -/
theorem eventually_of_dwp {ewp : StateEffectWP S E} (Target : S → Prop)
    {Q : R → S → Prop} {t : ITree E R} {s : S} (h : DWP ewp t Q s) :
    Eventually ewp Target Q t s := by
  refine DWP.induct (fun x s₀ => Eventually ewp Target Q x s₀) ?_ h
  intro x s₀ hx
  rw [Eventually.unfold_eq]
  exact Or.inr hx

/-- Terminating in a target state is in particular eventually reaching it. -/
theorem eventually_of_dwp_target {ewp : StateEffectWP S E} {Target : S → Prop}
    {t : ITree E R} {s : S} (h : DWP ewp t (fun _ s' => Target s') s) :
    Eventually ewp Target (fun _ s' => Target s') t s :=
  eventually_of_dwp Target h

/--
Well-founded (`Acc`) loop progress rule for `Eventually`: a retry loop whose
continuing iterations decrease `R_lt` eventually exits or hits the target.
-/
theorem Eventually.iter_acc {I : Type u} {ewp : StateEffectWP S E}
    {Target : S → Prop}
    (body : I → ITree E (I ⊕ R)) (R_lt : I → I → Prop)
    (LInv : I → S → Prop) {Q : R → S → Prop}
    (h_body : ∀ a s₀, LInv a s₀ →
      Eventually ewp Target
        (Sum.elim (fun next s' => LInv next s' ∧ R_lt next a) Q) (body a) s₀)
    {init : I} (h_acc : Acc R_lt init) {s : S} (h_init : LInv init s) :
    Eventually ewp Target Q (ITree.iter body init) s :=
  (eventually_iff_until ewp Target Q _ s).2
    (Until.iter_acc body R_lt LInv
      (fun a s₀ ha => (eventually_iff_until ewp Target _ _ s₀).1 (h_body a s₀ ha))
      h_acc h_init)

/--
`Nat`-ranked loop progress rule for `Eventually` (retry loops under bounded
contention: the rank bounds the number of remaining failed attempts).
-/
theorem Eventually.iter_ranked {I : Type u} {ewp : StateEffectWP S E}
    {Target : S → Prop}
    (body : I → ITree E (I ⊕ R))
    (LInv : Nat → I → S → Prop) {Q : R → S → Prop}
    (h_zero : ∀ a s₀, LInv 0 a s₀ →
      Eventually ewp Target (Sum.elim (fun _ _ => False) Q) (body a) s₀)
    (h_succ : ∀ n a s₀, LInv (n + 1) a s₀ →
      Eventually ewp Target (Sum.elim (LInv n) Q) (body a) s₀)
    (rank : Nat) {a : I} {s : S} (h_init : LInv rank a s) :
    Eventually ewp Target Q (ITree.iter body a) s :=
  (eventually_iff_until ewp Target Q _ s).2
    (Until.iter_ranked body LInv
      (fun a s₀ ha => (eventually_iff_until ewp Target _ _ s₀).1 (h_zero a s₀ ha))
      (fun n a s₀ ha =>
        (eventually_iff_until ewp Target _ _ s₀).1 (h_succ n a s₀ ha))
      rank h_init)

/-- On `ITree.spin`, `Eventually` holds exactly when the target already holds. -/
theorem eventually_spin_iff (ewp : StateEffectWP S E) (Target : S → Prop)
    (Q : R → S → Prop) (s : S) :
    Eventually ewp Target Q (ITree.spin (E := E) (R := R)) s ↔ Target s :=
  (eventually_iff_until ewp Target Q _ s).trans
    (until_spin_iff ewp (fun _ => True) Target Q s)

/-- `spin` refutation for `Eventually`. -/
theorem not_eventually_spin {ewp : StateEffectWP S E} {Target : S → Prop}
    {Q : R → S → Prop} {s : S} (h : ¬ Target s) :
    ¬ Eventually ewp Target Q (ITree.spin (E := E) (R := R)) s :=
  fun he => h ((eventually_spin_iff ewp Target Q s).1 he)

end Eventually

section EventuallyStep

variable {S : Type u} {E : Effect.{u}} {R : Type u}

private def eventuallyStepAux (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (t : ITree E R) (s : S) : Prop :=
  match t.observe with
  | .ret r => Q r s
  | .tau t' => eventuallyStepAux ewp AccEdge Q t' s
  | .vis i k =>
    ewp.wp i
      (fun o s' => AccEdge i o s s' ∨ eventuallyStepAux ewp AccEdge Q (k o) s') s
inductive_fixpoint

/--
Strict event-step eventuality: on every path the tree performs, after finitely
many steps, an accepting `.vis` transition `AccEdge i o s s'`, or returns `r`
with `Q r s`. Unlike `Eventually`, nothing is discharged in zero steps, so
silent `.tau` stuttering never satisfies it (`not_eventuallyStep_spin`).
-/
def EventuallyStep (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (t : ITree E R) (s : S) : Prop :=
  eventuallyStepAux ewp AccEdge Q t s

theorem EventuallyStep.unfold_eq (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (t : ITree E R) (s : S) :
    EventuallyStep ewp AccEdge Q t s =
      match t.observe with
      | .ret r => Q r s
      | .tau t' => EventuallyStep ewp AccEdge Q t' s
      | .vis i k =>
        ewp.wp i
          (fun o s' => AccEdge i o s s' ∨ EventuallyStep ewp AccEdge Q (k o) s') s :=
  eventuallyStepAux.eq_def ewp AccEdge Q t s

/-- Park induction principle for `EventuallyStep`. -/
theorem EventuallyStep.induct {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    (Pre : ITree E R → S → Prop)
    (h_closed : ∀ x s₀,
      (match x.observe with
       | .ret r => Q r s₀
       | .tau x' => Pre x' s₀
       | .vis i k => ewp.wp i (fun o s' => AccEdge i o s₀ s' ∨ Pre (k o) s') s₀) →
      Pre x s₀)
    {t : ITree E R} {s : S} (h : EventuallyStep ewp AccEdge Q t s) :
    Pre t s :=
  eventuallyStepAux.induct ewp AccEdge Q Pre h_closed t s h

@[simp]
theorem EventuallyStep.ret_iff (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (r : R) (s : S) :
    EventuallyStep ewp AccEdge Q (.ret r) s ↔ Q r s := by
  conv => lhs; rw [EventuallyStep.unfold_eq, ITree.observe_ret]

@[simp]
theorem EventuallyStep.tau_iff (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (t : ITree E R) (s : S) :
    EventuallyStep ewp AccEdge Q (.tau t) s ↔
      EventuallyStep ewp AccEdge Q t s := by
  conv => lhs; rw [EventuallyStep.unfold_eq, ITree.observe_tau]

@[simp]
theorem EventuallyStep.vis_iff (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (i : E.I) (k : E.O i → ITree E R) (s : S) :
    EventuallyStep ewp AccEdge Q (.vis i k) s ↔
      ewp.wp i
        (fun o s' => AccEdge i o s s' ∨ EventuallyStep ewp AccEdge Q (k o) s') s := by
  conv => lhs; rw [EventuallyStep.unfold_eq, ITree.observe_vis]

/-- Weakening of the accepting edges and the postcondition. -/
theorem EventuallyStep.mono {ewp : StateEffectWP S E}
    {AccEdge AccEdge' : (i : E.I) → E.O i → S → S → Prop}
    {P Q : R → S → Prop} {t : ITree E R} {s : S}
    (h_acc : ∀ i o s₀ s', AccEdge i o s₀ s' → AccEdge' i o s₀ s')
    (h_post : ∀ r s', P r s' → Q r s')
    (h : EventuallyStep ewp AccEdge P t s) :
    EventuallyStep ewp AccEdge' Q t s := by
  refine EventuallyStep.induct
    (fun x s₀ => EventuallyStep ewp AccEdge' Q x s₀) ?_ h
  intro x s₀ hx
  rw [EventuallyStep.unfold_eq]
  cases h_obs : x.observe <;> simp only [h_obs] at hx ⊢
  · exact h_post _ _ hx
  · exact hx
  · exact ewp.mono (fun _ _ hp => hp.imp (h_acc _ _ _ _) id) hx

/--
**Unconditional `spin` refutation** for strict step eventuality: no hypothesis
on the state, the accepting edges, or the postcondition is needed.
-/
theorem not_eventuallyStep_spin {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop} {s : S} :
    ¬ EventuallyStep ewp AccEdge Q (ITree.spin (E := E) (R := R)) s := by
  intro h
  refine EventuallyStep.induct (fun x _ => x ≠ ITree.spin) ?_ h rfl
  intro x _ hx rfl
  rw [observe_spin] at hx
  exact hx rfl

/-- Total correctness implies strict step eventuality. -/
theorem eventuallyStep_of_dwp {ewp : StateEffectWP S E}
    (AccEdge : (i : E.I) → E.O i → S → S → Prop)
    {Q : R → S → Prop} {t : ITree E R} {s : S} (h : DWP ewp t Q s) :
    EventuallyStep ewp AccEdge Q t s := by
  refine DWP.induct (fun x s₀ => EventuallyStep ewp AccEdge Q x s₀) ?_ h
  intro x s₀ hx
  rw [EventuallyStep.unfold_eq]
  cases h_obs : x.observe <;> simp only [h_obs] at hx ⊢
  · exact hx
  · exact hx
  · exact ewp.mono (fun _ _ hp => Or.inr hp) hx

/--
Strict step eventuality implies state eventuality of any target established
by every accepting edge.
-/
theorem EventuallyStep.toEventually {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Target : S → Prop}
    {Q : R → S → Prop} {t : ITree E R} {s : S}
    (h_acc : ∀ i o s₀ s', AccEdge i o s₀ s' → Target s')
    (h : EventuallyStep ewp AccEdge Q t s) : Eventually ewp Target Q t s := by
  refine EventuallyStep.induct (fun x s₀ => Eventually ewp Target Q x s₀) ?_ h
  intro x s₀ hx
  rw [Eventually.unfold_eq]
  refine Or.inr ?_
  cases h_obs : x.observe <;> simp only [h_obs] at hx ⊢
  · exact hx
  · exact hx
  · exact ewp.mono
      (fun _ _ hp => hp.elim (fun ha => Eventually.here (h_acc _ _ _ _ ha)) id) hx

/-- Monadic sequencing rule for `EventuallyStep`. -/
theorem EventuallyStep.bind {A B : Type u} {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : B → S → Prop}
    {t : ITree E A} {k : A → ITree E B} {s : S}
    (h : EventuallyStep ewp AccEdge
      (fun a s' => EventuallyStep ewp AccEdge Q (k a) s') t s) :
    EventuallyStep ewp AccEdge Q (t >>= k) s := by
  refine EventuallyStep.induct
    (fun t₀ s₀ => EventuallyStep ewp AccEdge Q (t₀ >>= k) s₀) ?_ h
  intro t₀ s₀ ht₀
  cases h_obs : t₀.observe with
  | ret a =>
    simp only [h_obs] at ht₀
    rw [eq_ret_of_observe h_obs, ret_bind]; exact ht₀
  | tau t₀' =>
    simp only [h_obs] at ht₀
    rw [eq_tau_of_observe h_obs, tau_bind, EventuallyStep.tau_iff]; exact ht₀
  | vis i c =>
    simp only [h_obs] at ht₀
    rw [eq_vis_of_observe h_obs, vis_bind, EventuallyStep.vis_iff]; exact ht₀

/-- Exact monadic bind characterisation for `EventuallyStep`. -/
theorem EventuallyStep.bind_iff {A B : Type u} (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : B → S → Prop)
    (t : ITree E A) (k : A → ITree E B) (s : S) :
    EventuallyStep ewp AccEdge Q (t >>= k) s ↔
      EventuallyStep ewp AccEdge
        (fun a s' => EventuallyStep ewp AccEdge Q (k a) s') t s := by
  refine ⟨fun h => ?_, EventuallyStep.bind⟩
  refine (EventuallyStep.induct
    (fun u s₀ => EventuallyStep ewp AccEdge Q u s₀ ∧
      ∀ t₀ : ITree E A, u = (t₀ >>= k) →
        EventuallyStep ewp AccEdge
          (fun a s' => EventuallyStep ewp AccEdge Q (k a) s') t₀ s₀) ?_ h).2
    t rfl
  intro u s₀ hx
  have hU : EventuallyStep ewp AccEdge Q u s₀ := by
    rw [EventuallyStep.unfold_eq]
    cases h_obs : u.observe <;> simp only [h_obs] at hx ⊢
    · exact hx
    · exact hx.1
    · exact ewp.mono (fun _ _ hp => hp.imp id And.left) hx
  refine ⟨hU, ?_⟩
  intro t₀ h_eq
  subst h_eq
  cases h_obs : t₀.observe with
  | ret a =>
    rw [eq_ret_of_observe h_obs, ret_bind] at hU
    rw [eq_ret_of_observe h_obs, EventuallyStep.ret_iff]
    exact hU
  | tau t₀' =>
    rw [eq_tau_of_observe h_obs, tau_bind, ITree.observe_tau] at hx
    rw [eq_tau_of_observe h_obs, EventuallyStep.tau_iff]
    exact hx.2 t₀' rfl
  | vis i c =>
    rw [eq_vis_of_observe h_obs, vis_bind, ITree.observe_vis] at hx
    rw [eq_vis_of_observe h_obs, EventuallyStep.vis_iff]
    exact ewp.mono (fun o _ hp => hp.imp id (fun hpre => hpre.2 (c o) rfl)) hx

/-- Total correctness is strong `Until` with trivial hold and no target. -/
theorem dwp_iff_until (ewp : StateEffectWP S E) (Q : R → S → Prop)
    (t : ITree E R) (s : S) :
    DWP ewp t Q s ↔ Until ewp (fun _ => True) (fun _ => False) Q t s := by
  constructor
  · intro h
    refine DWP.induct
      (fun x s₀ => Until ewp (fun _ => True) (fun _ => False) Q x s₀) ?_ h
    intro x s₀ hx
    rw [Until.unfold_eq]
    exact Or.inr ⟨trivial, hx⟩
  · intro h
    refine Until.induct (fun x s₀ => DWP ewp x Q s₀) ?_ h
    intro x s₀ hx
    rw [DWP.unfold_eq]
    exact hx.elim False.elim And.right

/-- Exact monadic bind characterisation for `DWP`. -/
theorem dwp_bind_iff {A B : Type u} (ewp : StateEffectWP S E)
    (t : ITree E A) (k : A → ITree E B) (Q : B → S → Prop) (s : S) :
    DWP ewp (t >>= k) Q s ↔ DWP ewp t (fun a s' => DWP ewp (k a) Q s') s := by
  refine (dwp_iff_until ewp Q (t >>= k) s).trans
    ((Until.bind_iff ewp _ _ Q t k s).trans
      (Iff.trans ?_ (dwp_iff_until ewp _ t s).symm))
  constructor <;>
    refine Until.mono (fun _ h => h) (fun _ h => h) fun a s' ha => ?_
  · exact (dwp_iff_until ewp Q (k a) s').2 ha
  · exact (dwp_iff_until ewp Q (k a) s').1 ha

end EventuallyStep

/-! ## 3. Nested-Fixpoint `InfOften` ($\Box\Diamond$) and Büchi Acceptance -/

section BuchiProgress

variable {S : Type u} {E : Effect.{u}} {R : Type u}

private def buchiProgressAux (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (Rec : ITree E R → S → Prop) (t : ITree E R) (s : S) : Prop :=
  match t.observe with
  | .ret r => Q r s
  | .tau t' => buchiProgressAux ewp AccEdge Q Rec t' s
  | .vis i k =>
    ewp.wp i
      (fun o s' => (AccEdge i o s s' ∧ Rec (k o) s') ∨
        buchiProgressAux ewp AccEdge Q Rec (k o) s') s
inductive_fixpoint

/--
Inner inductive progress transformer ($\mu Y$) of the Büchi fixpoint: the tree
returns `r` with `Q r s`, or after finitely many `.tau` / non-accepting `.vis`
steps performs an accepting transition `AccEdge i o s s'` whose residual
configuration satisfies the outer continuation `Rec`.
-/
def buchiProgress (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (Rec : ITree E R → S → Prop) (t : ITree E R) (s : S) : Prop :=
  buchiProgressAux ewp AccEdge Q Rec t s

theorem buchiProgress.unfold_eq (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (Rec : ITree E R → S → Prop) (t : ITree E R) (s : S) :
    buchiProgress ewp AccEdge Q Rec t s =
      match t.observe with
      | .ret r => Q r s
      | .tau t' => buchiProgress ewp AccEdge Q Rec t' s
      | .vis i k =>
        ewp.wp i
          (fun o s' => (AccEdge i o s s' ∧ Rec (k o) s') ∨
            buchiProgress ewp AccEdge Q Rec (k o) s') s :=
  buchiProgressAux.eq_def ewp AccEdge Q Rec t s

/-- Park induction principle for `buchiProgress`. -/
theorem buchiProgress.induct {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {Rec : ITree E R → S → Prop} (Pre : ITree E R → S → Prop)
    (h_closed : ∀ x s₀,
      (match x.observe with
       | .ret r => Q r s₀
       | .tau x' => Pre x' s₀
       | .vis i k =>
         ewp.wp i
           (fun o s' => (AccEdge i o s₀ s' ∧ Rec (k o) s') ∨ Pre (k o) s') s₀) →
      Pre x s₀)
    {t : ITree E R} {s : S} (h : buchiProgress ewp AccEdge Q Rec t s) :
    Pre t s :=
  buchiProgressAux.induct ewp AccEdge Q Rec Pre h_closed t s h

@[simp]
theorem buchiProgress.ret_iff (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (Rec : ITree E R → S → Prop) (r : R) (s : S) :
    buchiProgress ewp AccEdge Q Rec (.ret r) s ↔ Q r s := by
  conv => lhs; rw [buchiProgress.unfold_eq, ITree.observe_ret]

@[simp]
theorem buchiProgress.tau_iff (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (Rec : ITree E R → S → Prop) (t : ITree E R) (s : S) :
    buchiProgress ewp AccEdge Q Rec (.tau t) s ↔
      buchiProgress ewp AccEdge Q Rec t s := by
  conv => lhs; rw [buchiProgress.unfold_eq, ITree.observe_tau]

@[simp]
theorem buchiProgress.vis_iff (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (Rec : ITree E R → S → Prop) (i : E.I) (k : E.O i → ITree E R) (s : S) :
    buchiProgress ewp AccEdge Q Rec (.vis i k) s ↔
      ewp.wp i
        (fun o s' => (AccEdge i o s s' ∧ Rec (k o) s') ∨
          buchiProgress ewp AccEdge Q Rec (k o) s') s := by
  conv => lhs; rw [buchiProgress.unfold_eq, ITree.observe_vis]

/-- Introduction rule: an accepting `.vis` step into the continuation `Rec`. -/
theorem buchiProgress.vis_accept {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {Rec : ITree E R → S → Prop} {i : E.I} {k : E.O i → ITree E R} {s : S}
    (hv : ewp.wp i (fun o s' => AccEdge i o s s' ∧ Rec (k o) s') s) :
    buchiProgress ewp AccEdge Q Rec (.vis i k) s :=
  (buchiProgress.vis_iff ewp AccEdge Q Rec i k s).2
    (ewp.mono (fun _ _ hp => Or.inl hp) hv)

/-- Introduction rule: a non-accepting `.vis` step that keeps making progress. -/
theorem buchiProgress.vis_skip {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {Rec : ITree E R → S → Prop} {i : E.I} {k : E.O i → ITree E R} {s : S}
    (hv : ewp.wp i (fun o s' => buchiProgress ewp AccEdge Q Rec (k o) s') s) :
    buchiProgress ewp AccEdge Q Rec (.vis i k) s :=
  (buchiProgress.vis_iff ewp AccEdge Q Rec i k s).2
    (ewp.mono (fun _ _ hp => Or.inr hp) hv)

/--
Monotonicity of `buchiProgress` in the transformer, the accepting edges, the
postcondition and the outer continuation `Rec`.
-/
theorem buchiProgress.mono {ewp ewp' : StateEffectWP S E}
    {AccEdge AccEdge' : (i : E.I) → E.O i → S → S → Prop}
    {P Q : R → S → Prop} {Rec Rec' : ITree E R → S → Prop}
    {t : ITree E R} {s : S}
    (h_wp : ∀ (i : E.I) (K : E.O i → S → Prop) (s₀ : S),
      ewp.wp i K s₀ → ewp'.wp i K s₀)
    (h_acc : ∀ i o s₀ s', AccEdge i o s₀ s' → AccEdge' i o s₀ s')
    (h_post : ∀ r s', P r s' → Q r s')
    (h_rec : ∀ x s', Rec x s' → Rec' x s')
    (h : buchiProgress ewp AccEdge P Rec t s) :
    buchiProgress ewp' AccEdge' Q Rec' t s := by
  refine buchiProgress.induct
    (fun x s₀ => buchiProgress ewp' AccEdge' Q Rec' x s₀) ?_ h
  intro x s₀ hx
  rw [buchiProgress.unfold_eq]
  cases h_obs : x.observe <;> simp only [h_obs] at hx ⊢
  · exact h_post _ _ hx
  · exact hx
  · exact h_wp _ _ _ (ewp.mono
      (fun _ _ hp => hp.imp (And.imp (h_acc _ _ _ _) (h_rec _ _)) id) hx)

/-- Monotonicity of `buchiProgress` in the outer continuation only. -/
theorem buchiProgress.mono_rec {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {Rec Rec' : ITree E R → S → Prop} {t : ITree E R} {s : S}
    (h_rec : ∀ x s', Rec x s' → Rec' x s')
    (h : buchiProgress ewp AccEdge Q Rec t s) :
    buchiProgress ewp AccEdge Q Rec' t s :=
  buchiProgress.mono (fun _ _ _ hw => hw) (fun _ _ _ _ ha => ha)
    (fun _ _ hq => hq) h_rec h

/--
`buchiProgress` is monotone in its outer continuation `Rec` for the
`coinductive_fixpoint` order, enabling the nested $\nu X.\,\mu Y$ definition of
`InfOften`.
-/
@[partial_fixpoint_monotone]
theorem buchiProgress.monotone_coind (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    {α : Type _} [Lean.Order.PartialOrder α] (t : ITree E R) (s : S)
    (f : α → ITree E R → S → Lean.Order.ReverseImplicationOrder)
    (hf : Lean.Order.monotone f) :
    @Lean.Order.monotone _ _ _ Lean.Order.ReverseImplicationOrder.instOrder
      (fun x => buchiProgress ewp AccEdge Q (f x) t s) :=
  fun x y hxy h =>
    buchiProgress.mono_rec (fun t' s' hr => hf x y hxy t' s' hr) h

/-- Monotonicity in `Rec` for the `inductive_fixpoint` order. -/
@[partial_fixpoint_monotone]
theorem buchiProgress.monotone_ind (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    {α : Type _} [Lean.Order.PartialOrder α] (t : ITree E R) (s : S)
    (f : α → ITree E R → S → Lean.Order.ImplicationOrder)
    (hf : Lean.Order.monotone f) :
    @Lean.Order.monotone _ _ _ Lean.Order.ImplicationOrder.instOrder
      (fun x => buchiProgress ewp AccEdge Q (f x) t s) :=
  fun x y hxy h =>
    buchiProgress.mono_rec (fun t' s' hr => hf x y hxy t' s' hr) h

/-- Total correctness implies `buchiProgress` for any continuation. -/
theorem buchiProgress.of_dwp {ewp : StateEffectWP S E}
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) {Q : R → S → Prop}
    (Rec : ITree E R → S → Prop) {t : ITree E R} {s : S}
    (h : DWP ewp t Q s) : buchiProgress ewp AccEdge Q Rec t s := by
  refine DWP.induct (fun x s₀ => buchiProgress ewp AccEdge Q Rec x s₀) ?_ h
  intro x s₀ hx
  rw [buchiProgress.unfold_eq]
  cases h_obs : x.observe <;> simp only [h_obs] at hx ⊢
  · exact hx
  · exact hx
  · exact ewp.mono (fun _ _ hp => Or.inr hp) hx

/-- Without accepting edges `buchiProgress` degenerates to `DWP`. -/
theorem buchiProgress_false_iff_dwp (ewp : StateEffectWP S E)
    (Q : R → S → Prop) (Rec : ITree E R → S → Prop) (t : ITree E R) (s : S) :
    buchiProgress ewp (fun _ _ _ _ => False) Q Rec t s ↔ DWP ewp t Q s := by
  refine ⟨fun h => ?_, buchiProgress.of_dwp _ Rec⟩
  refine buchiProgress.induct (fun x s₀ => DWP ewp x Q s₀) ?_ h
  intro x s₀ hx
  rw [DWP.unfold_eq]
  cases h_obs : x.observe <;> simp only [h_obs] at hx ⊢
  · exact hx
  · exact hx
  · exact ewp.mono (fun _ _ hp => hp.elim (fun ha => ha.1.elim) id) hx

/-- With a trivial continuation `buchiProgress` is strict step eventuality. -/
theorem eventuallyStep_iff_buchiProgress (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (t : ITree E R) (s : S) :
    EventuallyStep ewp AccEdge Q t s ↔
      buchiProgress ewp AccEdge Q (fun _ _ => True) t s := by
  constructor
  · intro h
    refine EventuallyStep.induct
      (fun x s₀ => buchiProgress ewp AccEdge Q (fun _ _ => True) x s₀) ?_ h
    intro x s₀ hx
    rw [buchiProgress.unfold_eq]
    cases h_obs : x.observe <;> simp only [h_obs] at hx ⊢
    · exact hx
    · exact hx
    · exact ewp.mono (fun _ _ hp => hp.imp (fun ha => ⟨ha, trivial⟩) id) hx
  · intro h
    refine buchiProgress.induct
      (fun x s₀ => EventuallyStep ewp AccEdge Q x s₀) ?_ h
    intro x s₀ hx
    rw [EventuallyStep.unfold_eq]
    cases h_obs : x.observe <;> simp only [h_obs] at hx ⊢
    · exact hx
    · exact hx
    · exact ewp.mono (fun _ _ hp => hp.imp And.left id) hx

/--
General sequencing rule for `buchiProgress`: the prefix either returns into a
continuation that itself makes progress, or takes an accepting edge after
which the *sequenced* residual satisfies `Rec`.
-/
theorem buchiProgress.bind {A B : Type u} {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : B → S → Prop}
    {Rec : ITree E B → S → Prop} {t : ITree E A} {k : A → ITree E B} {s : S}
    (h : buchiProgress ewp AccEdge
      (fun a s' => buchiProgress ewp AccEdge Q Rec (k a) s')
      (fun t' s' => Rec (t' >>= k) s') t s) :
    buchiProgress ewp AccEdge Q Rec (t >>= k) s := by
  refine buchiProgress.induct
    (fun t₀ s₀ => buchiProgress ewp AccEdge Q Rec (t₀ >>= k) s₀) ?_ h
  intro t₀ s₀ ht₀
  cases h_obs : t₀.observe with
  | ret a =>
    simp only [h_obs] at ht₀
    rw [eq_ret_of_observe h_obs, ret_bind]; exact ht₀
  | tau t₀' =>
    simp only [h_obs] at ht₀
    rw [eq_tau_of_observe h_obs, tau_bind, buchiProgress.tau_iff]; exact ht₀
  | vis i c =>
    simp only [h_obs] at ht₀
    rw [eq_vis_of_observe h_obs, vis_bind, buchiProgress.vis_iff]; exact ht₀

end BuchiProgress

section InfOften

variable {S : Type u} {E : Effect.{u}} {R : Type u}

private def infOftenAux (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (t : ITree E R) (s : S) : Prop :=
  buchiProgress ewp AccEdge Q (infOftenAux ewp AccEdge Q) t s
coinductive_fixpoint

/--
Büchi recurrence ($\Box\Diamond$) as the nested fixpoint
$\nu X.\,\mu Y$ `buchiProgress X`: every path either returns `r` with `Q r s`
after finitely many steps, or takes accepting `AccEdge` transitions infinitely
often. Finite `.tau` stuttering is permitted between accepting edges, while
infinite silent divergence is rejected (`not_infOften_spin`).
-/
def InfOften (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (t : ITree E R) (s : S) : Prop :=
  infOftenAux ewp AccEdge Q t s

/-- State-predicate specialisation: an edge accepts when its target state does. -/
def InfOftenState (ewp : StateEffectWP S E) (AccState : S → Prop)
    (Q : R → S → Prop) (t : ITree E R) (s : S) : Prop :=
  InfOften ewp (fun _ _ _ s' => AccState s') Q t s

theorem InfOften.unfold_eq (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (t : ITree E R) (s : S) :
    InfOften ewp AccEdge Q t s =
      buchiProgress ewp AccEdge Q (InfOften ewp AccEdge Q) t s :=
  infOftenAux.eq_def ewp AccEdge Q t s

/-- Park coinduction principle for the outer greatest fixed point of `InfOften`. -/
theorem InfOften.coinduct {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    (X : ITree E R → S → Prop)
    (h_step : ∀ x s₀, X x s₀ → buchiProgress ewp AccEdge Q X x s₀)
    {t : ITree E R} {s : S} (h_init : X t s) :
    InfOften ewp AccEdge Q t s :=
  infOftenAux.coinduct ewp AccEdge Q X h_step t s h_init

/-- Folding one layer of progress back into `InfOften`. -/
theorem InfOften.of_buchiProgress {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t : ITree E R} {s : S}
    (h : buchiProgress ewp AccEdge Q (InfOften ewp AccEdge Q) t s) :
    InfOften ewp AccEdge Q t s := by
  rw [InfOften.unfold_eq]; exact h

/-- Unfolding `InfOften` into one layer of progress. -/
theorem InfOften.toBuchiProgress {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t : ITree E R} {s : S} (h : InfOften ewp AccEdge Q t s) :
    buchiProgress ewp AccEdge Q (InfOften ewp AccEdge Q) t s := by
  rw [InfOften.unfold_eq] at h; exact h

@[simp]
theorem InfOften.ret_iff (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (r : R) (s : S) :
    InfOften ewp AccEdge Q (.ret r) s ↔ Q r s := by
  rw [InfOften.unfold_eq, buchiProgress.ret_iff]

@[simp]
theorem InfOften.tau_iff (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (t : ITree E R) (s : S) :
    InfOften ewp AccEdge Q (.tau t) s ↔ InfOften ewp AccEdge Q t s := by
  rw [InfOften.unfold_eq, buchiProgress.tau_iff, ← InfOften.unfold_eq]

/--
The defining `.vis` clause of `InfOften`: after an accepting edge the residual
satisfies `InfOften` again; otherwise it keeps making inductive progress.
-/
theorem InfOften.vis_unfold (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (i : E.I) (k : E.O i → ITree E R) (s : S) :
    InfOften ewp AccEdge Q (.vis i k) s ↔
      ewp.wp i
        (fun o s' => (AccEdge i o s s' ∧ InfOften ewp AccEdge Q (k o) s') ∨
          buchiProgress ewp AccEdge Q (InfOften ewp AccEdge Q) (k o) s') s := by
  rw [InfOften.unfold_eq, buchiProgress.vis_iff]

/--
`InfOften` is a fixed point of the one-step functor: a `.vis` node satisfies it
exactly when every answer admitted by `ewp` leads to a residual that does.
-/
@[simp]
theorem InfOften.vis_iff (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (i : E.I) (k : E.O i → ITree E R) (s : S) :
    InfOften ewp AccEdge Q (.vis i k) s ↔
      ewp.wp i (fun o s' => InfOften ewp AccEdge Q (k o) s') s := by
  rw [InfOften.vis_unfold]
  constructor
  · exact ewp.mono (fun _ _ hp => hp.elim And.right InfOften.of_buchiProgress)
  · exact ewp.mono (fun _ _ hp => Or.inr hp.toBuchiProgress)

theorem InfOften.ret {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {r : R} {s : S} (hq : Q r s) : InfOften ewp AccEdge Q (.ret r) s :=
  (InfOften.ret_iff ewp AccEdge Q r s).2 hq

theorem InfOften.tau {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t : ITree E R} {s : S} (h : InfOften ewp AccEdge Q t s) :
    InfOften ewp AccEdge Q (.tau t) s :=
  (InfOften.tau_iff ewp AccEdge Q t s).2 h

theorem InfOften.vis {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {i : E.I} {k : E.O i → ITree E R} {s : S}
    (hv : ewp.wp i (fun o s' => InfOften ewp AccEdge Q (k o) s') s) :
    InfOften ewp AccEdge Q (.vis i k) s :=
  (InfOften.vis_iff ewp AccEdge Q i k s).2 hv

/--
Inner induction principle for `InfOften`: to establish `Pre` at every
`InfOften` configuration one may assume, at each child, `InfOften` itself and
that the child was either entered through an accepting edge or already
satisfies `Pre`.
-/
theorem InfOften.progress_induct {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    (Pre : ITree E R → S → Prop)
    (h_closed : ∀ x s₀,
      (match x.observe with
       | .ret r => Q r s₀
       | .tau x' => InfOften ewp AccEdge Q x' s₀ ∧ Pre x' s₀
       | .vis i k =>
         ewp.wp i
           (fun o s' => InfOften ewp AccEdge Q (k o) s' ∧
             (AccEdge i o s₀ s' ∨ Pre (k o) s')) s₀) →
      Pre x s₀)
    {t : ITree E R} {s : S} (h : InfOften ewp AccEdge Q t s) :
    Pre t s := by
  refine (buchiProgress.induct
    (fun x s₀ => InfOften ewp AccEdge Q x s₀ ∧ Pre x s₀) ?_
    h.toBuchiProgress).2
  intro x s₀ hx
  have hm : match x.observe with
      | .ret r => Q r s₀
      | .tau x' => InfOften ewp AccEdge Q x' s₀ ∧ Pre x' s₀
      | .vis i k =>
        ewp.wp i
          (fun o s' => InfOften ewp AccEdge Q (k o) s' ∧
            (AccEdge i o s₀ s' ∨ Pre (k o) s')) s₀ := by
    cases h_obs : x.observe <;> simp only [h_obs] at hx ⊢
    · exact hx
    · exact hx
    · exact ewp.mono
        (fun _ _ hp => hp.elim (fun ha => ⟨ha.2, Or.inl ha.1⟩)
          (fun hp' => ⟨hp'.1, Or.inr hp'.2⟩)) hx
  refine ⟨?_, h_closed x s₀ hm⟩
  cases h_obs : x.observe with
  | ret r =>
    simp only [h_obs] at hm
    rw [eq_ret_of_observe h_obs, InfOften.ret_iff]; exact hm
  | tau x' =>
    simp only [h_obs] at hm
    rw [eq_tau_of_observe h_obs, InfOften.tau_iff]; exact hm.1
  | vis i k =>
    simp only [h_obs] at hm
    rw [eq_vis_of_observe h_obs, InfOften.vis_iff]
    exact ewp.mono (fun _ _ hp => hp.1) hm

/--
Monotonicity of `InfOften` in the transformer, the accepting edges and the
postcondition.
-/
theorem InfOften.mono {ewp ewp' : StateEffectWP S E}
    {AccEdge AccEdge' : (i : E.I) → E.O i → S → S → Prop}
    {P Q : R → S → Prop} {t : ITree E R} {s : S}
    (h_wp : ∀ (i : E.I) (K : E.O i → S → Prop) (s₀ : S),
      ewp.wp i K s₀ → ewp'.wp i K s₀)
    (h_acc : ∀ i o s₀ s', AccEdge i o s₀ s' → AccEdge' i o s₀ s')
    (h_post : ∀ r s', P r s' → Q r s')
    (h : InfOften ewp AccEdge P t s) : InfOften ewp' AccEdge' Q t s := by
  refine InfOften.coinduct (fun x s₀ => InfOften ewp AccEdge P x s₀) ?_ h
  intro x s₀ hx
  exact buchiProgress.mono h_wp h_acc h_post (fun _ _ hr => hr)
    hx.toBuchiProgress

/-- Postcondition weakening for `InfOften`. -/
theorem InfOften.mono_post {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop}
    {P Q : R → S → Prop} {t : ITree E R} {s : S}
    (h_post : ∀ r s', P r s' → Q r s')
    (h : InfOften ewp AccEdge P t s) : InfOften ewp AccEdge Q t s :=
  InfOften.mono (fun _ _ _ hw => hw) (fun _ _ _ _ ha => ha) h_post h

/--
**Unconditional `spin` refutation** for `InfOften`: silent divergence never
satisfies Büchi recurrence, whatever the accepting edges, postcondition, or
state.
-/
theorem not_infOften_spin {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop} {s : S} :
    ¬ InfOften ewp AccEdge Q (ITree.spin (E := E) (R := R)) s := by
  intro h
  refine buchiProgress.induct (fun x _ => x ≠ ITree.spin) ?_
    h.toBuchiProgress rfl
  intro x _ hx rfl
  rw [observe_spin] at hx
  exact hx rfl

/-- **`DWP` embedding**: total correctness implies Büchi recurrence. -/
theorem infOften_of_dwp {ewp : StateEffectWP S E}
    (AccEdge : (i : E.I) → E.O i → S → S → Prop)
    {Q : R → S → Prop} {t : ITree E R} {s : S} (h : DWP ewp t Q s) :
    InfOften ewp AccEdge Q t s :=
  InfOften.coinduct (fun x s₀ => DWP ewp x Q s₀)
    (fun _ _ hx => buchiProgress.of_dwp AccEdge _ hx) h

/-- Büchi recurrence implies partial correctness. -/
theorem InfOften.toDWLP {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop}
    {Q : R → S → Prop} {t : ITree E R} {s : S}
    (h : InfOften ewp AccEdge Q t s) : DWLP ewp t Q s := by
  refine DWLP.coinduct (fun x s₀ => InfOften ewp AccEdge Q x s₀) ?_ h
  intro x s₀ hx
  cases h_obs : x.observe with
  | ret r =>
    rw [eq_ret_of_observe h_obs, InfOften.ret_iff] at hx; exact hx
  | tau x' =>
    rw [eq_tau_of_observe h_obs, InfOften.tau_iff] at hx; exact hx
  | vis i k =>
    rw [eq_vis_of_observe h_obs, InfOften.vis_iff] at hx; exact hx

/-- Büchi recurrence implies strict step eventuality at the current node. -/
theorem InfOften.toEventuallyStep {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop}
    {Q : R → S → Prop} {t : ITree E R} {s : S}
    (h : InfOften ewp AccEdge Q t s) : EventuallyStep ewp AccEdge Q t s :=
  (eventuallyStep_iff_buchiProgress ewp AccEdge Q t s).2
    (buchiProgress.mono_rec (fun _ _ _ => trivial) h.toBuchiProgress)

/--
State-based Büchi recurrence implies eventuality of the accepting state
predicate (or a `Q`-return).
-/
theorem InfOftenState.toEventually {ewp : StateEffectWP S E}
    {AccState : S → Prop} {Q : R → S → Prop} {t : ITree E R} {s : S}
    (h : InfOftenState ewp AccState Q t s) : Eventually ewp AccState Q t s :=
  EventuallyStep.toEventually (fun _ _ _ _ ha => ha)
    (InfOften.toEventuallyStep h)

/-- `spin` refutation for state-based Büchi recurrence. -/
theorem not_infOftenState_spin {ewp : StateEffectWP S E}
    {AccState : S → Prop} {Q : R → S → Prop} {s : S} :
    ¬ InfOftenState ewp AccState Q (ITree.spin (E := E) (R := R)) s :=
  not_infOften_spin

/--
Without accepting edges, and for a non-miraculous transformer, a tree that
never returns cannot satisfy `InfOften`: recurrence genuinely needs accepting
transitions.
-/
theorem not_infOften_of_no_accept {ewp : StateEffectWP S E}
    [h_em : StateEffectWP.ExcludedMiracle ewp] (h_empty : R → False)
    {Q : R → S → Prop} {t : ITree E R} {s : S} :
    ¬ InfOften ewp (fun _ _ _ _ => False) Q t s := by
  intro h
  refine buchiProgress.induct (fun _ _ => False) ?_ h.toBuchiProgress
  intro x _ hx
  cases h_obs : x.observe with
  | ret r => exact h_empty r
  | tau x' => rw [h_obs] at hx; exact hx
  | vis i k =>
    rw [h_obs] at hx
    exact h_em.no_miracle
      (ewp.mono (fun _ _ hp => hp.elim (fun ha => ha.1) id) hx)

/--
**Compositionality** (general prefix): an `InfOften` prefix whose returns land
in `InfOften` continuations yields `InfOften` of the sequenced tree.
-/
theorem InfOften.bind {A B : Type u} {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : B → S → Prop}
    {t : ITree E A} {k : A → ITree E B} {s : S}
    (h : InfOften ewp AccEdge
      (fun a s' => InfOften ewp AccEdge Q (k a) s') t s) :
    InfOften ewp AccEdge Q (t >>= k) s := by
  refine InfOften.coinduct
    (fun u s₀ => InfOften ewp AccEdge Q u s₀ ∨
      ∃ t₀ : ITree E A, u = (t₀ >>= k) ∧
        InfOften ewp AccEdge
          (fun a s' => InfOften ewp AccEdge Q (k a) s') t₀ s₀)
    ?_ (Or.inr ⟨t, rfl, h⟩)
  rintro u s₀ (hu | ⟨t₀, rfl, ht₀⟩)
  · exact buchiProgress.mono_rec (fun _ _ hr => Or.inl hr) hu.toBuchiProgress
  · refine buchiProgress.bind
      (buchiProgress.mono (fun _ _ _ hw => hw) (fun _ _ _ _ ha => ha)
        ?_ ?_ ht₀.toBuchiProgress)
    · intro a s' ha
      exact buchiProgress.mono_rec (fun _ _ hr => Or.inl hr) ha.toBuchiProgress
    · intro t' s' ht'
      exact Or.inr ⟨t', rfl, ht'⟩

/-- **Compositionality** (`DWP` prefix followed by an `InfOften` continuation). -/
theorem InfOften.bind_dwp {A B : Type u} {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : B → S → Prop}
    {t : ITree E A} {k : A → ITree E B} {s : S}
    (h : DWP ewp t (fun a s' => InfOften ewp AccEdge Q (k a) s') s) :
    InfOften ewp AccEdge Q (t >>= k) s :=
  InfOften.bind (infOften_of_dwp AccEdge h)

/-- Exact monadic bind characterisation for `InfOften`. -/
theorem InfOften.bind_iff {A B : Type u} (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : B → S → Prop)
    (t : ITree E A) (k : A → ITree E B) (s : S) :
    InfOften ewp AccEdge Q (t >>= k) s ↔
      InfOften ewp AccEdge
        (fun a s' => InfOften ewp AccEdge Q (k a) s') t s := by
  refine ⟨fun h => ?_, InfOften.bind⟩
  refine InfOften.coinduct
    (fun t₀ s₀ => InfOften ewp AccEdge Q (t₀ >>= k) s₀) ?_ h
  intro t₀ s₀ ht₀
  refine InfOften.progress_induct
    (fun u s₁ => ∀ t₁ : ITree E A, u = (t₁ >>= k) →
      buchiProgress ewp AccEdge
        (fun a s' => InfOften ewp AccEdge Q (k a) s')
        (fun t₂ s₂ => InfOften ewp AccEdge Q (t₂ >>= k) s₂) t₁ s₁)
    ?_ ht₀ t₀ rfl
  intro u s₁ hx t₁ h_eq
  subst h_eq
  cases h_obs : t₁.observe with
  | ret a =>
    rw [eq_ret_of_observe h_obs, ret_bind] at hx
    rw [eq_ret_of_observe h_obs, buchiProgress.ret_iff]
    cases hk : (k a).observe with
    | ret b =>
      simp only [hk] at hx
      rw [eq_ret_of_observe hk, InfOften.ret_iff]; exact hx
    | tau u' =>
      simp only [hk] at hx
      rw [eq_tau_of_observe hk, InfOften.tau_iff]; exact hx.1
    | vis j c =>
      simp only [hk] at hx
      rw [eq_vis_of_observe hk, InfOften.vis_iff]
      exact ewp.mono (fun _ _ hp => hp.1) hx
  | tau t₁' =>
    rw [eq_tau_of_observe h_obs, tau_bind, ITree.observe_tau] at hx
    rw [eq_tau_of_observe h_obs, buchiProgress.tau_iff]
    exact hx.2 t₁' rfl
  | vis i c =>
    rw [eq_vis_of_observe h_obs, vis_bind, ITree.observe_vis] at hx
    rw [eq_vis_of_observe h_obs, buchiProgress.vis_iff]
    exact ewp.mono
      (fun o _ hp => hp.2.elim (fun ha => Or.inl ⟨ha, hp.1⟩)
        (fun hpre => Or.inr (hpre (c o) rfl))) hx

/-- Postcondition conjunction for `InfOften` under `[Conjunctive ewp]`. -/
theorem InfOften.conj {ewp : StateEffectWP S E}
    [h_conj : StateEffectWP.Conjunctive ewp]
    {AccEdge : (i : E.I) → E.O i → S → S → Prop}
    {P Q : R → S → Prop} {t : ITree E R} {s : S}
    (hp : InfOften ewp AccEdge P t s) (hq : InfOften ewp AccEdge Q t s) :
    InfOften ewp AccEdge (fun r s' => P r s' ∧ Q r s') t s := by
  refine InfOften.coinduct
    (fun x s₀ => InfOften ewp AccEdge P x s₀ ∧ InfOften ewp AccEdge Q x s₀)
    ?_ ⟨hp, hq⟩
  rintro x s₀ ⟨hpx, hqx⟩
  refine InfOften.progress_induct
    (fun y s₁ => InfOften ewp AccEdge Q y s₁ →
      buchiProgress ewp AccEdge (fun r s' => P r s' ∧ Q r s')
        (fun z s₂ => InfOften ewp AccEdge P z s₂ ∧ InfOften ewp AccEdge Q z s₂)
        y s₁) ?_ hpx hqx
  intro y s₁ hy hqy
  rw [buchiProgress.unfold_eq]
  cases h_obs : y.observe with
  | ret r =>
    simp only [h_obs] at hy ⊢
    rw [eq_ret_of_observe h_obs, InfOften.ret_iff] at hqy
    exact ⟨hy, hqy⟩
  | tau y' =>
    simp only [h_obs] at hy ⊢
    rw [eq_tau_of_observe h_obs, InfOften.tau_iff] at hqy
    exact hy.2 hqy
  | vis i k =>
    simp only [h_obs] at hy ⊢
    rw [eq_vis_of_observe h_obs, InfOften.vis_iff] at hqy
    exact ewp.mono
      (fun _ _ hpq => hpq.1.2.elim (fun ha => Or.inl ⟨ha, hpq.1.1, hpq.2⟩)
        (fun hpre => Or.inr (hpre hpq.2))) (h_conj.conj hy hqy)

/--
Under `[Conjunctive ewp]`, `Always` safety can be merged into a Büchi
recurrence proof, yielding recurrence over the invariant-guarded transformer.
-/
theorem InfOften.guardInv_of_always {ewp : StateEffectWP S E}
    [h_conj : StateEffectWP.Conjunctive ewp]
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Inv : S → Prop}
    {P Q : R → S → Prop} {t : ITree E R} {s : S}
    (h_safe : Always ewp Inv P t s) (h : InfOften ewp AccEdge Q t s) :
    InfOften (guardInvWP ewp Inv) AccEdge Q t s := by
  refine InfOften.coinduct
    (fun x s₀ => Always ewp Inv P x s₀ ∧ InfOften ewp AccEdge Q x s₀)
    ?_ ⟨h_safe, h⟩
  rintro x s₀ ⟨hax, hix⟩
  refine InfOften.progress_induct
    (fun y s₁ => Always ewp Inv P y s₁ →
      buchiProgress (guardInvWP ewp Inv) AccEdge Q
        (fun z s₂ => Always ewp Inv P z s₂ ∧ InfOften ewp AccEdge Q z s₂)
        y s₁) ?_ hix hax
  intro y s₁ hy hay
  rw [buchiProgress.unfold_eq]
  rw [Always.unfold_eq] at hay
  obtain ⟨_, hay⟩ := hay
  cases h_obs : y.observe <;> simp only [h_obs] at hy hay ⊢
  · exact hy
  · exact hy.2 hay
  · exact ewp.mono
      (fun _ _ hpq => ⟨hpq.2.inv,
        hpq.1.2.elim (fun ha => Or.inl ⟨ha, hpq.2, hpq.1.1⟩)
          (fun hpre => Or.inr (hpre hpq.2))⟩) (h_conj.conj hy hay)

/-- Conditional branching rule for `InfOften`. -/
theorem InfOften.ite {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {c : Prop} [Decidable c] {t₁ t₂ : ITree E R} {s : S}
    (h₁ : c → InfOften ewp AccEdge Q t₁ s)
    (h₂ : ¬ c → InfOften ewp AccEdge Q t₂ s) :
    InfOften ewp AccEdge Q (if c then t₁ else t₂) s := by
  split
  · exact h₁ ‹_›
  · exact h₂ ‹_›

/-- `Sum`-branching rule for `InfOften`. -/
theorem InfOften.sum_elim {A B : Type u} {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {f : A → ITree E R} {g : B → ITree E R} {s : S} (x : A ⊕ B)
    (h₁ : ∀ a, x = .inl a → InfOften ewp AccEdge Q (f a) s)
    (h₂ : ∀ b, x = .inr b → InfOften ewp AccEdge Q (g b) s) :
    InfOften ewp AccEdge Q (Sum.elim f g x) s := by
  cases x with
  | inl a => exact h₁ a rfl
  | inr b => exact h₂ b rfl

end InfOften

/-! ### 3.1 Büchi Loop Rules and Diverging `-> !` Reactive Loops -/

section InfOftenLoops

variable {S : Type u} {E : Effect.{u}} {R : Type u}

/--
**Well-founded Büchi loop rule** for `ITree.iter`. Each iteration either exits
with `Q`, or continues *without* having taken an accepting edge while strictly
decreasing the measure `lt`, or takes an accepting edge, after which the
measure may be reset arbitrarily. Hence accepting edges recur infinitely often
on every infinite run of the loop.
-/
theorem InfOften.iter_wf {I : Type u} {α : Type _} {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop}
    (lt : α → α → Prop) (h_wf : WellFounded lt)
    (body : I → ITree E (I ⊕ R)) (LInv : α → I → S → Prop)
    {Q : R → S → Prop}
    (h_body : ∀ m a s₀, LInv m a s₀ →
      buchiProgress ewp AccEdge
        (Sum.elim (fun next s' => ∃ m', lt m' m ∧ LInv m' next s') Q)
        (InfOften ewp AccEdge
          (Sum.elim (fun next s' => ∃ m', LInv m' next s') Q))
        (body a) s₀)
    {m : α} {init : I} {s : S} (h_init : LInv m init s) :
    InfOften ewp AccEdge Q (ITree.iter body init) s := by
  let cont : I ⊕ R → ITree E R :=
    Sum.elim (fun next => .tau (ITree.iter body next)) .ret
  let X : ITree E R → S → Prop := fun u s₀ =>
    ∃ cur : ITree E (I ⊕ R), u = (cur >>= cont) ∧
      InfOften ewp AccEdge
        (Sum.elim (fun next s' => ∃ m', LInv m' next s') Q) cur s₀
  have h_body_io : ∀ m a s₀, LInv m a s₀ →
      InfOften ewp AccEdge
        (Sum.elim (fun next s' => ∃ m', LInv m' next s') Q) (body a) s₀ := by
    intro m a s₀ hm
    refine InfOften.of_buchiProgress
      (buchiProgress.mono (fun _ _ _ hw => hw) (fun _ _ _ _ ha => ha) ?_
        (fun _ _ hr => hr) (h_body m a s₀ hm))
    rintro (next | r) s' hp
    · obtain ⟨m', _, hm'⟩ := hp
      exact ⟨m', hm'⟩
    · exact hp
  have h_enter : ∀ m a s₀, LInv m a s₀ →
      buchiProgress ewp AccEdge Q X (body a >>= cont) s₀ := by
    intro m
    refine h_wf.induction
      (C := fun m => ∀ a s₀, LInv m a s₀ →
        buchiProgress ewp AccEdge Q X (body a >>= cont) s₀) m ?_
    intro m ih a s₀ hm
    refine buchiProgress.induct
      (fun b s₁ => buchiProgress ewp AccEdge Q X (b >>= cont) s₁) ?_
      (h_body m a s₀ hm)
    intro b s₁ hb
    cases h_obs : b.observe with
    | ret res =>
      simp only [h_obs] at hb
      rw [eq_ret_of_observe h_obs, ret_bind]
      cases res with
      | inl next =>
        obtain ⟨m', hlt, hm'⟩ := hb
        dsimp only [cont, Sum.elim]
        rw [buchiProgress.tau_iff, iter_unfold body next]
        exact ih m' hlt next s₁ hm'
      | inr r =>
        dsimp only [cont, Sum.elim]
        rw [buchiProgress.ret_iff]; exact hb
    | tau b' =>
      simp only [h_obs] at hb
      rw [eq_tau_of_observe h_obs, tau_bind, buchiProgress.tau_iff]; exact hb
    | vis i c =>
      simp only [h_obs] at hb
      rw [eq_vis_of_observe h_obs, vis_bind, buchiProgress.vis_iff]
      exact ewp.mono
        (fun o _ hp => hp.imp (And.imp id (fun hio => ⟨c o, rfl, hio⟩)) id) hb
  refine InfOften.coinduct X ?_
    ⟨body init, iter_unfold body init, h_body_io m init s h_init⟩
  rintro u s₀ ⟨cur, rfl, h_cur⟩
  refine buchiProgress.induct
    (fun c s₁ => buchiProgress ewp AccEdge Q X (c >>= cont) s₁) ?_
    h_cur.toBuchiProgress
  intro c s₁ hc
  cases h_obs : c.observe with
  | ret res =>
    simp only [h_obs] at hc
    rw [eq_ret_of_observe h_obs, ret_bind]
    cases res with
    | inl next =>
      obtain ⟨m', hm'⟩ := hc
      dsimp only [cont, Sum.elim]
      rw [buchiProgress.tau_iff, iter_unfold body next]
      exact h_enter m' next s₁ hm'
    | inr r =>
      dsimp only [cont, Sum.elim]
      rw [buchiProgress.ret_iff]; exact hc
  | tau c' =>
    simp only [h_obs] at hc
    rw [eq_tau_of_observe h_obs, tau_bind, buchiProgress.tau_iff]; exact hc
  | vis i c' =>
    simp only [h_obs] at hc
    rw [eq_vis_of_observe h_obs, vis_bind, buchiProgress.vis_iff]
    exact ewp.mono
      (fun o _ hp => hp.imp (And.imp id (fun hio => ⟨c' o, rfl, hio⟩)) id) hc

/--
**`Nat`-ranked Büchi loop rule**: a bounded cycle of at most `n` non-accepting
iterations is followed by an accepting edge (or a loop exit with `Q`).
-/
theorem InfOften.iter_ranked {I : Type u} {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop}
    (body : I → ITree E (I ⊕ R)) (LInv : Nat → I → S → Prop)
    {Q : R → S → Prop}
    (h_body : ∀ n a s₀, LInv n a s₀ →
      buchiProgress ewp AccEdge
        (Sum.elim (fun next s' => ∃ m, m < n ∧ LInv m next s') Q)
        (InfOften ewp AccEdge
          (Sum.elim (fun next s' => ∃ m, LInv m next s') Q))
        (body a) s₀)
    {n : Nat} {init : I} {s : S} (h_init : LInv n init s) :
    InfOften ewp AccEdge Q (ITree.iter body init) s :=
  InfOften.iter_wf (fun a b : Nat => a < b) Nat.lt_wfRel.wf body LInv h_body
    h_init

/--
**Büchi loop rule** (one accepting edge per iteration): every iteration that
continues the loop must first take an accepting edge.
-/
theorem InfOften.iter_progress {I : Type u} {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop}
    (body : I → ITree E (I ⊕ R)) (LInv : I → S → Prop) {Q : R → S → Prop}
    (h_body : ∀ a s₀, LInv a s₀ →
      buchiProgress ewp AccEdge (Sum.elim (fun _ _ => False) Q)
        (InfOften ewp AccEdge (Sum.elim LInv Q)) (body a) s₀)
    {init : I} {s : S} (h_init : LInv init s) :
    InfOften ewp AccEdge Q (ITree.iter body init) s := by
  refine InfOften.iter_ranked body (fun _ a s' => LInv a s') ?_
    (n := 0) h_init
  intro n a s₀ ha
  refine buchiProgress.mono (fun _ _ _ hw => hw) (fun _ _ _ _ hacc => hacc)
    ?_ ?_ (h_body a s₀ ha)
  · rintro (next | r) s' hp
    · exact False.elim hp
    · exact hp
  · intro x s' hx
    refine InfOften.mono_post ?_ hx
    rintro (next | r) s'' hp
    · exact ⟨0, hp⟩
    · exact hp

/--
A diverging `-> !` reactive event loop (`zerocopy#4162`): `body` is iterated
forever and the loop never returns, so its return type is `PEmpty`.
-/
def divergingLoop {I : Type u} (body : I → ITree E I) (init : I) :
    ITree E PEmpty.{u + 1} :=
  ITree.iter (fun a => Sum.inl <$> body a) init

private theorem always_map_inl {I : Type u} {ewp : StateEffectWP S E}
    {Inv : S → Prop} {LInv : I → S → Prop} {Q : R → S → Prop}
    {t : ITree E I} {s : S} (h : Always ewp Inv LInv t s) :
    Always ewp Inv (Sum.elim LInv Q) (Sum.inl <$> t : ITree E (I ⊕ R)) s := by
  have h_eq : (Sum.inl <$> t : ITree E (I ⊕ R)) =
      (t >>= fun a => ITree.ret (Sum.inl a)) := rfl
  rw [h_eq]
  refine Always.bind (Always.mono (fun _ hi => hi) ?_ h.post_inv)
  intro a s' ha
  exact Always.ret ha.1 ha.2

private theorem buchiProgress_map_inl {I : Type u} {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop}
    {Q₀ LInv : I → S → Prop} {Q : R → S → Prop} {t : ITree E I} {s : S}
    (h : buchiProgress ewp AccEdge Q₀ (InfOften ewp AccEdge LInv) t s) :
    buchiProgress ewp AccEdge (Sum.elim Q₀ Q)
      (InfOften ewp AccEdge (Sum.elim LInv Q))
      (Sum.inl <$> t : ITree E (I ⊕ R)) s := by
  have h_eq : (Sum.inl <$> t : ITree E (I ⊕ R)) =
      (t >>= fun a => ITree.ret (Sum.inl a)) := rfl
  rw [h_eq]
  refine buchiProgress.bind
    (buchiProgress.mono (fun _ _ _ hw => hw) (fun _ _ _ _ ha => ha) ?_ ?_ h)
  · intro a s' ha
    exact (buchiProgress.ret_iff ewp AccEdge _ _ (Sum.inl a) s').2 ha
  · intro t' s' ht'
    refine InfOften.bind (InfOften.mono_post ?_ ht')
    intro a s'' ha
    exact (InfOften.ret_iff ewp AccEdge _ (Sum.inl a) s'').2 ha

/-- A tree that cannot return never satisfies `DWP` under excluded miracle. -/
theorem not_dwp_of_isEmpty {ewp : StateEffectWP S E}
    [h_em : StateEffectWP.ExcludedMiracle ewp] (h_empty : R → False)
    {Q : R → S → Prop} {t : ITree E R} {s : S} :
    ¬ DWP ewp t Q s := by
  refine DWP.induct (fun _ _ => False) ?_
  intro x _ hx
  cases h_obs : x.observe with
  | ret r => exact h_empty r
  | tau x' => rw [h_obs] at hx; exact hx
  | vis i k => rw [h_obs] at hx; exact h_em.no_miracle hx

/--
**Total correctness is unsatisfiable on diverging loops.** For a non-miraculous
transformer, `DWP` never holds of a `-> !` loop. No safety hypothesis is needed:
the statement is strictly stronger than its `Always`-guarded form.
-/
theorem not_dwp_diverging_loop {I : Type u} {ewp : StateEffectWP S E}
    [StateEffectWP.ExcludedMiracle ewp] (body : I → ITree E I) (init : I)
    {Q : PEmpty.{u + 1} → S → Prop} {s : S} :
    ¬ DWP ewp (divergingLoop body init) Q s :=
  not_dwp_of_isEmpty (fun r => PEmpty.elim r)

/-- Loop-invariant safety rule for diverging loops. -/
theorem always_divergingLoop {I : Type u} {ewp : StateEffectWP S E}
    {Inv : S → Prop} (body : I → ITree E I) (LInv : I → S → Prop)
    (h_body : ∀ a s₀, LInv a s₀ → Always ewp Inv LInv (body a) s₀)
    {init : I} {s : S} (h_init : LInv init s)
    (Q : PEmpty.{u + 1} → S → Prop) :
    Always ewp Inv Q (divergingLoop body init) s :=
  Always.iter_invariant _ LInv
    (fun a s₀ ha => always_map_inl (h_body a s₀ ha)) h_init

/-- Well-founded Büchi recurrence rule for diverging loops. -/
theorem infOften_divergingLoop_wf {I : Type u} {α : Type _}
    {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop}
    (lt : α → α → Prop) (h_wf : WellFounded lt)
    (body : I → ITree E I) (LInv : α → I → S → Prop)
    (h_body : ∀ m a s₀, LInv m a s₀ →
      buchiProgress ewp AccEdge
        (fun next s' => ∃ m', lt m' m ∧ LInv m' next s')
        (InfOften ewp AccEdge (fun next s' => ∃ m', LInv m' next s'))
        (body a) s₀)
    {m : α} {init : I} {s : S} (h_init : LInv m init s)
    (Q : PEmpty.{u + 1} → S → Prop) :
    InfOften ewp AccEdge Q (divergingLoop body init) s :=
  InfOften.iter_wf lt h_wf _ LInv
    (fun m a s₀ hm => buchiProgress_map_inl (h_body m a s₀ hm)) h_init

/--
**Diverging `-> !` reactive loop rule** (`zerocopy#4162`). Under a loop
invariant `LInv` whose every iteration is `Always`-safe and takes at least one
accepting edge before re-establishing `LInv`, the diverging loop satisfies
**both** `Always` safety and `InfOften` Büchi recurrence, even though `DWP` is
unsatisfiable on it (`not_dwp_diverging_loop`).
-/
theorem buchi_diverging_loop_rule {I : Type u} {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Inv : S → Prop}
    (body : I → ITree E I) (LInv : I → S → Prop)
    (h_safe : ∀ a s₀, LInv a s₀ → Always ewp Inv LInv (body a) s₀)
    (h_live : ∀ a s₀, LInv a s₀ →
      buchiProgress ewp AccEdge (fun _ _ => False)
        (InfOften ewp AccEdge LInv) (body a) s₀)
    {init : I} {s : S} (h_init : LInv init s)
    (Q : PEmpty.{u + 1} → S → Prop) :
    Always ewp Inv Q (divergingLoop body init) s ∧
      InfOften ewp AccEdge Q (divergingLoop body init) s :=
  ⟨always_divergingLoop body LInv h_safe h_init Q,
   InfOften.iter_progress _ LInv
     (fun a s₀ ha => buchiProgress_map_inl (h_live a s₀ ha)) h_init⟩

/--
**Ranked diverging loop rule**: a `Nat`-bounded cycle of non-accepting
iterations is tolerated between accepting edges. The rank is existentially
re-chosen after every accepting edge.
-/
theorem buchi_diverging_loop_ranked {I : Type u} {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Inv : S → Prop}
    (body : I → ITree E I) (LInv : Nat → I → S → Prop)
    (h_safe : ∀ n a s₀, LInv n a s₀ →
      Always ewp Inv (fun next s' => ∃ m, LInv m next s') (body a) s₀)
    (h_live : ∀ n a s₀, LInv n a s₀ →
      buchiProgress ewp AccEdge
        (fun next s' => ∃ m, m < n ∧ LInv m next s')
        (InfOften ewp AccEdge (fun next s' => ∃ m, LInv m next s'))
        (body a) s₀)
    {n : Nat} {init : I} {s : S} (h_init : LInv n init s)
    (Q : PEmpty.{u + 1} → S → Prop) :
    Always ewp Inv Q (divergingLoop body init) s ∧
      InfOften ewp AccEdge Q (divergingLoop body init) s :=
  ⟨always_divergingLoop body (fun a s' => ∃ m, LInv m a s')
     (fun a s₀ ⟨m, hm⟩ => h_safe m a s₀ hm) ⟨n, h_init⟩ Q,
   infOften_divergingLoop_wf (fun a b : Nat => a < b) Nat.lt_wfRel.wf body
     LInv h_live h_init Q⟩

end InfOftenLoops

/-! ### 3.2 Shallowly Embedded Büchi Monitors (`BuchiSpec`, `BuchiSat`) -/

/--
A shallowly embedded Büchi specification over effect signature `E`, logical
state `S`, return type `R` and an arbitrary (finite or infinite) automaton
state carrier `QState`.
-/
structure BuchiSpec (S QState : Type u) (E : Effect.{u}) (R : Type u) :
    Type (u + 1) where
  /-- One-step predicate transformer interpreting the program's effects. -/
  ewp : StateEffectWP S E
  /-- Monitor transition relation `step q i o s s' q'` along the program
  transition `(i, o, s, s')`. A transition with no monitor successor is a
  safety violation. -/
  step : QState → (i : E.I) → E.O i → S → S → QState → Prop
  /-- Accepting monitor transitions (Büchi acceptance on edges). -/
  accept : QState → (i : E.I) → E.O i → S → S → QState → Prop
  /-- Joint invariant on the monitor state and the logical state. -/
  inv : QState → S → Prop
  /-- Hoare postcondition for finite (terminating) runs. -/
  terminal : QState → R → S → Prop

namespace BuchiSpec

variable {S QState : Type u} {E : Effect.{u}} {R : Type u}

/--
Synchronous product of the program transformer with the monitor: after each
answer the monitor (angelically, as in a nondeterministic Büchi automaton)
picks a successor state allowed by `step`.
-/
def prodWP (spec : BuchiSpec S QState E R) : StateEffectWP (QState × S) E where
  wp i K qs :=
    spec.ewp.wp i
      (fun o s' => ∃ q', spec.step qs.1 i o qs.2 s' q' ∧ K o (q', s')) qs.2
  mono h hw :=
    spec.ewp.mono (fun o _ hk => hk.elim fun q' hq => ⟨q', hq.1, h o _ hq.2⟩) hw

/-- The joint invariant as a predicate on product states. -/
def invPred (spec : BuchiSpec S QState E R) : QState × S → Prop :=
  fun qs => spec.inv qs.1 qs.2

/--
The invariant-guarded monitor product: the *same* monitor run that is checked
for acceptance must also maintain the invariant.
-/
def monitorWP (spec : BuchiSpec S QState E R) : StateEffectWP (QState × S) E :=
  guardInvWP spec.prodWP spec.invPred

/-- Accepting edges of the monitor product. -/
def acceptEdge (spec : BuchiSpec S QState E R) :
    (i : E.I) → E.O i → QState × S → QState × S → Prop :=
  fun i o qs qs' => spec.accept qs.1 i o qs.2 qs'.2 qs'.1

/-- The terminal postcondition as a predicate on product states. -/
def terminalPost (spec : BuchiSpec S QState E R) : R → QState × S → Prop :=
  fun r qs => spec.terminal qs.1 r qs.2

/-- Replace the terminal postcondition (possibly changing the return type). -/
def withTerminal {A : Type u} (spec : BuchiSpec S QState E R)
    (term : QState → A → S → Prop) : BuchiSpec S QState E A where
  ewp := spec.ewp
  step := spec.step
  accept := spec.accept
  inv := spec.inv
  terminal := term

/-- One-step unfolding of the invariant-guarded monitor product. -/
theorem monitorWP_wp (spec : BuchiSpec S QState E R) (i : E.I)
    (K : E.O i → QState × S → Prop) (q : QState) (s : S) :
    spec.monitorWP.wp i K (q, s) ↔
      spec.ewp.wp i
        (fun o s' => ∃ q', spec.step q i o s s' q' ∧ spec.inv q' s' ∧
          K o (q', s')) s :=
  Iff.rfl

/--
A deterministic monitor over a conjunctive program transformer yields a
conjunctive product.
-/
theorem prodWP_conjunctive (spec : BuchiSpec S QState E R)
    [h_conj : StateEffectWP.Conjunctive spec.ewp]
    (h_det : ∀ q i o s s' q₁ q₂,
      spec.step q i o s s' q₁ → spec.step q i o s s' q₂ → q₁ = q₂) :
    StateEffectWP.Conjunctive spec.prodWP where
  conj hp hq :=
    spec.ewp.mono
      (fun _ _ hpq =>
        hpq.1.elim fun q₁ h₁ => hpq.2.elim fun _ h₂ =>
          ⟨q₁, h₁.1, h₁.2, (h_det _ _ _ _ _ _ _ h₁.1 h₂.1) ▸ h₂.2⟩)
      (h_conj.conj hp hq)

instance (spec : BuchiSpec S QState E R)
    [h : StateEffectWP.ExcludedMiracle spec.ewp] :
    StateEffectWP.ExcludedMiracle spec.prodWP where
  no_miracle hw :=
    h.no_miracle (spec.ewp.mono (fun _ _ hk => hk.elim fun _ hq => hq.2) hw)

instance (spec : BuchiSpec S QState E R)
    [StateEffectWP.ExcludedMiracle spec.ewp] :
    StateEffectWP.ExcludedMiracle spec.monitorWP :=
  inferInstanceAs
    (StateEffectWP.ExcludedMiracle (guardInvWP spec.prodWP spec.invPred))

end BuchiSpec

section BuchiSat

variable {S QState : Type u} {E : Effect.{u}} {R : Type u}

/--
`BuchiSat spec t q₀ s₀`: the tree `t` started in monitor state `q₀` and logical
state `s₀` satisfies the Büchi specification, unifying

* `Always` safety of the joint invariant along the monitor product,
* `InfOften` Büchi recurrence of accepting monitor edges along the
  invariant-guarded product (so acceptance is witnessed by a safe run), and
* the `terminal` Hoare postcondition on every finite run.
-/
def BuchiSat (spec : BuchiSpec S QState E R) (t : ITree E R)
    (q₀ : QState) (s₀ : S) : Prop :=
  Always spec.prodWP spec.invPred spec.terminalPost t (q₀, s₀) ∧
    InfOften spec.monitorWP spec.acceptEdge spec.terminalPost t (q₀, s₀)

/-- The joint invariant holds initially. -/
theorem BuchiSat.inv {spec : BuchiSpec S QState E R} {t : ITree E R}
    {q₀ : QState} {s₀ : S} (h : BuchiSat spec t q₀ s₀) : spec.inv q₀ s₀ :=
  h.1.inv

/--
Because acceptance is checked along the invariant-guarded product, the safety
conjunct of `BuchiSat` is derivable: `BuchiSat` is the invariant now plus
Büchi recurrence of the guarded monitor product.
-/
theorem buchiSat_iff_infOften (spec : BuchiSpec S QState E R) (t : ITree E R)
    (q₀ : QState) (s₀ : S) :
    BuchiSat spec t q₀ s₀ ↔
      spec.inv q₀ s₀ ∧
        InfOften spec.monitorWP spec.acceptEdge spec.terminalPost t (q₀, s₀) := by
  constructor
  · intro h
    exact ⟨h.1.inv, h.2⟩
  · rintro ⟨hi, hl⟩
    exact ⟨(always_iff_dwlp_guard spec.prodWP spec.invPred spec.terminalPost
      t (q₀, s₀)).2 ⟨hi, hl.toDWLP⟩, hl⟩

/-- `BuchiSat` implies Büchi recurrence along the unguarded monitor product. -/
theorem BuchiSat.infOften_prod {spec : BuchiSpec S QState E R} {t : ITree E R}
    {q₀ : QState} {s₀ : S} (h : BuchiSat spec t q₀ s₀) :
    InfOften spec.prodWP spec.acceptEdge spec.terminalPost t (q₀, s₀) :=
  InfOften.mono (ewp := spec.monitorWP) (ewp' := spec.prodWP)
    (fun _ K _ hw =>
      spec.prodWP.mono (P := fun o qs' => spec.invPred qs' ∧ K o qs')
        (fun _ _ hk => hk.2) hw)
    (fun _ _ _ _ ha => ha) (fun _ _ hq => hq) h.2

/--
For a conjunctive monitor product (e.g. a deterministic monitor over a
conjunctive transformer), safety and recurrence established separately along
the unguarded product combine into `BuchiSat`.
-/
theorem buchiSat_of_always_of_infOften {spec : BuchiSpec S QState E R}
    [StateEffectWP.Conjunctive spec.prodWP] {t : ITree E R}
    {q₀ : QState} {s₀ : S}
    (h_safe : Always spec.prodWP spec.invPred spec.terminalPost t (q₀, s₀))
    (h_live : InfOften spec.prodWP spec.acceptEdge spec.terminalPost t
      (q₀, s₀)) :
    BuchiSat spec t q₀ s₀ :=
  ⟨h_safe, InfOften.guardInv_of_always h_safe h_live⟩

/-- Exact decomposition of `BuchiSat` for conjunctive monitor products. -/
theorem buchiSat_iff_always_and_infOften (spec : BuchiSpec S QState E R)
    [StateEffectWP.Conjunctive spec.prodWP] (t : ITree E R)
    (q₀ : QState) (s₀ : S) :
    BuchiSat spec t q₀ s₀ ↔
      Always spec.prodWP spec.invPred spec.terminalPost t (q₀, s₀) ∧
        InfOften spec.prodWP spec.acceptEdge spec.terminalPost t (q₀, s₀) :=
  ⟨fun h => ⟨h.1, h.infOften_prod⟩,
   fun h => buchiSat_of_always_of_infOften h.1 h.2⟩

/--
**Unconditional `spin` refutation** for `BuchiSat`: no Büchi specification,
monitor state, or logical state accepts silent divergence.
-/
theorem not_buchiSat_spin {spec : BuchiSpec S QState E R}
    {q₀ : QState} {s₀ : S} :
    ¬ BuchiSat spec (ITree.spin (E := E) (R := R)) q₀ s₀ :=
  fun h => not_infOften_spin h.2

/--
Büchi acceptance has teeth: a non-miraculous specification without accepting
monitor edges is satisfied by **no** tree that never returns.
-/
theorem not_buchiSat_of_no_accept {spec : BuchiSpec S QState E R}
    [StateEffectWP.ExcludedMiracle spec.ewp] (h_empty : R → False)
    (h_acc : ∀ q i o s s' q', ¬ spec.accept q i o s s' q')
    {t : ITree E R} {q₀ : QState} {s₀ : S} :
    ¬ BuchiSat spec t q₀ s₀ :=
  fun h =>
    not_infOften_of_no_accept h_empty
      (InfOften.mono (fun _ _ _ hw => hw)
        (fun _ _ _ _ ha => h_acc _ _ _ _ _ _ ha) (fun _ _ hq => hq) h.2)

/--
**`DWP` embedding**: total correctness along the invariant-guarded monitor
product yields `BuchiSat`.
-/
theorem buchiSat_of_dwp {spec : BuchiSpec S QState E R} {t : ITree E R}
    {q₀ : QState} {s₀ : S} (h_inv : spec.inv q₀ s₀)
    (h : DWP spec.monitorWP t spec.terminalPost (q₀, s₀)) :
    BuchiSat spec t q₀ s₀ :=
  (buchiSat_iff_infOften spec t q₀ s₀).2
    ⟨h_inv, infOften_of_dwp spec.acceptEdge h⟩

/--
**`DWP` embedding when `Always` safety also holds**: for a conjunctive monitor
product, plain total correctness plus `Always` safety yields `BuchiSat`.
-/
theorem buchiSat_of_dwp_of_always {spec : BuchiSpec S QState E R}
    [StateEffectWP.Conjunctive spec.prodWP] {t : ITree E R}
    {q₀ : QState} {s₀ : S}
    (h_safe : Always spec.prodWP spec.invPred spec.terminalPost t (q₀, s₀))
    (h : DWP spec.prodWP t spec.terminalPost (q₀, s₀)) :
    BuchiSat spec t q₀ s₀ :=
  buchiSat_of_always_of_infOften h_safe (infOften_of_dwp spec.acceptEdge h)

/-- Weakening of the terminal postcondition. -/
theorem BuchiSat.mono {spec : BuchiSpec S QState E R} {t : ITree E R}
    {q₀ : QState} {s₀ : S} {term' : QState → R → S → Prop}
    (h_term : ∀ q r s, spec.terminal q r s → term' q r s)
    (h : BuchiSat spec t q₀ s₀) :
    BuchiSat (spec.withTerminal term') t q₀ s₀ :=
  ⟨Always.mono (fun _ hi => hi) (fun _ _ ha => h_term _ _ _ ha) h.1,
   InfOften.mono_post (fun _ _ ha => h_term _ _ _ ha) h.2⟩

/--
**Compositionality**: a prefix satisfying the specification with terminal
condition "the continuation satisfies the specification" sequences into a tree
satisfying the specification.
-/
theorem BuchiSat.bind {A : Type u} {spec : BuchiSpec S QState E R}
    {t : ITree E A} {k : A → ITree E R} {q₀ : QState} {s₀ : S}
    (h : BuchiSat (spec.withTerminal (fun q a s => BuchiSat spec (k a) q s))
      t q₀ s₀) :
    BuchiSat spec (t >>= k) q₀ s₀ :=
  ⟨Always.bind (Always.mono (fun _ hi => hi) (fun _ _ ha => ha.1) h.1),
   InfOften.bind (InfOften.mono_post (fun _ _ ha => ha.2) h.2)⟩

/-- Sequential composition `t₁ ; t₂` of Büchi-satisfying trees. -/
theorem BuchiSat.seq {A : Type u} {spec : BuchiSpec S QState E R}
    {t₁ : ITree E A} {t₂ : ITree E R} {q₀ : QState} {s₀ : S}
    (h : BuchiSat (spec.withTerminal (fun q _ s => BuchiSat spec t₂ q s))
      t₁ q₀ s₀) :
    BuchiSat spec (t₁ >>= fun _ => t₂) q₀ s₀ :=
  BuchiSat.bind h

/-- Conditional branching rule for `BuchiSat`. -/
theorem BuchiSat.ite {spec : BuchiSpec S QState E R}
    {c : Prop} [Decidable c] {t₁ t₂ : ITree E R} {q₀ : QState} {s₀ : S}
    (h₁ : c → BuchiSat spec t₁ q₀ s₀) (h₂ : ¬ c → BuchiSat spec t₂ q₀ s₀) :
    BuchiSat spec (if c then t₁ else t₂) q₀ s₀ := by
  split
  · exact h₁ ‹_›
  · exact h₂ ‹_›

/-- `Sum`-branching rule for `BuchiSat`. -/
theorem BuchiSat.sum_elim {A B : Type u} {spec : BuchiSpec S QState E R}
    {f : A → ITree E R} {g : B → ITree E R} {q₀ : QState} {s₀ : S}
    (x : A ⊕ B)
    (h₁ : ∀ a, x = .inl a → BuchiSat spec (f a) q₀ s₀)
    (h₂ : ∀ b, x = .inr b → BuchiSat spec (g b) q₀ s₀) :
    BuchiSat spec (Sum.elim f g x) q₀ s₀ := by
  cases x with
  | inl a => exact h₁ a rfl
  | inr b => exact h₂ b rfl

/--
**Ranked diverging loop rule for `BuchiSat`**: a `-> !` loop whose iterations
take an accepting monitor edge after a `Nat`-bounded cycle of non-accepting
iterations satisfies the Büchi specification.
-/
theorem buchiSat_diverging_loop_ranked {I : Type u}
    (spec : BuchiSpec S QState E PEmpty.{u + 1}) (body : I → ITree E I)
    (LInv : Nat → I → QState → S → Prop)
    (h_live : ∀ n a q s, LInv n a q s →
      buchiProgress spec.monitorWP spec.acceptEdge
        (fun next qs' => ∃ m, m < n ∧ LInv m next qs'.1 qs'.2)
        (InfOften spec.monitorWP spec.acceptEdge
          (fun next qs' => ∃ m, LInv m next qs'.1 qs'.2))
        (body a) (q, s))
    {n : Nat} {init : I} {q₀ : QState} {s₀ : S}
    (h_inv : spec.inv q₀ s₀) (h_init : LInv n init q₀ s₀) :
    BuchiSat spec (divergingLoop body init) q₀ s₀ :=
  (buchiSat_iff_infOften spec _ q₀ s₀).2
    ⟨h_inv,
     infOften_divergingLoop_wf (fun a b : Nat => a < b) Nat.lt_wfRel.wf body
       (fun m a qs => LInv m a qs.1 qs.2)
       (fun m a qs hm => h_live m a qs.1 qs.2 hm) h_init _⟩

/--
**Diverging loop rule for `BuchiSat`**: a `-> !` loop whose every iteration
takes an accepting monitor edge satisfies the Büchi specification.
-/
theorem buchiSat_diverging_loop_rule {I : Type u}
    (spec : BuchiSpec S QState E PEmpty.{u + 1}) (body : I → ITree E I)
    (LInv : I → QState → S → Prop)
    (h_live : ∀ a q s, LInv a q s →
      buchiProgress spec.monitorWP spec.acceptEdge (fun _ _ => False)
        (InfOften spec.monitorWP spec.acceptEdge
          (fun next qs' => LInv next qs'.1 qs'.2))
        (body a) (q, s))
    {init : I} {q₀ : QState} {s₀ : S}
    (h_inv : spec.inv q₀ s₀) (h_init : LInv init q₀ s₀) :
    BuchiSat spec (divergingLoop body init) q₀ s₀ := by
  refine buchiSat_diverging_loop_ranked spec body
    (fun _ a q s => LInv a q s) ?_ (n := 0) h_inv h_init
  intro n a q s ha
  refine buchiProgress.mono (fun _ _ _ hw => hw) (fun _ _ _ _ hacc => hacc)
    (fun _ _ hp => False.elim hp) ?_ (h_live a q s ha)
  intro x qs hx
  exact InfOften.mono_post (fun _ _ hp => ⟨0, hp⟩) hx

end BuchiSat

/-! ### 3.3 Handler Linking and Operational Adequacy for `InfOften` -/

/--
**Horizontal handler linking** for `InfOften` across `ITree.interp`. The link
condition asks each handler `h i` to terminate, and to take an accepting
`E₂`-edge whenever the interpreted `E₁`-edge was accepting: answers reached
*before* an accepting `E₂`-edge must lie in the non-accepting continuation
`Knon`; afterwards the handler may finish (`DWP`) into either continuation.
-/
theorem InfOften.interp {S : Type u} {E₁ E₂ : Effect.{u}} {R : Type u}
    {ewp₁ : StateEffectWP S E₁} {ewp₂ : StateEffectWP S E₂}
    {Acc₁ : (i : E₁.I) → E₁.O i → S → S → Prop}
    {Acc₂ : (j : E₂.I) → E₂.O j → S → S → Prop}
    (h : (i : E₁.I) → ITree E₂ (E₁.O i))
    (h_link : ∀ (i : E₁.I) (Kacc Knon : E₁.O i → S → Prop) (s₀ : S),
      ewp₁.wp i (fun o s' => (Acc₁ i o s₀ s' ∧ Kacc o s') ∨ Knon o s') s₀ →
      buchiProgress ewp₂ Acc₂ Knon
        (fun m s' => DWP ewp₂ m (fun o s'' => Kacc o s'' ∨ Knon o s'') s')
        (h i) s₀)
    {t : ITree E₁ R} {Q : R → S → Prop} {s : S}
    (h_io : InfOften ewp₁ Acc₁ Q t s) :
    InfOften ewp₂ Acc₂ Q (ITree.interp h t) s := by
  let X : ITree E₂ R → S → Prop := fun u s₀ =>
    (∃ t₀, u = ITree.interp h t₀ ∧ InfOften ewp₁ Acc₁ Q t₀ s₀) ∨
    (∃ (i : E₁.I) (m : ITree E₂ (E₁.O i)) (k : E₁.O i → ITree E₁ R),
      u = (m >>= fun o => .tau (ITree.interp h (k o))) ∧
      DWP ewp₂ m (fun o s' => InfOften ewp₁ Acc₁ Q (k o) s') s₀)
  have h_main : ∀ (t₀ : ITree E₁ R) (s₀ : S), InfOften ewp₁ Acc₁ Q t₀ s₀ →
      buchiProgress ewp₂ Acc₂ Q X (ITree.interp h t₀) s₀ := by
    intro t₀ s₀ ht₀
    refine InfOften.progress_induct
      (fun t₁ s₁ => buchiProgress ewp₂ Acc₂ Q X (ITree.interp h t₁) s₁) ?_ ht₀
    intro t₁ s₁ hx
    cases h_obs : t₁.observe with
    | ret r =>
      simp only [h_obs] at hx
      rw [eq_ret_of_observe h_obs, interp_ret, buchiProgress.ret_iff]; exact hx
    | tau t₁' =>
      simp only [h_obs] at hx
      rw [eq_tau_of_observe h_obs, interp_tau, buchiProgress.tau_iff]
      exact hx.2
    | vis i k =>
      simp only [h_obs] at hx
      rw [eq_vis_of_observe h_obs, interp_vis]
      have h_l := h_link i (fun o s' => InfOften ewp₁ Acc₁ Q (k o) s')
        (fun o s' => InfOften ewp₁ Acc₁ Q (k o) s' ∧
          buchiProgress ewp₂ Acc₂ Q X (ITree.interp h (k o)) s') s₁
        (ewp₁.mono
          (fun _ _ hp => hp.2.elim (fun ha => Or.inl ⟨ha, hp.1⟩)
            (fun hpre => Or.inr ⟨hp.1, hpre⟩)) hx)
      refine buchiProgress.induct
        (fun m s₂ => buchiProgress ewp₂ Acc₂ Q X
          (m >>= fun o => .tau (ITree.interp h (k o))) s₂) ?_ h_l
      intro m s₂ hm
      cases hm_obs : m.observe with
      | ret o =>
        simp only [hm_obs] at hm
        rw [eq_ret_of_observe hm_obs, ret_bind, buchiProgress.tau_iff]
        exact hm.2
      | tau m' =>
        simp only [hm_obs] at hm
        rw [eq_tau_of_observe hm_obs, tau_bind, buchiProgress.tau_iff]
        exact hm
      | vis j c =>
        simp only [hm_obs] at hm
        rw [eq_vis_of_observe hm_obs, vis_bind, buchiProgress.vis_iff]
        exact ewp₂.mono
          (fun o₂ _ hp => hp.imp
            (And.imp id (fun hd => Or.inr ⟨i, c o₂, k, rfl,
              DWP.mono (fun _ _ hq => hq.elim id And.left) hd⟩)) id) hm
  refine InfOften.coinduct X ?_ (Or.inl ⟨t, rfl, h_io⟩)
  rintro u s₀ (⟨t₀, rfl, ht₀⟩ | ⟨i, m, k, rfl, hm⟩)
  · exact h_main t₀ s₀ ht₀
  · refine DWP.induct
      (fun m s₁ => buchiProgress ewp₂ Acc₂ Q X
        (m >>= fun o => .tau (ITree.interp h (k o))) s₁) ?_ hm
    intro m s₁ hm
    cases hm_obs : m.observe with
    | ret o =>
      simp only [hm_obs] at hm
      rw [eq_ret_of_observe hm_obs, ret_bind, buchiProgress.tau_iff]
      exact h_main (k o) s₁ hm
    | tau m' =>
      simp only [hm_obs] at hm
      rw [eq_tau_of_observe hm_obs, tau_bind, buchiProgress.tau_iff]
      exact hm
    | vis j c =>
      simp only [hm_obs] at hm
      rw [eq_vis_of_observe hm_obs, vis_bind, buchiProgress.vis_iff]
      exact ewp₂.mono (fun _ _ hp => Or.inr hp) hm

/--
The link condition of `InfOften.interp` is satisfiable for every transformer
and every choice of accepting edges: re-triggering each request preserves
Büchi recurrence.
-/
theorem InfOften.interp_trigger {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop}
    {t : ITree E R} {Q : R → S → Prop} {s : S}
    (h : InfOften ewp AccEdge Q t s) :
    InfOften ewp AccEdge Q (ITree.interp (fun i => ITree.trigger i) t) s := by
  refine InfOften.interp (fun i => ITree.trigger i) ?_ h
  intro i Kacc Knon s₀ hw
  refine (buchiProgress.vis_iff _ _ _ _ _ _ _).2 (ewp.mono ?_ hw)
  rintro o s' (⟨ha, hk⟩ | hk)
  · exact Or.inl ⟨ha, DWP.ret (Or.inl hk)⟩
  · exact Or.inr ((buchiProgress.ret_iff _ _ _ _ _ _).2 hk)

/--
**Stateful handler linking** for `InfOften` across `ITree.interpState`,
threading the handler state `H` that the source transformer treats as its
logical state.
-/
theorem InfOften.interpState {H : Type u} {E₁ E₂ : Effect.{u}} {R : Type u}
    {ewp₁ : StateEffectWP H E₁} {ewp₂ : EffectWP E₂}
    {Acc₁ : (i : E₁.I) → E₁.O i → H → H → Prop}
    {Acc₂ : (j : E₂.I) → E₂.O j → PUnit.{u + 1} → PUnit.{u + 1} → Prop}
    (h : (i : E₁.I) → H → ITree E₂ (E₁.O i × H))
    (h_link : ∀ (i : E₁.I) (Kacc Knon : E₁.O i → H → Prop) (st : H),
      ewp₁.wp i (fun o st' => (Acc₁ i o st st' ∧ Kacc o st') ∨ Knon o st') st →
      buchiProgress ewp₂ Acc₂ (fun pair _ => Knon pair.1 pair.2)
        (fun m _ => DWP ewp₂ m
          (fun pair _ => Kacc pair.1 pair.2 ∨ Knon pair.1 pair.2) PUnit.unit)
        (h i st) PUnit.unit)
    {t : ITree E₁ R} {Q : R → H → Prop} {st : H}
    (h_io : InfOften ewp₁ Acc₁ Q t st) :
    InfOften ewp₂ Acc₂ (fun pair _ => Q pair.1 pair.2)
      (ITree.interpState h t st) PUnit.unit := by
  let X : ITree E₂ (R × H) → PUnit.{u + 1} → Prop := fun u _ =>
    (∃ t₀ st₀, u = ITree.interpState h t₀ st₀ ∧
      InfOften ewp₁ Acc₁ Q t₀ st₀) ∨
    (∃ (i : E₁.I) (m : ITree E₂ (E₁.O i × H)) (k : E₁.O i → ITree E₁ R),
      u = (m >>= fun (o, st') => .tau (ITree.interpState h (k o) st')) ∧
      DWP ewp₂ m (fun pair _ => InfOften ewp₁ Acc₁ Q (k pair.1) pair.2)
        PUnit.unit)
  have h_main : ∀ (t₀ : ITree E₁ R) (st₀ : H), InfOften ewp₁ Acc₁ Q t₀ st₀ →
      buchiProgress ewp₂ Acc₂ (fun pair _ => Q pair.1 pair.2) X
        (ITree.interpState h t₀ st₀) PUnit.unit := by
    intro t₀ st₀ ht₀
    refine InfOften.progress_induct
      (fun t₁ st₁ => buchiProgress ewp₂ Acc₂ (fun pair _ => Q pair.1 pair.2) X
        (ITree.interpState h t₁ st₁) PUnit.unit) ?_ ht₀
    intro t₁ st₁ hx
    cases h_obs : t₁.observe with
    | ret r =>
      simp only [h_obs] at hx
      rw [eq_ret_of_observe h_obs, interpState_ret, buchiProgress.ret_iff]
      exact hx
    | tau t₁' =>
      simp only [h_obs] at hx
      rw [eq_tau_of_observe h_obs, interpState_tau, buchiProgress.tau_iff]
      exact hx.2
    | vis i k =>
      simp only [h_obs] at hx
      rw [eq_vis_of_observe h_obs, interpState_vis]
      have h_l := h_link i (fun o st' => InfOften ewp₁ Acc₁ Q (k o) st')
        (fun o st' => InfOften ewp₁ Acc₁ Q (k o) st' ∧
          buchiProgress ewp₂ Acc₂ (fun pair _ => Q pair.1 pair.2) X
            (ITree.interpState h (k o) st') PUnit.unit) st₁
        (ewp₁.mono
          (fun _ _ hp => hp.2.elim (fun ha => Or.inl ⟨ha, hp.1⟩)
            (fun hpre => Or.inr ⟨hp.1, hpre⟩)) hx)
      refine buchiProgress.induct
        (fun m _ => buchiProgress ewp₂ Acc₂ (fun pair _ => Q pair.1 pair.2) X
          (m >>= fun (o, st') => .tau (ITree.interpState h (k o) st'))
          PUnit.unit) ?_ h_l
      intro m ⟨⟩ hm
      cases hm_obs : m.observe with
      | ret pair =>
        rcases pair with ⟨o, st'⟩
        simp only [hm_obs] at hm
        rw [eq_ret_of_observe hm_obs, ret_bind, buchiProgress.tau_iff]
        exact hm.2
      | tau m' =>
        simp only [hm_obs] at hm
        rw [eq_tau_of_observe hm_obs, tau_bind, buchiProgress.tau_iff]
        exact hm
      | vis j c =>
        simp only [hm_obs] at hm
        rw [eq_vis_of_observe hm_obs, vis_bind, buchiProgress.vis_iff]
        exact ewp₂.mono
          (fun o₂ _ hp => hp.imp
            (And.imp id (fun hd => Or.inr ⟨i, c o₂, k, rfl,
              DWP.mono (fun _ _ hq => hq.elim id And.left) hd⟩)) id) hm
  refine InfOften.coinduct X ?_ (Or.inl ⟨t, st, rfl, h_io⟩)
  rintro u ⟨⟩ (⟨t₀, st₀, rfl, ht₀⟩ | ⟨i, m, k, rfl, hm⟩)
  · exact h_main t₀ st₀ ht₀
  · refine DWP.induct
      (fun m _ => buchiProgress ewp₂ Acc₂ (fun pair _ => Q pair.1 pair.2) X
        (m >>= fun (o, st') => .tau (ITree.interpState h (k o) st'))
        PUnit.unit) ?_ hm
    intro m ⟨⟩ hm
    cases hm_obs : m.observe with
    | ret pair =>
      rcases pair with ⟨o, st'⟩
      simp only [hm_obs] at hm
      rw [eq_ret_of_observe hm_obs, ret_bind, buchiProgress.tau_iff]
      exact h_main (k o) st' hm
    | tau m' =>
      simp only [hm_obs] at hm
      rw [eq_tau_of_observe hm_obs, tau_bind, buchiProgress.tau_iff]
      exact hm
    | vis j c =>
      simp only [hm_obs] at hm
      rw [eq_vis_of_observe hm_obs, vis_bind, buchiProgress.vis_iff]
      exact ewp₂.mono (fun _ _ hp => Or.inr hp) hm

section InfOftenAdequacy

variable {E : Effect.{u}} {R : Type u} [FaultEffect E]

private theorem infOften_pure_reaches {ewp : EffectWP E}
    [h_sound : PureSoundWP ewp]
    {AccEdge : (i : E.I) → E.O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop}
    {Q : R → PUnit.{u + 1} → Prop} {t u : ITree E R} {tr : List (Event E)}
    (h_reach : Reaches t tr u) (h : InfOften ewp AccEdge Q t PUnit.unit) :
    InfOften ewp AccEdge Q u PUnit.unit := by
  induction h_reach with
  | refl => exact h
  | tau ht _ ih =>
    rw [eq_tau_of_observe ht, InfOften.tau_iff] at h; exact ih h
  | vis hv _ o _ ih =>
    rw [eq_vis_of_observe hv, InfOften.vis_iff] at h
    exact ih ((h_sound.sound h).2 o)

omit [FaultEffect E] in
private theorem infOften_stabilizes {S : Type u} {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t : ITree E R} {s : S} (h : InfOften ewp AccEdge Q t s) :
    ∃ u' : ITree E R, TauStar t u' ∧ ∀ w, u'.observe ≠ .tau w := by
  refine buchiProgress.induct
    (fun x _ => ∃ u', TauStar x u' ∧ ∀ w, u'.observe ≠ .tau w) ?_
    h.toBuchiProgress
  intro x _ hx
  cases h_obs : x.observe with
  | ret _ =>
    exact ⟨x, .refl x, fun _ hw => by rw [h_obs] at hw; nomatch hw⟩
  | tau x' =>
    simp only [h_obs] at hx
    rcases hx with ⟨u', hs, hnt⟩
    exact ⟨u', .step h_obs hs, hnt⟩
  | vis _ _ =>
    exact ⟨x, .refl x, fun _ hw => by rw [h_obs] at hw; nomatch hw⟩

/--
Stateless adequacy of Büchi recurrence: `InfOften` over a `PureSoundWP`
transformer guarantees `TreeSafe t`, reactive productivity (no reachable
residual silently diverges) and the postcondition on every return.
-/
theorem infOften_pure_adequacy {ewp : EffectWP E} [PureSoundWP ewp]
    {AccEdge : (i : E.I) → E.O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop}
    {t : ITree E R} {post : R → Prop}
    (h : InfOften ewp AccEdge (fun r _ => post r) t PUnit.unit) :
    TreeSafe t ∧ Productive t ∧ ¬ MayDiverge t ∧
      ∀ tr r, ReachesRet t tr r → post r := by
  have h_part := dwlp_pure_adequacy h.toDWLP
  have h_prod : Productive t :=
    fun _ _ h_reach => infOften_stabilizes (infOften_pure_reaches h_reach h)
  exact ⟨h_part.1, h_prod, productive_not_mayDiverge h_prod, h_part.2⟩

/--
$\Box\Diamond$ reading of `InfOften`: at **every** reachable residual, strict
step eventuality of an accepting edge (or a `Q`-return) holds again.
-/
theorem infOften_coAlways_eventuallyStep {ewp : EffectWP E}
    [h_sound : PureSoundWP ewp]
    {AccEdge : (i : E.I) → E.O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop}
    {Q : R → PUnit.{u + 1} → Prop} {t : ITree E R}
    (h : InfOften ewp AccEdge Q t PUnit.unit) :
    CoAlways (fun x => EventuallyStep ewp AccEdge Q x PUnit.unit) t := by
  refine CoAlways.coinduct _
    (fun x => InfOften ewp AccEdge Q x PUnit.unit) ?_ t h
  intro x hx
  refine ⟨hx.toEventuallyStep, ?_⟩
  cases h_obs : x.observe with
  | ret _ => trivial
  | tau x' =>
    rw [eq_tau_of_observe h_obs, InfOften.tau_iff] at hx; exact hx
  | vis i k =>
    rw [eq_vis_of_observe h_obs, InfOften.vis_iff] at hx
    exact (h_sound.sound hx).2

end InfOftenAdequacy

/-! ## 4. Monotone-Chain / `CofixA` Continuity Laws for `ITree.iter` -/

section ContinuityClasses

variable {S : Type u} {E : Effect.{u}}

/--
One-step co-continuity (continuity for decreasing $\omega$-chains): the
transformer commutes with countable *decreasing* intersections of
postconditions. Demonic (`∀`) and deterministic transformers satisfy it;
unboundedly angelic ones do not (`not_always_iter_continuity_angelic`).
-/
class DownContinuous (ewp : StateEffectWP S E) : Prop where
  iInf : ∀ {i : E.I} {P : Nat → E.O i → S → Prop} {s : S},
    (∀ n o s', P (n + 1) o s' → P n o s') →
    (∀ n, ewp.wp i (P n) s) → ewp.wp i (fun o s' => ∀ n, P n o s') s

/--
One-step Scott continuity (continuity for increasing $\omega$-chains): the
transformer commutes with countable *increasing* unions of postconditions.
Angelic (`∃`) and deterministic transformers satisfy it; unboundedly demonic
ones do not (`not_dwp_iter_continuity_unbounded`).
-/
class UpContinuous (ewp : StateEffectWP S E) : Prop where
  iSup : ∀ {i : E.I} {P : Nat → E.O i → S → Prop} {s : S},
    (∀ n o s', P n o s' → P (n + 1) o s') →
    ewp.wp i (fun o s' => ∃ n, P n o s') s → ∃ n, ewp.wp i (P n) s

instance (S : Type u) : DownContinuous (emptyWP S) where
  iInf {i} := PEmpty.elim i

instance (S : Type u) : UpContinuous (emptyWP S) where
  iSup {i} := PEmpty.elim i

instance (S Err : Type u) : DownContinuous (failWP S Err) where
  iInf _ h := h 0

instance (S Err : Type u) : UpContinuous (failWP S Err) where
  iSup _ h := False.elim h

instance (S Obs : Type u) : DownContinuous (obsIgnoreWP S Obs) where
  iInf _ h := h

instance (S Obs : Type u) : UpContinuous (obsIgnoreWP S Obs) where
  iSup _ h := h

instance (Obs : Type u) : DownContinuous (obsTraceWP Obs) where
  iInf {i} _ _ _ h := match i with | .emit _ => h

instance (Obs : Type u) : UpContinuous (obsTraceWP Obs) where
  iSup {i} _ _ _ h := match i with | .emit _ => h

instance (S : Type u) : DownContinuous (stateWP S) where
  iInf {op} _ _ _ h := match op with | .get => h | .put _ => h

instance (S : Type u) : UpContinuous (stateWP S) where
  iSup {op} _ _ _ h := match op with | .get => h | .put _ => h

/-- Demonic choice over any answer type is co-continuous. -/
instance (S α : Type u) : DownContinuous (pickWP S α) where
  iInf _ h := ⟨(h 0).1, fun o n => (h n).2 o⟩

/-- Angelic choice over any answer type is Scott continuous. -/
instance (S α : Type u) : UpContinuous (witnessWP S α) where
  iSup _ h := h.elim fun o ho => ho.elim fun n hn => ⟨n, o, hn⟩

instance (S Req : Type u) (Resp : Req → Type u) :
    DownContinuous (unconstrainedCallWP S Req Resp) where
  iInf {i} _ _ _ h := match i with | .call _ => fun resp n => h n resp

instance (S : Type u) {Req : Type u} {Resp : Req → Type u}
    (C : CallContract Req Resp) : DownContinuous (contractCallWP S C) where
  iInf {i} _ _ _ h :=
    match i with
    | .call _ => ⟨(h 0).1, fun resp hp n => (h n).2 resp hp⟩

instance (E : Effect.{u}) [FaultEffect E] : DownContinuous (eventTraceWP E) where
  iInf _ h := ⟨(h 0).1, fun o n => (h n).2 o⟩

instance {E₁ E₂ : Effect.{u}} (w₁ : StateEffectWP S E₁)
    (w₂ : StateEffectWP S E₂) [h₁ : DownContinuous w₁]
    [h₂ : DownContinuous w₂] : DownContinuous (w₁.sum w₂) where
  iInf {i} _ _ ha h :=
    match i with
    | .inl _ => h₁.iInf ha h
    | .inr _ => h₂.iInf ha h

instance {E₁ E₂ : Effect.{u}} (w₁ : StateEffectWP S E₁)
    (w₂ : StateEffectWP S E₂) [h₁ : UpContinuous w₁]
    [h₂ : UpContinuous w₂] : UpContinuous (w₁.sum w₂) where
  iSup {i} _ _ ha h :=
    match i with
    | .inl _ => h₁.iSup ha h
    | .inr _ => h₂.iSup ha h

instance (ewp : StateEffectWP S E) (Inv : S → Prop)
    [h : DownContinuous ewp] : DownContinuous (guardInvWP ewp Inv) where
  iInf ha hw :=
    ewp.mono (fun _ _ hk => ⟨(hk 0).1, fun n => (hk n).2⟩)
      (h.iInf (fun n o s' hk => ⟨hk.1, ha n o s' hk.2⟩) hw)

instance (ewp : StateEffectWP S E) (Inv : S → Prop)
    [h : UpContinuous ewp] : UpContinuous (guardInvWP ewp Inv) where
  iSup ha hw :=
    h.iSup (fun n o s' hk => ⟨hk.1, ha n o s' hk.2⟩)
      (ewp.mono (fun _ _ hk => hk.2.elim fun n hn => ⟨n, hk.1, hn⟩) hw)

instance (ewp : StateEffectWP S E)
    (StepRel : (i : E.I) → E.O i → S → S → Prop)
    [h : DownContinuous ewp] : DownContinuous (guardStepWP ewp StepRel) where
  iInf ha hw :=
    ewp.mono (fun _ _ hk => ⟨(hk 0).1, fun n => (hk n).2⟩)
      (h.iInf (fun n o s' hk => ⟨hk.1, ha n o s' hk.2⟩) hw)

instance (ewp : StateEffectWP S E)
    (StepRel : (i : E.I) → E.O i → S → S → Prop)
    [h : UpContinuous ewp] : UpContinuous (guardStepWP ewp StepRel) where
  iSup ha hw :=
    h.iSup (fun n o s' hk => ⟨hk.1, ha n o s' hk.2⟩)
      (ewp.mono (fun _ _ hk => hk.2.elim fun n hn => ⟨n, hk.1, hn⟩) hw)

private theorem up_chain_le {P : Nat → Prop} (h : ∀ n, P n → P (n + 1))
    {n m : Nat} (h_le : n ≤ m) (hp : P n) : P m := by
  induction h_le with
  | refl => exact hp
  | step _ ih => exact h _ ih

/--
Demonic choice over a *finitely enumerable* answer type is Scott continuous
(bounded nondeterminism).
-/
theorem pickWP_upContinuous_of_finite (S : Type u) {α : Type u}
    (l : List α) (h_all : ∀ a : α, a ∈ l) : UpContinuous (pickWP S α) where
  iSup {_ P s} h_mono hw := by
    have h_list : ∀ l' : List α, ∃ N, ∀ a, a ∈ l' → P N a s := by
      intro l'
      induction l' with
      | nil => exact ⟨0, fun _ ha => nomatch ha⟩
      | cons b l'' ih =>
        obtain ⟨N₁, hN₁⟩ := ih
        obtain ⟨N₂, hN₂⟩ := hw.2 b
        refine ⟨N₁ + N₂, fun a ha => ?_⟩
        rcases List.mem_cons.1 ha with rfl | ha'
        · exact up_chain_le (fun n => h_mono n a s) (Nat.le_add_left N₂ N₁) hN₂
        · exact up_chain_le (fun n => h_mono n a s) (Nat.le_add_right N₁ N₂)
            (hN₁ a ha')
    obtain ⟨N, hN⟩ := h_list l
    exact ⟨N, hw.1, fun o => hN o (h_all o)⟩

instance (S : Type) : UpContinuous (pickWP S Bool) :=
  pickWP_upContinuous_of_finite S [true, false]
    (fun b => by cases b <;> simp)

private theorem down_chain_le {P : Nat → Prop} (h : ∀ n, P (n + 1) → P n)
    {n m : Nat} (h_le : n ≤ m) (hp : P m) : P n := by
  induction h_le with
  | refl => exact hp
  | step _ ih => exact ih (h _ hp)

/--
Angelic choice over a *finitely enumerable* answer type is co-continuous
(König's lemma for finitely branching angelic choice).
-/
theorem witnessWP_downContinuous_of_finite (S : Type u) {α : Type u}
    (l : List α) (h_all : ∀ a : α, a ∈ l) : DownContinuous (witnessWP S α) where
  iInf {_ P s} h_anti hw := by
    have h_list : ∀ (l' : List α) (k : Nat),
        (∀ n, ∃ a, a ∈ l' ∧ P (n + k) a s) → ∃ a, a ∈ l' ∧ ∀ n, P n a s := by
      intro l'
      induction l' with
      | nil =>
        intro k h
        obtain ⟨a, ha, _⟩ := h 0
        exact nomatch ha
      | cons b l'' ih =>
        intro k h
        by_cases hb : ∀ n, P n b s
        · exact ⟨b, List.mem_cons.2 (Or.inl rfl), hb⟩
        · obtain ⟨n₀, hn₀⟩ := Classical.not_forall.1 hb
          have h_tail : ∀ n, ∃ a, a ∈ l'' ∧ P (n + (k + n₀)) a s := by
            intro n
            obtain ⟨a, ha, hp⟩ := h (n + n₀)
            rcases List.mem_cons.1 ha with h_eq | ha'
            · subst h_eq
              exact absurd
                (down_chain_le (P := fun j => P j a s) (n := n₀)
                  (m := n + n₀ + k) (fun j => h_anti j a s) (by omega) hp) hn₀
            · exact ⟨a, ha', by rwa [show n + (k + n₀) = n + n₀ + k by omega]⟩
          obtain ⟨a, ha, h_a⟩ := ih (k + n₀) h_tail
          exact ⟨a, List.mem_cons.2 (Or.inr ha), h_a⟩
    obtain ⟨a, _, ha⟩ :=
      h_list l 0 (fun n => (hw n).elim fun a hp => ⟨a, h_all a, hp⟩)
    exact ⟨a, ha⟩

instance (S : Type) : DownContinuous (witnessWP S Bool) :=
  witnessWP_downContinuous_of_finite S [true, false]
    (fun b => by cases b <;> simp)

end ContinuityClasses

section BuchiSpecInstances

variable {S QState : Type u} {E : Effect.{u}} {R : Type u}

instance (spec : BuchiSpec S QState E R) [h : UpContinuous spec.ewp] :
    UpContinuous spec.prodWP where
  iSup {i P qs} ha hw :=
    h.iSup
      (P := fun n o s' => ∃ q', spec.step qs.1 i o qs.2 s' q' ∧ P n o (q', s'))
      (fun n _ _ hk => hk.elim fun q' hq => ⟨q', hq.1, ha n _ _ hq.2⟩)
      (spec.ewp.mono
        (fun _ _ hk => hk.elim fun q' hq =>
          hq.2.elim fun n hn => ⟨n, q', hq.1, hn⟩) hw)

instance (spec : BuchiSpec S QState E R) [UpContinuous spec.ewp] :
    UpContinuous spec.monitorWP :=
  inferInstanceAs (UpContinuous (guardInvWP spec.prodWP spec.invPred))

/-- A deterministic monitor over a co-continuous transformer is co-continuous. -/
theorem BuchiSpec.prodWP_downContinuous (spec : BuchiSpec S QState E R)
    [h : DownContinuous spec.ewp]
    (h_det : ∀ q i o s s' q₁ q₂,
      spec.step q i o s s' q₁ → spec.step q i o s s' q₂ → q₁ = q₂) :
    DownContinuous spec.prodWP where
  iInf {i P qs} ha hw :=
    spec.ewp.mono
      (fun _ _ hk => (hk 0).elim fun q' hq =>
        ⟨q', hq.1, fun n => (hk n).elim fun _ hq'' =>
          (h_det _ _ _ _ _ _ _ hq''.1 hq.1) ▸ hq''.2⟩)
      (h.iInf
        (P := fun n o s' =>
          ∃ q', spec.step qs.1 i o qs.2 s' q' ∧ P n o (q', s'))
        (fun n _ _ hk => hk.elim fun q' hq => ⟨q', hq.1, ha n _ _ hq.2⟩) hw)

end BuchiSpecInstances

section IterChain

variable {S : Type u} {E : Effect.{u}} {I R : Type u}

/--
Finite-unfolding $\omega$-chain of `ITree.iter`: `iterChain 0` is the bottom
element `ITree.spin`, and `iterChain (n + 1)` runs one more loop iteration
before falling back to `iterChain n`.
-/
def iterChain (n : Nat) (body : I → ITree E (I ⊕ R)) (init : I) : ITree E R :=
  match n with
  | 0 => ITree.spin
  | n + 1 =>
    body init >>= Sum.elim (fun next => .tau (iterChain n body next)) .ret

@[simp]
theorem iterChain_zero (body : I → ITree E (I ⊕ R)) (init : I) :
    iterChain 0 body init = ITree.spin :=
  rfl

@[simp]
theorem iterChain_succ (n : Nat) (body : I → ITree E (I ⊕ R)) (init : I) :
    iterChain (n + 1) body init =
      (body init >>=
        Sum.elim (fun next => ITree.tau (iterChain n body next)) ITree.ret) :=
  rfl

private theorem ofITree_bind_congr_le {A B : Type u} (n : Nat) :
    ∀ (cur : ITree E A) (k₁ k₂ : A → ITree E B),
      (∀ a d, d ≤ n → ofITree d (k₁ a) = ofITree d (k₂ a)) →
      ofITree n (cur >>= k₁) = ofITree n (cur >>= k₂) := by
  induction n with
  | zero => intro _ _ _ _; rfl
  | succ m ih =>
    intro cur k₁ k₂ hk
    cases hc : cur.observe with
    | ret a =>
      rw [eq_ret_of_observe hc, ret_bind, ret_bind]
      exact hk a (m + 1) (Nat.le_refl _)
    | tau cur' =>
      rw [eq_tau_of_observe hc, tau_bind, tau_bind, ofITree_tau, ofITree_tau]
      exact congrArg CofixA.tau
        (ih cur' k₁ k₂ (fun a d hd => hk a d (Nat.le_succ_of_le hd)))
    | vis i c =>
      rw [eq_vis_of_observe hc, vis_bind, vis_bind, ofITree_vis, ofITree_vis]
      exact congrArg (CofixA.vis i) (funext fun o =>
        ih (c o) k₁ k₂ (fun a d hd => hk a d (Nat.le_succ_of_le hd)))

/--
**Projective `CofixA` convergence**: every depth-`n` approximant of
`iterChain m` coincides with that of `ITree.iter` as soon as `n ≤ m`.
-/
theorem ofITree_iterChain (body : I → ITree E (I ⊕ R)) :
    ∀ {n m : Nat}, n ≤ m → ∀ init : I,
      ofITree n (iterChain m body init) = ofITree n (ITree.iter body init) := by
  intro n m
  induction m generalizing n with
  | zero =>
    intro h init
    have h0 : n = 0 := Nat.eq_zero_of_le_zero h
    subst h0; rfl
  | succ m ih =>
    intro h init
    rw [iterChain_succ, iter_unfold]
    refine ofITree_bind_congr_le n (body init) _ _ ?_
    rintro (next | r) d hd
    · cases d with
      | zero => rfl
      | succ d' =>
        show ofITree (d' + 1) (ITree.tau (iterChain m body next)) =
          ofITree (d' + 1) (ITree.tau (ITree.iter body next))
        rw [ofITree_tau, ofITree_tau]
        exact congrArg CofixA.tau (ih (by omega) next)
    · rfl

/--
`iterChain` converges to `ITree.iter` in the projective `CofixA` topology:
every finite observation depth is eventually stable along the chain.
-/
theorem iterChain_converges (body : I → ITree E (I ⊕ R)) (init : I) (n : Nat) :
    ∃ N, ∀ m, N ≤ m →
      ofITree n (iterChain m body init) = ofITree n (ITree.iter body init) :=
  ⟨n, fun _ h => ofITree_iterChain body h init⟩

/-- `ITree.iter` is the *unique* limit of the chain `iterChain`. -/
theorem iter_eq_of_iterChain_limit (body : I → ITree E (I ⊕ R)) (init : I)
    (t : ITree E R)
    (h : ∀ n, ofITree n t = ofITree n (iterChain n body init)) :
    t = ITree.iter body init :=
  ofITree_inj.1 fun n =>
    (h n).trans (ofITree_iterChain body (Nat.le_refl n) init)

/-! ### 4.1 Safety Continuity ($\bigwedge_n$) -/

/-- Safety of the loop restricts to every finite unfolding. -/
theorem Always.iterChain_of_iter {ewp : StateEffectWP S E} {Inv : S → Prop}
    {Q : R → S → Prop} (body : I → ITree E (I ⊕ R)) :
    ∀ (n : Nat) {init : I} {s : S},
      Always ewp Inv Q (ITree.iter body init) s →
      Always ewp Inv Q (iterChain n body init) s
  | 0, _, _, h => Always.spin ewp Q h.inv
  | n + 1, init, s, h => by
    rw [iter_unfold, Always.bind_iff] at h
    rw [iterChain_succ]
    refine Always.bind (Always.mono (fun _ hi => hi) ?_ h)
    rintro (next | r) s' ha
    · exact Always.tau
        (Always.iterChain_of_iter body n ((Always.tau_iff _ _ _ _ _).1 ha))
    · exact ha

/-- The safety chain is decreasing. -/
theorem Always.iterChain_antitone {ewp : StateEffectWP S E} {Inv : S → Prop}
    {Q : R → S → Prop} (body : I → ITree E (I ⊕ R)) :
    ∀ (n : Nat) {init : I} {s : S},
      Always ewp Inv Q (iterChain (n + 1) body init) s →
      Always ewp Inv Q (iterChain n body init) s
  | 0, _, _, h => Always.spin ewp Q h.inv
  | n + 1, init, s, h => by
    rw [iterChain_succ, Always.bind_iff] at h
    rw [iterChain_succ]
    refine Always.bind (Always.mono (fun _ hi => hi) ?_ h)
    rintro (next | r) s' ha
    · exact Always.tau
        (Always.iterChain_antitone body n ((Always.tau_iff _ _ _ _ _).1 ha))
    · exact ha

/--
**Safety continuity ($\bigwedge_n$).** For a co-continuous transformer, `Always`
on `ITree.iter` is exactly `Always` on every finite unfolding `iterChain n`
(each of which ends in the safe bottom element `ITree.spin`).
-/
theorem always_iter_iff_forall_iterChain {ewp : StateEffectWP S E}
    [h_cont : DownContinuous ewp] (Inv : S → Prop) (Q : R → S → Prop)
    (body : I → ITree E (I ⊕ R)) (init : I) (s : S) :
    Always ewp Inv Q (ITree.iter body init) s ↔
      ∀ n, Always ewp Inv Q (iterChain n body init) s := by
  refine ⟨fun h n => Always.iterChain_of_iter body n h, fun h => ?_⟩
  let contN : Nat → I ⊕ R → ITree E R := fun n =>
    Sum.elim (fun next => .tau (iterChain n body next)) .ret
  let cont : I ⊕ R → ITree E R :=
    Sum.elim (fun next => .tau (ITree.iter body next)) .ret
  have h_anti : ∀ (cur : ITree E (I ⊕ R)) (s₀ : S) (n : Nat),
      Always ewp Inv Q (cur >>= contN (n + 1)) s₀ →
      Always ewp Inv Q (cur >>= contN n) s₀ := by
    intro cur s₀ n hc
    rw [Always.bind_iff] at hc ⊢
    refine Always.mono (fun _ hi => hi) ?_ hc
    rintro (next | r) s' ha
    · exact Always.tau
        (Always.iterChain_antitone body n ((Always.tau_iff _ _ _ _ _).1 ha))
    · exact ha
  refine Always.coinduct
    (fun u s₀ => ∃ cur : ITree E (I ⊕ R), u = (cur >>= cont) ∧
      ∀ n, Always ewp Inv Q (cur >>= contN n) s₀)
    ?_ ⟨body init, iter_unfold body init, fun n => h (n + 1)⟩
  rintro u s₀ ⟨cur, rfl, h_cur⟩
  refine ⟨(h_cur 0).inv, ?_⟩
  cases h_obs : cur.observe with
  | ret res =>
    have hEq := eq_ret_of_observe h_obs
    cases res with
    | inl next =>
      rw [hEq, ret_bind]
      dsimp only [cont, Sum.elim]; rw [ITree.observe_tau]
      refine ⟨body next, iter_unfold body next, fun n => ?_⟩
      have h1 := h_cur (n + 1)
      rw [hEq, ret_bind] at h1
      exact (Always.tau_iff _ _ _ _ _).1 h1
    | inr r =>
      rw [hEq, ret_bind]
      dsimp only [cont, Sum.elim]; rw [ITree.observe_ret]
      have h0 := h_cur 0
      rw [hEq, ret_bind] at h0
      exact ((Always.ret_iff _ _ _ _ _).1 h0).2
  | tau cur' =>
    have hEq := eq_tau_of_observe h_obs
    rw [hEq, tau_bind, ITree.observe_tau]
    refine ⟨cur', rfl, fun n => ?_⟩
    have hn := h_cur n
    rw [hEq, tau_bind] at hn
    exact (Always.tau_iff _ _ _ _ _).1 hn
  | vis i c =>
    have hEq := eq_vis_of_observe h_obs
    rw [hEq, vis_bind, ITree.observe_vis]
    have h_all : ∀ n,
        ewp.wp i (fun o s' => Always ewp Inv Q (c o >>= contN n) s') s₀ := by
      intro n
      have hn := h_cur n
      rw [hEq, vis_bind] at hn
      exact ((Always.vis_iff _ _ _ _ _ _).1 hn).2
    exact ewp.mono (fun o _ h_o => ⟨c o, rfl, h_o⟩)
      (h_cont.iInf (fun n o s' => h_anti (c o) s' n) h_all)

/-! ### 4.2 Finite-Horizon Eventuality Continuity ($\bigvee_n$) -/

/-- The `Until` chain is increasing. -/
theorem Until.iterChain_succ {ewp : StateEffectWP S E}
    {Hold Target : S → Prop} {Q : R → S → Prop}
    (body : I → ITree E (I ⊕ R)) :
    ∀ (n : Nat) {init : I} {s : S},
      Until ewp Hold Target Q (iterChain n body init) s →
      Until ewp Hold Target Q (iterChain (n + 1) body init) s
  | 0, _, _, h => Until.here ((until_spin_iff ewp Hold Target Q _).1 h)
  | n + 1, init, s, h => by
    rw [ITreeBuchi.iterChain_succ, Until.bind_iff] at h
    rw [ITreeBuchi.iterChain_succ (n + 1)]
    refine Until.bind (Until.mono (fun _ hh => hh) (fun _ ht => ht) ?_ h)
    rintro (next | r) s' hu
    · exact Until.tau
        (Until.iterChain_succ body n ((Until.tau_iff _ _ _ _ _ _).1 hu))
    · exact hu

/-- `Until` on any finite unfolding transfers to the loop. -/
theorem Until.iter_of_iterChain {ewp : StateEffectWP S E}
    {Hold Target : S → Prop} {Q : R → S → Prop}
    (body : I → ITree E (I ⊕ R)) :
    ∀ (n : Nat) {init : I} {s : S},
      Until ewp Hold Target Q (iterChain n body init) s →
      Until ewp Hold Target Q (ITree.iter body init) s
  | 0, _, _, h => Until.here ((until_spin_iff ewp Hold Target Q _).1 h)
  | n + 1, init, s, h => by
    rw [ITreeBuchi.iterChain_succ, Until.bind_iff] at h
    rw [iter_unfold]
    refine Until.bind (Until.mono (fun _ hh => hh) (fun _ ht => ht) ?_ h)
    rintro (next | r) s' hu
    · exact Until.tau
        (Until.iter_of_iterChain body n ((Until.tau_iff _ _ _ _ _ _).1 hu))
    · exact hu

/--
**Finite-horizon continuity ($\bigvee_n$) for `Until`.** For a Scott-continuous
transformer, `Until` on `ITree.iter` holds exactly when it already holds on
some finite unfolding `iterChain n`.
-/
theorem until_iter_iff_exists_iterChain {ewp : StateEffectWP S E}
    [h_cont : UpContinuous ewp] (Hold Target : S → Prop) (Q : R → S → Prop)
    (body : I → ITree E (I ⊕ R)) (init : I) (s : S) :
    Until ewp Hold Target Q (ITree.iter body init) s ↔
      ∃ n, Until ewp Hold Target Q (iterChain n body init) s := by
  refine ⟨fun h => ?_, fun ⟨n, hn⟩ => Until.iter_of_iterChain body n hn⟩
  let contN : Nat → I ⊕ R → ITree E R := fun n =>
    Sum.elim (fun next => .tau (iterChain n body next)) .ret
  let cont : I ⊕ R → ITree E R :=
    Sum.elim (fun next => .tau (ITree.iter body next)) .ret
  have h_mono : ∀ (cur : ITree E (I ⊕ R)) (s₀ : S) (n : Nat),
      Until ewp Hold Target Q (cur >>= contN n) s₀ →
      Until ewp Hold Target Q (cur >>= contN (n + 1)) s₀ := by
    intro cur s₀ n hc
    rw [Until.bind_iff] at hc ⊢
    refine Until.mono (fun _ hh => hh) (fun _ ht => ht) ?_ hc
    rintro (next | r) s' hu
    · exact Until.tau
        (Until.iterChain_succ body n ((Until.tau_iff _ _ _ _ _ _).1 hu))
    · exact hu
  have key : ∀ (u : ITree E R) (s₀ : S), Until ewp Hold Target Q u s₀ →
      ∀ cur : ITree E (I ⊕ R), u = (cur >>= cont) →
        ∃ n, Until ewp Hold Target Q (cur >>= contN n) s₀ := by
    intro u s₀ hu
    refine Until.induct
      (fun u s₀ => ∀ cur : ITree E (I ⊕ R), u = (cur >>= cont) →
        ∃ n, Until ewp Hold Target Q (cur >>= contN n) s₀) ?_ hu
    intro u s₀ hx cur h_eq
    subst h_eq
    rcases hx with ht | ⟨hh, hx⟩
    · exact ⟨0, Until.here ht⟩
    · cases h_obs : cur.observe with
      | ret res =>
        have hEq := eq_ret_of_observe h_obs
        rw [hEq, ret_bind] at hx
        cases res with
        | inl next =>
          dsimp only [cont, Sum.elim] at hx
          rw [ITree.observe_tau] at hx
          obtain ⟨n, hn⟩ := hx (body next) (iter_unfold body next)
          refine ⟨n + 1, ?_⟩
          rw [hEq, ret_bind]
          exact Until.tau hn
        | inr r =>
          dsimp only [cont, Sum.elim] at hx
          rw [ITree.observe_ret] at hx
          refine ⟨0, ?_⟩
          rw [hEq, ret_bind]
          exact Until.ret hh hx
      | tau cur' =>
        have hEq := eq_tau_of_observe h_obs
        rw [hEq, tau_bind, ITree.observe_tau] at hx
        obtain ⟨n, hn⟩ := hx cur' rfl
        refine ⟨n, ?_⟩
        rw [hEq, tau_bind]
        exact Until.tau hn
      | vis i c =>
        have hEq := eq_vis_of_observe h_obs
        rw [hEq, vis_bind, ITree.observe_vis] at hx
        have hx' : ewp.wp i
            (fun o s' => ∃ n, Until ewp Hold Target Q (c o >>= contN n) s')
            s₀ :=
          ewp.mono (fun o _ hp => hp (c o) rfl) hx
        obtain ⟨n, hn⟩ := h_cont.iSup (fun n o s' => h_mono (c o) s' n) hx'
        refine ⟨n, ?_⟩
        rw [hEq, vis_bind]
        exact Until.vis hh hn
  obtain ⟨n, hn⟩ := key _ s h (body init) (iter_unfold body init)
  exact ⟨n + 1, hn⟩

/--
**Finite-horizon eventuality continuity ($\bigvee_n$).** No side condition on
the initial state is needed: if the target already holds, both sides hold.
-/
theorem eventually_iter_iff_exists_iterChain {ewp : StateEffectWP S E}
    [UpContinuous ewp] (Target : S → Prop) (Q : R → S → Prop)
    (body : I → ITree E (I ⊕ R)) (init : I) (s : S) :
    Eventually ewp Target Q (ITree.iter body init) s ↔
      ∃ n, Eventually ewp Target Q (iterChain n body init) s := by
  rw [eventually_iff_until, until_iter_iff_exists_iterChain]
  exact exists_congr fun n => (eventually_iff_until ewp Target Q _ s).symm

/--
**Finite-horizon continuity ($\bigvee_n$) for total correctness.** `DWP` of a
loop over a Scott-continuous transformer is witnessed by a finite unfolding.
-/
theorem dwp_iter_iff_exists_iterChain {ewp : StateEffectWP S E}
    [UpContinuous ewp] (Q : R → S → Prop)
    (body : I → ITree E (I ⊕ R)) (init : I) (s : S) :
    DWP ewp (ITree.iter body init) Q s ↔
      ∃ n, DWP ewp (iterChain n body init) Q s := by
  rw [dwp_iff_until, until_iter_iff_exists_iterChain]
  exact exists_congr fun n => (dwp_iff_until ewp Q _ s).symm

/-- The strict step-eventuality chain is increasing. -/
theorem EventuallyStep.iterChain_succ {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    (body : I → ITree E (I ⊕ R)) :
    ∀ (n : Nat) {init : I} {s : S},
      EventuallyStep ewp AccEdge Q (iterChain n body init) s →
      EventuallyStep ewp AccEdge Q (iterChain (n + 1) body init) s
  | 0, _, _, h => absurd h not_eventuallyStep_spin
  | n + 1, init, s, h => by
    rw [ITreeBuchi.iterChain_succ, EventuallyStep.bind_iff] at h
    rw [ITreeBuchi.iterChain_succ (n + 1)]
    refine EventuallyStep.bind
      (EventuallyStep.mono (fun _ _ _ _ ha => ha) ?_ h)
    rintro (next | r) s' hu
    · exact (EventuallyStep.tau_iff _ _ _ _ _).2
        (EventuallyStep.iterChain_succ body n
          ((EventuallyStep.tau_iff _ _ _ _ _).1 hu))
    · exact hu

/-- Strict step eventuality on a finite unfolding transfers to the loop. -/
theorem EventuallyStep.iter_of_iterChain {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    (body : I → ITree E (I ⊕ R)) :
    ∀ (n : Nat) {init : I} {s : S},
      EventuallyStep ewp AccEdge Q (iterChain n body init) s →
      EventuallyStep ewp AccEdge Q (ITree.iter body init) s
  | 0, _, _, h => absurd h not_eventuallyStep_spin
  | n + 1, init, s, h => by
    rw [ITreeBuchi.iterChain_succ, EventuallyStep.bind_iff] at h
    rw [iter_unfold]
    refine EventuallyStep.bind
      (EventuallyStep.mono (fun _ _ _ _ ha => ha) ?_ h)
    rintro (next | r) s' hu
    · exact (EventuallyStep.tau_iff _ _ _ _ _).2
        (EventuallyStep.iter_of_iterChain body n
          ((EventuallyStep.tau_iff _ _ _ _ _).1 hu))
    · exact hu

/--
**Finite-horizon continuity ($\bigvee_n$) for strict step eventuality**,
unconditionally in the initial state.
-/
theorem eventuallyStep_iter_iff_exists_iterChain {ewp : StateEffectWP S E}
    [h_cont : UpContinuous ewp]
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (body : I → ITree E (I ⊕ R)) (init : I) (s : S) :
    EventuallyStep ewp AccEdge Q (ITree.iter body init) s ↔
      ∃ n, EventuallyStep ewp AccEdge Q (iterChain n body init) s := by
  refine ⟨fun h => ?_,
    fun ⟨n, hn⟩ => EventuallyStep.iter_of_iterChain body n hn⟩
  let contN : Nat → I ⊕ R → ITree E R := fun n =>
    Sum.elim (fun next => .tau (iterChain n body next)) .ret
  let cont : I ⊕ R → ITree E R :=
    Sum.elim (fun next => .tau (ITree.iter body next)) .ret
  have h_mono : ∀ (cur : ITree E (I ⊕ R)) (s₀ : S) (n : Nat),
      EventuallyStep ewp AccEdge Q (cur >>= contN n) s₀ →
      EventuallyStep ewp AccEdge Q (cur >>= contN (n + 1)) s₀ := by
    intro cur s₀ n hc
    rw [EventuallyStep.bind_iff] at hc ⊢
    refine EventuallyStep.mono (fun _ _ _ _ ha => ha) ?_ hc
    rintro (next | r) s' hu
    · exact (EventuallyStep.tau_iff _ _ _ _ _).2
        (EventuallyStep.iterChain_succ body n
          ((EventuallyStep.tau_iff _ _ _ _ _).1 hu))
    · exact hu
  have key : ∀ (u : ITree E R) (s₀ : S), EventuallyStep ewp AccEdge Q u s₀ →
      ∀ cur : ITree E (I ⊕ R), u = (cur >>= cont) →
        ∃ n, EventuallyStep ewp AccEdge Q (cur >>= contN n) s₀ := by
    intro u s₀ hu
    refine EventuallyStep.induct
      (fun u s₀ => ∀ cur : ITree E (I ⊕ R), u = (cur >>= cont) →
        ∃ n, EventuallyStep ewp AccEdge Q (cur >>= contN n) s₀) ?_ hu
    intro u s₀ hx cur h_eq
    subst h_eq
    cases h_obs : cur.observe with
    | ret res =>
      have hEq := eq_ret_of_observe h_obs
      rw [hEq, ret_bind] at hx
      cases res with
      | inl next =>
        dsimp only [cont, Sum.elim] at hx
        rw [ITree.observe_tau] at hx
        obtain ⟨n, hn⟩ := hx (body next) (iter_unfold body next)
        refine ⟨n + 1, ?_⟩
        rw [hEq, ret_bind]
        exact (EventuallyStep.tau_iff _ _ _ _ _).2 hn
      | inr r =>
        dsimp only [cont, Sum.elim] at hx
        rw [ITree.observe_ret] at hx
        refine ⟨0, ?_⟩
        rw [hEq, ret_bind]
        exact (EventuallyStep.ret_iff _ _ _ _ _).2 hx
    | tau cur' =>
      have hEq := eq_tau_of_observe h_obs
      rw [hEq, tau_bind, ITree.observe_tau] at hx
      obtain ⟨n, hn⟩ := hx cur' rfl
      refine ⟨n, ?_⟩
      rw [hEq, tau_bind]
      exact (EventuallyStep.tau_iff _ _ _ _ _).2 hn
    | vis i c =>
      have hEq := eq_vis_of_observe h_obs
      rw [hEq, vis_bind, ITree.observe_vis] at hx
      have hx' : ewp.wp i
          (fun o s' => ∃ n, AccEdge i o s₀ s' ∨
            EventuallyStep ewp AccEdge Q (c o >>= contN n) s') s₀ :=
        ewp.mono
          (fun o _ hp => hp.elim (fun ha => ⟨0, Or.inl ha⟩)
            (fun hpre => (hpre (c o) rfl).elim fun n hn => ⟨n, Or.inr hn⟩)) hx
      obtain ⟨n, hn⟩ := h_cont.iSup
        (fun n o s' hp => hp.imp id (h_mono (c o) s' n)) hx'
      refine ⟨n, ?_⟩
      rw [hEq, vis_bind]
      exact (EventuallyStep.vis_iff _ _ _ _ _ _).2 hn
  obtain ⟨n, hn⟩ := key _ s h (body init) (iter_unfold body init)
  exact ⟨n + 1, hn⟩

/-! ### 4.3 `InfOften` Is Neither $\bigwedge_n$ nor $\bigvee_n$ Continuous -/

/--
Under conjunctivity and excluded miracle, a tree that terminates with `P`
cannot satisfy `InfOften` with a postcondition disjoint from `P`.
-/
theorem not_infOften_of_dwp_disjoint {ewp : StateEffectWP S E}
    [h_conj : StateEffectWP.Conjunctive ewp]
    [h_em : StateEffectWP.ExcludedMiracle ewp]
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {P Q : R → S → Prop}
    (h_dis : ∀ r s', P r s' → ¬ Q r s') {t : ITree E R} {s : S}
    (h : DWP ewp t P s) : ¬ InfOften ewp AccEdge Q t s := by
  refine DWP.induct (fun x s₀ => ¬ InfOften ewp AccEdge Q x s₀) ?_ h
  intro x s₀ hx hio
  cases h_obs : x.observe with
  | ret r =>
    simp only [h_obs] at hx
    rw [eq_ret_of_observe h_obs, InfOften.ret_iff] at hio
    exact h_dis r s₀ hx hio
  | tau x' =>
    simp only [h_obs] at hx
    rw [eq_tau_of_observe h_obs, InfOften.tau_iff] at hio
    exact hx hio
  | vis i k =>
    simp only [h_obs] at hx
    rw [eq_vis_of_observe h_obs, InfOften.vis_iff] at hio
    exact h_em.no_miracle
      (ewp.mono (fun _ _ hp => hp.1 hp.2) (h_conj.conj hx hio))

/--
Every finite unfolding of a diverging loop with terminating iterations ends in
`ITree.spin` and therefore **fails** `InfOften`, whatever the accepting edges.
-/
theorem not_infOften_iterChain_divergingLoop {ewp : StateEffectWP S E}
    [StateEffectWP.Conjunctive ewp] [StateEffectWP.ExcludedMiracle ewp]
    {AccEdge : (i : E.I) → E.O i → S → S → Prop}
    (body : I → ITree E I) (LInv : I → S → Prop)
    (h_term : ∀ a s₀, LInv a s₀ → DWP ewp (body a) LInv s₀)
    (Q : R → S → Prop) :
    ∀ (n : Nat) {init : I} {s : S}, LInv init s →
      ¬ InfOften ewp AccEdge Q
        (iterChain n (fun a => (Sum.inl <$> body a : ITree E (I ⊕ R))) init) s
  | 0, _, _, _ => not_infOften_spin
  | n + 1, init, s, h_init => by
    have h_eq : (Sum.inl <$> body init : ITree E (I ⊕ R)) =
        (body init >>= fun a => ITree.ret (Sum.inl a)) := rfl
    rw [iterChain_succ, InfOften.bind_iff, h_eq, InfOften.bind_iff]
    refine not_infOften_of_dwp_disjoint ?_ (h_term init s h_init)
    intro a s' ha hio
    rw [InfOften.ret_iff] at hio
    exact not_infOften_iterChain_divergingLoop body LInv h_term Q n ha
      ((InfOften.tau_iff _ _ _ _ _).1 hio)

/--
**`InfOften` is not chain-continuous.** For a diverging loop whose iterations
terminate and each take an accepting edge, `InfOften` holds of the loop
although it fails on *every* finite unfolding `iterChain n` (and `DWP` fails
of the loop). Hence `InfOften (iter)` is neither $\bigwedge_n$ nor $\bigvee_n$
of `InfOften (iterChain n)`: the nested $\nu\mu$ fixpoint is strictly more
expressive than the safety (`Always`) and finite-horizon (`DWP`,
`Eventually`) fragments, which *are* chain-continuous.
-/
theorem infOften_iter_not_chain_continuous {ewp : StateEffectWP S E}
    [StateEffectWP.Conjunctive ewp] [StateEffectWP.ExcludedMiracle ewp]
    {AccEdge : (i : E.I) → E.O i → S → S → Prop}
    (body : I → ITree E I) (LInv : I → S → Prop)
    (h_term : ∀ a s₀, LInv a s₀ → DWP ewp (body a) LInv s₀)
    (h_live : ∀ a s₀, LInv a s₀ →
      buchiProgress ewp AccEdge (fun _ _ => False)
        (InfOften ewp AccEdge LInv) (body a) s₀)
    {init : I} {s : S} (h_init : LInv init s)
    (Q : PEmpty.{u + 1} → S → Prop) :
    InfOften ewp AccEdge Q (divergingLoop body init) s ∧
      (∀ n, ¬ InfOften ewp AccEdge Q
        (iterChain n (fun a => Sum.inl <$> body a) init) s) ∧
      ¬ DWP ewp (divergingLoop body init) Q s :=
  ⟨InfOften.iter_progress _ LInv
     (fun a s₀ ha => buchiProgress_map_inl (h_live a s₀ ha)) h_init,
   fun n => not_infOften_iterChain_divergingLoop body LInv h_term Q n h_init,
   not_dwp_diverging_loop body init⟩

end IterChain

section Heartbeat

/-- One heartbeat: emit a single observation. -/
def heartbeat : PUnit.{u + 1} → ITree (ObsE PUnit.{u + 1}) PUnit.{u + 1} :=
  fun _ => ITree.trigger (E := ObsE PUnit.{u + 1}) (ObsReq.emit PUnit.unit)

/--
**Explicit counterexample to chain continuity of `InfOften`.** The heartbeat
loop `loop { emit () }` satisfies `InfOften` (every emission is accepting) but

* `InfOften` fails on every finite unfolding, so it is not $\bigwedge_n$;
* *a fortiori* no finite unfolding witnesses it, so it is not $\bigvee_n$;
* `DWP` fails of the loop, so it is not a finite-horizon property.
-/
theorem infOften_heartbeat_not_chain_continuous
    (Q : PEmpty.{u + 1} → PUnit.{u + 1} → Prop) :
    InfOften (obsIgnoreWP PUnit.{u + 1} PUnit.{u + 1}) (fun _ _ _ _ => True) Q
        (divergingLoop heartbeat PUnit.unit) PUnit.unit ∧
      (∀ n, ¬ InfOften (obsIgnoreWP PUnit.{u + 1} PUnit.{u + 1})
        (fun _ _ _ _ => True) Q
        (iterChain n (fun a => Sum.inl <$> heartbeat a) PUnit.unit)
        PUnit.unit) ∧
      ¬ DWP (obsIgnoreWP PUnit.{u + 1} PUnit.{u + 1})
        (divergingLoop heartbeat PUnit.unit) Q PUnit.unit := by
  refine infOften_iter_not_chain_continuous heartbeat (fun _ _ => True)
    ?_ ?_ trivial Q
  · intro _ _ _
    exact DWP.vis (DWP.ret trivial)
  · intro _ _ _
    exact (buchiProgress.vis_iff _ _ _ _ _ _ _).2
      (Or.inl ⟨trivial, (InfOften.ret_iff _ _ _ _ _).2 trivial⟩)

/-- `InfOften` of the heartbeat loop is not the meet of its finite unfoldings. -/
theorem infOften_heartbeat_ne_forall
    (Q : PEmpty.{u + 1} → PUnit.{u + 1} → Prop) :
    ¬ (InfOften (obsIgnoreWP PUnit.{u + 1} PUnit.{u + 1})
          (fun _ _ _ _ => True) Q
          (divergingLoop heartbeat PUnit.unit) PUnit.unit ↔
        ∀ n, InfOften (obsIgnoreWP PUnit.{u + 1} PUnit.{u + 1})
          (fun _ _ _ _ => True) Q
          (iterChain n (fun a => Sum.inl <$> heartbeat a) PUnit.unit)
          PUnit.unit) :=
  fun h =>
    (infOften_heartbeat_not_chain_continuous Q).2.1 0
      (h.1 (infOften_heartbeat_not_chain_continuous Q).1 0)

/-- `InfOften` of the heartbeat loop is not the join of its finite unfoldings. -/
theorem infOften_heartbeat_ne_exists
    (Q : PEmpty.{u + 1} → PUnit.{u + 1} → Prop) :
    ¬ (InfOften (obsIgnoreWP PUnit.{u + 1} PUnit.{u + 1})
          (fun _ _ _ _ => True) Q
          (divergingLoop heartbeat PUnit.unit) PUnit.unit ↔
        ∃ n, InfOften (obsIgnoreWP PUnit.{u + 1} PUnit.{u + 1})
          (fun _ _ _ _ => True) Q
          (iterChain n (fun a => Sum.inl <$> heartbeat a) PUnit.unit)
          PUnit.unit) :=
  fun h =>
    (h.1 (infOften_heartbeat_not_chain_continuous Q).1).elim
      (infOften_heartbeat_not_chain_continuous Q).2.1

/--
A parity Büchi monitor over heartbeats: it flips its bit on every emission and
accepts exactly the edges that enter `true`.
-/
def parityHeartbeatSpec :
    BuchiSpec PUnit.{1} Bool (ObsE PUnit.{1}) PEmpty.{1} where
  ewp := obsIgnoreWP PUnit.{1} PUnit.{1}
  step q _ _ _ _ q' := q' = !q
  accept _ _ _ _ _ q' := q' = true
  inv _ _ := True
  terminal _ _ _ := False

/--
**Non-vacuity witness for `BuchiSat`.** The diverging heartbeat loop satisfies
the parity monitor from either initial monitor state: only every other
iteration is accepting, so the proof genuinely needs the *ranked* loop rule
(one non-accepting iteration is tolerated between accepting edges).
-/
theorem heartbeat_buchiSat_parity (q₀ : Bool) :
    BuchiSat parityHeartbeatSpec (divergingLoop heartbeat PUnit.unit) q₀
      PUnit.unit := by
  refine buchiSat_diverging_loop_ranked parityHeartbeatSpec heartbeat
    (fun n _ q _ => q = true → 1 ≤ n) ?_ (n := 1) trivial
    (fun _ => Nat.le_refl 1)
  intro n a q s h_inv
  refine (buchiProgress.vis_iff _ _ _ _ _ _ _).2 ⟨!q, rfl, trivial, ?_⟩
  cases q with
  | false =>
    exact Or.inl
      ⟨rfl, (InfOften.ret_iff _ _ _ _ _).2 ⟨1, fun _ => Nat.le_refl 1⟩⟩
  | true =>
    exact Or.inr
      ((buchiProgress.ret_iff _ _ _ _ _ _).2
        ⟨0, h_inv rfl, fun h => nomatch h⟩)

end Heartbeat

/-! ### 4.4 The Continuity Hypotheses Cannot Be Dropped -/

section ContinuityCounterexamples

/--
Countdown loop body: at `none` it obtains a number through request `i`, then
counts it down one iteration at a time and finally exits.
-/
def countdownBody (E : Effect.{0}) (i : E.I) (dec : E.O i → Nat) :
    Option Nat → ITree E (Option Nat ⊕ PUnit.{1})
  | none => ITree.vis i (fun o => ITree.ret (Sum.inl (some (dec o))))
  | some 0 => ITree.ret (Sum.inr PUnit.unit)
  | some (m + 1) => ITree.ret (Sum.inl (some m))

variable {S : Type} {E : Effect.{0}}

private theorem countdown_iter_none (i : E.I) (dec : E.O i → Nat) :
    ITree.iter (countdownBody E i dec) none =
      ITree.vis i (fun o =>
        ITree.tau (ITree.iter (countdownBody E i dec) (some (dec o)))) := by
  rw [iter_unfold]
  show (ITree.vis i (fun o => ITree.ret (Sum.inl (some (dec o)))) >>= _) = _
  rw [vis_bind]
  exact congrArg (ITree.vis i) (funext fun o => (ret_bind _ _).trans rfl)

private theorem countdown_iter_zero (i : E.I) (dec : E.O i → Nat) :
    ITree.iter (countdownBody E i dec) (some 0) = ITree.ret PUnit.unit := by
  rw [iter_unfold]
  exact (ret_bind (E := E) (Sum.inr PUnit.unit) _).trans rfl

private theorem countdown_iter_succ (i : E.I) (dec : E.O i → Nat) (m : Nat) :
    ITree.iter (countdownBody E i dec) (some (m + 1)) =
      ITree.tau (ITree.iter (countdownBody E i dec) (some m)) := by
  rw [iter_unfold]
  exact (ret_bind (E := E) (Sum.inl (some m)) _).trans rfl

private theorem countdown_chain_none (i : E.I) (dec : E.O i → Nat) (n : Nat) :
    iterChain (n + 1) (countdownBody E i dec) none =
      ITree.vis i (fun o =>
        ITree.tau (iterChain n (countdownBody E i dec) (some (dec o)))) := by
  rw [iterChain_succ]
  show (ITree.vis i (fun o => ITree.ret (Sum.inl (some (dec o)))) >>= _) = _
  rw [vis_bind]
  exact congrArg (ITree.vis i) (funext fun o => (ret_bind _ _).trans rfl)

private theorem countdown_chain_succ (i : E.I) (dec : E.O i → Nat)
    (n m : Nat) :
    iterChain (n + 1) (countdownBody E i dec) (some (m + 1)) =
      ITree.tau (iterChain n (countdownBody E i dec) (some m)) := by
  rw [iterChain_succ]
  exact (ret_bind (E := E) (Sum.inl (some m)) _).trans rfl

private theorem countdown_dwp (ewp : StateEffectWP S E) (i : E.I)
    (dec : E.O i → Nat) (s : S) :
    ∀ m, DWP ewp (ITree.iter (countdownBody E i dec) (some m))
      (fun _ _ => True) s
  | 0 => by rw [countdown_iter_zero]; exact DWP.ret trivial
  | m + 1 => by
    rw [countdown_iter_succ]; exact DWP.tau (countdown_dwp ewp i dec s m)

private theorem countdown_not_dwp_chain (ewp : StateEffectWP S E) (i : E.I)
    (dec : E.O i → Nat) (Q : PUnit.{1} → S → Prop) (s : S) :
    ∀ n, ¬ DWP ewp (iterChain n (countdownBody E i dec) (some n)) Q s
  | 0 => DWP.spin_false
  | n + 1 => by
    rw [countdown_chain_succ, DWP.tau_iff]
    exact countdown_not_dwp_chain ewp i dec Q s n

private theorem countdown_always_chain (ewp : StateEffectWP S E) (i : E.I)
    (dec : E.O i → Nat) (s : S) :
    ∀ n m, n ≤ m →
      Always ewp (fun _ => True) (fun _ _ => False)
        (iterChain n (countdownBody E i dec) (some m)) s
  | 0, _, _ => Always.spin ewp _ trivial
  | n + 1, 0, h => absurd h (Nat.not_succ_le_zero n)
  | n + 1, m + 1, h => by
    rw [countdown_chain_succ]
    exact Always.tau
      (countdown_always_chain ewp i dec s n m (Nat.le_of_succ_le_succ h))

private theorem countdown_not_always (ewp : StateEffectWP S E) (i : E.I)
    (dec : E.O i → Nat) (s : S) :
    ∀ m, ¬ Always ewp (fun _ => True) (fun _ _ => False)
      (ITree.iter (countdownBody E i dec) (some m)) s
  | 0 => by
    rw [countdown_iter_zero, Always.ret_iff]; exact fun h => h.2
  | m + 1 => by
    rw [countdown_iter_succ, Always.tau_iff]
    exact countdown_not_always ewp i dec s m

/--
**Scott continuity is necessary for $\bigvee_n$.** Under *unbounded demonic*
choice (`pickWP` over `Nat`) the countdown loop terminates (`DWP`), yet no
finite unfolding does: the environment can always pick a countdown longer than
the unfolding depth. So `DWP (iter) ↔ ∃ n, DWP (iterChain n)` is false without
`[UpContinuous ewp]`.
-/
theorem not_dwp_iter_continuity_unbounded :
    DWP (pickWP PUnit.{1} Nat)
        (ITree.iter (countdownBody (PickE Nat) PickReq.pick id) none)
        (fun _ _ => True) PUnit.unit ∧
      ∀ n, ¬ DWP (pickWP PUnit.{1} Nat)
        (iterChain n (countdownBody (PickE Nat) PickReq.pick id) none)
        (fun _ _ => True) PUnit.unit := by
  refine ⟨?_, fun n => ?_⟩
  · rw [countdown_iter_none (E := PickE Nat) PickReq.pick id]
    exact DWP.vis ⟨⟨0⟩, fun m => DWP.tau (countdown_dwp _ _ _ _ m)⟩
  · cases n with
    | zero => exact DWP.spin_false
    | succ n =>
      rw [countdown_chain_none (E := PickE Nat) PickReq.pick id]
      intro h
      have h' := (DWP.vis_iff _ _ _ _ _).1 h
      exact countdown_not_dwp_chain _ _ _ _ _ n
        ((DWP.tau_iff _ _ _ _).1 (h'.2 n))

/-- Unbounded demonic choice is not Scott continuous. -/
theorem not_upContinuous_pickNat : ¬ UpContinuous (pickWP PUnit.{1} Nat) :=
  fun _ =>
    ((dwp_iter_iff_exists_iterChain _ _ _ _).1
      not_dwp_iter_continuity_unbounded.1).elim
      not_dwp_iter_continuity_unbounded.2

/--
**Co-continuity is necessary for $\bigwedge_n$.** Under *unbounded angelic*
choice (`witnessWP` over `Nat`) every finite unfolding of the countdown loop is
`Always`-safe for the postcondition `False` (the prover picks a countdown
outlasting the unfolding), yet the loop itself is not: every choice eventually
returns. So `Always (iter) ↔ ∀ n, Always (iterChain n)` is false without
`[DownContinuous ewp]`.
-/
theorem not_always_iter_continuity_angelic :
    (∀ n, Always (witnessWP PUnit.{1} Nat) (fun _ => True) (fun _ _ => False)
        (iterChain n (countdownBody (WitnessE Nat) WitnessReq.witness id) none)
        PUnit.unit) ∧
      ¬ Always (witnessWP PUnit.{1} Nat) (fun _ => True) (fun _ _ => False)
        (ITree.iter (countdownBody (WitnessE Nat) WitnessReq.witness id) none)
        PUnit.unit := by
  refine ⟨fun n => ?_, ?_⟩
  · cases n with
    | zero => exact Always.spin _ _ trivial
    | succ n =>
      rw [countdown_chain_none (E := WitnessE Nat) WitnessReq.witness id]
      exact Always.vis trivial
        ⟨n, Always.tau (countdown_always_chain _ _ _ _ n n (Nat.le_refl n))⟩
  · rw [countdown_iter_none (E := WitnessE Nat) WitnessReq.witness id]
    intro h
    obtain ⟨_, m, hm⟩ := (Always.vis_iff _ _ _ _ _ _).1 h
    exact countdown_not_always _ _ _ _ m ((Always.tau_iff _ _ _ _ _).1 hm)

/-- Unbounded angelic choice is not co-continuous. -/
theorem not_downContinuous_witnessNat :
    ¬ DownContinuous (witnessWP PUnit.{1} Nat) :=
  fun _ =>
    not_always_iter_continuity_angelic.2
      ((always_iter_iff_forall_iterChain _ _ _ _ _).2
        not_always_iter_continuity_angelic.1)

end ContinuityCounterexamples

end Anneal.ITreeBuchi
