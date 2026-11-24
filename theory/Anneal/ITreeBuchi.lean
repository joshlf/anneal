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
- **`BuchiSpec`** / **`BuchiSat`** / **`FairBuchiSat`**: shallow Büchi and
  Streett monitors synchronised with the program through `BuchiSpec.monitorWP`,
  unifying `Always` safety, `InfOften`/`FairInfOften` liveness, and a terminal
  Hoare postcondition, with horizontal (`interp`) and target-stateful
  (`interpState`) handler linking.
- **`FairInfOften`** (Streett `□◇ Fair → □◇ AccEdge`): liveness *under a
  fairness assumption*, the four-level parity fixpoint
  `ν X₄. μ X₃. ν X₂. μ X₁` (`fairProgress` / `fairStall` / `fairStep`). It
  reduces exactly to `InfOften` when every edge is fair and to reactive
  productivity when none is, rejects `ITree.spin` unconditionally, and admits
  the fair retry-loop rule `FairInfOften.iter_fair` and well-founded/ranked loop
  rules (`iter_wf` / `iter_ranked`). `CoBuchi` (`◇□`) is its accepting-edge-free
  instance (closed under conjunction `CoBuchi.conj_bad`);
  `buchiSat_nondet_incomplete` shows that nondeterministic `BuchiSat` cannot
  replace it, paired with operational soundness `trace_buchiSat_strategy_adequacy`.
- **`StrategyAdequacy`**: general `EnvStrategy` operational soundness over
  arbitrary `[FaultEffect E]` and `[TraceSoundWP]` / `[PureSoundWP]` for
  `InfOften`, `FairInfOften`, `CoBuchi`, deterministic `FairBuchiSat`, arbitrary
  nondeterministic `BuchiSat`, and strong-fairness termination
  (`trace_strongFair_terminates`).
- **`tryUpdate`** (§5): an end-to-end `Atomic::try_update` template combining
  history monotonicity (`AlwaysStep`), non-vacuous CAS enabling (`InfOften`),
  fairness-conditional liveness (`FairInfOften.iter_fair`), three-way separation
  against load-spinning and CAS-ignoring loops, a one-shot `Committer` monitor
  (`FairBuchiSat`), target-stateful `interpState_stateful` lowering, and the
  failure of `DWP`.
- **Capstone** (§6): `temporal_hierarchy` / `temporal_hierarchy_strict` package
  the strict chain `DWP ⊊ InfOften ⊊ FairInfOften ⊊ DWLP`.
- **`iterChain`**: the finite-unfolding $\omega$-chain of `ITree.iter`, its
  convergence in the projective `CofixA` order (`ofITree_iterChain`), and the
  safety ($\bigwedge_n$) versus eventuality ($\bigvee_n$) continuity laws.

The continuity laws are stated under the one-step continuity classes
`DownContinuous` / `UpContinuous`. Neither can be dropped:
`not_always_iter_continuity_angelic` and `not_dwp_iter_continuity_unbounded`
exhibit unboundedly angelic and unboundedly demonic transformers for which the
corresponding law is false.
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

private theorem eutt_inv_ret {E : Effect.{u}} {R : Type u}
    {t u : ITree E R} {r : R} (he : Eutt t u) (h_obs : t.observe = .ret r) :
    ∃ u', TauStar u u' ∧ u'.observe = .ret r := by
  rw [Eutt.eq_def] at he
  rcases he with ⟨t', u', r', ht, hu, htr, hur⟩ |
    ⟨t', _, _, _, _, ht, _, htv, _, _⟩ | ⟨_, _, ht, _, _⟩
  · cases ht with
    | refl =>
      rw [h_obs] at htr; injection htr with hr; subst hr
      exact ⟨u', hu, hur⟩
    | step htau _ => rw [h_obs] at htau; nomatch htau
  · cases ht with
    | refl => rw [h_obs] at htv; nomatch htv
    | step htau _ => rw [h_obs] at htau; nomatch htau
  · rw [h_obs] at ht; nomatch ht

private theorem eutt_inv_vis {E : Effect.{u}} {R : Type u}
    {t u : ITree E R} {i : E.I} {k₁ : E.O i → ITree E R}
    (he : Eutt t u) (h_obs : t.observe = .vis i k₁) :
    ∃ u' k₂, TauStar u u' ∧ u'.observe = .vis i k₂ ∧
      ∀ o, Eutt (k₁ o) (k₂ o) := by
  rw [Eutt.eq_def] at he
  rcases he with ⟨t', _, _, ht, _, htr, _⟩ |
    ⟨t', u', i', k₁', k₂, ht, hu, htv, huv, hk⟩ | ⟨_, _, ht, _, _⟩
  · cases ht with
    | refl => rw [h_obs] at htr; nomatch htr
    | step htau _ => rw [h_obs] at htau; nomatch htau
  · cases ht with
    | refl =>
      rw [h_obs] at htv
      injection htv with hi hk_eq
      subst hi
      cases hk_eq
      exact ⟨u', k₂, hu, huv, hk⟩
    | step htau _ => rw [h_obs] at htau; nomatch htau
  · rw [h_obs] at ht; nomatch ht

private theorem eutt_inv_tau {E : Effect.{u}} {R : Type u}
    {t t' u : ITree E R} (he : Eutt t u) (h_obs : t.observe = .tau t') :
    Eutt t' u ∨ ∃ u', u.observe = .tau u' ∧ Eutt t' u' := by
  rw [Eutt.eq_def] at he
  rcases he with ⟨t₁, u₁, r, ht, hu, htr, hur⟩ |
    ⟨t₁, u₁, i, k₁, k₂, ht, hu, htv, huv, hk⟩ | ⟨t₁, u₁, ht, hu, h'⟩
  · cases ht with
    | refl => rw [h_obs] at htr; nomatch htr
    | step htau hrest =>
      rw [h_obs] at htau; injection htau with h_eq; subst h_eq
      exact Or.inl (by rw [Eutt.eq_def]; exact Or.inl ⟨t₁, u₁, r, hrest, hu, htr, hur⟩)
  · cases ht with
    | refl => rw [h_obs] at htv; nomatch htv
    | step htau hrest =>
      rw [h_obs] at htau; injection htau with h_eq; subst h_eq
      exact Or.inl (by
        rw [Eutt.eq_def]
        exact Or.inr (Or.inl ⟨t₁, u₁, i, k₁, k₂, hrest, hu, htv, huv, hk⟩))
  · rw [h_obs] at ht; injection ht with h_eq; subst h_eq
    exact Or.inr ⟨u₁, hu, h'⟩

/-- `DWLP` is invariant backwards across finite `.tau` prefixes. -/
theorem DWLP.of_tauStar {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {Q : R → S → Prop} {t u : ITree E R} {s : S}
    (h_tau : TauStar t u) (h : DWLP ewp u Q s) : DWLP ewp t Q s := by
  induction h_tau with
  | refl => exact h
  | step ht _ ih => rw [eq_tau_of_observe ht, DWLP.tau_iff]; exact ih h

/-- `DWLP` is invariant forward across finite `.tau` prefixes. -/
theorem DWLP.tauStar {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {Q : R → S → Prop} {t u : ITree E R} {s : S}
    (h_tau : TauStar t u) (h : DWLP ewp t Q s) : DWLP ewp u Q s := by
  induction h_tau with
  | refl => exact h
  | step ht _ ih => rw [eq_tau_of_observe ht, DWLP.tau_iff] at h; exact ih h

/-- `DWLP` respects equivalence up to finite `.tau`s (`Eutt`). -/
theorem DWLP.eutt {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {Q : R → S → Prop} {t u : ITree E R} {s : S}
    (he : Eutt t u) (h : DWLP ewp t Q s) : DWLP ewp u Q s := by
  refine DWLP.coinduct (fun u₀ s₀ => ∃ t₀, Eutt t₀ u₀ ∧ DWLP ewp t₀ Q s₀) ?_
    ⟨t, he, h⟩
  rintro u₀ s₀ ⟨t₀, h_eutt, ht₀⟩
  rw [Eutt.eq_def] at h_eutt
  rcases h_eutt with ⟨t', u', r, ht, hu, htr, hur⟩ |
    ⟨t', u', i, k₁, k₂, ht, hu, htv, huv, hk⟩ | ⟨t', u', ht, hu, h'⟩
  · have ht' := DWLP.tauStar ht ht₀
    rw [eq_ret_of_observe htr, DWLP.ret_iff] at ht'
    cases hu with
    | refl => rw [hur]; exact ht'
    | step hu_tau hrest =>
      rw [hu_tau]
      exact ⟨t', by rw [Eutt.eq_def]; exact Or.inl ⟨t', u', r, .refl t', hrest, htr, hur⟩,
        by rw [eq_ret_of_observe htr, DWLP.ret_iff]; exact ht'⟩
  · have ht' := DWLP.tauStar ht ht₀
    rw [eq_vis_of_observe htv, DWLP.vis_iff] at ht'
    cases hu with
    | refl =>
      rw [huv]
      exact ewp.mono (fun o _ hko => ⟨k₁ o, hk o, hko⟩) ht'
    | step hu_tau hrest =>
      rw [hu_tau]
      exact ⟨t',
        by
          rw [Eutt.eq_def]
          exact Or.inr (Or.inl ⟨t', u', i, k₁, k₂, .refl t', hrest, htv, huv, hk⟩),
        by rw [eq_vis_of_observe htv, DWLP.vis_iff]; exact ht'⟩
  · rw [eq_tau_of_observe ht, DWLP.tau_iff] at ht₀
    rw [hu]
    exact ⟨t', h', ht₀⟩

/-- `Eutt`-equivalent trees satisfy the exact same `DWLP` specifications. -/
theorem DWLP.eutt_iff {S : Type u} {E : Effect.{u}} {R : Type u}
    (ewp : StateEffectWP S E) (Q : R → S → Prop) {t u : ITree E R}
    (he : Eutt t u) (s : S) :
    DWLP ewp t Q s ↔ DWLP ewp u Q s :=
  ⟨DWLP.eutt he, DWLP.eutt he.symm⟩

/-- `DWP` is invariant backwards across finite `.tau` prefixes. -/
theorem DWP.of_tauStar {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {Q : R → S → Prop} {t u : ITree E R} {s : S}
    (h_tau : TauStar t u) (h : DWP ewp u Q s) : DWP ewp t Q s := by
  induction h_tau with
  | refl => exact h
  | step ht _ ih => rw [eq_tau_of_observe ht, DWP.tau_iff]; exact ih h

/-- `DWP` respects equivalence up to finite `.tau`s (`Eutt`). -/
theorem DWP.eutt {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {Q : R → S → Prop} {t u : ITree E R} {s : S}
    (he : Eutt t u) (h : DWP ewp t Q s) : DWP ewp u Q s := by
  refine DWP.induct (fun x s₀ => ∀ u₀, Eutt x u₀ → DWP ewp u₀ Q s₀) ?_ h u he
  intro x s₀ hx u₀ h_eutt
  cases h_obs : x.observe with
  | ret r =>
    simp only [h_obs] at hx
    obtain ⟨u', hu, hur⟩ := eutt_inv_ret h_eutt h_obs
    exact DWP.of_tauStar hu (by rw [eq_ret_of_observe hur, DWP.ret_iff]; exact hx)
  | tau x' =>
    simp only [h_obs] at hx
    rcases eutt_inv_tau h_eutt h_obs with h' | ⟨u', hu, h'⟩
    · exact hx u₀ h'
    · rw [eq_tau_of_observe hu, DWP.tau_iff]; exact hx u' h'
  | vis i k =>
    simp only [h_obs] at hx
    obtain ⟨u', k₂, hu, huv, hk⟩ := eutt_inv_vis h_eutt h_obs
    refine DWP.of_tauStar hu ?_
    rw [eq_vis_of_observe huv, DWP.vis_iff]
    exact ewp.mono (fun o _ ih => ih (k₂ o) (hk o)) hx

/-- `Eutt`-equivalent trees satisfy the exact same `DWP` specifications. -/
theorem DWP.eutt_iff {S : Type u} {E : Effect.{u}} {R : Type u}
    (ewp : StateEffectWP S E) (Q : R → S → Prop) {t u : ITree E R}
    (he : Eutt t u) (s : S) :
    DWP ewp t Q s ↔ DWP ewp u Q s :=
  ⟨DWP.eutt he, DWP.eutt he.symm⟩

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

/-- `Always` is invariant backwards across finite `.tau` prefixes. -/
theorem Always.of_tauStar {ewp : StateEffectWP S E} {Inv : S → Prop}
    {Q : R → S → Prop} {t u : ITree E R} {s : S}
    (h_tau : TauStar t u) (h : Always ewp Inv Q u s) :
    Always ewp Inv Q t s := by
  induction h_tau with
  | refl => exact h
  | step ht _ ih => rw [eq_tau_of_observe ht, Always.tau_iff]; exact ih h

/-- Conditional branching rule for `Always`. -/
theorem Always.ite {ewp : StateEffectWP S E} {Inv : S → Prop}
    {Q : R → S → Prop} {c : Prop} [Decidable c] {t₁ t₂ : ITree E R} {s : S}
    (h₁ : c → Always ewp Inv Q t₁ s) (h₂ : ¬ c → Always ewp Inv Q t₂ s) :
    Always ewp Inv Q (if c then t₁ else t₂) s := by
  split
  · exact h₁ ‹_›
  · exact h₂ ‹_›

/-- `Sum`-branching rule for `Always`. -/
theorem Always.sum_elim {A B : Type u} {ewp : StateEffectWP S E}
    {Inv : S → Prop} {Q : R → S → Prop}
    {f : A → ITree E R} {g : B → ITree E R} {s : S} (x : A ⊕ B)
    (h₁ : ∀ a, x = .inl a → Always ewp Inv Q (f a) s)
    (h₂ : ∀ b, x = .inr b → Always ewp Inv Q (g b) s) :
    Always ewp Inv Q (Sum.elim f g x) s := by
  cases x with
  | inl a => exact h₁ a rfl
  | inr b => exact h₂ b rfl

/-- `Always` respects equivalence up to finite `.tau`s (`Eutt`). -/
theorem Always.eutt {ewp : StateEffectWP S E} {Inv : S → Prop}
    {Q : R → S → Prop} {t u : ITree E R} {s : S}
    (he : Eutt t u) (h : Always ewp Inv Q t s) : Always ewp Inv Q u s := by
  refine Always.coinduct (fun u₀ s₀ => ∃ t₀, Eutt t₀ u₀ ∧ Always ewp Inv Q t₀ s₀) ?_
    ⟨t, he, h⟩
  rintro u₀ s₀ ⟨t₀, h_eutt, ht₀⟩
  refine ⟨ht₀.inv, ?_⟩
  rw [Eutt.eq_def] at h_eutt
  rcases h_eutt with ⟨t', u', r, ht, hu, htr, hur⟩ |
    ⟨t', u', i, k₁, k₂, ht, hu, htv, huv, hk⟩ | ⟨t', u', ht, hu, h'⟩
  · have ht' := Always.tauStar ht ht₀
    rw [eq_ret_of_observe htr, Always.ret_iff] at ht'
    cases hu with
    | refl => rw [hur]; exact ht'.2
    | step hu_tau hrest =>
      rw [hu_tau]
      exact ⟨t', by rw [Eutt.eq_def]; exact Or.inl ⟨t', u', r, .refl t', hrest, htr, hur⟩,
        by rw [eq_ret_of_observe htr, Always.ret_iff]; exact ht'⟩
  · have ht' := Always.tauStar ht ht₀
    rw [eq_vis_of_observe htv, Always.vis_iff] at ht'
    cases hu with
    | refl =>
      rw [huv]
      exact ewp.mono (fun o _ hko => ⟨k₁ o, hk o, hko⟩) ht'.2
    | step hu_tau hrest =>
      rw [hu_tau]
      exact ⟨t',
        by
          rw [Eutt.eq_def]
          exact Or.inr (Or.inl ⟨t', u', i, k₁, k₂, .refl t', hrest, htv, huv, hk⟩),
        by rw [eq_vis_of_observe htv, Always.vis_iff]; exact ht'⟩
  · rw [eq_tau_of_observe ht, Always.tau_iff] at ht₀
    rw [hu]
    exact ⟨t', h', ht₀⟩

/-- `Eutt`-equivalent trees satisfy the exact same `Always` invariants. -/
theorem Always.eutt_iff (ewp : StateEffectWP S E) (Inv : S → Prop)
    (Q : R → S → Prop) {t u : ITree E R} (he : Eutt t u) (s : S) :
    Always ewp Inv Q t s ↔ Always ewp Inv Q u s :=
  ⟨Always.eutt he, Always.eutt he.symm⟩

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

/-- Horizontal handler linking for `Always` across `ITree.interp`. -/
theorem Always.interp {E₁ E₂ : Effect.{u}}
    {ewp₁ : StateEffectWP S E₁} {ewp₂ : StateEffectWP S E₂}
    {Inv : S → Prop} (h : (i : E₁.I) → ITree E₂ (E₁.O i))
    (h_link : ∀ i (Q : E₁.O i → S → Prop) s₀,
      ewp₁.wp i (fun o s' => Inv s' ∧ Q o s') s₀ →
      DWLP (guardInvWP ewp₂ Inv) (h i) (fun o s' => Inv s' ∧ Q o s') s₀)
    {t : ITree E₁ R} {post : R → S → Prop} {s : S}
    (h_always : Always ewp₁ Inv post t s) :
    Always ewp₂ Inv post (ITree.interp h t) s := by
  have ⟨hi, hd⟩ := (always_iff_dwlp_invariant ewp₁ Inv post t s).1 h_always
  refine (always_iff_dwlp_invariant ewp₂ Inv post (ITree.interp h t) s).2 ⟨hi, ?_⟩
  refine dwlp_interp (ewp₁ := guardInvWP ewp₁ Inv) (ewp₂ := guardInvWP ewp₂ Inv) h ?_ hd
  intro i Q s₀ hw
  exact DWLP.mono (fun _ _ hk => hk.2) (h_link i Q s₀ hw)

/-- Stateful handler linking for `Always` across `ITree.interpState`. -/
theorem Always.interpState {H : Type u} {E₁ E₂ : Effect.{u}}
    {ewp₁ : StateEffectWP H E₁} {ewp₂ : EffectWP E₂}
    {Inv : H → Prop} (h : (i : E₁.I) → H → ITree E₂ (E₁.O i × H))
    (h_link : ∀ i (Q : E₁.O i → H → Prop) st,
      ewp₁.wp i (fun o st' => Inv st' ∧ Q o st') st →
      DWLP ewp₂ (h i st) (fun pair _ => Q pair.1 pair.2) PUnit.unit)
    {t : ITree E₁ R} {post : R → H → Prop} {st : H}
    (h_always : Always ewp₁ Inv post t st) :
    DWLP ewp₂ (ITree.interpState h t st)
      (fun pair _ => Inv pair.2 ∧ post pair.1 pair.2) PUnit.unit := by
  have ⟨_, hd⟩ := (always_iff_dwlp_invariant ewp₁ Inv post t st).1 h_always
  exact dwlp_interpState (ewp₁ := guardInvWP ewp₁ Inv) (ewp₂ := ewp₂) h h_link hd

/--
**Target-stateful handler linking** for `Always` across `ITree.interpState`:
threads handler state `H` while preserving an independent logical invariant
`Inv₂` over target state `S₂`.
-/
theorem Always.interpState_stateful {S₂ H : Type u} {E₁ E₂ : Effect.{u}}
    {ewp₁ : StateEffectWP (S₂ × H) E₁} {ewp₂ : StateEffectWP S₂ E₂}
    {Inv₁ : S₂ × H → Prop} {Inv₂ : S₂ → Prop}
    (h_inv : ∀ s₂ st, Inv₁ (s₂, st) → Inv₂ s₂)
    (h : (i : E₁.I) → H → ITree E₂ (E₁.O i × H))
    (h_link : ∀ i (Q : E₁.O i → S₂ × H → Prop) s₂ st,
      ewp₁.wp i (fun o p' => Inv₁ p' ∧ Q o p') (s₂, st) →
      DWLP (guardInvWP ewp₂ Inv₂) (h i st)
        (fun pair s₂' => Q pair.1 (s₂', pair.2)) s₂)
    {t : ITree E₁ R} {post : R → S₂ × H → Prop} {s₂ : S₂} {st : H}
    (h_always : Always ewp₁ Inv₁ post t (s₂, st)) :
    Always ewp₂ Inv₂ (fun pair s₂' => Inv₁ (s₂', pair.2) ∧ post pair.1 (s₂', pair.2))
      (ITree.interpState h t st) s₂ := by
  have ⟨hi₁, hd₁⟩ := (always_iff_dwlp_invariant ewp₁ Inv₁ post t (s₂, st)).1 h_always
  refine (always_iff_dwlp_invariant ewp₂ Inv₂ _ (ITree.interpState h t st) s₂).2
    ⟨h_inv s₂ st hi₁, ?_⟩
  let Q₁ : R → S₂ × H → Prop := fun r p => Inv₁ p ∧ post r p
  let Rrel : ITree E₂ (R × H) → S₂ → Prop := fun u s₀ =>
    (∃ t₀ st₀, u = ITree.interpState h t₀ st₀ ∧
      DWLP (guardInvWP ewp₁ Inv₁) t₀ Q₁ (s₀, st₀)) ∨
    (∃ (i : E₁.I) (m : ITree E₂ (E₁.O i × H)) (k : E₁.O i → ITree E₁ R),
      u = (m >>= fun (o, st') => .tau (ITree.interpState h (k o) st')) ∧
      DWLP (guardInvWP ewp₂ Inv₂) m
        (fun pair s' => DWLP (guardInvWP ewp₁ Inv₁) (k pair.1) Q₁ (s', pair.2)) s₀)
  refine DWLP.mono (fun pair s₂' hq => ⟨h_inv s₂' pair.2 hq.1, hq⟩)
    (DWLP.coinduct Rrel ?_ (Or.inl ⟨t, st, rfl, hd₁⟩))
  rintro u s₀ (⟨t₀, st₀, rfl, hd⟩ | ⟨i, m, k, rfl, hm⟩)
  · rw [DWLP.unfold_eq] at hd
    cases h_obs : t₀.observe with
    | ret r =>
      simp only [h_obs] at hd
      rw [eq_ret_of_observe h_obs, interpState_ret, ITree.observe_ret]; exact hd
    | tau t₀' =>
      simp only [h_obs] at hd
      rw [eq_tau_of_observe h_obs, interpState_tau, ITree.observe_tau]
      exact Or.inl ⟨t₀', st₀, rfl, hd⟩
    | vis i k =>
      simp only [h_obs] at hd
      rw [eq_vis_of_observe h_obs, interpState_vis]
      have hm := h_link i (fun o p' => DWLP (guardInvWP ewp₁ Inv₁) (k o) Q₁ p') s₀ st₀ hd
      rw [DWLP.unfold_eq] at hm
      cases hm_obs : (h i st₀).observe with
      | ret pair =>
        simp only [hm_obs] at hm
        rcases pair with ⟨o, st'⟩
        rw [eq_ret_of_observe hm_obs, ret_bind, ITree.observe_tau]
        exact Or.inl ⟨k o, st', rfl, hm⟩
      | tau m' =>
        simp only [hm_obs] at hm
        rw [eq_tau_of_observe hm_obs, tau_bind, ITree.observe_tau]
        exact Or.inr ⟨i, m', k, rfl, hm⟩
      | vis j c =>
        simp only [hm_obs] at hm
        rw [eq_vis_of_observe hm_obs, vis_bind, ITree.observe_vis]
        exact ewp₂.mono (fun o₂ _ ⟨hi₂, hc⟩ => ⟨hi₂, Or.inr ⟨i, c o₂, k, rfl, hc⟩⟩) hm
  · rw [DWLP.unfold_eq] at hm
    cases hm_obs : m.observe with
    | ret pair =>
      simp only [hm_obs] at hm
      rcases pair with ⟨o, st'⟩
      rw [eq_ret_of_observe hm_obs, ret_bind, ITree.observe_tau]
      exact Or.inl ⟨k o, st', rfl, hm⟩
    | tau m' =>
      simp only [hm_obs] at hm
      rw [eq_tau_of_observe hm_obs, tau_bind, ITree.observe_tau]
      exact Or.inr ⟨i, m', k, rfl, hm⟩
    | vis j c =>
      simp only [hm_obs] at hm
      rw [eq_vis_of_observe hm_obs, vis_bind, ITree.observe_vis]
      exact ewp₂.mono (fun o₂ _ ⟨hi₂, hc⟩ => ⟨hi₂, Or.inr ⟨i, c o₂, k, rfl, hc⟩⟩) hm

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

instance (ewp : StateEffectWP S E)
    (StepRel : (i : E.I) → E.O i → S → S → Prop)
    [h : StateEffectWP.Disjunctive ewp] :
    StateEffectWP.Disjunctive (guardStepWP ewp StepRel) where
  disj hw :=
    h.disj (ewp.mono
      (fun _ _ hk => hk.2.elim (fun hp => Or.inl ⟨hk.1, hp⟩)
        (fun hq => Or.inr ⟨hk.1, hq⟩)) hw)

instance {E : Effect.{u}} [FaultEffect E] (ewp : EffectWP E)
    (StepRel : (i : E.I) → E.O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop)
    [h : PureSoundWP ewp] :
    PureSoundWP (guardStepWP ewp StepRel) where
  sound hw := ⟨(h.sound hw).1, fun o => ((h.sound hw).2 o).2⟩

instance {E : Effect.{u}} [FaultEffect E]
    (ewp : StateEffectWP (List (Event E)) E)
    (StepRel : (i : E.I) → E.O i → List (Event E) → List (Event E) → Prop)
    [h : TraceSoundWP ewp] :
    TraceSoundWP (guardStepWP ewp StepRel) where
  sound hw := ⟨(h.sound hw).1, fun o => ((h.sound hw).2 o).2⟩

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

@[simp]
theorem AlwaysStep.ret_iff (ewp : StateEffectWP S E)
    (StepRel : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (r : R) (s : S) :
    AlwaysStep ewp StepRel Q (.ret r) s ↔ Q r s := by
  conv => lhs; rw [AlwaysStep.unfold_eq, ITree.observe_ret]

@[simp]
theorem AlwaysStep.tau_iff (ewp : StateEffectWP S E)
    (StepRel : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (t : ITree E R) (s : S) :
    AlwaysStep ewp StepRel Q (.tau t) s ↔ AlwaysStep ewp StepRel Q t s := by
  conv => lhs; rw [AlwaysStep.unfold_eq, ITree.observe_tau]

@[simp]
theorem AlwaysStep.vis_iff (ewp : StateEffectWP S E)
    (StepRel : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (i : E.I) (k : E.O i → ITree E R) (s : S) :
    AlwaysStep ewp StepRel Q (.vis i k) s ↔
      ewp.wp i (fun o s' => StepRel i o s s' ∧ AlwaysStep ewp StepRel Q (k o) s') s := by
  conv => lhs; rw [AlwaysStep.unfold_eq, ITree.observe_vis]

theorem AlwaysStep.ret {ewp : StateEffectWP S E}
    {StepRel : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {r : R} {s : S} (hq : Q r s) : AlwaysStep ewp StepRel Q (.ret r) s :=
  (AlwaysStep.ret_iff ewp StepRel Q r s).2 hq

theorem AlwaysStep.tau {ewp : StateEffectWP S E}
    {StepRel : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t : ITree E R} {s : S} (h : AlwaysStep ewp StepRel Q t s) :
    AlwaysStep ewp StepRel Q (.tau t) s :=
  (AlwaysStep.tau_iff ewp StepRel Q t s).2 h

theorem AlwaysStep.vis {ewp : StateEffectWP S E}
    {StepRel : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {i : E.I} {k : E.O i → ITree E R} {s : S}
    (hv : ewp.wp i (fun o s' => StepRel i o s s' ∧ AlwaysStep ewp StepRel Q (k o) s') s) :
    AlwaysStep ewp StepRel Q (.vis i k) s :=
  (AlwaysStep.vis_iff ewp StepRel Q i k s).2 hv

/-- Silent divergence vacuously satisfies every transition-relational safety spec. -/
theorem AlwaysStep.spin (ewp : StateEffectWP S E)
    (StepRel : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop) (s : S) :
    AlwaysStep ewp StepRel Q (ITree.spin (E := E) (R := R)) s :=
  (alwaysStep_iff_dwlp ewp StepRel Q ITree.spin s).2 (DWLP.spin _ Q s)

/-- Transition-relational safety implies plain partial correctness `DWLP`. -/
theorem AlwaysStep.toDWLP {ewp : StateEffectWP S E}
    {StepRel : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t : ITree E R} {s : S} (h : AlwaysStep ewp StepRel Q t s) :
    DWLP ewp t Q s := by
  refine DWLP.coinduct (fun x s₀ => AlwaysStep ewp StepRel Q x s₀) ?_ h
  intro x s₀ hx
  rw [AlwaysStep.unfold_eq] at hx
  cases h_obs : x.observe <;> simp only [h_obs] at hx
  · exact hx
  · exact hx
  · exact ewp.mono (fun _ _ hk => hk.2) hx

/-- Exact monadic bind characterisation for `AlwaysStep`. -/
theorem AlwaysStep.bind_iff {A B : Type u} (ewp : StateEffectWP S E)
    (StepRel : (i : E.I) → E.O i → S → S → Prop) (Q : B → S → Prop)
    (t : ITree E A) (k : A → ITree E B) (s : S) :
    AlwaysStep ewp StepRel Q (t >>= k) s ↔
      AlwaysStep ewp StepRel
        (fun a s' => AlwaysStep ewp StepRel Q (k a) s') t s := by
  rw [alwaysStep_iff_dwlp, DWLP.bind_iff, alwaysStep_iff_dwlp]
  constructor <;>
    exact DWLP.mono (fun a s' ha =>
      by first | exact (alwaysStep_iff_dwlp ewp StepRel Q (k a) s').2 ha
               | exact (alwaysStep_iff_dwlp ewp StepRel Q (k a) s').1 ha)

/-- Conjunction rule for `AlwaysStep` under `[StateEffectWP.Conjunctive ewp]`. -/
theorem AlwaysStep.conj {ewp : StateEffectWP S E}
    [h_conj : StateEffectWP.Conjunctive ewp]
    {Step₁ Step₂ : (i : E.I) → E.O i → S → S → Prop}
    {P Q : R → S → Prop} {t : ITree E R} {s : S}
    (hp : AlwaysStep ewp Step₁ P t s) (hq : AlwaysStep ewp Step₂ Q t s) :
    AlwaysStep ewp (fun i o s₀ s' => Step₁ i o s₀ s' ∧ Step₂ i o s₀ s')
      (fun r s' => P r s' ∧ Q r s') t s := by
  refine AlwaysStep.coinduct
    (fun x s₀ => AlwaysStep ewp Step₁ P x s₀ ∧ AlwaysStep ewp Step₂ Q x s₀) ?_ ⟨hp, hq⟩
  intro x s₀ ⟨hpx, hqx⟩
  rw [AlwaysStep.unfold_eq] at hpx hqx
  cases h_obs : x.observe <;> simp only [h_obs] at hpx hqx
  · exact ⟨hpx, hqx⟩
  · exact ⟨hpx, hqx⟩
  · exact ewp.mono (fun _ _ hpq => ⟨⟨hpq.1.1, hpq.2.1⟩, ⟨hpq.1.2, hpq.2.2⟩⟩)
      (h_conj.conj hpx hqx)

/-- Combine state invariance `Always` with transition safety `AlwaysStep` under conjunctivity. -/
theorem Always.and_alwaysStep {ewp : StateEffectWP S E}
    [h_conj : StateEffectWP.Conjunctive ewp]
    {Inv : S → Prop} {StepRel : (i : E.I) → E.O i → S → S → Prop}
    {P Q : R → S → Prop} {t : ITree E R} {s : S}
    (ha : Always ewp Inv P t s) (hs : AlwaysStep ewp StepRel Q t s) :
    Always (guardStepWP ewp StepRel) Inv (fun r s' => P r s' ∧ Q r s') t s := by
  refine Always.coinduct
    (fun x s₀ => Always ewp Inv P x s₀ ∧ AlwaysStep ewp StepRel Q x s₀) ?_ ⟨ha, hs⟩
  intro x s₀ ⟨hax, hsx⟩
  rw [Always.unfold_eq] at hax
  rw [AlwaysStep.unfold_eq] at hsx
  obtain ⟨hi, hax⟩ := hax
  refine ⟨hi, ?_⟩
  cases h_obs : x.observe <;> simp only [h_obs] at hax hsx
  · exact ⟨hax, hsx⟩
  · exact ⟨hax, hsx⟩
  · exact ewp.mono (fun _ _ hpq => ⟨hpq.2.1, hpq.1, hpq.2.2⟩)
      (h_conj.conj hax hsx)

/-- Conditional branching rule for `AlwaysStep`. -/
theorem AlwaysStep.ite {ewp : StateEffectWP S E}
    {StepRel : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {c : Prop} [Decidable c] {t₁ t₂ : ITree E R} {s : S}
    (h₁ : c → AlwaysStep ewp StepRel Q t₁ s)
    (h₂ : ¬ c → AlwaysStep ewp StepRel Q t₂ s) :
    AlwaysStep ewp StepRel Q (if c then t₁ else t₂) s := by
  split
  · exact h₁ ‹_›
  · exact h₂ ‹_›

/-- `Sum`-branching rule for `AlwaysStep`. -/
theorem AlwaysStep.sum_elim {A B : Type u} {ewp : StateEffectWP S E}
    {StepRel : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {f : A → ITree E R} {g : B → ITree E R} {s : S} (x : A ⊕ B)
    (h₁ : ∀ a, x = .inl a → AlwaysStep ewp StepRel Q (f a) s)
    (h₂ : ∀ b, x = .inr b → AlwaysStep ewp StepRel Q (g b) s) :
    AlwaysStep ewp StepRel Q (Sum.elim f g x) s := by
  cases x with
  | inl a => exact h₁ a rfl
  | inr b => exact h₂ b rfl

/-- `AlwaysStep` respects equivalence up to finite `.tau`s (`Eutt`). -/
theorem AlwaysStep.eutt {ewp : StateEffectWP S E}
    {StepRel : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t u : ITree E R} {s : S} (he : Eutt t u)
    (h : AlwaysStep ewp StepRel Q t s) : AlwaysStep ewp StepRel Q u s :=
  (alwaysStep_iff_dwlp ewp StepRel Q u s).2
    (DWLP.eutt he ((alwaysStep_iff_dwlp ewp StepRel Q t s).1 h))

/-- `Eutt`-equivalent trees satisfy the exact same `AlwaysStep` specs. -/
theorem AlwaysStep.eutt_iff (ewp : StateEffectWP S E)
    (StepRel : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    {t u : ITree E R} (he : Eutt t u) (s : S) :
    AlwaysStep ewp StepRel Q t s ↔ AlwaysStep ewp StepRel Q u s :=
  ⟨AlwaysStep.eutt he, AlwaysStep.eutt he.symm⟩

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

/--
State-dependent well-founded loop rule for `Until`: unlike `Until.iter_acc`
(whose measure lives only on the loop index `I`), the measure `m : α` may
depend on the logical state `S` (e.g., contention or spurious-failure budgets
that decrease while the loop index stays unchanged).
-/
theorem Until.iter_wf {I : Type u} {α : Type _} {ewp : StateEffectWP S E}
    {Hold Target : S → Prop}
    (lt : α → α → Prop) (h_wf : WellFounded lt)
    (body : I → ITree E (I ⊕ R)) (LInv : α → I → S → Prop)
    {Q : R → S → Prop}
    (h_body : ∀ m a s₀, LInv m a s₀ →
      Until ewp Hold Target
        (Sum.elim (fun next s' => ∃ m', lt m' m ∧ LInv m' next s') Q)
        (body a) s₀)
    {m : α} {init : I} {s : S} (h_init : LInv m init s) :
    Until ewp Hold Target Q (ITree.iter body init) s := by
  refine h_wf.induction
    (C := fun m => ∀ a s₀, LInv m a s₀ →
      Until ewp Hold Target Q (ITree.iter body a) s₀) m ?_ init s h_init
  intro m ih a s₀ hm
  rw [iter_unfold]
  apply Until.bind
  refine Until.mono (fun _ h => h) (fun _ h => h) ?_
    (h_body m a s₀ hm).post_hold
  rintro (next | r) s' ⟨h_hold, hp⟩
  · obtain ⟨m', hlt, hm'⟩ := hp
    exact Until.tau (ih m' hlt next s' hm')
  · exact Until.ret h_hold hp

/-- `Nat`-ranked loop rule for `Until` allowing arbitrary strict rank drops `m < n`. -/
theorem Until.iter_ranked_lt {I : Type u} {ewp : StateEffectWP S E}
    {Hold Target : S → Prop}
    (body : I → ITree E (I ⊕ R)) (LInv : Nat → I → S → Prop)
    {Q : R → S → Prop}
    (h_body : ∀ n a s₀, LInv n a s₀ →
      Until ewp Hold Target
        (Sum.elim (fun next s' => ∃ m, m < n ∧ LInv m next s') Q)
        (body a) s₀)
    {n : Nat} {init : I} {s : S} (h_init : LInv n init s) :
    Until ewp Hold Target Q (ITree.iter body init) s :=
  Until.iter_wf (fun a b : Nat => a < b) Nat.lt_wfRel.wf body LInv h_body h_init

/-- `Until` is invariant backwards across finite `.tau` prefixes. -/
theorem Until.of_tauStar {ewp : StateEffectWP S E} {Hold Target : S → Prop}
    {Q : R → S → Prop} {t u : ITree E R} {s : S}
    (h_tau : TauStar t u) (h : Until ewp Hold Target Q u s) :
    Until ewp Hold Target Q t s := by
  induction h_tau with
  | refl => exact h
  | step ht _ ih => rw [eq_tau_of_observe ht, Until.tau_iff]; exact ih h

/-- `Until` respects equivalence up to finite `.tau`s (`Eutt`). -/
theorem Until.eutt {ewp : StateEffectWP S E} {Hold Target : S → Prop}
    {Q : R → S → Prop} {t u : ITree E R} {s : S}
    (he : Eutt t u) (h : Until ewp Hold Target Q t s) :
    Until ewp Hold Target Q u s := by
  refine Until.induct (fun x s₀ => ∀ u₀, Eutt x u₀ → Until ewp Hold Target Q u₀ s₀)
    ?_ h u he
  intro x s₀ hx u₀ h_eutt
  rcases hx with ht | ⟨hh, hx⟩
  · exact Until.here ht
  · cases h_obs : x.observe with
    | ret r =>
      simp only [h_obs] at hx
      obtain ⟨u', hu, hur⟩ := eutt_inv_ret h_eutt h_obs
      exact Until.of_tauStar hu (by rw [eq_ret_of_observe hur]; exact Until.ret hh hx)
    | tau x' =>
      simp only [h_obs] at hx
      rcases eutt_inv_tau h_eutt h_obs with h' | ⟨u', hu, h'⟩
      · exact hx u₀ h'
      · rw [eq_tau_of_observe hu, Until.tau_iff]; exact hx u' h'
    | vis i k =>
      simp only [h_obs] at hx
      obtain ⟨u', k₂, hu, huv, hk⟩ := eutt_inv_vis h_eutt h_obs
      refine Until.of_tauStar hu ?_
      rw [eq_vis_of_observe huv]
      exact Until.vis hh (ewp.mono (fun o _ ih => ih (k₂ o) (hk o)) hx)

/-- `Eutt`-equivalent trees satisfy the exact same `Until` specs. -/
theorem Until.eutt_iff (ewp : StateEffectWP S E) (Hold Target : S → Prop)
    (Q : R → S → Prop) {t u : ITree E R} (he : Eutt t u) (s : S) :
    Until ewp Hold Target Q t s ↔ Until ewp Hold Target Q u s :=
  ⟨Until.eutt he, Until.eutt he.symm⟩

/-- Horizontal handler linking for `Until` across `ITree.interp`. -/
theorem Until.interp {E₁ E₂ : Effect.{u}}
    {ewp₁ : StateEffectWP S E₁} {ewp₂ : StateEffectWP S E₂}
    {Hold Target : S → Prop} (h : (i : E₁.I) → ITree E₂ (E₁.O i))
    (h_link : ∀ i (Q : E₁.O i → S → Prop) s₀,
      Hold s₀ → ewp₁.wp i Q s₀ → Until ewp₂ Hold Target Q (h i) s₀)
    {t : ITree E₁ R} {post : R → S → Prop} {s : S}
    (h_until : Until ewp₁ Hold Target post t s) :
    Until ewp₂ Hold Target post (ITree.interp h t) s := by
  refine Until.induct (fun x s₀ => Until ewp₂ Hold Target post (ITree.interp h x) s₀)
    ?_ h_until
  intro x s₀ hx
  rcases hx with ht | ⟨hh, hx⟩
  · exact Until.here ht
  · cases h_obs : x.observe with
    | ret r =>
      simp only [h_obs] at hx
      rw [eq_ret_of_observe h_obs, interp_ret]; exact Until.ret hh hx
    | tau x' =>
      simp only [h_obs] at hx
      rw [eq_tau_of_observe h_obs, interp_tau]; exact Until.tau hx
    | vis i k =>
      simp only [h_obs] at hx
      rw [eq_vis_of_observe h_obs, interp_vis]
      exact Until.bind (h_link i _ s₀ hh (ewp₁.mono (fun _ _ hu => Until.tau hu) hx))

/-- Combining `Always` safety with `Until` under `[Conjunctive ewp]`. -/
theorem Until.and_always {ewp : StateEffectWP S E}
    [h_conj : StateEffectWP.Conjunctive ewp]
    {Inv Hold Target : S → Prop} {P Q : R → S → Prop} {t : ITree E R} {s : S}
    (h_safe : Always ewp Inv P t s) (h_until : Until ewp Hold Target Q t s) :
    Until ewp (fun s' => Inv s' ∧ Hold s') (fun s' => Inv s' ∧ Target s')
      (fun r s' => P r s' ∧ Q r s') t s := by
  refine Until.induct
    (fun x s₀ => Always ewp Inv P x s₀ →
      Until ewp (fun s' => Inv s' ∧ Hold s') (fun s' => Inv s' ∧ Target s')
        (fun r s' => P r s' ∧ Q r s') x s₀) ?_ h_until h_safe
  intro x s₀ hx ha
  rw [Always.unfold_eq] at ha
  obtain ⟨hi, ha⟩ := ha
  rcases hx with ht | ⟨hh, hx⟩
  · exact Until.here ⟨hi, ht⟩
  · rw [Until.unfold_eq]
    refine Or.inr ⟨⟨hi, hh⟩, ?_⟩
    cases h_obs : x.observe <;> simp only [h_obs] at hx ha ⊢
    · exact ⟨ha, hx⟩
    · exact hx ha
    · exact ewp.mono (fun _ _ hpq => hpq.1 hpq.2) (h_conj.conj hx ha)

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

/-- Monotonicity of `Eventually` in the effect transformer. -/
theorem Eventually.mono_wp {ewp ewp' : StateEffectWP S E} {Target : S → Prop}
    {Q : R → S → Prop} {t : ITree E R} {s : S}
    (h_wp : ∀ (i : E.I) (K : E.O i → S → Prop) (s₀ : S),
      ewp.wp i K s₀ → ewp'.wp i K s₀)
    (h : Eventually ewp Target Q t s) : Eventually ewp' Target Q t s :=
  (eventually_iff_until ewp' Target Q t s).2
    (Until.mono_wp h_wp ((eventually_iff_until ewp Target Q t s).1 h))

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

/-- State-dependent well-founded loop progress rule for `Eventually`. -/
theorem Eventually.iter_wf {I : Type u} {α : Type _} {ewp : StateEffectWP S E}
    {Target : S → Prop}
    (lt : α → α → Prop) (h_wf : WellFounded lt)
    (body : I → ITree E (I ⊕ R)) (LInv : α → I → S → Prop)
    {Q : R → S → Prop}
    (h_body : ∀ m a s₀, LInv m a s₀ →
      Eventually ewp Target
        (Sum.elim (fun next s' => ∃ m', lt m' m ∧ LInv m' next s') Q)
        (body a) s₀)
    {m : α} {init : I} {s : S} (h_init : LInv m init s) :
    Eventually ewp Target Q (ITree.iter body init) s :=
  (eventually_iff_until ewp Target Q _ s).2
    (Until.iter_wf lt h_wf body LInv
      (fun m a s₀ hm => (eventually_iff_until ewp Target _ _ s₀).1 (h_body m a s₀ hm))
      h_init)

/-- `Nat`-ranked loop progress rule for `Eventually` allowing arbitrary strict drops `m < n`. -/
theorem Eventually.iter_ranked_lt {I : Type u} {ewp : StateEffectWP S E}
    {Target : S → Prop}
    (body : I → ITree E (I ⊕ R)) (LInv : Nat → I → S → Prop)
    {Q : R → S → Prop}
    (h_body : ∀ n a s₀, LInv n a s₀ →
      Eventually ewp Target
        (Sum.elim (fun next s' => ∃ m, m < n ∧ LInv m next s') Q)
        (body a) s₀)
    {n : Nat} {init : I} {s : S} (h_init : LInv n init s) :
    Eventually ewp Target Q (ITree.iter body init) s :=
  Eventually.iter_wf (fun a b : Nat => a < b) Nat.lt_wfRel.wf body LInv h_body h_init

/--
Classic LTL implication
$\Box H \land \Diamond T \implies H \mathbin{\mathcal{U}} (H \land T)$.
-/
theorem until_of_always_eventually {ewp : StateEffectWP S E}
    [StateEffectWP.Conjunctive ewp] {Hold Target : S → Prop}
    {P Q : R → S → Prop} {t : ITree E R} {s : S}
    (h_safe : Always ewp Hold P t s) (h_ev : Eventually ewp Target Q t s) :
    Until ewp Hold (fun s' => Hold s' ∧ Target s')
      (fun r s' => P r s' ∧ Q r s') t s :=
  Until.mono (fun _ h => h.1) (fun _ h => h) (fun _ _ h => h)
    (Until.and_always h_safe ((eventually_iff_until ewp Target Q t s).1 h_ev))

/-- `Eventually` is invariant backwards across finite `.tau` prefixes. -/
theorem Eventually.of_tauStar {ewp : StateEffectWP S E} {Target : S → Prop}
    {Q : R → S → Prop} {t u : ITree E R} {s : S}
    (h_tau : TauStar t u) (h : Eventually ewp Target Q u s) :
    Eventually ewp Target Q t s :=
  (eventually_iff_until ewp Target Q t s).2
    (Until.of_tauStar h_tau ((eventually_iff_until ewp Target Q u s).1 h))

/-- `Eventually` respects equivalence up to finite `.tau`s (`Eutt`). -/
theorem Eventually.eutt {ewp : StateEffectWP S E} {Target : S → Prop}
    {Q : R → S → Prop} {t u : ITree E R} {s : S}
    (he : Eutt t u) (h : Eventually ewp Target Q t s) :
    Eventually ewp Target Q u s :=
  (eventually_iff_until ewp Target Q u s).2
    (Until.eutt he ((eventually_iff_until ewp Target Q t s).1 h))

/-- `Eutt`-equivalent trees satisfy the exact same `Eventually` specs. -/
theorem Eventually.eutt_iff (ewp : StateEffectWP S E) (Target : S → Prop)
    (Q : R → S → Prop) {t u : ITree E R} (he : Eutt t u) (s : S) :
    Eventually ewp Target Q t s ↔ Eventually ewp Target Q u s :=
  ⟨Eventually.eutt he, Eventually.eutt he.symm⟩

/-- Horizontal handler linking for `Eventually` across `ITree.interp`. -/
theorem Eventually.interp {E₁ E₂ : Effect.{u}}
    {ewp₁ : StateEffectWP S E₁} {ewp₂ : StateEffectWP S E₂}
    {Target : S → Prop} (h : (i : E₁.I) → ITree E₂ (E₁.O i))
    (h_link : ∀ i (Q : E₁.O i → S → Prop) s₀,
      ewp₁.wp i Q s₀ → Eventually ewp₂ Target Q (h i) s₀)
    {t : ITree E₁ R} {post : R → S → Prop} {s : S}
    (h_ev : Eventually ewp₁ Target post t s) :
    Eventually ewp₂ Target post (ITree.interp h t) s :=
  (eventually_iff_until ewp₂ Target post _ s).2
    (Until.interp h
      (fun i Q s₀ _ hw => (eventually_iff_until ewp₂ Target Q _ s₀).1 (h_link i Q s₀ hw))
      ((eventually_iff_until ewp₁ Target post t s).1 h_ev))

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

/-- Total correctness is `Eventually` with an unreachable target. -/
theorem dwp_iff_eventually (ewp : StateEffectWP S E) (Q : R → S → Prop)
    (t : ITree E R) (s : S) :
    DWP ewp t Q s ↔ Eventually ewp (fun _ => False) Q t s :=
  (dwp_iff_until ewp Q t s).trans (eventually_iff_until ewp (fun _ => False) Q t s).symm

/-- Total correctness is strict `EventuallyStep` with no accepting edges. -/
theorem dwp_iff_eventuallyStep (ewp : StateEffectWP S E) (Q : R → S → Prop)
    (t : ITree E R) (s : S) :
    DWP ewp t Q s ↔ EventuallyStep ewp (fun _ _ _ _ => False) Q t s := by
  refine ⟨eventuallyStep_of_dwp _, fun h => ?_⟩
  refine EventuallyStep.induct (fun x s₀ => DWP ewp x Q s₀) ?_ h
  intro x s₀ hx
  rw [DWP.unfold_eq]
  cases h_obs : x.observe <;> simp only [h_obs] at hx ⊢
  · exact hx
  · exact hx
  · exact ewp.mono (fun _ _ hp => hp.elim False.elim id) hx

/--
State-dependent well-founded total-correctness loop rule for `DWP`: the
well-founded measure `m : α` may depend on the logical state `S` (e.g., bounded
external contention / spurious CAS failure budgets).
-/
theorem dwp_iter_wf {I : Type u} {α : Type _} {ewp : StateEffectWP S E}
    (lt : α → α → Prop) (h_wf : WellFounded lt)
    (body : I → ITree E (I ⊕ R)) (LInv : α → I → S → Prop)
    {Q : R → S → Prop}
    (h_body : ∀ m a s₀, LInv m a s₀ →
      DWP ewp (body a)
        (Sum.elim (fun next s' => ∃ m', lt m' m ∧ LInv m' next s') Q) s₀)
    {m : α} {init : I} {s : S} (h_init : LInv m init s) :
    DWP ewp (ITree.iter body init) Q s :=
  (dwp_iff_until ewp Q _ s).2
    (Until.iter_wf lt h_wf body LInv
      (fun m a s₀ hm => (dwp_iff_until ewp _ _ s₀).1 (h_body m a s₀ hm))
      h_init)

/-- `Nat`-ranked total-correctness loop rule allowing arbitrary strict drops `m < n`. -/
theorem dwp_iter_ranked_lt {I : Type u} {ewp : StateEffectWP S E}
    (body : I → ITree E (I ⊕ R)) (LInv : Nat → I → S → Prop)
    {Q : R → S → Prop}
    (h_body : ∀ n a s₀, LInv n a s₀ →
      DWP ewp (body a)
        (Sum.elim (fun next s' => ∃ m, m < n ∧ LInv m next s') Q) s₀)
    {n : Nat} {init : I} {s : S} (h_init : LInv n init s) :
    DWP ewp (ITree.iter body init) Q s :=
  dwp_iter_wf (fun a b : Nat => a < b) Nat.lt_wfRel.wf body LInv h_body h_init

/-- Monotonicity of `EventuallyStep` in the effect transformer. -/
theorem EventuallyStep.mono_wp {ewp ewp' : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t : ITree E R} {s : S}
    (h_wp : ∀ (i : E.I) (K : E.O i → S → Prop) (s₀ : S),
      ewp.wp i K s₀ → ewp'.wp i K s₀)
    (h : EventuallyStep ewp AccEdge Q t s) :
    EventuallyStep ewp' AccEdge Q t s := by
  refine EventuallyStep.induct
    (fun x s₀ => EventuallyStep ewp' AccEdge Q x s₀) ?_ h
  intro x s₀ hx
  rw [EventuallyStep.unfold_eq]
  cases h_obs : x.observe <;> simp only [h_obs] at hx ⊢
  · exact hx
  · exact hx
  · exact h_wp _ _ _ hx

/-- Conditional branching rule for `EventuallyStep`. -/
theorem EventuallyStep.ite {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {c : Prop} [Decidable c] {t₁ t₂ : ITree E R} {s : S}
    (h₁ : c → EventuallyStep ewp AccEdge Q t₁ s)
    (h₂ : ¬ c → EventuallyStep ewp AccEdge Q t₂ s) :
    EventuallyStep ewp AccEdge Q (if c then t₁ else t₂) s := by
  split
  · exact h₁ ‹_›
  · exact h₂ ‹_›

/-- `Sum`-branching rule for `EventuallyStep`. -/
theorem EventuallyStep.sum_elim {A B : Type u} {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {f : A → ITree E R} {g : B → ITree E R} {s : S} (x : A ⊕ B)
    (h₁ : ∀ a, x = .inl a → EventuallyStep ewp AccEdge Q (f a) s)
    (h₂ : ∀ b, x = .inr b → EventuallyStep ewp AccEdge Q (g b) s) :
    EventuallyStep ewp AccEdge Q (Sum.elim f g x) s := by
  cases x with
  | inl a => exact h₁ a rfl
  | inr b => exact h₂ b rfl

/-- State-dependent well-founded loop progress rule for `EventuallyStep`. -/
theorem EventuallyStep.iter_wf {I : Type u} {α : Type _}
    {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop}
    (lt : α → α → Prop) (h_wf : WellFounded lt)
    (body : I → ITree E (I ⊕ R)) (LInv : α → I → S → Prop)
    {Q : R → S → Prop}
    (h_body : ∀ m a s₀, LInv m a s₀ →
      EventuallyStep ewp AccEdge
        (Sum.elim (fun next s' => ∃ m', lt m' m ∧ LInv m' next s') Q)
        (body a) s₀)
    {m : α} {init : I} {s : S} (h_init : LInv m init s) :
    EventuallyStep ewp AccEdge Q (ITree.iter body init) s := by
  refine h_wf.induction
    (C := fun m => ∀ a s₀, LInv m a s₀ →
      EventuallyStep ewp AccEdge Q (ITree.iter body a) s₀) m ?_ init s h_init
  intro m ih a s₀ hm
  rw [iter_unfold]
  apply EventuallyStep.bind
  refine EventuallyStep.mono (fun _ _ _ _ ha => ha) ?_ (h_body m a s₀ hm)
  rintro (next | r) s' hp
  · obtain ⟨m', hlt, hm'⟩ := hp
    exact (EventuallyStep.tau_iff _ _ _ _ _).2 (ih m' hlt next s' hm')
  · exact (EventuallyStep.ret_iff _ _ _ _ _).2 hp

/-- `Nat`-ranked loop progress rule for `EventuallyStep`. -/
theorem EventuallyStep.iter_ranked {I : Type u} {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop}
    (body : I → ITree E (I ⊕ R)) (LInv : Nat → I → S → Prop)
    {Q : R → S → Prop}
    (h_body : ∀ n a s₀, LInv n a s₀ →
      EventuallyStep ewp AccEdge
        (Sum.elim (fun next s' => ∃ m, m < n ∧ LInv m next s') Q)
        (body a) s₀)
    {n : Nat} {init : I} {s : S} (h_init : LInv n init s) :
    EventuallyStep ewp AccEdge Q (ITree.iter body init) s :=
  EventuallyStep.iter_wf (fun a b : Nat => a < b) Nat.lt_wfRel.wf body LInv
    h_body h_init

/-- `EventuallyStep` is invariant backwards across finite `.tau` prefixes. -/
theorem EventuallyStep.of_tauStar {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t u : ITree E R} {s : S}
    (h_tau : TauStar t u) (h : EventuallyStep ewp AccEdge Q u s) :
    EventuallyStep ewp AccEdge Q t s := by
  induction h_tau with
  | refl => exact h
  | step ht _ ih => rw [eq_tau_of_observe ht, EventuallyStep.tau_iff]; exact ih h

/-- `EventuallyStep` respects equivalence up to finite `.tau`s (`Eutt`). -/
theorem EventuallyStep.eutt {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t u : ITree E R} {s : S} (he : Eutt t u)
    (h : EventuallyStep ewp AccEdge Q t s) :
    EventuallyStep ewp AccEdge Q u s := by
  refine EventuallyStep.induct
    (fun x s₀ => ∀ u₀, Eutt x u₀ → EventuallyStep ewp AccEdge Q u₀ s₀) ?_ h u he
  intro x s₀ hx u₀ h_eutt
  cases h_obs : x.observe with
  | ret r =>
    simp only [h_obs] at hx
    obtain ⟨u', hu, hur⟩ := eutt_inv_ret h_eutt h_obs
    exact EventuallyStep.of_tauStar hu
      (by rw [eq_ret_of_observe hur, EventuallyStep.ret_iff]; exact hx)
  | tau x' =>
    simp only [h_obs] at hx
    rcases eutt_inv_tau h_eutt h_obs with h' | ⟨u', hu, h'⟩
    · exact hx u₀ h'
    · rw [eq_tau_of_observe hu, EventuallyStep.tau_iff]; exact hx u' h'
  | vis i k =>
    simp only [h_obs] at hx
    obtain ⟨u', k₂, hu, huv, hk⟩ := eutt_inv_vis h_eutt h_obs
    refine EventuallyStep.of_tauStar hu ?_
    rw [eq_vis_of_observe huv, EventuallyStep.vis_iff]
    exact ewp.mono (fun o _ hp => hp.imp id (fun ih => ih (k₂ o) (hk o))) hx

/-- `Eutt`-equivalent trees satisfy the exact same `EventuallyStep` specs. -/
theorem EventuallyStep.eutt_iff (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    {t u : ITree E R} (he : Eutt t u) (s : S) :
    EventuallyStep ewp AccEdge Q t s ↔ EventuallyStep ewp AccEdge Q u s :=
  ⟨EventuallyStep.eutt he, EventuallyStep.eutt he.symm⟩

/-- Horizontal handler linking for `EventuallyStep` across `ITree.interp`. -/
theorem EventuallyStep.interp {E₁ E₂ : Effect.{u}}
    {ewp₁ : StateEffectWP S E₁} {ewp₂ : StateEffectWP S E₂}
    {Acc₁ : (i : E₁.I) → E₁.O i → S → S → Prop}
    {Acc₂ : (j : E₂.I) → E₂.O j → S → S → Prop}
    (h : (i : E₁.I) → ITree E₂ (E₁.O i))
    (h_link : ∀ i (Q : E₁.O i → S → Prop) s₀,
      ewp₁.wp i (fun o s' => Acc₁ i o s₀ s' ∨ Q o s') s₀ →
      EventuallyStep ewp₂ Acc₂ Q (h i) s₀)
    {t : ITree E₁ R} {post : R → S → Prop} {s : S}
    (h_es : EventuallyStep ewp₁ Acc₁ post t s) :
    EventuallyStep ewp₂ Acc₂ post (ITree.interp h t) s := by
  refine EventuallyStep.induct
    (fun x s₀ => EventuallyStep ewp₂ Acc₂ post (ITree.interp h x) s₀) ?_ h_es
  intro x s₀ hx
  cases h_obs : x.observe with
  | ret r =>
    simp only [h_obs] at hx
    rw [eq_ret_of_observe h_obs, interp_ret, EventuallyStep.ret_iff]; exact hx
  | tau x' =>
    simp only [h_obs] at hx
    rw [eq_tau_of_observe h_obs, interp_tau, EventuallyStep.tau_iff]; exact hx
  | vis i k =>
    simp only [h_obs] at hx
    rw [eq_vis_of_observe h_obs, interp_vis]
    exact EventuallyStep.bind
      (h_link i _ s₀ (ewp₁.mono (fun _ _ hp => hp.imp id (EventuallyStep.tau_iff _ _ _ _ _).2) hx))

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

/-- `buchiProgress` is invariant backwards across finite `.tau` prefixes. -/
theorem buchiProgress.of_tauStar {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {Rec : ITree E R → S → Prop} {t u : ITree E R} {s : S}
    (h_tau : TauStar t u) (h : buchiProgress ewp AccEdge Q Rec u s) :
    buchiProgress ewp AccEdge Q Rec t s := by
  induction h_tau with
  | refl => exact h
  | step ht _ ih => rw [eq_tau_of_observe ht, buchiProgress.tau_iff]; exact ih h

/-- `DWP`-prefix sequencing rule for `buchiProgress`. -/
theorem buchiProgress.bind_dwp {A B : Type u} {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : B → S → Prop}
    {Rec : ITree E B → S → Prop} {t : ITree E A} {k : A → ITree E B} {s : S}
    (h : DWP ewp t (fun a s' => buchiProgress ewp AccEdge Q Rec (k a) s') s) :
    buchiProgress ewp AccEdge Q Rec (t >>= k) s :=
  buchiProgress.bind (buchiProgress.of_dwp AccEdge _ h)

/--
Well-founded loop progress rule for `buchiProgress` over `ITree.iter`:
allows nested retry loops (such as a bounded-contention CAS loop inside a
reactive service loop) to discharge a single `buchiProgress` obligation.
-/
theorem buchiProgress.iter_wf {I : Type u} {α : Type _}
    {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop}
    (lt : α → α → Prop) (h_wf : WellFounded lt)
    (body : I → ITree E (I ⊕ R)) (LInv : α → I → S → Prop)
    {Q : R → S → Prop} {Rec : ITree E R → S → Prop}
    (h_body : ∀ m a s₀, LInv m a s₀ →
      buchiProgress ewp AccEdge
        (Sum.elim (fun next s' => ∃ m', lt m' m ∧ LInv m' next s') Q)
        (fun t' s' => Rec (t' >>= Sum.elim (fun next => .tau (ITree.iter body next)) .ret) s')
        (body a) s₀)
    {m : α} {init : I} {s : S} (h_init : LInv m init s) :
    buchiProgress ewp AccEdge Q Rec (ITree.iter body init) s := by
  refine h_wf.induction
    (C := fun m => ∀ a s₀, LInv m a s₀ →
      buchiProgress ewp AccEdge Q Rec (ITree.iter body a) s₀) m ?_ init s h_init
  intro m ih a s₀ hm
  rw [iter_unfold]
  refine buchiProgress.bind
    (buchiProgress.mono (fun _ _ _ hw => hw) (fun _ _ _ _ ha => ha) ?_ (fun _ _ hr => hr)
      (h_body m a s₀ hm))
  rintro (next | r) s' hp
  · obtain ⟨m', hlt, hm'⟩ := hp
    dsimp only [Sum.elim]
    rw [buchiProgress.tau_iff]
    exact ih m' hlt next s' hm'
  · dsimp only [Sum.elim]
    rw [buchiProgress.ret_iff]; exact hp

/-- `Nat`-ranked loop progress rule for `buchiProgress` over `ITree.iter`. -/
theorem buchiProgress.iter_ranked {I : Type u} {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop}
    (body : I → ITree E (I ⊕ R)) (LInv : Nat → I → S → Prop)
    {Q : R → S → Prop} {Rec : ITree E R → S → Prop}
    (h_body : ∀ n a s₀, LInv n a s₀ →
      buchiProgress ewp AccEdge
        (Sum.elim (fun next s' => ∃ m, m < n ∧ LInv m next s') Q)
        (fun t' s' => Rec (t' >>= Sum.elim (fun next => .tau (ITree.iter body next)) .ret) s')
        (body a) s₀)
    {n : Nat} {init : I} {s : S} (h_init : LInv n init s) :
    buchiProgress ewp AccEdge Q Rec (ITree.iter body init) s :=
  buchiProgress.iter_wf (fun a b : Nat => a < b) Nat.lt_wfRel.wf body LInv
    h_body h_init

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

/--
Under `[Conjunctive ewp]`, transition-relational `AlwaysStep` safety can be
merged into a Büchi recurrence proof, yielding recurrence over the
step-guarded transformer (every accepting run respects `StepRel`).
-/
theorem InfOften.guardStep_of_alwaysStep {ewp : StateEffectWP S E}
    [h_conj : StateEffectWP.Conjunctive ewp]
    {AccEdge StepRel : (i : E.I) → E.O i → S → S → Prop}
    {P Q : R → S → Prop} {t : ITree E R} {s : S}
    (h_safe : AlwaysStep ewp StepRel P t s) (h : InfOften ewp AccEdge Q t s) :
    InfOften (guardStepWP ewp StepRel) AccEdge Q t s := by
  refine InfOften.coinduct
    (fun x s₀ => AlwaysStep ewp StepRel P x s₀ ∧ InfOften ewp AccEdge Q x s₀)
    ?_ ⟨h_safe, h⟩
  rintro x s₀ ⟨hax, hix⟩
  refine InfOften.progress_induct
    (fun y s₁ => AlwaysStep ewp StepRel P y s₁ →
      buchiProgress (guardStepWP ewp StepRel) AccEdge Q
        (fun z s₂ => AlwaysStep ewp StepRel P z s₂ ∧ InfOften ewp AccEdge Q z s₂)
        y s₁) ?_ hix hax
  intro y s₁ hy hay
  rw [buchiProgress.unfold_eq]
  rw [AlwaysStep.unfold_eq] at hay
  cases h_obs : y.observe <;> simp only [h_obs] at hy hay ⊢
  · exact hy
  · exact hy.2 hay
  · exact ewp.mono
      (fun _ _ hpq => ⟨hpq.2.1,
        hpq.1.2.elim (fun ha => Or.inl ⟨ha, hpq.2.2, hpq.1.1⟩)
          (fun hpre => Or.inr (hpre hpq.2.2))⟩) (h_conj.conj hy hay)

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

/-- `InfOften` is stable forward across finite `.tau` prefixes. -/
theorem InfOften.tauStar {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t u : ITree E R} {s : S}
    (h_tau : TauStar t u) (h : InfOften ewp AccEdge Q t s) :
    InfOften ewp AccEdge Q u s := by
  induction h_tau with
  | refl => exact h
  | step ht _ ih => rw [eq_tau_of_observe ht, InfOften.tau_iff] at h; exact ih h

/-- `InfOften` is invariant backwards across finite `.tau` prefixes. -/
theorem InfOften.of_tauStar {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t u : ITree E R} {s : S}
    (h_tau : TauStar t u) (h : InfOften ewp AccEdge Q u s) :
    InfOften ewp AccEdge Q t s := by
  induction h_tau with
  | refl => exact h
  | step ht _ ih => rw [eq_tau_of_observe ht, InfOften.tau_iff]; exact ih h

/-- `InfOften` respects equivalence up to finite `.tau`s (`Eutt`). -/
theorem InfOften.eutt {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t u : ITree E R} {s : S} (he : Eutt t u)
    (h : InfOften ewp AccEdge Q t s) : InfOften ewp AccEdge Q u s := by
  let X : ITree E R → S → Prop := fun u₀ s₀ =>
    ∃ t₀, Eutt t₀ u₀ ∧ InfOften ewp AccEdge Q t₀ s₀
  refine InfOften.coinduct X ?_ ⟨t, he, h⟩
  rintro u₀ s₀ ⟨t₀, h_eutt, ht₀⟩
  refine buchiProgress.induct
    (fun x s₁ => ∀ u₁, Eutt x u₁ → buchiProgress ewp AccEdge Q X u₁ s₁)
    ?_ ht₀.toBuchiProgress u₀ h_eutt
  intro x s₁ hx u₁ h_eu
  cases h_obs : x.observe with
  | ret r =>
    simp only [h_obs] at hx
    obtain ⟨u', hu, hur⟩ := eutt_inv_ret h_eu h_obs
    exact buchiProgress.of_tauStar hu
      (by rw [eq_ret_of_observe hur, buchiProgress.ret_iff]; exact hx)
  | tau x' =>
    simp only [h_obs] at hx
    rcases eutt_inv_tau h_eu h_obs with h' | ⟨u', hu, h'⟩
    · exact hx u₁ h'
    · rw [eq_tau_of_observe hu, buchiProgress.tau_iff]; exact hx u' h'
  | vis i k =>
    simp only [h_obs] at hx
    obtain ⟨u', k₂, hu, huv, hk⟩ := eutt_inv_vis h_eu h_obs
    refine buchiProgress.of_tauStar hu ?_
    rw [eq_vis_of_observe huv, buchiProgress.vis_iff]
    exact ewp.mono
      (fun o _ hp => hp.elim
        (fun ⟨ha, hio⟩ => Or.inl ⟨ha, ⟨k o, hk o, hio⟩⟩)
        (fun ih => Or.inr (ih (k₂ o) (hk o)))) hx

/-- `Eutt`-equivalent trees satisfy the exact same `InfOften` specs. -/
theorem InfOften.eutt_iff (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    {t u : ITree E R} (he : Eutt t u) (s : S) :
    InfOften ewp AccEdge Q t s ↔ InfOften ewp AccEdge Q u s :=
  ⟨InfOften.eutt he, InfOften.eutt he.symm⟩

/--
Under an invariant-guarded transformer `guardInvWP ewp Inv`, the invariant can
always be added to the return postcondition of `InfOften` without needing
`Conjunctive ewp`.
-/
theorem InfOften.post_inv_guardInv {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Inv : S → Prop}
    {Q : R → S → Prop} {t : ITree E R} {s : S}
    (h_inv : Inv s) (h : InfOften (guardInvWP ewp Inv) AccEdge Q t s) :
    InfOften (guardInvWP ewp Inv) AccEdge (fun r s' => Inv s' ∧ Q r s') t s := by
  let X : ITree E R → S → Prop := fun x s₀ =>
    Inv s₀ ∧ InfOften (guardInvWP ewp Inv) AccEdge Q x s₀
  refine InfOften.coinduct X ?_ ⟨h_inv, h⟩
  rintro x s₀ ⟨hi₀, hx⟩
  refine buchiProgress.induct
    (fun y s₁ => Inv s₁ →
      buchiProgress (guardInvWP ewp Inv) AccEdge
        (fun r s' => Inv s' ∧ Q r s') X y s₁)
    ?_ hx.toBuchiProgress hi₀
  intro y s₁ hy hi₁
  rw [buchiProgress.unfold_eq]
  cases h_obs : y.observe <;> simp only [h_obs] at hy ⊢
  · exact ⟨hi₁, hy⟩
  · exact hy hi₁
  · exact ewp.mono
      (fun _ _ ⟨hi', hp⟩ =>
        ⟨hi', hp.elim (fun ⟨ha, hio⟩ => Or.inl ⟨ha, ⟨hi', hio⟩⟩)
          (fun hpre => Or.inr (hpre hi'))⟩) hy

/--
**Suffix-no-accept refutation**: under conjunctivity and excluded miracle, any
tree whose reachable steps all avoid `AccEdge` and whose returns all avoid `Q`
cannot satisfy `InfOften` — even when `AccEdge` is non-empty globally.
-/
theorem not_infOften_of_alwaysStep_not_accept {ewp : StateEffectWP S E}
    [h_conj : StateEffectWP.Conjunctive ewp]
    [h_em : StateEffectWP.ExcludedMiracle ewp]
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t : ITree E R} {s : S}
    (h_no : AlwaysStep ewp (fun i o s₀ s' => ¬ AccEdge i o s₀ s')
      (fun r s' => ¬ Q r s') t s) :
    ¬ InfOften ewp AccEdge Q t s := by
  intro h
  refine buchiProgress.induct
    (fun x s₀ => AlwaysStep ewp (fun i o s₁ s₂ => ¬ AccEdge i o s₁ s₂)
      (fun r s₁ => ¬ Q r s₁) x s₀ → False) ?_ h.toBuchiProgress h_no
  intro x s₀ hx h_as
  rw [AlwaysStep.unfold_eq] at h_as
  cases h_obs : x.observe <;> simp only [h_obs] at hx h_as
  · exact h_as hx
  · exact hx h_as
  · refine h_em.no_miracle
      (ewp.mono (fun _ _ ⟨hp, ⟨hna, has'⟩⟩ => hp.elim (fun ha => hna ha.1) (fun f => f has'))
        (h_conj.conj hx h_as))

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
**Finite-accept-prefix-then-stutter refutation**: if a terminating (`DWP`)
prefix `t` (which may emit arbitrarily many accepting edges!) transitions into
a suffix `k a` that never again takes an accepting edge or returns with `Q`,
then `t >>= k` refutes `InfOften`.
-/
theorem not_infOften_of_dwp_then_no_accept {A : Type u}
    {ewp : StateEffectWP S E}
    [StateEffectWP.Conjunctive ewp] [StateEffectWP.ExcludedMiracle ewp]
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t : ITree E A} {k : A → ITree E R} {s : S}
    (h_prefix : DWP ewp t
      (fun a s' => AlwaysStep ewp (fun i o s₀ s₁ => ¬ AccEdge i o s₀ s₁)
        (fun r s₁ => ¬ Q r s₁) (k a) s') s) :
    ¬ InfOften ewp AccEdge Q (t >>= k) s := by
  rw [InfOften.bind_iff]
  exact not_infOften_of_dwp_disjoint
    (fun _ _ has => not_infOften_of_alwaysStep_not_accept has) h_prefix

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

/--
**Well-founded diverging loop rule**: combines `Always` safety and `InfOften`
recurrence for an arbitrary well-founded measure `lt` (e.g., lexicographic
contention/fairness ranks).
-/
theorem buchi_diverging_loop_wf {I : Type u} {α : Type _}
    {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Inv : S → Prop}
    (lt : α → α → Prop) (h_wf : WellFounded lt)
    (body : I → ITree E I) (LInv : α → I → S → Prop)
    (h_safe : ∀ m a s₀, LInv m a s₀ →
      Always ewp Inv (fun next s' => ∃ m', LInv m' next s') (body a) s₀)
    (h_live : ∀ m a s₀, LInv m a s₀ →
      buchiProgress ewp AccEdge
        (fun next s' => ∃ m', lt m' m ∧ LInv m' next s')
        (InfOften ewp AccEdge (fun next s' => ∃ m', LInv m' next s'))
        (body a) s₀)
    {m : α} {init : I} {s : S} (h_init : LInv m init s)
    (Q : PEmpty.{u + 1} → S → Prop) :
    Always ewp Inv Q (divergingLoop body init) s ∧
      InfOften ewp AccEdge Q (divergingLoop body init) s :=
  ⟨always_divergingLoop body (fun a s' => ∃ m', LInv m' a s')
     (fun a s₀ ⟨m', hm'⟩ => h_safe m' a s₀ hm') ⟨m, h_init⟩ Q,
   infOften_divergingLoop_wf lt h_wf body LInv h_live h_init Q⟩

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

The successor is chosen *at the current tree position*, i.e. knowing the
history but not the environment's future answers. `BuchiSat` is therefore
sound for every monitor, and complete for deterministic (`ofDet`) or
history-deterministic monitors, but incomplete for monitors that must guess
the future (e.g. the two-state automaton for `◇□ a` against an environment
that may emit one more `b` at every step).
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

/--
Universal (∀-successor) monitor product: requires at least one valid monitor
successor (`∃ q', step ...`) and checks `K` against **every** valid monitor
successor (`∀ q', step ... → K o (q', s')`). Unlike `prodWP`, this product is
always `Conjunctive` and `DownContinuous` even for nondeterministic monitors.
-/
def univProdWP (spec : BuchiSpec S QState E R) :
    StateEffectWP (QState × S) E where
  wp i K qs :=
    spec.ewp.wp i
      (fun o s' =>
        (∃ q', spec.step qs.1 i o qs.2 s' q') ∧
        ∀ q', spec.step qs.1 i o qs.2 s' q' → K o (q', s')) qs.2
  mono h hw :=
    spec.ewp.mono
      (fun o _ hk => ⟨hk.1, fun q' hs => h o _ (hk.2 q' hs)⟩) hw

instance (spec : BuchiSpec S QState E R)
    [h_conj : StateEffectWP.Conjunctive spec.ewp] :
    StateEffectWP.Conjunctive spec.univProdWP where
  conj hp hq :=
    spec.ewp.mono
      (fun _ _ hpq => ⟨hpq.1.1, fun q' hs => ⟨hpq.1.2 q' hs, hpq.2.2 q' hs⟩⟩)
      (h_conj.conj hp hq)

instance (spec : BuchiSpec S QState E R)
    [h_em : StateEffectWP.ExcludedMiracle spec.ewp] :
    StateEffectWP.ExcludedMiracle spec.univProdWP where
  no_miracle hw :=
    h_em.no_miracle
      (spec.ewp.mono (fun _ _ hk => hk.1.elim fun q' hs => hk.2 q' hs) hw)

/-- Universal monitor satisfaction always implies existential (NBA) monitor satisfaction. -/
theorem univProdWP_to_prodWP (spec : BuchiSpec S QState E R)
    (i : E.I) (K : E.O i → QState × S → Prop) (qs : QState × S)
    (h : spec.univProdWP.wp i K qs) : spec.prodWP.wp i K qs :=
  spec.ewp.mono (fun _ _ hk => hk.1.elim fun q' hs => ⟨q', hs, hk.2 q' hs⟩) h

/-- For deterministic monitors, `univProdWP` and `prodWP` coincide identically. -/
theorem univProdWP_wp_iff_prodWP_wp_of_det (spec : BuchiSpec S QState E R)
    (h_det : ∀ q i o s s' q₁ q₂,
      spec.step q i o s s' q₁ → spec.step q i o s s' q₂ → q₁ = q₂)
    (i : E.I) (K : E.O i → QState × S → Prop) (qs : QState × S) :
    spec.univProdWP.wp i K qs ↔ spec.prodWP.wp i K qs := by
  refine ⟨univProdWP_to_prodWP spec i K qs, fun hw => ?_⟩
  refine spec.ewp.mono (fun _ _ hk => hk.elim fun q₁ h₁ => ?_) hw
  exact ⟨⟨q₁, h₁.1⟩, fun q₂ h₂ => (h_det _ _ _ _ _ _ _ h₁.1 h₂) ▸ h₁.2⟩

/--
Trivial one-state (`PUnit`) Büchi specification lifting a plain `(ewp, AccEdge,
Inv, Q)` specification directly into `BuchiSpec`.
-/
def trivial (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop)
    (Inv : S → Prop) (Q : R → S → Prop) :
    BuchiSpec S PUnit.{u + 1} E R where
  ewp := ewp
  step _ _ _ _ _ _ := True
  accept _ i o s s' _ := AccEdge i o s s'
  inv _ s := Inv s
  terminal _ r s := Q r s

/--
Deterministic Büchi monitor constructor: the transition function `next` selects
the unique successor whenever `allow` holds, avoiding existential witness
boilerplate and automatically preserving conjunctivity and co-continuity.
-/
def ofDet (ewp : StateEffectWP S E)
    (next : QState → (i : E.I) → E.O i → S → S → QState)
    (allow : QState → (i : E.I) → E.O i → S → S → Prop)
    (accept : QState → (i : E.I) → E.O i → S → S → Prop)
    (inv : QState → S → Prop) (terminal : QState → R → S → Prop) :
    BuchiSpec S QState E R where
  ewp := ewp
  step q i o s s' q' := allow q i o s s' ∧ q' = next q i o s s'
  accept q i o s s' q' := accept q i o s s' ∧ q' = next q i o s s'
  inv := inv
  terminal := terminal

theorem ofDet_step_det (ewp : StateEffectWP S E)
    (next : QState → (i : E.I) → E.O i → S → S → QState)
    (allow accept : QState → (i : E.I) → E.O i → S → S → Prop)
    (inv : QState → S → Prop) (terminal : QState → R → S → Prop) :
    ∀ q i o s s' q₁ q₂,
      (ofDet ewp next allow accept inv terminal).step q i o s s' q₁ →
      (ofDet ewp next allow accept inv terminal).step q i o s s' q₂ → q₁ = q₂ :=
  fun _ _ _ _ _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm

@[simp]
theorem ofDet_monitorWP_wp (ewp : StateEffectWP S E)
    (next : QState → (i : E.I) → E.O i → S → S → QState)
    (allow accept : QState → (i : E.I) → E.O i → S → S → Prop)
    (inv : QState → S → Prop) (terminal : QState → R → S → Prop)
    (i : E.I) (K : E.O i → QState × S → Prop) (q : QState) (s : S) :
    (ofDet ewp next allow accept inv terminal).monitorWP.wp i K (q, s) ↔
      ewp.wp i (fun o s' =>
        allow q i o s s' ∧ inv (next q i o s s') s' ∧
          K o (next q i o s s', s')) s := by
  constructor
  · exact ewp.mono (fun _ _ ⟨q', ⟨ha, hq⟩, hi, hk⟩ => hq ▸ ⟨ha, hi, hk⟩)
  · exact ewp.mono (fun _ _ ⟨ha, hi, hk⟩ => ⟨next q i _ s _, ⟨ha, rfl⟩, hi, hk⟩)

instance (ewp : StateEffectWP S E) [h_conj : StateEffectWP.Conjunctive ewp]
    (next : QState → (i : E.I) → E.O i → S → S → QState)
    (allow accept : QState → (i : E.I) → E.O i → S → S → Prop)
    (inv : QState → S → Prop) (terminal : QState → R → S → Prop) :
    StateEffectWP.Conjunctive (ofDet ewp next allow accept inv terminal).prodWP :=
  @prodWP_conjunctive _ _ _ _ (ofDet ewp next allow accept inv terminal) h_conj
    (ofDet_step_det ewp next allow accept inv terminal)

/--
Classical 2-state Choueka flag monitor reducing Generalized Büchi acceptance
($\Box\Diamond \mathit{Acc}_1 \land \Box\Diamond \mathit{Acc}_2$) to a single
Büchi acceptance condition: state `false` waits for `Acc₁` to advance to `true`,
and state `true` waits for `Acc₂` to emit an accepting transition back to `false`.
-/
def generalized2 (ewp : StateEffectWP S E)
    (Acc₁ Acc₂ : (i : E.I) → E.O i → S → S → Prop)
    (Q : R → S → Prop) : BuchiSpec S (ULift.{u} Bool) E R where
  ewp := ewp
  step q i o s s' q' :=
    match q.down with
    | false => (q'.down = true ∧ Acc₁ i o s s') ∨ q'.down = false
    | true => (q'.down = false ∧ Acc₂ i o s s') ∨ q'.down = true
  accept q i o s s' q' := q.down = true ∧ q'.down = false ∧ Acc₂ i o s s'
  inv _ _ := True
  terminal _ r s := Q r s

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

@[simp]
theorem BuchiSat.ret_iff (spec : BuchiSpec S QState E R)
    (r : R) (q₀ : QState) (s₀ : S) :
    BuchiSat spec (.ret r) q₀ s₀ ↔ spec.inv q₀ s₀ ∧ spec.terminal q₀ r s₀ := by
  rw [buchiSat_iff_infOften, InfOften.ret_iff]; rfl

@[simp]
theorem BuchiSat.tau_iff (spec : BuchiSpec S QState E R)
    (t : ITree E R) (q₀ : QState) (s₀ : S) :
    BuchiSat spec (.tau t) q₀ s₀ ↔ BuchiSat spec t q₀ s₀ := by
  rw [buchiSat_iff_infOften, buchiSat_iff_infOften, InfOften.tau_iff]

@[simp]
theorem BuchiSat.vis_iff (spec : BuchiSpec S QState E R)
    (i : E.I) (k : E.O i → ITree E R) (q₀ : QState) (s₀ : S) :
    BuchiSat spec (.vis i k) q₀ s₀ ↔
      spec.inv q₀ s₀ ∧
        spec.ewp.wp i (fun o s' => ∃ q',
          spec.step q₀ i o s₀ s' q' ∧ BuchiSat spec (k o) q' s') s₀ := by
  rw [buchiSat_iff_infOften, InfOften.vis_iff, BuchiSpec.monitorWP_wp]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · exact spec.ewp.mono (fun _ _ ⟨q', hs, hi, hio⟩ =>
      ⟨q', hs, (buchiSat_iff_infOften spec _ q' _).2 ⟨hi, hio⟩⟩)
  · exact spec.ewp.mono (fun _ _ ⟨q', hs, hbs⟩ =>
      let ⟨hi, hio⟩ := (buchiSat_iff_infOften spec _ q' _).1 hbs
      ⟨q', hs, hi, hio⟩)

theorem BuchiSat.ret {spec : BuchiSpec S QState E R}
    {r : R} {q₀ : QState} {s₀ : S}
    (h_inv : spec.inv q₀ s₀) (ht : spec.terminal q₀ r s₀) :
    BuchiSat spec (.ret r) q₀ s₀ :=
  (BuchiSat.ret_iff spec r q₀ s₀).2 ⟨h_inv, ht⟩

theorem BuchiSat.tau {spec : BuchiSpec S QState E R}
    {t : ITree E R} {q₀ : QState} {s₀ : S} (h : BuchiSat spec t q₀ s₀) :
    BuchiSat spec (.tau t) q₀ s₀ :=
  (BuchiSat.tau_iff spec t q₀ s₀).2 h

/-- `BuchiSat` respects equivalence up to finite `.tau`s (`Eutt`). -/
theorem BuchiSat.eutt {spec : BuchiSpec S QState E R}
    {t u : ITree E R} {q₀ : QState} {s₀ : S}
    (he : Eutt t u) (h : BuchiSat spec t q₀ s₀) :
    BuchiSat spec u q₀ s₀ :=
  ⟨Always.eutt he h.1, InfOften.eutt he h.2⟩

/-- `Eutt`-equivalent trees satisfy the exact same `BuchiSat` specifications. -/
theorem BuchiSat.eutt_iff (spec : BuchiSpec S QState E R)
    {t u : ITree E R} (he : Eutt t u) (q₀ : QState) (s₀ : S) :
    BuchiSat spec t q₀ s₀ ↔ BuchiSat spec u q₀ s₀ :=
  ⟨BuchiSat.eutt he, BuchiSat.eutt he.symm⟩

/--
**Exact monadic bind characterisation for `BuchiSat`**, holding for every
`BuchiSpec` (including nondeterministic, non-conjunctive monitors).
-/
theorem BuchiSat.bind_iff {A : Type u} (spec : BuchiSpec S QState E R)
    (t : ITree E A) (k : A → ITree E R) (q₀ : QState) (s₀ : S) :
    BuchiSat spec (t >>= k) q₀ s₀ ↔
      BuchiSat (spec.withTerminal (fun q a s => BuchiSat spec (k a) q s))
        t q₀ s₀ := by
  refine ⟨fun h => ?_, BuchiSat.bind⟩
  have ⟨hi, hio⟩ := (buchiSat_iff_infOften spec (t >>= k) q₀ s₀).1 h
  rw [InfOften.bind_iff] at hio
  have hio' := InfOften.post_inv_guardInv (ewp := spec.prodWP)
    (Inv := spec.invPred) (s := (q₀, s₀)) hi hio
  refine (buchiSat_iff_infOften _ t q₀ s₀).2 ⟨hi, ?_⟩
  refine InfOften.mono_post (fun a qs ⟨hi', hio_k⟩ => ?_) hio'
  exact (buchiSat_iff_infOften spec (k a) qs.1 qs.2).2 ⟨hi', hio_k⟩

/-- Well-founded loop rule for general `ITree.iter` under `BuchiSat`. -/
theorem BuchiSat.iter_wf {I : Type u} {α : Type _}
    (spec : BuchiSpec S QState E R)
    (lt : α → α → Prop) (h_wf : WellFounded lt)
    (body : I → ITree E (I ⊕ R)) (LInv : α → I → QState → S → Prop)
    (h_body : ∀ m a q s, LInv m a q s →
      buchiProgress spec.monitorWP spec.acceptEdge
        (Sum.elim (fun next qs' => ∃ m', lt m' m ∧ LInv m' next qs'.1 qs'.2)
          spec.terminalPost)
        (InfOften spec.monitorWP spec.acceptEdge
          (Sum.elim (fun next qs' => ∃ m', LInv m' next qs'.1 qs'.2)
            spec.terminalPost))
        (body a) (q, s))
    {m : α} {init : I} {q₀ : QState} {s₀ : S}
    (h_inv : spec.inv q₀ s₀) (h_init : LInv m init q₀ s₀) :
    BuchiSat spec (ITree.iter body init) q₀ s₀ :=
  (buchiSat_iff_infOften spec _ q₀ s₀).2
    ⟨h_inv,
     InfOften.iter_wf lt h_wf body (fun m a qs => LInv m a qs.1 qs.2)
       (fun m a qs hm => h_body m a qs.1 qs.2 hm) h_init⟩

/-- `Nat`-ranked loop rule for general `ITree.iter` under `BuchiSat`. -/
theorem BuchiSat.iter_ranked {I : Type u}
    (spec : BuchiSpec S QState E R)
    (body : I → ITree E (I ⊕ R)) (LInv : Nat → I → QState → S → Prop)
    (h_body : ∀ n a q s, LInv n a q s →
      buchiProgress spec.monitorWP spec.acceptEdge
        (Sum.elim (fun next qs' => ∃ m, m < n ∧ LInv m next qs'.1 qs'.2)
          spec.terminalPost)
        (InfOften spec.monitorWP spec.acceptEdge
          (Sum.elim (fun next qs' => ∃ m, LInv m next qs'.1 qs'.2)
            spec.terminalPost))
        (body a) (q, s))
    {n : Nat} {init : I} {q₀ : QState} {s₀ : S}
    (h_inv : spec.inv q₀ s₀) (h_init : LInv n init q₀ s₀) :
    BuchiSat spec (ITree.iter body init) q₀ s₀ :=
  BuchiSat.iter_wf spec (fun a b : Nat => a < b) Nat.lt_wfRel.wf body LInv
    h_body h_inv h_init

/-- Single-iteration progress loop rule for general `ITree.iter` under `BuchiSat`. -/
theorem BuchiSat.iter_progress {I : Type u}
    (spec : BuchiSpec S QState E R)
    (body : I → ITree E (I ⊕ R)) (LInv : I → QState → S → Prop)
    (h_body : ∀ a q s, LInv a q s →
      buchiProgress spec.monitorWP spec.acceptEdge
        (Sum.elim (fun _ _ => False) spec.terminalPost)
        (InfOften spec.monitorWP spec.acceptEdge
          (Sum.elim (fun next qs' => LInv next qs'.1 qs'.2) spec.terminalPost))
        (body a) (q, s))
    {init : I} {q₀ : QState} {s₀ : S}
    (h_inv : spec.inv q₀ s₀) (h_init : LInv init q₀ s₀) :
    BuchiSat spec (ITree.iter body init) q₀ s₀ :=
  (buchiSat_iff_infOften spec _ q₀ s₀).2
    ⟨h_inv,
     InfOften.iter_progress body (fun a qs => LInv a qs.1 qs.2)
       (fun a qs ha => h_body a qs.1 qs.2 ha) h_init⟩

/-- Well-founded diverging loop rule for `BuchiSat`. -/
theorem buchiSat_diverging_loop_wf {I : Type u} {α : Type _}
    (spec : BuchiSpec S QState E PEmpty.{u + 1})
    (lt : α → α → Prop) (h_wf : WellFounded lt)
    (body : I → ITree E I) (LInv : α → I → QState → S → Prop)
    (h_live : ∀ m a q s, LInv m a q s →
      buchiProgress spec.monitorWP spec.acceptEdge
        (fun next qs' => ∃ m', lt m' m ∧ LInv m' next qs'.1 qs'.2)
        (InfOften spec.monitorWP spec.acceptEdge
          (fun next qs' => ∃ m', LInv m' next qs'.1 qs'.2))
        (body a) (q, s))
    {m : α} {init : I} {q₀ : QState} {s₀ : S}
    (h_inv : spec.inv q₀ s₀) (h_init : LInv m init q₀ s₀) :
    BuchiSat spec (divergingLoop body init) q₀ s₀ :=
  (buchiSat_iff_infOften spec _ q₀ s₀).2
    ⟨h_inv,
     infOften_divergingLoop_wf lt h_wf body (fun m a qs => LInv m a qs.1 qs.2)
       (fun m a qs hm => h_live m a qs.1 qs.2 hm) h_init _⟩

/--
**Trivial monitor collapse**: a trivial `PUnit` `BuchiSpec` reduces identically
to the initial invariant plus `InfOften` over `guardInvWP ewp Inv`.
-/
theorem buchiSat_trivial_iff (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop)
    (Inv : S → Prop) (Q : R → S → Prop) (t : ITree E R) (s : S) :
    BuchiSat (BuchiSpec.trivial ewp AccEdge Inv Q) t PUnit.unit s ↔
      Inv s ∧ InfOften (guardInvWP ewp Inv) AccEdge Q t s := by
  let spec := BuchiSpec.trivial ewp AccEdge Inv Q
  rw [buchiSat_iff_infOften]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · refine InfOften.coinduct
      (fun x s₀ => InfOften spec.monitorWP spec.acceptEdge spec.terminalPost x (PUnit.unit, s₀))
      ?_ h
    intro x s₀ hx
    refine buchiProgress.induct
      (fun y qs => buchiProgress (guardInvWP ewp Inv) AccEdge Q
        (fun z s₁ => InfOften spec.monitorWP spec.acceptEdge spec.terminalPost z (PUnit.unit, s₁))
        y qs.2) ?_ hx.toBuchiProgress
    intro y qs hy
    rw [buchiProgress.unfold_eq]
    cases h_obs : y.observe <;> simp only [h_obs] at hy ⊢
    · exact hy
    · exact hy
    · exact ewp.mono (fun _ _ ⟨⟨⟩, _, hi, hp⟩ => ⟨hi, hp⟩) hy
  · refine InfOften.coinduct
      (fun x qs => InfOften (guardInvWP ewp Inv) AccEdge Q x qs.2) ?_ h
    intro x qs hx
    refine buchiProgress.induct
      (fun y s₁ => buchiProgress spec.monitorWP spec.acceptEdge spec.terminalPost
        (fun z qs' => InfOften (guardInvWP ewp Inv) AccEdge Q z qs'.2) y (qs.1, s₁))
      ?_ hx.toBuchiProgress
    intro y s₁ hy
    rw [buchiProgress.unfold_eq]
    cases h_obs : y.observe <;> simp only [h_obs] at hy ⊢
    · exact hy
    · exact hy
    · exact ewp.mono
        (fun _ _ ⟨hi, hp⟩ =>
          ⟨PUnit.unit, trivial, hi,
            hp.elim (fun ⟨ha, hio⟩ => Or.inl ⟨ha, hio⟩)
              (fun hpre => Or.inr (by cases qs.1; exact hpre))⟩) hy

/--
Under `[Conjunctive ewp]`, the trivial-monitor `BuchiSpec` is literally the
conjunction `Always ewp Inv Q t s ∧ InfOften ewp AccEdge Q t s`.
-/
theorem buchiSat_trivial_iff_always_and_infOften (ewp : StateEffectWP S E)
    [StateEffectWP.Conjunctive ewp]
    (AccEdge : (i : E.I) → E.O i → S → S → Prop)
    (Inv : S → Prop) (Q : R → S → Prop) (t : ITree E R) (s : S) :
    BuchiSat (BuchiSpec.trivial ewp AccEdge Inv Q) t PUnit.unit s ↔
      Always ewp Inv Q t s ∧ InfOften ewp AccEdge Q t s := by
  rw [buchiSat_trivial_iff]
  constructor
  · rintro ⟨hi, hio⟩
    refine ⟨(always_iff_dwlp_guard ewp Inv Q t s).2 ⟨hi, hio.toDWLP⟩, ?_⟩
    exact InfOften.mono (ewp := guardInvWP ewp Inv) (ewp' := ewp)
      (fun _ _ _ hw => ewp.mono (fun _ _ hk => hk.2) hw)
      (fun _ _ _ _ ha => ha) (fun _ _ hq => hq) hio
  · rintro ⟨ha, hio⟩
    exact ⟨ha.inv, InfOften.guardInv_of_always ha hio⟩

/--
**Generalized Büchi Reduction ($\Box\Diamond A_1 \land \Box\Diamond A_2 \iff \mathrm{BuchiSat}$)**:
under `[Conjunctive ewp]`, simultaneous recurrence of two distinct edge classes
`Acc₁` and `Acc₂` is **exactly equivalent** to `BuchiSat` of the 2-state
Choueka flag monitor `BuchiSpec.generalized2`.
-/
theorem buchiSat_generalized2_iff {ewp : StateEffectWP S E}
    [h_conj : StateEffectWP.Conjunctive ewp]
    (Acc₁ Acc₂ : (i : E.I) → E.O i → S → S → Prop)
    (Q : R → S → Prop) (t : ITree E R) (s : S) :
    BuchiSat (BuchiSpec.generalized2 ewp Acc₁ Acc₂ Q) t (ULift.up false) s ↔
      InfOften ewp Acc₁ Q t s ∧ InfOften ewp Acc₂ Q t s := by
  let spec := BuchiSpec.generalized2 ewp Acc₁ Acc₂ Q
  rw [buchiSat_iff_infOften]
  constructor
  · rintro ⟨_, hio⟩
    let X : ITree E R → S → Prop := fun x s₀ =>
      ∃ q : ULift.{u} Bool,
        InfOften spec.monitorWP spec.acceptEdge spec.terminalPost x (q, s₀)
    have h_acc2 : ∀ x s₀, X x s₀ → InfOften ewp Acc₂ Q x s₀ := by
      intro x s₀ hx
      refine InfOften.coinduct X ?_ hx
      rintro y s₁ ⟨q, hy⟩
      refine buchiProgress.induct
        (fun z qs => buchiProgress ewp Acc₂ Q X z qs.2) ?_ hy.toBuchiProgress
      intro z qs hz
      rw [buchiProgress.unfold_eq]
      cases h_obs : z.observe <;> simp only [h_obs] at hz ⊢
      · exact hz
      · exact hz
      · exact ewp.mono
          (fun _ _ ⟨q', _, _, hp⟩ =>
            hp.elim (fun ⟨⟨_, _, ha₂⟩, hio'⟩ => Or.inl ⟨ha₂, ⟨q', hio'⟩⟩) Or.inr) hz
    have h_false : ∀ x s₀,
        InfOften spec.monitorWP spec.acceptEdge spec.terminalPost x (ULift.up false, s₀) →
        buchiProgress ewp Acc₁ Q X x s₀ := by
      intro x s₀ hx
      refine InfOften.progress_induct
        (fun y qs => qs.1.down = false → buchiProgress ewp Acc₁ Q X y qs.2) ?_ hx rfl
      intro y qs hy hqf
      rw [buchiProgress.unfold_eq]
      cases h_obs : y.observe <;> simp only [h_obs] at hy ⊢
      · exact hy
      · exact hy.2 hqf
      · refine ewp.mono (fun _ _ ⟨q', hstep, _, hio', hdisj⟩ => ?_) hy
        have hpre : q'.down = false → buchiProgress ewp Acc₁ Q X _ _ :=
          hdisj.elim (fun ha => by
            dsimp only [spec, BuchiSpec.acceptEdge, BuchiSpec.generalized2] at ha
            rw [hqf] at ha; exact nomatch ha.1) id
        dsimp only [spec, BuchiSpec.generalized2] at hstep
        rw [hqf] at hstep
        rcases hstep with ⟨_, ha₁⟩ | hq'f
        · exact Or.inl ⟨ha₁, ⟨q', hio'⟩⟩
        · exact Or.inr (hpre hq'f)
    have h_true : ∀ x s₀,
        InfOften spec.monitorWP spec.acceptEdge spec.terminalPost x (ULift.up true, s₀) →
        buchiProgress ewp Acc₁ Q X x s₀ := by
      intro x s₀ hx
      refine InfOften.progress_induct
        (fun y qs => qs.1.down = true → buchiProgress ewp Acc₁ Q X y qs.2) ?_ hx rfl
      intro y qs hy hqt
      rw [buchiProgress.unfold_eq]
      cases h_obs : y.observe <;> simp only [h_obs] at hy ⊢
      · exact hy
      · exact hy.2 hqt
      · refine ewp.mono (fun _ _ ⟨q', hstep, _, hio', hdisj⟩ => ?_) hy
        dsimp only [spec, BuchiSpec.generalized2] at hstep
        rw [hqt] at hstep
        rcases hstep with ⟨hq'f, _⟩ | hq't
        · have hq'eq : q' = ULift.up false := by cases q'; cases hq'f; rfl
          subst hq'eq
          exact Or.inr (h_false _ _ hio')
        · have hpre : q'.down = true → buchiProgress ewp Acc₁ Q X _ _ :=
            hdisj.elim (fun ha => by
              dsimp only [spec, BuchiSpec.acceptEdge, BuchiSpec.generalized2] at ha
              rw [hq't] at ha; exact nomatch ha.2.1) id
          exact Or.inr (hpre hq't)
    refine ⟨InfOften.coinduct X ?_ ⟨ULift.up false, hio⟩, h_acc2 t s ⟨ULift.up false, hio⟩⟩
    rintro x s₀ ⟨⟨b⟩, hx⟩
    cases b with
    | false => exact h_false x s₀ hx
    | true => exact h_true x s₀ hx
  · rintro ⟨h₁, h₂⟩
    refine ⟨trivial, ?_⟩
    let Y : ITree E R → ULift.{u} Bool × S → Prop := fun x qs =>
      InfOften ewp Acc₁ Q x qs.2 ∧ InfOften ewp Acc₂ Q x qs.2
    have h_phase2 : ∀ x s₀, InfOften ewp Acc₁ Q x s₀ → InfOften ewp Acc₂ Q x s₀ →
        buchiProgress spec.monitorWP spec.acceptEdge spec.terminalPost Y x
          (ULift.up true, s₀) := by
      intro x s₀ hx₁ hx₂
      refine InfOften.progress_induct
        (fun y s₁ => InfOften ewp Acc₁ Q y s₁ →
          buchiProgress spec.monitorWP spec.acceptEdge spec.terminalPost Y y
            (ULift.up true, s₁)) ?_ hx₂ hx₁
      intro y s₁ hy hy₁
      rw [buchiProgress.unfold_eq]
      cases h_obs : y.observe with
      | ret r => simp only [h_obs] at hy ⊢; exact hy
      | tau y' =>
        simp only [h_obs] at hy ⊢
        rw [eq_tau_of_observe h_obs, InfOften.tau_iff] at hy₁
        exact hy.2 hy₁
      | vis i k =>
        simp only [h_obs] at hy ⊢
        rw [eq_vis_of_observe h_obs, InfOften.vis_iff] at hy₁
        refine ewp.mono (fun _ _ ⟨⟨hio₂, hdisj⟩, hio₁⟩ => ?_) (h_conj.conj hy hy₁)
        rcases hdisj with ha₂ | hpre
        · exact ⟨ULift.up false, Or.inl ⟨rfl, ha₂⟩, trivial,
            Or.inl ⟨⟨rfl, rfl, ha₂⟩, ⟨hio₁, hio₂⟩⟩⟩
        · exact ⟨ULift.up true, Or.inr rfl, trivial, Or.inr (hpre hio₁)⟩
    have h_phase1 : ∀ x s₀, InfOften ewp Acc₁ Q x s₀ → InfOften ewp Acc₂ Q x s₀ →
        buchiProgress spec.monitorWP spec.acceptEdge spec.terminalPost Y x
          (ULift.up false, s₀) := by
      intro x s₀ hx₁ hx₂
      refine InfOften.progress_induct
        (fun y s₁ => InfOften ewp Acc₂ Q y s₁ →
          buchiProgress spec.monitorWP spec.acceptEdge spec.terminalPost Y y
            (ULift.up false, s₁)) ?_ hx₁ hx₂
      intro y s₁ hy hy₂
      rw [buchiProgress.unfold_eq]
      cases h_obs : y.observe with
      | ret r => simp only [h_obs] at hy ⊢; exact hy
      | tau y' =>
        simp only [h_obs] at hy ⊢
        rw [eq_tau_of_observe h_obs, InfOften.tau_iff] at hy₂
        exact hy.2 hy₂
      | vis i k =>
        simp only [h_obs] at hy ⊢
        rw [eq_vis_of_observe h_obs, InfOften.vis_iff] at hy₂
        refine ewp.mono (fun _ _ ⟨⟨hio₁, hdisj⟩, hio₂⟩ => ?_) (h_conj.conj hy hy₂)
        rcases hdisj with ha₁ | hpre
        · exact ⟨ULift.up true, Or.inl ⟨rfl, ha₁⟩, trivial,
            Or.inr (h_phase2 _ _ hio₁ hio₂)⟩
        · exact ⟨ULift.up false, Or.inr rfl, trivial, Or.inr (hpre hio₂)⟩
    refine InfOften.coinduct Y ?_ ⟨h₁, h₂⟩
    rintro x ⟨⟨b⟩, s₀⟩ ⟨hx₁, hx₂⟩
    cases b with
    | false => exact h_phase1 x s₀ hx₁ hx₂
    | true => exact h_phase2 x s₀ hx₁ hx₂

end BuchiSat

/-! ### 3.3 Handler Linking and Operational Adequacy for `InfOften` -/

/--
**Horizontal handler linking** for `InfOften` across `ITree.interp`, supporting
both terminating and non-terminating Büchi-accepting handlers. Answers reached
*before* an accepting `E₂`-edge must lie in the non-accepting continuation
`Knon`; once the handler takes an accepting `E₂`-edge, its residual only needs
to satisfy `InfOften` into `Kacc ∨ Knon`.
-/
theorem InfOften.interp {S : Type u} {E₁ E₂ : Effect.{u}} {R : Type u}
    {ewp₁ : StateEffectWP S E₁} {ewp₂ : StateEffectWP S E₂}
    {Acc₁ : (i : E₁.I) → E₁.O i → S → S → Prop}
    {Acc₂ : (j : E₂.I) → E₂.O j → S → S → Prop}
    (h : (i : E₁.I) → ITree E₂ (E₁.O i))
    (h_link : ∀ (i : E₁.I) (Kacc Knon : E₁.O i → S → Prop) (s₀ : S),
      ewp₁.wp i (fun o s' => (Acc₁ i o s₀ s' ∧ Kacc o s') ∨ Knon o s') s₀ →
      buchiProgress ewp₂ Acc₂ Knon
        (InfOften ewp₂ Acc₂ (fun o s'' => Kacc o s'' ∨ Knon o s''))
        (h i) s₀)
    {t : ITree E₁ R} {Q : R → S → Prop} {s : S}
    (h_io : InfOften ewp₁ Acc₁ Q t s) :
    InfOften ewp₂ Acc₂ Q (ITree.interp h t) s := by
  let X : ITree E₂ R → S → Prop := fun u s₀ =>
    (∃ t₀, u = ITree.interp h t₀ ∧ InfOften ewp₁ Acc₁ Q t₀ s₀) ∨
    (∃ (i : E₁.I) (m : ITree E₂ (E₁.O i)) (k : E₁.O i → ITree E₁ R),
      u = (m >>= fun o => .tau (ITree.interp h (k o))) ∧
      InfOften ewp₂ Acc₂ (fun o s' => InfOften ewp₁ Acc₁ Q (k o) s') m s₀)
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
              InfOften.mono_post (fun _ _ hq => hq.elim id And.left) hd⟩)) id) hm
  refine InfOften.coinduct X ?_ (Or.inl ⟨t, rfl, h_io⟩)
  rintro u s₀ (⟨t₀, rfl, ht₀⟩ | ⟨i, m, k, rfl, hm⟩)
  · exact h_main t₀ s₀ ht₀
  · refine buchiProgress.induct
      (fun m s₁ => buchiProgress ewp₂ Acc₂ Q X
        (m >>= fun o => .tau (ITree.interp h (k o))) s₁) ?_ hm.toBuchiProgress
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
      exact ewp₂.mono
        (fun o₂ _ hp => hp.imp
          (And.imp id (fun hio_m => Or.inr ⟨i, c o₂, k, rfl, hio_m⟩)) id) hm

/-- `BuchiSat` horizontal handler linking across `ITree.interp`. -/
theorem BuchiSat.interp {S QState : Type u} {E₁ E₂ : Effect.{u}} {R : Type u}
    {spec₁ : BuchiSpec S QState E₁ R} {spec₂ : BuchiSpec S QState E₂ R}
    (h_inv : ∀ q s, spec₁.inv q s → spec₂.inv q s)
    (h_term : ∀ q r s, spec₁.terminal q r s → spec₂.terminal q r s)
    (h : (i : E₁.I) → ITree E₂ (E₁.O i))
    (h_link : ∀ (i : E₁.I) (Kacc Knon : E₁.O i → QState × S → Prop)
      (qs₀ : QState × S),
      spec₁.monitorWP.wp i
        (fun o qs' => (spec₁.acceptEdge i o qs₀ qs' ∧ Kacc o qs') ∨ Knon o qs') qs₀ →
      buchiProgress spec₂.monitorWP spec₂.acceptEdge Knon
        (InfOften spec₂.monitorWP spec₂.acceptEdge
          (fun o qs'' => Kacc o qs'' ∨ Knon o qs''))
        (h i) qs₀)
    {t : ITree E₁ R} {q₀ : QState} {s₀ : S}
    (h_bs : BuchiSat spec₁ t q₀ s₀) :
    BuchiSat spec₂ (ITree.interp h t) q₀ s₀ := by
  have ⟨hi, hio⟩ := (buchiSat_iff_infOften spec₁ t q₀ s₀).1 h_bs
  refine (buchiSat_iff_infOften spec₂ _ q₀ s₀).2 ⟨h_inv q₀ s₀ hi, ?_⟩
  exact InfOften.mono_post (fun r qs ht => h_term qs.1 r qs.2 ht)
    (InfOften.interp h h_link hio)

/-- Corollary of `InfOften.interp` specialized to terminating (`DWP`) handlers. -/
theorem InfOften.interp_dwp {S : Type u} {E₁ E₂ : Effect.{u}} {R : Type u}
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
    InfOften ewp₂ Acc₂ Q (ITree.interp h t) s :=
  InfOften.interp h
    (fun i Kacc Knon s₀ hw =>
      buchiProgress.mono_rec (fun _ _ hd => infOften_of_dwp Acc₂ hd)
        (h_link i Kacc Knon s₀ hw)) h_io

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
  · exact Or.inl ⟨ha, InfOften.ret (Or.inl hk)⟩
  · exact Or.inr ((buchiProgress.ret_iff _ _ _ _ _ _).2 hk)

/--
**Stateful handler linking** for `InfOften` across `ITree.interpState`,
threading the handler state `H` that the source transformer treats as its
logical state (supporting both terminating and Büchi-accepting handlers).
-/
theorem InfOften.interpState {H : Type u} {E₁ E₂ : Effect.{u}} {R : Type u}
    {ewp₁ : StateEffectWP H E₁} {ewp₂ : EffectWP E₂}
    {Acc₁ : (i : E₁.I) → E₁.O i → H → H → Prop}
    {Acc₂ : (j : E₂.I) → E₂.O j → PUnit.{u + 1} → PUnit.{u + 1} → Prop}
    (h : (i : E₁.I) → H → ITree E₂ (E₁.O i × H))
    (h_link : ∀ (i : E₁.I) (Kacc Knon : E₁.O i → H → Prop) (st : H),
      ewp₁.wp i (fun o st' => (Acc₁ i o st st' ∧ Kacc o st') ∨ Knon o st') st →
      buchiProgress ewp₂ Acc₂ (fun pair _ => Knon pair.1 pair.2)
        (InfOften ewp₂ Acc₂
          (fun pair _ => Kacc pair.1 pair.2 ∨ Knon pair.1 pair.2))
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
      InfOften ewp₂ Acc₂ (fun pair _ => InfOften ewp₁ Acc₁ Q (k pair.1) pair.2)
        m PUnit.unit)
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
              InfOften.mono_post (fun _ _ hq => hq.elim id And.left) hd⟩)) id) hm
  refine InfOften.coinduct X ?_ (Or.inl ⟨t, st, rfl, h_io⟩)
  rintro u ⟨⟩ (⟨t₀, st₀, rfl, ht₀⟩ | ⟨i, m, k, rfl, hm⟩)
  · exact h_main t₀ st₀ ht₀
  · refine buchiProgress.induct
      (fun m _ => buchiProgress ewp₂ Acc₂ (fun pair _ => Q pair.1 pair.2) X
        (m >>= fun (o, st') => .tau (ITree.interpState h (k o) st'))
        PUnit.unit) ?_ hm.toBuchiProgress
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
      exact ewp₂.mono
        (fun o₂ _ hp => hp.imp
          (And.imp id (fun hio_m => Or.inr ⟨i, c o₂, k, rfl, hio_m⟩)) id) hm

/-- Corollary of `InfOften.interpState` specialized to terminating (`DWP`) handlers. -/
theorem InfOften.interpState_dwp {H : Type u} {E₁ E₂ : Effect.{u}} {R : Type u}
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
      (ITree.interpState h t st) PUnit.unit :=
  InfOften.interpState h
    (fun i Kacc Knon st hw =>
      buchiProgress.mono_rec (fun _ _ hd => infOften_of_dwp Acc₂ hd)
        (h_link i Kacc Knon st hw)) h_io

/--
**Target-stateful handler linking** for `InfOften` across `ITree.interpState`:
the handler threads the program state `H`, while an independent logical/monitor
state `S₂` (such as a Büchi monitor state `QState` or an event trace
`List (Event E₂)`) is preserved across the lowered `E₂` tree.
-/
theorem InfOften.interpState_stateful {S₂ H : Type u} {E₁ E₂ : Effect.{u}}
    {R : Type u} {ewp₁ : StateEffectWP (S₂ × H) E₁} {ewp₂ : StateEffectWP S₂ E₂}
    {Acc₁ : (i : E₁.I) → E₁.O i → S₂ × H → S₂ × H → Prop}
    {Acc₂ : (j : E₂.I) → E₂.O j → S₂ → S₂ → Prop}
    (h : (i : E₁.I) → H → ITree E₂ (E₁.O i × H))
    (h_link : ∀ (i : E₁.I) (Kacc Knon : E₁.O i → S₂ × H → Prop)
      (s₂ : S₂) (st : H),
      ewp₁.wp i
        (fun o p' => (Acc₁ i o (s₂, st) p' ∧ Kacc o p') ∨ Knon o p') (s₂, st) →
      buchiProgress ewp₂ Acc₂ (fun pair s₂' => Knon pair.1 (s₂', pair.2))
        (InfOften ewp₂ Acc₂
          (fun pair s₂' => Kacc pair.1 (s₂', pair.2) ∨ Knon pair.1 (s₂', pair.2)))
        (h i st) s₂)
    {t : ITree E₁ R} {Q : R → S₂ × H → Prop} {s₂ : S₂} {st : H}
    (h_io : InfOften ewp₁ Acc₁ Q t (s₂, st)) :
    InfOften ewp₂ Acc₂ (fun pair s₂' => Q pair.1 (s₂', pair.2))
      (ITree.interpState h t st) s₂ := by
  let Q₂ : R × H → S₂ → Prop := fun pair s₂' => Q pair.1 (s₂', pair.2)
  let X : ITree E₂ (R × H) → S₂ → Prop := fun u s₀ =>
    (∃ t₀ st₀, u = ITree.interpState h t₀ st₀ ∧
      InfOften ewp₁ Acc₁ Q t₀ (s₀, st₀)) ∨
    (∃ (i : E₁.I) (m : ITree E₂ (E₁.O i × H)) (k : E₁.O i → ITree E₁ R),
      u = (m >>= fun (o, st') => .tau (ITree.interpState h (k o) st')) ∧
      InfOften ewp₂ Acc₂
        (fun pair s₂' => InfOften ewp₁ Acc₁ Q (k pair.1) (s₂', pair.2)) m s₀)
  have h_main : ∀ (t₀ : ITree E₁ R) (s₀ : S₂) (st₀ : H),
      InfOften ewp₁ Acc₁ Q t₀ (s₀, st₀) →
      buchiProgress ewp₂ Acc₂ Q₂ X (ITree.interpState h t₀ st₀) s₀ := by
    intro t₀ s₀ st₀ ht₀
    refine InfOften.progress_induct
      (fun t₁ p => buchiProgress ewp₂ Acc₂ Q₂ X
        (ITree.interpState h t₁ p.2) p.1) ?_ ht₀
    intro t₁ p hx
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
      have h_l := h_link i (fun o p' => InfOften ewp₁ Acc₁ Q (k o) p')
        (fun o p' => InfOften ewp₁ Acc₁ Q (k o) p' ∧
          buchiProgress ewp₂ Acc₂ Q₂ X (ITree.interpState h (k o) p'.2) p'.1)
        p.1 p.2
        (ewp₁.mono
          (fun _ _ hp => hp.2.elim (fun ha => Or.inl ⟨ha, hp.1⟩)
            (fun hpre => Or.inr ⟨hp.1, hpre⟩)) hx)
      refine buchiProgress.induct
        (fun m s₁ => buchiProgress ewp₂ Acc₂ Q₂ X
          (m >>= fun (o, st') => .tau (ITree.interpState h (k o) st')) s₁) ?_ h_l
      intro m s₁ hm
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
              InfOften.mono_post (fun _ _ hq => hq.elim id And.left) hd⟩)) id) hm
  refine InfOften.coinduct X ?_ (Or.inl ⟨t, st, rfl, h_io⟩)
  rintro u s₀ (⟨t₀, st₀, rfl, ht₀⟩ | ⟨i, m, k, rfl, hm⟩)
  · exact h_main t₀ s₀ st₀ ht₀
  · refine buchiProgress.induct
      (fun m s₁ => buchiProgress ewp₂ Acc₂ Q₂ X
        (m >>= fun (o, st') => .tau (ITree.interpState h (k o) st')) s₁)
      ?_ hm.toBuchiProgress
    intro m s₁ hm
    cases hm_obs : m.observe with
    | ret pair =>
      rcases pair with ⟨o, st'⟩
      simp only [hm_obs] at hm
      rw [eq_ret_of_observe hm_obs, ret_bind, buchiProgress.tau_iff]
      exact h_main (k o) s₁ st' hm
    | tau m' =>
      simp only [hm_obs] at hm
      rw [eq_tau_of_observe hm_obs, tau_bind, buchiProgress.tau_iff]
      exact hm
    | vis j c =>
      simp only [hm_obs] at hm
      rw [eq_vis_of_observe hm_obs, vis_bind, buchiProgress.vis_iff]
      exact ewp₂.mono
        (fun o₂ _ hp => hp.imp
          (And.imp id (fun hio_m => Or.inr ⟨i, c o₂, k, rfl, hio_m⟩)) id) hm

/--
**Stateful monitor handler linking** for `BuchiSat` across `ITree.interpState`:
the handler threads the program state `S` while the ghost Büchi monitor state
`QState` persists on the target `BuchiSpec PUnit QState E₂ (R × S)`.
-/
theorem BuchiSat.interpState {S QState : Type u} {E₁ E₂ : Effect.{u}}
    {R : Type u} {spec₁ : BuchiSpec S QState E₁ R}
    {spec₂ : BuchiSpec PUnit.{u + 1} QState E₂ (R × S)}
    (h_inv : ∀ q s, spec₁.inv q s → spec₂.inv q PUnit.unit)
    (h_term : ∀ q r s, spec₁.terminal q r s → spec₂.terminal q (r, s) PUnit.unit)
    (h : (i : E₁.I) → S → ITree E₂ (E₁.O i × S))
    (h_link : ∀ (i : E₁.I) (Kacc Knon : E₁.O i → QState × S → Prop)
      (q : QState) (s : S),
      spec₁.monitorWP.wp i
        (fun o qs' => (spec₁.acceptEdge i o (q, s) qs' ∧ Kacc o qs') ∨ Knon o qs')
        (q, s) →
      buchiProgress spec₂.monitorWP spec₂.acceptEdge
        (fun pair qp => Knon pair.1 (qp.1, pair.2))
        (InfOften spec₂.monitorWP spec₂.acceptEdge
          (fun pair qp =>
            Kacc pair.1 (qp.1, pair.2) ∨ Knon pair.1 (qp.1, pair.2)))
        (h i s) (q, PUnit.unit))
    {t : ITree E₁ R} {q₀ : QState} {s₀ : S}
    (h_bs : BuchiSat spec₁ t q₀ s₀) :
    BuchiSat spec₂ (ITree.interpState h t s₀) q₀ PUnit.unit := by
  have ⟨hi, hio⟩ := (buchiSat_iff_infOften spec₁ t q₀ s₀).1 h_bs
  let liftEwp₁ : StateEffectWP ((QState × PUnit.{u + 1}) × S) E₁ :=
    { wp := fun i K p => spec₁.monitorWP.wp i (fun o qs' => K o ((qs'.1, PUnit.unit), qs'.2))
        (p.1.1, p.2)
      mono := fun hm hw => spec₁.monitorWP.mono (fun o qs' hk => hm o _ hk) hw }
  have hio_lift : InfOften liftEwp₁
      (fun i o p p' => spec₁.acceptEdge i o (p.1.1, p.2) (p'.1.1, p'.2))
      (fun r p => spec₁.terminal p.1.1 r p.2) t ((q₀, PUnit.unit), s₀) := by
    refine InfOften.coinduct
      (fun x p => InfOften spec₁.monitorWP spec₁.acceptEdge spec₁.terminalPost x (p.1.1, p.2))
      ?_ hio
    intro x p hx
    refine buchiProgress.induct
      (fun y qs => buchiProgress liftEwp₁
        (fun i o a b => spec₁.acceptEdge i o (a.1.1, a.2) (b.1.1, b.2))
        (fun r a => spec₁.terminal a.1.1 r a.2)
        (fun z a => InfOften spec₁.monitorWP spec₁.acceptEdge spec₁.terminalPost z (a.1.1, a.2))
        y ((qs.1, PUnit.unit), qs.2)) ?_ hx.toBuchiProgress
    intro y qs hy
    rw [buchiProgress.unfold_eq]
    cases h_obs : y.observe <;> simp only [h_obs] at hy ⊢
    · exact hy
    · exact hy
    · exact hy
  have hio₂ := InfOften.interpState_stateful
    (S₂ := QState × PUnit.{u + 1}) (H := S) (ewp₁ := liftEwp₁)
    (ewp₂ := spec₂.monitorWP) h
    (fun i Kacc Knon qp s hw => by
      cases qp with
      | mk q u =>
        cases u
        exact h_link i (fun o qs' => Kacc o ((qs'.1, PUnit.unit), qs'.2))
          (fun o qs' => Knon o ((qs'.1, PUnit.unit), qs'.2)) q s hw)
    hio_lift
  refine (buchiSat_iff_infOften spec₂ _ q₀ PUnit.unit).2 ⟨h_inv q₀ s₀ hi, ?_⟩
  exact InfOften.mono_post (fun pair qp ht => h_term qp.1 pair.1 pair.2 ht) hio₂

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

/--
Bridge from `ITreeBuchi.EventuallyStep` to `Anneal.ITree.Eventually`: under
`PureSoundWP` and `InhabitedDemonic`, strict step eventuality of an accepting
request class (or `Q`-return) guarantees `Anneal.ITree.Eventually`.
-/
theorem eventuallyStep_to_itree_eventually
    [EffectOwner E] [InhabitedDemonic E]
    {ewp : EffectWP E} [h_sound : PureSoundWP ewp]
    {AccEdge : (i : E.I) → E.O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop}
    {AccReq : E.I → Prop} {Q : R → PUnit.{u + 1} → Prop}
    (h_acc : ∀ i o, AccEdge i o PUnit.unit PUnit.unit → AccReq i)
    {t : ITree E R} (h : EventuallyStep ewp AccEdge Q t PUnit.unit) :
    Anneal.ITree.Eventually
      (fun x => (∃ r, x.observe = .ret r ∧ Q r PUnit.unit) ∨
        (∃ i k, x.observe = .vis i k ∧ AccReq i)) t := by
  let P : ITree E R → Prop := fun x =>
    (∃ r, x.observe = .ret r ∧ Q r PUnit.unit) ∨
      (∃ i k, x.observe = .vis i k ∧ AccReq i)
  refine EventuallyStep.induct (fun x _ => Anneal.ITree.Eventually P x) ?_ h
  intro x ⟨⟩ hx
  cases h_obs : x.observe with
  | ret r =>
    simp only [h_obs] at hx
    exact .here (Or.inl ⟨r, h_obs, hx⟩)
  | tau x' =>
    simp only [h_obs] at hx
    exact .tau h_obs hx
  | vis i k =>
    simp only [h_obs] at hx
    have ⟨hnf, hall⟩ := h_sound.sound hx
    have hne : Nonempty (E.O i) := InhabitedDemonic.nonempty_of_nonFault i hnf
    by_cases ha : AccReq i
    · exact .here (Or.inr ⟨i, k, h_obs, ha⟩)
    · have hall' : ∀ o, Anneal.ITree.Eventually P (k o) := fun o =>
        (hall o).elim (fun hacc => False.elim (ha (h_acc i o hacc))) id
      cases ho : EffectOwner.owner i with
      | demonic => exact .visDemonic h_obs ho hnf hne hall'
      | angelic => exact hne.elim fun o => .visAngelic o h_obs ho hnf (hall' o)

/--
Bridge from `ITreeBuchi.InfOften` to `Anneal.ITree.InfinitelyOften` ($\Box\Diamond$):
every reachable residual satisfies `Anneal.ITree.Eventually` of an accepting
request (or a `Q`-return).
-/
theorem infOften_to_itree_infinitelyOften
    [EffectOwner E] [InhabitedDemonic E]
    {ewp : EffectWP E} [PureSoundWP ewp]
    {AccEdge : (i : E.I) → E.O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop}
    {AccReq : E.I → Prop} {Q : R → PUnit.{u + 1} → Prop}
    (h_acc : ∀ i o, AccEdge i o PUnit.unit PUnit.unit → AccReq i)
    {t : ITree E R} (h : InfOften ewp AccEdge Q t PUnit.unit) :
    Anneal.ITree.InfinitelyOften
      (fun x => (∃ r, x.observe = .ret r ∧ Q r PUnit.unit) ∨
        (∃ i k, x.observe = .vis i k ∧ AccReq i)) t := by
  have hco := infOften_coAlways_eventuallyStep h
  refine CoAlways.coinduct _
    (fun x => CoAlways (fun y => EventuallyStep ewp AccEdge Q y PUnit.unit) x)
    ?_ t hco
  intro x hx
  rw [CoAlways.eq_def] at hx
  exact ⟨eventuallyStep_to_itree_eventually h_acc hx.1, hx.2⟩

end InfOftenAdequacy

section InfOftenStreamAdequacy

private theorem followsStream_of_tau {α R : Type u}
    {t t' : ITree (ObsE α) R} {s : Stream' α}
    (h_tau : t.observe = .tau t') (hf : FollowsStream t s) :
    FollowsStream t' s := by
  rw [FollowsStream.eq_def] at hf ⊢
  rcases hf with ⟨u, k, hts, hv, hcont⟩
  cases hts with
  | refl => rw [h_tau] at hv; nomatch hv
  | step hstep hrest =>
    rw [h_tau] at hstep; injection hstep with h_eq; subst h_eq
    exact ⟨u, k, hrest, hv, hcont⟩

private theorem followsStream_vis_inv {α R : Type u}
    {t : ITree (ObsE α) R} {a : α} {k : PUnit.{u + 1} → ITree (ObsE α) R}
    {s : Stream' α} (hv : t.observe = .vis (.emit a) k)
    (hf : FollowsStream t s) :
    s 0 = a ∧ FollowsStream (k PUnit.unit) s.tail := by
  rw [FollowsStream.eq_def] at hf
  rcases hf with ⟨u, k', hts, hv', hcont⟩
  cases hts with
  | refl =>
    rw [hv] at hv'
    injection hv' with hreq hk
    injection hreq with ha
    subst ha
    cases hk
    exact ⟨rfl, hcont⟩
  | step hstep _ => rw [hv] at hstep; nomatch hstep

private theorem obs_infOften_next_exists {α : Type u}
    {Acc : (i : (ObsE α).I) → (ObsE α).O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop}
    {Q : PEmpty.{u + 1} → PUnit.{u + 1} → Prop}
    {x : ITree (ObsE α) PEmpty.{u + 1}}
    (h : InfOften (obsIgnoreWP PUnit.{u + 1} α) Acc Q x PUnit.unit) :
    ∃ a k, TauStar x (.vis (.emit a) k) ∧
      InfOften (obsIgnoreWP PUnit.{u + 1} α) Acc Q (k PUnit.unit) PUnit.unit := by
  obtain ⟨u, hts, hnt⟩ := infOften_stabilizes h
  have hu := InfOften.tauStar hts h
  cases hu_obs : u.observe with
  | ret r => exact PEmpty.elim r
  | tau w => exact False.elim (hnt w hu_obs)
  | vis i k =>
    cases i with
    | emit a =>
      have hu_eq : u = .vis (.emit a) k := eq_vis_of_observe hu_obs
      rw [hu_eq] at hts hu
      exact ⟨a, k, hts, (InfOften.vis_iff _ _ _ _ _ _).1 hu⟩

private noncomputable def obsStepState {α : Type u}
    {Acc : (i : (ObsE α).I) → (ObsE α).O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop}
    {Q : PEmpty.{u + 1} → PUnit.{u + 1} → Prop}
    (p : {x : ITree (ObsE α) PEmpty.{u + 1} //
      InfOften (obsIgnoreWP PUnit.{u + 1} α) Acc Q x PUnit.unit}) :
    α × {x : ITree (ObsE α) PEmpty.{u + 1} //
      InfOften (obsIgnoreWP PUnit.{u + 1} α) Acc Q x PUnit.unit} :=
  let a := Classical.choose (obs_infOften_next_exists p.2)
  let h1 := Classical.choose_spec (obs_infOften_next_exists p.2)
  let k := Classical.choose h1
  let h2 := Classical.choose_spec h1
  (a, ⟨k PUnit.unit, h2.2⟩)

private noncomputable def obsChainState {α : Type u}
    {Acc : (i : (ObsE α).I) → (ObsE α).O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop}
    {Q : PEmpty.{u + 1} → PUnit.{u + 1} → Prop}
    (n : Nat) :
    {x : ITree (ObsE α) PEmpty.{u + 1} //
      InfOften (obsIgnoreWP PUnit.{u + 1} α) Acc Q x PUnit.unit} →
    {x : ITree (ObsE α) PEmpty.{u + 1} //
      InfOften (obsIgnoreWP PUnit.{u + 1} α) Acc Q x PUnit.unit} :=
  Nat.rec id (fun _ ih p => ih (obsStepState p).2) n

private theorem obs_infOften_wait {α : Type u}
    (AccObs : α → Prop) (Q : PEmpty.{u + 1} → PUnit.{u + 1} → Prop)
    {x : ITree (ObsE α) PEmpty.{u + 1}}
    (h : InfOften (obsIgnoreWP PUnit.{u + 1} α)
      (fun i _ _ _ => match i with | .emit a => AccObs a) Q x PUnit.unit)
    {s : Stream' α} (hf : FollowsStream x s) :
    ∃ n : Nat, AccObs (s n) := by
  refine buchiProgress.induct
    (fun y _ => ∀ s', FollowsStream y s' → ∃ n, AccObs (s' n)) ?_ h.toBuchiProgress s hf
  intro y ⟨⟩ hy s' hfs
  cases h_obs : y.observe with
  | ret r => exact PEmpty.elim r
  | tau y' =>
    simp only [h_obs] at hy
    exact hy s' (followsStream_of_tau h_obs hfs)
  | vis i k =>
    cases i with
    | emit a =>
      simp only [h_obs] at hy
      have ⟨hs0, htail⟩ := followsStream_vis_inv h_obs hfs
      rcases hy with ⟨ha, _⟩ | ih
      · exact ⟨0, hs0.symm ▸ ha⟩
      · obtain ⟨m, hm⟩ := ih s'.tail htail
        exact ⟨m + 1, hm⟩

/--
**Exact $\omega$-language Büchi adequacy (`FollowsStream`)**: a non-returning
observation tree `t : ITree (ObsE α) PEmpty` satisfies `InfOften` for `AccObs`
**if and only if** it emits an infinite stream `s : Stream' α` (`FollowsStream`)
that visits `AccObs` infinitely often (`∀ k, ∃ n, k ≤ n ∧ AccObs (s n)`).
-/
theorem infOften_obsIgnoreWP_iff_followsStream {α : Type u}
    (AccObs : α → Prop) (Q : PEmpty.{u + 1} → PUnit.{u + 1} → Prop)
    (t : ITree (ObsE α) PEmpty.{u + 1}) :
    InfOften (obsIgnoreWP PUnit.{u + 1} α)
        (fun i _ _ _ => match i with | .emit a => AccObs a) Q t PUnit.unit ↔
      ∃ s : Stream' α, FollowsStream t s ∧ ∀ k : Nat, ∃ n : Nat, k ≤ n ∧ AccObs (s n) := by
  let Acc : (i : (ObsE α).I) → (ObsE α).O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop :=
    fun i _ _ _ => match i with | .emit a => AccObs a
  constructor
  · intro h
    let s : Stream' α := fun n => (obsStepState (obsChainState n ⟨t, h⟩)).1
    have h_fol : ∀ p : {x : ITree (ObsE α) PEmpty.{u + 1} //
        InfOften (obsIgnoreWP PUnit.{u + 1} α) Acc Q x PUnit.unit},
        FollowsStream p.1 (fun n => (obsStepState (obsChainState n p)).1) := by
      intro p₀
      refine FollowsStream.coinduct
        (fun u s' => ∃ p : {x : ITree (ObsE α) PEmpty.{u + 1} //
          InfOften (obsIgnoreWP PUnit.{u + 1} α) Acc Q x PUnit.unit},
          u = p.1 ∧ s' = fun n => (obsStepState (obsChainState n p)).1)
        ?_ p₀.1 _ ⟨p₀, rfl, rfl⟩
      rintro u s' ⟨p, rfl, rfl⟩
      let h1 := Classical.choose_spec (obs_infOften_next_exists p.2)
      let k := Classical.choose h1
      let h2 := Classical.choose_spec h1
      refine ⟨.vis (.emit (obsStepState p).1) k, k, h2.1, ITree.observe_vis _ _,
        ⟨(obsStepState p).2, rfl, rfl⟩⟩
    refine ⟨s, h_fol ⟨t, h⟩, fun k => ?_⟩
    have h_shift : FollowsStream (obsChainState k ⟨t, h⟩).1 (fun m => s (k + m)) := by
      have hc : ∀ (j m : Nat) (p : {x : ITree (ObsE α) PEmpty.{u + 1} //
          InfOften (obsIgnoreWP PUnit.{u + 1} α) Acc Q x PUnit.unit}),
          obsChainState m (obsChainState j p) = obsChainState (j + m) p := by
        intro j m
        induction j with
        | zero => intro p; rw [Nat.zero_add]; rfl
        | succ j ih =>
          intro p
          rw [Nat.succ_add]
          exact ih (obsStepState p).2
      have h_eq : (fun m => s (k + m)) =
          (fun m => (obsStepState (obsChainState m (obsChainState k ⟨t, h⟩))).1) := by
        funext m; dsimp only [s]; rw [hc k m ⟨t, h⟩]
      rw [h_eq]
      exact h_fol (obsChainState k ⟨t, h⟩)
    obtain ⟨m, hm⟩ := obs_infOften_wait AccObs Q (obsChainState k ⟨t, h⟩).2 h_shift
    exact ⟨k + m, Nat.le_add_right k m, hm⟩
  · rintro ⟨s, hfol, hinf⟩
    let X : ITree (ObsE α) PEmpty.{u + 1} → PUnit.{u + 1} → Prop := fun u _ =>
      ∃ s' : Stream' α, FollowsStream u s' ∧ ∀ k : Nat, ∃ n : Nat, k ≤ n ∧ AccObs (s' n)
    refine InfOften.coinduct X ?_ ⟨s, hfol, hinf⟩
    rintro u ⟨⟩ ⟨s', hfu, hinfu⟩
    obtain ⟨n, _, hn⟩ := hinfu 0
    have h_step : ∀ (d : Nat) (u₀ : ITree (ObsE α) PEmpty.{u + 1}) (s₀ : Stream' α),
        FollowsStream u₀ s₀ →
        (∀ k, ∃ m, k ≤ m ∧ AccObs (s₀ m)) →
        AccObs (s₀ d) →
        buchiProgress (obsIgnoreWP PUnit.{u + 1} α) Acc Q X u₀ PUnit.unit := by
      intro d
      induction d with
      | zero =>
        intro u₀ s₀ hfu₀ hinf₀ ha₀
        rw [FollowsStream.eq_def] at hfu₀
        rcases hfu₀ with ⟨u', k, hts, hv, hcont⟩
        refine buchiProgress.of_tauStar hts ?_
        rw [eq_vis_of_observe hv]
        refine buchiProgress.vis_accept ?_
        refine ⟨ha₀, ⟨s₀.tail, hcont, fun j => ?_⟩⟩
        obtain ⟨m, hle, hm⟩ := hinf₀ (j + 1)
        cases m with
        | zero => exact absurd hle (Nat.not_succ_le_zero j)
        | succ m' => exact ⟨m', Nat.le_of_succ_le_succ hle, hm⟩
      | succ d ih =>
        intro u₀ s₀ hfu₀ hinf₀ ha_succ
        rw [FollowsStream.eq_def] at hfu₀
        rcases hfu₀ with ⟨u', k, hts, hv, hcont⟩
        refine buchiProgress.of_tauStar hts ?_
        rw [eq_vis_of_observe hv]
        refine buchiProgress.vis_skip ?_
        refine ih (k PUnit.unit) s₀.tail hcont (fun j => ?_) ha_succ
        obtain ⟨m, hle, hm⟩ := hinf₀ (j + 1)
        cases m with
        | zero => exact absurd hle (Nat.not_succ_le_zero j)
        | succ m' => exact ⟨m', Nat.le_of_succ_le_succ hle, hm⟩
    exact h_step n u s' hfu hinfu hn

end InfOftenStreamAdequacy

section InfOftenStdDo

open Std.Do

variable {E : Effect.{u}} {R : Type u}

/-- `InfOften` over a `PureEffectWP` yields the corresponding `Std.Do.Triple`. -/
theorem Triple.of_infOften [p : PureEffectWP E]
    {AccEdge : (i : E.I) → E.O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop}
    {t : ITree E R} {P : Prop} {Q : R → Prop}
    (h : P → InfOften p.ewp AccEdge (fun r _ => Q r) t PUnit.unit) :
    ⦃⌜P⌝⦄ t ⦃⇓ r => ⌜Q r⌝⦄ :=
  fun hp => (h hp).toDWLP

end InfOftenStdDo

/-! ### 3.4 Fairness-Conditional Liveness (`FairInfOften`, Streett / Parity) -/

section FairInfOften

variable {S : Type u} {E : Effect.{u}} {R : Type u}

/-!
`InfOften` (Büchi) can only state `□◇ AccEdge ∨ ◇ ret`. Liveness of retry loops
*under a fairness assumption* (`creusot#2386` `Atomic::try_update`: "if the
environment infinitely often lets the CAS through, the loop terminates") is the
Streett condition `□◇ Fair → □◇ AccEdge` (or a `Q`-return). `FairInfOften` is the
max-parity game with priorities

* `4` accepting edges (`AccEdge`, good),
* `3` fair edges (`Fair`, bad unless dominated by accepting edges),
* `2` other visible edges (good: an unfair environment is not the program's fault),
* `1` silent `.tau` steps (bad: silent divergence is always rejected),

encoded as the four-level nested fixpoint `ν X₄. μ X₃. ν X₂. μ X₁`
(`FairInfOften` / `fairProgress` / `fairStall` / `fairStep`).
-/

private def fairStepAux (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (X4 X3 X2 : ITree E R → S → Prop) (t : ITree E R) (s : S) : Prop :=
  match t.observe with
  | .ret r => Q r s
  | .tau t' => fairStepAux ewp AccEdge Fair Q X4 X3 X2 t' s
  | .vis i k =>
    ewp.wp i
      (fun o s' => (AccEdge i o s s' ∧ X4 (k o) s') ∨
        (Fair i o s s' ∧ X3 (k o) s') ∨ (¬ Fair i o s s' ∧ X2 (k o) s')) s
inductive_fixpoint

/--
Innermost level (`μ X₁`, priority `1`) of the fairness game: after finitely many
silent steps the tree returns with `Q` or takes a visible edge, whose residual
must satisfy `X4` (accepting edge), `X3` (fair edge) or `X2` (unfair edge).
-/
def fairStep (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (X4 X3 X2 : ITree E R → S → Prop) (t : ITree E R) (s : S) : Prop :=
  fairStepAux ewp AccEdge Fair Q X4 X3 X2 t s

theorem fairStep.unfold_eq (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (X4 X3 X2 : ITree E R → S → Prop) (t : ITree E R) (s : S) :
    fairStep ewp AccEdge Fair Q X4 X3 X2 t s =
      match t.observe with
      | .ret r => Q r s
      | .tau t' => fairStep ewp AccEdge Fair Q X4 X3 X2 t' s
      | .vis i k =>
        ewp.wp i
          (fun o s' => (AccEdge i o s s' ∧ X4 (k o) s') ∨
            (Fair i o s s' ∧ X3 (k o) s') ∨ (¬ Fair i o s s' ∧ X2 (k o) s')) s :=
  fairStepAux.eq_def ewp AccEdge Fair Q X4 X3 X2 t s

/-- Park induction principle for `fairStep`. -/
theorem fairStep.induct {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {X4 X3 X2 : ITree E R → S → Prop} (Pre : ITree E R → S → Prop)
    (h_closed : ∀ x s₀,
      (match x.observe with
       | .ret r => Q r s₀
       | .tau x' => Pre x' s₀
       | .vis i k =>
         ewp.wp i
           (fun o s' => (AccEdge i o s₀ s' ∧ X4 (k o) s') ∨
             (Fair i o s₀ s' ∧ X3 (k o) s') ∨ (¬ Fair i o s₀ s' ∧ X2 (k o) s')) s₀) →
      Pre x s₀)
    {t : ITree E R} {s : S} (h : fairStep ewp AccEdge Fair Q X4 X3 X2 t s) :
    Pre t s :=
  fairStepAux.induct ewp AccEdge Fair Q X4 X3 X2 s (fun x => Pre x s)
    (fun x hx => h_closed x s hx) t h

@[simp]
theorem fairStep.ret_iff (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (X4 X3 X2 : ITree E R → S → Prop) (r : R) (s : S) :
    fairStep ewp AccEdge Fair Q X4 X3 X2 (.ret r) s ↔ Q r s := by
  conv => lhs; rw [fairStep.unfold_eq, ITree.observe_ret]

@[simp]
theorem fairStep.tau_iff (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (X4 X3 X2 : ITree E R → S → Prop) (t : ITree E R) (s : S) :
    fairStep ewp AccEdge Fair Q X4 X3 X2 (.tau t) s ↔
      fairStep ewp AccEdge Fair Q X4 X3 X2 t s := by
  conv => lhs; rw [fairStep.unfold_eq, ITree.observe_tau]

@[simp]
theorem fairStep.vis_iff (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (X4 X3 X2 : ITree E R → S → Prop) (i : E.I) (k : E.O i → ITree E R)
    (s : S) :
    fairStep ewp AccEdge Fair Q X4 X3 X2 (.vis i k) s ↔
      ewp.wp i
        (fun o s' => (AccEdge i o s s' ∧ X4 (k o) s') ∨
          (Fair i o s s' ∧ X3 (k o) s') ∨ (¬ Fair i o s s' ∧ X2 (k o) s')) s := by
  conv => lhs; rw [fairStep.unfold_eq, ITree.observe_vis]

/-- Monotonicity of `fairStep` in its three continuations. -/
theorem fairStep.mono {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {X4 X4' X3 X3' X2 X2' : ITree E R → S → Prop} {t : ITree E R} {s : S}
    (h4 : ∀ x s', X4 x s' → X4' x s') (h3 : ∀ x s', X3 x s' → X3' x s')
    (h2 : ∀ x s', X2 x s' → X2' x s')
    (h : fairStep ewp AccEdge Fair Q X4 X3 X2 t s) :
    fairStep ewp AccEdge Fair Q X4' X3' X2' t s := by
  refine fairStep.induct
    (fun x s₀ => fairStep ewp AccEdge Fair Q X4' X3' X2' x s₀) ?_ h
  intro x s₀ hx
  rw [fairStep.unfold_eq]
  cases h_obs : x.observe <;> simp only [h_obs] at hx ⊢
  · exact hx
  · exact hx
  · exact ewp.mono
      (fun _ _ hp => hp.imp (And.imp id (h4 _ _))
        (Or.imp (And.imp id (h3 _ _)) (And.imp id (h2 _ _)))) hx

/-- `fairStep` is invariant backwards across finite `.tau` prefixes. -/
theorem fairStep.of_tauStar {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {X4 X3 X2 : ITree E R → S → Prop} {t u : ITree E R} {s : S}
    (h_tau : TauStar t u) (h : fairStep ewp AccEdge Fair Q X4 X3 X2 u s) :
    fairStep ewp AccEdge Fair Q X4 X3 X2 t s := by
  induction h_tau with
  | refl => exact h
  | step ht _ ih => rw [eq_tau_of_observe ht, fairStep.tau_iff]; exact ih h

/-- `fairStep` is monotone in `X2` for the `coinductive_fixpoint` order. -/
@[partial_fixpoint_monotone]
theorem fairStep.monotone_coind (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (X4 X3 : ITree E R → S → Prop)
    {α : Type _} [Lean.Order.PartialOrder α] (t : ITree E R) (s : S)
    (f : α → ITree E R → S → Lean.Order.ReverseImplicationOrder)
    (hf : Lean.Order.monotone f) :
    @Lean.Order.monotone _ _ _ Lean.Order.ReverseImplicationOrder.instOrder
      (fun x => fairStep ewp AccEdge Fair Q X4 X3 (f x) t s) :=
  fun x y hxy h =>
    fairStep.mono (fun _ _ h => h) (fun _ _ h => h)
      (fun t' s' hr => hf x y hxy t' s' hr) h

private def fairStallAux (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (X4 X3 : ITree E R → S → Prop) (t : ITree E R) (s : S) : Prop :=
  fairStep ewp AccEdge Fair Q X4 X3 (fairStallAux ewp AccEdge Fair Q X4 X3) t s
coinductive_fixpoint

/--
Level `ν X₂` (priority `2`) of the fairness game: unfair visible edges may be
taken forever.
-/
def fairStall (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (X4 X3 : ITree E R → S → Prop) (t : ITree E R) (s : S) : Prop :=
  fairStallAux ewp AccEdge Fair Q X4 X3 t s

theorem fairStall.unfold_eq (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (X4 X3 : ITree E R → S → Prop) (t : ITree E R) (s : S) :
    fairStall ewp AccEdge Fair Q X4 X3 t s =
      fairStep ewp AccEdge Fair Q X4 X3 (fairStall ewp AccEdge Fair Q X4 X3) t s :=
  fairStallAux.eq_def ewp AccEdge Fair Q X4 X3 t s

/-- Park coinduction principle for `fairStall`. -/
theorem fairStall.coinduct {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {X4 X3 : ITree E R → S → Prop} (Z : ITree E R → S → Prop)
    (h_step : ∀ x s₀, Z x s₀ → fairStep ewp AccEdge Fair Q X4 X3 Z x s₀)
    {t : ITree E R} {s : S} (h : Z t s) :
    fairStall ewp AccEdge Fair Q X4 X3 t s :=
  fairStallAux.coinduct ewp AccEdge Fair Q X4 X3 Z h_step t s h

/-- Monotonicity of `fairStall` in `X4` and `X3`. -/
theorem fairStall.mono {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {X4 X4' X3 X3' : ITree E R → S → Prop} {t : ITree E R} {s : S}
    (h4 : ∀ x s', X4 x s' → X4' x s') (h3 : ∀ x s', X3 x s' → X3' x s')
    (h : fairStall ewp AccEdge Fair Q X4 X3 t s) :
    fairStall ewp AccEdge Fair Q X4' X3' t s := by
  refine fairStall.coinduct
    (fun x s₀ => fairStall ewp AccEdge Fair Q X4 X3 x s₀) ?_ h
  intro x s₀ hx
  rw [fairStall.unfold_eq] at hx
  exact fairStep.mono h4 h3 (fun _ _ h => h) hx

/-- `fairStall` is monotone in `X3` for the `inductive_fixpoint` order. -/
@[partial_fixpoint_monotone]
theorem fairStall.monotone_ind (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (X4 : ITree E R → S → Prop)
    {α : Type _} [Lean.Order.PartialOrder α] (t : ITree E R) (s : S)
    (f : α → ITree E R → S → Lean.Order.ImplicationOrder)
    (hf : Lean.Order.monotone f) :
    @Lean.Order.monotone _ _ _ Lean.Order.ImplicationOrder.instOrder
      (fun x => fairStall ewp AccEdge Fair Q X4 (f x) t s) :=
  fun x y hxy h =>
    fairStall.mono (fun _ _ h => h) (fun t' s' hr => hf x y hxy t' s' hr) h

private def fairProgressAux (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (X4 : ITree E R → S → Prop) (t : ITree E R) (s : S) : Prop :=
  fairStall ewp AccEdge Fair Q X4 (fairProgressAux ewp AccEdge Fair Q X4) t s
inductive_fixpoint

/--
Level `μ X₃` (priority `3`) of the fairness game: only finitely many fair edges
may be taken before the next accepting edge (or a `Q`-return).
-/
def fairProgress (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (X4 : ITree E R → S → Prop) (t : ITree E R) (s : S) : Prop :=
  fairProgressAux ewp AccEdge Fair Q X4 t s

theorem fairProgress.unfold_eq (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (X4 : ITree E R → S → Prop) (t : ITree E R) (s : S) :
    fairProgress ewp AccEdge Fair Q X4 t s =
      fairStall ewp AccEdge Fair Q X4 (fairProgress ewp AccEdge Fair Q X4) t s :=
  fairProgressAux.eq_def ewp AccEdge Fair Q X4 t s

/-- Park induction principle for `fairProgress`. -/
theorem fairProgress.induct {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {X4 : ITree E R → S → Prop} (Pre : ITree E R → S → Prop)
    (h_closed : ∀ x s₀, fairStall ewp AccEdge Fair Q X4 Pre x s₀ → Pre x s₀)
    {t : ITree E R} {s : S} (h : fairProgress ewp AccEdge Fair Q X4 t s) :
    Pre t s :=
  fairProgressAux.induct ewp AccEdge Fair Q X4 Pre h_closed t s h

/-- Monotonicity of `fairProgress` in `X4`. -/
theorem fairProgress.mono {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {X4 X4' : ITree E R → S → Prop} {t : ITree E R} {s : S}
    (h4 : ∀ x s', X4 x s' → X4' x s')
    (h : fairProgress ewp AccEdge Fair Q X4 t s) :
    fairProgress ewp AccEdge Fair Q X4' t s := by
  refine fairProgress.induct
    (fun x s₀ => fairProgress ewp AccEdge Fair Q X4' x s₀) ?_ h
  intro x s₀ hx
  rw [fairProgress.unfold_eq]
  exact fairStall.mono h4 (fun _ _ h => h) hx

/-- `fairProgress` is monotone in `X4` for the `coinductive_fixpoint` order. -/
@[partial_fixpoint_monotone]
theorem fairProgress.monotone_coind (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    {α : Type _} [Lean.Order.PartialOrder α] (t : ITree E R) (s : S)
    (f : α → ITree E R → S → Lean.Order.ReverseImplicationOrder)
    (hf : Lean.Order.monotone f) :
    @Lean.Order.monotone _ _ _ Lean.Order.ReverseImplicationOrder.instOrder
      (fun x => fairProgress ewp AccEdge Fair Q (f x) t s) :=
  fun x y hxy h => fairProgress.mono (fun t' s' hr => hf x y hxy t' s' hr) h

/-- `fairProgress X4` is a fixed point of `Z ↦ fairStep X4 Z Z` (one direction). -/
theorem fairProgress.toFairStep {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {X4 : ITree E R → S → Prop} {t : ITree E R} {s : S}
    (h : fairProgress ewp AccEdge Fair Q X4 t s) :
    fairStep ewp AccEdge Fair Q X4 (fairProgress ewp AccEdge Fair Q X4)
      (fairProgress ewp AccEdge Fair Q X4) t s := by
  rw [fairProgress.unfold_eq, fairStall.unfold_eq] at h
  refine fairStep.mono (fun _ _ h => h) (fun _ _ h => h) ?_ h
  intro x s' hx
  rw [fairProgress.unfold_eq]; exact hx

/-- `fairProgress X4` is a fixed point of `Z ↦ fairStep X4 Z Z`. -/
theorem fairProgress.iff_fairStep (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (X4 : ITree E R → S → Prop) (t : ITree E R) (s : S) :
    fairProgress ewp AccEdge Fair Q X4 t s ↔
      fairStep ewp AccEdge Fair Q X4 (fairProgress ewp AccEdge Fair Q X4)
        (fairProgress ewp AccEdge Fair Q X4) t s := by
  refine ⟨fairProgress.toFairStep, fun h => ?_⟩
  rw [fairProgress.unfold_eq]
  refine fairStall.coinduct
    (fun x s₀ => fairStep ewp AccEdge Fair Q X4
      (fairProgress ewp AccEdge Fair Q X4)
      (fairProgress ewp AccEdge Fair Q X4) x s₀) ?_ h
  intro x s₀ hx
  exact fairStep.mono (fun _ _ h => h) (fun _ _ h => h)
    (fun _ _ hy => fairProgress.toFairStep hy) hx

/-- Total correctness implies `fairProgress` for any outer continuation. -/
theorem fairProgress.of_dwp {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    (X4 : ITree E R → S → Prop) {t : ITree E R} {s : S}
    (h : DWP ewp t Q s) : fairProgress ewp AccEdge Fair Q X4 t s := by
  refine DWP.induct
    (fun x s₀ => fairProgress ewp AccEdge Fair Q X4 x s₀) ?_ h
  intro x s₀ hx
  rw [fairProgress.iff_fairStep, fairStep.unfold_eq]
  cases h_obs : x.observe <;> simp only [h_obs] at hx ⊢
  · exact hx
  · exact fairProgress.toFairStep hx
  · refine ewp.mono (fun o s' hp => ?_) hx
    by_cases hf : Fair _ o s₀ s'
    · exact Or.inr (Or.inl ⟨hf, hp⟩)
    · exact Or.inr (Or.inr ⟨hf, hp⟩)

private def fairInfOftenAux (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (t : ITree E R) (s : S) : Prop :=
  fairProgress ewp AccEdge Fair Q (fairInfOftenAux ewp AccEdge Fair Q) t s
coinductive_fixpoint

/--
**Fairness-conditional Büchi recurrence** (Streett `□◇ Fair → □◇ AccEdge`): on
every path the tree returns `r` with `Q r s`, or takes accepting edges infinitely
often, or takes fair edges only finitely often while never silently diverging.
-/
def FairInfOften (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (t : ITree E R) (s : S) : Prop :=
  fairInfOftenAux ewp AccEdge Fair Q t s

theorem FairInfOften.unfold_eq (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (t : ITree E R) (s : S) :
    FairInfOften ewp AccEdge Fair Q t s =
      fairProgress ewp AccEdge Fair Q (FairInfOften ewp AccEdge Fair Q) t s :=
  fairInfOftenAux.eq_def ewp AccEdge Fair Q t s

/-- Park coinduction principle for the outer greatest fixed point of `FairInfOften`. -/
theorem FairInfOften.coinduct {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    (X : ITree E R → S → Prop)
    (h_step : ∀ x s₀, X x s₀ → fairProgress ewp AccEdge Fair Q X x s₀)
    {t : ITree E R} {s : S} (h : X t s) :
    FairInfOften ewp AccEdge Fair Q t s :=
  fairInfOftenAux.coinduct ewp AccEdge Fair Q X h_step t s h

/-- One-step characterisation of `FairInfOften` through `fairStep`. -/
theorem FairInfOften.iff_fairStep (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (t : ITree E R) (s : S) :
    FairInfOften ewp AccEdge Fair Q t s ↔
      fairStep ewp AccEdge Fair Q (FairInfOften ewp AccEdge Fair Q)
        (FairInfOften ewp AccEdge Fair Q) (FairInfOften ewp AccEdge Fair Q) t s := by
  constructor
  · intro h
    rw [FairInfOften.unfold_eq] at h
    refine fairStep.mono (fun _ _ h => h) ?_ ?_ (fairProgress.toFairStep h) <;>
    · intro x s' hx; rw [FairInfOften.unfold_eq]; exact hx
  · intro h
    rw [FairInfOften.unfold_eq, fairProgress.iff_fairStep]
    refine fairStep.mono (fun _ _ h => h) ?_ ?_ h <;>
    · intro x s' hx; rw [FairInfOften.unfold_eq] at hx; exact hx

@[simp]
theorem FairInfOften.ret_iff (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (r : R) (s : S) :
    FairInfOften ewp AccEdge Fair Q (.ret r) s ↔ Q r s := by
  rw [FairInfOften.iff_fairStep, fairStep.ret_iff]

@[simp]
theorem FairInfOften.tau_iff (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (t : ITree E R) (s : S) :
    FairInfOften ewp AccEdge Fair Q (.tau t) s ↔
      FairInfOften ewp AccEdge Fair Q t s := by
  rw [FairInfOften.iff_fairStep, fairStep.tau_iff, ← FairInfOften.iff_fairStep]

/--
`FairInfOften` is a fixed point of the one-step `DWLP` functor: Streett
acceptance is prefix-independent.
-/
@[simp]
theorem FairInfOften.vis_iff (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (i : E.I) (k : E.O i → ITree E R) (s : S) :
    FairInfOften ewp AccEdge Fair Q (.vis i k) s ↔
      ewp.wp i (fun o s' => FairInfOften ewp AccEdge Fair Q (k o) s') s := by
  rw [FairInfOften.iff_fairStep, fairStep.vis_iff]
  constructor
  · exact ewp.mono (fun _ _ hp =>
      hp.elim And.right (fun h => h.elim And.right And.right))
  · refine ewp.mono (fun o s' hp => ?_)
    by_cases hf : Fair i o s s'
    · exact Or.inr (Or.inl ⟨hf, hp⟩)
    · exact Or.inr (Or.inr ⟨hf, hp⟩)

theorem FairInfOften.ret {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {r : R} {s : S} (hq : Q r s) : FairInfOften ewp AccEdge Fair Q (.ret r) s :=
  (FairInfOften.ret_iff ewp AccEdge Fair Q r s).2 hq

theorem FairInfOften.tau {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t : ITree E R} {s : S} (h : FairInfOften ewp AccEdge Fair Q t s) :
    FairInfOften ewp AccEdge Fair Q (.tau t) s :=
  (FairInfOften.tau_iff ewp AccEdge Fair Q t s).2 h

theorem FairInfOften.vis {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {i : E.I} {k : E.O i → ITree E R} {s : S}
    (hv : ewp.wp i (fun o s' => FairInfOften ewp AccEdge Fair Q (k o) s') s) :
    FairInfOften ewp AccEdge Fair Q (.vis i k) s :=
  (FairInfOften.vis_iff ewp AccEdge Fair Q i k s).2 hv

/--
**Unconditional `spin` refutation** for fairness-conditional recurrence: silent
divergence is the program's fault, never the environment's.
-/
theorem not_fairInfOften_spin {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {s : S} :
    ¬ FairInfOften ewp AccEdge Fair Q (ITree.spin (E := E) (R := R)) s := by
  intro h
  refine fairStep.induct (fun x _ => x ≠ ITree.spin) ?_
    ((FairInfOften.iff_fairStep ewp AccEdge Fair Q _ s).1 h) rfl
  intro x _ hx rfl
  rw [observe_spin] at hx
  exact hx rfl

/-- Fairness-conditional recurrence implies partial correctness. -/
theorem FairInfOften.toDWLP {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t : ITree E R} {s : S} (h : FairInfOften ewp AccEdge Fair Q t s) :
    DWLP ewp t Q s := by
  refine DWLP.coinduct (fun x s₀ => FairInfOften ewp AccEdge Fair Q x s₀) ?_ h
  intro x s₀ hx
  cases h_obs : x.observe with
  | ret r => rw [eq_ret_of_observe h_obs, FairInfOften.ret_iff] at hx; exact hx
  | tau x' => rw [eq_tau_of_observe h_obs, FairInfOften.tau_iff] at hx; exact hx
  | vis i k => rw [eq_vis_of_observe h_obs, FairInfOften.vis_iff] at hx; exact hx

/-- Plain Büchi recurrence implies fairness-conditional recurrence. -/
theorem InfOften.toFairInfOften {ewp : StateEffectWP S E}
    {AccEdge : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    (Fair : (i : E.I) → E.O i → S → S → Prop) {t : ITree E R} {s : S}
    (h : InfOften ewp AccEdge Q t s) :
    FairInfOften ewp AccEdge Fair Q t s := by
  refine FairInfOften.coinduct (fun x s₀ => InfOften ewp AccEdge Q x s₀) ?_ h
  intro x s₀ hx
  refine buchiProgress.induct
    (fun y s₁ => fairProgress ewp AccEdge Fair Q (InfOften ewp AccEdge Q) y s₁)
    ?_ hx.toBuchiProgress
  intro y s₁ hy
  rw [fairProgress.iff_fairStep, fairStep.unfold_eq]
  cases h_obs : y.observe <;> simp only [h_obs] at hy ⊢
  · exact hy
  · exact fairProgress.toFairStep hy
  · refine ewp.mono (fun o s' hp => ?_) hy
    rcases hp with ha | hpre
    · exact Or.inl ha
    · by_cases hf : Fair _ o s₁ s'
      · exact Or.inr (Or.inl ⟨hf, hpre⟩)
      · exact Or.inr (Or.inr ⟨hf, hpre⟩)

/-- **`DWP` embedding** for fairness-conditional recurrence. -/
theorem fairInfOften_of_dwp {ewp : StateEffectWP S E}
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) {Q : R → S → Prop}
    {t : ITree E R} {s : S} (h : DWP ewp t Q s) :
    FairInfOften ewp AccEdge Fair Q t s :=
  (infOften_of_dwp AccEdge h).toFairInfOften Fair

/--
**Exact reduction (every edge fair).** When every edge is fair, the Streett
condition `□◇ Fair → □◇ AccEdge` is plain Büchi recurrence.
-/
theorem fairInfOften_true_iff_infOften (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (t : ITree E R) (s : S) :
    FairInfOften ewp AccEdge (fun _ _ _ _ => True) Q t s ↔
      InfOften ewp AccEdge Q t s := by
  refine ⟨fun h => ?_, InfOften.toFairInfOften _⟩
  refine InfOften.coinduct
    (fun x s₀ => FairInfOften ewp AccEdge (fun _ _ _ _ => True) Q x s₀) ?_ h
  intro x s₀ hx
  rw [FairInfOften.unfold_eq] at hx
  refine fairProgress.induct
    (fun y s₁ => buchiProgress ewp AccEdge Q
      (FairInfOften ewp AccEdge (fun _ _ _ _ => True) Q) y s₁) ?_ hx
  intro y s₁ hy
  rw [fairStall.unfold_eq] at hy
  refine fairStep.induct
    (fun z s₂ => buchiProgress ewp AccEdge Q
      (FairInfOften ewp AccEdge (fun _ _ _ _ => True) Q) z s₂) ?_ hy
  intro z s₂ hz
  rw [buchiProgress.unfold_eq]
  cases h_obs : z.observe <;> simp only [h_obs] at hz ⊢
  · exact hz
  · exact hz
  · exact ewp.mono
      (fun _ _ hp => hp.elim Or.inl
        (fun h => h.elim (fun hf => Or.inr hf.2) (fun hn => (hn.1 trivial).elim)))
      hz

/--
**Exact reduction (no edge fair).** When no edge is fair, the Streett
condition only rules out silent divergence: `FairInfOften` is Büchi recurrence
of *all* visible edges (reactive productivity plus partial correctness).
-/
theorem fairInfOften_false_iff (ewp : StateEffectWP S E)
    (AccEdge : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (t : ITree E R) (s : S) :
    FairInfOften ewp AccEdge (fun _ _ _ _ => False) Q t s ↔
      InfOften ewp (fun _ _ _ _ => True) Q t s := by
  constructor
  · intro h
    refine InfOften.coinduct
      (fun x s₀ => FairInfOften ewp AccEdge (fun _ _ _ _ => False) Q x s₀) ?_ h
    intro x s₀ hx
    rw [FairInfOften.iff_fairStep] at hx
    refine fairStep.induct
      (fun z s₂ => buchiProgress ewp (fun _ _ _ _ => True) Q
        (FairInfOften ewp AccEdge (fun _ _ _ _ => False) Q) z s₂) ?_ hx
    intro z s₂ hz
    rw [buchiProgress.unfold_eq]
    cases h_obs : z.observe <;> simp only [h_obs] at hz ⊢
    · exact hz
    · exact hz
    · exact ewp.mono
        (fun _ _ hp => Or.inl ⟨trivial, hp.elim And.right
          (fun h => h.elim (fun hf => hf.1.elim) And.right)⟩) hz
  · intro h
    refine FairInfOften.coinduct
      (fun x s₀ => InfOften ewp (fun _ _ _ _ => True) Q x s₀) ?_ h
    intro x s₀ hx
    rw [fairProgress.unfold_eq]
    refine fairStall.coinduct
      (fun y s₁ => InfOften ewp (fun _ _ _ _ => True) Q y s₁) ?_ hx
    intro y s₁ hy
    refine InfOften.progress_induct
      (fun z s₂ => fairStep ewp AccEdge (fun _ _ _ _ => False) Q
        (InfOften ewp (fun _ _ _ _ => True) Q)
        (fairProgress ewp AccEdge (fun _ _ _ _ => False) Q
          (InfOften ewp (fun _ _ _ _ => True) Q))
        (InfOften ewp (fun _ _ _ _ => True) Q) z s₂) ?_ hy
    intro z s₂ hz
    rw [fairStep.unfold_eq]
    cases h_obs : z.observe <;> simp only [h_obs] at hz ⊢
    · exact hz
    · exact hz.2
    · exact ewp.mono (fun _ _ hp => Or.inr (Or.inr ⟨id, hp.1⟩)) hz

/--
Monotonicity of `FairInfOften`: weaker accepting edges, *fewer* fair edges and a
weaker postcondition.
-/
theorem FairInfOften.mono {ewp : StateEffectWP S E}
    {AccEdge AccEdge' Fair Fair' : (i : E.I) → E.O i → S → S → Prop}
    {P Q : R → S → Prop} {t : ITree E R} {s : S}
    (h_acc : ∀ i o s₀ s', AccEdge i o s₀ s' → AccEdge' i o s₀ s')
    (h_fair : ∀ i o s₀ s', Fair' i o s₀ s' → Fair i o s₀ s')
    (h_post : ∀ r s', P r s' → Q r s')
    (h : FairInfOften ewp AccEdge Fair P t s) :
    FairInfOften ewp AccEdge' Fair' Q t s := by
  refine FairInfOften.coinduct
    (fun x s₀ => FairInfOften ewp AccEdge Fair P x s₀) ?_ h
  intro x s₀ hx
  rw [FairInfOften.unfold_eq] at hx
  refine fairProgress.induct
    (fun y s₁ => fairProgress ewp AccEdge' Fair' Q
      (FairInfOften ewp AccEdge Fair P) y s₁) ?_ hx
  intro y s₁ hy
  rw [fairProgress.unfold_eq]
  refine fairStall.coinduct
    (fun z s₂ => fairStall ewp AccEdge Fair P (FairInfOften ewp AccEdge Fair P)
        (fun w s₃ => fairProgress ewp AccEdge' Fair' Q
          (FairInfOften ewp AccEdge Fair P) w s₃) z s₂ ∨
      fairProgress ewp AccEdge' Fair' Q (FairInfOften ewp AccEdge Fair P) z s₂)
    ?_ (Or.inl hy)
  rintro z s₂ (hz | hz)
  · rw [fairStall.unfold_eq] at hz
    refine fairStep.induct
      (fun w s₃ => fairStep ewp AccEdge' Fair' Q (FairInfOften ewp AccEdge Fair P)
        (fairProgress ewp AccEdge' Fair' Q (FairInfOften ewp AccEdge Fair P))
        (fun v s₄ => fairStall ewp AccEdge Fair P (FairInfOften ewp AccEdge Fair P)
            (fun w s₃ => fairProgress ewp AccEdge' Fair' Q
              (FairInfOften ewp AccEdge Fair P) w s₃) v s₄ ∨
          fairProgress ewp AccEdge' Fair' Q (FairInfOften ewp AccEdge Fair P) v s₄)
        w s₃) ?_ hz
    intro w s₃ hw
    rw [fairStep.unfold_eq]
    cases h_obs : w.observe <;> simp only [h_obs] at hw ⊢
    · exact h_post _ _ hw
    · exact hw
    · refine ewp.mono (fun o s' hp => ?_) hw
      rcases hp with ⟨ha, hfi⟩ | ⟨_, hpre⟩ | ⟨hnf, hst⟩
      · exact Or.inl ⟨h_acc _ _ _ _ ha, hfi⟩
      · by_cases hf' : Fair' _ o s₃ s'
        · exact Or.inr (Or.inl ⟨hf', hpre⟩)
        · exact Or.inr (Or.inr ⟨hf', Or.inr hpre⟩)
      · exact Or.inr (Or.inr ⟨fun hf' => hnf (h_fair _ _ _ _ hf'), Or.inl hst⟩)
  · exact fairStep.mono (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => Or.inr h)
      (fairProgress.toFairStep hz)

/--
**Compositionality** (general prefix): a fairness-recurrent prefix whose
returns land in fairness-recurrent continuations sequences into a
fairness-recurrent tree.
-/
theorem FairInfOften.bind {A B : Type u} {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : B → S → Prop}
    {t : ITree E A} {k : A → ITree E B} {s : S}
    (h : FairInfOften ewp AccEdge Fair
      (fun a s' => FairInfOften ewp AccEdge Fair Q (k a) s') t s) :
    FairInfOften ewp AccEdge Fair Q (t >>= k) s := by
  let FIk : A → S → Prop := fun a s' => FairInfOften ewp AccEdge Fair Q (k a) s'
  let X : ITree E B → S → Prop := fun u s₀ =>
    FairInfOften ewp AccEdge Fair Q u s₀ ∨
      ∃ t₀ : ITree E A, u = (t₀ >>= k) ∧ FairInfOften ewp AccEdge Fair FIk t₀ s₀
  have h_fi_x : ∀ u s₀, FairInfOften ewp AccEdge Fair Q u s₀ → X u s₀ :=
    fun _ _ hu => Or.inl hu
  refine FairInfOften.coinduct X ?_ (Or.inr ⟨t, rfl, h⟩)
  rintro u s₀ (hu | ⟨t₀, rfl, ht₀⟩)
  · rw [FairInfOften.unfold_eq] at hu
    exact fairProgress.mono h_fi_x hu
  · rw [FairInfOften.unfold_eq] at ht₀
    refine fairProgress.induct
      (fun t₁ s₁ => fairProgress ewp AccEdge Fair Q X (t₁ >>= k) s₁) ?_ ht₀
    intro t₁ s₁ ht₁
    rw [fairProgress.unfold_eq]
    refine fairStall.coinduct
      (fun u s₂ => (∃ t₂ : ITree E A, u = (t₂ >>= k) ∧
          fairStall ewp AccEdge Fair FIk (FairInfOften ewp AccEdge Fair FIk)
            (fun t₃ s₃ => fairProgress ewp AccEdge Fair Q X (t₃ >>= k) s₃) t₂ s₂) ∨
        fairProgress ewp AccEdge Fair Q X u s₂) ?_ (Or.inl ⟨t₁, rfl, ht₁⟩)
    rintro u s₂ (⟨t₂, rfl, ht₂⟩ | hu)
    · rw [fairStall.unfold_eq] at ht₂
      refine fairStep.induct
        (fun t₃ s₃ => fairStep ewp AccEdge Fair Q X
          (fairProgress ewp AccEdge Fair Q X)
          (fun u s₄ => (∃ t₂ : ITree E A, u = (t₂ >>= k) ∧
              fairStall ewp AccEdge Fair FIk (FairInfOften ewp AccEdge Fair FIk)
                (fun t₃ s₃ => fairProgress ewp AccEdge Fair Q X (t₃ >>= k) s₃)
                t₂ s₄) ∨
            fairProgress ewp AccEdge Fair Q X u s₄) (t₃ >>= k) s₃) ?_ ht₂
      intro t₃ s₃ ht₃
      cases h_obs : t₃.observe with
      | ret a =>
        simp only [h_obs] at ht₃
        rw [eq_ret_of_observe h_obs, ret_bind]
        have hk := (FairInfOften.iff_fairStep ewp AccEdge Fair Q (k a) s₃).1 ht₃
        refine fairStep.mono (fun _ _ h => Or.inl h) ?_ ?_ hk
        · intro x s' hx
          rw [FairInfOften.unfold_eq] at hx
          exact fairProgress.mono h_fi_x hx
        · intro x s' hx
          rw [FairInfOften.unfold_eq] at hx
          exact Or.inr (fairProgress.mono h_fi_x hx)
      | tau t₃' =>
        simp only [h_obs] at ht₃
        rw [eq_tau_of_observe h_obs, tau_bind, fairStep.tau_iff]
        exact ht₃
      | vis i c =>
        simp only [h_obs] at ht₃
        rw [eq_vis_of_observe h_obs, vis_bind, fairStep.vis_iff]
        refine ewp.mono (fun o s' hp => ?_) ht₃
        rcases hp with ⟨ha, hfi⟩ | ⟨hf, hpre⟩ | ⟨hnf, hst⟩
        · exact Or.inl ⟨ha, Or.inr ⟨c o, rfl, hfi⟩⟩
        · exact Or.inr (Or.inl ⟨hf, hpre⟩)
        · exact Or.inr (Or.inr ⟨hnf, Or.inl ⟨c o, rfl, hst⟩⟩)
    · exact fairStep.mono (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => Or.inr h)
        (fairProgress.toFairStep hu)

/-- **Compositionality** (`DWP` prefix followed by a fairness-recurrent continuation). -/
theorem FairInfOften.bind_dwp {A B : Type u} {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : B → S → Prop}
    {t : ITree E A} {k : A → ITree E B} {s : S}
    (h : DWP ewp t (fun a s' => FairInfOften ewp AccEdge Fair Q (k a) s') s) :
    FairInfOften ewp AccEdge Fair Q (t >>= k) s :=
  FairInfOften.bind (fairInfOften_of_dwp AccEdge Fair h)

/-- Conditional branching rule for `FairInfOften`. -/
theorem FairInfOften.ite {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {c : Prop} [Decidable c] {t₁ t₂ : ITree E R} {s : S}
    (h₁ : c → FairInfOften ewp AccEdge Fair Q t₁ s)
    (h₂ : ¬ c → FairInfOften ewp AccEdge Fair Q t₂ s) :
    FairInfOften ewp AccEdge Fair Q (if c then t₁ else t₂) s := by
  split
  · exact h₁ ‹_›
  · exact h₂ ‹_›

/-- `Sum`-branching rule for `FairInfOften`. -/
theorem FairInfOften.sum_elim {A B : Type u} {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {f : A → ITree E R} {g : B → ITree E R} {s : S} (x : A ⊕ B)
    (h₁ : ∀ a, x = .inl a → FairInfOften ewp AccEdge Fair Q (f a) s)
    (h₂ : ∀ b, x = .inr b → FairInfOften ewp AccEdge Fair Q (g b) s) :
    FairInfOften ewp AccEdge Fair Q (Sum.elim f g x) s := by
  cases x with
  | inl a => exact h₁ a rfl
  | inr b => exact h₂ b rfl

/-- Postcondition weakening for `FairInfOften`. -/
theorem FairInfOften.mono_post {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {P Q : R → S → Prop}
    {t : ITree E R} {s : S} (h_post : ∀ r s', P r s' → Q r s')
    (h : FairInfOften ewp AccEdge Fair P t s) :
    FairInfOften ewp AccEdge Fair Q t s :=
  FairInfOften.mono (fun _ _ _ _ ha => ha) (fun _ _ _ _ hf => hf) h_post h

/-- Monotonicity of `FairInfOften` in the effect transformer. -/
theorem FairInfOften.mono_wp {ewp ewp' : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t : ITree E R} {s : S}
    (h_wp : ∀ (i : E.I) (K : E.O i → S → Prop) (s₀ : S),
      ewp.wp i K s₀ → ewp'.wp i K s₀)
    (h : FairInfOften ewp AccEdge Fair Q t s) :
    FairInfOften ewp' AccEdge Fair Q t s := by
  refine FairInfOften.coinduct
    (fun x s₀ => FairInfOften ewp AccEdge Fair Q x s₀) ?_ h
  intro x s₀ hx
  rw [FairInfOften.unfold_eq] at hx
  refine fairProgress.induct
    (fun y s₁ => fairProgress ewp' AccEdge Fair Q
      (FairInfOften ewp AccEdge Fair Q) y s₁) ?_ hx
  intro y s₁ hy
  rw [fairProgress.unfold_eq]
  refine fairStall.coinduct
    (fun z s₂ => fairStall ewp AccEdge Fair Q (FairInfOften ewp AccEdge Fair Q)
      (fun w s₃ => fairProgress ewp' AccEdge Fair Q
        (FairInfOften ewp AccEdge Fair Q) w s₃) z s₂) ?_ hy
  intro z s₂ hz
  rw [fairStall.unfold_eq] at hz
  refine fairStep.induct
    (fun w s₃ => fairStep ewp' AccEdge Fair Q (FairInfOften ewp AccEdge Fair Q)
      (fairProgress ewp' AccEdge Fair Q (FairInfOften ewp AccEdge Fair Q))
      (fun v s₄ => fairStall ewp AccEdge Fair Q (FairInfOften ewp AccEdge Fair Q)
        (fun w s₃ => fairProgress ewp' AccEdge Fair Q
          (FairInfOften ewp AccEdge Fair Q) w s₃) v s₄) w s₃) ?_ hz
  intro w s₃ hw
  rw [fairStep.unfold_eq]
  cases h_obs : w.observe <;> simp only [h_obs] at hw ⊢
  · exact hw
  · exact hw
  · exact h_wp _ _ _ hw

/-- Folding `fairStall` over `FairInfOften` back into `FairInfOften`. -/
theorem fairStall_to_fairInfOften {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t : ITree E R} {s : S}
    (h : fairStall ewp AccEdge Fair Q (FairInfOften ewp AccEdge Fair Q)
      (FairInfOften ewp AccEdge Fair Q) t s) :
    FairInfOften ewp AccEdge Fair Q t s := by
  rw [FairInfOften.unfold_eq, fairProgress.unfold_eq]
  exact fairStall.mono (fun _ _ hx => hx)
    (fun _ _ hx => by rw [FairInfOften.unfold_eq] at hx; exact hx) h

/-- `FairInfOften` is stable forward across finite `.tau` prefixes. -/
theorem FairInfOften.tauStar {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t u : ITree E R} {s : S}
    (h_tau : TauStar t u) (h : FairInfOften ewp AccEdge Fair Q t s) :
    FairInfOften ewp AccEdge Fair Q u s := by
  induction h_tau with
  | refl => exact h
  | step ht _ ih => rw [eq_tau_of_observe ht, FairInfOften.tau_iff] at h; exact ih h

/-- `FairInfOften` is invariant backwards across finite `.tau` prefixes. -/
theorem FairInfOften.of_tauStar {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t u : ITree E R} {s : S}
    (h_tau : TauStar t u) (h : FairInfOften ewp AccEdge Fair Q u s) :
    FairInfOften ewp AccEdge Fair Q t s := by
  induction h_tau with
  | refl => exact h
  | step ht _ ih => rw [eq_tau_of_observe ht, FairInfOften.tau_iff]; exact ih h

/-- `FairInfOften` respects equivalence up to finite `.tau`s (`Eutt`). -/
theorem FairInfOften.eutt {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t u : ITree E R} {s : S} (he : Eutt t u)
    (h : FairInfOften ewp AccEdge Fair Q t s) :
    FairInfOften ewp AccEdge Fair Q u s := by
  let X : ITree E R → S → Prop := fun u₀ s₀ =>
    ∃ t₀, Eutt t₀ u₀ ∧ FairInfOften ewp AccEdge Fair Q t₀ s₀
  refine FairInfOften.coinduct X ?_ ⟨t, he, h⟩
  rintro u₀ s₀ ⟨t₀, h_eu, ht₀⟩
  rw [FairInfOften.unfold_eq] at ht₀
  refine fairProgress.induct
    (fun x s₁ => ∀ u₁, Eutt x u₁ → fairProgress ewp AccEdge Fair Q X u₁ s₁)
    ?_ ht₀ u₀ h_eu
  intro x s₁ hx u₁ h_eu₁
  rw [fairProgress.unfold_eq]
  let Z : ITree E R → S → Prop := fun u₂ s₂ =>
    ∃ y, Eutt y u₂ ∧ fairStall ewp AccEdge Fair Q
      (FairInfOften ewp AccEdge Fair Q)
      (fun v s₃ => ∀ u₃, Eutt v u₃ → fairProgress ewp AccEdge Fair Q X u₃ s₃) y s₂
  refine fairStall.coinduct Z ?_ ⟨x, h_eu₁, hx⟩
  rintro u₂ s₂ ⟨y, h_ey, hy⟩
  rw [fairStall.unfold_eq] at hy
  refine fairStep.induct
    (fun z s₃ => ∀ u₃, Eutt z u₃ →
      fairStep ewp AccEdge Fair Q X (fairProgress ewp AccEdge Fair Q X) Z u₃ s₃)
    ?_ hy u₂ h_ey
  intro z s₃ hz u₃ h_ez
  cases h_obs : z.observe with
  | ret r =>
    simp only [h_obs] at hz
    obtain ⟨u', hu, hur⟩ := eutt_inv_ret h_ez h_obs
    exact fairStep.of_tauStar hu
      (by rw [eq_ret_of_observe hur, fairStep.ret_iff]; exact hz)
  | tau z' =>
    simp only [h_obs] at hz
    rcases eutt_inv_tau h_ez h_obs with h' | ⟨u', hu, h'⟩
    · exact hz u₃ h'
    · rw [eq_tau_of_observe hu, fairStep.tau_iff]; exact hz u' h'
  | vis i k =>
    simp only [h_obs] at hz
    obtain ⟨u', k₂, hu, huv, hk⟩ := eutt_inv_vis h_ez h_obs
    refine fairStep.of_tauStar hu ?_
    rw [eq_vis_of_observe huv, fairStep.vis_iff]
    refine ewp.mono (fun o s' hp => ?_) hz
    rcases hp with ⟨ha, hfi⟩ | ⟨hf, hpre⟩ | ⟨hnf, hst⟩
    · exact Or.inl ⟨ha, k o, hk o, hfi⟩
    · exact Or.inr (Or.inl ⟨hf, hpre (k₂ o) (hk o)⟩)
    · exact Or.inr (Or.inr ⟨hnf, k o, hk o, hst⟩)

/-- `Eutt`-equivalent trees satisfy the exact same `FairInfOften` specs. -/
theorem FairInfOften.eutt_iff (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    {t u : ITree E R} (he : Eutt t u) (s : S) :
    FairInfOften ewp AccEdge Fair Q t s ↔ FairInfOften ewp AccEdge Fair Q u s :=
  ⟨FairInfOften.eutt he, FairInfOften.eutt he.symm⟩

/-- Exact monadic bind characterisation for `FairInfOften`. -/
theorem FairInfOften.bind_iff {A B : Type u} (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop) (Q : B → S → Prop)
    (t : ITree E A) (k : A → ITree E B) (s : S) :
    FairInfOften ewp AccEdge Fair Q (t >>= k) s ↔
      FairInfOften ewp AccEdge Fair
        (fun a s' => FairInfOften ewp AccEdge Fair Q (k a) s') t s := by
  refine ⟨fun h => ?_, FairInfOften.bind⟩
  let FIk : A → S → Prop := fun a s' => FairInfOften ewp AccEdge Fair Q (k a) s'
  let X : ITree E A → S → Prop := fun t₀ s₀ => FairInfOften ewp AccEdge Fair Q (t₀ >>= k) s₀
  refine FairInfOften.coinduct X ?_ h
  intro t₀ s₀ ht₀
  dsimp only [X] at ht₀
  rw [FairInfOften.unfold_eq] at ht₀
  let Pre : ITree E B → S → Prop := fun u s₁ =>
    FairInfOften ewp AccEdge Fair Q u s₁ ∧
      ∀ t₁ : ITree E A, u = (t₁ >>= k) → fairProgress ewp AccEdge Fair FIk X t₁ s₁
  refine (fairProgress.induct Pre ?_ ht₀).2 t₀ rfl
  intro u s₁ hu
  have hfi_u : FairInfOften ewp AccEdge Fair Q u s₁ :=
    fairStall_to_fairInfOften (fairStall.mono (fun _ _ hx => hx) (fun _ _ hp => hp.1) hu)
  refine ⟨hfi_u, fun t₁ h_eq => ?_⟩
  subst h_eq
  rw [fairProgress.unfold_eq]
  let Z : ITree E A → S → Prop := fun t₂ s₂ =>
    fairStall ewp AccEdge Fair Q (FairInfOften ewp AccEdge Fair Q) Pre (t₂ >>= k) s₂
  refine fairStall.coinduct Z ?_ hu
  intro t₂ s₂ hz
  dsimp only [Z] at hz
  rw [fairStall.unfold_eq] at hz
  refine (fairStep.induct
    (fun v s₃ => FairInfOften ewp AccEdge Fair Q v s₃ ∧
      ∀ t₃ : ITree E A, v = (t₃ >>= k) →
        fairStep ewp AccEdge Fair FIk X (fairProgress ewp AccEdge Fair FIk X) Z t₃ s₃)
    ?_ hz).2 t₂ rfl
  intro v s₃ hv
  have hfi_v : FairInfOften ewp AccEdge Fair Q v s₃ := by
    rw [FairInfOften.iff_fairStep, fairStep.unfold_eq]
    cases h_obs : v.observe <;> simp only [h_obs] at hv ⊢
    · exact hv
    · exact (FairInfOften.iff_fairStep _ _ _ _ _ _).1 hv.1
    · refine ewp.mono (fun _ _ hp => ?_) hv
      rcases hp with ⟨ha, hfi⟩ | ⟨hf, hpre⟩ | ⟨hnf, hst⟩
      · exact Or.inl ⟨ha, hfi⟩
      · exact Or.inr (Or.inl ⟨hf, hpre.1⟩)
      · exact Or.inr (Or.inr ⟨hnf,
          fairStall_to_fairInfOften
            (fairStall.mono (fun _ _ hx => hx) (fun _ _ hp => hp.1) hst)⟩)
  refine ⟨hfi_v, fun t₃ h_eq₃ => ?_⟩
  subst h_eq₃
  cases h_obs : t₃.observe with
  | ret a =>
    rw [eq_ret_of_observe h_obs, ret_bind] at hfi_v
    rw [eq_ret_of_observe h_obs, fairStep.ret_iff]; exact hfi_v
  | tau t₃' =>
    rw [eq_tau_of_observe h_obs, tau_bind, ITree.observe_tau] at hv
    rw [eq_tau_of_observe h_obs, fairStep.tau_iff]; exact hv.2 t₃' rfl
  | vis i c =>
    rw [eq_vis_of_observe h_obs, vis_bind, ITree.observe_vis] at hv
    rw [eq_vis_of_observe h_obs, fairStep.vis_iff]
    refine ewp.mono (fun o s' hp => ?_) hv
    rcases hp with ⟨ha, hfi⟩ | ⟨hf, hpre⟩ | ⟨hnf, hst⟩
    · exact Or.inl ⟨ha, hfi⟩
    · exact Or.inr (Or.inl ⟨hf, hpre.2 (c o) rfl⟩)
    · exact Or.inr (Or.inr ⟨hnf, hst⟩)

/-- Postcondition conjunction for `FairInfOften` under `[Conjunctive ewp]`. -/
theorem FairInfOften.conj {ewp : StateEffectWP S E}
    [h_conj : StateEffectWP.Conjunctive ewp]
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop}
    {P Q : R → S → Prop} {t : ITree E R} {s : S}
    (hp : FairInfOften ewp AccEdge Fair P t s)
    (hq : FairInfOften ewp AccEdge Fair Q t s) :
    FairInfOften ewp AccEdge Fair (fun r s' => P r s' ∧ Q r s') t s := by
  let X : ITree E R → S → Prop := fun x s₀ =>
    FairInfOften ewp AccEdge Fair P x s₀ ∧ FairInfOften ewp AccEdge Fair Q x s₀
  refine FairInfOften.coinduct X ?_ ⟨hp, hq⟩
  rintro x s₀ ⟨hpx, hqx⟩
  rw [FairInfOften.unfold_eq] at hpx
  refine fairProgress.induct
    (fun y s₁ => FairInfOften ewp AccEdge Fair Q y s₁ →
      fairProgress ewp AccEdge Fair (fun r s' => P r s' ∧ Q r s') X y s₁)
    ?_ hpx hqx
  intro y s₁ hy hqy
  rw [fairProgress.unfold_eq]
  let Z : ITree E R → S → Prop := fun z s₂ =>
    fairStall ewp AccEdge Fair P (FairInfOften ewp AccEdge Fair P)
      (fun v s₃ => FairInfOften ewp AccEdge Fair Q v s₃ →
        fairProgress ewp AccEdge Fair (fun r s' => P r s' ∧ Q r s') X v s₃) z s₂ ∧
      FairInfOften ewp AccEdge Fair Q z s₂
  refine fairStall.coinduct Z ?_ ⟨hy, hqy⟩
  rintro z s₂ ⟨hz, hqz⟩
  rw [fairStall.unfold_eq] at hz
  refine fairStep.induct
    (fun w s₃ => FairInfOften ewp AccEdge Fair Q w s₃ →
      fairStep ewp AccEdge Fair (fun r s' => P r s' ∧ Q r s') X
        (fairProgress ewp AccEdge Fair (fun r s' => P r s' ∧ Q r s') X) Z w s₃)
    ?_ hz hqz
  intro w s₃ hw hqw
  rw [fairStep.unfold_eq]
  cases h_obs : w.observe with
  | ret r =>
    simp only [h_obs] at hw ⊢
    rw [eq_ret_of_observe h_obs, FairInfOften.ret_iff] at hqw
    exact ⟨hw, hqw⟩
  | tau w' =>
    simp only [h_obs] at hw ⊢
    rw [eq_tau_of_observe h_obs, FairInfOften.tau_iff] at hqw
    exact hw hqw
  | vis i k =>
    simp only [h_obs] at hw ⊢
    rw [eq_vis_of_observe h_obs, FairInfOften.vis_iff] at hqw
    refine ewp.mono (fun _ _ ⟨hp_b, hq_b⟩ => ?_) (h_conj.conj hw hqw)
    rcases hp_b with ⟨ha, hfi⟩ | ⟨hf, hpre⟩ | ⟨hnf, hst⟩
    · exact Or.inl ⟨ha, hfi, hq_b⟩
    · exact Or.inr (Or.inl ⟨hf, hpre hq_b⟩)
    · exact Or.inr (Or.inr ⟨hnf, hst, hq_b⟩)

/-- Under `[Conjunctive ewp]`, merge `Always` safety into `FairInfOften` over `guardInvWP`. -/
theorem FairInfOften.guardInv_of_always {ewp : StateEffectWP S E}
    [h_conj : StateEffectWP.Conjunctive ewp]
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Inv : S → Prop}
    {P Q : R → S → Prop} {t : ITree E R} {s : S}
    (h_safe : Always ewp Inv P t s) (h : FairInfOften ewp AccEdge Fair Q t s) :
    FairInfOften (guardInvWP ewp Inv) AccEdge Fair Q t s := by
  let X : ITree E R → S → Prop := fun x s₀ =>
    Always ewp Inv P x s₀ ∧ FairInfOften ewp AccEdge Fair Q x s₀
  refine FairInfOften.coinduct X ?_ ⟨h_safe, h⟩
  rintro x s₀ ⟨hax, hfx⟩
  rw [FairInfOften.unfold_eq] at hfx
  refine fairProgress.induct
    (fun y s₁ => Always ewp Inv P y s₁ →
      fairProgress (guardInvWP ewp Inv) AccEdge Fair Q X y s₁) ?_ hfx hax
  intro y s₁ hy hay
  rw [fairProgress.unfold_eq]
  let Z : ITree E R → S → Prop := fun z s₂ =>
    fairStall ewp AccEdge Fair Q (FairInfOften ewp AccEdge Fair Q)
      (fun v s₃ => Always ewp Inv P v s₃ →
        fairProgress (guardInvWP ewp Inv) AccEdge Fair Q X v s₃) z s₂ ∧
      Always ewp Inv P z s₂
  refine fairStall.coinduct Z ?_ ⟨hy, hay⟩
  rintro z s₂ ⟨hz, haz⟩
  rw [fairStall.unfold_eq] at hz
  refine fairStep.induct
    (fun w s₃ => Always ewp Inv P w s₃ →
      fairStep (guardInvWP ewp Inv) AccEdge Fair Q X
        (fairProgress (guardInvWP ewp Inv) AccEdge Fair Q X) Z w s₃)
    ?_ hz haz
  intro w s₃ hw haw
  rw [fairStep.unfold_eq]
  rw [Always.unfold_eq] at haw
  obtain ⟨_, haw⟩ := haw
  cases h_obs : w.observe <;> simp only [h_obs] at hw haw ⊢
  · exact hw
  · exact hw haw
  · refine ewp.mono (fun _ _ ⟨hp_b, ha_b⟩ => ⟨ha_b.inv, ?_⟩) (h_conj.conj hw haw)
    rcases hp_b with ⟨ha, hfi⟩ | ⟨hf, hpre⟩ | ⟨hnf, hst⟩
    · exact Or.inl ⟨ha, ha_b, hfi⟩
    · exact Or.inr (Or.inl ⟨hf, hpre ha_b⟩)
    · exact Or.inr (Or.inr ⟨hnf, hst, ha_b⟩)

/-- Under `[Conjunctive ewp]`, merge `AlwaysStep` into `FairInfOften` over `guardStepWP`. -/
theorem FairInfOften.guardStep_of_alwaysStep {ewp : StateEffectWP S E}
    [h_conj : StateEffectWP.Conjunctive ewp]
    {AccEdge Fair StepRel : (i : E.I) → E.O i → S → S → Prop}
    {P Q : R → S → Prop} {t : ITree E R} {s : S}
    (h_safe : AlwaysStep ewp StepRel P t s)
    (h : FairInfOften ewp AccEdge Fair Q t s) :
    FairInfOften (guardStepWP ewp StepRel) AccEdge Fair Q t s := by
  let X : ITree E R → S → Prop := fun x s₀ =>
    AlwaysStep ewp StepRel P x s₀ ∧ FairInfOften ewp AccEdge Fair Q x s₀
  refine FairInfOften.coinduct X ?_ ⟨h_safe, h⟩
  rintro x s₀ ⟨hsx, hfx⟩
  rw [FairInfOften.unfold_eq] at hfx
  refine fairProgress.induct
    (fun y s₁ => AlwaysStep ewp StepRel P y s₁ →
      fairProgress (guardStepWP ewp StepRel) AccEdge Fair Q X y s₁) ?_ hfx hsx
  intro y s₁ hy hsy
  rw [fairProgress.unfold_eq]
  let Z : ITree E R → S → Prop := fun z s₂ =>
    fairStall ewp AccEdge Fair Q (FairInfOften ewp AccEdge Fair Q)
      (fun v s₃ => AlwaysStep ewp StepRel P v s₃ →
        fairProgress (guardStepWP ewp StepRel) AccEdge Fair Q X v s₃) z s₂ ∧
      AlwaysStep ewp StepRel P z s₂
  refine fairStall.coinduct Z ?_ ⟨hy, hsy⟩
  rintro z s₂ ⟨hz, hsz⟩
  rw [fairStall.unfold_eq] at hz
  refine fairStep.induct
    (fun w s₃ => AlwaysStep ewp StepRel P w s₃ →
      fairStep (guardStepWP ewp StepRel) AccEdge Fair Q X
        (fairProgress (guardStepWP ewp StepRel) AccEdge Fair Q X) Z w s₃)
    ?_ hz hsz
  intro w s₃ hw hsw
  rw [fairStep.unfold_eq]
  rw [AlwaysStep.unfold_eq] at hsw
  cases h_obs : w.observe <;> simp only [h_obs] at hw hsw ⊢
  · exact hw
  · exact hw hsw
  · refine ewp.mono (fun _ _ ⟨hp_b, hsr, hs_b⟩ => ⟨hsr, ?_⟩) (h_conj.conj hw hsw)
    rcases hp_b with ⟨ha, hfi⟩ | ⟨hf, hpre⟩ | ⟨hnf, hst⟩
    · exact Or.inl ⟨ha, hs_b, hfi⟩
    · exact Or.inr (Or.inl ⟨hf, hpre hs_b⟩)
    · exact Or.inr (Or.inr ⟨hnf, hst, hs_b⟩)

/--
Under `guardInvWP ewp Inv`, the invariant can always be added to the return
postcondition of `FairInfOften` without needing `Conjunctive ewp`.
-/
theorem FairInfOften.post_inv_guardInv {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Inv : S → Prop}
    {Q : R → S → Prop} {t : ITree E R} {s : S}
    (h_inv : Inv s) (h : FairInfOften (guardInvWP ewp Inv) AccEdge Fair Q t s) :
    FairInfOften (guardInvWP ewp Inv) AccEdge Fair (fun r s' => Inv s' ∧ Q r s') t s := by
  let X : ITree E R → S → Prop := fun x s₀ =>
    Inv s₀ ∧ FairInfOften (guardInvWP ewp Inv) AccEdge Fair Q x s₀
  refine FairInfOften.coinduct X ?_ ⟨h_inv, h⟩
  rintro x s₀ ⟨hi₀, hx⟩
  rw [FairInfOften.unfold_eq] at hx
  refine fairProgress.induct
    (fun y s₁ => Inv s₁ →
      fairProgress (guardInvWP ewp Inv) AccEdge Fair (fun r s' => Inv s' ∧ Q r s') X y s₁)
    ?_ hx hi₀
  intro y s₁ hy hi₁
  rw [fairProgress.unfold_eq]
  let Z : ITree E R → S → Prop := fun z s₂ =>
    Inv s₂ ∧ fairStall (guardInvWP ewp Inv) AccEdge Fair Q
      (FairInfOften (guardInvWP ewp Inv) AccEdge Fair Q)
      (fun v s₃ => Inv s₃ →
        fairProgress (guardInvWP ewp Inv) AccEdge Fair (fun r s' => Inv s' ∧ Q r s') X v s₃)
      z s₂
  refine fairStall.coinduct Z ?_ ⟨hi₁, hy⟩
  rintro z s₂ ⟨hi₂, hz⟩
  rw [fairStall.unfold_eq] at hz
  refine fairStep.induct
    (fun w s₃ => Inv s₃ →
      fairStep (guardInvWP ewp Inv) AccEdge Fair (fun r s' => Inv s' ∧ Q r s') X
        (fairProgress (guardInvWP ewp Inv) AccEdge Fair (fun r s' => Inv s' ∧ Q r s') X)
        Z w s₃) ?_ hz hi₂
  intro w s₃ hw hi₃
  rw [fairStep.unfold_eq]
  cases h_obs : w.observe <;> simp only [h_obs] at hw ⊢
  · exact ⟨hi₃, hw⟩
  · exact hw hi₃
  · refine ewp.mono (fun _ _ ⟨hi', hp⟩ => ⟨hi', ?_⟩) hw
    rcases hp with ⟨ha, hfi⟩ | ⟨hf, hpre⟩ | ⟨hnf, hst⟩
    · exact Or.inl ⟨ha, hi', hfi⟩
    · exact Or.inr (Or.inl ⟨hf, hpre hi'⟩)
    · exact Or.inr (Or.inr ⟨hnf, hi', hst⟩)

/--
**Adversarial fair-non-accepting refutation** (no `Conjunctive` / `ExcludedMiracle`
needed): if there is an adversary invariant `Bad` from which the environment can
always force a fair non-accepting edge (and any return violates `Q`), then
`FairInfOften` is refuted.
-/
theorem not_fairInfOften_of_fair_adversary {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    (Bad : ITree E R → S → Prop)
    (h_bad : ∀ x s₀, Bad x s₀ →
      match x.observe with
      | .ret r => ¬ Q r s₀
      | .tau x' => Bad x' s₀
      | .vis i k => ∀ K, ewp.wp i K s₀ →
          ∃ o s', K o s' ∧ ¬ AccEdge i o s₀ s' ∧ Fair i o s₀ s' ∧ Bad (k o) s')
    {t : ITree E R} {s : S} (h_init : Bad t s) :
    ¬ FairInfOften ewp AccEdge Fair Q t s := by
  intro h
  rw [FairInfOften.unfold_eq] at h
  refine fairProgress.induct (fun x s₀ => Bad x s₀ → False) ?_ h h_init
  intro x s₀ hx hbx
  rw [fairStall.unfold_eq] at hx
  refine fairStep.induct (fun y s₁ => Bad y s₁ → False) ?_ hx hbx
  intro y s₁ hy hby
  have hb := h_bad y s₁ hby
  cases h_obs : y.observe <;> simp only [h_obs] at hy hb
  · exact hb hy
  · exact hy hb
  · obtain ⟨_, _, hdisj, hna, hf, hbk⟩ := hb _ hy
    rcases hdisj with ⟨ha, _⟩ | ⟨_, hpre⟩ | ⟨hnf, _⟩
    · exact hna ha
    · exact hpre hbk
    · exact hnf hf

/--
Under conjunctivity and excluded miracle, any tree whose reachable steps are all
fair and non-accepting (and whose returns violate `Q`) refutes `FairInfOften`.
-/
theorem not_fairInfOften_of_alwaysStep_fair_not_accept {ewp : StateEffectWP S E}
    [h_conj : StateEffectWP.Conjunctive ewp]
    [h_em : StateEffectWP.ExcludedMiracle ewp]
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t : ITree E R} {s : S}
    (h_no : AlwaysStep ewp
      (fun i o s₀ s' => ¬ AccEdge i o s₀ s' ∧ Fair i o s₀ s')
      (fun r s' => ¬ Q r s') t s) :
    ¬ FairInfOften ewp AccEdge Fair Q t s := by
  intro h
  rw [FairInfOften.unfold_eq] at h
  refine fairProgress.induct
    (fun x s₀ => AlwaysStep ewp
      (fun i o s₁ s₂ => ¬ AccEdge i o s₁ s₂ ∧ Fair i o s₁ s₂)
      (fun r s₁ => ¬ Q r s₁) x s₀ → False) ?_ h h_no
  intro x s₀ hx h_as
  rw [fairStall.unfold_eq] at hx
  refine fairStep.induct
    (fun y s₁ => AlwaysStep ewp
      (fun i o s₂ s₃ => ¬ AccEdge i o s₂ s₃ ∧ Fair i o s₂ s₃)
      (fun r s₂ => ¬ Q r s₂) y s₁ → False) ?_ hx h_as
  intro y s₁ hy has
  rw [AlwaysStep.unfold_eq] at has
  cases h_obs : y.observe <;> simp only [h_obs] at hy has
  · exact has hy
  · exact hy has
  · refine h_em.no_miracle
      (ewp.mono (fun _ _ ⟨hp, ⟨hna, hf⟩, has'⟩ => ?_) (h_conj.conj hy has))
    rcases hp with ⟨ha, _⟩ | ⟨_, hpre⟩ | ⟨hnf, _⟩
    · exact hna ha
    · exact hpre has'
    · exact hnf hf

/--
**Horizontal handler linking** for `FairInfOften` across `ITree.interp`.
The link condition preserves all four parity levels: zero visible `E₂` steps may
only return into `K3` (never `K2`, ruling out silent `.tau^\omega` collapse); a
`Fair₂` edge commits to `K3` (never `K2`, preventing unfair steps from amplifying
into fair loops); `¬ Fair₂` edges may return `K3 ∨ K2`; and `Acc₂` edges reset to
`FairInfOften` over `K4 ∨ K3 ∨ K2`.
-/
theorem FairInfOften.interp {E₁ E₂ : Effect.{u}}
    {ewp₁ : StateEffectWP S E₁} {ewp₂ : StateEffectWP S E₂}
    {Acc₁ Fair₁ : (i : E₁.I) → E₁.O i → S → S → Prop}
    {Acc₂ Fair₂ : (j : E₂.I) → E₂.O j → S → S → Prop}
    (h : (i : E₁.I) → ITree E₂ (E₁.O i))
    (h_link : ∀ (i : E₁.I) (K4 K3 K2 : E₁.O i → S → Prop) (s₀ : S),
      ewp₁.wp i (fun o s' =>
        (Acc₁ i o s₀ s' ∧ K4 o s') ∨
        (Fair₁ i o s₀ s' ∧ K3 o s') ∨
        (¬ Fair₁ i o s₀ s' ∧ K2 o s')) s₀ →
      fairStep ewp₂ Acc₂ Fair₂ K3
        (FairInfOften ewp₂ Acc₂ Fair₂
          (fun o s'' => K4 o s'' ∨ K3 o s'' ∨ K2 o s''))
        (fairProgress ewp₂ Acc₂ Fair₂ K3
          (FairInfOften ewp₂ Acc₂ Fair₂
            (fun o s'' => K4 o s'' ∨ K3 o s'' ∨ K2 o s'')))
        (fairStall ewp₂ Acc₂ Fair₂ (fun o s'' => K3 o s'' ∨ K2 o s'')
          (FairInfOften ewp₂ Acc₂ Fair₂
            (fun o s'' => K4 o s'' ∨ K3 o s'' ∨ K2 o s''))
          (fairProgress ewp₂ Acc₂ Fair₂ K3
            (FairInfOften ewp₂ Acc₂ Fair₂
              (fun o s'' => K4 o s'' ∨ K3 o s'' ∨ K2 o s''))))
        (h i) s₀)
    {t : ITree E₁ R} {Q : R → S → Prop} {s : S}
    (h_fi : FairInfOften ewp₁ Acc₁ Fair₁ Q t s) :
    FairInfOften ewp₂ Acc₂ Fair₂ Q (ITree.interp h t) s := by
  let X : ITree E₂ R → S → Prop := fun u s₀ =>
    (∃ t₀, u = ITree.interp h t₀ ∧ FairInfOften ewp₁ Acc₁ Fair₁ Q t₀ s₀) ∨
    (∃ (i : E₁.I) (m : ITree E₂ (E₁.O i)) (k : E₁.O i → ITree E₁ R),
      u = (m >>= fun o => .tau (ITree.interp h (k o))) ∧
      FairInfOften ewp₂ Acc₂ Fair₂
        (fun o s' => FairInfOften ewp₁ Acc₁ Fair₁ Q (k o) s') m s₀)
  let FP : ITree E₂ R → S → Prop := fairProgress ewp₂ Acc₂ Fair₂ Q X
  have h_lift_prog : ∀ (i : E₁.I) (k : E₁.O i → ITree E₁ R)
      (P3 : E₁.O i → S → Prop),
      (∀ o s', P3 o s' → FP (ITree.interp h (k o)) s') →
      ∀ (m : ITree E₂ (E₁.O i)) (s₀ : S),
        fairProgress ewp₂ Acc₂ Fair₂ P3
          (FairInfOften ewp₂ Acc₂ Fair₂
            (fun o s' => FairInfOften ewp₁ Acc₁ Fair₁ Q (k o) s')) m s₀ →
        FP (m >>= fun o => .tau (ITree.interp h (k o))) s₀ := by
    intro i k P3 hP3 m s₀ hm
    refine fairProgress.induct
      (fun m₁ s₁ => FP (m₁ >>= fun o => .tau (ITree.interp h (k o))) s₁) ?_ hm
    intro m₁ s₁ hm₁
    dsimp only [FP]
    rw [fairProgress.unfold_eq]
    let Zm : ITree E₂ R → S → Prop := fun u s₂ =>
      (∃ m₂, u = (m₂ >>= fun o => .tau (ITree.interp h (k o))) ∧
        fairStall ewp₂ Acc₂ Fair₂ P3
          (FairInfOften ewp₂ Acc₂ Fair₂
            (fun o s' => FairInfOften ewp₁ Acc₁ Fair₁ Q (k o) s'))
          (fun m₃ s₃ => FP (m₃ >>= fun o => .tau (ITree.interp h (k o))) s₃)
          m₂ s₂) ∨
      FP u s₂
    refine fairStall.coinduct Zm ?_ (Or.inl ⟨m₁, rfl, hm₁⟩)
    rintro u s₂ (⟨m₂, rfl, hm₂⟩ | hu)
    · rw [fairStall.unfold_eq] at hm₂
      refine fairStep.induct
        (fun m₃ s₃ => fairStep ewp₂ Acc₂ Fair₂ Q X FP Zm
          (m₃ >>= fun o => .tau (ITree.interp h (k o))) s₃) ?_ hm₂
      intro m₃ s₃ hm₃
      cases hm_obs : m₃.observe with
      | ret o =>
        simp only [hm_obs] at hm₃
        rw [eq_ret_of_observe hm_obs, ret_bind, fairStep.tau_iff]
        exact fairStep.mono (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => Or.inr h)
          (fairProgress.toFairStep (hP3 o s₃ hm₃))
      | tau m₃' =>
        simp only [hm_obs] at hm₃
        rw [eq_tau_of_observe hm_obs, tau_bind, fairStep.tau_iff]; exact hm₃
      | vis j c =>
        simp only [hm_obs] at hm₃
        rw [eq_vis_of_observe hm_obs, vis_bind, fairStep.vis_iff]
        refine ewp₂.mono (fun o₂ s' hp => ?_) hm₃
        rcases hp with ⟨ha, hfi_m⟩ | ⟨hf, hpre⟩ | ⟨hnf, hst⟩
        · exact Or.inl ⟨ha, Or.inr ⟨i, c o₂, k, rfl, hfi_m⟩⟩
        · exact Or.inr (Or.inl ⟨hf, hpre⟩)
        · exact Or.inr (Or.inr ⟨hnf, Or.inl ⟨c o₂, rfl, hst⟩⟩)
    · exact fairStep.mono (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => Or.inr h)
        (fairProgress.toFairStep hu)
  have h_main : ∀ (t₀ : ITree E₁ R) (s₀ : S), FairInfOften ewp₁ Acc₁ Fair₁ Q t₀ s₀ →
      FP (ITree.interp h t₀) s₀ := by
    intro t₀ s₀ ht₀
    rw [FairInfOften.unfold_eq] at ht₀
    let Pre : ITree E₁ R → S → Prop := fun v s₃ =>
      FairInfOften ewp₁ Acc₁ Fair₁ Q v s₃ ∧ FP (ITree.interp h v) s₃
    refine (fairProgress.induct Pre ?_ ht₀).2
    intro t₁ s₁ ht₁
    have hfi_t₁ : FairInfOften ewp₁ Acc₁ Fair₁ Q t₁ s₁ :=
      fairStall_to_fairInfOften (fairStall.mono (fun _ _ hx => hx) (fun _ _ hp => hp.1) ht₁)
    refine ⟨hfi_t₁, ?_⟩
    dsimp only [FP]
    rw [fairProgress.unfold_eq]
    let Z : ITree E₂ R → S → Prop := fun u s₂ =>
      (∃ t₂, u = ITree.interp h t₂ ∧
        fairStall ewp₁ Acc₁ Fair₁ Q (FairInfOften ewp₁ Acc₁ Fair₁ Q) Pre t₂ s₂) ∨
      (∃ (i : E₁.I) (m : ITree E₂ (E₁.O i)) (k : E₁.O i → ITree E₁ R),
        u = (m >>= fun o => .tau (ITree.interp h (k o))) ∧
        fairStall ewp₂ Acc₂ Fair₂
          (fun o s' => Pre (k o) s' ∨
            fairStall ewp₁ Acc₁ Fair₁ Q (FairInfOften ewp₁ Acc₁ Fair₁ Q) Pre (k o) s')
          (FairInfOften ewp₂ Acc₂ Fair₂
            (fun o s' => FairInfOften ewp₁ Acc₁ Fair₁ Q (k o) s'))
          (fairProgress ewp₂ Acc₂ Fair₂ (fun o s' => Pre (k o) s')
            (FairInfOften ewp₂ Acc₂ Fair₂
              (fun o s' => FairInfOften ewp₁ Acc₁ Fair₁ Q (k o) s')))
          m s₂) ∨
      FP u s₂
    have h_step_t : ∀ t₂ s₂,
        fairStall ewp₁ Acc₁ Fair₁ Q (FairInfOften ewp₁ Acc₁ Fair₁ Q) Pre t₂ s₂ →
        fairStep ewp₂ Acc₂ Fair₂ Q X FP Z (ITree.interp h t₂) s₂ := by
      intro t₂ s₂ ht₂
      rw [fairStall.unfold_eq] at ht₂
      refine fairStep.induct
        (fun t₃ s₃ => fairStep ewp₂ Acc₂ Fair₂ Q X FP Z (ITree.interp h t₃) s₃) ?_ ht₂
      intro t₃ s₃ ht₃
      cases h_obs : t₃.observe with
      | ret r =>
        simp only [h_obs] at ht₃
        rw [eq_ret_of_observe h_obs, interp_ret, fairStep.ret_iff]; exact ht₃
      | tau t₃' =>
        simp only [h_obs] at ht₃
        rw [eq_tau_of_observe h_obs, interp_tau, fairStep.tau_iff]; exact ht₃
      | vis i k =>
        simp only [h_obs] at ht₃
        rw [eq_vis_of_observe h_obs, interp_vis]
        let K4 : E₁.O i → S → Prop := fun o s' => FairInfOften ewp₁ Acc₁ Fair₁ Q (k o) s'
        let K3 : E₁.O i → S → Prop := fun o s' => Pre (k o) s'
        let K2 : E₁.O i → S → Prop := fun o s' =>
          fairStall ewp₁ Acc₁ Fair₁ Q (FairInfOften ewp₁ Acc₁ Fair₁ Q) Pre (k o) s'
        have h_all_fi : ∀ o s', K4 o s' ∨ K3 o s' ∨ K2 o s' → K4 o s' := by
          intro o s' hdisj
          rcases hdisj with h4 | h3 | h2
          · exact h4
          · exact h3.1
          · exact fairStall_to_fairInfOften
              (fairStall.mono (fun _ _ hx => hx) (fun _ _ hp => hp.1) h2)
        have h_l := h_link i K4 K3 K2 s₃ ht₃
        refine fairStep.induct
          (fun m s₄ => fairStep ewp₂ Acc₂ Fair₂ Q X FP Z
            (m >>= fun o => .tau (ITree.interp h (k o))) s₄) ?_ h_l
        intro m s₄ hm
        cases hm_obs : m.observe with
        | ret o =>
          simp only [hm_obs] at hm
          rw [eq_ret_of_observe hm_obs, ret_bind, fairStep.tau_iff]
          exact fairStep.mono (fun _ _ h => h) (fun _ _ h => h)
            (fun _ _ h => Or.inr (Or.inr h)) (fairProgress.toFairStep hm.2)
        | tau m' =>
          simp only [hm_obs] at hm
          rw [eq_tau_of_observe hm_obs, tau_bind, fairStep.tau_iff]; exact hm
        | vis j c =>
          simp only [hm_obs] at hm
          rw [eq_vis_of_observe hm_obs, vis_bind, fairStep.vis_iff]
          refine ewp₂.mono (fun o₂ s' hp => ?_) hm
          rcases hp with ⟨ha, hfi_m⟩ | ⟨hf, hprog_m⟩ | ⟨hnf, hst_m⟩
          · exact Or.inl ⟨ha, Or.inr ⟨i, c o₂, k, rfl,
              FairInfOften.mono_post h_all_fi hfi_m⟩⟩
          · refine Or.inr (Or.inl ⟨hf, h_lift_prog i k K3 (fun _ _ hp => hp.2) (c o₂) s' ?_⟩)
            exact fairProgress.mono (fun _ _ hm' => FairInfOften.mono_post h_all_fi hm') hprog_m
          · refine Or.inr (Or.inr ⟨hnf, Or.inr (Or.inl ⟨i, c o₂, k, rfl, ?_⟩)⟩)
            exact fairStall.mono
              (fun _ _ hm' => FairInfOften.mono_post h_all_fi hm')
              (fun _ _ hp' => fairProgress.mono
                (fun _ _ hm' => FairInfOften.mono_post h_all_fi hm') hp') hst_m
    refine fairStall.coinduct Z ?_ (Or.inl ⟨t₁, rfl, ht₁⟩)
    rintro u s₂ (⟨t₂, rfl, ht₂⟩ | ⟨i, m, k, rfl, hm⟩ | hu)
    · exact h_step_t t₂ s₂ ht₂
    · rw [fairStall.unfold_eq] at hm
      refine fairStep.induct
        (fun m₁ s₃ => fairStep ewp₂ Acc₂ Fair₂ Q X FP Z
          (m₁ >>= fun o => .tau (ITree.interp h (k o))) s₃) ?_ hm
      intro m₁ s₃ hm₁
      cases hm_obs : m₁.observe with
      | ret o =>
        simp only [hm_obs] at hm₁
        rw [eq_ret_of_observe hm_obs, ret_bind, fairStep.tau_iff]
        rcases hm₁ with hpre | hst_k
        · exact fairStep.mono (fun _ _ h => h) (fun _ _ h => h)
            (fun _ _ h => Or.inr (Or.inr h)) (fairProgress.toFairStep hpre.2)
        · exact h_step_t (k o) s₃ hst_k
      | tau m₁' =>
        simp only [hm_obs] at hm₁
        rw [eq_tau_of_observe hm_obs, tau_bind, fairStep.tau_iff]; exact hm₁
      | vis j c =>
        simp only [hm_obs] at hm₁
        rw [eq_vis_of_observe hm_obs, vis_bind, fairStep.vis_iff]
        refine ewp₂.mono (fun o₂ s' hp => ?_) hm₁
        rcases hp with ⟨ha, hfi_m⟩ | ⟨hf, hprog_m⟩ | ⟨hnf, hst_m⟩
        · exact Or.inl ⟨ha, Or.inr ⟨i, c o₂, k, rfl, hfi_m⟩⟩
        · exact Or.inr (Or.inl ⟨hf, h_lift_prog i k (fun o s' => Pre (k o) s')
            (fun _ _ hp => hp.2) (c o₂) s' hprog_m⟩)
        · exact Or.inr (Or.inr ⟨hnf, Or.inr (Or.inl ⟨i, c o₂, k, rfl, hst_m⟩)⟩)
    · exact fairStep.mono (fun _ _ h => h) (fun _ _ h => h)
        (fun _ _ h => Or.inr (Or.inr h)) (fairProgress.toFairStep hu)
  refine FairInfOften.coinduct X ?_ (Or.inl ⟨t, rfl, h_fi⟩)
  rintro u s₀ (⟨t₀, rfl, ht₀⟩ | ⟨i, m, k, rfl, hm⟩)
  · exact h_main t₀ s₀ ht₀
  · rw [FairInfOften.unfold_eq] at hm
    exact h_lift_prog i k (fun o s' => FairInfOften ewp₁ Acc₁ Fair₁ Q (k o) s')
      (fun o s' hk => h_main (k o) s' hk) m s₀ hm

/--
**Stateful handler linking** for `FairInfOften` across `ITree.interpState`,
threading the handler state `H` that the source transformer treats as its
logical state. The link condition is the stateful analogue of the parity
constraint of `FairInfOften.interp`: handler returns before any visible `E₂`
step (or after a `Fair₂` edge) land only in `K3`, unfair `E₂` edges may return
into `K3 ∨ K2`, and `Acc₂` edges reset to `FairInfOften` over `K4 ∨ K3 ∨ K2`.
-/
theorem FairInfOften.interpState {H : Type u} {E₁ E₂ : Effect.{u}} {R : Type u}
    {ewp₁ : StateEffectWP H E₁} {ewp₂ : EffectWP E₂}
    {Acc₁ Fair₁ : (i : E₁.I) → E₁.O i → H → H → Prop}
    {Acc₂ Fair₂ : (j : E₂.I) → E₂.O j → PUnit.{u + 1} → PUnit.{u + 1} → Prop}
    (h : (i : E₁.I) → H → ITree E₂ (E₁.O i × H))
    (h_link : ∀ (i : E₁.I) (K4 K3 K2 : E₁.O i → H → Prop) (st : H),
      ewp₁.wp i (fun o st' =>
        (Acc₁ i o st st' ∧ K4 o st') ∨
        (Fair₁ i o st st' ∧ K3 o st') ∨
        (¬ Fair₁ i o st st' ∧ K2 o st')) st →
      fairStep ewp₂ Acc₂ Fair₂ (fun pair _ => K3 pair.1 pair.2)
        (FairInfOften ewp₂ Acc₂ Fair₂
          (fun pair _ => K4 pair.1 pair.2 ∨ K3 pair.1 pair.2 ∨ K2 pair.1 pair.2))
        (fairProgress ewp₂ Acc₂ Fair₂ (fun pair _ => K3 pair.1 pair.2)
          (FairInfOften ewp₂ Acc₂ Fair₂
            (fun pair _ => K4 pair.1 pair.2 ∨ K3 pair.1 pair.2 ∨ K2 pair.1 pair.2)))
        (fairStall ewp₂ Acc₂ Fair₂
          (fun pair _ => K3 pair.1 pair.2 ∨ K2 pair.1 pair.2)
          (FairInfOften ewp₂ Acc₂ Fair₂
            (fun pair _ => K4 pair.1 pair.2 ∨ K3 pair.1 pair.2 ∨ K2 pair.1 pair.2))
          (fairProgress ewp₂ Acc₂ Fair₂ (fun pair _ => K3 pair.1 pair.2)
            (FairInfOften ewp₂ Acc₂ Fair₂
              (fun pair _ => K4 pair.1 pair.2 ∨ K3 pair.1 pair.2 ∨ K2 pair.1 pair.2))))
        (h i st) PUnit.unit)
    {t : ITree E₁ R} {Q : R → H → Prop} {st : H}
    (h_fi : FairInfOften ewp₁ Acc₁ Fair₁ Q t st) :
    FairInfOften ewp₂ Acc₂ Fair₂ (fun pair _ => Q pair.1 pair.2)
      (ITree.interpState h t st) PUnit.unit := by
  let Q₂ : R × H → PUnit.{u + 1} → Prop := fun pair _ => Q pair.1 pair.2
  let X : ITree E₂ (R × H) → PUnit.{u + 1} → Prop := fun u _ =>
    (∃ t₀ st₀, u = ITree.interpState h t₀ st₀ ∧
      FairInfOften ewp₁ Acc₁ Fair₁ Q t₀ st₀) ∨
    (∃ (i : E₁.I) (m : ITree E₂ (E₁.O i × H)) (k : E₁.O i → ITree E₁ R),
      u = (m >>= fun (o, st') => .tau (ITree.interpState h (k o) st')) ∧
      FairInfOften ewp₂ Acc₂ Fair₂
        (fun pair _ => FairInfOften ewp₁ Acc₁ Fair₁ Q (k pair.1) pair.2)
        m PUnit.unit)
  let FP : ITree E₂ (R × H) → PUnit.{u + 1} → Prop :=
    fairProgress ewp₂ Acc₂ Fair₂ Q₂ X
  have h_lift_prog : ∀ (i : E₁.I) (k : E₁.O i → ITree E₁ R)
      (P3 : E₁.O i × H → PUnit.{u + 1} → Prop),
      (∀ pair s', P3 pair s' →
        FP (ITree.interpState h (k pair.1) pair.2) s') →
      ∀ (m : ITree E₂ (E₁.O i × H)) (s₀ : PUnit.{u + 1}),
        fairProgress ewp₂ Acc₂ Fair₂ P3
          (FairInfOften ewp₂ Acc₂ Fair₂
            (fun pair _ => FairInfOften ewp₁ Acc₁ Fair₁ Q (k pair.1) pair.2))
          m s₀ →
        FP (m >>= fun (o, st') => .tau (ITree.interpState h (k o) st')) s₀ := by
    intro i k P3 hP3 m s₀ hm
    refine fairProgress.induct
      (fun m₁ s₁ => FP (m₁ >>= fun (o, st') => .tau (ITree.interpState h (k o) st'))
        s₁) ?_ hm
    intro m₁ s₁ hm₁
    dsimp only [FP]
    rw [fairProgress.unfold_eq]
    let Zm : ITree E₂ (R × H) → PUnit.{u + 1} → Prop := fun u s₂ =>
      (∃ m₂, u = (m₂ >>= fun (o, st') => .tau (ITree.interpState h (k o) st')) ∧
        fairStall ewp₂ Acc₂ Fair₂ P3
          (FairInfOften ewp₂ Acc₂ Fair₂
            (fun pair _ => FairInfOften ewp₁ Acc₁ Fair₁ Q (k pair.1) pair.2))
          (fun m₃ s₃ =>
            FP (m₃ >>= fun (o, st') => .tau (ITree.interpState h (k o) st')) s₃)
          m₂ s₂) ∨
      FP u s₂
    refine fairStall.coinduct Zm ?_ (Or.inl ⟨m₁, rfl, hm₁⟩)
    rintro u s₂ (⟨m₂, rfl, hm₂⟩ | hu)
    · rw [fairStall.unfold_eq] at hm₂
      refine fairStep.induct
        (fun m₃ s₃ => fairStep ewp₂ Acc₂ Fair₂ Q₂ X FP Zm
          (m₃ >>= fun (o, st') => .tau (ITree.interpState h (k o) st')) s₃) ?_ hm₂
      intro m₃ s₃ hm₃
      cases hm_obs : m₃.observe with
      | ret pair =>
        simp only [hm_obs] at hm₃
        rcases pair with ⟨o, st'⟩
        rw [eq_ret_of_observe hm_obs, ret_bind, fairStep.tau_iff]
        exact fairStep.mono (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => Or.inr h)
          (fairProgress.toFairStep (hP3 (o, st') s₃ hm₃))
      | tau m₃' =>
        simp only [hm_obs] at hm₃
        rw [eq_tau_of_observe hm_obs, tau_bind, fairStep.tau_iff]; exact hm₃
      | vis j c =>
        simp only [hm_obs] at hm₃
        rw [eq_vis_of_observe hm_obs, vis_bind, fairStep.vis_iff]
        refine ewp₂.mono (fun o₂ s' hp => ?_) hm₃
        rcases hp with ⟨ha, hfi_m⟩ | ⟨hf, hpre⟩ | ⟨hnf, hst⟩
        · exact Or.inl ⟨ha, Or.inr ⟨i, c o₂, k, rfl, hfi_m⟩⟩
        · exact Or.inr (Or.inl ⟨hf, hpre⟩)
        · exact Or.inr (Or.inr ⟨hnf, Or.inl ⟨c o₂, rfl, hst⟩⟩)
    · exact fairStep.mono (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => Or.inr h)
        (fairProgress.toFairStep hu)
  have h_main : ∀ (t₀ : ITree E₁ R) (st₀ : H),
      FairInfOften ewp₁ Acc₁ Fair₁ Q t₀ st₀ →
      FP (ITree.interpState h t₀ st₀) PUnit.unit := by
    intro t₀ st₀ ht₀
    rw [FairInfOften.unfold_eq] at ht₀
    let Pre : ITree E₁ R → H → Prop := fun v st₃ =>
      FairInfOften ewp₁ Acc₁ Fair₁ Q v st₃ ∧ FP (ITree.interpState h v st₃) PUnit.unit
    refine (fairProgress.induct Pre ?_ ht₀).2
    intro t₁ st₁ ht₁
    have hfi_t₁ : FairInfOften ewp₁ Acc₁ Fair₁ Q t₁ st₁ :=
      fairStall_to_fairInfOften
        (fairStall.mono (fun _ _ hx => hx) (fun _ _ hp => hp.1) ht₁)
    refine ⟨hfi_t₁, ?_⟩
    dsimp only [FP]
    rw [fairProgress.unfold_eq]
    let Z : ITree E₂ (R × H) → PUnit.{u + 1} → Prop := fun u _ =>
      (∃ t₂ st₂, u = ITree.interpState h t₂ st₂ ∧
        fairStall ewp₁ Acc₁ Fair₁ Q (FairInfOften ewp₁ Acc₁ Fair₁ Q) Pre t₂ st₂) ∨
      (∃ (i : E₁.I) (m : ITree E₂ (E₁.O i × H)) (k : E₁.O i → ITree E₁ R),
        u = (m >>= fun (o, st') => .tau (ITree.interpState h (k o) st')) ∧
        fairStall ewp₂ Acc₂ Fair₂
          (fun pair _ => Pre (k pair.1) pair.2 ∨
            fairStall ewp₁ Acc₁ Fair₁ Q (FairInfOften ewp₁ Acc₁ Fair₁ Q) Pre
              (k pair.1) pair.2)
          (FairInfOften ewp₂ Acc₂ Fair₂
            (fun pair _ => FairInfOften ewp₁ Acc₁ Fair₁ Q (k pair.1) pair.2))
          (fairProgress ewp₂ Acc₂ Fair₂ (fun pair _ => Pre (k pair.1) pair.2)
            (FairInfOften ewp₂ Acc₂ Fair₂
              (fun pair _ => FairInfOften ewp₁ Acc₁ Fair₁ Q (k pair.1) pair.2)))
          m PUnit.unit) ∨
      FP u PUnit.unit
    have h_step_t : ∀ t₂ st₂,
        fairStall ewp₁ Acc₁ Fair₁ Q (FairInfOften ewp₁ Acc₁ Fair₁ Q) Pre t₂ st₂ →
        fairStep ewp₂ Acc₂ Fair₂ Q₂ X FP Z (ITree.interpState h t₂ st₂) PUnit.unit := by
      intro t₂ st₂ ht₂
      rw [fairStall.unfold_eq] at ht₂
      refine fairStep.induct
        (fun t₃ st₃ => fairStep ewp₂ Acc₂ Fair₂ Q₂ X FP Z
          (ITree.interpState h t₃ st₃) PUnit.unit) ?_ ht₂
      intro t₃ st₃ ht₃
      cases h_obs : t₃.observe with
      | ret r =>
        simp only [h_obs] at ht₃
        rw [eq_ret_of_observe h_obs, interpState_ret, fairStep.ret_iff]; exact ht₃
      | tau t₃' =>
        simp only [h_obs] at ht₃
        rw [eq_tau_of_observe h_obs, interpState_tau, fairStep.tau_iff]; exact ht₃
      | vis i k =>
        simp only [h_obs] at ht₃
        rw [eq_vis_of_observe h_obs, interpState_vis]
        let K4 : E₁.O i → H → Prop := fun o st' =>
          FairInfOften ewp₁ Acc₁ Fair₁ Q (k o) st'
        let K3 : E₁.O i → H → Prop := fun o st' => Pre (k o) st'
        let K2 : E₁.O i → H → Prop := fun o st' =>
          fairStall ewp₁ Acc₁ Fair₁ Q (FairInfOften ewp₁ Acc₁ Fair₁ Q) Pre (k o) st'
        have h_all_fi : ∀ (pair : E₁.O i × H) (s' : PUnit.{u + 1}),
            K4 pair.1 pair.2 ∨ K3 pair.1 pair.2 ∨ K2 pair.1 pair.2 →
            K4 pair.1 pair.2 := by
          intro pair s' hdisj
          rcases hdisj with h4 | h3 | h2
          · exact h4
          · exact h3.1
          · exact fairStall_to_fairInfOften
              (fairStall.mono (fun _ _ hx => hx) (fun _ _ hp => hp.1) h2)
        have h_l := h_link i K4 K3 K2 st₃ ht₃
        refine fairStep.induct
          (fun m s₄ => fairStep ewp₂ Acc₂ Fair₂ Q₂ X FP Z
            (m >>= fun (o, st') => .tau (ITree.interpState h (k o) st')) s₄) ?_ h_l
        intro m s₄ hm
        cases hm_obs : m.observe with
        | ret pair =>
          simp only [hm_obs] at hm
          rcases pair with ⟨o, st'⟩
          rw [eq_ret_of_observe hm_obs, ret_bind, fairStep.tau_iff]
          exact fairStep.mono (fun _ _ h => h) (fun _ _ h => h)
            (fun _ _ h => Or.inr (Or.inr h)) (fairProgress.toFairStep hm.2)
        | tau m' =>
          simp only [hm_obs] at hm
          rw [eq_tau_of_observe hm_obs, tau_bind, fairStep.tau_iff]; exact hm
        | vis j c =>
          simp only [hm_obs] at hm
          rw [eq_vis_of_observe hm_obs, vis_bind, fairStep.vis_iff]
          refine ewp₂.mono (fun o₂ s' hp => ?_) hm
          rcases hp with ⟨ha, hfi_m⟩ | ⟨hf, hprog_m⟩ | ⟨hnf, hst_m⟩
          · exact Or.inl ⟨ha, Or.inr ⟨i, c o₂, k, rfl,
              FairInfOften.mono_post h_all_fi hfi_m⟩⟩
          · refine Or.inr (Or.inl ⟨hf, h_lift_prog i k (fun pair _ => K3 pair.1 pair.2)
              (fun _ _ hp => hp.2) (c o₂) s' ?_⟩)
            exact fairProgress.mono
              (fun _ _ hm' => FairInfOften.mono_post h_all_fi hm') hprog_m
          · refine Or.inr (Or.inr ⟨hnf, Or.inr (Or.inl ⟨i, c o₂, k, rfl, ?_⟩)⟩)
            exact fairStall.mono
              (fun _ _ hm' => FairInfOften.mono_post h_all_fi hm')
              (fun _ _ hp' => fairProgress.mono
                (fun _ _ hm' => FairInfOften.mono_post h_all_fi hm') hp') hst_m
    refine fairStall.coinduct Z ?_ (Or.inl ⟨t₁, st₁, rfl, ht₁⟩)
    rintro u ⟨⟩ (⟨t₂, st₂, rfl, ht₂⟩ | ⟨i, m, k, rfl, hm⟩ | hu)
    · exact h_step_t t₂ st₂ ht₂
    · rw [fairStall.unfold_eq] at hm
      refine fairStep.induct
        (fun m₁ s₃ => fairStep ewp₂ Acc₂ Fair₂ Q₂ X FP Z
          (m₁ >>= fun (o, st') => .tau (ITree.interpState h (k o) st')) s₃) ?_ hm
      intro m₁ s₃ hm₁
      cases hm_obs : m₁.observe with
      | ret pair =>
        simp only [hm_obs] at hm₁
        rcases pair with ⟨o, st'⟩
        rw [eq_ret_of_observe hm_obs, ret_bind, fairStep.tau_iff]
        rcases hm₁ with hpre | hst_k
        · exact fairStep.mono (fun _ _ h => h) (fun _ _ h => h)
            (fun _ _ h => Or.inr (Or.inr h)) (fairProgress.toFairStep hpre.2)
        · exact h_step_t (k o) st' hst_k
      | tau m₁' =>
        simp only [hm_obs] at hm₁
        rw [eq_tau_of_observe hm_obs, tau_bind, fairStep.tau_iff]; exact hm₁
      | vis j c =>
        simp only [hm_obs] at hm₁
        rw [eq_vis_of_observe hm_obs, vis_bind, fairStep.vis_iff]
        refine ewp₂.mono (fun o₂ s' hp => ?_) hm₁
        rcases hp with ⟨ha, hfi_m⟩ | ⟨hf, hprog_m⟩ | ⟨hnf, hst_m⟩
        · exact Or.inl ⟨ha, Or.inr ⟨i, c o₂, k, rfl, hfi_m⟩⟩
        · exact Or.inr (Or.inl ⟨hf, h_lift_prog i k (fun pair _ => Pre (k pair.1) pair.2)
            (fun _ _ hp => hp.2) (c o₂) s' hprog_m⟩)
        · exact Or.inr (Or.inr ⟨hnf, Or.inr (Or.inl ⟨i, c o₂, k, rfl, hst_m⟩)⟩)
    · exact fairStep.mono (fun _ _ h => h) (fun _ _ h => h)
        (fun _ _ h => Or.inr (Or.inr h)) (fairProgress.toFairStep hu)
  refine FairInfOften.coinduct X ?_ (Or.inl ⟨t, st, rfl, h_fi⟩)
  rintro u ⟨⟩ (⟨t₀, st₀, rfl, ht₀⟩ | ⟨i, m, k, rfl, hm⟩)
  · exact h_main t₀ st₀ ht₀
  · rw [FairInfOften.unfold_eq] at hm
    exact h_lift_prog i k
      (fun pair _ => FairInfOften ewp₁ Acc₁ Fair₁ Q (k pair.1) pair.2)
      (fun pair _ hk => h_main (k pair.1) pair.2 hk) m PUnit.unit hm

/--
The link condition of `FairInfOften.interpState` is satisfiable: the
state-threading re-trigger handler preserves fairness-conditional recurrence.
-/
theorem FairInfOften.interpState_retrigger {E : Effect.{u}} {R : Type u}
    {ewp : EffectWP E}
    {AccEdge Fair : (i : E.I) → E.O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop}
    {t : ITree E R} {Q : R → PUnit.{u + 1} → Prop}
    (h_fi : FairInfOften ewp AccEdge Fair Q t PUnit.unit) :
    FairInfOften ewp AccEdge Fair (fun pair _ => Q pair.1 pair.2)
      (ITree.interpState (fun i st => ITree.vis i (fun o => ITree.ret (o, st))) t
        PUnit.unit) PUnit.unit := by
  refine FairInfOften.interpState _ ?_ h_fi
  intro i K4 K3 K2 st hw
  refine (fairStep.vis_iff _ _ _ _ _ _ _ _ _ _).2 (ewp.mono ?_ hw)
  rintro o s' (⟨ha, h4⟩ | ⟨hf, h3⟩ | ⟨hnf, h2⟩)
  · exact Or.inl ⟨ha, FairInfOften.ret (Or.inl h4)⟩
  · exact Or.inr (Or.inl ⟨hf, fairProgress.of_dwp _ (DWP.ret h3)⟩)
  · refine Or.inr (Or.inr ⟨hnf, ?_⟩)
    rw [fairStall.unfold_eq, fairStep.ret_iff]; exact Or.inr h2

/--
**Target-stateful handler linking** for `FairInfOften` across `ITree.interpState`:
the handler threads the program state `H` while an independent logical/monitor
state `S₂` persists on the target transformer `ewp₂ : StateEffectWP S₂ E₂`.
-/
theorem FairInfOften.interpState_stateful {S₂ H : Type u} {E₁ E₂ : Effect.{u}}
    {R : Type u} {ewp₁ : StateEffectWP (S₂ × H) E₁}
    {ewp₂ : StateEffectWP S₂ E₂}
    {Acc₁ Fair₁ : (i : E₁.I) → E₁.O i → S₂ × H → S₂ × H → Prop}
    {Acc₂ Fair₂ : (j : E₂.I) → E₂.O j → S₂ → S₂ → Prop}
    (h : (i : E₁.I) → H → ITree E₂ (E₁.O i × H))
    (h_link : ∀ (i : E₁.I) (K4 K3 K2 : E₁.O i → S₂ × H → Prop)
      (s₂ : S₂) (st : H),
      ewp₁.wp i (fun o p' =>
        (Acc₁ i o (s₂, st) p' ∧ K4 o p') ∨
        (Fair₁ i o (s₂, st) p' ∧ K3 o p') ∨
        (¬ Fair₁ i o (s₂, st) p' ∧ K2 o p')) (s₂, st) →
      fairStep ewp₂ Acc₂ Fair₂ (fun pair s₂' => K3 pair.1 (s₂', pair.2))
        (FairInfOften ewp₂ Acc₂ Fair₂
          (fun pair s₂' =>
            K4 pair.1 (s₂', pair.2) ∨ K3 pair.1 (s₂', pair.2) ∨
              K2 pair.1 (s₂', pair.2)))
        (fairProgress ewp₂ Acc₂ Fair₂ (fun pair s₂' => K3 pair.1 (s₂', pair.2))
          (FairInfOften ewp₂ Acc₂ Fair₂
            (fun pair s₂' =>
              K4 pair.1 (s₂', pair.2) ∨ K3 pair.1 (s₂', pair.2) ∨
                K2 pair.1 (s₂', pair.2))))
        (fairStall ewp₂ Acc₂ Fair₂
          (fun pair s₂' => K3 pair.1 (s₂', pair.2) ∨ K2 pair.1 (s₂', pair.2))
          (FairInfOften ewp₂ Acc₂ Fair₂
            (fun pair s₂' =>
              K4 pair.1 (s₂', pair.2) ∨ K3 pair.1 (s₂', pair.2) ∨
                K2 pair.1 (s₂', pair.2)))
          (fairProgress ewp₂ Acc₂ Fair₂ (fun pair s₂' => K3 pair.1 (s₂', pair.2))
            (FairInfOften ewp₂ Acc₂ Fair₂
              (fun pair s₂' =>
                K4 pair.1 (s₂', pair.2) ∨ K3 pair.1 (s₂', pair.2) ∨
                  K2 pair.1 (s₂', pair.2)))))
        (h i st) s₂)
    {t : ITree E₁ R} {Q : R → S₂ × H → Prop} {s₂ : S₂} {st : H}
    (h_fi : FairInfOften ewp₁ Acc₁ Fair₁ Q t (s₂, st)) :
    FairInfOften ewp₂ Acc₂ Fair₂ (fun pair s₂' => Q pair.1 (s₂', pair.2))
      (ITree.interpState h t st) s₂ := by
  let Q₂ : R × H → S₂ → Prop := fun pair s₂' => Q pair.1 (s₂', pair.2)
  let X : ITree E₂ (R × H) → S₂ → Prop := fun u s₀ =>
    (∃ t₀ st₀, u = ITree.interpState h t₀ st₀ ∧
      FairInfOften ewp₁ Acc₁ Fair₁ Q t₀ (s₀, st₀)) ∨
    (∃ (i : E₁.I) (m : ITree E₂ (E₁.O i × H)) (k : E₁.O i → ITree E₁ R),
      u = (m >>= fun (o, st') => .tau (ITree.interpState h (k o) st')) ∧
      FairInfOften ewp₂ Acc₂ Fair₂
        (fun pair s₂' => FairInfOften ewp₁ Acc₁ Fair₁ Q (k pair.1) (s₂', pair.2))
        m s₀)
  let FP : ITree E₂ (R × H) → S₂ → Prop := fairProgress ewp₂ Acc₂ Fair₂ Q₂ X
  have h_lift_prog : ∀ (i : E₁.I) (k : E₁.O i → ITree E₁ R)
      (P3 : E₁.O i × H → S₂ → Prop),
      (∀ pair s', P3 pair s' → FP (ITree.interpState h (k pair.1) pair.2) s') →
      ∀ (m : ITree E₂ (E₁.O i × H)) (s₀ : S₂),
        fairProgress ewp₂ Acc₂ Fair₂ P3
          (FairInfOften ewp₂ Acc₂ Fair₂
            (fun pair s₂' =>
              FairInfOften ewp₁ Acc₁ Fair₁ Q (k pair.1) (s₂', pair.2))) m s₀ →
        FP (m >>= fun (o, st') => .tau (ITree.interpState h (k o) st')) s₀ := by
    intro i k P3 hP3 m s₀ hm
    refine fairProgress.induct
      (fun m₁ s₁ => FP (m₁ >>= fun (o, st') => .tau (ITree.interpState h (k o) st')) s₁)
      ?_ hm
    intro m₁ s₁ hm₁
    dsimp only [FP]
    rw [fairProgress.unfold_eq]
    let Zm : ITree E₂ (R × H) → S₂ → Prop := fun u s₁' =>
      (∃ m₂, u = (m₂ >>= fun (o, st') => .tau (ITree.interpState h (k o) st')) ∧
        fairStall ewp₂ Acc₂ Fair₂ P3
          (FairInfOften ewp₂ Acc₂ Fair₂
            (fun pair s₂' =>
              FairInfOften ewp₁ Acc₁ Fair₁ Q (k pair.1) (s₂', pair.2)))
          (fun m₃ s₃ =>
            FP (m₃ >>= fun (o, st') => .tau (ITree.interpState h (k o) st')) s₃)
          m₂ s₁') ∨
      FP u s₁'
    refine fairStall.coinduct Zm ?_ (Or.inl ⟨m₁, rfl, hm₁⟩)
    rintro u s₁' (⟨m₂, rfl, hm₂⟩ | hu)
    · rw [fairStall.unfold_eq] at hm₂
      refine fairStep.induct
        (fun m₃ s₃ => fairStep ewp₂ Acc₂ Fair₂ Q₂ X FP Zm
          (m₃ >>= fun (o, st') => .tau (ITree.interpState h (k o) st')) s₃) ?_ hm₂
      intro m₃ s₃ hm₃
      cases hm_obs : m₃.observe with
      | ret pair =>
        simp only [hm_obs] at hm₃
        rcases pair with ⟨o, st'⟩
        rw [eq_ret_of_observe hm_obs, ret_bind, fairStep.tau_iff]
        exact fairStep.mono (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => Or.inr h)
          (fairProgress.toFairStep (hP3 (o, st') s₃ hm₃))
      | tau m₃' =>
        simp only [hm_obs] at hm₃
        rw [eq_tau_of_observe hm_obs, tau_bind, fairStep.tau_iff]; exact hm₃
      | vis j c =>
        simp only [hm_obs] at hm₃
        rw [eq_vis_of_observe hm_obs, vis_bind, fairStep.vis_iff]
        refine ewp₂.mono (fun o₂ s' hp => ?_) hm₃
        rcases hp with ⟨ha, hfi_m⟩ | ⟨hf, hpre⟩ | ⟨hnf, hst⟩
        · exact Or.inl ⟨ha, Or.inr ⟨i, c o₂, k, rfl, hfi_m⟩⟩
        · exact Or.inr (Or.inl ⟨hf, hpre⟩)
        · exact Or.inr (Or.inr ⟨hnf, Or.inl ⟨c o₂, rfl, hst⟩⟩)
    · exact fairStep.mono (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => Or.inr h)
        (fairProgress.toFairStep hu)
  have h_main : ∀ (t₀ : ITree E₁ R) (s₀ : S₂) (st₀ : H),
      FairInfOften ewp₁ Acc₁ Fair₁ Q t₀ (s₀, st₀) →
      FP (ITree.interpState h t₀ st₀) s₀ := by
    intro t₀ s₀ st₀ ht₀
    rw [FairInfOften.unfold_eq] at ht₀
    let Pre : ITree E₁ R → S₂ × H → Prop := fun v p =>
      FairInfOften ewp₁ Acc₁ Fair₁ Q v p ∧ FP (ITree.interpState h v p.2) p.1
    refine (fairProgress.induct Pre ?_ ht₀).2
    intro t₁ p ht₁
    have hfi_t₁ : FairInfOften ewp₁ Acc₁ Fair₁ Q t₁ p :=
      fairStall_to_fairInfOften
        (fairStall.mono (fun _ _ hx => hx) (fun _ _ hp => hp.1) ht₁)
    refine ⟨hfi_t₁, ?_⟩
    dsimp only [FP]
    rw [fairProgress.unfold_eq]
    let Z : ITree E₂ (R × H) → S₂ → Prop := fun u s₁ =>
      (∃ t₂ st₂, u = ITree.interpState h t₂ st₂ ∧
        fairStall ewp₁ Acc₁ Fair₁ Q (FairInfOften ewp₁ Acc₁ Fair₁ Q) Pre t₂ (s₁, st₂)) ∨
      (∃ (i : E₁.I) (m : ITree E₂ (E₁.O i × H)) (k : E₁.O i → ITree E₁ R),
        u = (m >>= fun (o, st') => .tau (ITree.interpState h (k o) st')) ∧
        fairStall ewp₂ Acc₂ Fair₂
          (fun pair s₂' => Pre (k pair.1) (s₂', pair.2) ∨
            fairStall ewp₁ Acc₁ Fair₁ Q (FairInfOften ewp₁ Acc₁ Fair₁ Q) Pre
              (k pair.1) (s₂', pair.2))
          (FairInfOften ewp₂ Acc₂ Fair₂
            (fun pair s₂' =>
              FairInfOften ewp₁ Acc₁ Fair₁ Q (k pair.1) (s₂', pair.2)))
          (fairProgress ewp₂ Acc₂ Fair₂ (fun pair s₂' => Pre (k pair.1) (s₂', pair.2))
            (FairInfOften ewp₂ Acc₂ Fair₂
              (fun pair s₂' =>
                FairInfOften ewp₁ Acc₁ Fair₁ Q (k pair.1) (s₂', pair.2))))
          m s₁) ∨
      FP u s₁
    have h_step_t : ∀ t₂ s₁ st₂,
        fairStall ewp₁ Acc₁ Fair₁ Q (FairInfOften ewp₁ Acc₁ Fair₁ Q) Pre t₂ (s₁, st₂) →
        fairStep ewp₂ Acc₂ Fair₂ Q₂ X FP Z (ITree.interpState h t₂ st₂) s₁ := by
      intro t₂ s₁ st₂ ht₂
      rw [fairStall.unfold_eq] at ht₂
      refine fairStep.induct
        (fun t₃ p₃ => fairStep ewp₂ Acc₂ Fair₂ Q₂ X FP Z
          (ITree.interpState h t₃ p₃.2) p₃.1) ?_ ht₂
      intro t₃ p₃ ht₃
      cases h_obs : t₃.observe with
      | ret r =>
        simp only [h_obs] at ht₃
        rw [eq_ret_of_observe h_obs, interpState_ret, fairStep.ret_iff]; exact ht₃
      | tau t₃' =>
        simp only [h_obs] at ht₃
        rw [eq_tau_of_observe h_obs, interpState_tau, fairStep.tau_iff]; exact ht₃
      | vis i k =>
        simp only [h_obs] at ht₃
        rw [eq_vis_of_observe h_obs, interpState_vis]
        let K4 : E₁.O i → S₂ × H → Prop := fun o p' =>
          FairInfOften ewp₁ Acc₁ Fair₁ Q (k o) p'
        let K3 : E₁.O i → S₂ × H → Prop := fun o p' => Pre (k o) p'
        let K2 : E₁.O i → S₂ × H → Prop := fun o p' =>
          fairStall ewp₁ Acc₁ Fair₁ Q (FairInfOften ewp₁ Acc₁ Fair₁ Q) Pre (k o) p'
        have h_all_fi : ∀ (pair : E₁.O i × H) (s' : S₂),
            K4 pair.1 (s', pair.2) ∨ K3 pair.1 (s', pair.2) ∨ K2 pair.1 (s', pair.2) →
            K4 pair.1 (s', pair.2) := by
          intro pair s' hdisj
          rcases hdisj with h4 | h3 | h2
          · exact h4
          · exact h3.1
          · exact fairStall_to_fairInfOften
              (fairStall.mono (fun _ _ hx => hx) (fun _ _ hp => hp.1) h2)
        have h_l := h_link i K4 K3 K2 p₃.1 p₃.2 ht₃
        refine fairStep.induct
          (fun m s₄ => fairStep ewp₂ Acc₂ Fair₂ Q₂ X FP Z
            (m >>= fun (o, st') => .tau (ITree.interpState h (k o) st')) s₄) ?_ h_l
        intro m s₄ hm
        cases hm_obs : m.observe with
        | ret pair =>
          simp only [hm_obs] at hm
          rcases pair with ⟨o, st'⟩
          rw [eq_ret_of_observe hm_obs, ret_bind, fairStep.tau_iff]
          exact fairStep.mono (fun _ _ h => h) (fun _ _ h => h)
            (fun _ _ h => Or.inr (Or.inr h)) (fairProgress.toFairStep hm.2)
        | tau m' =>
          simp only [hm_obs] at hm
          rw [eq_tau_of_observe hm_obs, tau_bind, fairStep.tau_iff]; exact hm
        | vis j c =>
          simp only [hm_obs] at hm
          rw [eq_vis_of_observe hm_obs, vis_bind, fairStep.vis_iff]
          refine ewp₂.mono (fun o₂ s' hp => ?_) hm
          rcases hp with ⟨ha, hfi_m⟩ | ⟨hf, hprog_m⟩ | ⟨hnf, hst_m⟩
          · exact Or.inl ⟨ha, Or.inr ⟨i, c o₂, k, rfl,
              FairInfOften.mono_post h_all_fi hfi_m⟩⟩
          · refine Or.inr (Or.inl ⟨hf,
              h_lift_prog i k (fun pair s₂' => K3 pair.1 (s₂', pair.2))
                (fun _ _ hp => hp.2) (c o₂) s' ?_⟩)
            exact fairProgress.mono
              (fun _ _ hm' => FairInfOften.mono_post h_all_fi hm') hprog_m
          · refine Or.inr (Or.inr ⟨hnf, Or.inr (Or.inl ⟨i, c o₂, k, rfl, ?_⟩)⟩)
            exact fairStall.mono
              (fun _ _ hm' => FairInfOften.mono_post h_all_fi hm')
              (fun _ _ hp' => fairProgress.mono
                (fun _ _ hm' => FairInfOften.mono_post h_all_fi hm') hp') hst_m
    refine fairStall.coinduct Z ?_ (Or.inl ⟨t₁, p.2, rfl, ht₁⟩)
    rintro u s₁ (⟨t₂, st₂, rfl, ht₂⟩ | ⟨i, m, k, rfl, hm⟩ | hu)
    · exact h_step_t t₂ s₁ st₂ ht₂
    · rw [fairStall.unfold_eq] at hm
      refine fairStep.induct
        (fun m₁ s₃ => fairStep ewp₂ Acc₂ Fair₂ Q₂ X FP Z
          (m₁ >>= fun (o, st') => .tau (ITree.interpState h (k o) st')) s₃) ?_ hm
      intro m₁ s₃ hm₁
      cases hm_obs : m₁.observe with
      | ret pair =>
        simp only [hm_obs] at hm₁
        rcases pair with ⟨o, st'⟩
        rw [eq_ret_of_observe hm_obs, ret_bind, fairStep.tau_iff]
        rcases hm₁ with hpre | hst_k
        · exact fairStep.mono (fun _ _ h => h) (fun _ _ h => h)
            (fun _ _ h => Or.inr (Or.inr h)) (fairProgress.toFairStep hpre.2)
        · exact h_step_t (k o) s₃ st' hst_k
      | tau m₁' =>
        simp only [hm_obs] at hm₁
        rw [eq_tau_of_observe hm_obs, tau_bind, fairStep.tau_iff]; exact hm₁
      | vis j c =>
        simp only [hm_obs] at hm₁
        rw [eq_vis_of_observe hm_obs, vis_bind, fairStep.vis_iff]
        refine ewp₂.mono (fun o₂ s' hp => ?_) hm₁
        rcases hp with ⟨ha, hfi_m⟩ | ⟨hf, hprog_m⟩ | ⟨hnf, hst_m⟩
        · exact Or.inl ⟨ha, Or.inr ⟨i, c o₂, k, rfl, hfi_m⟩⟩
        · exact Or.inr (Or.inl ⟨hf,
            h_lift_prog i k (fun pair s₂' => Pre (k pair.1) (s₂', pair.2))
              (fun _ _ hp => hp.2) (c o₂) s' hprog_m⟩)
        · exact Or.inr (Or.inr ⟨hnf, Or.inr (Or.inl ⟨i, c o₂, k, rfl, hst_m⟩)⟩)
    · exact fairStep.mono (fun _ _ h => h) (fun _ _ h => h)
        (fun _ _ h => Or.inr (Or.inr h)) (fairProgress.toFairStep hu)
  refine FairInfOften.coinduct X ?_ (Or.inl ⟨t, st, rfl, h_fi⟩)
  rintro u s₀ (⟨t₀, st₀, rfl, ht₀⟩ | ⟨i, m, k, rfl, hm⟩)
  · exact h_main t₀ s₀ st₀ ht₀
  · rw [FairInfOften.unfold_eq] at hm
    exact h_lift_prog i k
      (fun pair s₂' => FairInfOften ewp₁ Acc₁ Fair₁ Q (k pair.1) (s₂', pair.2))
      (fun pair s₂' hk => h_main (k pair.1) s₂' pair.2 hk) m s₀ hm

/-- Re-triggering each request satisfies the link condition of `FairInfOften.interp`. -/
theorem FairInfOften.interp_trigger {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop}
    {t : ITree E R} {Q : R → S → Prop} {s : S}
    (h : FairInfOften ewp AccEdge Fair Q t s) :
    FairInfOften ewp AccEdge Fair Q (ITree.interp (fun i => ITree.trigger i) t) s := by
  refine FairInfOften.interp (fun i => ITree.trigger i) ?_ h
  intro i K4 K3 K2 s₀ hw
  refine (fairStep.vis_iff _ _ _ _ _ _ _ _ _ _).2 (ewp.mono ?_ hw)
  rintro o s' (⟨ha, h4⟩ | ⟨hf, h3⟩ | ⟨hnf, h2⟩)
  · exact Or.inl ⟨ha, FairInfOften.ret (Or.inl h4)⟩
  · exact Or.inr (Or.inl ⟨hf, fairProgress.of_dwp _ (DWP.ret h3)⟩)
  · refine Or.inr (Or.inr ⟨hnf, ?_⟩)
    rw [fairStall.unfold_eq, fairStep.ret_iff]; exact Or.inr h2

/--
**Vacuity warning for edge-local fairness.** A productive tree that never takes
a `Fair` edge satisfies `FairInfOften` for *every* choice of accepting edges:
`□◇ Fair` is simply never triggered. In particular a retry loop that never
issues the fair-able operation (e.g. spins on loads without attempting the CAS)
is not refuted. Specifications should therefore classify as `Fair` every
cooperative environment answer the program could exploit (an
enabledness-based choice `Fair i o s s' := Enabled s` yields strong fairness).
-/
theorem FairInfOften.of_never_fair {ewp : StateEffectWP S E}
    [h_conj : StateEffectWP.Conjunctive ewp]
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {P Q : R → S → Prop}
    {t : ITree E R} {s : S}
    (h_nf : AlwaysStep ewp (fun i o s₀ s' => ¬ Fair i o s₀ s') P t s)
    (h_prod : InfOften ewp (fun _ _ _ _ => True) Q t s) :
    FairInfOften ewp AccEdge Fair Q t s := by
  let X : ITree E R → S → Prop := fun x s₀ =>
    AlwaysStep ewp (fun i o s₁ s' => ¬ Fair i o s₁ s') P x s₀ ∧
      InfOften ewp (fun _ _ _ _ => True) Q x s₀
  refine FairInfOften.coinduct X ?_ ⟨h_nf, h_prod⟩
  intro x s₀ hx
  rw [fairProgress.unfold_eq]
  refine fairStall.coinduct X ?_ hx
  rintro y s₁ ⟨hay, hiy⟩
  refine InfOften.progress_induct
    (fun z s₂ => AlwaysStep ewp (fun i o s₃ s' => ¬ Fair i o s₃ s') P z s₂ →
      fairStep ewp AccEdge Fair Q X (fairProgress ewp AccEdge Fair Q X) X z s₂)
    ?_ hiy hay
  intro z s₂ hz haz
  rw [fairStep.unfold_eq]
  rw [AlwaysStep.unfold_eq] at haz
  cases h_obs : z.observe <;> simp only [h_obs] at hz haz ⊢
  · exact hz
  · exact hz.2 haz
  · exact ewp.mono
      (fun _ _ hp => Or.inr (Or.inr ⟨hp.2.1, hp.2.2, hp.1.1⟩)) (h_conj.conj hz haz)

private def fairIterAux {I : Type u} (ewp : StateEffectWP S E)
    (Fair : (i : E.I) → E.O i → S → S → Prop) (LInv : I → S → Prop)
    (Q : R → S → Prop) (seen : Bool) (t : ITree E (I ⊕ R)) (s : S) : Prop :=
  match t.observe with
  | .ret (.inl next) => seen = true ∧ LInv next s
  | .ret (.inr r) => Q r s
  | .tau t' => fairIterAux ewp Fair LInv Q seen t' s
  | .vis i k =>
    ewp.wp i
      (fun o s' =>
        (Fair i o s s' ∧ DWP ewp (k o) (Sum.elim (fun _ _ => False) Q) s') ∨
        (¬ Fair i o s s' ∧ fairIterAux ewp Fair LInv Q true (k o) s')) s
inductive_fixpoint

/--
Per-iteration obligation of the fair retry-loop rule: after finitely many steps
the iteration either exits with `Q`, or continues with `LInv` after having taken
at least one visible edge (`seen`), and **every fair edge commits the iteration
to exiting** (`DWP` into an `.inr` return).
-/
def fairIter {I : Type u} (ewp : StateEffectWP S E)
    (Fair : (i : E.I) → E.O i → S → S → Prop) (LInv : I → S → Prop)
    (Q : R → S → Prop) (seen : Bool) (t : ITree E (I ⊕ R)) (s : S) : Prop :=
  fairIterAux ewp Fair LInv Q seen t s

theorem fairIter.unfold_eq {I : Type u} (ewp : StateEffectWP S E)
    (Fair : (i : E.I) → E.O i → S → S → Prop) (LInv : I → S → Prop)
    (Q : R → S → Prop) (seen : Bool) (t : ITree E (I ⊕ R)) (s : S) :
    fairIter ewp Fair LInv Q seen t s =
      match t.observe with
      | .ret (.inl next) => seen = true ∧ LInv next s
      | .ret (.inr r) => Q r s
      | .tau t' => fairIter ewp Fair LInv Q seen t' s
      | .vis i k =>
        ewp.wp i
          (fun o s' =>
            (Fair i o s s' ∧ DWP ewp (k o) (Sum.elim (fun _ _ => False) Q) s') ∨
            (¬ Fair i o s s' ∧ fairIter ewp Fair LInv Q true (k o) s')) s :=
  fairIterAux.eq_def ewp Fair LInv Q seen t s

@[simp]
theorem fairIter.vis_iff {I : Type u} (ewp : StateEffectWP S E)
    (Fair : (i : E.I) → E.O i → S → S → Prop) (LInv : I → S → Prop)
    (Q : R → S → Prop) (seen : Bool) (i : E.I) (k : E.O i → ITree E (I ⊕ R))
    (s : S) :
    fairIter ewp Fair LInv Q seen (.vis i k) s ↔
      ewp.wp i
        (fun o s' =>
          (Fair i o s s' ∧ DWP ewp (k o) (Sum.elim (fun _ _ => False) Q) s') ∨
          (¬ Fair i o s s' ∧ fairIter ewp Fair LInv Q true (k o) s')) s := by
  conv => lhs; rw [fairIter.unfold_eq, ITree.observe_vis]

@[simp]
theorem fairIter.ret_inl_iff {I : Type u} (ewp : StateEffectWP S E)
    (Fair : (i : E.I) → E.O i → S → S → Prop) (LInv : I → S → Prop)
    (Q : R → S → Prop) (seen : Bool) (next : I) (s : S) :
    fairIter ewp Fair LInv Q seen (.ret (.inl next)) s ↔ seen = true ∧ LInv next s := by
  conv => lhs; rw [fairIter.unfold_eq, ITree.observe_ret]

@[simp]
theorem fairIter.ret_inr_iff {I : Type u} (ewp : StateEffectWP S E)
    (Fair : (i : E.I) → E.O i → S → S → Prop) (LInv : I → S → Prop)
    (Q : R → S → Prop) (seen : Bool) (r : R) (s : S) :
    fairIter ewp Fair LInv Q seen (.ret (.inr r)) s ↔ Q r s := by
  conv => lhs; rw [fairIter.unfold_eq, ITree.observe_ret]

/-- Case-analysis induction principle for `fairIter` (children keep `fairIter`). -/
theorem fairIter.induct_cases {I : Type u} {ewp : StateEffectWP S E}
    {Fair : (i : E.I) → E.O i → S → S → Prop} {LInv : I → S → Prop}
    {Q : R → S → Prop} (G : Bool → ITree E (I ⊕ R) → S → Prop)
    (h_inl : ∀ x next s₀, x.observe = .ret (.inl next) → LInv next s₀ → G true x s₀)
    (h_inr : ∀ seen x r s₀, x.observe = .ret (.inr r) → Q r s₀ → G seen x s₀)
    (h_tau : ∀ seen x x' s₀, x.observe = .tau x' → G seen x' s₀ → G seen x s₀)
    (h_vis : ∀ seen x (i : E.I) (k : E.O i → ITree E (I ⊕ R)) s₀,
      x.observe = .vis i k →
      ewp.wp i
        (fun o s' =>
          (Fair i o s₀ s' ∧ DWP ewp (k o) (Sum.elim (fun _ _ => False) Q) s') ∨
          (¬ Fair i o s₀ s' ∧ fairIter ewp Fair LInv Q true (k o) s')) s₀ →
      G seen x s₀)
    {seen : Bool} {t : ITree E (I ⊕ R)} {s : S}
    (h : fairIter ewp Fair LInv Q seen t s) : G seen t s := by
  refine (fairIterAux.induct ewp Fair LInv Q
    (fun seen x s₀ => fairIter ewp Fair LInv Q seen x s₀ ∧ G seen x s₀)
    ?_ seen t s h).2
  intro seen x s₀ hx
  cases h_obs : x.observe with
  | ret res =>
    cases res with
    | inl next =>
      simp only [h_obs] at hx
      obtain ⟨rfl, hl⟩ := hx
      refine ⟨?_, h_inl x next s₀ h_obs hl⟩
      rw [fairIter.unfold_eq, h_obs]; exact ⟨rfl, hl⟩
    | inr r =>
      simp only [h_obs] at hx
      refine ⟨?_, h_inr seen x r s₀ h_obs hx⟩
      rw [fairIter.unfold_eq, h_obs]; exact hx
  | tau x' =>
    simp only [h_obs] at hx
    refine ⟨?_, h_tau seen x x' s₀ h_obs hx.2⟩
    rw [fairIter.unfold_eq, h_obs]; exact hx.1
  | vis i k =>
    simp only [h_obs] at hx
    have hw := ewp.mono
      (fun _ _ hp => hp.imp id (And.imp id And.left)) hx
    refine ⟨?_, h_vis seen x i k s₀ h_obs hw⟩
    rw [fairIter.unfold_eq, h_obs]; exact hw

/--
**Fair retry-loop rule** (`Atomic::try_update` under fairness). If every
iteration satisfies `fairIter` (it exits with `Q`, or continues with `LInv`
after at least one *unfair* visible edge, and any fair edge commits it to
exiting), then the loop satisfies the Streett condition `□◇ Fair → ◇ ret Q`
for **any** accepting edges: a fair environment forces termination, an unfair
one at worst keeps it productively retrying.
-/
theorem FairInfOften.iter_fair {I : Type u} {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop}
    (body : I → ITree E (I ⊕ R)) (LInv : I → S → Prop) {Q : R → S → Prop}
    (h_body : ∀ a s₀, LInv a s₀ → fairIter ewp Fair LInv Q false (body a) s₀)
    {init : I} {s : S} (h_init : LInv init s) :
    FairInfOften ewp AccEdge Fair Q (ITree.iter body init) s := by
  let cont : I ⊕ R → ITree E R :=
    Sum.elim (fun next => .tau (ITree.iter body next)) .ret
  let Z : ITree E R → S → Prop := fun u s₀ =>
    ∃ (cur : ITree E (I ⊕ R)) (seen : Bool),
      u = (cur >>= cont) ∧ fairIter ewp Fair LInv Q seen cur s₀
  have h_exit : ∀ (m : ITree E (I ⊕ R)) (s₀ : S),
      DWP ewp m (Sum.elim (fun _ _ => False) Q) s₀ →
      fairProgress ewp AccEdge Fair Q (FairInfOften ewp AccEdge Fair Q)
        (m >>= cont) s₀ := by
    intro m s₀ hm
    refine fairProgress.of_dwp _ (DWP.bind (DWP.mono ?_ hm))
    rintro (next | r) s' hp
    · exact False.elim hp
    · exact DWP.ret hp
  have h_vis : ∀ (i : E.I) (k : E.O i → ITree E (I ⊕ R)) (s₀ : S),
      ewp.wp i
        (fun o s' =>
          (Fair i o s₀ s' ∧ DWP ewp (k o) (Sum.elim (fun _ _ => False) Q) s') ∨
          (¬ Fair i o s₀ s' ∧ fairIter ewp Fair LInv Q true (k o) s')) s₀ →
      fairStep ewp AccEdge Fair Q (FairInfOften ewp AccEdge Fair Q)
        (fairProgress ewp AccEdge Fair Q (FairInfOften ewp AccEdge Fair Q)) Z
        (ITree.vis i k >>= cont) s₀ := by
    intro i k s₀ hw
    rw [vis_bind, fairStep.vis_iff]
    exact ewp.mono (fun o s' hp => hp.elim
      (fun hf => Or.inr (Or.inl ⟨hf.1, h_exit (k o) s' hf.2⟩))
      (fun hn => Or.inr (Or.inr ⟨hn.1, k o, true, rfl, hn.2⟩))) hw
  have h_enter : ∀ (cur : ITree E (I ⊕ R)) (s₀ : S),
      fairIter ewp Fair LInv Q false cur s₀ →
      fairStep ewp AccEdge Fair Q (FairInfOften ewp AccEdge Fair Q)
        (fairProgress ewp AccEdge Fair Q (FairInfOften ewp AccEdge Fair Q)) Z
        (cur >>= cont) s₀ := by
    intro cur s₀ h
    refine fairIter.induct_cases
      (G := fun seen c s₁ => seen = false →
        fairStep ewp AccEdge Fair Q (FairInfOften ewp AccEdge Fair Q)
          (fairProgress ewp AccEdge Fair Q (FairInfOften ewp AccEdge Fair Q)) Z
          (c >>= cont) s₁) ?_ ?_ ?_ ?_ h rfl
    · intro _ _ _ _ _ h_eq; exact Bool.noConfusion h_eq
    · intro _ x r s₁ hx hq _
      rw [eq_ret_of_observe hx, ret_bind]
      exact (fairStep.ret_iff _ _ _ _ _ _ _ r s₁).2 hq
    · intro _ x x' s₁ hx ih hs
      rw [eq_tau_of_observe hx, tau_bind, fairStep.tau_iff]
      exact ih hs
    · intro _ x i k s₁ hx hw _
      rw [eq_vis_of_observe hx]
      exact h_vis i k s₁ hw
  have h_step : ∀ (seen : Bool) (cur : ITree E (I ⊕ R)) (s₀ : S),
      fairIter ewp Fair LInv Q seen cur s₀ →
      fairStep ewp AccEdge Fair Q (FairInfOften ewp AccEdge Fair Q)
        (fairProgress ewp AccEdge Fair Q (FairInfOften ewp AccEdge Fair Q)) Z
        (cur >>= cont) s₀ := by
    intro seen cur s₀ h
    refine fairIter.induct_cases
      (G := fun _ c s₁ =>
        fairStep ewp AccEdge Fair Q (FairInfOften ewp AccEdge Fair Q)
          (fairProgress ewp AccEdge Fair Q (FairInfOften ewp AccEdge Fair Q)) Z
          (c >>= cont) s₁) ?_ ?_ ?_ ?_ h
    · intro x next s₁ hx hl
      rw [eq_ret_of_observe hx, ret_bind]
      show fairStep _ _ _ _ _ _ _ (ITree.tau (ITree.iter body next)) s₁
      rw [fairStep.tau_iff, iter_unfold]
      exact h_enter (body next) s₁ (h_body next s₁ hl)
    · intro _ x r s₁ hx hq
      rw [eq_ret_of_observe hx, ret_bind]
      exact (fairStep.ret_iff _ _ _ _ _ _ _ r s₁).2 hq
    · intro _ x x' s₁ hx ih
      rw [eq_tau_of_observe hx, tau_bind, fairStep.tau_iff]
      exact ih
    · intro _ x i k s₁ hx hw
      rw [eq_vis_of_observe hx]
      exact h_vis i k s₁ hw
  rw [FairInfOften.unfold_eq, fairProgress.unfold_eq]
  refine fairStall.coinduct Z ?_
    ⟨body init, false, iter_unfold body init, h_body init s h_init⟩
  rintro u s₀ ⟨cur, seen, rfl, hc⟩
  exact h_step seen cur s₀ hc

/--
**General well-founded fairness-conditional loop rule** for `ITree.iter` (no
extra fixpoint auxiliary needed). Starting from rank `m : α` and `LInv m a s₀`,
each iteration `body a` satisfies a single 4-level parity `fairStep` obligation:

* zero visible steps (or a `Fair` edge) may return `.inr r` (`Q r s'`) or
  continue `.inl next` with a **strictly smaller** rank `m' < m` (`PostDec`);
* an unfair (`¬ Fair`) visible edge enters `fairStall` and may continue with the
  **same** rank `m` (or strictly smaller) (`PostSame`), while any later `Fair`
  edge in the same iteration still commits to `PostDec`;
* an accepting edge (`AccEdge`) enters `FairInfOften` and resets the rank
  arbitrarily (`∃ m', LInv m' next s'`).

This strictly subsumes single-fair-step termination (`iter_fair`), multi-step
`load` + `cas` iterations, `k`-fair-step convergence, and diverging `-> !` fair
reactive servers (`□◇ Fair → □◇ AccEdge`).
-/
theorem FairInfOften.iter_wf {I : Type u} {α : Type _}
    {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop}
    (lt : α → α → Prop) (h_wf : WellFounded lt)
    (body : I → ITree E (I ⊕ R)) (LInv : α → I → S → Prop)
    {Q : R → S → Prop}
    (h_body : ∀ m a s₀, LInv m a s₀ →
      fairStep ewp AccEdge Fair
        (Sum.elim (fun next s' => ∃ m', lt m' m ∧ LInv m' next s') Q)
        (FairInfOften ewp AccEdge Fair
          (Sum.elim (fun next s' => ∃ m', LInv m' next s') Q))
        (fairProgress ewp AccEdge Fair
          (Sum.elim (fun next s' => ∃ m', lt m' m ∧ LInv m' next s') Q)
          (FairInfOften ewp AccEdge Fair
            (Sum.elim (fun next s' => ∃ m', LInv m' next s') Q)))
        (fairStall ewp AccEdge Fair
          (Sum.elim (fun next s' => LInv m next s' ∨ ∃ m', lt m' m ∧ LInv m' next s') Q)
          (FairInfOften ewp AccEdge Fair
            (Sum.elim (fun next s' => ∃ m', LInv m' next s') Q))
          (fairProgress ewp AccEdge Fair
            (Sum.elim (fun next s' => ∃ m', lt m' m ∧ LInv m' next s') Q)
            (FairInfOften ewp AccEdge Fair
              (Sum.elim (fun next s' => ∃ m', LInv m' next s') Q))))
        (body a) s₀)
    {m : α} {init : I} {s : S} (h_init : LInv m init s) :
    FairInfOften ewp AccEdge Fair Q (ITree.iter body init) s := by
  let cont : I ⊕ R → ITree E R :=
    Sum.elim (fun next => .tau (ITree.iter body next)) .ret
  let PostAny : I ⊕ R → S → Prop :=
    Sum.elim (fun next s' => ∃ m', LInv m' next s') Q
  let X4_body : ITree E (I ⊕ R) → S → Prop :=
    FairInfOften ewp AccEdge Fair PostAny
  let X_out : ITree E R → S → Prop := fun u s₀ =>
    (∃ m' a, u = ITree.iter body a ∧ LInv m' a s₀) ∨
    (∃ cur : ITree E (I ⊕ R), u = (cur >>= cont) ∧ X4_body cur s₀)
  let FP : ITree E R → S → Prop := fairProgress ewp AccEdge Fair Q X_out
  have h_lift_fp : ∀ (P : I ⊕ R → S → Prop),
      (∀ res s', P res s' → FP (cont res) s') →
      ∀ (cur : ITree E (I ⊕ R)) (s₀ : S),
        fairProgress ewp AccEdge Fair P X4_body cur s₀ →
        FP (cur >>= cont) s₀ := by
    intro P hP cur s₀ hcur
    refine fairProgress.induct (fun c s₁ => FP (c >>= cont) s₁) ?_ hcur
    intro c s₁ hc
    dsimp only [FP]
    rw [fairProgress.unfold_eq]
    let Zm : ITree E R → S → Prop := fun u s₂ =>
      (∃ c₂, u = (c₂ >>= cont) ∧
        fairStall ewp AccEdge Fair P X4_body (fun c₃ s₃ => FP (c₃ >>= cont) s₃) c₂ s₂) ∨
      FP u s₂
    refine fairStall.coinduct Zm ?_ (Or.inl ⟨c, rfl, hc⟩)
    rintro u s₂ (⟨c₂, rfl, hc₂⟩ | hu)
    · rw [fairStall.unfold_eq] at hc₂
      refine fairStep.induct
        (fun c₃ s₃ => fairStep ewp AccEdge Fair Q X_out FP Zm (c₃ >>= cont) s₃) ?_ hc₂
      intro c₃ s₃ hc₃
      cases h_obs : c₃.observe with
      | ret res =>
        simp only [h_obs] at hc₃
        rw [eq_ret_of_observe h_obs, ret_bind]
        exact fairStep.mono (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => Or.inr h)
          (fairProgress.toFairStep (hP res s₃ hc₃))
      | tau c₃' =>
        simp only [h_obs] at hc₃
        rw [eq_tau_of_observe h_obs, tau_bind, fairStep.tau_iff]; exact hc₃
      | vis i k =>
        simp only [h_obs] at hc₃
        rw [eq_vis_of_observe h_obs, vis_bind, fairStep.vis_iff]
        refine ewp.mono (fun o s' hp => ?_) hc₃
        rcases hp with ⟨ha, hx4⟩ | ⟨hf, hpre⟩ | ⟨hnf, hst⟩
        · exact Or.inl ⟨ha, Or.inr ⟨k o, rfl, hx4⟩⟩
        · exact Or.inr (Or.inl ⟨hf, hpre⟩)
        · exact Or.inr (Or.inr ⟨hnf, Or.inl ⟨k o, rfl, hst⟩⟩)
    · exact fairStep.mono (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => Or.inr h)
        (fairProgress.toFairStep hu)
  have h_enter : ∀ m a s₀, LInv m a s₀ → FP (ITree.iter body a) s₀ := by
    intro m₀
    refine h_wf.induction (C := fun m => ∀ a s₀, LInv m a s₀ → FP (ITree.iter body a) s₀)
      m₀ ?_
    intro m ih a₀ s₀ hm₀
    let PostDec : I ⊕ R → S → Prop :=
      Sum.elim (fun next s' => ∃ m', lt m' m ∧ LInv m' next s') Q
    let PostSame : I ⊕ R → S → Prop :=
      Sum.elim (fun next s' => LInv m next s' ∨ ∃ m', lt m' m ∧ LInv m' next s') Q
    let X3_body : ITree E (I ⊕ R) → S → Prop :=
      fairProgress ewp AccEdge Fair PostDec X4_body
    let X2_body : ITree E (I ⊕ R) → S → Prop :=
      fairStall ewp AccEdge Fair PostSame X4_body X3_body
    have h_postDec : ∀ res s', PostDec res s' → FP (cont res) s' := by
      rintro (next | r) s' hp
      · obtain ⟨m', hlt, hm'⟩ := hp
        dsimp only [cont, Sum.elim, FP]
        rw [fairProgress.iff_fairStep, fairStep.tau_iff]
        exact fairProgress.toFairStep (ih m' hlt next s' hm')
      · dsimp only [cont, Sum.elim, FP]
        rw [fairProgress.iff_fairStep, fairStep.ret_iff]; exact hp
    have h_x3 : ∀ cur s₁, X3_body cur s₁ → FP (cur >>= cont) s₁ :=
      fun cur s₁ hcur => h_lift_fp PostDec h_postDec cur s₁ hcur
    let Z_m : ITree E R → S → Prop := fun u s₁ =>
      (∃ a, u = ITree.iter body a ∧ LInv m a s₁) ∨
      (∃ cur : ITree E (I ⊕ R), u = (cur >>= cont) ∧ X2_body cur s₁) ∨
      FP u s₁
    have h_disj1 : ∀ a s₁, LInv m a s₁ →
        fairStep ewp AccEdge Fair Q X_out FP Z_m (ITree.iter body a) s₁ := by
      intro a s₁ ha
      rw [iter_unfold]
      refine fairStep.induct
        (fun cur s₂ => fairStep ewp AccEdge Fair Q X_out FP Z_m (cur >>= cont) s₂)
        ?_ (h_body m a s₁ ha)
      intro cur s₂ hcur
      cases h_obs : cur.observe with
      | ret res =>
        simp only [h_obs] at hcur
        rw [eq_ret_of_observe h_obs, ret_bind]
        exact fairStep.mono (fun _ _ h => h) (fun _ _ h => h)
          (fun _ _ h => Or.inr (Or.inr h)) (fairProgress.toFairStep (h_postDec res s₂ hcur))
      | tau cur' =>
        simp only [h_obs] at hcur
        rw [eq_tau_of_observe h_obs, tau_bind, fairStep.tau_iff]; exact hcur
      | vis i k =>
        simp only [h_obs] at hcur
        rw [eq_vis_of_observe h_obs, vis_bind, fairStep.vis_iff]
        refine ewp.mono (fun o s' hp => ?_) hcur
        rcases hp with ⟨hacc, hx4⟩ | ⟨hf, hx3⟩ | ⟨hnf, hx2⟩
        · exact Or.inl ⟨hacc, Or.inr ⟨k o, rfl, hx4⟩⟩
        · exact Or.inr (Or.inl ⟨hf, h_x3 (k o) s' hx3⟩)
        · exact Or.inr (Or.inr ⟨hnf, Or.inr (Or.inl ⟨k o, rfl, hx2⟩)⟩)
    dsimp only [FP]
    rw [fairProgress.unfold_eq]
    refine fairStall.coinduct Z_m ?_ (Or.inl ⟨a₀, rfl, hm₀⟩)
    rintro u s₁ (⟨a, rfl, ha⟩ | ⟨cur, rfl, hcur⟩ | hu)
    · exact h_disj1 a s₁ ha
    · dsimp only [X2_body] at hcur
      rw [fairStall.unfold_eq] at hcur
      refine fairStep.induct
        (fun c s₂ => fairStep ewp AccEdge Fair Q X_out FP Z_m (c >>= cont) s₂) ?_ hcur
      intro c s₂ hc
      cases h_obs : c.observe with
      | ret res =>
        simp only [h_obs] at hc
        rw [eq_ret_of_observe h_obs, ret_bind]
        cases res with
        | inl next =>
          dsimp only [cont, Sum.elim]
          rw [fairStep.tau_iff]
          rcases hc with hsame | ⟨m', hlt, hm'⟩
          · exact h_disj1 next s₂ hsame
          · exact fairStep.mono (fun _ _ h => h) (fun _ _ h => h)
              (fun _ _ h => Or.inr (Or.inr h)) (fairProgress.toFairStep (ih m' hlt next s₂ hm'))
        | inr r =>
          dsimp only [cont, Sum.elim]
          rw [fairStep.ret_iff]; exact hc
      | tau c' =>
        simp only [h_obs] at hc
        rw [eq_tau_of_observe h_obs, tau_bind, fairStep.tau_iff]; exact hc
      | vis i k =>
        simp only [h_obs] at hc
        rw [eq_vis_of_observe h_obs, vis_bind, fairStep.vis_iff]
        refine ewp.mono (fun o s' hp => ?_) hc
        rcases hp with ⟨hacc, hx4⟩ | ⟨hf, hx3⟩ | ⟨hnf, hx2⟩
        · exact Or.inl ⟨hacc, Or.inr ⟨k o, rfl, hx4⟩⟩
        · exact Or.inr (Or.inl ⟨hf, h_x3 (k o) s' hx3⟩)
        · exact Or.inr (Or.inr ⟨hnf, Or.inr (Or.inl ⟨k o, rfl, hx2⟩)⟩)
    · exact fairStep.mono (fun _ _ h => h) (fun _ _ h => h)
        (fun _ _ h => Or.inr (Or.inr h)) (fairProgress.toFairStep hu)
  refine FairInfOften.coinduct X_out ?_ (Or.inl ⟨m, init, rfl, h_init⟩)
  rintro u s₀ (⟨m', a, rfl, hm'⟩ | ⟨cur, rfl, hcur⟩)
  · exact h_enter m' a s₀ hm'
  · dsimp only [X4_body] at hcur
    rw [FairInfOften.unfold_eq] at hcur
    refine h_lift_fp PostAny ?_ cur s₀ hcur
    rintro (next | r) s' hp
    · obtain ⟨m', hm'⟩ := hp
      dsimp only [cont, Sum.elim, FP]
      rw [fairProgress.iff_fairStep, fairStep.tau_iff]
      exact fairProgress.toFairStep (h_enter m' next s' hm')
    · dsimp only [cont, Sum.elim, FP]
      rw [fairProgress.iff_fairStep, fairStep.ret_iff]; exact hp

/-- `Nat`-ranked fairness-conditional loop rule for `ITree.iter`. -/
theorem FairInfOften.iter_ranked {I : Type u} {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop}
    (body : I → ITree E (I ⊕ R)) (LInv : Nat → I → S → Prop)
    {Q : R → S → Prop}
    (h_body : ∀ n a s₀, LInv n a s₀ →
      fairStep ewp AccEdge Fair
        (Sum.elim (fun next s' => ∃ m, m < n ∧ LInv m next s') Q)
        (FairInfOften ewp AccEdge Fair
          (Sum.elim (fun next s' => ∃ m, LInv m next s') Q))
        (fairProgress ewp AccEdge Fair
          (Sum.elim (fun next s' => ∃ m, m < n ∧ LInv m next s') Q)
          (FairInfOften ewp AccEdge Fair
            (Sum.elim (fun next s' => ∃ m, LInv m next s') Q)))
        (fairStall ewp AccEdge Fair
          (Sum.elim (fun next s' => LInv n next s' ∨ ∃ m, m < n ∧ LInv m next s') Q)
          (FairInfOften ewp AccEdge Fair
            (Sum.elim (fun next s' => ∃ m, LInv m next s') Q))
          (fairProgress ewp AccEdge Fair
            (Sum.elim (fun next s' => ∃ m, m < n ∧ LInv m next s') Q)
            (FairInfOften ewp AccEdge Fair
              (Sum.elim (fun next s' => ∃ m, LInv m next s') Q))))
        (body a) s₀)
    {n : Nat} {init : I} {s : S} (h_init : LInv n init s) :
    FairInfOften ewp AccEdge Fair Q (ITree.iter body init) s :=
  FairInfOften.iter_wf (fun a b : Nat => a < b) Nat.lt_wfRel.wf body LInv
    h_body h_init

private theorem fairInfOften_map_inl {I : Type u} {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop}
    {LInv : I → S → Prop} {Q : R → S → Prop} {t : ITree E I} {s : S}
    (h : FairInfOften ewp AccEdge Fair LInv t s) :
    FairInfOften ewp AccEdge Fair (Sum.elim LInv Q)
      (Sum.inl <$> t : ITree E (I ⊕ R)) s := by
  have h_eq : (Sum.inl <$> t : ITree E (I ⊕ R)) =
      (t >>= fun a => ITree.ret (Sum.inl a)) := rfl
  rw [h_eq]
  refine FairInfOften.bind (FairInfOften.mono_post ?_ h)
  intro a s' ha
  exact FairInfOften.ret ha

private theorem fairStep_map_inl {I : Type u} {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop}
    {P₁ P₂ LInv : I → S → Prop} {Q : R → S → Prop}
    {t : ITree E I} {s : S}
    (h : fairStep ewp AccEdge Fair P₁
      (FairInfOften ewp AccEdge Fair LInv)
      (fairProgress ewp AccEdge Fair P₁ (FairInfOften ewp AccEdge Fair LInv))
      (fairStall ewp AccEdge Fair P₂
        (FairInfOften ewp AccEdge Fair LInv)
        (fairProgress ewp AccEdge Fair P₁ (FairInfOften ewp AccEdge Fair LInv)))
      t s) :
    fairStep ewp AccEdge Fair (Sum.elim P₁ Q)
      (FairInfOften ewp AccEdge Fair (Sum.elim LInv Q))
      (fairProgress ewp AccEdge Fair (Sum.elim P₁ Q)
        (FairInfOften ewp AccEdge Fair (Sum.elim LInv Q)))
      (fairStall ewp AccEdge Fair (Sum.elim P₂ Q)
        (FairInfOften ewp AccEdge Fair (Sum.elim LInv Q))
        (fairProgress ewp AccEdge Fair (Sum.elim P₁ Q)
          (FairInfOften ewp AccEdge Fair (Sum.elim LInv Q))))
      (Sum.inl <$> t : ITree E (I ⊕ R)) s := by
  let f : I → ITree E (I ⊕ R) := fun a => ITree.ret (Sum.inl a)
  have h_eq : ∀ u : ITree E I, (Sum.inl <$> u : ITree E (I ⊕ R)) = (u >>= f) :=
    fun _ => rfl
  have h_prog : ∀ (P : I → S → Prop) (u : ITree E I) (s₀ : S),
      fairProgress ewp AccEdge Fair P (FairInfOften ewp AccEdge Fair LInv) u s₀ →
      fairProgress ewp AccEdge Fair (Sum.elim P Q)
        (FairInfOften ewp AccEdge Fair (Sum.elim LInv Q)) (u >>= f) s₀ := by
    intro P u s₀ hu
    refine fairProgress.induct
      (fun x s₁ => fairProgress ewp AccEdge Fair (Sum.elim P Q)
        (FairInfOften ewp AccEdge Fair (Sum.elim LInv Q)) (x >>= f) s₁) ?_ hu
    intro x s₁ hx
    rw [fairProgress.unfold_eq]
    let Z : ITree E (I ⊕ R) → S → Prop := fun v s₂ =>
      ∃ y, v = (y >>= f) ∧
        fairStall ewp AccEdge Fair P (FairInfOften ewp AccEdge Fair LInv)
          (fun w s₃ => fairProgress ewp AccEdge Fair (Sum.elim P Q)
            (FairInfOften ewp AccEdge Fair (Sum.elim LInv Q)) (w >>= f) s₃) y s₂
    refine fairStall.coinduct Z ?_ ⟨x, rfl, hx⟩
    rintro v s₂ ⟨y, rfl, hy⟩
    rw [fairStall.unfold_eq] at hy
    refine fairStep.induct
      (fun w s₃ => fairStep ewp AccEdge Fair (Sum.elim P Q)
        (FairInfOften ewp AccEdge Fair (Sum.elim LInv Q))
        (fairProgress ewp AccEdge Fair (Sum.elim P Q)
          (FairInfOften ewp AccEdge Fair (Sum.elim LInv Q)))
        Z (w >>= f) s₃) ?_ hy
    intro w s₃ hw
    cases h_obs : w.observe with
    | ret a =>
      simp only [h_obs] at hw
      rw [eq_ret_of_observe h_obs, ret_bind]; dsimp only [f]
      rw [fairStep.ret_iff]; exact hw
    | tau w' =>
      simp only [h_obs] at hw
      rw [eq_tau_of_observe h_obs, tau_bind, fairStep.tau_iff]; exact hw
    | vis i k =>
      simp only [h_obs] at hw
      rw [eq_vis_of_observe h_obs, vis_bind, fairStep.vis_iff]
      refine ewp.mono (fun o s' hp => ?_) hw
      rcases hp with ⟨ha, hfi⟩ | ⟨hf, hpre⟩ | ⟨hnf, hst⟩
      · exact Or.inl ⟨ha, fairInfOften_map_inl hfi⟩
      · exact Or.inr (Or.inl ⟨hf, hpre⟩)
      · exact Or.inr (Or.inr ⟨hnf, ⟨k o, rfl, hst⟩⟩)
  have h_stall : ∀ (u : ITree E I) (s₀ : S),
      fairStall ewp AccEdge Fair P₂
        (FairInfOften ewp AccEdge Fair LInv)
        (fairProgress ewp AccEdge Fair P₁ (FairInfOften ewp AccEdge Fair LInv)) u s₀ →
      fairStall ewp AccEdge Fair (Sum.elim P₂ Q)
        (FairInfOften ewp AccEdge Fair (Sum.elim LInv Q))
        (fairProgress ewp AccEdge Fair (Sum.elim P₁ Q)
          (FairInfOften ewp AccEdge Fair (Sum.elim LInv Q))) (u >>= f) s₀ := by
    intro u s₀ hu
    let Z : ITree E (I ⊕ R) → S → Prop := fun v s₁ =>
      ∃ y, v = (y >>= f) ∧
        fairStall ewp AccEdge Fair P₂
          (FairInfOften ewp AccEdge Fair LInv)
          (fairProgress ewp AccEdge Fair P₁ (FairInfOften ewp AccEdge Fair LInv)) y s₁
    refine fairStall.coinduct Z ?_ ⟨u, rfl, hu⟩
    rintro v s₁ ⟨y, rfl, hy⟩
    rw [fairStall.unfold_eq] at hy
    refine fairStep.induct
      (fun w s₂ => fairStep ewp AccEdge Fair (Sum.elim P₂ Q)
        (FairInfOften ewp AccEdge Fair (Sum.elim LInv Q))
        (fairProgress ewp AccEdge Fair (Sum.elim P₁ Q)
          (FairInfOften ewp AccEdge Fair (Sum.elim LInv Q)))
        Z (w >>= f) s₂) ?_ hy
    intro w s₂ hw
    cases h_obs : w.observe with
    | ret a =>
      simp only [h_obs] at hw
      rw [eq_ret_of_observe h_obs, ret_bind]; dsimp only [f]
      rw [fairStep.ret_iff]; exact hw
    | tau w' =>
      simp only [h_obs] at hw
      rw [eq_tau_of_observe h_obs, tau_bind, fairStep.tau_iff]; exact hw
    | vis i k =>
      simp only [h_obs] at hw
      rw [eq_vis_of_observe h_obs, vis_bind, fairStep.vis_iff]
      refine ewp.mono (fun o s' hp => ?_) hw
      rcases hp with ⟨ha, hfi⟩ | ⟨hf, hp1⟩ | ⟨hnf, hst⟩
      · exact Or.inl ⟨ha, fairInfOften_map_inl hfi⟩
      · exact Or.inr (Or.inl ⟨hf, h_prog P₁ (k o) s' hp1⟩)
      · exact Or.inr (Or.inr ⟨hnf, ⟨k o, rfl, hst⟩⟩)
  rw [h_eq t]
  refine fairStep.induct
    (fun w s₀ => fairStep ewp AccEdge Fair (Sum.elim P₁ Q)
      (FairInfOften ewp AccEdge Fair (Sum.elim LInv Q))
      (fairProgress ewp AccEdge Fair (Sum.elim P₁ Q)
        (FairInfOften ewp AccEdge Fair (Sum.elim LInv Q)))
      (fairStall ewp AccEdge Fair (Sum.elim P₂ Q)
        (FairInfOften ewp AccEdge Fair (Sum.elim LInv Q))
        (fairProgress ewp AccEdge Fair (Sum.elim P₁ Q)
          (FairInfOften ewp AccEdge Fair (Sum.elim LInv Q))))
      (w >>= f) s₀) ?_ h
  intro w s₀ hw
  cases h_obs : w.observe with
  | ret a =>
    simp only [h_obs] at hw
    rw [eq_ret_of_observe h_obs, ret_bind]; dsimp only [f]
    rw [fairStep.ret_iff]; exact hw
  | tau w' =>
    simp only [h_obs] at hw
    rw [eq_tau_of_observe h_obs, tau_bind, fairStep.tau_iff]; exact hw
  | vis i k =>
    simp only [h_obs] at hw
    rw [eq_vis_of_observe h_obs, vis_bind, fairStep.vis_iff]
    refine ewp.mono (fun o s' hp => ?_) hw
    rcases hp with ⟨ha, hfi⟩ | ⟨hf, hp1⟩ | ⟨hnf, hst⟩
    · exact Or.inl ⟨ha, fairInfOften_map_inl hfi⟩
    · exact Or.inr (Or.inl ⟨hf, h_prog P₁ (k o) s' hp1⟩)
    · exact Or.inr (Or.inr ⟨hnf, h_stall (k o) s' hst⟩)

/--
**Well-founded fairness-conditional diverging `-> !` reactive loop rule**:
verifies BOTH `Always` safety and `FairInfOften` Streett liveness
(`□◇ Fair → □◇ AccEdge`) on a non-returning `divergingLoop : ITree E PEmpty`.
-/
theorem fair_diverging_loop_wf {I : Type u} {α : Type _}
    {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Inv : S → Prop}
    (lt : α → α → Prop) (h_wf : WellFounded lt)
    (body : I → ITree E I) (LInv : α → I → S → Prop)
    (h_safe : ∀ m a s₀, LInv m a s₀ →
      Always ewp Inv (fun next s' => ∃ m', LInv m' next s') (body a) s₀)
    (h_live : ∀ m a s₀, LInv m a s₀ →
      fairStep ewp AccEdge Fair
        (fun next s' => ∃ m', lt m' m ∧ LInv m' next s')
        (FairInfOften ewp AccEdge Fair (fun next s' => ∃ m', LInv m' next s'))
        (fairProgress ewp AccEdge Fair
          (fun next s' => ∃ m', lt m' m ∧ LInv m' next s')
          (FairInfOften ewp AccEdge Fair (fun next s' => ∃ m', LInv m' next s')))
        (fairStall ewp AccEdge Fair
          (fun next s' => LInv m next s' ∨ ∃ m', lt m' m ∧ LInv m' next s')
          (FairInfOften ewp AccEdge Fair (fun next s' => ∃ m', LInv m' next s'))
          (fairProgress ewp AccEdge Fair
            (fun next s' => ∃ m', lt m' m ∧ LInv m' next s')
            (FairInfOften ewp AccEdge Fair (fun next s' => ∃ m', LInv m' next s'))))
        (body a) s₀)
    {m : α} {init : I} {s : S} (h_init : LInv m init s)
    (Q : PEmpty.{u + 1} → S → Prop) :
    Always ewp Inv Q (divergingLoop body init) s ∧
      FairInfOften ewp AccEdge Fair Q (divergingLoop body init) s :=
  ⟨always_divergingLoop body (fun a s' => ∃ m', LInv m' a s')
     (fun a s₀ ⟨m', hm'⟩ => h_safe m' a s₀ hm') ⟨m, h_init⟩ Q,
   FairInfOften.iter_wf lt h_wf _ LInv
     (fun m a s₀ hm => fairStep_map_inl (h_live m a s₀ hm)) h_init⟩

/--
**Single-fair-step diverging `-> !` reactive loop rule**: every fair step
commits the current iteration to taking an accepting edge (e.g., a reactive CAS
service loop where every winning CAS is an accepting commit).
-/
theorem fair_diverging_loop_rule {I : Type u} {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Inv : S → Prop}
    (body : I → ITree E I) (LInv : I → S → Prop)
    (h_safe : ∀ a s₀, LInv a s₀ → Always ewp Inv LInv (body a) s₀)
    (h_live : ∀ a s₀, LInv a s₀ →
      fairStep ewp AccEdge Fair (fun _ _ => False)
        (FairInfOften ewp AccEdge Fair LInv)
        (fairProgress ewp AccEdge Fair (fun _ _ => False)
          (FairInfOften ewp AccEdge Fair LInv))
        (fairStall ewp AccEdge Fair LInv
          (FairInfOften ewp AccEdge Fair LInv)
          (fairProgress ewp AccEdge Fair (fun _ _ => False)
            (FairInfOften ewp AccEdge Fair LInv)))
        (body a) s₀)
    {init : I} {s : S} (h_init : LInv init s)
    (Q : PEmpty.{u + 1} → S → Prop) :
    Always ewp Inv Q (divergingLoop body init) s ∧
      FairInfOften ewp AccEdge Fair Q (divergingLoop body init) s := by
  refine fair_diverging_loop_wf (α := PUnit.{1}) (fun _ _ => False)
    ⟨fun u => Acc.intro u (fun _ hf => False.elim hf)⟩ body (fun _ a s' => LInv a s')
    (fun _ a s₀ ha => Always.mono (fun _ h => h) (fun _ _ hl => ⟨PUnit.unit, hl⟩)
      (h_safe a s₀ ha))
    ?_ (m := PUnit.unit) h_init Q
  intro _ a s₀ ha
  have h1 := h_live a s₀ ha
  have h_fi : ∀ x s', FairInfOften ewp AccEdge Fair LInv x s' →
      FairInfOften ewp AccEdge Fair (fun next s'' => ∃ _ : PUnit.{1}, LInv next s'') x s' :=
    fun _ _ hx => FairInfOften.mono_post (fun _ _ hl => ⟨PUnit.unit, hl⟩) hx
  have h_fp : ∀ x s',
      fairProgress ewp AccEdge Fair (fun _ _ => False) (FairInfOften ewp AccEdge Fair LInv) x s' →
      fairProgress ewp AccEdge Fair
        (fun next s'' => ∃ m' : PUnit.{1}, False ∧ LInv next s'')
        (FairInfOften ewp AccEdge Fair (fun next s'' => ∃ _ : PUnit.{1}, LInv next s'')) x s' := by
    intro x s' hx
    refine fairProgress.induct
      (fun y s₁ => fairProgress ewp AccEdge Fair
        (fun next s'' => ∃ m' : PUnit.{1}, False ∧ LInv next s'')
        (FairInfOften ewp AccEdge Fair (fun next s'' => ∃ _ : PUnit.{1}, LInv next s'')) y s₁)
      ?_ hx
    intro y s₁ hy
    rw [fairProgress.unfold_eq]
    refine fairStall.coinduct
      (fun z s₂ => fairStall ewp AccEdge Fair (fun _ _ => False)
        (FairInfOften ewp AccEdge Fair LInv)
        (fun w s₃ => fairProgress ewp AccEdge Fair
          (fun next s'' => ∃ m' : PUnit.{1}, False ∧ LInv next s'')
          (FairInfOften ewp AccEdge Fair (fun next s'' => ∃ _ : PUnit.{1}, LInv next s'')) w s₃)
        z s₂) ?_ hy
    intro z s₂ hz
    rw [fairStall.unfold_eq] at hz
    refine fairStep.induct
      (fun w s₃ => fairStep ewp AccEdge Fair
        (fun next s'' => ∃ m' : PUnit.{1}, False ∧ LInv next s'')
        (FairInfOften ewp AccEdge Fair (fun next s'' => ∃ _ : PUnit.{1}, LInv next s''))
        (fairProgress ewp AccEdge Fair
          (fun next s'' => ∃ m' : PUnit.{1}, False ∧ LInv next s'')
          (FairInfOften ewp AccEdge Fair (fun next s'' => ∃ _ : PUnit.{1}, LInv next s'')))
        (fun v s₄ => fairStall ewp AccEdge Fair (fun _ _ => False)
          (FairInfOften ewp AccEdge Fair LInv)
          (fun w s₃ => fairProgress ewp AccEdge Fair
            (fun next s'' => ∃ m' : PUnit.{1}, False ∧ LInv next s'')
            (FairInfOften ewp AccEdge Fair (fun next s'' => ∃ _ : PUnit.{1}, LInv next s'')) w s₃)
          v s₄) w s₃) ?_ hz
    intro w s₃ hw
    rw [fairStep.unfold_eq]
    cases h_obs : w.observe with
    | ret _ => simp only [h_obs] at hw
    | tau _ => simp only [h_obs] at hw; exact hw
    | vis _ _ =>
      simp only [h_obs] at hw
      exact ewp.mono (fun _ _ hp => hp.imp (And.imp id (h_fi _ _)) id) hw
  have h_st : ∀ x s',
      fairStall ewp AccEdge Fair LInv (FairInfOften ewp AccEdge Fair LInv)
        (fairProgress ewp AccEdge Fair (fun _ _ => False) (FairInfOften ewp AccEdge Fair LInv))
        x s' →
      fairStall ewp AccEdge Fair
        (fun next s'' => LInv next s'' ∨ ∃ m' : PUnit.{1}, False ∧ LInv next s'')
        (FairInfOften ewp AccEdge Fair (fun next s'' => ∃ _ : PUnit.{1}, LInv next s''))
        (fairProgress ewp AccEdge Fair
          (fun next s'' => ∃ m' : PUnit.{1}, False ∧ LInv next s'')
          (FairInfOften ewp AccEdge Fair (fun next s'' => ∃ _ : PUnit.{1}, LInv next s'')))
        x s' := by
    intro x s' hx
    refine fairStall.coinduct
      (fun y s₁ => fairStall ewp AccEdge Fair LInv (FairInfOften ewp AccEdge Fair LInv)
        (fairProgress ewp AccEdge Fair (fun _ _ => False) (FairInfOften ewp AccEdge Fair LInv))
        y s₁) ?_ hx
    intro y s₁ hy
    rw [fairStall.unfold_eq] at hy
    refine fairStep.induct
      (fun w s₂ => fairStep ewp AccEdge Fair
        (fun next s'' => LInv next s'' ∨ ∃ m' : PUnit.{1}, False ∧ LInv next s'')
        (FairInfOften ewp AccEdge Fair (fun next s'' => ∃ _ : PUnit.{1}, LInv next s''))
        (fairProgress ewp AccEdge Fair
          (fun next s'' => ∃ m' : PUnit.{1}, False ∧ LInv next s'')
          (FairInfOften ewp AccEdge Fair (fun next s'' => ∃ _ : PUnit.{1}, LInv next s'')))
        (fun v s₃ => fairStall ewp AccEdge Fair LInv (FairInfOften ewp AccEdge Fair LInv)
          (fairProgress ewp AccEdge Fair (fun _ _ => False) (FairInfOften ewp AccEdge Fair LInv))
          v s₃) w s₂) ?_ hy
    intro w s₂ hw
    rw [fairStep.unfold_eq]
    cases h_obs : w.observe <;> simp only [h_obs] at hw ⊢
    · exact Or.inl hw
    · exact hw
    · exact ewp.mono
        (fun _ _ hp => hp.imp (And.imp id (h_fi _ _)) (Or.imp (And.imp id (h_fp _ _)) id)) hw
  refine fairStep.induct
    (fun w s₁ => fairStep ewp AccEdge Fair
      (fun next s'' => ∃ m' : PUnit.{1}, False ∧ LInv next s'')
      (FairInfOften ewp AccEdge Fair (fun next s'' => ∃ _ : PUnit.{1}, LInv next s''))
      (fairProgress ewp AccEdge Fair
        (fun next s'' => ∃ m' : PUnit.{1}, False ∧ LInv next s'')
        (FairInfOften ewp AccEdge Fair (fun next s'' => ∃ _ : PUnit.{1}, LInv next s'')))
      (fairStall ewp AccEdge Fair
        (fun next s'' => LInv next s'' ∨ ∃ m' : PUnit.{1}, False ∧ LInv next s'')
        (FairInfOften ewp AccEdge Fair (fun next s'' => ∃ _ : PUnit.{1}, LInv next s''))
        (fairProgress ewp AccEdge Fair
          (fun next s'' => ∃ m' : PUnit.{1}, False ∧ LInv next s'')
          (FairInfOften ewp AccEdge Fair (fun next s'' => ∃ _ : PUnit.{1}, LInv next s''))))
      w s₁) ?_ h1
  intro w s₁ hw
  rw [fairStep.unfold_eq]
  cases h_obs : w.observe with
  | ret _ => simp only [h_obs] at hw
  | tau _ => simp only [h_obs] at hw; exact hw
  | vis _ _ =>
    simp only [h_obs] at hw
    exact ewp.mono
      (fun _ _ hp => hp.imp (And.imp id (h_fi _ _))
        (Or.imp (And.imp id (h_fp _ _)) (And.imp id (h_st _ _)))) hw

/-- `Nat`-ranked fairness-conditional diverging `-> !` reactive loop rule. -/
theorem fair_diverging_loop_ranked {I : Type u} {ewp : StateEffectWP S E}
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {Inv : S → Prop}
    (body : I → ITree E I) (LInv : Nat → I → S → Prop)
    (h_safe : ∀ n a s₀, LInv n a s₀ →
      Always ewp Inv (fun next s' => ∃ m, LInv m next s') (body a) s₀)
    (h_live : ∀ n a s₀, LInv n a s₀ →
      fairStep ewp AccEdge Fair
        (fun next s' => ∃ m, m < n ∧ LInv m next s')
        (FairInfOften ewp AccEdge Fair (fun next s' => ∃ m, LInv m next s'))
        (fairProgress ewp AccEdge Fair
          (fun next s' => ∃ m, m < n ∧ LInv m next s')
          (FairInfOften ewp AccEdge Fair (fun next s' => ∃ m, LInv m next s')))
        (fairStall ewp AccEdge Fair
          (fun next s' => LInv n next s' ∨ ∃ m, m < n ∧ LInv m next s')
          (FairInfOften ewp AccEdge Fair (fun next s' => ∃ m, LInv m next s'))
          (fairProgress ewp AccEdge Fair
            (fun next s' => ∃ m, m < n ∧ LInv m next s')
            (FairInfOften ewp AccEdge Fair (fun next s' => ∃ m, LInv m next s'))))
        (body a) s₀)
    {n : Nat} {init : I} {s : S} (h_init : LInv n init s)
    (Q : PEmpty.{u + 1} → S → Prop) :
    Always ewp Inv Q (divergingLoop body init) s ∧
      FairInfOften ewp AccEdge Fair Q (divergingLoop body init) s :=
  fair_diverging_loop_wf (fun a b : Nat => a < b) Nat.lt_wfRel.wf body LInv
    h_safe h_live h_init Q

end FairInfOften

/-! #### `FairBuchiSat`, Operational Adequacy, and Exact Streett Stream Adequacy -/

section FairBuchiSat

variable {S QState : Type u} {E : Effect.{u}} {R : Type u}

/-- Fairness edge predicate lifted to the product state `QState × S`. -/
def BuchiSpec.fairEdge (_spec : BuchiSpec S QState E R)
    (fair : QState → (i : E.I) → E.O i → S → S → QState → Prop) :
    (i : E.I) → E.O i → QState × S → QState × S → Prop :=
  fun i o qs qs' => fair qs.1 i o qs.2 qs'.2 qs'.1

/--
`FairBuchiSat spec fair t q₀ s₀`: fairness-conditional Streett satisfaction of
a shallow Büchi monitor `spec`, unifying `Always` safety, `FairInfOften` Streett
liveness (`□◇ fair → □◇ accept`) along `spec.monitorWP`, and `terminal` on
finite runs.
-/
def FairBuchiSat (spec : BuchiSpec S QState E R)
    (fair : QState → (i : E.I) → E.O i → S → S → QState → Prop)
    (t : ITree E R) (q₀ : QState) (s₀ : S) : Prop :=
  Always spec.prodWP spec.invPred spec.terminalPost t (q₀, s₀) ∧
    FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
      spec.terminalPost t (q₀, s₀)

/-- Because liveness uses `spec.monitorWP`, the safety conjunct is derivable. -/
theorem fairBuchiSat_iff_fairInfOften (spec : BuchiSpec S QState E R)
    (fair : QState → (i : E.I) → E.O i → S → S → QState → Prop)
    (t : ITree E R) (q₀ : QState) (s₀ : S) :
    FairBuchiSat spec fair t q₀ s₀ ↔
      spec.inv q₀ s₀ ∧
        FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
          spec.terminalPost t (q₀, s₀) := by
  constructor
  · intro h; exact ⟨h.1.inv, h.2⟩
  · rintro ⟨hi, hl⟩
    exact ⟨(always_iff_dwlp_guard spec.prodWP spec.invPred spec.terminalPost
      t (q₀, s₀)).2 ⟨hi, hl.toDWLP⟩, hl⟩

/-- When every monitor step is fair, `FairBuchiSat` collapses identically to `BuchiSat`. -/
theorem fairBuchiSat_true_iff_buchiSat (spec : BuchiSpec S QState E R)
    (t : ITree E R) (q₀ : QState) (s₀ : S) :
    FairBuchiSat spec (fun _ _ _ _ _ _ => True) t q₀ s₀ ↔
      BuchiSat spec t q₀ s₀ := by
  rw [fairBuchiSat_iff_fairInfOften, buchiSat_iff_infOften]
  exact and_congr_right fun _ =>
    fairInfOften_true_iff_infOften spec.monitorWP spec.acceptEdge spec.terminalPost t (q₀, s₀)

/-- Every `BuchiSat` proof implies `FairBuchiSat` for any fairness predicate. -/
theorem BuchiSat.toFairBuchiSat {spec : BuchiSpec S QState E R}
    (fair : QState → (i : E.I) → E.O i → S → S → QState → Prop)
    {t : ITree E R} {q₀ : QState} {s₀ : S} (h : BuchiSat spec t q₀ s₀) :
    FairBuchiSat spec fair t q₀ s₀ :=
  ⟨h.1, h.2.toFairInfOften (spec.fairEdge fair)⟩

/-- Unconditional `spin` refutation for `FairBuchiSat`. -/
theorem not_fairBuchiSat_spin {spec : BuchiSpec S QState E R}
    {fair : QState → (i : E.I) → E.O i → S → S → QState → Prop}
    {q₀ : QState} {s₀ : S} :
    ¬ FairBuchiSat spec fair (ITree.spin (E := E) (R := R)) q₀ s₀ :=
  fun h => not_fairInfOften_spin h.2

/-- Total correctness along `spec.monitorWP` implies `FairBuchiSat`. -/
theorem fairBuchiSat_of_dwp {spec : BuchiSpec S QState E R}
    (fair : QState → (i : E.I) → E.O i → S → S → QState → Prop)
    {t : ITree E R} {q₀ : QState} {s₀ : S} (h_inv : spec.inv q₀ s₀)
    (h : DWP spec.monitorWP t spec.terminalPost (q₀, s₀)) :
    FairBuchiSat spec fair t q₀ s₀ :=
  (fairBuchiSat_iff_fairInfOften spec fair t q₀ s₀).2
    ⟨h_inv, fairInfOften_of_dwp spec.acceptEdge (spec.fairEdge fair) h⟩

@[simp]
theorem FairBuchiSat.ret_iff (spec : BuchiSpec S QState E R)
    (fair : QState → (i : E.I) → E.O i → S → S → QState → Prop)
    (r : R) (q₀ : QState) (s₀ : S) :
    FairBuchiSat spec fair (.ret r) q₀ s₀ ↔ spec.inv q₀ s₀ ∧ spec.terminal q₀ r s₀ := by
  rw [fairBuchiSat_iff_fairInfOften, FairInfOften.ret_iff]; rfl

@[simp]
theorem FairBuchiSat.tau_iff (spec : BuchiSpec S QState E R)
    (fair : QState → (i : E.I) → E.O i → S → S → QState → Prop)
    (t : ITree E R) (q₀ : QState) (s₀ : S) :
    FairBuchiSat spec fair (.tau t) q₀ s₀ ↔ FairBuchiSat spec fair t q₀ s₀ := by
  rw [fairBuchiSat_iff_fairInfOften, fairBuchiSat_iff_fairInfOften, FairInfOften.tau_iff]

@[simp]
theorem FairBuchiSat.vis_iff (spec : BuchiSpec S QState E R)
    (fair : QState → (i : E.I) → E.O i → S → S → QState → Prop)
    (i : E.I) (k : E.O i → ITree E R) (q₀ : QState) (s₀ : S) :
    FairBuchiSat spec fair (.vis i k) q₀ s₀ ↔
      spec.inv q₀ s₀ ∧
        spec.ewp.wp i (fun o s' => ∃ q',
          spec.step q₀ i o s₀ s' q' ∧ FairBuchiSat spec fair (k o) q' s') s₀ := by
  rw [fairBuchiSat_iff_fairInfOften, FairInfOften.vis_iff, BuchiSpec.monitorWP_wp]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · exact spec.ewp.mono (fun _ _ ⟨q', hs, hi, hfi⟩ =>
      ⟨q', hs, (fairBuchiSat_iff_fairInfOften spec fair _ q' _).2 ⟨hi, hfi⟩⟩)
  · exact spec.ewp.mono (fun _ _ ⟨q', hs, hfbs⟩ =>
      let ⟨hi, hfi⟩ := (fairBuchiSat_iff_fairInfOften spec fair _ q' _).1 hfbs
      ⟨q', hs, hi, hfi⟩)

/-- `FairBuchiSat` respects equivalence up to finite `.tau`s (`Eutt`). -/
theorem FairBuchiSat.eutt {spec : BuchiSpec S QState E R}
    {fair : QState → (i : E.I) → E.O i → S → S → QState → Prop}
    {t u : ITree E R} {q₀ : QState} {s₀ : S}
    (he : Eutt t u) (h : FairBuchiSat spec fair t q₀ s₀) :
    FairBuchiSat spec fair u q₀ s₀ :=
  ⟨Always.eutt he h.1, FairInfOften.eutt he h.2⟩

/-- `Eutt`-equivalent trees satisfy the exact same `FairBuchiSat` specs. -/
theorem FairBuchiSat.eutt_iff (spec : BuchiSpec S QState E R)
    (fair : QState → (i : E.I) → E.O i → S → S → QState → Prop)
    {t u : ITree E R} (he : Eutt t u) (q₀ : QState) (s₀ : S) :
    FairBuchiSat spec fair t q₀ s₀ ↔ FairBuchiSat spec fair u q₀ s₀ :=
  ⟨FairBuchiSat.eutt he, FairBuchiSat.eutt he.symm⟩

/-- Monadic sequencing rule for `FairBuchiSat`. -/
theorem FairBuchiSat.bind {A : Type u} {spec : BuchiSpec S QState E R}
    {fair : QState → (i : E.I) → E.O i → S → S → QState → Prop}
    {t : ITree E A} {k : A → ITree E R} {q₀ : QState} {s₀ : S}
    (h : FairBuchiSat (spec.withTerminal (fun q a s => FairBuchiSat spec fair (k a) q s))
      fair t q₀ s₀) :
    FairBuchiSat spec fair (t >>= k) q₀ s₀ :=
  ⟨Always.bind (Always.mono (fun _ hi => hi) (fun _ _ ha => ha.1) h.1),
   FairInfOften.bind (FairInfOften.mono_post (fun _ _ ha => ha.2) h.2)⟩

/-- Exact monadic bind characterisation for `FairBuchiSat`. -/
theorem FairBuchiSat.bind_iff {A : Type u} (spec : BuchiSpec S QState E R)
    (fair : QState → (i : E.I) → E.O i → S → S → QState → Prop)
    (t : ITree E A) (k : A → ITree E R) (q₀ : QState) (s₀ : S) :
    FairBuchiSat spec fair (t >>= k) q₀ s₀ ↔
      FairBuchiSat (spec.withTerminal (fun q a s => FairBuchiSat spec fair (k a) q s))
        fair t q₀ s₀ := by
  refine ⟨fun h => ?_, FairBuchiSat.bind⟩
  have ⟨hi, hfi⟩ := (fairBuchiSat_iff_fairInfOften spec fair (t >>= k) q₀ s₀).1 h
  rw [FairInfOften.bind_iff] at hfi
  have hfi' := FairInfOften.post_inv_guardInv (ewp := spec.prodWP)
    (Inv := spec.invPred) (s := (q₀, s₀)) hi hfi
  refine (fairBuchiSat_iff_fairInfOften _ fair t q₀ s₀).2 ⟨hi, ?_⟩
  refine FairInfOften.mono_post (fun a qs ⟨hi', hfi_k⟩ => ?_) hfi'
  exact (fairBuchiSat_iff_fairInfOften spec fair (k a) qs.1 qs.2).2 ⟨hi', hfi_k⟩

/-- Conditional branching rule for `FairBuchiSat`. -/
theorem FairBuchiSat.ite {spec : BuchiSpec S QState E R}
    {fair : QState → (i : E.I) → E.O i → S → S → QState → Prop}
    {c : Prop} [Decidable c] {t₁ t₂ : ITree E R} {q₀ : QState} {s₀ : S}
    (h₁ : c → FairBuchiSat spec fair t₁ q₀ s₀)
    (h₂ : ¬ c → FairBuchiSat spec fair t₂ q₀ s₀) :
    FairBuchiSat spec fair (if c then t₁ else t₂) q₀ s₀ := by
  split
  · exact h₁ ‹_›
  · exact h₂ ‹_›

/-- `Sum`-branching rule for `FairBuchiSat`. -/
theorem FairBuchiSat.sum_elim {A B : Type u} {spec : BuchiSpec S QState E R}
    {fair : QState → (i : E.I) → E.O i → S → S → QState → Prop}
    {f : A → ITree E R} {g : B → ITree E R} {q₀ : QState} {s₀ : S} (x : A ⊕ B)
    (h₁ : ∀ a, x = .inl a → FairBuchiSat spec fair (f a) q₀ s₀)
    (h₂ : ∀ b, x = .inr b → FairBuchiSat spec fair (g b) q₀ s₀) :
    FairBuchiSat spec fair (Sum.elim f g x) q₀ s₀ := by
  cases x with
  | inl a => exact h₁ a rfl
  | inr b => exact h₂ b rfl

/-- Well-founded loop rule for general `ITree.iter` under `FairBuchiSat`. -/
theorem FairBuchiSat.iter_wf {I : Type u} {α : Type _}
    (spec : BuchiSpec S QState E R)
    (fair : QState → (i : E.I) → E.O i → S → S → QState → Prop)
    (lt : α → α → Prop) (h_wf : WellFounded lt)
    (body : I → ITree E (I ⊕ R)) (LInv : α → I → QState → S → Prop)
    (h_body : ∀ m a q s, LInv m a q s →
      fairStep spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
        (Sum.elim (fun next qs' => ∃ m', lt m' m ∧ LInv m' next qs'.1 qs'.2)
          spec.terminalPost)
        (FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
          (Sum.elim (fun next qs' => ∃ m', LInv m' next qs'.1 qs'.2)
            spec.terminalPost))
        (fairProgress spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
          (Sum.elim (fun next qs' => ∃ m', lt m' m ∧ LInv m' next qs'.1 qs'.2)
            spec.terminalPost)
          (FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
            (Sum.elim (fun next qs' => ∃ m', LInv m' next qs'.1 qs'.2)
              spec.terminalPost)))
        (fairStall spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
          (Sum.elim (fun next qs' =>
              LInv m next qs'.1 qs'.2 ∨ ∃ m', lt m' m ∧ LInv m' next qs'.1 qs'.2)
            spec.terminalPost)
          (FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
            (Sum.elim (fun next qs' => ∃ m', LInv m' next qs'.1 qs'.2)
              spec.terminalPost))
          (fairProgress spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
            (Sum.elim (fun next qs' => ∃ m', lt m' m ∧ LInv m' next qs'.1 qs'.2)
              spec.terminalPost)
            (FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
              (Sum.elim (fun next qs' => ∃ m', LInv m' next qs'.1 qs'.2)
                spec.terminalPost))))
        (body a) (q, s))
    {m : α} {init : I} {q₀ : QState} {s₀ : S}
    (h_inv : spec.inv q₀ s₀) (h_init : LInv m init q₀ s₀) :
    FairBuchiSat spec fair (ITree.iter body init) q₀ s₀ :=
  (fairBuchiSat_iff_fairInfOften spec fair _ q₀ s₀).2
    ⟨h_inv,
     FairInfOften.iter_wf lt h_wf body (fun m a qs => LInv m a qs.1 qs.2)
       (fun m a qs hm => h_body m a qs.1 qs.2 hm) h_init⟩

/-- Sequential composition for `FairBuchiSat`. -/
theorem FairBuchiSat.seq {A : Type u} {spec : BuchiSpec S QState E R}
    {fair : QState → (i : E.I) → E.O i → S → S → QState → Prop}
    {t₁ : ITree E A} {t₂ : ITree E R} {q₀ : QState} {s₀ : S}
    (h : FairBuchiSat (spec.withTerminal (fun q _ s => FairBuchiSat spec fair t₂ q s))
      fair t₁ q₀ s₀) :
    FairBuchiSat spec fair (t₁ >>= fun _ => t₂) q₀ s₀ :=
  FairBuchiSat.bind h

/-- `Nat`-ranked loop rule for general `ITree.iter` under `FairBuchiSat`. -/
theorem FairBuchiSat.iter_ranked {I : Type u}
    (spec : BuchiSpec S QState E R)
    (fair : QState → (i : E.I) → E.O i → S → S → QState → Prop)
    (body : I → ITree E (I ⊕ R)) (LInv : Nat → I → QState → S → Prop)
    (h_body : ∀ n a q s, LInv n a q s →
      fairStep spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
        (Sum.elim (fun next qs' => ∃ m, m < n ∧ LInv m next qs'.1 qs'.2)
          spec.terminalPost)
        (FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
          (Sum.elim (fun next qs' => ∃ m, LInv m next qs'.1 qs'.2)
            spec.terminalPost))
        (fairProgress spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
          (Sum.elim (fun next qs' => ∃ m, m < n ∧ LInv m next qs'.1 qs'.2)
            spec.terminalPost)
          (FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
            (Sum.elim (fun next qs' => ∃ m, LInv m next qs'.1 qs'.2)
              spec.terminalPost)))
        (fairStall spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
          (Sum.elim (fun next qs' =>
              LInv n next qs'.1 qs'.2 ∨ ∃ m, m < n ∧ LInv m next qs'.1 qs'.2)
            spec.terminalPost)
          (FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
            (Sum.elim (fun next qs' => ∃ m, LInv m next qs'.1 qs'.2)
              spec.terminalPost))
          (fairProgress spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
            (Sum.elim (fun next qs' => ∃ m, m < n ∧ LInv m next qs'.1 qs'.2)
              spec.terminalPost)
            (FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
              (Sum.elim (fun next qs' => ∃ m, LInv m next qs'.1 qs'.2)
                spec.terminalPost))))
        (body a) (q, s))
    {n : Nat} {init : I} {q₀ : QState} {s₀ : S}
    (h_inv : spec.inv q₀ s₀) (h_init : LInv n init q₀ s₀) :
    FairBuchiSat spec fair (ITree.iter body init) q₀ s₀ :=
  FairBuchiSat.iter_wf spec fair (fun a b : Nat => a < b) Nat.lt_wfRel.wf body
    LInv h_body h_inv h_init

/-- Well-founded diverging `-> !` reactive loop rule for `FairBuchiSat`. -/
theorem fairBuchiSat_diverging_loop_wf {I : Type u} {α : Type _}
    (spec : BuchiSpec S QState E PEmpty.{u + 1})
    (fair : QState → (i : E.I) → E.O i → S → S → QState → Prop)
    (lt : α → α → Prop) (h_wf : WellFounded lt)
    (body : I → ITree E I) (LInv : α → I → QState → S → Prop)
    (h_live : ∀ m a q s, LInv m a q s →
      fairStep spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
        (fun next qs' => ∃ m', lt m' m ∧ LInv m' next qs'.1 qs'.2)
        (FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
          (fun next qs' => ∃ m', LInv m' next qs'.1 qs'.2))
        (fairProgress spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
          (fun next qs' => ∃ m', lt m' m ∧ LInv m' next qs'.1 qs'.2)
          (FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
            (fun next qs' => ∃ m', LInv m' next qs'.1 qs'.2)))
        (fairStall spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
          (fun next qs' =>
            LInv m next qs'.1 qs'.2 ∨ ∃ m', lt m' m ∧ LInv m' next qs'.1 qs'.2)
          (FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
            (fun next qs' => ∃ m', LInv m' next qs'.1 qs'.2))
          (fairProgress spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
            (fun next qs' => ∃ m', lt m' m ∧ LInv m' next qs'.1 qs'.2)
            (FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
              (fun next qs' => ∃ m', LInv m' next qs'.1 qs'.2))))
        (body a) (q, s))
    {m : α} {init : I} {q₀ : QState} {s₀ : S}
    (h_inv : spec.inv q₀ s₀) (h_init : LInv m init q₀ s₀) :
    FairBuchiSat spec fair (divergingLoop body init) q₀ s₀ :=
  (fairBuchiSat_iff_fairInfOften spec fair _ q₀ s₀).2
    ⟨h_inv,
     FairInfOften.iter_wf lt h_wf _ (fun m a qs => LInv m a qs.1 qs.2)
       (fun m a qs hm => fairStep_map_inl (h_live m a qs.1 qs.2 hm)) h_init⟩

/-- Horizontal handler linking for `FairBuchiSat` across `ITree.interp`. -/
theorem FairBuchiSat.interp {E₁ E₂ : Effect.{u}}
    {spec₁ : BuchiSpec S QState E₁ R} {spec₂ : BuchiSpec S QState E₂ R}
    {fair₁ : QState → (i : E₁.I) → E₁.O i → S → S → QState → Prop}
    {fair₂ : QState → (j : E₂.I) → E₂.O j → S → S → QState → Prop}
    (h_inv : ∀ q s, spec₁.inv q s → spec₂.inv q s)
    (h_term : ∀ q r s, spec₁.terminal q r s → spec₂.terminal q r s)
    (h : (i : E₁.I) → ITree E₂ (E₁.O i))
    (h_link : ∀ (i : E₁.I) (K4 K3 K2 : E₁.O i → QState × S → Prop)
      (qs₀ : QState × S),
      spec₁.monitorWP.wp i (fun o qs' =>
        (spec₁.acceptEdge i o qs₀ qs' ∧ K4 o qs') ∨
        (spec₁.fairEdge fair₁ i o qs₀ qs' ∧ K3 o qs') ∨
        (¬ spec₁.fairEdge fair₁ i o qs₀ qs' ∧ K2 o qs')) qs₀ →
      fairStep spec₂.monitorWP spec₂.acceptEdge (spec₂.fairEdge fair₂) K3
        (FairInfOften spec₂.monitorWP spec₂.acceptEdge (spec₂.fairEdge fair₂)
          (fun o qs'' => K4 o qs'' ∨ K3 o qs'' ∨ K2 o qs''))
        (fairProgress spec₂.monitorWP spec₂.acceptEdge (spec₂.fairEdge fair₂) K3
          (FairInfOften spec₂.monitorWP spec₂.acceptEdge (spec₂.fairEdge fair₂)
            (fun o qs'' => K4 o qs'' ∨ K3 o qs'' ∨ K2 o qs'')))
        (fairStall spec₂.monitorWP spec₂.acceptEdge (spec₂.fairEdge fair₂)
          (fun o qs'' => K3 o qs'' ∨ K2 o qs'')
          (FairInfOften spec₂.monitorWP spec₂.acceptEdge (spec₂.fairEdge fair₂)
            (fun o qs'' => K4 o qs'' ∨ K3 o qs'' ∨ K2 o qs''))
          (fairProgress spec₂.monitorWP spec₂.acceptEdge (spec₂.fairEdge fair₂) K3
            (FairInfOften spec₂.monitorWP spec₂.acceptEdge (spec₂.fairEdge fair₂)
              (fun o qs'' => K4 o qs'' ∨ K3 o qs'' ∨ K2 o qs''))))
        (h i) qs₀)
    {t : ITree E₁ R} {q₀ : QState} {s₀ : S}
    (h_fbs : FairBuchiSat spec₁ fair₁ t q₀ s₀) :
    FairBuchiSat spec₂ fair₂ (ITree.interp h t) q₀ s₀ := by
  have ⟨hi, hfi⟩ := (fairBuchiSat_iff_fairInfOften spec₁ fair₁ t q₀ s₀).1 h_fbs
  refine (fairBuchiSat_iff_fairInfOften spec₂ fair₂ _ q₀ s₀).2 ⟨h_inv q₀ s₀ hi, ?_⟩
  exact FairInfOften.mono_post (fun r qs ht => h_term qs.1 r qs.2 ht)
    (FairInfOften.interp h h_link hfi)

/--
**Stateful monitor handler linking** for `FairBuchiSat` across
`ITree.interpState`: threads program state `S` while preserving ghost monitor
state `QState`.
-/
theorem FairBuchiSat.interpState {E₁ E₂ : Effect.{u}}
    {spec₁ : BuchiSpec S QState E₁ R}
    {spec₂ : BuchiSpec PUnit.{u + 1} QState E₂ (R × S)}
    {fair₁ : QState → (i : E₁.I) → E₁.O i → S → S → QState → Prop}
    {fair₂ : QState → (j : E₂.I) → E₂.O j → PUnit.{u + 1} → PUnit.{u + 1} → QState → Prop}
    (h_inv : ∀ q s, spec₁.inv q s → spec₂.inv q PUnit.unit)
    (h_term : ∀ q r s, spec₁.terminal q r s → spec₂.terminal q (r, s) PUnit.unit)
    (h : (i : E₁.I) → S → ITree E₂ (E₁.O i × S))
    (h_link : ∀ (i : E₁.I) (K4 K3 K2 : E₁.O i → QState × S → Prop)
      (q : QState) (s : S),
      spec₁.monitorWP.wp i (fun o qs' =>
        (spec₁.acceptEdge i o (q, s) qs' ∧ K4 o qs') ∨
        (spec₁.fairEdge fair₁ i o (q, s) qs' ∧ K3 o qs') ∨
        (¬ spec₁.fairEdge fair₁ i o (q, s) qs' ∧ K2 o qs')) (q, s) →
      fairStep spec₂.monitorWP spec₂.acceptEdge (spec₂.fairEdge fair₂)
        (fun pair qp => K3 pair.1 (qp.1, pair.2))
        (FairInfOften spec₂.monitorWP spec₂.acceptEdge (spec₂.fairEdge fair₂)
          (fun pair qp =>
            K4 pair.1 (qp.1, pair.2) ∨ K3 pair.1 (qp.1, pair.2) ∨
              K2 pair.1 (qp.1, pair.2)))
        (fairProgress spec₂.monitorWP spec₂.acceptEdge (spec₂.fairEdge fair₂)
          (fun pair qp => K3 pair.1 (qp.1, pair.2))
          (FairInfOften spec₂.monitorWP spec₂.acceptEdge (spec₂.fairEdge fair₂)
            (fun pair qp =>
              K4 pair.1 (qp.1, pair.2) ∨ K3 pair.1 (qp.1, pair.2) ∨
                K2 pair.1 (qp.1, pair.2))))
        (fairStall spec₂.monitorWP spec₂.acceptEdge (spec₂.fairEdge fair₂)
          (fun pair qp => K3 pair.1 (qp.1, pair.2) ∨ K2 pair.1 (qp.1, pair.2))
          (FairInfOften spec₂.monitorWP spec₂.acceptEdge (spec₂.fairEdge fair₂)
            (fun pair qp =>
              K4 pair.1 (qp.1, pair.2) ∨ K3 pair.1 (qp.1, pair.2) ∨
                K2 pair.1 (qp.1, pair.2)))
          (fairProgress spec₂.monitorWP spec₂.acceptEdge (spec₂.fairEdge fair₂)
            (fun pair qp => K3 pair.1 (qp.1, pair.2))
            (FairInfOften spec₂.monitorWP spec₂.acceptEdge (spec₂.fairEdge fair₂)
              (fun pair qp =>
                K4 pair.1 (qp.1, pair.2) ∨ K3 pair.1 (qp.1, pair.2) ∨
                  K2 pair.1 (qp.1, pair.2)))))
        (h i s) (q, PUnit.unit))
    {t : ITree E₁ R} {q₀ : QState} {s₀ : S}
    (h_fbs : FairBuchiSat spec₁ fair₁ t q₀ s₀) :
    FairBuchiSat spec₂ fair₂ (ITree.interpState h t s₀) q₀ PUnit.unit := by
  have ⟨hi, hfi⟩ := (fairBuchiSat_iff_fairInfOften spec₁ fair₁ t q₀ s₀).1 h_fbs
  let liftEwp₁ : StateEffectWP ((QState × PUnit.{u + 1}) × S) E₁ :=
    { wp := fun i K p => spec₁.monitorWP.wp i
        (fun o qs' => K o ((qs'.1, PUnit.unit), qs'.2)) (p.1.1, p.2)
      mono := fun hm hw => spec₁.monitorWP.mono (fun o qs' hk => hm o _ hk) hw }
  let Acc₁ := fun i o (a b : (QState × PUnit.{u + 1}) × S) =>
    spec₁.acceptEdge i o (a.1.1, a.2) (b.1.1, b.2)
  let Fair₁ := fun i o (a b : (QState × PUnit.{u + 1}) × S) =>
    spec₁.fairEdge fair₁ i o (a.1.1, a.2) (b.1.1, b.2)
  let Q₁ := fun r (a : (QState × PUnit.{u + 1}) × S) => spec₁.terminal a.1.1 r a.2
  have hfi_lift : FairInfOften liftEwp₁ Acc₁ Fair₁ Q₁ t ((q₀, PUnit.unit), s₀) := by
    let X := fun x (p : (QState × PUnit.{u + 1}) × S) =>
      FairInfOften spec₁.monitorWP spec₁.acceptEdge (spec₁.fairEdge fair₁)
        spec₁.terminalPost x (p.1.1, p.2)
    refine FairInfOften.coinduct X ?_ hfi
    intro x p hx
    dsimp only [X] at hx
    rw [FairInfOften.unfold_eq] at hx
    refine fairProgress.induct
      (fun y qs => fairProgress liftEwp₁ Acc₁ Fair₁ Q₁ X y ((qs.1, PUnit.unit), qs.2))
      ?_ hx
    intro y qs hy
    rw [fairProgress.unfold_eq]
    let Z := fun z (a : (QState × PUnit.{u + 1}) × S) =>
      fairStall spec₁.monitorWP spec₁.acceptEdge (spec₁.fairEdge fair₁)
        spec₁.terminalPost
        (FairInfOften spec₁.monitorWP spec₁.acceptEdge (spec₁.fairEdge fair₁)
          spec₁.terminalPost)
        (fun v qs' => fairProgress liftEwp₁ Acc₁ Fair₁ Q₁ X v ((qs'.1, PUnit.unit), qs'.2))
        z (a.1.1, a.2)
    refine fairStall.coinduct Z ?_ hy
    intro z a hz
    dsimp only [Z] at hz
    rw [fairStall.unfold_eq] at hz
    refine fairStep.induct
      (fun w qs' => fairStep liftEwp₁ Acc₁ Fair₁ Q₁ X
        (fairProgress liftEwp₁ Acc₁ Fair₁ Q₁ X) Z w ((qs'.1, PUnit.unit), qs'.2)) ?_ hz
    intro w qs' hw
    rw [fairStep.unfold_eq]
    cases h_obs : w.observe <;> simp only [h_obs] at hw ⊢
    · exact hw
    · exact hw
    · exact hw
  have hfi₂ := FairInfOften.interpState_stateful
    (S₂ := QState × PUnit.{u + 1}) (H := S) (ewp₁ := liftEwp₁)
    (ewp₂ := spec₂.monitorWP) h
    (fun i K4 K3 K2 qp s hw => by
      cases qp with
      | mk q u =>
        cases u
        exact h_link i
          (fun o qs' => K4 o ((qs'.1, PUnit.unit), qs'.2))
          (fun o qs' => K3 o ((qs'.1, PUnit.unit), qs'.2))
          (fun o qs' => K2 o ((qs'.1, PUnit.unit), qs'.2)) q s hw)
    hfi_lift
  refine (fairBuchiSat_iff_fairInfOften spec₂ fair₂ _ q₀ PUnit.unit).2
    ⟨h_inv q₀ s₀ hi, ?_⟩
  exact FairInfOften.mono_post (fun pair qp ht => h_term qp.1 pair.1 pair.2 ht) hfi₂

/-- `Nat`-ranked diverging `-> !` reactive loop rule for `FairBuchiSat`. -/
theorem fairBuchiSat_diverging_loop_ranked {I : Type u}
    (spec : BuchiSpec S QState E PEmpty.{u + 1})
    (fair : QState → (i : E.I) → E.O i → S → S → QState → Prop)
    (body : I → ITree E I) (LInv : Nat → I → QState → S → Prop)
    (h_live : ∀ n a q s, LInv n a q s →
      fairStep spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
        (fun next qs' => ∃ m, m < n ∧ LInv m next qs'.1 qs'.2)
        (FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
          (fun next qs' => ∃ m, LInv m next qs'.1 qs'.2))
        (fairProgress spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
          (fun next qs' => ∃ m, m < n ∧ LInv m next qs'.1 qs'.2)
          (FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
            (fun next qs' => ∃ m, LInv m next qs'.1 qs'.2)))
        (fairStall spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
          (fun next qs' =>
            LInv n next qs'.1 qs'.2 ∨ ∃ m, m < n ∧ LInv m next qs'.1 qs'.2)
          (FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
            (fun next qs' => ∃ m, LInv m next qs'.1 qs'.2))
          (fairProgress spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
            (fun next qs' => ∃ m, m < n ∧ LInv m next qs'.1 qs'.2)
            (FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
              (fun next qs' => ∃ m, LInv m next qs'.1 qs'.2))))
        (body a) (q, s))
    {n : Nat} {init : I} {q₀ : QState} {s₀ : S}
    (h_inv : spec.inv q₀ s₀) (h_init : LInv n init q₀ s₀) :
    FairBuchiSat spec fair (divergingLoop body init) q₀ s₀ :=
  fairBuchiSat_diverging_loop_wf spec fair (fun a b : Nat => a < b)
    Nat.lt_wfRel.wf body LInv h_live h_inv h_init

private theorem fairStall_to_dwlp {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop}
    {Q P : R → S → Prop} {X4 X3 : ITree E R → S → Prop}
    (hQ : ∀ r s', Q r s' → P r s')
    (h4 : ∀ x s', X4 x s' → DWLP ewp x P s')
    (h3 : ∀ x s', X3 x s' → DWLP ewp x P s')
    {t : ITree E R} {s : S} (h : fairStall ewp AccEdge Fair Q X4 X3 t s) :
    DWLP ewp t P s := by
  let D : ITree E R → S → Prop := fun x s₀ =>
    fairStep ewp AccEdge Fair Q X4 X3 (fairStall ewp AccEdge Fair Q X4 X3) x s₀ ∨
      DWLP ewp x P s₀
  refine DWLP.coinduct D ?_ (Or.inl (by rw [fairStall.unfold_eq] at h; exact h))
  rintro x s₀ (hfs | hdw)
  · rw [fairStep.unfold_eq] at hfs
    cases h_obs : x.observe <;> simp only [h_obs] at hfs ⊢
    · exact hQ _ _ hfs
    · exact Or.inl hfs
    · refine ewp.mono (fun _ _ hp => ?_) hfs
      rcases hp with ⟨_, hx4⟩ | ⟨_, hx3⟩ | ⟨_, hst⟩
      · exact Or.inr (h4 _ _ hx4)
      · exact Or.inr (h3 _ _ hx3)
      · rw [fairStall.unfold_eq] at hst; exact Or.inl hst
  · rw [DWLP.unfold_eq] at hdw
    cases h_obs : x.observe <;> simp only [h_obs] at hdw ⊢
    · exact hdw
    · exact Or.inr hdw
    · exact ewp.mono (fun _ _ h => Or.inr h) hdw

private theorem fairProgress_to_dwlp {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop}
    {Q P : R → S → Prop} {X4 : ITree E R → S → Prop}
    (hQ : ∀ r s', Q r s' → P r s') (h4 : ∀ x s', X4 x s' → DWLP ewp x P s')
    {t : ITree E R} {s : S} (h : fairProgress ewp AccEdge Fair Q X4 t s) :
    DWLP ewp t P s :=
  fairProgress.induct (fun x s₀ => DWLP ewp x P s₀)
    (fun _ _ hx => fairStall_to_dwlp hQ h4 (fun _ _ h => h) hx) h

private theorem fairStep_to_dwlp {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop}
    {Q P : R → S → Prop} {X4 X3 X2 : ITree E R → S → Prop}
    (hQ : ∀ r s', Q r s' → P r s')
    (h4 : ∀ x s', X4 x s' → DWLP ewp x P s')
    (h3 : ∀ x s', X3 x s' → DWLP ewp x P s')
    (h2 : ∀ x s', X2 x s' → DWLP ewp x P s')
    {t : ITree E R} {s : S} (h : fairStep ewp AccEdge Fair Q X4 X3 X2 t s) :
    DWLP ewp t P s := by
  refine fairStep.induct (fun x s₀ => DWLP ewp x P s₀) ?_ h
  intro x s₀ hx
  rw [DWLP.unfold_eq]
  cases h_obs : x.observe <;> simp only [h_obs] at hx ⊢
  · exact hQ _ _ hx
  · exact hx
  · refine ewp.mono (fun _ _ hp => ?_) hx
    rcases hp with ⟨_, hx4⟩ | ⟨_, hx3⟩ | ⟨_, hx2⟩
    · exact h4 _ _ hx4
    · exact h3 _ _ hx3
    · exact h2 _ _ hx2

/-- Single-fair-step diverging `-> !` reactive loop rule for `FairBuchiSat`. -/
theorem fairBuchiSat_diverging_loop_rule {I : Type u}
    (spec : BuchiSpec S QState E PEmpty.{u + 1})
    (fair : QState → (i : E.I) → E.O i → S → S → QState → Prop)
    (body : I → ITree E I) (LInv : I → QState → S → Prop)
    (h_live : ∀ a q s, LInv a q s →
      fairStep spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
        (fun _ _ => False)
        (FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
          (fun next qs' => LInv next qs'.1 qs'.2))
        (fairProgress spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
          (fun _ _ => False)
          (FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
            (fun next qs' => LInv next qs'.1 qs'.2)))
        (fairStall spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
          (fun next qs' => LInv next qs'.1 qs'.2)
          (FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
            (fun next qs' => LInv next qs'.1 qs'.2))
          (fairProgress spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
            (fun _ _ => False)
            (FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fair)
              (fun next qs' => LInv next qs'.1 qs'.2))))
        (body a) (q, s))
    {init : I} {q₀ : QState} {s₀ : S}
    (h_inv : spec.inv q₀ s₀) (h_init : LInv init q₀ s₀) :
    FairBuchiSat spec fair (divergingLoop body init) q₀ s₀ := by
  refine (fairBuchiSat_iff_fairInfOften spec fair _ q₀ s₀).2 ⟨h_inv, ?_⟩
  refine (fair_diverging_loop_rule (ewp := spec.monitorWP)
    (AccEdge := spec.acceptEdge) (Fair := spec.fairEdge fair)
    (Inv := fun _ => True) body (fun a qs => LInv a qs.1 qs.2)
    (fun a qs ha => (always_true_iff_dwlp spec.monitorWP _ _ _).2 ?_)
    (fun a qs ha => h_live a qs.1 qs.2 ha) h_init spec.terminalPost).2
  exact fairStep_to_dwlp (fun _ _ hf => False.elim hf)
    (fun _ _ hfi => hfi.toDWLP)
    (fun _ _ hfp => fairProgress_to_dwlp (fun _ _ hf => False.elim hf)
      (fun _ _ hfi => hfi.toDWLP) hfp)
    (fun _ _ hst => fairStall_to_dwlp (fun _ _ hl => hl)
      (fun _ _ hfi => hfi.toDWLP)
      (fun _ _ hfp => fairProgress_to_dwlp (fun _ _ hf => False.elim hf)
        (fun _ _ hfi => hfi.toDWLP) hfp) hst)
    (h_live a qs.1 qs.2 ha)

/--
**Trivial monitor collapse for `FairBuchiSat`**: a trivial `PUnit` `BuchiSpec`
reduces identically to `Inv s` plus `FairInfOften` over `guardInvWP ewp Inv`.
-/
theorem fairBuchiSat_trivial_iff (ewp : StateEffectWP S E)
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop)
    (Inv : S → Prop) (Q : R → S → Prop) (t : ITree E R) (s : S) :
    FairBuchiSat (BuchiSpec.trivial ewp AccEdge Inv Q)
        (fun _ i o s₀ s' _ => Fair i o s₀ s') t PUnit.unit s ↔
      Inv s ∧ FairInfOften (guardInvWP ewp Inv) AccEdge Fair Q t s := by
  let spec := BuchiSpec.trivial ewp AccEdge Inv Q
  let fairQ : PUnit.{u + 1} → (i : E.I) → E.O i → S → S → PUnit.{u + 1} → Prop :=
    fun _ i o s₀ s' _ => Fair i o s₀ s'
  rw [fairBuchiSat_iff_fairInfOften]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · let X := fun x s₀ =>
      FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fairQ)
        spec.terminalPost x (PUnit.unit, s₀)
    refine FairInfOften.coinduct X ?_ h
    intro x s₀ hx
    dsimp only [X] at hx
    rw [FairInfOften.unfold_eq] at hx
    refine fairProgress.induct
      (fun y qs => fairProgress (guardInvWP ewp Inv) AccEdge Fair Q X y qs.2)
      ?_ hx
    intro y qs hy
    rw [fairProgress.unfold_eq]
    let Z := fun z s₂ =>
      fairStall spec.monitorWP spec.acceptEdge (spec.fairEdge fairQ)
        spec.terminalPost
        (FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fairQ)
          spec.terminalPost)
        (fun v qs' => fairProgress (guardInvWP ewp Inv) AccEdge Fair Q X v qs'.2)
        z (PUnit.unit, s₂)
    refine fairStall.coinduct Z ?_ (by cases qs.1; exact hy)
    intro z s₂ hz
    dsimp only [Z] at hz
    rw [fairStall.unfold_eq] at hz
    refine fairStep.induct
      (fun w qs' => fairStep (guardInvWP ewp Inv) AccEdge Fair Q X
        (fairProgress (guardInvWP ewp Inv) AccEdge Fair Q X) Z w qs'.2)
      ?_ hz
    intro w qs' hw
    rw [fairStep.unfold_eq]
    cases h_obs : w.observe <;> simp only [h_obs] at hw ⊢
    · exact hw
    · exact hw
    · exact ewp.mono (fun _ _ ⟨⟨⟩, _, hi, hp⟩ => ⟨hi, hp⟩) hw
  · let X := fun x (qs : PUnit.{u + 1} × S) =>
      FairInfOften (guardInvWP ewp Inv) AccEdge Fair Q x qs.2
    refine FairInfOften.coinduct X ?_ h
    intro x qs hx
    dsimp only [X] at hx
    rw [FairInfOften.unfold_eq] at hx
    refine fairProgress.induct
      (fun y s₁ => fairProgress spec.monitorWP spec.acceptEdge (spec.fairEdge fairQ)
        spec.terminalPost X y (PUnit.unit, s₁)) ?_ hx
    intro y s₁ hy
    rw [fairProgress.unfold_eq]
    let Z := fun z (qs' : PUnit.{u + 1} × S) =>
      fairStall (guardInvWP ewp Inv) AccEdge Fair Q
        (FairInfOften (guardInvWP ewp Inv) AccEdge Fair Q)
        (fun v s₃ => fairProgress spec.monitorWP spec.acceptEdge
          (spec.fairEdge fairQ) spec.terminalPost X v (PUnit.unit, s₃)) z qs'.2
    refine fairStall.coinduct Z ?_ hy
    intro z qs' hz
    dsimp only [Z] at hz
    rw [fairStall.unfold_eq] at hz
    refine fairStep.induct
      (fun w s₃ => fairStep spec.monitorWP spec.acceptEdge (spec.fairEdge fairQ)
        spec.terminalPost X
        (fairProgress spec.monitorWP spec.acceptEdge (spec.fairEdge fairQ)
          spec.terminalPost X) Z w (qs'.1, s₃)) ?_ hz
    intro w s₃ hw
    rw [fairStep.unfold_eq]
    cases h_obs : w.observe <;> simp only [h_obs] at hw ⊢
    · exact hw
    · exact hw
    · exact ewp.mono (fun _ _ ⟨hi, hp⟩ => ⟨PUnit.unit, trivial, hi, hp⟩) hw

/--
Under `[Conjunctive ewp]`, the trivial-monitor `FairBuchiSat` is literally
`Always ewp Inv Q t s ∧ FairInfOften ewp AccEdge Fair Q t s`.
-/
theorem fairBuchiSat_trivial_iff_always_and_fairInfOften (ewp : StateEffectWP S E)
    [StateEffectWP.Conjunctive ewp]
    (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop)
    (Inv : S → Prop) (Q : R → S → Prop) (t : ITree E R) (s : S) :
    FairBuchiSat (BuchiSpec.trivial ewp AccEdge Inv Q)
        (fun _ i o s₀ s' _ => Fair i o s₀ s') t PUnit.unit s ↔
      Always ewp Inv Q t s ∧ FairInfOften ewp AccEdge Fair Q t s := by
  rw [fairBuchiSat_trivial_iff]
  constructor
  · rintro ⟨hi, hfi⟩
    refine ⟨(always_iff_dwlp_guard ewp Inv Q t s).2 ⟨hi, hfi.toDWLP⟩, ?_⟩
    exact FairInfOften.mono_wp (ewp := guardInvWP ewp Inv) (ewp' := ewp)
      (fun _ _ _ hw => ewp.mono (fun _ _ hk => hk.2) hw) hfi
  · rintro ⟨ha, hfi⟩
    exact ⟨ha.inv, FairInfOften.guardInv_of_always ha hfi⟩

end FairBuchiSat

section FairInfOftenAdequacy

/--
Stateless operational adequacy of `FairInfOften`: even under arbitrary fairness
assumptions, `FairInfOften` over a `PureSoundWP` transformer guarantees
`TreeSafe t`, `Productive t`, `¬ MayDiverge t`, and `post` on every return.
-/
theorem fairInfOften_pure_adequacy {E : Effect.{u}} {R : Type u}
    [FaultEffect E] {ewp : EffectWP E} [PureSoundWP ewp]
    {AccEdge Fair : (i : E.I) → E.O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop}
    {t : ITree E R} {post : R → Prop}
    (h : FairInfOften ewp AccEdge Fair (fun r _ => post r) t PUnit.unit) :
    TreeSafe t ∧ Productive t ∧ ¬ MayDiverge t ∧
      ∀ tr r, ReachesRet t tr r → post r :=
  infOften_pure_adequacy
    ((fairInfOften_false_iff ewp AccEdge (fun r _ => post r) t PUnit.unit).1
      (FairInfOften.mono (fun _ _ _ _ ha => ha) (fun _ _ _ _ hf => False.elim hf)
        (fun _ _ hp => hp) h))

open Std.Do in
/-- `FairInfOften` over a `PureEffectWP` yields the corresponding `Std.Do.Triple`. -/
theorem Triple.of_fairInfOften {E : Effect.{u}} {R : Type u} [p : PureEffectWP E]
    {AccEdge Fair : (i : E.I) → E.O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop}
    {t : ITree E R} {P : Prop} {Q : R → Prop}
    (h : P → FairInfOften p.ewp AccEdge Fair (fun r _ => Q r) t PUnit.unit) :
    ⦃⌜P⌝⦄ t ⦃⇓ r => ⌜Q r⌝⦄ :=
  fun hp => (h hp).toDWLP

private theorem obs_fairInfOften_wait {α : Type u}
    (AccObs FairObs : α → Prop) (Q : PEmpty.{u + 1} → PUnit.{u + 1} → Prop)
    {x : ITree (ObsE α) PEmpty.{u + 1}}
    (h : FairInfOften (obsIgnoreWP PUnit.{u + 1} α)
      (fun i _ _ _ => match i with | .emit a => AccObs a)
      (fun i _ _ _ => match i with | .emit a => FairObs a) Q x PUnit.unit)
    {s : Stream' α} (hf : FollowsStream x s)
    (h_fair_inf : ∀ k : Nat, ∃ n : Nat, k ≤ n ∧ FairObs (s n)) :
    ∃ m : Nat, AccObs (s m) := by
  let Acc : (i : (ObsE α).I) → (ObsE α).O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop :=
    fun i _ _ _ => match i with | .emit a => AccObs a
  let Fair : (i : (ObsE α).I) → (ObsE α).O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop :=
    fun i _ _ _ => match i with | .emit a => FairObs a
  rw [FairInfOften.unfold_eq] at h
  refine fairProgress.induct
    (fun y _ => ∀ s', FollowsStream y s' →
      (∀ k, ∃ n, k ≤ n ∧ FairObs (s' n)) → ∃ m, AccObs (s' m))
    ?_ h s hf h_fair_inf
  intro y ⟨⟩ hy s' hfs hfair
  obtain ⟨n, _, hn⟩ := hfair 0
  have h_drop : ∀ (d : Nat) (z : ITree (ObsE α) PEmpty.{u + 1}) (s₀ : Stream' α),
      fairStall (obsIgnoreWP PUnit.{u + 1} α) Acc Fair Q
        (FairInfOften (obsIgnoreWP PUnit.{u + 1} α) Acc Fair Q)
        (fun w _ => ∀ s₁, FollowsStream w s₁ →
          (∀ k, ∃ m, k ≤ m ∧ FairObs (s₁ m)) → ∃ m, AccObs (s₁ m)) z PUnit.unit →
      FollowsStream z s₀ →
      (∀ k, ∃ m, k ≤ m ∧ FairObs (s₀ m)) →
      FairObs (s₀ d) → ∃ m, AccObs (s₀ m) := by
    intro d
    induction d with
    | zero =>
      intro z s₀ hz hfz hfair₀ hf0
      rw [fairStall.unfold_eq] at hz
      refine fairStep.induct
        (fun w _ => FollowsStream w s₀ → ∃ m, AccObs (s₀ m)) ?_ hz hfz
      intro w ⟨⟩ hw hfw
      cases h_obs : w.observe with
      | ret r => exact PEmpty.elim r
      | tau w' => simp only [h_obs] at hw; exact hw (followsStream_of_tau h_obs hfw)
      | vis i k =>
        cases i with
        | emit a =>
          simp only [h_obs] at hw
          have ⟨hs0, htail⟩ := followsStream_vis_inv h_obs hfw
          rcases hw with ⟨ha, _⟩ | ⟨_, hpre⟩ | ⟨hnf, _⟩
          · exact ⟨0, hs0.symm ▸ ha⟩
          · obtain ⟨m, hm⟩ := hpre s₀.tail htail (fun j => by
              obtain ⟨m, hle, hfm⟩ := hfair₀ (j + 1)
              cases m with
              | zero => exact absurd hle (Nat.not_succ_le_zero j)
              | succ m' => exact ⟨m', Nat.le_of_succ_le_succ hle, hfm⟩)
            exact ⟨m + 1, hm⟩
          · exact False.elim (hnf (hs0 ▸ hf0))
    | succ d ih =>
      intro z s₀ hz hfz hfair₀ hfsd
      rw [fairStall.unfold_eq] at hz
      refine fairStep.induct
        (fun w _ => FollowsStream w s₀ → ∃ m, AccObs (s₀ m)) ?_ hz hfz
      intro w ⟨⟩ hw hfw
      cases h_obs : w.observe with
      | ret r => exact PEmpty.elim r
      | tau w' => simp only [h_obs] at hw; exact hw (followsStream_of_tau h_obs hfw)
      | vis i k =>
        cases i with
        | emit a =>
          simp only [h_obs] at hw
          have ⟨hs0, htail⟩ := followsStream_vis_inv h_obs hfw
          have hfair_tail : ∀ j, ∃ m, j ≤ m ∧ FairObs (s₀.tail m) := fun j => by
            obtain ⟨m, hle, hfm⟩ := hfair₀ (j + 1)
            cases m with
            | zero => exact absurd hle (Nat.not_succ_le_zero j)
            | succ m' => exact ⟨m', Nat.le_of_succ_le_succ hle, hfm⟩
          rcases hw with ⟨ha, _⟩ | ⟨_, hpre⟩ | ⟨_, hst⟩
          · exact ⟨0, hs0.symm ▸ ha⟩
          · obtain ⟨m, hm⟩ := hpre s₀.tail htail hfair_tail
            exact ⟨m + 1, hm⟩
          · obtain ⟨m, hm⟩ := ih (k PUnit.unit) s₀.tail hst htail hfair_tail hfsd
            exact ⟨m + 1, hm⟩
  exact h_drop n y s' hy hfs hfair hn

/--
**Exact $\omega$-language Streett adequacy (`FollowsStream`)**: a non-returning
observation tree `t : ITree (ObsE α) PEmpty` satisfies the 4-level parity
fixpoint `FairInfOften` for `(AccObs, FairObs)` **if and only if** it emits an
infinite stream `s : Stream' α` satisfying the textbook Streett condition
`(∀ k, ∃ n ≥ k, FairObs (s n)) → (∀ k, ∃ n ≥ k, AccObs (s n))`.
-/
theorem fairInfOften_obsIgnoreWP_iff_followsStream {α : Type u}
    (AccObs FairObs : α → Prop) (Q : PEmpty.{u + 1} → PUnit.{u + 1} → Prop)
    (t : ITree (ObsE α) PEmpty.{u + 1}) :
    FairInfOften (obsIgnoreWP PUnit.{u + 1} α)
        (fun i _ _ _ => match i with | .emit a => AccObs a)
        (fun i _ _ _ => match i with | .emit a => FairObs a) Q t PUnit.unit ↔
      ∃ s : Stream' α, FollowsStream t s ∧
        ((∀ k : Nat, ∃ n : Nat, k ≤ n ∧ FairObs (s n)) →
          (∀ k : Nat, ∃ n : Nat, k ≤ n ∧ AccObs (s n))) := by
  let Acc : (i : (ObsE α).I) → (ObsE α).O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop :=
    fun i _ _ _ => match i with | .emit a => AccObs a
  let Fair : (i : (ObsE α).I) → (ObsE α).O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop :=
    fun i _ _ _ => match i with | .emit a => FairObs a
  constructor
  · intro h
    have h_prod : InfOften (obsIgnoreWP PUnit.{u + 1} α) (fun _ _ _ _ => True) Q t PUnit.unit :=
      (fairInfOften_false_iff (obsIgnoreWP PUnit.{u + 1} α) Acc Q t PUnit.unit).1
        (FairInfOften.mono (fun _ _ _ _ ha => ha) (fun _ _ _ _ hf => False.elim hf)
          (fun _ _ hq => hq) h)
    obtain ⟨s, hfol, _⟩ :=
      (infOften_obsIgnoreWP_iff_followsStream (fun _ => True) Q t).1 h_prod
    refine ⟨s, hfol, fun hfair_inf k => ?_⟩
    have h_shift : ∀ (j : Nat) (u : ITree (ObsE α) PEmpty.{u + 1}) (s₀ : Stream' α),
        FairInfOften (obsIgnoreWP PUnit.{u + 1} α) Acc Fair Q u PUnit.unit →
        FollowsStream u s₀ →
        ∃ u', FairInfOften (obsIgnoreWP PUnit.{u + 1} α) Acc Fair Q u' PUnit.unit ∧
          FollowsStream u' (fun m => s₀ (j + m)) := by
      intro j
      induction j with
      | zero =>
        intro u s₀ hu hfu
        exact ⟨u, hu, by simpa using hfu⟩
      | succ j ih =>
        intro u s₀ hu hfu
        rw [FollowsStream.eq_def] at hfu
        rcases hfu with ⟨u', k_fn, hts, hv, hcont⟩
        have hu' := FairInfOften.tauStar hts hu
        rw [eq_vis_of_observe hv] at hu'
        have hu'' := (FairInfOften.vis_iff (E := ObsE α) _ _ _ _
          (ObsReq.emit s₀.head : (ObsE α).I) k_fn PUnit.unit).1 hu'
        obtain ⟨u'', hfi'', hfu''⟩ := ih (k_fn PUnit.unit) s₀.tail hu'' hcont
        refine ⟨u'', hfi'', ?_⟩
        have h_eq : (fun m => s₀.tail (j + m)) = (fun m => s₀ (j + 1 + m)) := by
          funext m; simp [Stream'.tail]; congr 1; omega
        rwa [h_eq] at hfu''
    obtain ⟨u_k, hfi_k, hfol_k⟩ := h_shift k t s h hfol
    have hfair_k : ∀ j, ∃ m, j ≤ m ∧ FairObs (s (k + m)) := fun j => by
      obtain ⟨n, hle, hfn⟩ := hfair_inf (k + j)
      exact ⟨n - k, by omega, by rwa [show k + (n - k) = n by omega]⟩
    obtain ⟨m, hm⟩ := obs_fairInfOften_wait AccObs FairObs Q hfi_k hfol_k hfair_k
    exact ⟨k + m, Nat.le_add_right k m, hm⟩
  · rintro ⟨s, hfol, hstreett⟩
    by_cases hfair_inf : ∀ k : Nat, ∃ n : Nat, k ≤ n ∧ FairObs (s n)
    · have hio := (infOften_obsIgnoreWP_iff_followsStream AccObs Q t).2
        ⟨s, hfol, hstreett hfair_inf⟩
      exact hio.toFairInfOften Fair
    · have h_ev_unfair : ∃ K : Nat, ∀ n : Nat, K ≤ n → ¬ FairObs (s n) := by
        obtain ⟨K, hK⟩ := Classical.not_forall.1 hfair_inf
        exact ⟨K, fun n hle hf => hK ⟨n, hle, hf⟩⟩
      obtain ⟨K, hK⟩ := h_ev_unfair
      have h_tail_unfair : ∀ (u : ITree (ObsE α) PEmpty.{u + 1}) (s₀ : Stream' α),
          FollowsStream u s₀ → (∀ n, ¬ FairObs (s₀ n)) →
          FairInfOften (obsIgnoreWP PUnit.{u + 1} α) Acc Fair Q u PUnit.unit := by
        intro u s₀ hfu hnf
        rw [FairInfOften.unfold_eq, fairProgress.unfold_eq]
        refine fairStall.coinduct
          (fun v _ => ∃ s₁ : Stream' α, FollowsStream v s₁ ∧ ∀ n, ¬ FairObs (s₁ n))
          ?_ ⟨s₀, hfu, hnf⟩
        rintro v ⟨⟩ ⟨s₁, hfv, hnf₁⟩
        rw [FollowsStream.eq_def] at hfv
        rcases hfv with ⟨v', k_fn, hts, hv, hcont⟩
        refine fairStep.of_tauStar hts ?_
        rw [eq_vis_of_observe hv]
        refine (fairStep.vis_iff (E := ObsE α) _ _ _ _ _ _ _
          (ObsReq.emit s₁.head : (ObsE α).I) k_fn PUnit.unit).2 ?_
        exact Or.inr (Or.inr ⟨hnf₁ 0, ⟨s₁.tail, hcont, fun n => hnf₁ (n + 1)⟩⟩)
      have h_prefix : ∀ (d : Nat) (u : ITree (ObsE α) PEmpty.{u + 1}) (s₀ : Stream' α),
          FollowsStream u s₀ → (∀ n, d ≤ n → ¬ FairObs (s₀ n)) →
          FairInfOften (obsIgnoreWP PUnit.{u + 1} α) Acc Fair Q u PUnit.unit := by
        intro d
        induction d with
        | zero =>
          intro u s₀ hfu hnf
          exact h_tail_unfair u s₀ hfu (fun n => hnf n (Nat.zero_le n))
        | succ d ih =>
          intro u s₀ hfu hnf
          rw [FollowsStream.eq_def] at hfu
          rcases hfu with ⟨u', k_fn, hts, hv, hcont⟩
          refine FairInfOften.of_tauStar hts ?_
          rw [eq_vis_of_observe hv]
          exact FairInfOften.vis
            (ih (k_fn PUnit.unit) s₀.tail hcont (fun n hle => hnf (n + 1) (Nat.succ_le_succ hle)))
      exact h_prefix K t s hfol hK

end FairInfOftenAdequacy

/-! #### Separation Canaries: `DWP ⊊ FairInfOften` and `FairInfOften ⊊ productivity` -/

section FairCanaries

/-- A boolean compare-and-swap oracle: the environment answers whether the CAS succeeded. -/
abbrev CasE : Effect.{0} := PickE Bool

/-- The CAS request. -/
def casReq : CasE.I := PickReq.pick

/-- An edge is fair when the environment lets the CAS succeed. -/
def casFair : (i : CasE.I) → CasE.O i → PUnit.{1} → PUnit.{1} → Prop :=
  fun _ b _ _ => b = true

/-- Whether the CAS succeeded. -/
def casOk (b : CasE.O casReq) : Bool := b

/-- Loop-body continuation after the CAS: exit on success, retry on failure. -/
def casStep (b : CasE.O casReq) : ITree CasE (PUnit.{1} ⊕ PUnit.{1}) :=
  ITree.ret (if casOk b then Sum.inr PUnit.unit else Sum.inl PUnit.unit)

/-- `loop { if cas() { break } }`. -/
def casBody (_ : PUnit.{1}) : ITree CasE (PUnit.{1} ⊕ PUnit.{1}) :=
  ITree.vis casReq casStep

/-- The CAS retry loop. -/
def casLoop : ITree CasE PUnit.{1} :=
  ITree.iter casBody PUnit.unit

/-- Unfolded continuation of `casLoop` after the CAS. -/
def casK (b : CasE.O casReq) : ITree CasE PUnit.{1} :=
  if casOk b then ITree.ret PUnit.unit else ITree.tau casLoop

/-- Loop-body continuation that ignores the CAS result. -/
def ignoreStep (_ : CasE.O casReq) : ITree CasE (PUnit.{1} ⊕ PEmpty.{1}) :=
  ITree.ret (Sum.inl PUnit.unit)

/-- `loop { cas(); }`: the result of the CAS is ignored, so the loop never exits. -/
def ignoreBody (_ : PUnit.{1}) : ITree CasE (PUnit.{1} ⊕ PEmpty.{1}) :=
  ITree.vis casReq ignoreStep

/-- The CAS-ignoring diverging loop. -/
def ignoreLoop : ITree CasE PEmpty.{1} :=
  ITree.iter ignoreBody PUnit.unit

/-- Unfolded continuation of `ignoreLoop` after the CAS. -/
def ignoreK (_ : CasE.O casReq) : ITree CasE PEmpty.{1} :=
  ITree.tau ignoreLoop

theorem casLoop_eq : casLoop = ITree.vis casReq casK := by
  refine (iter_unfold casBody PUnit.unit).trans ?_
  refine (vis_bind casReq casStep _).trans ?_
  refine congrArg (ITree.vis casReq) (funext fun b => ?_)
  cases b
  · exact (ret_bind (E := CasE) (Sum.inl PUnit.unit) _).trans rfl
  · exact (ret_bind (E := CasE) (Sum.inr PUnit.unit) _).trans rfl

theorem ignoreLoop_eq : ignoreLoop = ITree.vis casReq ignoreK := by
  refine (iter_unfold ignoreBody PUnit.unit).trans ?_
  refine (vis_bind casReq ignoreStep _).trans ?_
  exact congrArg (ITree.vis casReq)
    (funext fun _ => (ret_bind (E := CasE) (Sum.inl PUnit.unit) _).trans rfl)

/-- Under a fair environment the CAS retry loop terminates. -/
theorem casLoop_fairInfOften
    (AccEdge : (i : CasE.I) → CasE.O i → PUnit.{1} → PUnit.{1} → Prop) :
    FairInfOften (pickWP PUnit.{1} Bool) AccEdge casFair (fun _ _ => True)
      casLoop PUnit.unit := by
  refine FairInfOften.iter_fair casBody (fun _ _ => True) ?_ trivial
  intro a s₀ _
  refine (fairIter.vis_iff _ _ _ _ false casReq casStep s₀).2 ?_
  refine ⟨⟨true⟩, fun b => ?_⟩
  cases b
  · refine Or.inr ⟨fun h => Bool.noConfusion h, ?_⟩
    exact (fairIter.ret_inl_iff (pickWP PUnit.{1} Bool) casFair (fun _ _ => True)
      (fun _ _ => True) true PUnit.unit s₀).2 ⟨rfl, trivial⟩
  · exact Or.inl ⟨rfl, DWP.ret trivial⟩

/-- The CAS retry loop is not totally correct: the environment may refuse forever. -/
theorem not_dwp_casLoop (Q : PUnit.{1} → PUnit.{1} → Prop) :
    ¬ DWP (pickWP PUnit.{1} Bool) casLoop Q PUnit.unit := by
  have hobs : casLoop.observe = .vis casReq casK := by
    conv => lhs; rw [casLoop_eq]
    exact ITree.observe_vis _ _
  intro h
  refine DWP.induct
    (fun x _ => x = casLoop ∨ x = ITree.tau casLoop → False) ?_ h (Or.inl rfl)
  intro x s₀ hx hx_eq
  rcases hx_eq with rfl | rfl
  · rw [hobs] at hx
    exact hx.2 false (Or.inr rfl)
  · rw [ITree.observe_tau] at hx
    exact hx (Or.inl rfl)

/-- The CAS-ignoring loop is productive and safe (every visible edge accepted). -/
theorem ignoreLoop_infOften_productive (Q : PEmpty.{1} → PUnit.{1} → Prop) :
    InfOften (pickWP PUnit.{1} Bool) (fun _ _ _ _ => True) Q ignoreLoop
      PUnit.unit := by
  refine InfOften.iter_progress ignoreBody (fun _ _ => True) ?_ trivial
  intro a s₀ _
  exact buchiProgress.vis_accept (i := casReq) (k := ignoreStep)
    ⟨⟨true⟩, fun _ => ⟨trivial, (InfOften.ret_iff _ _ _ _ _).2 trivial⟩⟩

/--
The CAS-ignoring loop violates fairness-conditional liveness: along the path on
which every CAS succeeds the environment is fair, yet the loop never exits.
-/
theorem not_fairInfOften_ignoreLoop (Q : PEmpty.{1} → PUnit.{1} → Prop) :
    ¬ FairInfOften (pickWP PUnit.{1} Bool) (fun _ _ _ _ => False) casFair Q
      ignoreLoop PUnit.unit := by
  have hobs : ignoreLoop.observe = .vis casReq ignoreK := by
    conv => lhs; rw [ignoreLoop_eq]
    exact ITree.observe_vis _ _
  intro h
  rw [FairInfOften.unfold_eq] at h
  refine fairProgress.induct
    (fun x _ => x = ignoreLoop ∨ x = ITree.tau ignoreLoop → False) ?_ h (Or.inl rfl)
  intro x s₀ hx hx_eq
  rw [fairStall.unfold_eq] at hx
  refine fairStep.induct
    (fun y _ => y = ignoreLoop ∨ y = ITree.tau ignoreLoop → False) ?_ hx hx_eq
  intro y s₁ hy hy_eq
  rcases hy_eq with rfl | rfl
  · rw [hobs] at hy
    rcases hy.2 true with ⟨ha, _⟩ | ⟨_, hpre⟩ | ⟨hnf, _⟩
    · exact ha
    · exact hpre (Or.inr rfl)
    · exact hnf rfl
  · rw [ITree.observe_tau] at hy
    exact hy (Or.inl rfl)

/--
**Strict separation.** `FairInfOften` lies strictly between total correctness
and reactive productivity:

* the CAS retry loop satisfies fairness-conditional liveness but neither `DWP`
  nor Büchi recurrence without accepting edges;
* the CAS-ignoring loop is productive and safe (`InfOften` of every edge) but
  violates fairness-conditional liveness.
-/
theorem fairInfOften_strict_separation :
    (FairInfOften (pickWP PUnit.{1} Bool) (fun _ _ _ _ => False) casFair
        (fun _ _ => True) casLoop PUnit.unit ∧
      ¬ DWP (pickWP PUnit.{1} Bool) casLoop (fun _ _ => True) PUnit.unit ∧
      ¬ InfOften (pickWP PUnit.{1} Bool) (fun _ _ _ _ => False)
        (fun _ _ => True) casLoop PUnit.unit) ∧
    (InfOften (pickWP PUnit.{1} Bool) (fun _ _ _ _ => True) (fun _ _ => True)
        ignoreLoop PUnit.unit ∧
      ¬ FairInfOften (pickWP PUnit.{1} Bool) (fun _ _ _ _ => False) casFair
        (fun _ _ => True) ignoreLoop PUnit.unit) :=
  ⟨⟨casLoop_fairInfOften _, not_dwp_casLoop _,
    fun h => not_dwp_casLoop _
      ((buchiProgress_false_iff_dwp _ _ _ _ _).1 h.toBuchiProgress)⟩,
   ⟨ignoreLoop_infOften_productive _, not_fairInfOften_ignoreLoop _⟩⟩

/--
Multi-fair-step countdown retry loop: decrements `n` only when the CAS succeeds
(`b = true`) and retries at the same `n` when the CAS fails (`b = false`).
For `n ≥ 2`, a single fair step does not terminate the loop, so `iter_fair`
cannot verify it, whereas `FairInfOften.iter_ranked` handles arbitrary `n`.
-/
def multiCasBody : Nat → ITree CasE (Nat ⊕ PUnit.{1})
  | 0 => ITree.ret (Sum.inr PUnit.unit)
  | n + 1 => ITree.vis casReq (fun b =>
      ITree.ret (if casOk b then Sum.inl n else Sum.inl (n + 1)))

/-- Under fairness, `ITree.iter multiCasBody n` terminates for every `n : Nat`. -/
theorem multiCas_fairInfOften (n : Nat)
    (AccEdge : (i : CasE.I) → CasE.O i → PUnit.{1} → PUnit.{1} → Prop) :
    FairInfOften (pickWP PUnit.{1} Bool) AccEdge casFair (fun _ _ => True)
      (ITree.iter multiCasBody n) PUnit.unit := by
  refine FairInfOften.iter_ranked multiCasBody (fun r a _ => a = r) ?_ (n := n) rfl
  intro r a s₀ ha
  subst ha
  cases a with
  | zero => exact (fairStep.ret_iff _ _ _ _ _ _ _ _ _).2 trivial
  | succ r =>
    refine (fairStep.vis_iff _ _ _ _ _ _ _ _ _ _).2 ⟨⟨true⟩, fun b => ?_⟩
    cases b with
    | false =>
      refine Or.inr (Or.inr ⟨fun h => Bool.noConfusion h, ?_⟩)
      rw [fairStall.unfold_eq, fairStep.ret_iff]; exact Or.inl rfl
    | true =>
      refine Or.inr (Or.inl ⟨rfl, ?_⟩)
      exact fairProgress.of_dwp _ (DWP.ret ⟨r, Nat.lt_succ_self r, rfl⟩)

/--
A diverging `-> !` fair reactive service loop (`ITree CasE PEmpty`) that retries
CAS indefinitely and treats every winning CAS (`casFair`) as an accepting commit.
-/
def fairServiceBody (_ : PUnit.{1}) : ITree CasE PUnit.{1} :=
  ITree.vis casReq (fun _ => ITree.ret PUnit.unit)

/--
**Diverging fair reactive service separation (`InfOften ⊊ FairInfOften` with
non-empty `AccEdge`)**: `divergingLoop fairServiceBody ()` satisfies BOTH
`Always` and `FairInfOften` (via `fair_diverging_loop_rule`), yet refutes BOTH
`DWP` (non-terminating) AND plain Büchi `InfOften` for `casFair` (an unfair
environment can deny every CAS forever).
-/
theorem fairService_strict_separation (Q : PEmpty.{1} → PUnit.{1} → Prop) :
    Always (pickWP PUnit.{1} Bool) (fun _ => True) Q
        (divergingLoop fairServiceBody PUnit.unit) PUnit.unit ∧
      FairInfOften (pickWP PUnit.{1} Bool) casFair casFair Q
        (divergingLoop fairServiceBody PUnit.unit) PUnit.unit ∧
      ¬ DWP (pickWP PUnit.{1} Bool)
        (divergingLoop fairServiceBody PUnit.unit) Q PUnit.unit ∧
      ¬ InfOften (pickWP PUnit.{1} Bool) casFair Q
        (divergingLoop fairServiceBody PUnit.unit) PUnit.unit := by
  have h_both := fair_diverging_loop_rule (ewp := pickWP PUnit.{1} Bool)
    (AccEdge := casFair) (Fair := casFair) (Inv := fun _ => True)
    fairServiceBody (fun _ _ => True)
    (fun _ _ _ => Always.vis trivial ⟨⟨true⟩, fun _ => Always.ret trivial trivial⟩)
    (fun _ _ _ => by
      refine (fairStep.vis_iff _ _ _ _ _ _ _ _ _ _).2 ⟨⟨true⟩, fun b => ?_⟩
      cases b with
      | false =>
        refine Or.inr (Or.inr ⟨fun h => Bool.noConfusion h, ?_⟩)
        rw [fairStall.unfold_eq, fairStep.ret_iff]; trivial
      | true => exact Or.inl ⟨rfl, FairInfOften.ret trivial⟩)
    (init := PUnit.unit) (s := PUnit.unit) trivial Q
  have h_not_io : ¬ InfOften (pickWP PUnit.{1} Bool) casFair Q
      (divergingLoop fairServiceBody PUnit.unit) PUnit.unit := by
    have h_eq : divergingLoop fairServiceBody PUnit.unit =
        ITree.vis casReq (fun _ => ITree.tau (divergingLoop fairServiceBody PUnit.unit)) := by
      conv => lhs; unfold divergingLoop; rw [iter_unfold]
      show ((ITree.vis casReq (fun _ => ITree.ret PUnit.unit) >>=
          fun a => ITree.ret (Sum.inl a)) >>= _) = _
      rw [bind_assoc_itree, vis_bind]
      refine congrArg (ITree.vis casReq) (funext fun _ => ?_)
      rw [ret_bind, ret_bind]; rfl
    have hobs : (divergingLoop fairServiceBody PUnit.unit).observe =
        .vis casReq (fun _ => ITree.tau (divergingLoop fairServiceBody PUnit.unit)) := by
      conv => lhs; rw [h_eq]
      exact ITree.observe_vis _ _
    intro h
    refine buchiProgress.induct
      (fun x _ => x = divergingLoop fairServiceBody PUnit.unit ∨
        x = ITree.tau (divergingLoop fairServiceBody PUnit.unit) → False)
      ?_ h.toBuchiProgress (Or.inl rfl)
    intro x _ hx hx_eq
    rcases hx_eq with rfl | rfl
    · rw [hobs] at hx
      rcases hx.2 false with ⟨ha, _⟩ | hpre
      · exact Bool.noConfusion ha
      · exact hpre (Or.inr rfl)
    · rw [ITree.observe_tau] at hx
      exact hx (Or.inl rfl)
  exact ⟨h_both.1, h_both.2, not_dwp_diverging_loop _ _, h_not_io⟩

end FairCanaries

/-! #### Co-Büchi Persistence (`◇□`) -/

section CoBuchi

variable {S : Type u} {E : Effect.{u}} {R : Type u}

/--
Co-Büchi persistence `◇□ ¬ Bad`: on every path the tree returns with `Q`, or
takes `Bad` edges only finitely often (without silently diverging). This is
the Streett condition `□◇ Bad → □◇ False`, i.e. `FairInfOften` with no
accepting edges.
-/
def CoBuchi (ewp : StateEffectWP S E) (Bad : (i : E.I) → E.O i → S → S → Prop)
    (Q : R → S → Prop) (t : ITree E R) (s : S) : Prop :=
  FairInfOften ewp (fun _ _ _ _ => False) Bad Q t s

/-- `CoBuchi` is fairness-conditional recurrence without accepting edges. -/
theorem coBuchi_iff (ewp : StateEffectWP S E)
    (Bad : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (t : ITree E R) (s : S) :
    CoBuchi ewp Bad Q t s ↔ FairInfOften ewp (fun _ _ _ _ => False) Bad Q t s :=
  Iff.rfl

/-- Silent divergence is never persistent. -/
theorem not_coBuchi_spin {ewp : StateEffectWP S E}
    {Bad : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop} {s : S} :
    ¬ CoBuchi ewp Bad Q (ITree.spin (E := E) (R := R)) s :=
  not_fairInfOften_spin

/-- Total correctness implies persistence. -/
theorem CoBuchi.of_dwp {ewp : StateEffectWP S E}
    (Bad : (i : E.I) → E.O i → S → S → Prop) {Q : R → S → Prop}
    {t : ITree E R} {s : S} (h : DWP ewp t Q s) : CoBuchi ewp Bad Q t s :=
  fairInfOften_of_dwp _ Bad h

/-- Persistence of `Bad` implies persistence of any smaller edge class. -/
theorem CoBuchi.mono {ewp : StateEffectWP S E}
    {Bad Bad' : (i : E.I) → E.O i → S → S → Prop} {P Q : R → S → Prop}
    {t : ITree E R} {s : S}
    (h_bad : ∀ i o s₀ s', Bad' i o s₀ s' → Bad i o s₀ s')
    (h_post : ∀ r s', P r s' → Q r s') (h : CoBuchi ewp Bad P t s) :
    CoBuchi ewp Bad' Q t s :=
  FairInfOften.mono (fun _ _ _ _ ha => ha) h_bad h_post h

/-- `CoBuchi` with `Bad = False` (`◇□ True`) is reactive productivity (`InfOften True`). -/
theorem coBuchi_false_iff (ewp : StateEffectWP S E) (Q : R → S → Prop)
    (t : ITree E R) (s : S) :
    CoBuchi ewp (fun _ _ _ _ => False) Q t s ↔
      InfOften ewp (fun _ _ _ _ => True) Q t s :=
  fairInfOften_false_iff ewp (fun _ _ _ _ => False) Q t s

/-- `CoBuchi` with `Bad = True` (`◇□ False`) collapses to total correctness `DWP`. -/
theorem coBuchi_true_iff_dwp (ewp : StateEffectWP S E) (Q : R → S → Prop)
    (t : ITree E R) (s : S) :
    CoBuchi ewp (fun _ _ _ _ => True) Q t s ↔ DWP ewp t Q s := by
  rw [coBuchi_iff, fairInfOften_true_iff_infOften]
  exact ⟨fun h => (buchiProgress_false_iff_dwp ewp Q _ t s).1 h.toBuchiProgress,
    infOften_of_dwp _⟩

@[simp]
theorem CoBuchi.ret_iff (ewp : StateEffectWP S E)
    (Bad : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (r : R) (s : S) :
    CoBuchi ewp Bad Q (.ret r) s ↔ Q r s :=
  FairInfOften.ret_iff ewp _ Bad Q r s

@[simp]
theorem CoBuchi.tau_iff (ewp : StateEffectWP S E)
    (Bad : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (t : ITree E R) (s : S) :
    CoBuchi ewp Bad Q (.tau t) s ↔ CoBuchi ewp Bad Q t s :=
  FairInfOften.tau_iff ewp _ Bad Q t s

@[simp]
theorem CoBuchi.vis_iff (ewp : StateEffectWP S E)
    (Bad : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (i : E.I) (k : E.O i → ITree E R) (s : S) :
    CoBuchi ewp Bad Q (.vis i k) s ↔
      ewp.wp i (fun o s' => CoBuchi ewp Bad Q (k o) s') s :=
  FairInfOften.vis_iff ewp _ Bad Q i k s

theorem CoBuchi.ret {ewp : StateEffectWP S E}
    {Bad : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {r : R} {s : S} (hq : Q r s) : CoBuchi ewp Bad Q (.ret r) s :=
  FairInfOften.ret hq

theorem CoBuchi.tau {ewp : StateEffectWP S E}
    {Bad : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t : ITree E R} {s : S} (h : CoBuchi ewp Bad Q t s) :
    CoBuchi ewp Bad Q (.tau t) s :=
  FairInfOften.tau h

theorem CoBuchi.vis {ewp : StateEffectWP S E}
    {Bad : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {i : E.I} {k : E.O i → ITree E R} {s : S}
    (hv : ewp.wp i (fun o s' => CoBuchi ewp Bad Q (k o) s') s) :
    CoBuchi ewp Bad Q (.vis i k) s :=
  FairInfOften.vis hv

/-- Persistence implies partial correctness (`DWLP`). -/
theorem CoBuchi.toDWLP {ewp : StateEffectWP S E}
    {Bad : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t : ITree E R} {s : S} (h : CoBuchi ewp Bad Q t s) :
    DWLP ewp t Q s :=
  FairInfOften.toDWLP h

/-- `CoBuchi` is invariant under equivalence up to finite `.tau`s (`Eutt`). -/
theorem CoBuchi.eutt {ewp : StateEffectWP S E}
    {Bad : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t u : ITree E R} {s : S} (he : Eutt t u) (h : CoBuchi ewp Bad Q t s) :
    CoBuchi ewp Bad Q u s :=
  FairInfOften.eutt he h

/-- `Eutt`-equivalent trees satisfy the exact same `CoBuchi` specs. -/
theorem CoBuchi.eutt_iff (ewp : StateEffectWP S E)
    (Bad : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    {t u : ITree E R} (he : Eutt t u) (s : S) :
    CoBuchi ewp Bad Q t s ↔ CoBuchi ewp Bad Q u s :=
  ⟨CoBuchi.eutt he, CoBuchi.eutt he.symm⟩

/-- Monadic bind rule for `CoBuchi`. -/
theorem CoBuchi.bind {A B : Type u} {ewp : StateEffectWP S E}
    {Bad : (i : E.I) → E.O i → S → S → Prop} {Q : B → S → Prop}
    {t : ITree E A} {k : A → ITree E B} {s : S}
    (h : CoBuchi ewp Bad (fun a s' => CoBuchi ewp Bad Q (k a) s') t s) :
    CoBuchi ewp Bad Q (t >>= k) s :=
  FairInfOften.bind h

/-- Exact monadic bind characterisation for `CoBuchi`. -/
theorem CoBuchi.bind_iff {A B : Type u} (ewp : StateEffectWP S E)
    (Bad : (i : E.I) → E.O i → S → S → Prop) (Q : B → S → Prop)
    (t : ITree E A) (k : A → ITree E B) (s : S) :
    CoBuchi ewp Bad Q (t >>= k) s ↔
      CoBuchi ewp Bad (fun a s' => CoBuchi ewp Bad Q (k a) s') t s :=
  FairInfOften.bind_iff ewp _ Bad Q t k s

/-- Sequencing a terminating prefix before a persistent continuation. -/
theorem CoBuchi.bind_dwp {A B : Type u} {ewp : StateEffectWP S E}
    {Bad : (i : E.I) → E.O i → S → S → Prop} {P : A → S → Prop}
    {Q : B → S → Prop} {t : ITree E A} {k : A → ITree E B} {s : S}
    (ht : DWP ewp t P s)
    (hk : ∀ a s', P a s' → CoBuchi ewp Bad Q (k a) s') :
    CoBuchi ewp Bad Q (t >>= k) s :=
  FairInfOften.bind_dwp (DWP.mono hk ht)

/-- Conditional branching rule for `CoBuchi`. -/
theorem CoBuchi.ite {ewp : StateEffectWP S E}
    {Bad : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {c : Prop} [Decidable c] {t₁ t₂ : ITree E R} {s : S}
    (h₁ : c → CoBuchi ewp Bad Q t₁ s)
    (h₂ : ¬ c → CoBuchi ewp Bad Q t₂ s) :
    CoBuchi ewp Bad Q (if c then t₁ else t₂) s :=
  FairInfOften.ite h₁ h₂

/-- `Sum`-branching rule for `CoBuchi`. -/
theorem CoBuchi.sum_elim {A B : Type u} {ewp : StateEffectWP S E}
    {Bad : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {f : A → ITree E R} {g : B → ITree E R} {s : S} (x : A ⊕ B)
    (h₁ : ∀ a, x = .inl a → CoBuchi ewp Bad Q (f a) s)
    (h₂ : ∀ b, x = .inr b → CoBuchi ewp Bad Q (g b) s) :
    CoBuchi ewp Bad Q (Sum.elim f g x) s :=
  FairInfOften.sum_elim x h₁ h₂

/-- Monotonicity of `CoBuchi` in the effect transformer `ewp`. -/
theorem CoBuchi.mono_wp {ewp ewp' : StateEffectWP S E}
    {Bad : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    {t : ITree E R} {s : S}
    (h_wp : ∀ i K s₀, ewp.wp i K s₀ → ewp'.wp i K s₀)
    (h : CoBuchi ewp Bad Q t s) : CoBuchi ewp' Bad Q t s :=
  FairInfOften.mono_wp h_wp h

/-- Merge `Always` safety into `CoBuchi` over `guardInvWP`. -/
theorem CoBuchi.guardInv_of_always {ewp : StateEffectWP S E}
    [StateEffectWP.Conjunctive ewp]
    {Bad : (i : E.I) → E.O i → S → S → Prop} {Inv : S → Prop}
    {P Q : R → S → Prop} {t : ITree E R} {s : S}
    (h_safe : Always ewp Inv P t s) (h : CoBuchi ewp Bad Q t s) :
    CoBuchi (guardInvWP ewp Inv) Bad Q t s :=
  FairInfOften.guardInv_of_always h_safe h

/-- Merge `AlwaysStep` into `CoBuchi` over `guardStepWP`. -/
theorem CoBuchi.guardStep_of_alwaysStep {ewp : StateEffectWP S E}
    [StateEffectWP.Conjunctive ewp]
    {Bad StepRel : (i : E.I) → E.O i → S → S → Prop}
    {P Q : R → S → Prop} {t : ITree E R} {s : S}
    (h_safe : AlwaysStep ewp StepRel P t s) (h : CoBuchi ewp Bad Q t s) :
    CoBuchi (guardStepWP ewp StepRel) Bad Q t s :=
  FairInfOften.guardStep_of_alwaysStep h_safe h

/--
A productive tree that never takes a `Bad` edge (`AlwaysStep (¬ Bad)`) satisfies
`CoBuchi ewp Bad Q` (`□ ¬ Bad ∧ productive → ◇□ ¬ Bad`).
-/
theorem CoBuchi.of_alwaysStep_not_bad {ewp : StateEffectWP S E}
    [StateEffectWP.Conjunctive ewp]
    {Bad : (i : E.I) → E.O i → S → S → Prop} {P Q : R → S → Prop}
    {t : ITree E R} {s : S}
    (h_nb : AlwaysStep ewp (fun i o s₀ s' => ¬ Bad i o s₀ s') P t s)
    (h_prod : InfOften ewp (fun _ _ _ _ => True) Q t s) :
    CoBuchi ewp Bad Q t s :=
  FairInfOften.of_never_fair h_nb h_prod

/--
**Co-Büchi conjunction closure (`◇□ ¬ Bad₁ ∧ ◇□ ¬ Bad₂ → ◇□ ¬ (Bad₁ ∨ Bad₂)`).**
Under `[Conjunctive ewp]`, two independent persistence properties compose by
nested `fairProgress` induction + `fairStall` coinduction, combining BOTH their
excluded edge classes (`Bad₁ ∨ Bad₂`) AND their return postconditions (`P ∧ Q`).
-/
theorem CoBuchi.conj_bad {ewp : StateEffectWP S E}
    [h_conj : StateEffectWP.Conjunctive ewp]
    {Bad₁ Bad₂ : (i : E.I) → E.O i → S → S → Prop}
    {P Q : R → S → Prop} {t : ITree E R} {s : S}
    (h₁ : CoBuchi ewp Bad₁ P t s) (h₂ : CoBuchi ewp Bad₂ Q t s) :
    CoBuchi ewp (fun i o s₀ s' => Bad₁ i o s₀ s' ∨ Bad₂ i o s₀ s')
      (fun r s' => P r s' ∧ Q r s') t s := by
  let Bad := fun i o s₀ s' => Bad₁ i o s₀ s' ∨ Bad₂ i o s₀ s'
  let PQ := fun r s' => P r s' ∧ Q r s'
  let X₁ := FairInfOften ewp (fun _ _ _ _ => False) Bad₁ P
  let X₂ := FairInfOften ewp (fun _ _ _ _ => False) Bad₂ Q
  let Xo := FairInfOften ewp (fun _ _ _ _ => False) Bad PQ
  unfold CoBuchi at h₁ h₂ ⊢
  rw [FairInfOften.unfold_eq] at h₁
  refine fairProgress.induct (fun x s₀ => X₂ x s₀ → Xo x s₀) ?_ h₁ h₂
  intro x s₀ hx₁ hx₂
  have hx₂_u := hx₂
  dsimp only [X₂] at hx₂_u
  rw [FairInfOften.unfold_eq] at hx₂_u
  refine fairProgress.induct
    (fun y s₁ =>
      fairStall ewp (fun _ _ _ _ => False) Bad₁ P X₁ (fun v s' => X₂ v s' → Xo v s') y s₁ →
      X₂ y s₁ → Xo y s₁) ?_ hx₂_u hx₁ hx₂
  intro y s₁ hy₂ hy₁ hy₂_cb
  dsimp only [Xo]
  rw [FairInfOften.unfold_eq, fairProgress.unfold_eq]
  let Z : ITree E R → S → Prop := fun z s₂ =>
    fairStall ewp (fun _ _ _ _ => False) Bad₁ P X₁ (fun v s' => X₂ v s' → Xo v s') z s₂ ∧
    fairStall ewp (fun _ _ _ _ => False) Bad₂ Q X₂
      (fun v s' =>
        fairStall ewp (fun _ _ _ _ => False) Bad₁ P X₁ (fun u s'' => X₂ u s'' → Xo u s'') v s' →
        X₂ v s' → Xo v s') z s₂ ∧
    X₂ z s₂
  refine fairStall.coinduct Z ?_ ⟨hy₁, hy₂, hy₂_cb⟩
  rintro z s₂ ⟨hz₁, hz₂, hz₂_cb⟩
  rw [fairStall.unfold_eq] at hz₁ hz₂
  refine fairStep.induct
    (fun w s₃ =>
      fairStep ewp (fun _ _ _ _ => False) Bad₂ Q X₂
        (fun v s' =>
          fairStall ewp (fun _ _ _ _ => False) Bad₁ P X₁
            (fun u s'' => X₂ u s'' → Xo u s'') v s' →
          X₂ v s' → Xo v s')
        (fairStall ewp (fun _ _ _ _ => False) Bad₂ Q X₂
          (fun v s' =>
            fairStall ewp (fun _ _ _ _ => False) Bad₁ P X₁
              (fun u s'' => X₂ u s'' → Xo u s'') v s' →
            X₂ v s' → Xo v s')) w s₃ →
      X₂ w s₃ →
      fairStep ewp (fun _ _ _ _ => False) Bad PQ Xo
        (fairProgress ewp (fun _ _ _ _ => False) Bad PQ Xo) Z w s₃)
    ?_ hz₁ hz₂ hz₂_cb
  intro w s₃ hw₁ hw₂ hw₂_cb
  rw [fairStep.unfold_eq] at hw₂ ⊢
  cases h_obs : w.observe with
  | ret r =>
    simp only [h_obs] at hw₁ hw₂ ⊢
    exact ⟨hw₁, hw₂⟩
  | tau w' =>
    simp only [h_obs] at hw₁ hw₂ ⊢
    dsimp only [X₂] at hw₂_cb
    rw [eq_tau_of_observe h_obs, FairInfOften.tau_iff] at hw₂_cb
    exact hw₁ hw₂ hw₂_cb
  | vis i k =>
    simp only [h_obs] at hw₁ hw₂ ⊢
    dsimp only [X₂] at hw₂_cb
    rw [eq_vis_of_observe h_obs, FairInfOften.vis_iff] at hw₂_cb
    refine ewp.mono (fun o s' ⟨⟨hp₁, hp₂⟩, hcb₂⟩ => ?_)
      (h_conj.conj (h_conj.conj hw₁ hw₂) hw₂_cb)
    rcases hp₁ with ⟨hf, _⟩ | ⟨hb₁, hpre₁⟩ | ⟨hnb₁, hst₁⟩
    · exact False.elim hf
    · refine Or.inr (Or.inl ⟨Or.inl hb₁, ?_⟩)
      have hxo := hpre₁ hcb₂
      dsimp only [Xo] at hxo
      rw [FairInfOften.unfold_eq] at hxo; exact hxo
    · rcases hp₂ with ⟨hf, _⟩ | ⟨hb₂, hpre₂⟩ | ⟨hnb₂, hst₂⟩
      · exact False.elim hf
      · refine Or.inr (Or.inl ⟨Or.inr hb₂, ?_⟩)
        have hxo := hpre₂ hst₁ hcb₂
        dsimp only [Xo] at hxo
        rw [FairInfOften.unfold_eq] at hxo; exact hxo
      · exact Or.inr (Or.inr ⟨fun hb => hb.elim hnb₁ hnb₂, hst₁, hst₂, hcb₂⟩)

/-- Same-predicate postcondition conjunction for `CoBuchi`. -/
theorem CoBuchi.conj {ewp : StateEffectWP S E}
    [StateEffectWP.Conjunctive ewp]
    {Bad : (i : E.I) → E.O i → S → S → Prop} {P Q : R → S → Prop}
    {t : ITree E R} {s : S}
    (hp : CoBuchi ewp Bad P t s) (hq : CoBuchi ewp Bad Q t s) :
    CoBuchi ewp Bad (fun r s' => P r s' ∧ Q r s') t s :=
  FairInfOften.conj hp hq

/-- Well-founded loop rule for `ITree.iter` under `CoBuchi` (finite `Bad` budget). -/
theorem CoBuchi.iter_wf {I : Type u} {α : Type _} {ewp : StateEffectWP S E}
    {Bad : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    (lt : α → α → Prop) (h_wf : WellFounded lt)
    (body : I → ITree E (I ⊕ R)) (LInv : α → I → S → Prop)
    (h_body : ∀ m a s₀, LInv m a s₀ →
      fairStep ewp (fun _ _ _ _ => False) Bad
        (Sum.elim (fun next s' => ∃ m', lt m' m ∧ LInv m' next s') Q)
        (CoBuchi ewp Bad (Sum.elim (fun next s' => ∃ m', LInv m' next s') Q))
        (fairProgress ewp (fun _ _ _ _ => False) Bad
          (Sum.elim (fun next s' => ∃ m', lt m' m ∧ LInv m' next s') Q)
          (CoBuchi ewp Bad (Sum.elim (fun next s' => ∃ m', LInv m' next s') Q)))
        (fairStall ewp (fun _ _ _ _ => False) Bad
          (Sum.elim (fun next s' => LInv m next s' ∨ ∃ m', lt m' m ∧ LInv m' next s') Q)
          (CoBuchi ewp Bad (Sum.elim (fun next s' => ∃ m', LInv m' next s') Q))
          (fairProgress ewp (fun _ _ _ _ => False) Bad
            (Sum.elim (fun next s' => ∃ m', lt m' m ∧ LInv m' next s') Q)
            (CoBuchi ewp Bad (Sum.elim (fun next s' => ∃ m', LInv m' next s') Q))))
        (body a) s₀)
    {m : α} {init : I} {s : S} (h_init : LInv m init s) :
    CoBuchi ewp Bad Q (ITree.iter body init) s :=
  FairInfOften.iter_wf lt h_wf body LInv h_body h_init

/-- `Nat`-ranked loop rule for `ITree.iter` under `CoBuchi`. -/
theorem CoBuchi.iter_ranked {I : Type u} {ewp : StateEffectWP S E}
    {Bad : (i : E.I) → E.O i → S → S → Prop} {Q : R → S → Prop}
    (body : I → ITree E (I ⊕ R)) (LInv : Nat → I → S → Prop)
    (h_body : ∀ n a s₀, LInv n a s₀ →
      fairStep ewp (fun _ _ _ _ => False) Bad
        (Sum.elim (fun next s' => ∃ m, m < n ∧ LInv m next s') Q)
        (CoBuchi ewp Bad (Sum.elim (fun next s' => ∃ m, LInv m next s') Q))
        (fairProgress ewp (fun _ _ _ _ => False) Bad
          (Sum.elim (fun next s' => ∃ m, m < n ∧ LInv m next s') Q)
          (CoBuchi ewp Bad (Sum.elim (fun next s' => ∃ m, LInv m next s') Q)))
        (fairStall ewp (fun _ _ _ _ => False) Bad
          (Sum.elim (fun next s' => LInv n next s' ∨ ∃ m, m < n ∧ LInv m next s') Q)
          (CoBuchi ewp Bad (Sum.elim (fun next s' => ∃ m, LInv m next s') Q))
          (fairProgress ewp (fun _ _ _ _ => False) Bad
            (Sum.elim (fun next s' => ∃ m, m < n ∧ LInv m next s') Q)
            (CoBuchi ewp Bad (Sum.elim (fun next s' => ∃ m, LInv m next s') Q))))
        (body a) s₀)
    {n : Nat} {init : I} {s : S} (h_init : LInv n init s) :
    CoBuchi ewp Bad Q (ITree.iter body init) s :=
  FairInfOften.iter_ranked body LInv h_body h_init

/-- Well-founded diverging `-> !` reactive loop rule for `CoBuchi`. -/
theorem coBuchi_diverging_loop_wf {I : Type u} {α : Type _}
    {ewp : StateEffectWP S E}
    {Bad : (i : E.I) → E.O i → S → S → Prop} {Inv : S → Prop}
    (lt : α → α → Prop) (h_wf : WellFounded lt)
    (body : I → ITree E I) (LInv : α → I → S → Prop)
    (h_safe : ∀ m a s₀, LInv m a s₀ →
      Always ewp Inv (fun next s' => ∃ m', LInv m' next s') (body a) s₀)
    (h_live : ∀ m a s₀, LInv m a s₀ →
      fairStep ewp (fun _ _ _ _ => False) Bad
        (fun next s' => ∃ m', lt m' m ∧ LInv m' next s')
        (CoBuchi ewp Bad (fun next s' => ∃ m', LInv m' next s'))
        (fairProgress ewp (fun _ _ _ _ => False) Bad
          (fun next s' => ∃ m', lt m' m ∧ LInv m' next s')
          (CoBuchi ewp Bad (fun next s' => ∃ m', LInv m' next s')))
        (fairStall ewp (fun _ _ _ _ => False) Bad
          (fun next s' => LInv m next s' ∨ ∃ m', lt m' m ∧ LInv m' next s')
          (CoBuchi ewp Bad (fun next s' => ∃ m', LInv m' next s'))
          (fairProgress ewp (fun _ _ _ _ => False) Bad
            (fun next s' => ∃ m', lt m' m ∧ LInv m' next s')
            (CoBuchi ewp Bad (fun next s' => ∃ m', LInv m' next s'))))
        (body a) s₀)
    {m : α} {init : I} {s : S} (h_init : LInv m init s)
    (Q : PEmpty.{u + 1} → S → Prop) :
    Always ewp Inv Q (divergingLoop body init) s ∧
      CoBuchi ewp Bad Q (divergingLoop body init) s :=
  fair_diverging_loop_wf lt h_wf body LInv h_safe h_live h_init Q

/-- `Nat`-ranked diverging `-> !` reactive loop rule for `CoBuchi`. -/
theorem coBuchi_diverging_loop_ranked {I : Type u} {ewp : StateEffectWP S E}
    {Bad : (i : E.I) → E.O i → S → S → Prop} {Inv : S → Prop}
    (body : I → ITree E I) (LInv : Nat → I → S → Prop)
    (h_safe : ∀ n a s₀, LInv n a s₀ →
      Always ewp Inv (fun next s' => ∃ m, LInv m next s') (body a) s₀)
    (h_live : ∀ n a s₀, LInv n a s₀ →
      fairStep ewp (fun _ _ _ _ => False) Bad
        (fun next s' => ∃ m, m < n ∧ LInv m next s')
        (CoBuchi ewp Bad (fun next s' => ∃ m, LInv m next s'))
        (fairProgress ewp (fun _ _ _ _ => False) Bad
          (fun next s' => ∃ m, m < n ∧ LInv m next s')
          (CoBuchi ewp Bad (fun next s' => ∃ m, LInv m next s')))
        (fairStall ewp (fun _ _ _ _ => False) Bad
          (fun next s' => LInv n next s' ∨ ∃ m, m < n ∧ LInv m next s')
          (CoBuchi ewp Bad (fun next s' => ∃ m, LInv m next s'))
          (fairProgress ewp (fun _ _ _ _ => False) Bad
            (fun next s' => ∃ m, m < n ∧ LInv m next s')
            (CoBuchi ewp Bad (fun next s' => ∃ m, LInv m next s'))))
        (body a) s₀)
    {n : Nat} {init : I} {s : S} (h_init : LInv n init s)
    (Q : PEmpty.{u + 1} → S → Prop) :
    Always ewp Inv Q (divergingLoop body init) s ∧
      CoBuchi ewp Bad Q (divergingLoop body init) s :=
  fair_diverging_loop_ranked body LInv h_safe h_live h_init Q

/-- Horizontal handler linking for `CoBuchi` across `ITree.interp`. -/
theorem CoBuchi.interp {E₁ E₂ : Effect.{u}}
    {ewp₁ : StateEffectWP S E₁} {ewp₂ : StateEffectWP S E₂}
    {Bad₁ : (i : E₁.I) → E₁.O i → S → S → Prop}
    {Bad₂ : (j : E₂.I) → E₂.O j → S → S → Prop}
    (h : (i : E₁.I) → ITree E₂ (E₁.O i))
    (h_link : ∀ (i : E₁.I) (K3 K2 : E₁.O i → S → Prop) (s₀ : S),
      ewp₁.wp i (fun o s' =>
        (Bad₁ i o s₀ s' ∧ K3 o s') ∨
        (¬ Bad₁ i o s₀ s' ∧ K2 o s')) s₀ →
      fairStep ewp₂ (fun _ _ _ _ => False) Bad₂ K3
        (CoBuchi ewp₂ Bad₂ (fun o s'' => K3 o s'' ∨ K2 o s''))
        (fairProgress ewp₂ (fun _ _ _ _ => False) Bad₂ K3
          (CoBuchi ewp₂ Bad₂ (fun o s'' => K3 o s'' ∨ K2 o s'')))
        (fairStall ewp₂ (fun _ _ _ _ => False) Bad₂
          (fun o s'' => K3 o s'' ∨ K2 o s'')
          (CoBuchi ewp₂ Bad₂ (fun o s'' => K3 o s'' ∨ K2 o s''))
          (fairProgress ewp₂ (fun _ _ _ _ => False) Bad₂ K3
            (CoBuchi ewp₂ Bad₂ (fun o s'' => K3 o s'' ∨ K2 o s''))))
        (h i) s₀)
    {t : ITree E₁ R} {Q : R → S → Prop} {s : S}
    (h_cb : CoBuchi ewp₁ Bad₁ Q t s) :
    CoBuchi ewp₂ Bad₂ Q (ITree.interp h t) s :=
  FairInfOften.interp h (fun i K4 K3 K2 s₀ hw =>
    have hw' := ewp₁.mono (fun _ _ hp => hp.elim (fun ⟨hf, _⟩ => False.elim hf) id) hw
    have hst := h_link i K3 K2 s₀ hw'
    have h_fi : ∀ x s',
        CoBuchi ewp₂ Bad₂ (fun o s'' => K3 o s'' ∨ K2 o s'') x s' →
        FairInfOften ewp₂ (fun _ _ _ _ => False) Bad₂
          (fun o s'' => K4 o s'' ∨ K3 o s'' ∨ K2 o s'') x s' :=
      fun _ _ hx => FairInfOften.mono_post (fun _ _ h => Or.inr h) hx
    fairStep.mono (fun _ _ hx => h_fi _ _ hx)
      (fun _ _ hx => fairProgress.mono (fun _ _ h => h_fi _ _ h) hx)
      (fun _ _ hx => fairStall.mono (fun _ _ h => h_fi _ _ h)
        (fun _ _ h => fairProgress.mono (fun _ _ h' => h_fi _ _ h') h) hx)
      hst) h_cb

/--
**Target-stateful handler linking** for `CoBuchi` across `ITree.interpState`:
threads handler state `H` while preserving target logical state `S₂`.
-/
theorem CoBuchi.interpState_stateful {S₂ H : Type u} {E₁ E₂ : Effect.{u}}
    {ewp₁ : StateEffectWP (S₂ × H) E₁} {ewp₂ : StateEffectWP S₂ E₂}
    {Bad₁ : (i : E₁.I) → E₁.O i → S₂ × H → S₂ × H → Prop}
    {Bad₂ : (j : E₂.I) → E₂.O j → S₂ → S₂ → Prop}
    (h : (i : E₁.I) → H → ITree E₂ (E₁.O i × H))
    (h_link : ∀ (i : E₁.I) (K3 K2 : E₁.O i → S₂ × H → Prop)
      (s₂ : S₂) (st : H),
      ewp₁.wp i (fun o p' =>
        (Bad₁ i o (s₂, st) p' ∧ K3 o p') ∨
        (¬ Bad₁ i o (s₂, st) p' ∧ K2 o p')) (s₂, st) →
      fairStep ewp₂ (fun _ _ _ _ => False) Bad₂
        (fun pair s₂' => K3 pair.1 (s₂', pair.2))
        (CoBuchi ewp₂ Bad₂
          (fun pair s₂' => K3 pair.1 (s₂', pair.2) ∨ K2 pair.1 (s₂', pair.2)))
        (fairProgress ewp₂ (fun _ _ _ _ => False) Bad₂
          (fun pair s₂' => K3 pair.1 (s₂', pair.2))
          (CoBuchi ewp₂ Bad₂
            (fun pair s₂' => K3 pair.1 (s₂', pair.2) ∨ K2 pair.1 (s₂', pair.2))))
        (fairStall ewp₂ (fun _ _ _ _ => False) Bad₂
          (fun pair s₂' => K3 pair.1 (s₂', pair.2) ∨ K2 pair.1 (s₂', pair.2))
          (CoBuchi ewp₂ Bad₂
            (fun pair s₂' => K3 pair.1 (s₂', pair.2) ∨ K2 pair.1 (s₂', pair.2)))
          (fairProgress ewp₂ (fun _ _ _ _ => False) Bad₂
            (fun pair s₂' => K3 pair.1 (s₂', pair.2))
            (CoBuchi ewp₂ Bad₂
              (fun pair s₂' => K3 pair.1 (s₂', pair.2) ∨ K2 pair.1 (s₂', pair.2)))))
        (h i st) s₂)
    {t : ITree E₁ R} {Q : R → S₂ × H → Prop} {s₂ : S₂} {st : H}
    (h_cb : CoBuchi ewp₁ Bad₁ Q t (s₂, st)) :
    CoBuchi ewp₂ Bad₂ (fun pair s₂' => Q pair.1 (s₂', pair.2))
      (ITree.interpState h t st) s₂ :=
  FairInfOften.interpState_stateful h (fun i K4 K3 K2 s₂ st hw =>
    have hw' := ewp₁.mono (fun _ _ hp => hp.elim (fun ⟨hf, _⟩ => False.elim hf) id) hw
    have hst := h_link i K3 K2 s₂ st hw'
    have h_fi : ∀ x s',
        CoBuchi ewp₂ Bad₂
          (fun (pair : E₁.O i × H) s₂' => K3 pair.1 (s₂', pair.2) ∨ K2 pair.1 (s₂', pair.2))
          x s' →
        FairInfOften ewp₂ (fun _ _ _ _ => False) Bad₂
          (fun (pair : E₁.O i × H) s₂' =>
            K4 pair.1 (s₂', pair.2) ∨ K3 pair.1 (s₂', pair.2) ∨
              K2 pair.1 (s₂', pair.2)) x s' :=
      fun _ _ hx => FairInfOften.mono_post (fun _ _ h => Or.inr h) hx
    fairStep.mono (fun _ _ hx => h_fi _ _ hx)
      (fun _ _ hx => fairProgress.mono (fun _ _ h => h_fi _ _ h) hx)
      (fun _ _ hx => fairStall.mono (fun _ _ h => h_fi _ _ h)
        (fun _ _ h => fairProgress.mono (fun _ _ h' => h_fi _ _ h') h) hx)
      hst) h_cb

/-- Stateless operational adequacy for `CoBuchi`. -/
theorem coBuchi_pure_adequacy {E : Effect.{u}} {R : Type u}
    [FaultEffect E] {ewp : EffectWP E} [PureSoundWP ewp]
    {Bad : (i : E.I) → E.O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop}
    {t : ITree E R} {post : R → Prop}
    (h : CoBuchi ewp Bad (fun r _ => post r) t PUnit.unit) :
    TreeSafe t ∧ Productive t ∧ ¬ MayDiverge t ∧
      ∀ tr r, ReachesRet t tr r → post r :=
  fairInfOften_pure_adequacy h

open Std.Do in
/-- `CoBuchi` over a `PureEffectWP` yields the corresponding `Std.Do.Triple`. -/
theorem Triple.of_coBuchi {E : Effect.{u}} {R : Type u} [p : PureEffectWP E]
    {Bad : (i : E.I) → E.O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop}
    {t : ITree E R} {P : Prop} {Q : R → Prop}
    (h : P → CoBuchi p.ewp Bad (fun r _ => Q r) t PUnit.unit) :
    ⦃⌜P⌝⦄ t ⦃⇓ r => ⌜Q r⌝⦄ :=
  Triple.of_fairInfOften h

/--
**Exact $\omega$-language co-Büchi adequacy (`FollowsStream`)**: a non-returning
observation tree `t : ITree (ObsE α) PEmpty` satisfies `CoBuchi` for `BadObs`
**if and only if** it emits an infinite stream `s : Stream' α` with only finitely
many `BadObs` elements (`∃ K, ∀ n ≥ K, ¬ BadObs (s n)`).
-/
theorem coBuchi_obsIgnoreWP_iff_followsStream {α : Type u}
    (BadObs : α → Prop) (Q : PEmpty.{u + 1} → PUnit.{u + 1} → Prop)
    (t : ITree (ObsE α) PEmpty.{u + 1}) :
    CoBuchi (obsIgnoreWP PUnit.{u + 1} α)
        (fun i _ _ _ => match i with | .emit a => BadObs a) Q t PUnit.unit ↔
      ∃ s : Stream' α, FollowsStream t s ∧
        ∃ K : Nat, ∀ n : Nat, K ≤ n → ¬ BadObs (s n) := by
  have h_eq := fairInfOften_obsIgnoreWP_iff_followsStream
    (fun _ : α => False) BadObs Q t
  have h_acc : (fun i (_ : (ObsE α).O i) (_ _ : PUnit.{u + 1}) =>
      match i with | .emit _ => False) = (fun _ _ _ _ => False) := by
    funext i _ _ _; cases i; rfl
  rw [coBuchi_iff, ← h_acc, h_eq]
  refine exists_congr fun s => and_congr_right fun _ => ⟨fun h => ?_, fun ⟨K, hK⟩ hinf _ => ?_⟩
  · have h_not : ¬ ∀ k : Nat, ∃ n : Nat, k ≤ n ∧ BadObs (s n) := fun hinf =>
      let ⟨_, _, hf⟩ := h hinf 0; hf
    obtain ⟨K, hK⟩ := Classical.not_forall.1 h_not
    exact ⟨K, fun n hle hb => hK ⟨n, hle, hb⟩⟩
  · obtain ⟨n, hle, hb⟩ := hinf K
    exact False.elim (hK n hle hb)

end CoBuchi

/-! #### General `EnvStrategy` Operational Adequacy (All Effects, All `σ`) -/

section StrategyAdequacy

/-- First `n` elements of an infinite stream `ev : Stream' α` as a `List α`. -/
def takePrefix {α : Type u} (ev : Stream' α) (n : Nat) : List α :=
  Nat.rec [] (fun k ih => ih ++ [ev k]) n

@[simp]
theorem takePrefix_zero {α : Type u} (ev : Stream' α) :
    takePrefix ev 0 = [] := rfl

@[simp]
theorem takePrefix_succ {α : Type u} (ev : Stream' α) (n : Nat) :
    takePrefix ev (n + 1) = takePrefix ev n ++ [ev n] := rfl

/--
`t` reaches a return value `r` along finite event trace `tr` when executed from
history `hist` against deterministic environment strategy `σ`.
-/
def RetWithStrategy {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (σ : EnvStrategy E) (hist : List (Event E)) (t : ITree E R)
    (tr : List (Event E)) (r : R) : Prop :=
  ∃ u, ReachesWithStrategy σ hist t tr u ∧ u.observe = .ret r

/--
`t` exhibits the infinite event stream `ev : Stream' (Event E)` when executed
from history `hist` against deterministic environment strategy `σ`: every
finite prefix `takePrefix ev n` is reachable via `ReachesWithStrategy`.
-/
def InfRunWithStrategy {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (σ : EnvStrategy E) (hist : List (Event E)) (t : ITree E R)
    (ev : Stream' (Event E)) : Prop :=
  ∀ n : Nat, ∃ u, ReachesWithStrategy σ hist t (takePrefix ev n) u

/-- Lift a stateless `EffectWP E` to a trace-recording `StateEffectWP (List (Event E)) E`. -/
def traceLiftWP {E : Effect.{u}} (ewp : EffectWP E) :
    StateEffectWP (List (Event E)) E where
  wp i K tr := ewp.wp i (fun o _ => K o (tr ++ [⟨i, o⟩])) PUnit.unit
  mono h_imp h_wp := ewp.mono (fun o _ hk => h_imp o _ hk) h_wp

instance {E : Effect.{u}} [FaultEffect E] (ewp : EffectWP E) [h : PureSoundWP ewp] :
    TraceSoundWP (traceLiftWP ewp) where
  sound h_wp := h.sound h_wp

/-- Lift a stateless `BuchiSpec` to a trace-recording `BuchiSpec (List (Event E))`. -/
def BuchiSpec.toTrace {QState : Type u} {E : Effect.{u}} {R : Type u}
    (spec : BuchiSpec PUnit.{u + 1} QState E R) :
    BuchiSpec (List (Event E)) QState E R where
  ewp := traceLiftWP spec.ewp
  step q i o _ _ q' := spec.step q i o PUnit.unit PUnit.unit q'
  accept q i o _ _ q' := spec.accept q i o PUnit.unit PUnit.unit q'
  inv q _ := spec.inv q PUnit.unit
  terminal q r _ := spec.terminal q r PUnit.unit

instance {QState : Type u} {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (spec : BuchiSpec PUnit.{u + 1} QState E R) [PureSoundWP spec.ewp] :
    TraceSoundWP spec.toTrace.ewp :=
  inferInstanceAs (TraceSoundWP (traceLiftWP spec.ewp))

private theorem reachesWithStrategy_of_tauStar {E : Effect.{u}} {R : Type u}
    [FaultEffect E] {σ : EnvStrategy E} {hist tr : List (Event E)}
    {a b c : ITree E R} (h₁ : TauStar a b)
    (h₂ : ReachesWithStrategy σ hist b tr c) :
    ReachesWithStrategy σ hist a tr c := by
  induction h₁ with
  | refl => exact h₂
  | step htau _ ih => exact .tau htau (ih h₂)

private theorem reachesWithStrategy_trans {E : Effect.{u}} {R : Type u}
    [FaultEffect E] {σ : EnvStrategy E} {hist tr₁ tr₂ : List (Event E)}
    {t u v : ITree E R} (h₁ : ReachesWithStrategy σ hist t tr₁ u)
    (h₂ : ReachesWithStrategy σ (hist ++ tr₁) u tr₂ v) :
    ReachesWithStrategy σ hist t (tr₁ ++ tr₂) v := by
  induction h₁ with
  | refl h x => simpa using h₂
  | tau htau _ ih => exact .tau htau (ih h₂)
  | vis hv hnf _ ih =>
    rw [List.cons_append]
    exact .vis hv hnf (ih (by simpa [List.append_assoc] using h₂))

private theorem tauStar_vis_inv_ret {E : Effect.{u}} {R : Type u}
    {w v : ITree E R} {r : R} {i : E.I} {k : E.O i → ITree E R}
    (hts : TauStar w v) (hw : w.observe = .ret r) (hv : v.observe = .vis i k) :
    False := by
  cases hts with
  | refl => rw [hw] at hv; exact nomatch hv
  | step htau _ => rw [hw] at htau; exact nomatch htau

private theorem tauStar_vis_inv_tau {E : Effect.{u}} {R : Type u}
    {w w' v : ITree E R} {i : E.I} {k : E.O i → ITree E R}
    (hts : TauStar w v) (hw : w.observe = .tau w') (hv : v.observe = .vis i k) :
    TauStar w' v := by
  cases hts with
  | refl => rw [hw] at hv; exact nomatch hv
  | step htau hrest =>
    rw [hw] at htau
    injection htau with heq
    exact heq ▸ hrest

private theorem tauStar_vis_inv_vis {E : Effect.{u}} {R : Type u}
    {w v : ITree E R} {i₀ i : E.I} {k₀ : E.O i₀ → ITree E R}
    {k : E.O i → ITree E R}
    (hts : TauStar w v) (hw : w.observe = .vis i₀ k₀) (hv : v.observe = .vis i k) :
    w = v := by
  cases hts with
  | refl => rfl
  | step htau _ => rw [hw] at htau; exact nomatch htau

private structure GhostStep {E : Effect.{u}} {R G : Type u} [FaultEffect E]
    (ewp : StateEffectWP (G × List (Event E)) E)
    (StepG : G → (i : E.I) → E.O i → List (Event E) → G → Prop)
    (AccEdge Fair : (i : E.I) → E.O i → G × List (Event E) → G × List (Event E) → Prop)
    (Q : R → G × List (Event E) → Prop)
    (σ : EnvStrategy E) (tr₀ : List (Event E))
    (u : ITree E R) (g : G) (tr : List (Event E)) : Type u where
  v : ITree E R
  i : E.I
  k : E.O i → ITree E R
  hnf : ¬ FaultEffect.isFault i
  g' : G
  hts : TauStar u v
  hv : v.observe = .vis i k
  hsg : StepG g i (σ (tr₀ ++ tr) i hnf) (tr₀ ++ tr) g'
  hfi' : FairInfOften ewp AccEdge Fair Q (k (σ (tr₀ ++ tr) i hnf))
    (g', tr₀ ++ (tr ++ [⟨i, σ (tr₀ ++ tr) i hnf⟩]))

private structure GhostCfg {E : Effect.{u}} {R G : Type u} [FaultEffect E]
    (ewp : StateEffectWP (G × List (Event E)) E)
    (AccEdge Fair : (i : E.I) → E.O i → G × List (Event E) → G × List (Event E) → Prop)
    (Q : R → G × List (Event E) → Prop)
    (σ : EnvStrategy E) (tr₀ : List (Event E)) (t : ITree E R) : Type u where
  u : ITree E R
  g : G
  tr : List (Event E)
  hreach : ReachesWithStrategy σ tr₀ t tr u
  hfi : FairInfOften ewp AccEdge Fair Q u (g, tr₀ ++ tr)

private theorem ghost_trace_fairInfOften_adequacy {E : Effect.{u}} {R G : Type u}
    [FaultEffect E] (ewp : StateEffectWP (G × List (Event E)) E)
    (StepG : G → (i : E.I) → E.O i → List (Event E) → G → Prop)
    (h_sound : ∀ {i K g tr}, ewp.wp i K (g, tr) →
      ¬ FaultEffect.isFault i ∧ ∀ o, ∃ g', StepG g i o tr g' ∧ K o (g', tr ++ [⟨i, o⟩]))
    (h_det : ∀ g i o tr g₁ g₂, StepG g i o tr g₁ → StepG g i o tr g₂ → g₁ = g₂)
    (AccEdge Fair : (i : E.I) → E.O i → G × List (Event E) → G × List (Event E) → Prop)
    (Q : R → G × List (Event E) → Prop) (σ : EnvStrategy E)
    {t : ITree E R} {g₀ : G} {tr₀ : List (Event E)}
    (h : FairInfOften ewp AccEdge Fair Q t (g₀, tr₀)) :
    (∃ tr r g', RetWithStrategy σ tr₀ t tr r ∧ Q r (g', tr₀ ++ tr)) ∨
      (∃ (ev : Stream' (Event E)) (g : Stream' G),
        InfRunWithStrategy σ tr₀ t ev ∧ g 0 = g₀ ∧
        (∀ n, StepG (g n) (ev n).req (ev n).ans (tr₀ ++ takePrefix ev n) (g (n + 1))) ∧
        ((∀ k, ∃ n, k ≤ n ∧
            Fair (ev n).req (ev n).ans (g n, tr₀ ++ takePrefix ev n)
              (g (n + 1), tr₀ ++ takePrefix ev (n + 1))) →
          (∀ k, ∃ n, k ≤ n ∧
            AccEdge (ev n).req (ev n).ans (g n, tr₀ ++ takePrefix ev n)
              (g (n + 1), tr₀ ++ takePrefix ev (n + 1))))) := by
  by_cases h_ret : ∃ tr r g', RetWithStrategy σ tr₀ t tr r ∧ Q r (g', tr₀ ++ tr)
  · exact Or.inl h_ret
  · right
    have h_step_ne : ∀ c : GhostCfg ewp AccEdge Fair Q σ tr₀ t,
        Nonempty (GhostStep ewp StepG AccEdge Fair Q σ tr₀ c.u c.g c.tr) := by
      intro c
      have hfs := (FairInfOften.iff_fairStep ewp AccEdge Fair Q c.u (c.g, tr₀ ++ c.tr)).1 c.hfi
      refine fairStep.induct
        (fun w p => TauStar c.u w → p = (c.g, tr₀ ++ c.tr) →
          Nonempty (GhostStep ewp StepG AccEdge Fair Q σ tr₀ c.u c.g c.tr))
        ?_ hfs (.refl c.u) rfl
      intro w p hw hts hp
      subst hp
      cases h_obs : w.observe with
      | ret r =>
        simp only [h_obs] at hw
        have hreach_w : ReachesWithStrategy σ tr₀ t c.tr w := by
          have hr := reachesWithStrategy_trans c.hreach
            (reachesWithStrategy_of_tauStar hts (.refl (tr₀ ++ c.tr) w))
          simpa using hr
        exact False.elim (h_ret ⟨c.tr, r, c.g, ⟨w, hreach_w, h_obs⟩, hw⟩)
      | tau w' =>
        simp only [h_obs] at hw
        exact hw (TauStar.trans hts (.step h_obs (.refl w'))) trivial
      | vis i k =>
        simp only [h_obs] at hw
        obtain ⟨hnf, hall⟩ := h_sound hw
        let o := σ (tr₀ ++ c.tr) i hnf
        obtain ⟨g', hsg, hbr⟩ := hall o
        have hfi' : FairInfOften ewp AccEdge Fair Q (k o)
            (g', tr₀ ++ (c.tr ++ [⟨i, o⟩])) := by
          have hfi₀ : FairInfOften ewp AccEdge Fair Q (k o)
              (g', (tr₀ ++ c.tr) ++ [⟨i, o⟩]) :=
            hbr.elim And.right (fun h' => h'.elim And.right And.right)
          simpa [List.append_assoc] using hfi₀
        exact ⟨⟨w, i, k, hnf, g', hts, h_obs, hsg, hfi'⟩⟩
    let stepOf (c : GhostCfg ewp AccEdge Fair Q σ tr₀ t) :
        GhostStep ewp StepG AccEdge Fair Q σ tr₀ c.u c.g c.tr :=
      Classical.choice (h_step_ne c)
    let nextCfg (c : GhostCfg ewp AccEdge Fair Q σ tr₀ t) :
        GhostCfg ewp AccEdge Fair Q σ tr₀ t :=
      let s := stepOf c
      let o := σ (tr₀ ++ c.tr) s.i s.hnf
      { u := s.k o
        g := s.g'
        tr := c.tr ++ [⟨s.i, o⟩]
        hreach := reachesWithStrategy_trans c.hreach
          (reachesWithStrategy_of_tauStar s.hts
            (.vis s.hv s.hnf (.refl _ (s.k o))))
        hfi := s.hfi' }
    let cfg₀ : GhostCfg ewp AccEdge Fair Q σ tr₀ t :=
      { u := t, g := g₀, tr := [], hreach := .refl tr₀ t, hfi := by simpa using h }
    let cfg : Nat → GhostCfg ewp AccEdge Fair Q σ tr₀ t :=
      Nat.rec cfg₀ (fun _ c => nextCfg c)
    let ev : Stream' (Event E) := fun n =>
      let s := stepOf (cfg n)
      ⟨s.i, σ (tr₀ ++ (cfg n).tr) s.i s.hnf⟩
    let g : Stream' G := fun n => (cfg n).g
    have h_pref : ∀ n, (cfg n).tr = takePrefix ev n := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        show (cfg n).tr ++ [ev n] = takePrefix ev n ++ [ev n]
        rw [ih]
    have h_inf : InfRunWithStrategy σ tr₀ t ev := fun n =>
      ⟨(cfg n).u, h_pref n ▸ (cfg n).hreach⟩
    have h_step_g : ∀ n, StepG (g n) (ev n).req (ev n).ans
        (tr₀ ++ takePrefix ev n) (g (n + 1)) := by
      intro n
      have hs := (stepOf (cfg n)).hsg
      simpa [g, ev, cfg, nextCfg, h_pref n] using hs
    refine ⟨ev, g, h_inf, rfl, h_step_g, fun hfair_inf k => ?_⟩
    have hfi_k := (cfg k).hfi
    rw [FairInfOften.unfold_eq] at hfi_k
    refine fairProgress.induct
      (fun y p => ∀ j, y = (cfg j).u → p = (g j, tr₀ ++ takePrefix ev j) →
        ∃ m, j ≤ m ∧
          AccEdge (ev m).req (ev m).ans (g m, tr₀ ++ takePrefix ev m)
            (g (m + 1), tr₀ ++ takePrefix ev (m + 1)))
      ?_ hfi_k k rfl (by simp [g, h_pref k])
    intro y p hy j hy_eq hp_eq
    subst hy_eq; subst hp_eq
    obtain ⟨n, hle, hfn⟩ := hfair_inf j
    have h_drop : ∀ (d : Nat) (j₀ : Nat),
        fairStall ewp AccEdge Fair Q (FairInfOften ewp AccEdge Fair Q)
          (fun w q => ∀ j₁, w = (cfg j₁).u → q = (g j₁, tr₀ ++ takePrefix ev j₁) →
            ∃ m, j₁ ≤ m ∧
              AccEdge (ev m).req (ev m).ans (g m, tr₀ ++ takePrefix ev m)
                (g (m + 1), tr₀ ++ takePrefix ev (m + 1)))
          (cfg j₀).u (g j₀, tr₀ ++ takePrefix ev j₀) →
        Fair (ev (j₀ + d)).req (ev (j₀ + d)).ans
          (g (j₀ + d), tr₀ ++ takePrefix ev (j₀ + d))
          (g (j₀ + d + 1), tr₀ ++ takePrefix ev (j₀ + d + 1)) →
        ∃ m, j₀ ≤ m ∧
          AccEdge (ev m).req (ev m).ans (g m, tr₀ ++ takePrefix ev m)
            (g (m + 1), tr₀ ++ takePrefix ev (m + 1)) := by
      intro d
      induction d with
      | zero =>
        intro j₀ hz hf0
        rw [fairStall.unfold_eq] at hz
        let sj := stepOf (cfg j₀)
        refine fairStep.induct
          (fun w q => TauStar w sj.v → q = (g j₀, tr₀ ++ takePrefix ev j₀) →
            ∃ m, j₀ ≤ m ∧
              AccEdge (ev m).req (ev m).ans (g m, tr₀ ++ takePrefix ev m)
                (g (m + 1), tr₀ ++ takePrefix ev (m + 1)))
          ?_ hz sj.hts rfl
        intro w q hw hts hq
        subst hq
        cases h_obs : w.observe with
        | ret r => exact False.elim (tauStar_vis_inv_ret hts h_obs sj.hv)
        | tau w' =>
          simp only [h_obs] at hw
          exact hw (tauStar_vis_inv_tau hts h_obs sj.hv) trivial
        | vis i₀ k₀ =>
          simp only [h_obs] at hw
          have hwv : w = sj.v := tauStar_vis_inv_vis hts h_obs sj.hv
          subst hwv
          rw [sj.hv] at h_obs
          injection h_obs with hi₀ hk₀
          subst hi₀
          have hk_eq : k₀ = sj.k := (eq_of_heq hk₀).symm
          subst hk_eq
          obtain ⟨_, hall⟩ := h_sound hw
          have h_tr_eq : tr₀ ++ (cfg j₀).tr = tr₀ ++ takePrefix ev j₀ := by
            rw [h_pref j₀]
          let o_j : E.O sj.i := σ (tr₀ ++ (cfg j₀).tr) sj.i sj.hnf
          obtain ⟨g', hsg', hbr⟩ := hall o_j
          have hg'_eq : g' = g (j₀ + 1) :=
            h_det (g j₀) sj.i o_j (tr₀ ++ takePrefix ev j₀) g' (g (j₀ + 1))
              hsg' (h_step_g j₀)
          subst hg'_eq
          have h_tr_next : (tr₀ ++ takePrefix ev j₀) ++ [⟨sj.i, o_j⟩] =
              tr₀ ++ takePrefix ev (j₀ + 1) := by
            show (tr₀ ++ takePrefix ev j₀) ++ [ev j₀] =
              tr₀ ++ (takePrefix ev j₀ ++ [ev j₀])
            rw [List.append_assoc]
          rw [h_tr_next] at hbr
          rcases hbr with ⟨ha, _⟩ | ⟨_, hpre⟩ | ⟨hnf_f, _⟩
          · exact ⟨j₀, Nat.le_refl j₀, ha⟩
          · have h_u_next : sj.k o_j = (cfg (j₀ + 1)).u := rfl
            obtain ⟨m, hle', hm⟩ := hpre (j₀ + 1) h_u_next rfl
            exact ⟨m, Nat.le_trans (Nat.le_succ j₀) hle', hm⟩
          · exact False.elim (hnf_f hf0)
      | succ d ih =>
        intro j₀ hz hfsd
        rw [fairStall.unfold_eq] at hz
        let sj := stepOf (cfg j₀)
        refine fairStep.induct
          (fun w q => TauStar w sj.v → q = (g j₀, tr₀ ++ takePrefix ev j₀) →
            ∃ m, j₀ ≤ m ∧
              AccEdge (ev m).req (ev m).ans (g m, tr₀ ++ takePrefix ev m)
                (g (m + 1), tr₀ ++ takePrefix ev (m + 1)))
          ?_ hz sj.hts rfl
        intro w q hw hts hq
        subst hq
        cases h_obs : w.observe with
        | ret r => exact False.elim (tauStar_vis_inv_ret hts h_obs sj.hv)
        | tau w' =>
          simp only [h_obs] at hw
          exact hw (tauStar_vis_inv_tau hts h_obs sj.hv) trivial
        | vis i₀ k₀ =>
          simp only [h_obs] at hw
          have hwv : w = sj.v := tauStar_vis_inv_vis hts h_obs sj.hv
          subst hwv
          rw [sj.hv] at h_obs
          injection h_obs with hi₀ hk₀
          subst hi₀
          have hk_eq : k₀ = sj.k := (eq_of_heq hk₀).symm
          subst hk_eq
          obtain ⟨_, hall⟩ := h_sound hw
          let o_j : E.O sj.i := σ (tr₀ ++ (cfg j₀).tr) sj.i sj.hnf
          obtain ⟨g', hsg', hbr⟩ := hall o_j
          have hg'_eq : g' = g (j₀ + 1) :=
            h_det (g j₀) sj.i o_j (tr₀ ++ takePrefix ev j₀) g' (g (j₀ + 1))
              hsg' (h_step_g j₀)
          subst hg'_eq
          have h_tr_next : (tr₀ ++ takePrefix ev j₀) ++ [⟨sj.i, o_j⟩] =
              tr₀ ++ takePrefix ev (j₀ + 1) := by
            show (tr₀ ++ takePrefix ev j₀) ++ [ev j₀] =
              tr₀ ++ (takePrefix ev j₀ ++ [ev j₀])
            rw [List.append_assoc]
          rw [h_tr_next] at hbr
          have h_u_next : sj.k o_j = (cfg (j₀ + 1)).u := rfl
          rcases hbr with ⟨ha, _⟩ | ⟨_, hpre⟩ | ⟨_, hst⟩
          · exact ⟨j₀, Nat.le_refl j₀, ha⟩
          · obtain ⟨m, hle', hm⟩ := hpre (j₀ + 1) h_u_next rfl
            exact ⟨m, Nat.le_trans (Nat.le_succ j₀) hle', hm⟩
          · have hfsd' : Fair (ev (j₀ + 1 + d)).req (ev (j₀ + 1 + d)).ans
                (g (j₀ + 1 + d), tr₀ ++ takePrefix ev (j₀ + 1 + d))
                (g (j₀ + 1 + d + 1), tr₀ ++ takePrefix ev (j₀ + 1 + d + 1)) := by
              have h_idx : j₀ + 1 + d = j₀ + (d + 1) := by omega
              rwa [h_idx]
            obtain ⟨m, hle', hm⟩ := ih (j₀ + 1) (h_u_next ▸ hst) hfsd'
            exact ⟨m, Nat.le_trans (Nat.le_succ j₀) hle', hm⟩
    exact h_drop (n - j) j hy (by rwa [show j + (n - j) = n by omega])

private theorem fairInfOften_lift_punit {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP (List (Event E)) E}
    {AccEdge Fair : (i : E.I) → E.O i → List (Event E) → List (Event E) → Prop}
    {Q : R → List (Event E) → Prop} {t : ITree E R} {tr₀ : List (Event E)}
    (h : FairInfOften ewp AccEdge Fair Q t tr₀) :
    FairInfOften
      { wp := fun i K p => ewp.wp i (fun o tr' => K o (PUnit.unit, tr')) p.2
        mono := fun hm hw => ewp.mono (fun o _ hk => hm o _ hk) hw }
      (fun i o p₁ p₂ => AccEdge i o p₁.2 p₂.2)
      (fun i o p₁ p₂ => Fair i o p₁.2 p₂.2)
      (fun r p => Q r p.2) t (PUnit.unit, tr₀) := by
  let ewp' : StateEffectWP (PUnit.{u + 1} × List (Event E)) E :=
    { wp := fun i K p => ewp.wp i (fun o tr' => K o (PUnit.unit, tr')) p.2
      mono := fun hm hw => ewp.mono (fun o _ hk => hm o _ hk) hw }
  let Acc' := fun i o (p₁ p₂ : PUnit.{u + 1} × List (Event E)) => AccEdge i o p₁.2 p₂.2
  let Fair' := fun i o (p₁ p₂ : PUnit.{u + 1} × List (Event E)) => Fair i o p₁.2 p₂.2
  let Q' := fun r (p : PUnit.{u + 1} × List (Event E)) => Q r p.2
  let X := fun x (p : PUnit.{u + 1} × List (Event E)) =>
    FairInfOften ewp AccEdge Fair Q x p.2
  refine FairInfOften.coinduct X ?_ h
  intro x p hx
  dsimp only [X] at hx
  rw [FairInfOften.unfold_eq] at hx
  refine fairProgress.induct (fun y tr => fairProgress ewp' Acc' Fair' Q' X y (PUnit.unit, tr))
    ?_ hx
  intro y tr hy
  rw [fairProgress.unfold_eq]
  let Z := fun z (p' : PUnit.{u + 1} × List (Event E)) =>
    fairStall ewp AccEdge Fair Q (FairInfOften ewp AccEdge Fair Q)
      (fun v tr' => fairProgress ewp' Acc' Fair' Q' X v (PUnit.unit, tr')) z p'.2
  refine fairStall.coinduct Z ?_ hy
  intro z p' hz
  dsimp only [Z] at hz
  rw [fairStall.unfold_eq] at hz
  refine fairStep.induct
    (fun w tr' => fairStep ewp' Acc' Fair' Q' X (fairProgress ewp' Acc' Fair' Q' X) Z
      w (p'.1, tr')) ?_ hz
  intro w _ hw
  rw [fairStep.unfold_eq]
  cases h_obs : w.observe <;> simp only [h_obs] at hw ⊢
  · exact hw
  · exact hw
  · exact hw

/-- Lift stateless `FairInfOften` over `ewp : EffectWP E` to `traceLiftWP ewp`. -/
theorem FairInfOften.toTraceLift {E : Effect.{u}} {R : Type u}
    {ewp : EffectWP E}
    {AccEdge Fair : (i : E.I) → E.O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop}
    {Q : R → PUnit.{u + 1} → Prop} {t : ITree E R} (tr₀ : List (Event E))
    (h : FairInfOften ewp AccEdge Fair Q t PUnit.unit) :
    FairInfOften (traceLiftWP ewp)
      (fun i o _ _ => AccEdge i o PUnit.unit PUnit.unit)
      (fun i o _ _ => Fair i o PUnit.unit PUnit.unit)
      (fun r _ => Q r PUnit.unit) t tr₀ := by
  let Acc' := fun i o (_ _ : List (Event E)) => AccEdge i o PUnit.unit PUnit.unit
  let Fair' := fun i o (_ _ : List (Event E)) => Fair i o PUnit.unit PUnit.unit
  let Q' := fun r (_ : List (Event E)) => Q r PUnit.unit
  let X := fun x (_ : List (Event E)) => FairInfOften ewp AccEdge Fair Q x PUnit.unit
  refine FairInfOften.coinduct X ?_ h
  intro x tr hx
  dsimp only [X] at hx
  rw [FairInfOften.unfold_eq] at hx
  refine fairProgress.induct
    (fun y _ => ∀ tr₁, fairProgress (traceLiftWP ewp) Acc' Fair' Q' X y tr₁) ?_ hx tr
  intro y ⟨⟩ hy tr₁
  rw [fairProgress.unfold_eq]
  let Z := fun z (_ : List (Event E)) =>
    fairStall ewp AccEdge Fair Q (FairInfOften ewp AccEdge Fair Q)
      (fun v _ => ∀ tr₂, fairProgress (traceLiftWP ewp) Acc' Fair' Q' X v tr₂) z PUnit.unit
  refine fairStall.coinduct Z ?_ hy
  intro z tr₂ hz
  dsimp only [Z] at hz
  rw [fairStall.unfold_eq] at hz
  refine fairStep.induct
    (fun w _ => ∀ tr₃, fairStep (traceLiftWP ewp) Acc' Fair' Q' X
      (fairProgress (traceLiftWP ewp) Acc' Fair' Q' X) Z w tr₃) ?_ hz tr₂
  intro w ⟨⟩ hw tr₃
  rw [fairStep.unfold_eq]
  cases h_obs : w.observe <;> simp only [h_obs] at hw ⊢
  · exact hw
  · exact hw tr₃
  · exact ewp.mono
      (fun _ _ hp => hp.imp id (Or.imp (And.imp id (fun hpre => hpre _)) id)) hw

/--
**General `EnvStrategy` Streett operational adequacy (`TraceSoundWP`)**:
for ANY `[FaultEffect E]`, ANY `R`, ANY `[TraceSoundWP ewp]`, and EVERY
deterministic environment strategy `σ : EnvStrategy E`, `FairInfOften` ensures
that executing `t` against `σ` from `tr₀` either returns `r` satisfying
`Q r (tr₀ ++ tr)` or produces an infinite event stream `ev` satisfying the
Streett implication `□◇ Fair → □◇ AccEdge`.
-/
theorem trace_fairInfOften_strategy_adequacy {E : Effect.{u}} {R : Type u}
    [FaultEffect E] {ewp : StateEffectWP (List (Event E)) E}
    [h_sound : TraceSoundWP ewp]
    {AccEdge Fair : (i : E.I) → E.O i → List (Event E) → List (Event E) → Prop}
    {Q : R → List (Event E) → Prop} {t : ITree E R} {tr₀ : List (Event E)}
    (h : FairInfOften ewp AccEdge Fair Q t tr₀) (σ : EnvStrategy E) :
    (∃ tr r, RetWithStrategy σ tr₀ t tr r ∧ Q r (tr₀ ++ tr)) ∨
      (∃ ev : Stream' (Event E), InfRunWithStrategy σ tr₀ t ev ∧
        ((∀ k, ∃ n, k ≤ n ∧
            Fair (ev n).req (ev n).ans (tr₀ ++ takePrefix ev n)
              (tr₀ ++ takePrefix ev (n + 1))) →
          (∀ k, ∃ n, k ≤ n ∧
            AccEdge (ev n).req (ev n).ans (tr₀ ++ takePrefix ev n)
              (tr₀ ++ takePrefix ev (n + 1))))) := by
  have h_res := ghost_trace_fairInfOften_adequacy
    (G := PUnit.{u + 1})
    { wp := fun i K p => ewp.wp i (fun o tr' => K o (PUnit.unit, tr')) p.2
      mono := fun hm hw => ewp.mono (fun o tr' hk => hm o _ hk) hw }
    (fun _ _ _ _ _ => True)
    (fun hw => let ⟨hnf, hall⟩ := h_sound.sound hw; ⟨hnf, fun o => ⟨PUnit.unit, trivial, hall o⟩⟩)
    (fun _ _ _ _ _ _ _ _ => rfl)
    (fun i o p₁ p₂ => AccEdge i o p₁.2 p₂.2)
    (fun i o p₁ p₂ => Fair i o p₁.2 p₂.2)
    (fun r p => Q r p.2) σ (fairInfOften_lift_punit h)
  rcases h_res with ⟨tr, r, _, hret, hq⟩ | ⟨ev, _, hinf, _, _, hstreett⟩
  · exact Or.inl ⟨tr, r, hret, hq⟩
  · exact Or.inr ⟨ev, hinf, hstreett⟩

/-- **General `EnvStrategy` Büchi operational adequacy (`TraceSoundWP`)**. -/
theorem trace_infOften_strategy_adequacy {E : Effect.{u}} {R : Type u}
    [FaultEffect E] {ewp : StateEffectWP (List (Event E)) E}
    [TraceSoundWP ewp]
    {AccEdge : (i : E.I) → E.O i → List (Event E) → List (Event E) → Prop}
    {Q : R → List (Event E) → Prop} {t : ITree E R} {tr₀ : List (Event E)}
    (h : InfOften ewp AccEdge Q t tr₀) (σ : EnvStrategy E) :
    (∃ tr r, RetWithStrategy σ tr₀ t tr r ∧ Q r (tr₀ ++ tr)) ∨
      (∃ ev : Stream' (Event E), InfRunWithStrategy σ tr₀ t ev ∧
        ∀ k, ∃ n, k ≤ n ∧
          AccEdge (ev n).req (ev n).ans (tr₀ ++ takePrefix ev n)
            (tr₀ ++ takePrefix ev (n + 1))) := by
  rcases trace_fairInfOften_strategy_adequacy (h.toFairInfOften (fun _ _ _ _ => True)) σ with
    hret | ⟨ev, hinf, hacc⟩
  · exact Or.inl hret
  · exact Or.inr ⟨ev, hinf, hacc (fun k => ⟨k, Nat.le_refl k, trivial⟩)⟩

/-- **General `EnvStrategy` co-Büchi operational adequacy (`TraceSoundWP`)**. -/
theorem trace_coBuchi_strategy_adequacy {E : Effect.{u}} {R : Type u}
    [FaultEffect E] {ewp : StateEffectWP (List (Event E)) E}
    [TraceSoundWP ewp]
    {Bad : (i : E.I) → E.O i → List (Event E) → List (Event E) → Prop}
    {Q : R → List (Event E) → Prop} {t : ITree E R} {tr₀ : List (Event E)}
    (h : CoBuchi ewp Bad Q t tr₀) (σ : EnvStrategy E) :
    (∃ tr r, RetWithStrategy σ tr₀ t tr r ∧ Q r (tr₀ ++ tr)) ∨
      (∃ ev : Stream' (Event E), InfRunWithStrategy σ tr₀ t ev ∧
        ∃ K, ∀ n, K ≤ n →
          ¬ Bad (ev n).req (ev n).ans (tr₀ ++ takePrefix ev n)
            (tr₀ ++ takePrefix ev (n + 1))) := by
  rcases trace_fairInfOften_strategy_adequacy h σ with hret | ⟨ev, hinf, hst⟩
  · exact Or.inl hret
  · refine Or.inr ⟨ev, hinf, ?_⟩
    have h_not : ¬ ∀ k, ∃ n, k ≤ n ∧
        Bad (ev n).req (ev n).ans (tr₀ ++ takePrefix ev n)
          (tr₀ ++ takePrefix ev (n + 1)) := fun hinf_bad =>
      let ⟨_, _, hf⟩ := hst hinf_bad 0; hf
    obtain ⟨K, hK⟩ := Classical.not_forall.1 h_not
    exact ⟨K, fun n hle hb => hK ⟨n, hle, hb⟩⟩

/-- **General `EnvStrategy` Streett operational adequacy (`PureSoundWP`)**. -/
theorem pure_fairInfOften_strategy_adequacy {E : Effect.{u}} {R : Type u}
    [FaultEffect E] {ewp : EffectWP E} [PureSoundWP ewp]
    {AccEdge Fair : (i : E.I) → E.O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop}
    {Q : R → PUnit.{u + 1} → Prop} {t : ITree E R}
    (h : FairInfOften ewp AccEdge Fair Q t PUnit.unit)
    (σ : EnvStrategy E) (tr₀ : List (Event E) := []) :
    (∃ tr r, RetWithStrategy σ tr₀ t tr r ∧ Q r PUnit.unit) ∨
      (∃ ev : Stream' (Event E), InfRunWithStrategy σ tr₀ t ev ∧
        ((∀ k, ∃ n, k ≤ n ∧ Fair (ev n).req (ev n).ans PUnit.unit PUnit.unit) →
          (∀ k, ∃ n, k ≤ n ∧ AccEdge (ev n).req (ev n).ans PUnit.unit PUnit.unit))) :=
  trace_fairInfOften_strategy_adequacy (FairInfOften.toTraceLift tr₀ h) σ

/-- **General `EnvStrategy` Büchi operational adequacy (`PureSoundWP`)**. -/
theorem pure_infOften_strategy_adequacy {E : Effect.{u}} {R : Type u}
    [FaultEffect E] {ewp : EffectWP E} [PureSoundWP ewp]
    {AccEdge : (i : E.I) → E.O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop}
    {Q : R → PUnit.{u + 1} → Prop} {t : ITree E R}
    (h : InfOften ewp AccEdge Q t PUnit.unit)
    (σ : EnvStrategy E) (tr₀ : List (Event E) := []) :
    (∃ tr r, RetWithStrategy σ tr₀ t tr r ∧ Q r PUnit.unit) ∨
      (∃ ev : Stream' (Event E), InfRunWithStrategy σ tr₀ t ev ∧
        ∀ k, ∃ n, k ≤ n ∧ AccEdge (ev n).req (ev n).ans PUnit.unit PUnit.unit) :=
  trace_infOften_strategy_adequacy
    ((fairInfOften_true_iff_infOften _ _ _ _ _).1
      (FairInfOften.toTraceLift tr₀ (h.toFairInfOften (fun _ _ _ _ => True)))) σ

/-- **General `EnvStrategy` co-Büchi operational adequacy (`PureSoundWP`)**. -/
theorem pure_coBuchi_strategy_adequacy {E : Effect.{u}} {R : Type u}
    [FaultEffect E] {ewp : EffectWP E} [PureSoundWP ewp]
    {Bad : (i : E.I) → E.O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop}
    {Q : R → PUnit.{u + 1} → Prop} {t : ITree E R}
    (h : CoBuchi ewp Bad Q t PUnit.unit)
    (σ : EnvStrategy E) (tr₀ : List (Event E) := []) :
    (∃ tr r, RetWithStrategy σ tr₀ t tr r ∧ Q r PUnit.unit) ∨
      (∃ ev : Stream' (Event E), InfRunWithStrategy σ tr₀ t ev ∧
        ∃ K, ∀ n, K ≤ n → ¬ Bad (ev n).req (ev n).ans PUnit.unit PUnit.unit) :=
  trace_coBuchi_strategy_adequacy (FairInfOften.toTraceLift tr₀ h) σ

/--
**Deterministic-monitor `FairBuchiSat` `EnvStrategy` adequacy (`TraceSoundWP`)**:
produces BOTH the operational infinite run `ev` AND the unique invariant-preserving
monitor run `q : Stream' QState` satisfying the Streett condition.
-/
theorem trace_fairBuchiSat_det_strategy_adequacy {QState : Type u}
    {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (spec : BuchiSpec (List (Event E)) QState E R) [h_sound : TraceSoundWP spec.ewp]
    (fair : QState → (i : E.I) → E.O i → List (Event E) → List (Event E) → QState → Prop)
    (h_det : ∀ q i o tr tr' q₁ q₂,
      spec.step q i o tr tr' q₁ → spec.step q i o tr tr' q₂ → q₁ = q₂)
    {t : ITree E R} {q₀ : QState} {tr₀ : List (Event E)}
    (h : FairBuchiSat spec fair t q₀ tr₀) (σ : EnvStrategy E) :
    (∃ tr r q', RetWithStrategy σ tr₀ t tr r ∧
        spec.inv q' (tr₀ ++ tr) ∧ spec.terminal q' r (tr₀ ++ tr)) ∨
      (∃ (ev : Stream' (Event E)) (q : Stream' QState),
        InfRunWithStrategy σ tr₀ t ev ∧ q 0 = q₀ ∧
        (∀ n, spec.inv (q n) (tr₀ ++ takePrefix ev n) ∧
          spec.step (q n) (ev n).req (ev n).ans
            (tr₀ ++ takePrefix ev n) (tr₀ ++ takePrefix ev (n + 1)) (q (n + 1))) ∧
        ((∀ k, ∃ n, k ≤ n ∧
            fair (q n) (ev n).req (ev n).ans
              (tr₀ ++ takePrefix ev n) (tr₀ ++ takePrefix ev (n + 1)) (q (n + 1))) →
          (∀ k, ∃ n, k ≤ n ∧
            spec.accept (q n) (ev n).req (ev n).ans
              (tr₀ ++ takePrefix ev n) (tr₀ ++ takePrefix ev (n + 1)) (q (n + 1))))) := by
  have ⟨hi₀, hfi⟩ := (fairBuchiSat_iff_fairInfOften spec fair t q₀ tr₀).1 h
  have hfi_inv := FairInfOften.post_inv_guardInv (ewp := spec.prodWP) (Inv := spec.invPred)
    (s := (q₀, tr₀)) hi₀ hfi
  let StepG : QState → (i : E.I) → E.O i → List (Event E) → QState → Prop :=
    fun q i o tr q' =>
      spec.step q i o tr (tr ++ [⟨i, o⟩]) q' ∧ spec.inv q' (tr ++ [⟨i, o⟩])
  have h_res := ghost_trace_fairInfOften_adequacy spec.monitorWP StepG
    (fun {i K q tr} hw =>
      let ⟨hnf, hall⟩ := h_sound.sound hw
      ⟨hnf, fun o => let ⟨q', hs, hi, hk⟩ := hall o; ⟨q', ⟨hs, hi⟩, hk⟩⟩)
    (fun q i o tr q₁ q₂ h₁ h₂ => h_det q i o tr _ q₁ q₂ h₁.1 h₂.1)
    spec.acceptEdge (spec.fairEdge fair)
    (fun r qs => spec.inv qs.1 qs.2 ∧ spec.terminal qs.1 r qs.2) σ hfi_inv
  rcases h_res with ⟨tr, r, q', hret, hi', hterm⟩ | ⟨ev, q, hinf, hq0, hsteps, hst⟩
  · exact Or.inl ⟨tr, r, q', hret, hi', hterm⟩
  · refine Or.inr ⟨ev, q, hinf, hq0, fun n => ?_, hst⟩
    have h_step_n := hsteps n
    have h_tr_n : (tr₀ ++ takePrefix ev n) ++ [ev n] = tr₀ ++ takePrefix ev (n + 1) := by
      show (tr₀ ++ takePrefix ev n) ++ [ev n] = tr₀ ++ (takePrefix ev n ++ [ev n])
      rw [List.append_assoc]
    have h_inv_n : spec.inv (q n) (tr₀ ++ takePrefix ev n) := by
      cases n with
      | zero => simpa [hq0] using hi₀
      | succ m =>
        have hsm := (hsteps m).2
        have h_tr_m : (tr₀ ++ takePrefix ev m) ++ [ev m] = tr₀ ++ takePrefix ev (m + 1) := by
          show (tr₀ ++ takePrefix ev m) ++ [ev m] = tr₀ ++ (takePrefix ev m ++ [ev m])
          rw [List.append_assoc]
        rwa [h_tr_m] at hsm
    exact ⟨h_inv_n, h_tr_n ▸ h_step_n.1⟩

/-- Lift stateless `FairBuchiSat` to `spec.toTrace`. -/
theorem FairBuchiSat.toTrace {QState : Type u} {E : Effect.{u}} {R : Type u}
    {spec : BuchiSpec PUnit.{u + 1} QState E R}
    {fair : QState → (i : E.I) → E.O i → PUnit.{u + 1} → PUnit.{u + 1} → QState → Prop}
    {t : ITree E R} {q₀ : QState} (tr₀ : List (Event E))
    (h : FairBuchiSat spec fair t q₀ PUnit.unit) :
    FairBuchiSat spec.toTrace (fun q i o _ _ q' => fair q i o PUnit.unit PUnit.unit q')
      t q₀ tr₀ := by
  have ⟨hi, hfi⟩ := (fairBuchiSat_iff_fairInfOften spec fair t q₀ PUnit.unit).1 h
  let fairT : QState → (i : E.I) → E.O i → List (Event E) → List (Event E) → QState → Prop :=
    fun q i o _ _ q' => fair q i o PUnit.unit PUnit.unit q'
  refine (fairBuchiSat_iff_fairInfOften spec.toTrace fairT t q₀ tr₀).2 ⟨hi, ?_⟩
  let X := fun x (qs : QState × List (Event E)) =>
    FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fair) spec.terminalPost
      x (qs.1, PUnit.unit)
  refine FairInfOften.coinduct X ?_ hfi
  intro x qs hx
  dsimp only [X] at hx
  rw [FairInfOften.unfold_eq] at hx
  refine fairProgress.induct
    (fun y qp => ∀ tr, fairProgress spec.toTrace.monitorWP spec.toTrace.acceptEdge
      (spec.toTrace.fairEdge fairT) spec.toTrace.terminalPost X y (qp.1, tr))
    ?_ hx qs.2
  intro y qp hy tr
  rw [fairProgress.unfold_eq]
  let Z := fun z (qs' : QState × List (Event E)) =>
    fairStall spec.monitorWP spec.acceptEdge (spec.fairEdge fair) spec.terminalPost
      (FairInfOften spec.monitorWP spec.acceptEdge (spec.fairEdge fair) spec.terminalPost)
      (fun v qp' => ∀ tr', fairProgress spec.toTrace.monitorWP spec.toTrace.acceptEdge
        (spec.toTrace.fairEdge fairT) spec.toTrace.terminalPost X v (qp'.1, tr'))
      z (qs'.1, PUnit.unit)
  refine fairStall.coinduct Z ?_ hy
  intro z qs' hz
  dsimp only [Z] at hz
  rw [fairStall.unfold_eq] at hz
  refine fairStep.induct
    (fun w qp' => ∀ tr', fairStep spec.toTrace.monitorWP spec.toTrace.acceptEdge
      (spec.toTrace.fairEdge fairT) spec.toTrace.terminalPost X
      (fairProgress spec.toTrace.monitorWP spec.toTrace.acceptEdge
        (spec.toTrace.fairEdge fairT) spec.toTrace.terminalPost X)
      Z w (qp'.1, tr')) ?_ hz qs'.2
  intro w qp' hw tr'
  rw [fairStep.unfold_eq]
  cases h_obs : w.observe <;> simp only [h_obs] at hw ⊢
  · exact hw
  · exact hw tr'
  · exact spec.ewp.mono (fun _ _ ⟨q', hs, hi', hp⟩ =>
      ⟨q', hs, hi', hp.imp id (Or.imp (And.imp id (fun hpre => hpre _)) id)⟩) hw

/--
**Deterministic-monitor `FairBuchiSat` `EnvStrategy` adequacy (`PureSoundWP`)**.
-/
theorem pure_fairBuchiSat_det_strategy_adequacy {QState : Type u}
    {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (spec : BuchiSpec PUnit.{u + 1} QState E R) [PureSoundWP spec.ewp]
    (fair : QState → (i : E.I) → E.O i → PUnit.{u + 1} → PUnit.{u + 1} → QState → Prop)
    (h_det : ∀ q i o q₁ q₂,
      spec.step q i o PUnit.unit PUnit.unit q₁ →
      spec.step q i o PUnit.unit PUnit.unit q₂ → q₁ = q₂)
    {t : ITree E R} {q₀ : QState}
    (h : FairBuchiSat spec fair t q₀ PUnit.unit)
    (σ : EnvStrategy E) (tr₀ : List (Event E) := []) :
    (∃ tr r q', RetWithStrategy σ tr₀ t tr r ∧
        spec.inv q' PUnit.unit ∧ spec.terminal q' r PUnit.unit) ∨
      (∃ (ev : Stream' (Event E)) (q : Stream' QState),
        InfRunWithStrategy σ tr₀ t ev ∧ q 0 = q₀ ∧
        (∀ n, spec.inv (q n) PUnit.unit ∧
          spec.step (q n) (ev n).req (ev n).ans PUnit.unit PUnit.unit (q (n + 1))) ∧
        ((∀ k, ∃ n, k ≤ n ∧
            fair (q n) (ev n).req (ev n).ans PUnit.unit PUnit.unit (q (n + 1))) →
          (∀ k, ∃ n, k ≤ n ∧
            spec.accept (q n) (ev n).req (ev n).ans PUnit.unit PUnit.unit (q (n + 1))))) :=
  trace_fairBuchiSat_det_strategy_adequacy spec.toTrace
    (fun q i o _ _ q' => fair q i o PUnit.unit PUnit.unit q')
    (fun q i o _ _ q₁ q₂ h₁ h₂ => h_det q i o q₁ q₂ h₁ h₂)
    (FairBuchiSat.toTrace tr₀ h) σ

private inductive MonitorSeg {E : Effect.{u}} {R QState : Type u} [FaultEffect E]
    (spec : BuchiSpec (List (Event E)) QState E R) (σ : EnvStrategy E) :
    List (Event E) → ITree E R → QState →
      List (Event E × QState) → ITree E R → QState → Prop where
  | single {hist u v i k q q'} (hts : TauStar u v)
      (hv : v.observe = .vis i k) (hnf : ¬ FaultEffect.isFault i)
      (hinv : spec.inv q' (hist ++ [⟨i, σ hist i hnf⟩]))
      (hstep : spec.step q i (σ hist i hnf) hist (hist ++ [⟨i, σ hist i hnf⟩]) q')
      (hacc : spec.accept q i (σ hist i hnf) hist (hist ++ [⟨i, σ hist i hnf⟩]) q') :
      MonitorSeg spec σ hist u q [(⟨i, σ hist i hnf⟩, q')] (k (σ hist i hnf)) q'
  | cons {hist u v i k q q₁ seg u' q'} (hts : TauStar u v)
      (hv : v.observe = .vis i k) (hnf : ¬ FaultEffect.isFault i)
      (hinv : spec.inv q₁ (hist ++ [⟨i, σ hist i hnf⟩]))
      (hstep : spec.step q i (σ hist i hnf) hist (hist ++ [⟨i, σ hist i hnf⟩]) q₁)
      (hrest : MonitorSeg spec σ (hist ++ [⟨i, σ hist i hnf⟩])
        (k (σ hist i hnf)) q₁ seg u' q') :
      MonitorSeg spec σ hist u q ((⟨i, σ hist i hnf⟩, q₁) :: seg) u' q'

private theorem MonitorSeg.nonempty {E : Effect.{u}} {R QState : Type u} [FaultEffect E]
    {spec : BuchiSpec (List (Event E)) QState E R} {σ : EnvStrategy E}
    {hist u q seg u' q'} (h : MonitorSeg spec σ hist u q seg u' q') :
    0 < seg.length := by
  cases h <;> simp

private theorem MonitorSeg.reaches_end {E : Effect.{u}} {R QState : Type u} [FaultEffect E]
    {spec : BuchiSpec (List (Event E)) QState E R} {σ : EnvStrategy E}
    {hist u q seg u' q'} (h : MonitorSeg spec σ hist u q seg u' q') :
    ReachesWithStrategy σ hist u (seg.map Prod.fst) u' := by
  induction h with
  | single hts hv hnf _ _ _ =>
    exact reachesWithStrategy_of_tauStar hts (.vis hv hnf (.refl _ _))
  | cons hts hv hnf _ _ _ ih =>
    exact reachesWithStrategy_of_tauStar hts (.vis hv hnf ih)

private theorem MonitorSeg.reaches_pref {E : Effect.{u}} {R QState : Type u} [FaultEffect E]
    {spec : BuchiSpec (List (Event E)) QState E R} {σ : EnvStrategy E}
    {hist u q seg u' q'} (h : MonitorSeg spec σ hist u q seg u' q') :
    ∀ j, j ≤ seg.length →
      ∃ u_j, ReachesWithStrategy σ hist u ((seg.take j).map Prod.fst) u_j := by
  induction h with
  | single hts hv hnf _ _ _ =>
    intro j hj
    cases j with
    | zero => exact ⟨_, .refl _ _⟩
    | succ j' =>
      have hj0 : j' = 0 := by simp at hj; omega
      subst hj0
      exact ⟨_, reachesWithStrategy_of_tauStar hts (.vis hv hnf (.refl _ _))⟩
  | cons hts hv hnf _ _ _ ih =>
    intro j hj
    cases j with
    | zero => exact ⟨_, .refl _ _⟩
    | succ j' =>
      obtain ⟨u_j, hu⟩ := ih j' (Nat.le_of_succ_le_succ hj)
      exact ⟨u_j, reachesWithStrategy_of_tauStar hts (.vis hv hnf hu)⟩

private theorem MonitorSeg.last_q {E : Effect.{u}} {R QState : Type u} [FaultEffect E]
    {spec : BuchiSpec (List (Event E)) QState E R} {σ : EnvStrategy E}
    {hist u q seg u' q'} (h : MonitorSeg spec σ hist u q seg u' q') :
    (seg[seg.length - 1]'(Nat.sub_lt h.nonempty Nat.zero_lt_one)).2 = q' := by
  induction h with
  | single => rfl
  | cons _ _ _ _ _ hrest ih =>
    cases hrest <;> exact ih

private theorem MonitorSeg.step_at {E : Effect.{u}} {R QState : Type u} [FaultEffect E]
    {spec : BuchiSpec (List (Event E)) QState E R} {σ : EnvStrategy E}
    {hist u q seg u' q'} (h : MonitorSeg spec σ hist u q seg u' q') :
    ∀ (j : Nat) (hj : j < seg.length),
      let prevQ := if _ : j = 0 then q else (seg[j - 1]'(by omega)).2
      let pref := hist ++ (seg.take j).map Prod.fst
      spec.inv (seg[j].2) (pref ++ [seg[j].1]) ∧
        spec.step prevQ seg[j].1.req seg[j].1.ans pref (pref ++ [seg[j].1]) seg[j].2 := by
  induction h with
  | single _ _ _ hinv hstep _ =>
    intro j hj
    have hj0 : j = 0 := by simp at hj; omega
    subst hj0
    simpa using ⟨hinv, hstep⟩
  | @cons hist u v i k q q₁ seg u' q' _ _ hnf hinv hstep _ ih =>
    intro j hj
    cases j with
    | zero => simpa using ⟨hinv, hstep⟩
    | succ j' =>
      have hj' : j' < seg.length := Nat.lt_of_succ_lt_succ hj
      have hres := ih j' hj'
      have h_pref : hist ++ (((⟨i, σ hist i hnf⟩, q₁) :: seg).take (j' + 1)).map Prod.fst =
          (hist ++ [⟨i, σ hist i hnf⟩]) ++ (seg.take j').map Prod.fst := by
        simp [List.append_assoc]
      cases j' with
      | zero => simpa [h_pref] using hres
      | succ j'' => simpa [h_pref] using hres

private theorem MonitorSeg.last_accept {E : Effect.{u}} {R QState : Type u} [FaultEffect E]
    {spec : BuchiSpec (List (Event E)) QState E R} {σ : EnvStrategy E}
    {hist u q seg u' q'} (h : MonitorSeg spec σ hist u q seg u' q') :
    let j := seg.length - 1
    have hj : j < seg.length := Nat.sub_lt h.nonempty Nat.zero_lt_one
    let prevQ := if _ : j = 0 then q else (seg[j - 1]'(by omega)).2
    let pref := hist ++ (seg.take j).map Prod.fst
    spec.accept prevQ seg[j].1.req seg[j].1.ans pref (pref ++ [seg[j].1]) seg[j].2 := by
  induction h with
  | single _ _ _ _ _ hacc => simpa using hacc
  | @cons hist u v i k q q₁ seg u' q' _ _ hnf _ _ hrest ih =>
    cases hrest with
    | single =>
      dsimp only at ih ⊢
      simpa [List.append_assoc] using ih
    | cons _ _ _ _ _ hrest₂ =>
      cases hrest₂ with
      | single =>
        dsimp only at ih ⊢
        simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel,
          Nat.succ_ne_zero, ↓reduceDIte, List.take_succ_cons, List.take_zero,
          List.map_cons, List.map_nil, List.getElem_cons_succ,
          List.getElem_cons_zero] at ih ⊢
        simpa [List.append_assoc] using ih
      | cons =>
        dsimp only at ih ⊢
        simp only [List.length_cons, Nat.add_sub_cancel, Nat.succ_ne_zero,
          ↓reduceDIte, List.take_succ_cons, List.map_cons,
          List.getElem_cons_succ] at ih ⊢
        simpa [List.append_assoc] using ih

private structure MonitorAccState {E : Effect.{u}} {R QState : Type u} [FaultEffect E]
    (spec : BuchiSpec (List (Event E)) QState E R) (σ : EnvStrategy E)
    (tr₀ : List (Event E)) (t : ITree E R) (q₀ : QState) (m : Nat) : Type u where
  acc : List (Event E × QState)
  u : ITree E R
  q : QState
  hlen : m ≤ acc.length
  hreach_end : ReachesWithStrategy σ tr₀ t (acc.map Prod.fst) u
  hreach_pref : ∀ j, j ≤ acc.length →
    ∃ u', ReachesWithStrategy σ tr₀ t ((acc.take j).map Prod.fst) u'
  hlastQ : (if h : acc.length = 0 then q₀ else (acc[acc.length - 1]'(by omega)).2) = q
  hinv_end : spec.inv q (tr₀ ++ acc.map Prod.fst)
  hio : InfOften spec.monitorWP spec.acceptEdge spec.terminalPost u (q, tr₀ ++ acc.map Prod.fst)
  hstep_all : ∀ (j : Nat) (hj : j < acc.length),
    let prevQ := if _ : j = 0 then q₀ else (acc[j - 1]'(by omega)).2
    let pref := tr₀ ++ (acc.take j).map Prod.fst
    spec.inv (acc[j].2) (pref ++ [acc[j].1]) ∧
      spec.step prevQ acc[j].1.req acc[j].1.ans pref (pref ++ [acc[j].1]) acc[j].2
  hacc_all : ∀ k, k < m → ∃ (j : Nat) (hj : j < acc.length), k ≤ j ∧
    let prevQ := if _ : j = 0 then q₀ else (acc[j - 1]'(by omega)).2
    let pref := tr₀ ++ (acc.take j).map Prod.fst
    spec.accept prevQ acc[j].1.req acc[j].1.ans pref (pref ++ [acc[j].1]) acc[j].2

private structure SegChoice {E : Effect.{u}} {R QState : Type u} [FaultEffect E]
    (spec : BuchiSpec (List (Event E)) QState E R) (σ : EnvStrategy E)
    (hist : List (Event E)) (u : ITree E R) (q : QState) : Type u where
  seg : List (Event E × QState)
  u' : ITree E R
  q' : QState
  hseg : MonitorSeg spec σ hist u q seg u' q'
  hinv' : spec.inv q' (hist ++ seg.map Prod.fst)
  hio' : InfOften spec.monitorWP spec.acceptEdge spec.terminalPost u'
    (q', hist ++ seg.map Prod.fst)

/--
**Arbitrary nondeterministic `BuchiSat` `EnvStrategy` operational soundness
(`TraceSoundWP`)**: even without monitor determinism, every satisfied `BuchiSat`
produces against EVERY environment strategy `σ` either a valid terminal return
or an infinite execution stream `ev` accompanied by an infinite accepting
monitor run `q : Stream' QState` (complementing `buchiSat_nondet_incomplete`).
-/
theorem trace_buchiSat_strategy_adequacy {QState : Type u}
    {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (spec : BuchiSpec (List (Event E)) QState E R) [h_sound : TraceSoundWP spec.ewp]
    {t : ITree E R} {q₀ : QState} {tr₀ : List (Event E)}
    (h : BuchiSat spec t q₀ tr₀) (σ : EnvStrategy E) :
    (∃ tr r q', RetWithStrategy σ tr₀ t tr r ∧
        spec.inv q' (tr₀ ++ tr) ∧ spec.terminal q' r (tr₀ ++ tr)) ∨
      (∃ (ev : Stream' (Event E)) (q : Stream' QState),
        InfRunWithStrategy σ tr₀ t ev ∧ q 0 = q₀ ∧
        (∀ n, spec.inv (q n) (tr₀ ++ takePrefix ev n) ∧
          spec.step (q n) (ev n).req (ev n).ans
            (tr₀ ++ takePrefix ev n) (tr₀ ++ takePrefix ev (n + 1)) (q (n + 1))) ∧
        (∀ k, ∃ n, k ≤ n ∧
          spec.accept (q n) (ev n).req (ev n).ans
            (tr₀ ++ takePrefix ev n) (tr₀ ++ takePrefix ev (n + 1)) (q (n + 1)))) := by
  by_cases h_ret : ∃ tr r q', RetWithStrategy σ tr₀ t tr r ∧
      spec.inv q' (tr₀ ++ tr) ∧ spec.terminal q' r (tr₀ ++ tr)
  · exact Or.inl h_ret
  · right
    have ⟨hi₀, hio₀⟩ := (buchiSat_iff_infOften spec t q₀ tr₀).1 h
    have h_seg_ne : ∀ (tr : List (Event E)) (u : ITree E R) (q : QState),
        ReachesWithStrategy σ tr₀ t tr u → spec.inv q (tr₀ ++ tr) →
        InfOften spec.monitorWP spec.acceptEdge spec.terminalPost u (q, tr₀ ++ tr) →
        Nonempty (SegChoice spec σ (tr₀ ++ tr) u q) := by
      intro tr u q hreach hinv hio
      refine buchiProgress.induct
        (fun w qs => ∀ tr_w, qs.2 = tr₀ ++ tr_w →
          ReachesWithStrategy σ tr₀ t tr_w w → spec.inv qs.1 (tr₀ ++ tr_w) →
          Nonempty (SegChoice spec σ (tr₀ ++ tr_w) w qs.1))
        ?_ hio.toBuchiProgress tr rfl hreach hinv
      intro w qs hw tr_w hqs_tr hreach_w hinv_w
      rcases qs with ⟨q_w, tr_qs⟩
      dsimp only at hqs_tr hinv_w ⊢
      subst hqs_tr
      cases h_obs : w.observe with
      | ret r =>
        simp only [h_obs] at hw
        exact False.elim (h_ret ⟨tr_w, r, q_w, ⟨w, hreach_w, h_obs⟩, hinv_w, hw⟩)
      | tau w' =>
        simp only [h_obs] at hw
        have hreach_w' : ReachesWithStrategy σ tr₀ t tr_w w' := by
          have hr := reachesWithStrategy_trans hreach_w (.tau h_obs (.refl (tr₀ ++ tr_w) w'))
          simpa using hr
        obtain ⟨⟨seg, u', q', hseg, hinv', hio'⟩⟩ := hw tr_w rfl hreach_w' hinv_w
        have hseg' : MonitorSeg spec σ (tr₀ ++ tr_w) w q_w seg u' q' := by
          cases hseg with
          | single hts hv hnf hi hs ha =>
            exact .single (.step h_obs hts) hv hnf hi hs ha
          | cons hts hv hnf hi hs hr =>
            exact .cons (.step h_obs hts) hv hnf hi hs hr
        exact ⟨⟨seg, u', q', hseg', hinv', hio'⟩⟩
      | vis i k =>
        simp only [h_obs] at hw
        rw [BuchiSpec.monitorWP_wp] at hw
        obtain ⟨hnf, hall⟩ := h_sound.sound hw
        let o := σ (tr₀ ++ tr_w) i hnf
        obtain ⟨q₁, hstep₁, hinv₁, hdisj⟩ := hall o
        have h_tr₁ : (tr₀ ++ tr_w) ++ [⟨i, o⟩] = tr₀ ++ (tr_w ++ [⟨i, o⟩]) := by
          rw [List.append_assoc]
        rcases hdisj with ⟨hacc₁, hio₁⟩ | hpre₁
        · refine ⟨⟨[(⟨i, o⟩, q₁)], k o, q₁,
            .single (.refl w) h_obs hnf hinv₁ hstep₁ hacc₁,
            by simpa using hinv₁, by simpa using hio₁⟩⟩
        · have hreach₁ : ReachesWithStrategy σ tr₀ t (tr_w ++ [⟨i, o⟩]) (k o) :=
            reachesWithStrategy_trans hreach_w (.vis h_obs hnf (.refl _ (k o)))
          obtain ⟨⟨seg, u', q', hseg, hinv', hio'⟩⟩ :=
            hpre₁ (tr_w ++ [⟨i, o⟩]) h_tr₁ hreach₁ (h_tr₁ ▸ hinv₁)
          refine ⟨⟨(⟨i, o⟩, q₁) :: seg, u', q',
            .cons (.refl w) h_obs hnf hinv₁ hstep₁ (h_tr₁ ▸ hseg),
            by simpa [List.append_assoc] using hinv',
            by simpa [List.append_assoc] using hio'⟩⟩
    let st₀ : MonitorAccState spec σ tr₀ t q₀ 0 :=
      { acc := [], u := t, q := q₀, hlen := Nat.le_refl 0,
        hreach_end := .refl tr₀ t,
        hreach_pref := fun j hj => ⟨t, by
          have hj0 : j = 0 := Nat.le_zero.1 hj; subst hj0; exact .refl tr₀ t⟩,
        hlastQ := rfl,
        hinv_end := by simpa using hi₀,
        hio := by simpa using hio₀,
        hstep_all := fun _ hj => absurd hj (Nat.not_lt_zero _),
        hacc_all := fun _ hk => absurd hk (Nat.not_lt_zero _) }
    let stepSt : ∀ m, MonitorAccState spec σ tr₀ t q₀ m →
        MonitorAccState spec σ tr₀ t q₀ (m + 1) := fun m st =>
      let sc := Classical.choice (h_seg_ne (st.acc.map Prod.fst) st.u st.q
        st.hreach_end st.hinv_end st.hio)
      have hne : 0 < sc.seg.length := sc.hseg.nonempty
      { acc := st.acc ++ sc.seg
        u := sc.u'
        q := sc.q'
        hlen := by have := st.hlen; rw [List.length_append]; omega
        hreach_end := by
          rw [List.map_append]
          exact reachesWithStrategy_trans st.hreach_end sc.hseg.reaches_end
        hreach_pref := fun j hj => by
          rw [List.length_append] at hj
          by_cases hle : j ≤ st.acc.length
          · rw [List.take_append_of_le_length hle]
            exact st.hreach_pref j hle
          · have hj' : j - st.acc.length ≤ sc.seg.length := by omega
            obtain ⟨u_j, hu_j⟩ := sc.hseg.reaches_pref (j - st.acc.length) hj'
            refine ⟨u_j, ?_⟩
            rw [List.take_append, List.take_of_length_le (by omega), List.map_append]
            exact reachesWithStrategy_trans st.hreach_end hu_j
        hlastQ := by
          have hne_app : (st.acc ++ sc.seg).length ≠ 0 := by
            rw [List.length_append]; omega
          simp only [hne_app, ↓reduceDIte]
          have h_idx : st.acc.length ≤ (st.acc ++ sc.seg).length - 1 := by
            rw [List.length_append]; omega
          rw [List.getElem_append_right h_idx]
          have h_sub : (st.acc ++ sc.seg).length - 1 - st.acc.length = sc.seg.length - 1 := by
            rw [List.length_append]; omega
          simp only [h_sub]
          exact sc.hseg.last_q
        hinv_end := by simpa [List.map_append, List.append_assoc] using sc.hinv'
        hio := by simpa [List.map_append, List.append_assoc] using sc.hio'
        hstep_all := fun j hj => by
          by_cases hlt : j < st.acc.length
          · have hst_j := st.hstep_all j hlt
            have h_take : (st.acc ++ sc.seg).take j = st.acc.take j :=
              List.take_append_of_le_length (Nat.le_of_lt hlt)
            have h_el : (st.acc ++ sc.seg)[j] = st.acc[j] :=
              List.getElem_append_left hlt
            by_cases h0 : j = 0
            · dsimp only at hst_j ⊢
              rw [h_take, h_el]
              simp only [h0, ↓reduceDIte] at hst_j ⊢
              exact hst_j
            · have h_prev : (st.acc ++ sc.seg)[j - 1]'(by omega) =
                  st.acc[j - 1]'(by omega) := List.getElem_append_left (by omega)
              dsimp only at hst_j ⊢
              simp only [h0, ↓reduceDIte] at hst_j ⊢
              rw [h_take, h_el, h_prev]; exact hst_j
          · have hge : st.acc.length ≤ j := Nat.le_of_not_lt hlt
            have hj' : j - st.acc.length < sc.seg.length := by
              rw [List.length_append] at hj; omega
            have hseg_j := sc.hseg.step_at (j - st.acc.length) hj'
            have h_take : ((st.acc ++ sc.seg).take j).map Prod.fst =
                st.acc.map Prod.fst ++ (sc.seg.take (j - st.acc.length)).map Prod.fst := by
              rw [List.take_append, List.take_of_length_le hge, List.map_append]
            have h_el : (st.acc ++ sc.seg)[j] = sc.seg[j - st.acc.length] :=
              List.getElem_append_right hge
            by_cases heq : j = st.acc.length
            · subst heq
              have h_prevQ : (if _ : st.acc.length = 0 then q₀
                  else ((st.acc ++ sc.seg)[st.acc.length - 1]'(by omega)).2) = st.q := by
                by_cases h0 : st.acc.length = 0
                · simp only [h0, ↓reduceDIte]
                  simpa [h0] using st.hlastQ
                · simp only [h0, ↓reduceDIte]
                  rw [List.getElem_append_left (by omega)]
                  simpa [h0] using st.hlastQ
              dsimp only at hseg_j ⊢
              simp only [Nat.sub_self, ↓reduceDIte] at hseg_j
              rw [h_take, h_el, h_prevQ]
              simp only [Nat.sub_self, List.append_assoc] at hseg_j ⊢
              exact hseg_j
            · have h0 : j ≠ 0 := by omega
              have h_sub_ne : j - st.acc.length ≠ 0 := by omega
              have h_prev : (st.acc ++ sc.seg)[j - 1]'(by omega) =
                  sc.seg[j - st.acc.length - 1]'(by omega) := by
                rw [List.getElem_append_right (by omega)]
                congr 1; omega
              dsimp only at hseg_j ⊢
              simp only [h0, h_sub_ne, ↓reduceDIte] at hseg_j ⊢
              rw [h_take, h_el, h_prev]
              simp only [List.append_assoc] at hseg_j ⊢
              exact hseg_j
        hacc_all := fun k hk => by
          by_cases hkm : k < m
          · obtain ⟨j, hj, hkj, hacc_j⟩ := st.hacc_all k hkm
            refine ⟨j, Nat.lt_of_lt_of_le hj (by rw [List.length_append]; omega), hkj, ?_⟩
            have h_take : (st.acc ++ sc.seg).take j = st.acc.take j :=
              List.take_append_of_le_length (Nat.le_of_lt hj)
            have h_el : (st.acc ++ sc.seg)[j]'(by rw [List.length_append]; omega) =
                st.acc[j] := List.getElem_append_left hj
            by_cases h0 : j = 0
            · dsimp only at hacc_j ⊢
              rw [h_take, h_el]
              simp only [h0, ↓reduceDIte] at hacc_j ⊢
              exact hacc_j
            · have h_prev : (st.acc ++ sc.seg)[j - 1]'(by rw [List.length_append]; omega) =
                  st.acc[j - 1]'(by omega) := List.getElem_append_left (by omega)
              dsimp only at hacc_j ⊢
              simp only [h0, ↓reduceDIte] at hacc_j ⊢
              rw [h_take, h_el, h_prev]; exact hacc_j
          · have h_eq_m : k = m := by omega
            subst h_eq_m
            let j := st.acc.length + (sc.seg.length - 1)
            have hj : j < (st.acc ++ sc.seg).length := by rw [List.length_append]; omega
            refine ⟨j, hj, by have := st.hlen; omega, ?_⟩
            have hlast := sc.hseg.last_accept
            have hge : st.acc.length ≤ j := Nat.le_add_right _ _
            have h_sub : j - st.acc.length = sc.seg.length - 1 := by omega
            have h_take : ((st.acc ++ sc.seg).take j).map Prod.fst =
                st.acc.map Prod.fst ++ (sc.seg.take (sc.seg.length - 1)).map Prod.fst := by
              rw [List.take_append, List.take_of_length_le hge, h_sub, List.map_append]
            have h_el : (st.acc ++ sc.seg)[j] = sc.seg[sc.seg.length - 1]'(by omega) := by
              rw [List.getElem_append_right hge]; simp [h_sub]
            by_cases heq : sc.seg.length - 1 = 0
            · have h_prevQ : (if _ : j = 0 then q₀
                  else ((st.acc ++ sc.seg)[j - 1]'(by omega)).2) = st.q := by
                by_cases h0 : j = 0
                · have hlen0 : st.acc.length = 0 := by omega
                  simp only [h0, ↓reduceDIte]
                  simpa [hlen0] using st.hlastQ
                · have hlen_ne : st.acc.length ≠ 0 := by omega
                  have h_j1 : j - 1 = st.acc.length - 1 := by omega
                  simp only [h0, ↓reduceDIte]
                  rw [List.getElem_append_left (by omega)]
                  have h_lq : (st.acc[st.acc.length - 1]'(by omega)).2 = st.q := by
                    simpa [hlen_ne] using st.hlastQ
                  simpa [h_j1] using h_lq
              dsimp only at hlast ⊢
              simp only [heq, ↓reduceDIte] at hlast
              rw [h_take, h_el, h_prevQ]
              simp only [heq, List.append_assoc] at hlast ⊢
              exact hlast
            · have h0 : j ≠ 0 := by omega
              have h_prev : (st.acc ++ sc.seg)[j - 1]'(by omega) =
                  sc.seg[sc.seg.length - 1 - 1]'(by omega) := by
                rw [List.getElem_append_right (by omega)]
                congr 1; omega
              dsimp only at hlast ⊢
              simp only [h0, heq, ↓reduceDIte] at hlast ⊢
              rw [h_take, h_el, h_prev]
              simp only [List.append_assoc] at hlast ⊢
              exact hlast }
    let st : (m : Nat) → MonitorAccState spec σ tr₀ t q₀ m :=
      Nat.rec st₀ stepSt
    have h_ext_step : ∀ m, ∃ s, (st (m + 1)).acc = (st m).acc ++ s := fun m =>
      ⟨_, rfl⟩
    have h_ext : ∀ m₁ m₂, m₁ ≤ m₂ → ∃ s, (st m₂).acc = (st m₁).acc ++ s := by
      intro m₁ m₂ hle
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      clear hle
      induction d with
      | zero => exact ⟨[], by simp⟩
      | succ d ih =>
        obtain ⟨s₁, hs₁⟩ := ih
        obtain ⟨s₂, hs₂⟩ := h_ext_step (m₁ + d)
        exact ⟨s₁ ++ s₂, by rw [← Nat.add_assoc, hs₂, hs₁, List.append_assoc]⟩
    let ev : Stream' (Event E) := fun n =>
      ((st (n + 1)).acc[n]'(Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (st (n + 1)).hlen)).1
    let q : Stream' QState := fun n =>
      match n with
      | 0 => q₀
      | m + 1 =>
        ((st (m + 1)).acc[m]'(Nat.lt_of_lt_of_le (Nat.lt_succ_self m) (st (m + 1)).hlen)).2
    have h_el_eq : ∀ {m j} (hj : j < (st m).acc.length),
        (st m).acc[j] = (ev j, q (j + 1)) := by
      intro m j hj
      have hj' : j < (st (j + 1)).acc.length :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self j) (st (j + 1)).hlen
      by_cases hle : j + 1 ≤ m
      · obtain ⟨s, hs⟩ := h_ext (j + 1) m hle
        have h_at : (st m).acc[j] = (st (j + 1)).acc[j] := by
          have : ((st (j + 1)).acc ++ s)[j]'(by rw [← hs]; exact hj) =
              (st (j + 1)).acc[j] := List.getElem_append_left hj'
          simpa [hs] using this
        rw [h_at]
      · obtain ⟨s, hs⟩ := h_ext m (j + 1) (by omega)
        have h_at : (st (j + 1)).acc[j] = (st m).acc[j] := by
          have : ((st m).acc ++ s)[j]'(by rw [← hs]; exact hj') = (st m).acc[j] :=
            List.getElem_append_left hj
          simpa [hs] using this
        have h_eta : (st m).acc[j] = ((st m).acc[j].1, (st m).acc[j].2) := rfl
        rw [h_eta, ← h_at]
    have h_take_eq : ∀ m j, j ≤ (st m).acc.length →
        ((st m).acc.take j).map Prod.fst = takePrefix ev j := by
      intro m j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro hj
        have h_take_succ : (st m).acc.take (j + 1) =
            (st m).acc.take j ++ [(st m).acc[j]'(Nat.lt_of_succ_le hj)] :=
          List.take_succ_eq_append_getElem (Nat.lt_of_succ_le hj)
        rw [h_take_succ, List.map_append, ih (Nat.le_of_succ_le hj)]
        have h_ev := congrArg Prod.fst (h_el_eq (Nat.lt_of_succ_le hj))
        simp [h_ev]
    refine ⟨ev, q, fun n => ?_, rfl, fun n => ?_, fun k => ?_⟩
    · obtain ⟨u_n, hu_n⟩ := (st n).hreach_pref n (st n).hlen
      exact ⟨u_n, h_take_eq n n (st n).hlen ▸ hu_n⟩
    · have hn : n < (st (n + 1)).acc.length :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (st (n + 1)).hlen
      have hst_n := (st (n + 1)).hstep_all n hn
      have h_take_n := h_take_eq (n + 1) n (Nat.le_of_lt hn)
      have h_el_n := h_el_eq hn
      have h_prev : (if _ : n = 0 then q₀ else ((st (n + 1)).acc[n - 1]'(by omega)).2) = q n := by
        cases n with
        | zero => rfl
        | succ m =>
          simp only [Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel]
          exact congrArg Prod.snd (h_el_eq (Nat.lt_trans (Nat.lt_succ_self m) hn))
      have h_tr_next : (tr₀ ++ takePrefix ev n) ++ [ev n] = tr₀ ++ takePrefix ev (n + 1) := by
        show (tr₀ ++ takePrefix ev n) ++ [ev n] = tr₀ ++ (takePrefix ev n ++ [ev n])
        rw [List.append_assoc]
      have h_inv_n : spec.inv (q n) (tr₀ ++ takePrefix ev n) := by
        cases n with
        | zero => simpa [q] using hi₀
        | succ m =>
          have hm : m < (st (m + 1)).acc.length :=
            Nat.lt_of_lt_of_le (Nat.lt_succ_self m) (st (m + 1)).hlen
          have h_m := ((st (m + 1)).hstep_all m hm).1
          have h_tm := h_take_eq (m + 1) m (Nat.le_of_lt hm)
          have h_em := h_el_eq hm
          have h_tr_m : (tr₀ ++ takePrefix ev m) ++ [ev m] = tr₀ ++ takePrefix ev (m + 1) := by
            show (tr₀ ++ takePrefix ev m) ++ [ev m] = tr₀ ++ (takePrefix ev m ++ [ev m])
            rw [List.append_assoc]
          rw [h_tm, h_em, h_tr_m] at h_m
          exact h_m
      dsimp only at hst_n
      rw [h_take_n, h_el_n, h_prev, h_tr_next] at hst_n
      exact ⟨h_inv_n, hst_n.2⟩
    · obtain ⟨j, hj, hkj, hacc_j⟩ := (st (k + 1)).hacc_all k (Nat.lt_succ_self k)
      have h_take_j := h_take_eq (k + 1) j (Nat.le_of_lt hj)
      have h_el_j := h_el_eq hj
      have h_prev : (if _ : j = 0 then q₀ else ((st (k + 1)).acc[j - 1]'(by omega)).2) = q j := by
        cases j with
        | zero => rfl
        | succ m =>
          simp only [Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel]
          exact congrArg Prod.snd (h_el_eq (Nat.lt_trans (Nat.lt_succ_self m) hj))
      have h_tr_next : (tr₀ ++ takePrefix ev j) ++ [ev j] = tr₀ ++ takePrefix ev (j + 1) := by
        show (tr₀ ++ takePrefix ev j) ++ [ev j] = tr₀ ++ (takePrefix ev j ++ [ev j])
        rw [List.append_assoc]
      dsimp only at hacc_j
      rw [h_take_j, h_el_j, h_prev, h_tr_next] at hacc_j
      exact ⟨j, hkj, hacc_j⟩

/-- Lift stateless `BuchiSat` over `[PureSoundWP spec.ewp]` to `spec.toTrace`. -/
theorem BuchiSat.toTrace {QState : Type u} {E : Effect.{u}} {R : Type u}
    {spec : BuchiSpec PUnit.{u + 1} QState E R}
    {t : ITree E R} {q₀ : QState} (tr₀ : List (Event E))
    (h : BuchiSat spec t q₀ PUnit.unit) :
    BuchiSat spec.toTrace t q₀ tr₀ := by
  have ⟨hi, hio⟩ := (buchiSat_iff_infOften spec t q₀ PUnit.unit).1 h
  refine (buchiSat_iff_infOften spec.toTrace t q₀ tr₀).2 ⟨hi, ?_⟩
  let X := fun x (qs : QState × List (Event E)) =>
    InfOften spec.monitorWP spec.acceptEdge spec.terminalPost x (qs.1, PUnit.unit)
  refine InfOften.coinduct X ?_ hio
  intro x qs hx
  dsimp only [X] at hx
  refine buchiProgress.induct
    (fun y qp => ∀ tr, buchiProgress spec.toTrace.monitorWP spec.toTrace.acceptEdge
      spec.toTrace.terminalPost X y (qp.1, tr)) ?_ hx.toBuchiProgress qs.2
  intro y qp hy tr
  rw [buchiProgress.unfold_eq]
  cases h_obs : y.observe <;> simp only [h_obs] at hy ⊢
  · exact hy
  · exact hy tr
  · exact spec.ewp.mono (fun _ _ ⟨q', hs, hi', hp⟩ =>
      ⟨q', hs, hi', hp.imp id (fun hpre => hpre _)⟩) hy

/--
**Arbitrary nondeterministic `BuchiSat` `EnvStrategy` operational soundness
(`PureSoundWP`)**.
-/
theorem pure_buchiSat_strategy_adequacy {QState : Type u}
    {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (spec : BuchiSpec PUnit.{u + 1} QState E R) [PureSoundWP spec.ewp]
    {t : ITree E R} {q₀ : QState} (h : BuchiSat spec t q₀ PUnit.unit)
    (σ : EnvStrategy E) (tr₀ : List (Event E) := []) :
    (∃ tr r q', RetWithStrategy σ tr₀ t tr r ∧
        spec.inv q' PUnit.unit ∧ spec.terminal q' r PUnit.unit) ∨
      (∃ (ev : Stream' (Event E)) (q : Stream' QState),
        InfRunWithStrategy σ tr₀ t ev ∧ q 0 = q₀ ∧
        (∀ n, spec.inv (q n) PUnit.unit ∧
          spec.step (q n) (ev n).req (ev n).ans PUnit.unit PUnit.unit (q (n + 1))) ∧
        (∀ k, ∃ n, k ≤ n ∧
          spec.accept (q n) (ev n).req (ev n).ans PUnit.unit PUnit.unit (q (n + 1)))) :=
  trace_buchiSat_strategy_adequacy spec.toTrace (BuchiSat.toTrace tr₀ h) σ

@[simp]
theorem takePrefix_length {α : Type u} (ev : Stream' α) :
    ∀ n : Nat, (takePrefix ev n).length = n
  | 0 => rfl
  | n + 1 => by simp [takePrefix_length ev n]

private theorem reachesWithStrategy_nil_tauStar {E : Effect.{u}} {R : Type u}
    [FaultEffect E] {σ : EnvStrategy E} {hist : List (Event E)} {t u : ITree E R}
    (h : ReachesWithStrategy σ hist t [] u) : TauStar t u := by
  generalize htr : ([] : List (Event E)) = tr at h
  induction h with
  | refl => exact .refl _
  | tau htau _ ih => exact .step htau (ih htr)
  | vis _ _ _ => exact nomatch htr

private theorem reachesWithStrategy_cons_inv {E : Effect.{u}} {R : Type u}
    [FaultEffect E] {σ : EnvStrategy E} {hist tr : List (Event E)} {e : Event E}
    {t u : ITree E R} (h : ReachesWithStrategy σ hist t (e :: tr) u) :
    ∃ (w : ITree E R) (i : E.I) (k : E.O i → ITree E R) (hnf : ¬ FaultEffect.isFault i),
      TauStar t w ∧ w.observe = .vis i k ∧ e = ⟨i, σ hist i hnf⟩ ∧
        ReachesWithStrategy σ (hist ++ [e]) (k (σ hist i hnf)) tr u := by
  generalize htr : e :: tr = tr₀ at h
  induction h with
  | refl => exact nomatch htr
  | tau htau _ ih =>
    obtain ⟨w, i, k, hnf, hts, hv, he, hr⟩ := ih htr
    exact ⟨w, i, k, hnf, .step htau hts, hv, he, hr⟩
  | vis hv hnf hcont =>
    injection htr with he' htr'
    subst he'; subst htr'
    exact ⟨_, _, _, hnf, .refl _, hv, rfl, hcont⟩

/-- Deterministic strategies produce a unique trace of any given length. -/
theorem reachesWithStrategy_trace_unique {E : Effect.{u}} {R : Type u}
    [FaultEffect E] {σ : EnvStrategy E} :
    ∀ {hist tr₁ tr₂ : List (Event E)} {t u₁ u₂ : ITree E R},
      ReachesWithStrategy σ hist t tr₁ u₁ →
      ReachesWithStrategy σ hist t tr₂ u₂ →
      tr₁.length = tr₂.length → tr₁ = tr₂
  | _, [], [], _, _, _, _, _, _ => rfl
  | _, [], _ :: _, _, _, _, _, _, hlen => by simp at hlen
  | _, _ :: _, [], _, _, _, _, _, hlen => by simp at hlen
  | hist, e₁ :: rest₁, e₂ :: rest₂, t, _, _, h₁, h₂, hlen => by
    obtain ⟨w₁, i₁, k₁, hnf₁, hts₁, hv₁, he₁, hr₁⟩ := reachesWithStrategy_cons_inv h₁
    obtain ⟨w₂, i₂, k₂, hnf₂, hts₂, hv₂, he₂, hr₂⟩ := reachesWithStrategy_cons_inv h₂
    have hw : w₁ = w₂ := TauStar.unique_nonTau hts₁ hts₂
      (fun _ ht => by rw [hv₁] at ht; exact nomatch ht)
      (fun _ ht => by rw [hv₂] at ht; exact nomatch ht)
    subst hw
    rw [hv₁] at hv₂
    injection hv₂ with hi hk
    subst hi
    have hk' : k₁ = k₂ := eq_of_heq hk
    subst hk'
    have he : e₁ = e₂ := by rw [he₁, he₂]
    subst he
    rw [he₁] at hr₁ hr₂
    exact congrArg (List.cons _) (reachesWithStrategy_trace_unique hr₁ hr₂ (Nat.succ.inj hlen))

private theorem reachesWithStrategy_ret_no_extend {E : Effect.{u}} {R : Type u}
    [FaultEffect E] {σ : EnvStrategy E} :
    ∀ {hist tr₁ tr₂ : List (Event E)} {t u₁ u₂ : ITree E R} {r : R},
      ReachesWithStrategy σ hist t tr₁ u₁ → u₁.observe = .ret r →
      ReachesWithStrategy σ hist t tr₂ u₂ → tr₂.length ≤ tr₁.length
  | _, [], [], _, _, _, _, _, _, _ => Nat.le_refl 0
  | _, [], _ :: _, _, _, _, _, h₁, hret, h₂ => by
    have hts₁ := reachesWithStrategy_nil_tauStar h₁
    obtain ⟨w₂, _, _, _, hts₂, hv₂, _, _⟩ := reachesWithStrategy_cons_inv h₂
    have hw := TauStar.unique_nonTau hts₁ hts₂
      (fun _ ht => by rw [hret] at ht; exact nomatch ht)
      (fun _ ht => by rw [hv₂] at ht; exact nomatch ht)
    subst hw; rw [hret] at hv₂; exact nomatch hv₂
  | _, _ :: _, [], _, _, _, _, _, _, _ => Nat.zero_le _
  | _, e₁ :: rest₁, e₂ :: rest₂, _, _, _, _, h₁, hret, h₂ => by
    obtain ⟨w₁, i₁, k₁, _, hts₁, hv₁, he₁, hr₁⟩ := reachesWithStrategy_cons_inv h₁
    obtain ⟨w₂, i₂, k₂, _, hts₂, hv₂, he₂, hr₂⟩ := reachesWithStrategy_cons_inv h₂
    have hw := TauStar.unique_nonTau hts₁ hts₂
      (fun _ ht => by rw [hv₁] at ht; exact nomatch ht)
      (fun _ ht => by rw [hv₂] at ht; exact nomatch ht)
    subst hw; rw [hv₁] at hv₂; injection hv₂ with hi hk; subst hi
    have hk' : k₁ = k₂ := eq_of_heq hk
    subst hk'
    have he : e₁ = e₂ := by rw [he₁, he₂]
    subst he; rw [he₁] at hr₁ hr₂
    exact Nat.succ_le_succ (reachesWithStrategy_ret_no_extend hr₁ hret hr₂)

private theorem reachesWithStrategy_ret_val_unique {E : Effect.{u}} {R : Type u}
    [FaultEffect E] {σ : EnvStrategy E} :
    ∀ {hist tr : List (Event E)} {t u₁ u₂ : ITree E R} {r₁ r₂ : R},
      ReachesWithStrategy σ hist t tr u₁ → u₁.observe = .ret r₁ →
      ReachesWithStrategy σ hist t tr u₂ → u₂.observe = .ret r₂ → r₁ = r₂
  | _, [], _, _, _, _, _, h₁, hr₁, h₂, hr₂ => by
    have hw := TauStar.unique_nonTau
      (reachesWithStrategy_nil_tauStar h₁) (reachesWithStrategy_nil_tauStar h₂)
      (fun _ ht => by rw [hr₁] at ht; exact nomatch ht)
      (fun _ ht => by rw [hr₂] at ht; exact nomatch ht)
    subst hw; rw [hr₁] at hr₂; injection hr₂
  | _, e :: rest, _, _, _, _, _, h₁, hr₁, h₂, hr₂ => by
    obtain ⟨w₁, i₁, k₁, _, hts₁, hv₁, he₁, hcont₁⟩ := reachesWithStrategy_cons_inv h₁
    obtain ⟨w₂, i₂, k₂, _, hts₂, hv₂, he₂, hcont₂⟩ := reachesWithStrategy_cons_inv h₂
    have hw := TauStar.unique_nonTau hts₁ hts₂
      (fun _ ht => by rw [hv₁] at ht; exact nomatch ht)
      (fun _ ht => by rw [hv₂] at ht; exact nomatch ht)
    subst hw; rw [hv₁] at hv₂; injection hv₂ with hi hk; subst hi
    have hk' : k₁ = k₂ := eq_of_heq hk
    subst hk'; rw [he₁] at hcont₁ hcont₂
    exact reachesWithStrategy_ret_val_unique hcont₁ hr₁ hcont₂ hr₂

/-- Against a fixed deterministic strategy `σ`, a return trace and value are unique. -/
theorem retWithStrategy_unique {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {σ : EnvStrategy E} {hist tr₁ tr₂ : List (Event E)} {t : ITree E R} {r₁ r₂ : R}
    (h₁ : RetWithStrategy σ hist t tr₁ r₁) (h₂ : RetWithStrategy σ hist t tr₂ r₂) :
    tr₁ = tr₂ ∧ r₁ = r₂ := by
  obtain ⟨u₁, hr₁, ho₁⟩ := h₁
  obtain ⟨u₂, hr₂, ho₂⟩ := h₂
  have hlen : tr₁.length = tr₂.length :=
    Nat.le_antisymm (reachesWithStrategy_ret_no_extend hr₂ ho₂ hr₁)
      (reachesWithStrategy_ret_no_extend hr₁ ho₁ hr₂)
  have htr : tr₁ = tr₂ := reachesWithStrategy_trace_unique hr₁ hr₂ hlen
  subst htr
  exact ⟨rfl, reachesWithStrategy_ret_val_unique hr₁ ho₁ hr₂ ho₂⟩

/-- Against a fixed strategy `σ`, `t` cannot both return and produce an infinite run. -/
theorem not_ret_and_infRunWithStrategy {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {σ : EnvStrategy E} {hist tr : List (Event E)} {t : ITree E R} {r : R}
    {ev : Stream' (Event E)}
    (hret : RetWithStrategy σ hist t tr r) (hinf : InfRunWithStrategy σ hist t ev) :
    False := by
  obtain ⟨u₁, hr₁, ho₁⟩ := hret
  obtain ⟨u₂, hr₂⟩ := hinf (tr.length + 1)
  have hle := reachesWithStrategy_ret_no_extend hr₁ ho₁ hr₂
  rw [takePrefix_length] at hle
  omega

/-- Against a fixed deterministic strategy `σ`, any infinite run `ev` is unique. -/
theorem infRunWithStrategy_unique {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {σ : EnvStrategy E} {hist : List (Event E)} {t : ITree E R}
    {ev₁ ev₂ : Stream' (Event E)}
    (h₁ : InfRunWithStrategy σ hist t ev₁) (h₂ : InfRunWithStrategy σ hist t ev₂) :
    ev₁ = ev₂ := by
  funext n
  obtain ⟨u₁, hr₁⟩ := h₁ (n + 1)
  obtain ⟨u₂, hr₂⟩ := h₂ (n + 1)
  have heq : takePrefix ev₁ n ++ [ev₁ n] = takePrefix ev₂ n ++ [ev₂ n] :=
    reachesWithStrategy_trace_unique hr₁ hr₂ (by simp [takePrefix_length])
  exact (List.cons.inj (List.append_inj_right' heq rfl)).1

/--
**Strong-fairness operational adequacy (`TraceSoundWP`)**: combining a program
enabling obligation `InfOften ewp Enabled Q₁` (ruling out vacuous load-spinning)
with conditional Streett liveness `FairInfOften ewp AccEdge Fair Q₂` yields, for
every strategy `σ`, either a return satisfying `Q₁ ∧ Q₂` or a unique infinite run
enabling `Enabled` infinitely often and satisfying `□◇ Fair → □◇ AccEdge`.
-/
theorem trace_strongFair_strategy_adequacy {E : Effect.{u}} {R : Type u}
    [FaultEffect E] {ewp : StateEffectWP (List (Event E)) E} [TraceSoundWP ewp]
    {Enabled AccEdge Fair : (i : E.I) → E.O i → List (Event E) → List (Event E) → Prop}
    {Q₁ Q₂ : R → List (Event E) → Prop} {t : ITree E R} {tr₀ : List (Event E)}
    (h_en : InfOften ewp Enabled Q₁ t tr₀)
    (h_fair : FairInfOften ewp AccEdge Fair Q₂ t tr₀) (σ : EnvStrategy E) :
    (∃ tr r, RetWithStrategy σ tr₀ t tr r ∧ Q₁ r (tr₀ ++ tr) ∧ Q₂ r (tr₀ ++ tr)) ∨
      (∃ ev : Stream' (Event E), InfRunWithStrategy σ tr₀ t ev ∧
        (∀ k, ∃ n, k ≤ n ∧
          Enabled (ev n).req (ev n).ans (tr₀ ++ takePrefix ev n)
            (tr₀ ++ takePrefix ev (n + 1))) ∧
        ((∀ k, ∃ n, k ≤ n ∧
            Fair (ev n).req (ev n).ans (tr₀ ++ takePrefix ev n)
              (tr₀ ++ takePrefix ev (n + 1))) →
          (∀ k, ∃ n, k ≤ n ∧
            AccEdge (ev n).req (ev n).ans (tr₀ ++ takePrefix ev n)
              (tr₀ ++ takePrefix ev (n + 1))))) := by
  rcases trace_infOften_strategy_adequacy h_en σ with
    ⟨tr₁, r₁, hret₁, hq₁⟩ | ⟨ev₁, hinf₁, hen₁⟩
  · rcases trace_fairInfOften_strategy_adequacy h_fair σ with
      ⟨tr₂, r₂, hret₂, hq₂⟩ | ⟨ev₂, hinf₂, _⟩
    · obtain ⟨rfl, rfl⟩ := retWithStrategy_unique hret₁ hret₂
      exact Or.inl ⟨tr₁, r₁, hret₁, hq₁, hq₂⟩
    · exact False.elim (not_ret_and_infRunWithStrategy hret₁ hinf₂)
  · rcases trace_fairInfOften_strategy_adequacy h_fair σ with
      ⟨tr₂, r₂, hret₂, _⟩ | ⟨ev₂, hinf₂, hst₂⟩
    · exact False.elim (not_ret_and_infRunWithStrategy hret₂ hinf₁)
    · have hev : ev₁ = ev₂ := infRunWithStrategy_unique hinf₁ hinf₂
      subst hev
      exact Or.inr ⟨ev₁, hinf₁, hen₁, hst₂⟩

/--
**Guaranteed operational termination under strong fairness (`TraceSoundWP`)**:
if every diverging run of `t` enables `Enabled` infinitely often (`InfOften`)
and `t` terminates whenever `Fair` fires infinitely often (`CoBuchi`), then `t`
**must return with `Q`** against every strategy `σ` that is strongly fair for
`(Enabled, Fair)` along `t`'s execution.
-/
theorem trace_strongFair_terminates {E : Effect.{u}} {R : Type u}
    [FaultEffect E] {ewp : StateEffectWP (List (Event E)) E} [TraceSoundWP ewp]
    {Enabled Fair : (i : E.I) → E.O i → List (Event E) → List (Event E) → Prop}
    {Q : R → List (Event E) → Prop} {t : ITree E R} {tr₀ : List (Event E)}
    (h_en : InfOften ewp Enabled Q t tr₀)
    (h_cb : CoBuchi ewp Fair Q t tr₀) (σ : EnvStrategy E)
    (h_sf : ∀ ev : Stream' (Event E), InfRunWithStrategy σ tr₀ t ev →
      (∀ k, ∃ n, k ≤ n ∧
        Enabled (ev n).req (ev n).ans (tr₀ ++ takePrefix ev n)
          (tr₀ ++ takePrefix ev (n + 1))) →
      (∀ k, ∃ n, k ≤ n ∧
        Fair (ev n).req (ev n).ans (tr₀ ++ takePrefix ev n)
          (tr₀ ++ takePrefix ev (n + 1)))) :
    ∃ tr r, RetWithStrategy σ tr₀ t tr r ∧ Q r (tr₀ ++ tr) := by
  rcases trace_strongFair_strategy_adequacy h_en h_cb σ with
    ⟨tr, r, hret, hq, _⟩ | ⟨ev, hinf, hen, hst⟩
  · exact ⟨tr, r, hret, hq⟩
  · obtain ⟨_, _, hf⟩ := hst (h_sf ev hinf hen) 0
    exact False.elim hf

/-- **Strong-fairness operational adequacy (`PureSoundWP`)**. -/
theorem pure_strongFair_strategy_adequacy {E : Effect.{u}} {R : Type u}
    [FaultEffect E] {ewp : EffectWP E} [PureSoundWP ewp]
    {Enabled AccEdge Fair : (i : E.I) → E.O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop}
    {Q₁ Q₂ : R → PUnit.{u + 1} → Prop} {t : ITree E R}
    (h_en : InfOften ewp Enabled Q₁ t PUnit.unit)
    (h_fair : FairInfOften ewp AccEdge Fair Q₂ t PUnit.unit)
    (σ : EnvStrategy E) (tr₀ : List (Event E) := []) :
    (∃ tr r, RetWithStrategy σ tr₀ t tr r ∧ Q₁ r PUnit.unit ∧ Q₂ r PUnit.unit) ∨
      (∃ ev : Stream' (Event E), InfRunWithStrategy σ tr₀ t ev ∧
        (∀ k, ∃ n, k ≤ n ∧ Enabled (ev n).req (ev n).ans PUnit.unit PUnit.unit) ∧
        ((∀ k, ∃ n, k ≤ n ∧ Fair (ev n).req (ev n).ans PUnit.unit PUnit.unit) →
          (∀ k, ∃ n, k ≤ n ∧ AccEdge (ev n).req (ev n).ans PUnit.unit PUnit.unit))) :=
  trace_strongFair_strategy_adequacy
    ((fairInfOften_true_iff_infOften _ _ _ _ _).1
      (FairInfOften.toTraceLift tr₀ (h_en.toFairInfOften (fun _ _ _ _ => True))))
    (FairInfOften.toTraceLift tr₀ h_fair) σ

/-- **Guaranteed operational termination under strong fairness (`PureSoundWP`)**. -/
theorem pure_strongFair_terminates {E : Effect.{u}} {R : Type u}
    [FaultEffect E] {ewp : EffectWP E} [PureSoundWP ewp]
    {Enabled Fair : (i : E.I) → E.O i → PUnit.{u + 1} → PUnit.{u + 1} → Prop}
    {Q : R → PUnit.{u + 1} → Prop} {t : ITree E R}
    (h_en : InfOften ewp Enabled Q t PUnit.unit)
    (h_cb : CoBuchi ewp Fair Q t PUnit.unit)
    (σ : EnvStrategy E) (tr₀ : List (Event E) := [])
    (h_sf : ∀ ev : Stream' (Event E), InfRunWithStrategy σ tr₀ t ev →
      (∀ k, ∃ n, k ≤ n ∧ Enabled (ev n).req (ev n).ans PUnit.unit PUnit.unit) →
      (∀ k, ∃ n, k ≤ n ∧ Fair (ev n).req (ev n).ans PUnit.unit PUnit.unit)) :
    ∃ tr r, RetWithStrategy σ tr₀ t tr r ∧ Q r PUnit.unit :=
  trace_strongFair_terminates
    ((fairInfOften_true_iff_infOften _ _ _ _ _).1
      (FairInfOften.toTraceLift tr₀ (h_en.toFairInfOften (fun _ _ _ _ => True))))
    (FairInfOften.toTraceLift tr₀ h_cb) σ h_sf

end StrategyAdequacy

/-! #### Completeness Boundary of `BuchiSat` for Nondeterministic Monitors -/

section BuchiNondetIncomplete

/-- Two visible letters: `fgReqA` (`a`) and `fgReqB` (`b`), each answered by a `Bool`. -/
abbrev FgE : Effect.{0} := CallE Bool (fun _ => Bool)

/-- The letter `a`. -/
def fgReqA : FgE.I := CallReq.call true

/-- The letter `b`. -/
def fgReqB : FgE.I := CallReq.call false

/-- Decode the environment's boolean answer. -/
def fgAns : (i : FgE.I) → FgE.O i → Bool
  | .call _, b => b

/-- Answer "keep emitting `a`" to the letter `a`. -/
def fgYes : FgE.O fgReqA := (true : Bool)

/-- Answer "switch to `b`" to the letter `a`. -/
def fgNo : FgE.O fgReqA := (false : Bool)

/-- Any answer to the letter `b`. -/
def fgAnyB : FgE.O fgReqB := (true : Bool)

/-- Demonic environment answering every letter. -/
abbrev fgWP : StateEffectWP PUnit.{1} FgE :=
  unconstrainedCallWP PUnit.{1} Bool (fun _ => Bool)

/-- `b`-edges. -/
def fgIsB : (i : FgE.I) → FgE.O i → PUnit.{1} → PUnit.{1} → Prop :=
  fun i _ _ _ => i = fgReqB

/--
Coalgebra of the tree `T = a. (T + b. a^ω)`: in state `none` emit `a` and let
the environment decide between staying in `T` or moving to `some false`
(emit one `b`), after which `some true` emits `a` forever.
-/
def fgStep : Option Bool → ITreeF FgE PEmpty.{1} (Option Bool)
  | none => .vis fgReqA (fun c => if fgAns fgReqA c then none else some false)
  | some false => .vis fgReqB (fun _ => some true)
  | some true => .vis fgReqA (fun _ => some true)

/-- The trees of the coalgebra `fgStep`. -/
def fgTree : Option Bool → ITree FgE PEmpty.{1} :=
  ITree.cofix fgStep

theorem fgTree_none_observe :
    (fgTree none).observe =
      .vis fgReqA (fun c => fgTree (if fgAns fgReqA c then none else some false)) :=
  (ITree.observe_cofix _ _).trans rfl

theorem fgTree_b_observe :
    (fgTree (some false)).observe = .vis fgReqB (fun _ => fgTree (some true)) :=
  (ITree.observe_cofix _ _).trans rfl

theorem fgTree_a_observe :
    (fgTree (some true)).observe = .vis fgReqA (fun _ => fgTree (some true)) :=
  (ITree.observe_cofix _ _).trans rfl

/--
The textbook two-state nondeterministic Büchi automaton for `◇□ a`: state
`false` reads anything and may guess to commit; state `true` only reads `a`
and accepts.
-/
def fgSpec : BuchiSpec PUnit.{1} Bool FgE PEmpty.{1} where
  ewp := fgWP
  step q i _ _ _ q' := q = false ∨ (q' = true ∧ i = fgReqA)
  accept _ _ _ _ _ q' := q' = true
  inv _ _ := True
  terminal _ _ _ := False

private theorem fgReqB_ne_fgReqA : fgReqB ≠ fgReqA :=
  fun h => Bool.noConfusion (CallReq.call.inj h)

private theorem fg_b_dead (X : ITree FgE PEmpty.{1} → Bool × PUnit.{1} → Prop) :
    ¬ buchiProgress fgSpec.monitorWP fgSpec.acceptEdge fgSpec.terminalPost X
      (fgTree (some false)) (true, PUnit.unit) := by
  intro h
  rw [buchiProgress.unfold_eq, fgTree_b_observe] at h
  obtain ⟨q', hstep, _⟩ := h fgAnyB
  rcases hstep with hq | ⟨_, hi⟩
  · exact Bool.noConfusion hq
  · exact fgReqB_ne_fgReqA hi

private theorem fg_not_infOften_committed :
    ¬ InfOften fgSpec.monitorWP fgSpec.acceptEdge fgSpec.terminalPost
      (fgTree none) (true, PUnit.unit) := by
  intro h
  have hb := h.toBuchiProgress
  rw [buchiProgress.unfold_eq, fgTree_none_observe] at hb
  obtain ⟨q', hstep, _, hdisj⟩ := hb fgNo
  have hq' : q' = true := by
    rcases hstep with hq | ⟨hq, _⟩
    · exact Bool.noConfusion hq
    · exact hq
  subst hq'
  rcases hdisj with ⟨_, hio⟩ | hprog
  · exact fg_b_dead _ hio.toBuchiProgress
  · exact fg_b_dead _ hprog

/-- The tail `a^ω` is accepted from the committed state. -/
theorem fgSpec_accepts_a :
    BuchiSat fgSpec (fgTree (some true)) true PUnit.unit := by
  refine (buchiSat_iff_infOften _ _ _ _).2 ⟨trivial, ?_⟩
  refine InfOften.coinduct
    (fun x qs => x = fgTree (some true) ∧ qs.1 = true) ?_ ⟨rfl, rfl⟩
  rintro x ⟨q, s⟩ ⟨rfl, hq⟩
  rw [buchiProgress.unfold_eq, fgTree_a_observe]
  intro _
  exact ⟨true, Or.inr ⟨rfl, rfl⟩, trivial, Or.inl ⟨rfl, rfl, rfl⟩⟩

/-- The path `b a^ω` is accepted by guessing the commitment after the `b`. -/
theorem fgSpec_accepts_b :
    BuchiSat fgSpec (fgTree (some false)) false PUnit.unit := by
  refine (buchiSat_iff_infOften _ _ _ _).2 ⟨trivial, ?_⟩
  refine InfOften.of_buchiProgress ?_
  rw [buchiProgress.unfold_eq, fgTree_b_observe]
  intro _
  exact ⟨true, Or.inl rfl, trivial, Or.inl ⟨rfl,
    ((buchiSat_iff_infOften _ _ _ _).1 fgSpec_accepts_a).2⟩⟩

/--
Every path of `T` has only finitely many `b`s: `T` satisfies the co-Büchi
property `◇□ ¬ b`.
-/
theorem fgTree_coBuchi (Q : PEmpty.{1} → PUnit.{1} → Prop) :
    CoBuchi fgWP fgIsB Q (fgTree none) PUnit.unit := by
  have h_a : CoBuchi fgWP fgIsB Q (fgTree (some true)) PUnit.unit := by
    unfold CoBuchi
    rw [FairInfOften.unfold_eq, fairProgress.unfold_eq]
    refine fairStall.coinduct (fun x _ => x = fgTree (some true)) ?_ rfl
    rintro x s rfl
    rw [fairStep.unfold_eq, fgTree_a_observe]
    intro _
    exact Or.inr (Or.inr ⟨fun h => fgReqB_ne_fgReqA h.symm, rfl⟩)
  unfold CoBuchi at h_a ⊢
  rw [FairInfOften.unfold_eq, fairProgress.unfold_eq]
  refine fairStall.coinduct
    (fun x _ => x = fgTree none ∨ x = fgTree (some false)) ?_ (Or.inl rfl)
  rintro x s (rfl | rfl)
  · rw [fairStep.unfold_eq, fgTree_none_observe]
    intro c
    refine Or.inr (Or.inr ⟨fun h => fgReqB_ne_fgReqA h.symm, ?_⟩)
    show fgTree _ = fgTree none ∨ fgTree _ = fgTree (some false)
    cases fgAns fgReqA c
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rw [fairStep.unfold_eq, fgTree_b_observe]
    intro _
    refine Or.inr (Or.inl ⟨rfl, ?_⟩)
    rw [FairInfOften.unfold_eq] at h_a
    exact h_a

/--
**`BuchiSat` is incomplete for nondeterministic monitors.** Every path of
`T = a. (T + b. a^ω)` satisfies `◇□ a` (`fgTree_coBuchi`), and the two-state
NBA `fgSpec` for `◇□ a` accepts each kind of tail (`fgSpec_accepts_a`,
`fgSpec_accepts_b`), yet `BuchiSat fgSpec T q₀` fails from **every** initial
monitor state: the monitor must commit at the current tree position, but the
environment can always answer with one more `b`. Persistence properties should
be stated with `CoBuchi` / `FairInfOften`, or with deterministic monitors.
-/
theorem buchiSat_nondet_incomplete (Q : PEmpty.{1} → PUnit.{1} → Prop) :
    CoBuchi fgWP fgIsB Q (fgTree none) PUnit.unit ∧
      BuchiSat fgSpec (fgTree (some true)) true PUnit.unit ∧
      BuchiSat fgSpec (fgTree (some false)) false PUnit.unit ∧
      ∀ q₀ : Bool, ¬ BuchiSat fgSpec (fgTree none) q₀ PUnit.unit := by
  refine ⟨fgTree_coBuchi Q, fgSpec_accepts_a, fgSpec_accepts_b, ?_⟩
  intro q₀ hsat
  have hio := ((buchiSat_iff_infOften _ _ _ _).1 hsat).2
  cases q₀ with
  | true => exact fg_not_infOften_committed hio
  | false =>
    refine buchiProgress.induct (fun x _ => x = fgTree none → False) ?_
      hio.toBuchiProgress rfl
    rintro x ⟨q, s⟩ hx rfl
    rw [fgTree_none_observe] at hx
    obtain ⟨q', _, _, hdisj⟩ := hx fgYes
    rcases hdisj with ⟨hacc, hio'⟩ | hpre
    · have hq' : q' = true := hacc
      subst hq'
      exact fg_not_infOften_committed hio'
    · exact hpre rfl

end BuchiNondetIncomplete

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

/-- Deterministic monitor invariant-guarded product is co-continuous. -/
theorem BuchiSpec.monitorWP_downContinuous (spec : BuchiSpec S QState E R)
    [DownContinuous spec.ewp]
    (h_det : ∀ q i o s s' q₁ q₂,
      spec.step q i o s s' q₁ → spec.step q i o s s' q₂ → q₁ = q₂) :
    DownContinuous spec.monitorWP :=
  letI := BuchiSpec.prodWP_downContinuous spec h_det
  inferInstanceAs (DownContinuous (guardInvWP spec.prodWP spec.invPred))

instance (ewp : StateEffectWP S E) [h : DownContinuous ewp]
    (next : QState → (i : E.I) → E.O i → S → S → QState)
    (allow accept : QState → (i : E.I) → E.O i → S → S → Prop)
    (inv : QState → S → Prop) (terminal : QState → R → S → Prop) :
    DownContinuous (BuchiSpec.ofDet ewp next allow accept inv terminal).prodWP :=
  @BuchiSpec.prodWP_downContinuous _ _ _ _
    (BuchiSpec.ofDet ewp next allow accept inv terminal) h
    (BuchiSpec.ofDet_step_det ewp next allow accept inv terminal)

/-- The universal monitor product `univProdWP` is co-continuous without determinism. -/
instance (spec : BuchiSpec S QState E R) [h : DownContinuous spec.ewp] :
    DownContinuous spec.univProdWP where
  iInf {i P qs} ha hw :=
    spec.ewp.mono
      (fun _ _ hk => ⟨(hk 0).1, fun q' hs n => (hk n).2 q' hs⟩)
      (h.iInf
        (P := fun n o s' =>
          (∃ q', spec.step qs.1 i o qs.2 s' q') ∧
          ∀ q', spec.step qs.1 i o qs.2 s' q' → P n o (q', s'))
        (fun n _ _ hk => ⟨hk.1, fun q' hs => ha n _ _ (hk.2 q' hs)⟩) hw)

end BuchiSpecInstances

section IterChain

variable {S : Type u} {E : Effect.{u}} {I R : Type u}

/--
Finite-unfolding $\omega$-chain of `ITree.iter`: `iterChain 0` is the bottom
element `ITree.spin`, and `iterChain (n + 1)` runs one more loop iteration
before falling back to `iterChain n`. Defined directly via `Nat.rec` so no
compiler-only `._unsafe_rec` auxiliary is emitted.
-/
def iterChain (n : Nat) (body : I → ITree E (I ⊕ R)) (init : I) : ITree E R :=
  Nat.rec (motive := fun _ => I → ITree E R)
    (fun _ => ITree.spin)
    (fun _ ih a => body a >>= Sum.elim (fun next => .tau (ih next)) .ret)
    n init

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

/-- Safety continuity ($\bigwedge_n$) for `DWLP`. -/
theorem dwlp_iter_iff_forall_iterChain {ewp : StateEffectWP S E}
    [DownContinuous ewp] (Q : R → S → Prop)
    (body : I → ITree E (I ⊕ R)) (init : I) (s : S) :
    DWLP ewp (ITree.iter body init) Q s ↔
      ∀ n, DWLP ewp (iterChain n body init) Q s := by
  rw [← always_true_iff_dwlp, always_iter_iff_forall_iterChain]
  exact forall_congr' fun n => always_true_iff_dwlp ewp Q _ s

/-- Safety continuity ($\bigwedge_n$) for `AlwaysStep`. -/
theorem alwaysStep_iter_iff_forall_iterChain {ewp : StateEffectWP S E}
    [DownContinuous ewp]
    (StepRel : (i : E.I) → E.O i → S → S → Prop) (Q : R → S → Prop)
    (body : I → ITree E (I ⊕ R)) (init : I) (s : S) :
    AlwaysStep ewp StepRel Q (ITree.iter body init) s ↔
      ∀ n, AlwaysStep ewp StepRel Q (iterChain n body init) s := by
  rw [alwaysStep_iff_dwlp, dwlp_iter_iff_forall_iterChain]
  exact forall_congr' fun n => (alwaysStep_iff_dwlp ewp StepRel Q _ s).symm

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

/-- `Eventually` on any finite unfolding transfers unconditionally to the loop. -/
theorem Eventually.iter_of_iterChain {ewp : StateEffectWP S E}
    {Target : S → Prop} {Q : R → S → Prop}
    (body : I → ITree E (I ⊕ R)) (n : Nat) {init : I} {s : S}
    (h : Eventually ewp Target Q (iterChain n body init) s) :
    Eventually ewp Target Q (ITree.iter body init) s :=
  (eventually_iff_until ewp Target Q _ s).2
    (Until.iter_of_iterChain body n ((eventually_iff_until ewp Target Q _ s).1 h))

/-- `DWP` on any finite unfolding transfers unconditionally to the loop. -/
theorem DWP.iter_of_iterChain {ewp : StateEffectWP S E} {Q : R → S → Prop}
    (body : I → ITree E (I ⊕ R)) (n : Nat) {init : I} {s : S}
    (h : DWP ewp (iterChain n body init) Q s) :
    DWP ewp (ITree.iter body init) Q s :=
  (dwp_iff_until ewp Q _ s).2
    (Until.iter_of_iterChain body n ((dwp_iff_until ewp Q _ s).1 h))

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

/--
Under conjunctivity and excluded miracle, a tree that terminates with `P`
cannot satisfy `FairInfOften` (hence also `CoBuchi`) with a postcondition
disjoint from `P`.
-/
theorem not_fairInfOften_of_dwp_disjoint {ewp : StateEffectWP S E}
    [h_conj : StateEffectWP.Conjunctive ewp]
    [h_em : StateEffectWP.ExcludedMiracle ewp]
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop} {P Q : R → S → Prop}
    (h_dis : ∀ r s', P r s' → ¬ Q r s') {t : ITree E R} {s : S}
    (h : DWP ewp t P s) : ¬ FairInfOften ewp AccEdge Fair Q t s := by
  refine DWP.induct (fun x s₀ => ¬ FairInfOften ewp AccEdge Fair Q x s₀) ?_ h
  intro x s₀ hx hfi
  cases h_obs : x.observe with
  | ret r =>
    simp only [h_obs] at hx
    rw [eq_ret_of_observe h_obs, FairInfOften.ret_iff] at hfi
    exact h_dis r s₀ hx hfi
  | tau x' =>
    simp only [h_obs] at hx
    rw [eq_tau_of_observe h_obs, FairInfOften.tau_iff] at hfi
    exact hx hfi
  | vis i k =>
    simp only [h_obs] at hx
    rw [eq_vis_of_observe h_obs, FairInfOften.vis_iff] at hfi
    exact h_em.no_miracle
      (ewp.mono (fun _ _ hp => hp.1 hp.2) (h_conj.conj hx hfi))

/--
Every finite unfolding of a diverging loop with terminating iterations ends in
`ITree.spin` and therefore **fails** `FairInfOften` (and `CoBuchi`), for every
`(AccEdge, Fair)`.
-/
theorem not_fairInfOften_iterChain_divergingLoop {ewp : StateEffectWP S E}
    [StateEffectWP.Conjunctive ewp] [StateEffectWP.ExcludedMiracle ewp]
    {AccEdge Fair : (i : E.I) → E.O i → S → S → Prop}
    (body : I → ITree E I) (LInv : I → S → Prop)
    (h_term : ∀ a s₀, LInv a s₀ → DWP ewp (body a) LInv s₀)
    (Q : R → S → Prop) :
    ∀ (n : Nat) {init : I} {s : S}, LInv init s →
      ¬ FairInfOften ewp AccEdge Fair Q
        (iterChain n (fun a => (Sum.inl <$> body a : ITree E (I ⊕ R))) init) s
  | 0, _, _, _ => not_fairInfOften_spin
  | n + 1, init, s, h_init => by
    have h_eq : (Sum.inl <$> body init : ITree E (I ⊕ R)) =
        (body init >>= fun a => ITree.ret (Sum.inl a)) := rfl
    rw [iterChain_succ, FairInfOften.bind_iff, h_eq, FairInfOften.bind_iff]
    refine not_fairInfOften_of_dwp_disjoint ?_ (h_term init s h_init)
    intro a s' ha hfi
    rw [FairInfOften.ret_iff] at hfi
    exact not_fairInfOften_iterChain_divergingLoop body LInv h_term Q n ha
      ((FairInfOften.tau_iff _ _ _ _ _ _).1 hfi)

/--
**`FairInfOften` is neither $\bigwedge_n$ nor $\bigvee_n$ chain-continuous.**
The fair reactive CAS service loop satisfies `FairInfOften` while failing on
*every* finite unfolding `iterChain n`.
-/
theorem fairService_not_chain_continuous (Q : PEmpty.{1} → PUnit.{1} → Prop) :
    FairInfOften (pickWP PUnit.{1} Bool) casFair casFair Q
        (divergingLoop fairServiceBody PUnit.unit) PUnit.unit ∧
      (∀ n, ¬ FairInfOften (pickWP PUnit.{1} Bool) casFair casFair Q
        (iterChain n (fun a => Sum.inl <$> fairServiceBody a) PUnit.unit) PUnit.unit) ∧
      ¬ (FairInfOften (pickWP PUnit.{1} Bool) casFair casFair Q
            (divergingLoop fairServiceBody PUnit.unit) PUnit.unit ↔
          ∀ n, FairInfOften (pickWP PUnit.{1} Bool) casFair casFair Q
            (iterChain n (fun a => Sum.inl <$> fairServiceBody a) PUnit.unit) PUnit.unit) ∧
      ¬ (FairInfOften (pickWP PUnit.{1} Bool) casFair casFair Q
            (divergingLoop fairServiceBody PUnit.unit) PUnit.unit ↔
          ∃ n, FairInfOften (pickWP PUnit.{1} Bool) casFair casFair Q
            (iterChain n (fun a => Sum.inl <$> fairServiceBody a) PUnit.unit) PUnit.unit) := by
  have h_yes := (fairService_strict_separation Q).2.1
  have h_no : ∀ n, ¬ FairInfOften (pickWP PUnit.{1} Bool) casFair casFair Q
      (iterChain n (fun a => Sum.inl <$> fairServiceBody a) PUnit.unit) PUnit.unit := fun n =>
    not_fairInfOften_iterChain_divergingLoop (ewp := pickWP PUnit.{1} Bool)
      fairServiceBody (fun _ _ => True)
      (fun _ _ _ => DWP.vis ⟨⟨true⟩, fun _ => DWP.ret trivial⟩) Q n trivial
  exact ⟨h_yes, h_no, fun h => h_no 0 (h.1 h_yes 0), fun h => (h.1 h_yes).elim h_no⟩

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
**`CoBuchi` is neither $\bigwedge_n$ nor $\bigvee_n$ chain-continuous.** The
heartbeat loop satisfies `CoBuchi` (no bad edges) while failing on *every*
finite unfolding `iterChain n`.
-/
theorem coBuchi_heartbeat_not_chain_continuous
    (Q : PEmpty.{u + 1} → PUnit.{u + 1} → Prop) :
    CoBuchi (obsIgnoreWP PUnit.{u + 1} PUnit.{u + 1}) (fun _ _ _ _ => False) Q
        (divergingLoop heartbeat PUnit.unit) PUnit.unit ∧
      (∀ n, ¬ CoBuchi (obsIgnoreWP PUnit.{u + 1} PUnit.{u + 1})
        (fun _ _ _ _ => False) Q
        (iterChain n (fun a => Sum.inl <$> heartbeat a) PUnit.unit) PUnit.unit) ∧
      ¬ (CoBuchi (obsIgnoreWP PUnit.{u + 1} PUnit.{u + 1}) (fun _ _ _ _ => False) Q
            (divergingLoop heartbeat PUnit.unit) PUnit.unit ↔
          ∀ n, CoBuchi (obsIgnoreWP PUnit.{u + 1} PUnit.{u + 1})
            (fun _ _ _ _ => False) Q
            (iterChain n (fun a => Sum.inl <$> heartbeat a) PUnit.unit) PUnit.unit) ∧
      ¬ (CoBuchi (obsIgnoreWP PUnit.{u + 1} PUnit.{u + 1}) (fun _ _ _ _ => False) Q
            (divergingLoop heartbeat PUnit.unit) PUnit.unit ↔
          ∃ n, CoBuchi (obsIgnoreWP PUnit.{u + 1} PUnit.{u + 1})
            (fun _ _ _ _ => False) Q
            (iterChain n (fun a => Sum.inl <$> heartbeat a) PUnit.unit) PUnit.unit) := by
  have h_yes : CoBuchi (obsIgnoreWP PUnit.{u + 1} PUnit.{u + 1}) (fun _ _ _ _ => False) Q
      (divergingLoop heartbeat PUnit.unit) PUnit.unit :=
    (coBuchi_false_iff _ Q _ PUnit.unit).2 (infOften_heartbeat_not_chain_continuous Q).1
  have h_no : ∀ n, ¬ CoBuchi (obsIgnoreWP PUnit.{u + 1} PUnit.{u + 1})
      (fun _ _ _ _ => False) Q
      (iterChain n (fun a => Sum.inl <$> heartbeat a) PUnit.unit) PUnit.unit := fun n =>
    not_fairInfOften_iterChain_divergingLoop heartbeat (fun _ _ => True)
      (fun _ _ _ => DWP.vis (DWP.ret trivial)) Q n trivial
  exact ⟨h_yes, h_no, fun h => h_no 0 (h.1 h_yes 0), fun h => (h.1 h_yes).elim h_no⟩

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

/--
A reactive loop body over `ObsE Bool` that emits `true` (accepting) for `k`
iterations (`k > 0`) and then permanently emits `false` (non-accepting stutter).
-/
def finiteAcceptBody : Nat → ITree (ObsE Bool) Nat
  | 0 => ITree.trigger (E := ObsE Bool) (ObsReq.emit false) >>= fun _ => ITree.ret 0
  | k + 1 => ITree.trigger (E := ObsE Bool) (ObsReq.emit true) >>= fun _ => ITree.ret k

/--
**Negative canary for loops that stop accepting after finitely many steps**:
for EVERY `k : Nat`, `divergingLoop finiteAcceptBody k` satisfies `Always` and
`DWLP` safety (it is productive and fault-free forever!), yet **refutes**
`InfOften` for `ObsReq.emit true` (because after `k` accepting emissions it
stutters forever on `false`).
-/
theorem finiteAccept_always_and_not_infOften (k : Nat)
    (Q : PEmpty.{1} → PUnit.{1} → Prop) :
    Always (obsIgnoreWP PUnit.{1} Bool) (fun _ => True) Q
        (divergingLoop finiteAcceptBody k) PUnit.unit ∧
      ¬ InfOften (obsIgnoreWP PUnit.{1} Bool)
        (fun i _ _ _ => i = ObsReq.emit true) Q
        (divergingLoop finiteAcceptBody k) PUnit.unit := by
  have h_safe : Always (obsIgnoreWP PUnit.{1} Bool) (fun _ => True) Q
      (divergingLoop finiteAcceptBody k) PUnit.unit := by
    refine always_divergingLoop finiteAcceptBody (fun _ _ => True) ?_ trivial Q
    intro m _ _
    cases m with
    | zero =>
      refine Always.bind (Always.vis trivial ?_)
      exact Always.ret trivial (Always.ret trivial trivial)
    | succ m' =>
      refine Always.bind (Always.vis trivial ?_)
      exact Always.ret trivial (Always.ret trivial trivial)
  have h_zero_no : AlwaysStep (obsIgnoreWP PUnit.{1} Bool)
      (fun i _ _ _ => i ≠ ObsReq.emit true) (fun r _ => ¬ Q r PUnit.unit)
      (divergingLoop finiteAcceptBody 0) PUnit.unit := by
    refine AlwaysStep.iter_invariant _ (fun m _ => m = 0) ?_ rfl
    intro m _ hm
    subst hm
    have h_map : (Sum.inl <$> finiteAcceptBody 0 : ITree (ObsE Bool) (Nat ⊕ PEmpty.{1})) =
        (ITree.trigger (E := ObsE Bool) (ObsReq.emit false) >>= fun _ =>
          ITree.ret (Sum.inl 0)) := by
      show ((ITree.trigger (E := ObsE Bool) (ObsReq.emit false) >>= fun _ => ITree.ret 0) >>=
        fun a => ITree.ret (Sum.inl a)) = _
      rw [bind_assoc_itree]
      exact congrArg _ (funext fun _ => ret_bind _ _)
    rw [h_map]
    refine AlwaysStep.bind (AlwaysStep.vis ?_)
    exact ⟨fun h => Bool.noConfusion (ObsReq.emit.inj h),
      AlwaysStep.ret (AlwaysStep.ret rfl)⟩
  have h_not_io : ∀ n, ¬ InfOften (obsIgnoreWP PUnit.{1} Bool)
      (fun i _ _ _ => i = ObsReq.emit true) Q
      (divergingLoop finiteAcceptBody n) PUnit.unit := by
    intro n
    induction n with
    | zero => exact not_infOften_of_alwaysStep_not_accept h_zero_no
    | succ n ih =>
      intro h
      unfold divergingLoop at h
      rw [iter_unfold, InfOften.bind_iff] at h
      have h_map : (Sum.inl <$> finiteAcceptBody (n + 1) :
            ITree (ObsE Bool) (Nat ⊕ PEmpty.{1})) =
          ((ITree.trigger (E := ObsE Bool) (ObsReq.emit true) >>= fun _ => ITree.ret n) >>=
            fun a => ITree.ret (Sum.inl a)) := rfl
      rw [h_map, InfOften.bind_iff, InfOften.bind_iff] at h
      have h1 := (InfOften.vis_iff (E := ObsE Bool) _ _ _
        (ObsReq.emit true : (ObsE Bool).I) ITree.ret PUnit.unit).1 h
      have h2 := (InfOften.ret_iff _ _ _ _ _).1 h1
      have h3 := (InfOften.ret_iff _ _ _ _ _).1 h2
      have h4 := (InfOften.ret_iff _ _ _ _ _).1 h3
      exact ih ((InfOften.tau_iff _ _ _ _ _).1 h4)
  exact ⟨h_safe, h_not_io k⟩

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

/-! ## 5. Episode-2 Template: `Atomic::try_update` Under Fairness With History -/

section TryUpdate

/-!
An end-to-end template for `creusot#2386` `Atomic::try_update` style proofs:
a thread repeatedly loads an atomic cell (the environment may have changed it)
and attempts a CAS that the environment may refuse. The logical state is the
history of values this thread has published. The loop is proved

* transition-safe: the history only grows (`AlwaysStep` with `List.IsPrefix`);
* live under fairness: if the environment lets a CAS through infinitely often,
  the loop returns a value `v` whose update `f v` was the last published write
  (`FairInfOften`, via `FairInfOften.iter_fair`);
* not totally correct (`¬ DWP`): an adversarial environment may refuse forever.
-/

/-- Requests of an atomic cell observed by one thread. -/
inductive TryReq : Type where
  /-- Read the current value (chosen by the environment). -/
  | load
  /-- Compare-and-swap `expected ↦ new`; the environment reports success. -/
  | cas (expected new : Nat)

/-- Answers: a load returns the current value, a CAS reports success. -/
def TryAns : TryReq → Type
  | .load => Nat
  | .cas _ _ => Bool

/-- The atomic-cell effect. -/
abbrev TryE : Effect.{0} := CallE TryReq TryAns

/--
Demonic environment over the published history: a load may return any value,
and a CAS may fail (history unchanged) or succeed (`new` is published).
-/
def tryWP : StateEffectWP (List Nat) TryE where
  wp
    | .call .load, K, h => ∀ v : Nat, K v h
    | .call (.cas _ n), K, h => K false h ∧ K true (h ++ [n])
  mono {i} _ _ _ hPQ hw :=
    match i with
    | .call .load => fun v => hPQ v _ (hw v)
    | .call (.cas _ _) => ⟨hPQ false _ hw.1, hPQ true _ hw.2⟩

instance : StateEffectWP.Conjunctive tryWP where
  conj {i} _ _ _ hp hq :=
    match i with
    | .call .load => fun v => ⟨hp v, hq v⟩
    | .call (.cas _ _) => ⟨⟨hp.1, hq.1⟩, ⟨hp.2, hq.2⟩⟩

/-- The load request. -/
def tryLoad : TryE.I := .call .load

/-- The CAS request. -/
def tryCas (expected new : Nat) : TryE.I := .call (.cas expected new)

/-- Decode a loaded value. -/
def tryVal (o : TryE.O tryLoad) : Nat := o

/-- Decode a CAS outcome. -/
def tryOk (expected new : Nat) (o : TryE.O (tryCas expected new)) : Bool := o

/-- Fair edges: CAS attempts that the environment lets through. -/
def tryFair : (i : TryE.I) → TryE.O i → List Nat → List Nat → Prop
  | .call .load, _, _, _ => False
  | .call (.cas _ _), b, _, _ => b = true

/-- History monotonicity: every step extends the published history. -/
def tryHist : (i : TryE.I) → TryE.O i → List Nat → List Nat → Prop :=
  fun _ _ h h' => h <+: h'

/-- On return with `v`, the last published write is `f v`. -/
def tryPost (f : Nat → Nat) : Nat → List Nat → Prop :=
  fun v h => ∃ h₀, h = h₀ ++ [f v]

/-- Body continuation after the CAS: exit with the loaded value on success. -/
def tryCasK (f : Nat → Nat) (v : Nat) (o : TryE.O (tryCas v (f v))) :
    ITree TryE (PUnit.{1} ⊕ Nat) :=
  ITree.ret (if tryOk v (f v) o then Sum.inr v else Sum.inl PUnit.unit)

/-- Body continuation after the load: attempt `v ↦ f v`. -/
def tryLoadK (f : Nat → Nat) (o : TryE.O tryLoad) : ITree TryE (PUnit.{1} ⊕ Nat) :=
  ITree.vis (tryCas (tryVal o) (f (tryVal o))) (tryCasK f (tryVal o))

/-- One `try_update` attempt. -/
def tryBody (f : Nat → Nat) (_ : PUnit.{1}) : ITree TryE (PUnit.{1} ⊕ Nat) :=
  ITree.vis tryLoad (tryLoadK f)

/-- `loop { let v = load(); if cas(v, f v) { return v } }`. -/
def tryUpdate (f : Nat → Nat) : ITree TryE Nat :=
  ITree.iter (tryBody f) PUnit.unit

/-- Unfolded continuation of `tryUpdate` after the CAS. -/
def tryAfterCas (f : Nat → Nat) (v : Nat) (o : TryE.O (tryCas v (f v))) :
    ITree TryE Nat :=
  if tryOk v (f v) o then ITree.ret v else ITree.tau (tryUpdate f)

/-- Unfolded continuation of `tryUpdate` after the load. -/
def tryAfterLoad (f : Nat → Nat) (v : Nat) : ITree TryE Nat :=
  ITree.vis (tryCas v (f v)) (tryAfterCas f v)

theorem tryUpdate_eq (f : Nat → Nat) :
    tryUpdate f = ITree.vis tryLoad (fun o => tryAfterLoad f (tryVal o)) := by
  refine (iter_unfold (tryBody f) PUnit.unit).trans ?_
  refine (vis_bind tryLoad (tryLoadK f) _).trans ?_
  refine congrArg (ITree.vis tryLoad) (funext fun o => ?_)
  refine (vis_bind _ (tryCasK f (tryVal o)) _).trans ?_
  refine congrArg (ITree.vis (tryCas (tryVal o) (f (tryVal o)))) (funext fun b => ?_)
  cases b
  · exact (ret_bind (E := TryE) (Sum.inl PUnit.unit) _).trans rfl
  · exact (ret_bind (E := TryE) (Sum.inr (tryVal o)) _).trans rfl

/-- **Safety**: `try_update` only ever extends the published history. -/
theorem tryUpdate_history_monotone (f : Nat → Nat) (h₀ : List Nat) :
    AlwaysStep tryWP tryHist (fun _ _ => True) (tryUpdate f) h₀ := by
  refine AlwaysStep.iter_invariant (tryBody f) (fun _ _ => True) ?_ trivial
  intro a h _
  refine (AlwaysStep.vis_iff _ _ _ tryLoad (tryLoadK f) h).2 ?_
  intro v
  refine ⟨List.prefix_refl h, ?_⟩
  refine (AlwaysStep.vis_iff _ _ _ (tryCas v (f v)) (tryCasK f v) h).2 ?_
  refine ⟨⟨List.prefix_refl h, ?_⟩, ⟨List.prefix_append h [f v], ?_⟩⟩
  · exact (AlwaysStep.ret_iff _ _ _ (Sum.inl PUnit.unit) h).2 trivial
  · exact (AlwaysStep.ret_iff _ _ _ (Sum.inr v) (h ++ [f v])).2 trivial

/--
**Liveness under fairness**: on every path along which the environment lets a
CAS through infinitely often, `try_update` returns `v` with `f v` as the last
published write.
-/
theorem tryUpdate_fairInfOften (f : Nat → Nat) (h₀ : List Nat) :
    FairInfOften tryWP (fun _ _ _ _ => False) tryFair (tryPost f)
      (tryUpdate f) h₀ := by
  refine FairInfOften.iter_fair (tryBody f) (fun _ _ => True) ?_ trivial
  intro a h _
  refine (fairIter.vis_iff _ _ _ _ false tryLoad (tryLoadK f) h).2 ?_
  intro v
  refine Or.inr ⟨fun hf => hf, ?_⟩
  refine (fairIter.vis_iff _ _ _ _ true (tryCas v (f v)) (tryCasK f v) h).2 ?_
  refine ⟨Or.inr ⟨fun hf => Bool.noConfusion hf, ?_⟩, Or.inl ⟨rfl, ?_⟩⟩
  · exact (fairIter.ret_inl_iff tryWP tryFair (fun _ _ => True) (tryPost f) true
      PUnit.unit h).2 ⟨rfl, trivial⟩
  · exact DWP.ret ⟨h, rfl⟩

/-- **No total correctness**: the environment may refuse every CAS. -/
theorem not_dwp_tryUpdate (f : Nat → Nat) (Q : Nat → List Nat → Prop)
    (h₀ : List Nat) : ¬ DWP tryWP (tryUpdate f) Q h₀ := by
  have hobs : (tryUpdate f).observe =
      .vis tryLoad (fun o => tryAfterLoad f (tryVal o)) := by
    conv => lhs; rw [tryUpdate_eq]
    exact ITree.observe_vis _ _
  have hobs' : ∀ v, (tryAfterLoad f v).observe =
      .vis (tryCas v (f v)) (tryAfterCas f v) :=
    fun _ => ITree.observe_vis _ _
  intro h
  refine DWP.induct
    (fun x _ => (x = tryUpdate f ∨ x = ITree.tau (tryUpdate f) ∨
      ∃ v, x = tryAfterLoad f v) → False) ?_ h (Or.inl rfl)
  intro x s₀ hx hx_eq
  rcases hx_eq with rfl | rfl | ⟨v, rfl⟩
  · rw [hobs] at hx
    exact hx 0 (Or.inr (Or.inr ⟨_, rfl⟩))
  · rw [ITree.observe_tau] at hx
    exact hx (Or.inl rfl)
  · rw [hobs'] at hx
    exact hx.1 (Or.inr (Or.inl rfl))

/--
**`try_update` specification**: fairness-conditional liveness along the
history-monotone (step-guarded) environment, and no total correctness.
-/
theorem tryUpdate_spec (f : Nat → Nat) (h₀ : List Nat) :
    FairInfOften (guardStepWP tryWP tryHist) (fun _ _ _ _ => False) tryFair
        (tryPost f) (tryUpdate f) h₀ ∧
      ¬ DWP tryWP (tryUpdate f) (tryPost f) h₀ :=
  ⟨FairInfOften.guardStep_of_alwaysStep (tryUpdate_history_monotone f h₀)
     (tryUpdate_fairInfOften f h₀),
   not_dwp_tryUpdate f _ h₀⟩

/-- `ExcludedMiracle` for `tryWP`: every request has an admissible answer. -/
instance : StateEffectWP.ExcludedMiracle tryWP where
  no_miracle {i} _ h :=
    match i with
    | .call .load => h 0
    | .call (.cas _ _) => h.1

/-- Program-enabling edge predicate: a CAS is actually attempted (succeeding or failing). -/
def tryAttemptCas : (i : TryE.I) → TryE.O i → List Nat → List Nat → Prop
  | .call .load, _, _, _ => False
  | .call (.cas _ _), _, _, _ => True

/--
**Non-vacuous CAS enabling**: every non-terminating path of `tryUpdate f`
genuinely attempts CAS infinitely often (`InfOften tryWP tryAttemptCas`),
ruling out silent spin and load-spinning.
-/
theorem tryUpdate_infOften_attemptCas (f : Nat → Nat) (h₀ : List Nat) :
    InfOften tryWP tryAttemptCas (tryPost f) (tryUpdate f) h₀ := by
  refine InfOften.iter_progress (tryBody f) (fun _ _ => True) ?_ trivial
  intro a h _
  refine (buchiProgress.vis_iff _ _ _ _ tryLoad (tryLoadK f) h).2 ?_
  intro v
  refine Or.inr ?_
  refine (buchiProgress.vis_iff _ _ _ _ (tryCas v (f v)) (tryCasK f v) h).2 ?_
  refine ⟨Or.inl ⟨trivial, (InfOften.ret_iff _ _ _ _ _).2 trivial⟩,
    Or.inl ⟨trivial, (InfOften.ret_iff _ _ _ _ _).2 ⟨h, rfl⟩⟩⟩

/-- Load-spinning buggy loop body: only issues `load`, never attempts CAS. -/
def loadSpinBody (_ : PUnit.{1}) : ITree TryE (PUnit.{1} ⊕ Nat) :=
  ITree.vis tryLoad (fun _ => ITree.ret (Sum.inl PUnit.unit))

/-- Buggy load-spinning loop `loop { let _ = load(); }`. -/
def loadSpin : ITree TryE Nat :=
  ITree.iter loadSpinBody PUnit.unit

/--
**Vacuity witness (`loadSpin`)**: a load-spinning loop preserves history
monotonicity and satisfies `FairInfOften tryWP False tryFair` *vacuously* (by
`FairInfOften.of_never_fair`), yet **refutes** `InfOften tryWP tryAttemptCas`.
-/
theorem loadSpin_vacuous_but_refutes_attemptCas (f : Nat → Nat) (h₀ : List Nat) :
    AlwaysStep tryWP tryHist (fun _ _ => True) loadSpin h₀ ∧
      FairInfOften tryWP (fun _ _ _ _ => False) tryFair (tryPost f) loadSpin h₀ ∧
      ¬ InfOften tryWP tryAttemptCas (tryPost f) loadSpin h₀ := by
  have h_hist : AlwaysStep tryWP tryHist (fun _ _ => True) loadSpin h₀ := by
    refine AlwaysStep.iter_invariant loadSpinBody (fun _ _ => True) ?_ trivial
    intro _ h _
    refine (AlwaysStep.vis_iff _ _ _ tryLoad _ h).2 fun _ =>
      ⟨List.prefix_refl h, (AlwaysStep.ret_iff _ _ _ _ _).2 trivial⟩
  have h_no_cas : AlwaysStep tryWP (fun i o h₁ h₂ => ¬ tryAttemptCas i o h₁ h₂)
      (fun r h => ¬ tryPost f r h) loadSpin h₀ := by
    refine AlwaysStep.iter_invariant loadSpinBody (fun _ _ => True) ?_ trivial
    intro _ h _
    refine (AlwaysStep.vis_iff _ _ _ tryLoad _ h).2 fun _ =>
      ⟨fun hf => hf, (AlwaysStep.ret_iff _ _ _ _ _).2 trivial⟩
  have h_no_fair : AlwaysStep tryWP (fun i o h₁ h₂ => ¬ tryFair i o h₁ h₂)
      (fun _ _ => True) loadSpin h₀ := by
    refine AlwaysStep.iter_invariant loadSpinBody (fun _ _ => True) ?_ trivial
    intro _ h _
    refine (AlwaysStep.vis_iff _ _ _ tryLoad _ h).2 fun _ =>
      ⟨fun hf => hf, (AlwaysStep.ret_iff _ _ _ _ _).2 trivial⟩
  have h_prod : InfOften tryWP (fun _ _ _ _ => True) (tryPost f) loadSpin h₀ := by
    refine InfOften.iter_progress loadSpinBody (fun _ _ => True) ?_ trivial
    intro _ h _
    refine (buchiProgress.vis_iff _ _ _ _ tryLoad _ h).2 fun _ =>
      Or.inl ⟨trivial, (InfOften.ret_iff _ _ _ _ _).2 trivial⟩
  exact ⟨h_hist, FairInfOften.of_never_fair h_no_fair h_prod,
    not_infOften_of_alwaysStep_not_accept h_no_cas⟩

/-- CAS-ignoring loop continuation: executes CAS then retries regardless of result. -/
def tryIgnoreCasK (f : Nat → Nat) (v : Nat) (_ : TryE.O (tryCas v (f v))) :
    ITree TryE (PUnit.{1} ⊕ Nat) :=
  ITree.ret (Sum.inl PUnit.unit)

/-- CAS-ignoring loop body after load. -/
def tryIgnoreLoadK (f : Nat → Nat) (o : TryE.O tryLoad) : ITree TryE (PUnit.{1} ⊕ Nat) :=
  ITree.vis (tryCas (tryVal o) (f (tryVal o))) (tryIgnoreCasK f (tryVal o))

/-- CAS-ignoring loop body: `load(); let _ = cas(v, f v); retry`. -/
def tryIgnoreBody (f : Nat → Nat) (_ : PUnit.{1}) : ITree TryE (PUnit.{1} ⊕ Nat) :=
  ITree.vis tryLoad (tryIgnoreLoadK f)

/-- CAS-ignoring loop `loop { let v = load(); let _ = cas(v, f v); }`. -/
def tryIgnoreCas (f : Nat → Nat) : ITree TryE Nat :=
  ITree.iter (tryIgnoreBody f) PUnit.unit

/-- Unfolded continuation of `tryIgnoreCas` after the load. -/
def tryIgnoreAfterLoad (f : Nat → Nat) (v : Nat) : ITree TryE Nat :=
  ITree.vis (tryCas v (f v)) (fun _ => ITree.tau (tryIgnoreCas f))

private theorem tryIgnoreCas_eq (f : Nat → Nat) :
    tryIgnoreCas f = ITree.vis tryLoad (fun o => tryIgnoreAfterLoad f (tryVal o)) := by
  refine (iter_unfold (tryIgnoreBody f) PUnit.unit).trans ?_
  refine (vis_bind tryLoad (tryIgnoreLoadK f) _).trans ?_
  refine congrArg (ITree.vis tryLoad) (funext fun o => ?_)
  refine (vis_bind _ (tryIgnoreCasK f (tryVal o)) _).trans ?_
  refine congrArg (ITree.vis (tryCas (tryVal o) (f (tryVal o)))) (funext fun _ => ?_)
  exact (ret_bind (E := TryE) (Sum.inl PUnit.unit) _).trans rfl

/--
**Non-termination canary (`tryIgnoreCas`)**: attempts CAS infinitely often
(`InfOften tryWP tryAttemptCas`) while preserving history monotonicity, yet
**refutes** `FairInfOften tryWP False tryFair` (even when every CAS succeeds!).
-/
theorem tryIgnoreCas_attempts_but_refutes_fair (f : Nat → Nat) (h₀ : List Nat) :
    AlwaysStep tryWP tryHist (fun _ _ => True) (tryIgnoreCas f) h₀ ∧
      InfOften tryWP tryAttemptCas (tryPost f) (tryIgnoreCas f) h₀ ∧
      ¬ FairInfOften tryWP (fun _ _ _ _ => False) tryFair (tryPost f)
        (tryIgnoreCas f) h₀ := by
  have h_hist : AlwaysStep tryWP tryHist (fun _ _ => True) (tryIgnoreCas f) h₀ := by
    refine AlwaysStep.iter_invariant (tryIgnoreBody f) (fun _ _ => True) ?_ trivial
    intro _ h _
    refine (AlwaysStep.vis_iff _ _ _ tryLoad (tryIgnoreLoadK f) h).2 fun v =>
      ⟨List.prefix_refl h, ?_⟩
    refine (AlwaysStep.vis_iff _ _ _ (tryCas v (f v)) (tryIgnoreCasK f v) h).2
      ⟨⟨List.prefix_refl h, (AlwaysStep.ret_iff _ _ _ _ _).2 trivial⟩,
       ⟨List.prefix_append h [f v], (AlwaysStep.ret_iff _ _ _ _ _).2 trivial⟩⟩
  have h_att : InfOften tryWP tryAttemptCas (tryPost f) (tryIgnoreCas f) h₀ := by
    refine InfOften.iter_progress (tryIgnoreBody f) (fun _ _ => True) ?_ trivial
    intro _ h _
    refine (buchiProgress.vis_iff _ _ _ _ tryLoad (tryIgnoreLoadK f) h).2 fun v => Or.inr ?_
    refine (buchiProgress.vis_iff _ _ _ _ (tryCas v (f v)) (tryIgnoreCasK f v) h).2
      ⟨Or.inl ⟨trivial, (InfOften.ret_iff _ _ _ _ _).2 trivial⟩,
       Or.inl ⟨trivial, (InfOften.ret_iff _ _ _ _ _).2 trivial⟩⟩
  have h_not_fair : ¬ FairInfOften tryWP (fun _ _ _ _ => False) tryFair (tryPost f)
      (tryIgnoreCas f) h₀ := by
    have hobs : (tryIgnoreCas f).observe =
        .vis tryLoad (fun o => tryIgnoreAfterLoad f (tryVal o)) := by
      conv => lhs; rw [tryIgnoreCas_eq]
      exact ITree.observe_vis _ _
    have hobs' : ∀ v, (tryIgnoreAfterLoad f v).observe =
        .vis (tryCas v (f v)) (fun _ => ITree.tau (tryIgnoreCas f)) :=
      fun _ => ITree.observe_vis _ _
    intro h
    rw [FairInfOften.unfold_eq] at h
    refine fairProgress.induct
      (fun x _ => (x = tryIgnoreCas f ∨ x = ITree.tau (tryIgnoreCas f) ∨
        ∃ v, x = tryIgnoreAfterLoad f v) → False) ?_ h (Or.inl rfl)
    intro x s₀ hx hx_eq
    rw [fairStall.unfold_eq] at hx
    refine fairStep.induct
      (fun y _ => (y = tryIgnoreCas f ∨ y = ITree.tau (tryIgnoreCas f) ∨
        ∃ v, y = tryIgnoreAfterLoad f v) → False) ?_ hx hx_eq
    intro y s₁ hy hy_eq
    rcases hy_eq with rfl | rfl | ⟨v, rfl⟩
    · rw [hobs] at hy
      rcases hy 0 with ⟨hf, _⟩ | ⟨hf, _⟩ | ⟨_, hst⟩
      · exact hf
      · exact hf
      · rw [fairStall.unfold_eq] at hst
        refine fairStep.induct
          (fun z _ => z = tryIgnoreAfterLoad f 0 → False) ?_ hst rfl
        intro z _ hz hzeq
        subst hzeq
        rw [hobs'] at hz
        rcases hz.2 with ⟨hf, _⟩ | ⟨_, hpre⟩ | ⟨hnf, _⟩
        · exact hf
        · exact hpre (Or.inr (Or.inl rfl))
        · exact hnf rfl
    · rw [ITree.observe_tau] at hy
      exact hy (Or.inl rfl)
    · rw [hobs'] at hy
      rcases hy.2 with ⟨hf, _⟩ | ⟨_, hpre⟩ | ⟨hnf, _⟩
      · exact hf
      · exact hpre (Or.inr (Or.inl rfl))
      · exact hnf rfl
  exact ⟨h_hist, h_att, h_not_fair⟩

/--
**Three-way strong-fairness separation for `tryUpdate`**: combining `AlwaysStep`
history monotonicity, non-vacuous CAS enabling (`InfOften tryAttemptCas`), and
fair termination (`FairInfOften False tryFair`) uniquely separates `tryUpdate f`
from BOTH `loadSpin` (vacuously fair, fails `InfOften tryAttemptCas`) and
`tryIgnoreCas` (attempts CAS infinitely often, fails `FairInfOften False tryFair`),
while still refuting unconditional `DWP`.
-/
theorem tryUpdate_strong_separation (f : Nat → Nat) (h₀ : List Nat) :
    (AlwaysStep tryWP tryHist (fun _ _ => True) (tryUpdate f) h₀ ∧
      InfOften tryWP tryAttemptCas (tryPost f) (tryUpdate f) h₀ ∧
      FairInfOften (guardStepWP tryWP tryHist) (fun _ _ _ _ => False) tryFair
        (tryPost f) (tryUpdate f) h₀ ∧
      ¬ DWP tryWP (tryUpdate f) (tryPost f) h₀) ∧
    (FairInfOften tryWP (fun _ _ _ _ => False) tryFair (tryPost f) loadSpin h₀ ∧
      ¬ InfOften tryWP tryAttemptCas (tryPost f) loadSpin h₀) ∧
    (InfOften tryWP tryAttemptCas (tryPost f) (tryIgnoreCas f) h₀ ∧
      ¬ FairInfOften tryWP (fun _ _ _ _ => False) tryFair (tryPost f)
        (tryIgnoreCas f) h₀) :=
  ⟨⟨tryUpdate_history_monotone f h₀, tryUpdate_infOften_attemptCas f h₀,
    (tryUpdate_spec f h₀).1, (tryUpdate_spec f h₀).2⟩,
   ⟨(loadSpin_vacuous_but_refutes_attemptCas f h₀).2.1,
    (loadSpin_vacuous_but_refutes_attemptCas f h₀).2.2⟩,
   ⟨(tryIgnoreCas_attempts_but_refutes_fair f h₀).2.1,
    (tryIgnoreCas_attempts_but_refutes_fair f h₀).2.2⟩⟩

/--
**One-shot `Committer` ghost monitor (`creusot#2386` preview)**: `QState := Bool`
tracks whether the one-shot committer has fired (`false` = unshot, `true` = shot).
The monitor enforces that (i) `h₀ <+: h` holds at every step, (ii) a winning CAS
may fire **at most once** (`q = false ∧ q' = true`), and (iii) any return exits
with `q = true ∧ tryPost f v h`.
-/
def tryCommitterSpec (f : Nat → Nat) (h₀ : List Nat) :
    BuchiSpec (List Nat) Bool TryE Nat where
  ewp := tryWP
  step q i o _ _ q' :=
    match i, o with
    | .call .load, _ => q' = q
    | .call (.cas _ _), false => q' = q
    | .call (.cas _ _), true => q = false ∧ q' = true
  accept _ _ _ _ _ _ := False
  inv _ h := h₀ <+: h
  terminal q v h := q = true ∧ tryPost f v h

/--
**Monitor-verified `FairBuchiSat` witness for `tryUpdate`**: proves invariant
`h₀ <+: h`, one-shot committer protocol (`shot : false ↦ true` at most once),
and fair termination with `shot = true ∧ tryPost f v h`.
-/
theorem tryUpdate_fairBuchiSat_committer (f : Nat → Nat) (h₀ : List Nat) :
    FairBuchiSat (tryCommitterSpec f h₀)
      (fun _ i o h h' _ => tryFair i o h h') (tryUpdate f) false h₀ := by
  let spec := tryCommitterSpec f h₀
  let fairQ : Bool → (i : TryE.I) → TryE.O i → List Nat → List Nat → Bool → Prop :=
    fun _ i o h h' _ => tryFair i o h h'
  refine (fairBuchiSat_iff_fairInfOften spec fairQ (tryUpdate f) false h₀).2
    ⟨List.prefix_refl h₀, ?_⟩
  refine FairInfOften.iter_fair (tryBody f)
    (fun _ qs => qs.1 = false ∧ h₀ <+: qs.2) ?_ ⟨rfl, List.prefix_refl h₀⟩
  rintro _ ⟨q, h⟩ ⟨hq, hpref⟩
  subst hq
  refine (fairIter.vis_iff _ _ _ _ false tryLoad (tryLoadK f) (false, h)).2 ?_
  intro v
  refine ⟨false, rfl, hpref, Or.inr ⟨fun hf => hf, ?_⟩⟩
  refine (fairIter.vis_iff _ _ _ _ true (tryCas v (f v)) (tryCasK f v) (false, h)).2 ?_
  refine ⟨⟨false, rfl, hpref, Or.inr ⟨fun hf => Bool.noConfusion hf, ?_⟩⟩,
    ⟨true, ⟨rfl, rfl⟩, List.IsPrefix.trans hpref (List.prefix_append h [f v]),
      Or.inl ⟨rfl, DWP.ret ⟨rfl, h, rfl⟩⟩⟩⟩
  exact (fairIter.ret_inl_iff spec.monitorWP (spec.fairEdge fairQ)
    (fun _ qs => qs.1 = false ∧ h₀ <+: qs.2) spec.terminalPost true
    PUnit.unit (false, h)).2 ⟨rfl, rfl, hpref⟩

/-- Lower-level effect: an observation tick (load) plus a boolean CAS oracle carrying `new`. -/
abbrev TryLowE : Effect.{0} := SumE (ObsE PUnit.{1}) (CallE Nat (fun _ => Bool))

/-- Lower-level transformer tracking ghost published history `S₂ := List Nat`. -/
def tryLowWP : StateEffectWP (List Nat) TryLowE where
  wp
    | .inl (.emit _), K, h => K PUnit.unit h
    | .inr (.call n), K, h => K false h ∧ K true (h ++ [n])
  mono {i} _ _ _ hPQ hw :=
    match i with
    | .inl (.emit _) => hPQ PUnit.unit _ hw
    | .inr (.call _) => ⟨hPQ false _ hw.1, hPQ true _ hw.2⟩

/-- Lower-level fairness predicate: the CAS oracle answers `true`. -/
def tryLowFair : (j : TryLowE.I) → TryLowE.O j → List Nat → List Nat → Prop
  | .inl _, _, _, _ => False
  | .inr (.call _), b, _, _ => b = true

/--
Concrete stateful cell handler lowering `TryE` to `TryLowE` with threaded
concrete cell value `H := Nat` (each load emits a visible tick and reads `c`;
each CAS queries the lower oracle and updates `c ↦ n` on success).
-/
def tryCellHandler : (i : TryE.I) → Nat → ITree TryLowE (TryE.O i × Nat)
  | .call .load, c =>
    ITree.vis (Sum.inl (ObsReq.emit PUnit.unit) : TryLowE.I) (fun _ => ITree.ret (c, c))
  | .call (.cas _ n), c =>
    ITree.vis (Sum.inr (CallReq.call n) : TryLowE.I)
      (fun b => ITree.ret (b, match (b : Bool) with | true => n | false => c))

/--
**End-to-end `FairInfOften.interpState_stateful` lowering witness**: transports
`tryUpdate_fairInfOften` across `ITree.interpState tryCellHandler (tryUpdate f) c₀`,
threading concrete cell state `H := Nat` while preserving ghost published
history `S₂ := List Nat` on the target transformer `tryLowWP`.
-/
theorem tryUpdate_interpState_stateful (f : Nat → Nat) (h₀ : List Nat) (c₀ : Nat) :
    FairInfOften tryLowWP (fun _ _ _ _ => False) tryLowFair
      (fun pair h => tryPost f pair.1 h)
      (ITree.interpState tryCellHandler (tryUpdate f) c₀) h₀ := by
  let liftTryWP : StateEffectWP (List Nat × Nat) TryE :=
    { wp := fun i K p =>
        match i with
        | .call .load => ∀ v : Nat, K v (p.1, p.2)
        | .call (.cas _ n) => K false (p.1, p.2) ∧ K true (p.1 ++ [n], n)
      mono := fun {i} _ _ _ hPQ hw =>
        match i with
        | .call .load => fun v => hPQ v _ (hw v)
        | .call (.cas _ _) => ⟨hPQ false _ hw.1, hPQ true _ hw.2⟩ }
  let liftFair : (i : TryE.I) → TryE.O i → List Nat × Nat → List Nat × Nat → Prop :=
    fun i o p₁ p₂ => tryFair i o p₁.1 p₂.1
  have h_src : FairInfOften liftTryWP (fun _ _ _ _ => False) liftFair
      (fun v p => tryPost f v p.1) (tryUpdate f) (h₀, c₀) := by
    refine FairInfOften.iter_fair (tryBody f) (fun _ _ => True) ?_ trivial
    rintro _ ⟨h, c⟩ _
    refine (fairIter.vis_iff _ _ _ _ false tryLoad (tryLoadK f) (h, c)).2 fun v =>
      Or.inr ⟨fun hf => hf, ?_⟩
    refine (fairIter.vis_iff _ _ _ _ true (tryCas v (f v)) (tryCasK f v) (h, c)).2
      ⟨Or.inr ⟨fun hf => Bool.noConfusion hf, ?_⟩, Or.inl ⟨rfl, DWP.ret ⟨h, rfl⟩⟩⟩
    exact (fairIter.ret_inl_iff liftTryWP liftFair (fun _ _ => True)
      (fun v p => tryPost f v p.1) true PUnit.unit (h, c)).2 ⟨rfl, trivial⟩
  refine FairInfOften.interpState_stateful (S₂ := List Nat) (H := Nat)
    (ewp₁ := liftTryWP) (ewp₂ := tryLowWP) tryCellHandler ?_ h_src
  intro i K4 K3 K2 h c hw
  cases i with
  | call req =>
    cases req with
    | load =>
      refine (fairStep.vis_iff (E := TryLowE) _ _ _ _ _ _ _
        (Sum.inl (ObsReq.emit PUnit.unit) : TryLowE.I) _ h).2 ?_
      rcases hw c with ⟨hf, _⟩ | ⟨hf, _⟩ | ⟨_, hk2⟩
      · exact False.elim hf
      · exact False.elim hf
      · refine Or.inr (Or.inr ⟨fun hf => hf, ?_⟩)
        rw [fairStall.unfold_eq, fairStep.ret_iff]
        exact Or.inr hk2
    | cas v n =>
      refine (fairStep.vis_iff (E := TryLowE) _ _ _ _ _ _ _
        (Sum.inr (CallReq.call n) : TryLowE.I) _ h).2 ?_
      refine ⟨?_, ?_⟩
      · rcases hw.1 with ⟨hf, _⟩ | ⟨hf, _⟩ | ⟨_, hk2⟩
        · exact False.elim hf
        · exact Bool.noConfusion hf
        · refine Or.inr (Or.inr ⟨fun hf => Bool.noConfusion hf, ?_⟩)
          rw [fairStall.unfold_eq, fairStep.ret_iff]
          exact Or.inr hk2
      · rcases hw.2 with ⟨hf, _⟩ | ⟨_, hk3⟩ | ⟨hnf, _⟩
        · exact False.elim hf
        · refine Or.inr (Or.inl ⟨rfl, ?_⟩)
          exact fairProgress.of_dwp _ (DWP.ret hk3)
        · exact False.elim (hnf rfl)

end TryUpdate

/-! ## 6. The Strict Temporal Hierarchy `DWP ⊊ InfOften ⊊ FairInfOften ⊊ DWLP` -/

section TemporalHierarchy

/--
**Capstone (inclusions).** For every transformer, accepting edges and fair
edges: total correctness implies Büchi recurrence, which implies
fairness-conditional (Streett) recurrence, which implies partial correctness.
-/
theorem temporal_hierarchy {S : Type u} {E : Effect.{u}} {R : Type u}
    (ewp : StateEffectWP S E) (AccEdge Fair : (i : E.I) → E.O i → S → S → Prop)
    (Q : R → S → Prop) (t : ITree E R) (s : S) :
    (DWP ewp t Q s → InfOften ewp AccEdge Q t s) ∧
      (InfOften ewp AccEdge Q t s → FairInfOften ewp AccEdge Fair Q t s) ∧
      (FairInfOften ewp AccEdge Fair Q t s → DWLP ewp t Q s) :=
  ⟨infOften_of_dwp AccEdge, InfOften.toFairInfOften Fair, FairInfOften.toDWLP⟩

/--
**Capstone (strictness).** Each inclusion of `temporal_hierarchy` is strict,
witnessed with the *same* accepting edges on both sides:

* the heartbeat service `loop { emit () }` is Büchi-recurrent (every emission
  accepting) but not totally correct;
* the CAS retry loop is fairness-conditionally live but not Büchi-recurrent
  without accepting edges;
* `ITree.spin` is partially correct but never fairness-conditionally live.
-/
theorem temporal_hierarchy_strict :
    (InfOften (obsIgnoreWP PUnit.{1} PUnit.{1}) (fun _ _ _ _ => True)
        (fun _ _ => True) (divergingLoop heartbeat.{0} PUnit.unit) PUnit.unit ∧
      ¬ DWP (obsIgnoreWP PUnit.{1} PUnit.{1})
        (divergingLoop heartbeat.{0} PUnit.unit) (fun _ _ => True) PUnit.unit) ∧
    (FairInfOften (pickWP PUnit.{1} Bool) (fun _ _ _ _ => False) casFair
        (fun _ _ => True) casLoop PUnit.unit ∧
      ¬ InfOften (pickWP PUnit.{1} Bool) (fun _ _ _ _ => False)
        (fun _ _ => True) casLoop PUnit.unit) ∧
    (DWLP (pickWP PUnit.{1} Bool) (ITree.spin (E := CasE) (R := PUnit.{1}))
        (fun _ _ => True) PUnit.unit ∧
      ¬ FairInfOften (pickWP PUnit.{1} Bool) (fun _ _ _ _ => False) casFair
        (fun _ _ => True) (ITree.spin (E := CasE) (R := PUnit.{1})) PUnit.unit) :=
  ⟨⟨(infOften_heartbeat_not_chain_continuous _).1,
    (infOften_heartbeat_not_chain_continuous _).2.2⟩,
   ⟨fairInfOften_strict_separation.1.1, fairInfOften_strict_separation.1.2.2⟩,
   ⟨DWLP.spin _ _ _, not_fairInfOften_spin⟩⟩

end TemporalHierarchy

end Anneal.ITreeBuchi
