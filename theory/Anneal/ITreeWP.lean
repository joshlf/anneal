import Std.Do
import Trusted
import Anneal.Refinement
import Anneal.Effect
import Anneal.ITree
import Anneal.EffectWP

namespace Anneal.ITreeWP

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Anneal.Refinement
open Anneal.Effect
open Anneal.ITree
open Anneal.EffectWP

/-!
Coinductive partial-correctness (`DWLP`) and inductive total-correctness (`DWP`)
Dijkstra predicate transformers over interaction trees (`ITree E R`), built
directly on Lean 4's `coinductive_fixpoint`, `inductive_fixpoint`, `Acc`, and
`Std.Do.WP` / `Std.Do.WPMonad` (`#100`, `#103`; cf. `AeneasVerif/aeneas#1180`,
`#1344`):

- **`DWLP`** (`coinductive_fixpoint`): greatest fixed point admitting silent
  divergence (`DWLP.spin`) and loop invariants (`DWLP.iter_invariant`) while
  guaranteeing all-prefix fault freedom (`TreeSafe`).
- **`DWP`** (`inductive_fixpoint`): least fixed point rejecting both faults and
  silent divergence (`DWP.spin_false`), enforcing `DWP.excludedMiracle`, and
  supporting well-founded (`Acc`) and `Nat`-ranked loop rules (`DWP.iter_acc`,
  `DWP.iter_ranked`) as well as computable bounded coalgebra evaluation
  (`wpCoalBounded`).
- **`Std.Do.WP` / `Std.Do.WPMonad`**: connects `DWLP` directly to Lean's
  standard Hoare-triple specification framework (`⦃P⦄ prog ⦃Q⦄`).
-/

universe u

/-! ## 1. Coinductive Partial-Correctness (`DWLP`) -/

private def dwlpAux {S : Type u} {E : Effect.{u}} {R : Type u}
    (ewp : StateEffectWP S E) (Q : R → S → Prop)
    (t : ITree E R) (s : S) : Prop :=
  match t.observe with
  | .ret r => Q r s
  | .tau t' => dwlpAux ewp Q t' s
  | .vis i k => ewp.wp i (fun o s' => dwlpAux ewp Q (k o) s') s
coinductive_fixpoint

/--
Coinductive Dijkstra Weakest Liberal Precondition ($\nu F$) over `t : ITree E R`
and logical state `s : S`.
-/
def DWLP {S : Type u} {E : Effect.{u}} {R : Type u}
    (ewp : StateEffectWP S E)
    (t : ITree E R) (Q : R → S → Prop) (s : S) : Prop :=
  dwlpAux ewp Q t s

theorem DWLP.unfold_eq {S : Type u} {E : Effect.{u}} {R : Type u}
    (ewp : StateEffectWP S E)
    (t : ITree E R) (Q : R → S → Prop) (s : S) :
    DWLP ewp t Q s =
      match t.observe with
      | .ret r => Q r s
      | .tau t' => DWLP ewp t' Q s
      | .vis i k => ewp.wp i (fun o s' => DWLP ewp (k o) Q s') s :=
  dwlpAux.eq_def ewp Q t s

/-- Park coinduction principle for `DWLP`. -/
theorem DWLP.coinduct {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {Q : R → S → Prop}
    (Inv : ITree E R → S → Prop)
    (h_step : ∀ x s₀, Inv x s₀ →
      match x.observe with
      | .ret r => Q r s₀
      | .tau x' => Inv x' s₀
      | .vis i k => ewp.wp i (fun o s' => Inv (k o) s') s₀)
    {t : ITree E R} {s : S} (h_init : Inv t s) :
    DWLP ewp t Q s :=
  dwlpAux.coinduct ewp Q Inv h_step t s h_init

@[simp]
theorem DWLP.ret_iff {S : Type u} {E : Effect.{u}} {R : Type u}
    (ewp : StateEffectWP S E) (r : R) (Q : R → S → Prop) (s : S) :
    DWLP ewp (.ret r) Q s ↔ Q r s := by
  conv => lhs; rw [DWLP.unfold_eq, ITree.observe_ret]

theorem DWLP.ret {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {r : R} {Q : R → S → Prop} {s : S}
    (hq : Q r s) : DWLP ewp (.ret r) Q s :=
  (DWLP.ret_iff ewp r Q s).2 hq

@[simp]
theorem DWLP.tau_iff {S : Type u} {E : Effect.{u}} {R : Type u}
    (ewp : StateEffectWP S E) (t : ITree E R) (Q : R → S → Prop) (s : S) :
    DWLP ewp (.tau t) Q s ↔ DWLP ewp t Q s := by
  conv => lhs; rw [DWLP.unfold_eq, ITree.observe_tau]

theorem DWLP.tau {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {t : ITree E R} {Q : R → S → Prop} {s : S}
    (ht : DWLP ewp t Q s) : DWLP ewp (.tau t) Q s :=
  (DWLP.tau_iff ewp t Q s).2 ht

@[simp]
theorem DWLP.vis_iff {S : Type u} {E : Effect.{u}} {R : Type u}
    (ewp : StateEffectWP S E) (i : E.I) (k : E.O i → ITree E R)
    (Q : R → S → Prop) (s : S) :
    DWLP ewp (.vis i k) Q s ↔
      ewp.wp i (fun o s' => DWLP ewp (k o) Q s') s := by
  conv => lhs; rw [DWLP.unfold_eq, ITree.observe_vis]

theorem DWLP.vis {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {i : E.I} {k : E.O i → ITree E R}
    {Q : R → S → Prop} {s : S}
    (hv : ewp.wp i (fun o s' => DWLP ewp (k o) Q s') s) :
    DWLP ewp (.vis i k) Q s :=
  (DWLP.vis_iff ewp i k Q s).2 hv

/-- Silent infinite divergence (`ITree.spin`) satisfies `DWLP` for any `Q`. -/
theorem DWLP.spin {S : Type u} {E : Effect.{u}} {R : Type u}
    (ewp : StateEffectWP S E) (Q : R → S → Prop) (s : S) :
    DWLP ewp (ITree.spin (E := E) (R := R)) Q s :=
  DWLP.coinduct (fun x _ => x = ITree.spin)
    (fun _ _ hx => by subst hx; rw [observe_spin]) rfl

/-- Postcondition weakening for `DWLP`. -/
theorem DWLP.mono {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {t : ITree E R} {P Q : R → S → Prop} {s : S}
    (h_imp : ∀ r s', P r s' → Q r s') (h : DWLP ewp t P s) :
    DWLP ewp t Q s := by
  refine DWLP.coinduct (fun x s₀ => DWLP ewp x P s₀) ?_ h
  intro x s₀ hx
  rw [DWLP.unfold_eq] at hx
  cases h_obs : x.observe <;> simp only [h_obs] at hx
  · exact h_imp _ _ hx
  · exact hx
  · exact ewp.mono (fun _ _ hr => hr) hx

/-- Conjunction rule for `DWLP` under `[StateEffectWP.Conjunctive ewp]`. -/
theorem DWLP.conj {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} [h_conj : StateEffectWP.Conjunctive ewp]
    {t : ITree E R} {P Q : R → S → Prop} {s : S}
    (hp : DWLP ewp t P s) (hq : DWLP ewp t Q s) :
    DWLP ewp t (fun r s' => P r s' ∧ Q r s') s := by
  refine DWLP.coinduct (fun x s₀ => DWLP ewp x P s₀ ∧ DWLP ewp x Q s₀) ?_ ⟨hp, hq⟩
  intro x s₀ ⟨hpx, hqx⟩
  rw [DWLP.unfold_eq] at hpx hqx
  cases h_obs : x.observe <;> simp only [h_obs] at hpx hqx
  · exact ⟨hpx, hqx⟩
  · exact ⟨hpx, hqx⟩
  · exact h_conj.conj hpx hqx

theorem DWLP.conj_iff {S : Type u} {E : Effect.{u}} {R : Type u}
    (ewp : StateEffectWP S E) [StateEffectWP.Conjunctive ewp]
    (t : ITree E R) (P Q : R → S → Prop) (s : S) :
    DWLP ewp t (fun r s' => P r s' ∧ Q r s') s ↔
      DWLP ewp t P s ∧ DWLP ewp t Q s :=
  ⟨fun h => ⟨DWLP.mono (fun _ _ hpq => hpq.1) h,
             DWLP.mono (fun _ _ hpq => hpq.2) h⟩,
   fun ⟨hp, hq⟩ => DWLP.conj hp hq⟩

/-- Monadic sequencing rule for `DWLP`. -/
theorem DWLP.bind {S : Type u} {E : Effect.{u}} {A B : Type u}
    {ewp : StateEffectWP S E} {t : ITree E A} {k : A → ITree E B}
    {Q : B → S → Prop} {s : S}
    (h : DWLP ewp t (fun a s' => DWLP ewp (k a) Q s') s) :
    DWLP ewp (t >>= k) Q s := by
  refine DWLP.coinduct
    (fun u s₀ => DWLP ewp u Q s₀ ∨
      ∃ t₀ : ITree E A, u = (t₀ >>= k) ∧
        DWLP ewp t₀ (fun a s' => DWLP ewp (k a) Q s') s₀)
    ?_ (Or.inr ⟨t, rfl, h⟩)
  intro u s₀ h_inv
  rcases h_inv with hu | ⟨t₀, rfl, ht₀⟩
  · rw [DWLP.unfold_eq] at hu
    cases h_obs : u.observe <;> simp only [h_obs] at hu
    · exact hu
    · exact Or.inl hu
    · exact ewp.mono (fun _ _ hd => Or.inl hd) hu
  · rw [DWLP.unfold_eq] at ht₀
    cases h_obs : t₀.observe with
    | ret a =>
      simp only [h_obs] at ht₀
      have hEq : t₀ = .ret a := by rw [← ITree.fold_observe t₀, h_obs]; rfl
      rw [hEq, ret_bind]
      rw [DWLP.unfold_eq] at ht₀
      cases hk : (k a).observe <;> simp only [hk] at ht₀
      · exact ht₀
      · exact Or.inl ht₀
      · exact ewp.mono (fun _ _ hd => Or.inl hd) ht₀
    | tau t₀' =>
      simp only [h_obs] at ht₀
      have hEq : t₀ = .tau t₀' := by rw [← ITree.fold_observe t₀, h_obs]; rfl
      rw [hEq, tau_bind, ITree.observe_tau]
      exact Or.inr ⟨t₀', rfl, ht₀⟩
    | vis i c =>
      simp only [h_obs] at ht₀
      have hEq : t₀ = .vis i c := by rw [← ITree.fold_observe t₀, h_obs]; rfl
      rw [hEq, vis_bind, ITree.observe_vis]
      exact ewp.mono (fun o _ hd => Or.inr ⟨c o, rfl, hd⟩) ht₀

/-- Exact monadic bind characterization for `DWLP`. -/
theorem DWLP.bind_iff {S : Type u} {E : Effect.{u}} {A B : Type u}
    (ewp : StateEffectWP S E) (t : ITree E A) (k : A → ITree E B)
    (Q : B → S → Prop) (s : S) :
    DWLP ewp (t >>= k) Q s ↔
      DWLP ewp t (fun a s' => DWLP ewp (k a) Q s') s := by
  refine ⟨fun h => ?_, DWLP.bind⟩
  refine DWLP.coinduct (fun t₀ s₀ => DWLP ewp (t₀ >>= k) Q s₀) ?_ h
  intro t₀ s₀ ht₀
  cases h_obs : t₀.observe with
  | ret a =>
    have hEq : t₀ = .ret a := by rw [← ITree.fold_observe t₀, h_obs]; rfl
    rw [hEq, ret_bind] at ht₀; exact ht₀
  | tau t₀' =>
    have hEq : t₀ = .tau t₀' := by rw [← ITree.fold_observe t₀, h_obs]; rfl
    rw [hEq, tau_bind, DWLP.tau_iff] at ht₀; exact ht₀
  | vis i c =>
    have hEq : t₀ = .vis i c := by rw [← ITree.fold_observe t₀, h_obs]; rfl
    rw [hEq, vis_bind, DWLP.vis_iff] at ht₀; exact ht₀

/-- Coinductive loop-invariant rule for `ITree.iter`. -/
theorem DWLP.iter_invariant {S : Type u} {E : Effect.{u}} {I R : Type u}
    {ewp : StateEffectWP S E}
    (body : I → ITree E (I ⊕ R))
    (Inv : I → S → Prop) {Q : R → S → Prop}
    (h_body : ∀ a s₀, Inv a s₀ →
      DWLP ewp (body a) (Sum.elim Inv Q) s₀)
    {init : I} {s : S} (h_init : Inv init s) :
    DWLP ewp (ITree.iter body init) Q s := by
  let cont : I ⊕ R → ITree E R :=
    Sum.elim (fun next => .tau (ITree.iter body next)) .ret
  refine DWLP.coinduct
    (fun u s₀ => ∃ cur : ITree E (I ⊕ R),
      u = (cur >>= cont) ∧ DWLP ewp cur (Sum.elim Inv Q) s₀)
    ?_ ⟨body init, iter_unfold body init, h_body init s h_init⟩
  intro u s₀ ⟨cur, hu, h_cur⟩
  subst hu
  rw [DWLP.unfold_eq] at h_cur
  cases h_obs : cur.observe with
  | ret res =>
    simp only [h_obs] at h_cur
    have hEq : cur = .ret res := by rw [← ITree.fold_observe cur, h_obs]; rfl
    rw [hEq, ret_bind]
    cases res with
    | inl next =>
      dsimp only [cont, Sum.elim]; rw [ITree.observe_tau]
      exact ⟨body next, iter_unfold body next, h_body next s₀ h_cur⟩
    | inr r =>
      dsimp only [cont, Sum.elim]; rw [ITree.observe_ret]
      exact h_cur
  | tau cur' =>
    simp only [h_obs] at h_cur
    have hEq : cur = .tau cur' := by rw [← ITree.fold_observe cur, h_obs]; rfl
    rw [hEq, tau_bind, ITree.observe_tau]
    exact ⟨cur', rfl, h_cur⟩
  | vis i c =>
    simp only [h_obs] at h_cur
    have hEq : cur = .vis i c := by rw [← ITree.fold_observe cur, h_obs]; rfl
    rw [hEq, vis_bind, ITree.observe_vis]
    exact ewp.mono (fun o _ hd => ⟨c o, rfl, hd⟩) h_cur

/-! ## 2. Inductive Total-Correctness (`DWP`) -/

private def dwpAux {S : Type u} {E : Effect.{u}} {R : Type u}
    (ewp : StateEffectWP S E) (Q : R → S → Prop)
    (t : ITree E R) (s : S) : Prop :=
  match t.observe with
  | .ret r => Q r s
  | .tau t' => dwpAux ewp Q t' s
  | .vis i k => ewp.wp i (fun o s' => dwpAux ewp Q (k o) s') s
inductive_fixpoint

/--
Inductive Dijkstra Weakest Precondition ($\mu F$) over `t : ITree E R` and
logical state `s : S`.
-/
def DWP {S : Type u} {E : Effect.{u}} {R : Type u}
    (ewp : StateEffectWP S E)
    (t : ITree E R) (Q : R → S → Prop) (s : S) : Prop :=
  dwpAux ewp Q t s

theorem DWP.unfold_eq {S : Type u} {E : Effect.{u}} {R : Type u}
    (ewp : StateEffectWP S E)
    (t : ITree E R) (Q : R → S → Prop) (s : S) :
    DWP ewp t Q s =
      match t.observe with
      | .ret r => Q r s
      | .tau t' => DWP ewp t' Q s
      | .vis i k => ewp.wp i (fun o s' => DWP ewp (k o) Q s') s :=
  dwpAux.eq_def ewp Q t s

/-- Park induction principle for `DWP`. -/
theorem DWP.induct {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {Q : R → S → Prop}
    (Pre : ITree E R → S → Prop)
    (h_closed : ∀ x s₀,
      (match x.observe with
       | .ret r => Q r s₀
       | .tau x' => Pre x' s₀
       | .vis i k => ewp.wp i (fun o s' => Pre (k o) s') s₀) →
      Pre x s₀)
    {t : ITree E R} {s : S} (h : DWP ewp t Q s) :
    Pre t s :=
  dwpAux.induct ewp Q Pre h_closed t s h

/-- Every total-correctness proof (`DWP`) implies partial correctness (`DWLP`). -/
theorem DWP.toDWLP {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {t : ITree E R} {Q : R → S → Prop} {s : S}
    (h : DWP ewp t Q s) : DWLP ewp t Q s := by
  refine DWP.induct (fun x s₀ => DWLP ewp x Q s₀) ?_ h
  intro x s₀ hx
  rw [DWLP.unfold_eq]
  exact hx

@[simp]
theorem DWP.ret_iff {S : Type u} {E : Effect.{u}} {R : Type u}
    (ewp : StateEffectWP S E) (r : R) (Q : R → S → Prop) (s : S) :
    DWP ewp (.ret r) Q s ↔ Q r s := by
  conv => lhs; rw [DWP.unfold_eq, ITree.observe_ret]

theorem DWP.ret {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {r : R} {Q : R → S → Prop} {s : S}
    (hq : Q r s) : DWP ewp (.ret r) Q s :=
  (DWP.ret_iff ewp r Q s).2 hq

@[simp]
theorem DWP.tau_iff {S : Type u} {E : Effect.{u}} {R : Type u}
    (ewp : StateEffectWP S E) (t : ITree E R) (Q : R → S → Prop) (s : S) :
    DWP ewp (.tau t) Q s ↔ DWP ewp t Q s := by
  conv => lhs; rw [DWP.unfold_eq, ITree.observe_tau]

theorem DWP.tau {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {t : ITree E R} {Q : R → S → Prop} {s : S}
    (ht : DWP ewp t Q s) : DWP ewp (.tau t) Q s :=
  (DWP.tau_iff ewp t Q s).2 ht

@[simp]
theorem DWP.vis_iff {S : Type u} {E : Effect.{u}} {R : Type u}
    (ewp : StateEffectWP S E) (i : E.I) (k : E.O i → ITree E R)
    (Q : R → S → Prop) (s : S) :
    DWP ewp (.vis i k) Q s ↔
      ewp.wp i (fun o s' => DWP ewp (k o) Q s') s := by
  conv => lhs; rw [DWP.unfold_eq, ITree.observe_vis]

theorem DWP.vis {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {i : E.I} {k : E.O i → ITree E R}
    {Q : R → S → Prop} {s : S}
    (hv : ewp.wp i (fun o s' => DWP ewp (k o) Q s') s) :
    DWP ewp (.vis i k) Q s :=
  (DWP.vis_iff ewp i k Q s).2 hv

/-- Unlike `DWLP`, `DWP` rejects silent infinite divergence (`¬ DWP ewp spin Q s`). -/
theorem DWP.spin_false {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {Q : R → S → Prop} {s : S} :
    ¬ DWP ewp (ITree.spin (E := E) (R := R)) Q s := by
  intro h
  refine DWP.induct (fun x _ => x ≠ ITree.spin) ?_ h rfl
  intro x _ hx rfl
  rw [observe_spin] at hx
  exact hx rfl

/-- Dijkstra's Excluded Miracle lifted to full interaction trees. -/
theorem DWP.excludedMiracle {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} [h_em : StateEffectWP.ExcludedMiracle ewp]
    {t : ITree E R} {s : S} :
    ¬ DWP ewp t (fun _ _ => False) s := by
  refine DWP.induct (fun _ _ => False) ?_
  intro x _ hx
  cases h_obs : x.observe <;> simp only [h_obs] at hx
  exact h_em.no_miracle hx

/-- Postcondition weakening for `DWP`. -/
theorem DWP.mono {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {t : ITree E R} {P Q : R → S → Prop} {s : S}
    (h_imp : ∀ r s', P r s' → Q r s') (h : DWP ewp t P s) :
    DWP ewp t Q s := by
  refine DWP.induct (fun x s₀ => DWP ewp x Q s₀) ?_ h
  intro x s₀ hx
  rw [DWP.unfold_eq]
  cases h_obs : x.observe <;> simp only [h_obs] at hx ⊢
  · exact h_imp _ _ hx
  · exact hx
  · exact hx

/-- Conjunction rule for `DWP` under `[StateEffectWP.Conjunctive ewp]`. -/
theorem DWP.conj {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} [h_conj : StateEffectWP.Conjunctive ewp]
    {t : ITree E R} {P Q : R → S → Prop} {s : S}
    (hp : DWP ewp t P s) (hq : DWP ewp t Q s) :
    DWP ewp t (fun r s' => P r s' ∧ Q r s') s := by
  revert hq
  refine DWP.induct
    (fun x s₀ => DWP ewp x Q s₀ → DWP ewp x (fun r s' => P r s' ∧ Q r s') s₀)
    ?_ hp
  intro x s₀ hpx hqx
  rw [DWP.unfold_eq] at hqx ⊢
  cases h_obs : x.observe <;> simp only [h_obs] at hpx hqx ⊢
  · exact ⟨hpx, hqx⟩
  · exact hpx hqx
  · exact ewp.mono (fun _ _ ⟨f, q⟩ => f q) (h_conj.conj hpx hqx)

/-- Monadic sequencing rule for `DWP`. -/
theorem DWP.bind {S : Type u} {E : Effect.{u}} {A B : Type u}
    {ewp : StateEffectWP S E} {t : ITree E A} {k : A → ITree E B}
    {Q : B → S → Prop} {s : S}
    (h : DWP ewp t (fun a s' => DWP ewp (k a) Q s') s) :
    DWP ewp (t >>= k) Q s := by
  refine DWP.induct (fun t₀ s₀ => DWP ewp (t₀ >>= k) Q s₀) ?_ h
  intro t₀ s₀ ht₀
  cases h_obs : t₀.observe with
  | ret a =>
    simp only [h_obs] at ht₀
    have hEq : t₀ = .ret a := by rw [← ITree.fold_observe t₀, h_obs]; rfl
    rw [hEq, ret_bind]; exact ht₀
  | tau t₀' =>
    simp only [h_obs] at ht₀
    have hEq : t₀ = .tau t₀' := by rw [← ITree.fold_observe t₀, h_obs]; rfl
    rw [hEq, tau_bind]; exact DWP.tau ht₀
  | vis i c =>
    simp only [h_obs] at ht₀
    have hEq : t₀ = .vis i c := by rw [← ITree.fold_observe t₀, h_obs]; rfl
    rw [hEq, vis_bind]; exact DWP.vis ht₀

/--
Well-founded total-correctness loop rule for `ITree.iter` using Lean's standard
accessibility predicate `Acc`.
-/
theorem DWP.iter_acc {S : Type u} {E : Effect.{u}} {I R : Type u}
    {ewp : StateEffectWP S E}
    (body : I → ITree E (I ⊕ R))
    (R_lt : I → I → Prop)
    (Inv : I → S → Prop) {Q : R → S → Prop}
    (h_body : ∀ a s₀, Inv a s₀ →
      DWP ewp (body a)
        (Sum.elim (fun next s' => Inv next s' ∧ R_lt next a) Q) s₀)
    {init : I} (h_acc : Acc R_lt init) :
    ∀ {s : S}, Inv init s → DWP ewp (ITree.iter body init) Q s := by
  induction h_acc with
  | intro a _ ih =>
    intro s h_inv
    rw [iter_unfold]
    apply DWP.bind
    refine DWP.mono ?_ (h_body a s h_inv)
    rintro (next | r) s' h_post
    · exact DWP.tau (ih next h_post.2 h_post.1)
    · exact DWP.ret h_post

/-- `Nat`-ranked total-correctness loop rule for `ITree.iter`. -/
theorem DWP.iter_ranked {S : Type u} {E : Effect.{u}} {I R : Type u}
    {ewp : StateEffectWP S E}
    (body : I → ITree E (I ⊕ R))
    (Inv : Nat → I → S → Prop) {Q : R → S → Prop}
    (h_zero : ∀ a s₀, Inv 0 a s₀ →
      DWP ewp (body a) (Sum.elim (fun _ _ => False) Q) s₀)
    (h_succ : ∀ n a s₀, Inv (n + 1) a s₀ →
      DWP ewp (body a) (Sum.elim (Inv n) Q) s₀) :
    (rank : Nat) → ∀ {a : I} {s : S},
      Inv rank a s → DWP ewp (ITree.iter body a) Q s
  | 0, a, s, h_inv => by
    rw [iter_unfold]; apply DWP.bind
    refine DWP.mono ?_ (h_zero a s h_inv)
    rintro (_ | _) _ hp
    · exact False.elim hp
    · exact DWP.ret hp
  | n + 1, a, s, h_inv => by
    rw [iter_unfold]; apply DWP.bind
    refine DWP.mono ?_ (h_succ n a s h_inv)
    rintro (next | _) _ hp
    · exact DWP.tau (DWP.iter_ranked body Inv h_zero h_succ n hp)
    · exact DWP.ret hp

/-! ## 3. Operational Adequacy (`TreeSafe`, `Productive`, `¬ MayDiverge`) -/

private theorem dwlp_tauStar {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {t u : ITree E R} {Q : R → S → Prop} {s : S}
    (h_tau : TauStar t u) (h_dwlp : DWLP ewp t Q s) :
    DWLP ewp u Q s := by
  induction h_tau with
  | refl => exact h_dwlp
  | step ht _ ih =>
    rw [DWLP.unfold_eq, ht] at h_dwlp
    exact ih h_dwlp

private theorem dwlp_pure_reaches {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {ewp : EffectWP E} [h_sound : PureSoundWP ewp]
    {t u : ITree E R} {tr : List (Event E)} {Q : R → PUnit.{u + 1} → Prop}
    (h_reach : Reaches t tr u) (h_dwlp : DWLP ewp t Q PUnit.unit) :
    DWLP ewp u Q PUnit.unit := by
  induction h_reach with
  | refl => exact h_dwlp
  | tau ht _ ih =>
    rw [DWLP.unfold_eq, ht] at h_dwlp; exact ih h_dwlp
  | vis hv _ o _ ih =>
    rw [DWLP.unfold_eq, hv] at h_dwlp; exact ih ((h_sound.sound h_dwlp).2 o)

/-- Stateless `DWLP` adequacy: guarantees `TreeSafe t` and `post` on all returns. -/
theorem dwlp_pure_adequacy {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {ewp : EffectWP E} [h_sound : PureSoundWP ewp]
    {t : ITree E R} {post : R → Prop}
    (h_dwlp : DWLP ewp t (fun r _ => post r) PUnit.unit) :
    TreeSafe t ∧ ∀ tr r, ReachesRet t tr r → post r := by
  refine ⟨?_, ?_⟩
  · intro tr u h_reach ⟨u', i, k, h_tau, h_obs, h_fault⟩
    have hu' := dwlp_tauStar h_tau (dwlp_pure_reaches h_reach h_dwlp)
    rw [DWLP.unfold_eq, h_obs] at hu'
    exact (h_sound.sound hu').1 h_fault
  · intro tr r ⟨u, h_reach, h_ret⟩
    have hu := dwlp_pure_reaches h_reach h_dwlp
    rw [DWLP.unfold_eq, h_ret] at hu
    exact hu

private theorem dwlp_trace_reaches {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {ewp : StateEffectWP (List (Event E)) E} [h_sound : TraceSoundWP ewp]
    {t u : ITree E R} {tr : List (Event E)} {Q : R → List (Event E) → Prop}
    (h_reach : Reaches t tr u) :
    ∀ {tr₀ : List (Event E)},
      DWLP ewp t Q tr₀ → DWLP ewp u Q (tr₀ ++ tr) := by
  induction h_reach with
  | refl => intro tr₀ h; simpa using h
  | tau ht _ ih =>
    intro tr₀ h; rw [DWLP.unfold_eq, ht] at h; exact ih h
  | vis hv _ o _ ih =>
    intro tr₀ h
    rw [DWLP.unfold_eq, hv] at h
    have h_next := ih ((h_sound.sound h).2 o)
    simpa [List.append_assoc] using h_next

/-- Event-trace `DWLP` adequacy starting from `[]`. -/
theorem dwlp_trace_adequacy {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {ewp : StateEffectWP (List (Event E)) E} [h_sound : TraceSoundWP ewp]
    {t : ITree E R} {post : R → List (Event E) → Prop}
    (h_dwlp : DWLP ewp t post []) :
    TreeSafe t ∧ ∀ tr r, ReachesRet t tr r → post r tr := by
  refine ⟨?_, ?_⟩
  · intro tr u h_reach ⟨u', i, k, h_tau, h_obs, h_fault⟩
    have hu' := dwlp_tauStar h_tau (dwlp_trace_reaches h_reach h_dwlp)
    rw [DWLP.unfold_eq, h_obs] at hu'
    exact (h_sound.sound hu').1 h_fault
  · intro tr r ⟨u, h_reach, h_ret⟩
    have hu : DWLP ewp u post ([] ++ tr) := dwlp_trace_reaches h_reach h_dwlp
    rw [List.nil_append, DWLP.unfold_eq, h_ret] at hu
    exact hu

private theorem dwp_stabilizes {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {t : ITree E R} {Q : R → S → Prop} {s : S}
    (h_dwp : DWP ewp t Q s) :
    ∃ u' : ITree E R, TauStar t u' ∧ ∀ w, u'.observe ≠ .tau w := by
  refine DWP.induct
    (fun x _ => ∃ u', TauStar x u' ∧ ∀ w, u'.observe ≠ .tau w) ?_ h_dwp
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

private theorem dwp_pure_reaches {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {ewp : EffectWP E} [h_sound : PureSoundWP ewp]
    {t u : ITree E R} {tr : List (Event E)} {Q : R → PUnit.{u + 1} → Prop}
    (h_reach : Reaches t tr u) (h_dwp : DWP ewp t Q PUnit.unit) :
    DWP ewp u Q PUnit.unit := by
  induction h_reach with
  | refl => exact h_dwp
  | tau ht _ ih =>
    rw [DWP.unfold_eq, ht] at h_dwp; exact ih h_dwp
  | vis hv _ o _ ih =>
    rw [DWP.unfold_eq, hv] at h_dwp; exact ih ((h_sound.sound h_dwp).2 o)

/--
Total-correctness `DWP` adequacy: guarantees `TreeSafe t`, `Productive t`,
`¬ MayDiverge t`, and `post` on all returns.
-/
theorem dwp_pure_adequacy {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {ewp : EffectWP E} [PureSoundWP ewp]
    {t : ITree E R} {post : R → Prop}
    (h_dwp : DWP ewp t (fun r _ => post r) PUnit.unit) :
    TreeSafe t ∧ Productive t ∧ ¬ MayDiverge t ∧
      ∀ tr r, ReachesRet t tr r → post r := by
  have h_part := dwlp_pure_adequacy h_dwp.toDWLP
  have h_prod : Productive t :=
    fun _ _ h_reach => dwp_stabilizes (dwp_pure_reaches h_reach h_dwp)
  exact ⟨h_part.1, h_prod, productive_not_mayDiverge h_prod, h_part.2⟩

/-! ## 4. Horizontal Effect-Handler Linking (`interp` & `interpState`) -/

/-- Horizontal handler linking for `DWP` across `ITree.interp`. -/
theorem dwp_interp {S : Type u} {E₁ E₂ : Effect.{u}} {R : Type u}
    {ewp₁ : StateEffectWP S E₁} {ewp₂ : StateEffectWP S E₂}
    (h : (i : E₁.I) → ITree E₂ (E₁.O i))
    (h_link : ∀ i (Q : E₁.O i → S → Prop) s₀,
      ewp₁.wp i Q s₀ → DWP ewp₂ (h i) Q s₀)
    {t : ITree E₁ R} {post : R → S → Prop} {s : S}
    (h_dwp : DWP ewp₁ t post s) :
    DWP ewp₂ (ITree.interp h t) post s := by
  refine DWP.induct (fun t₀ s₀ => DWP ewp₂ (ITree.interp h t₀) post s₀) ?_ h_dwp
  intro t₀ s₀ ht₀
  cases h_obs : t₀.observe with
  | ret r =>
    simp only [h_obs] at ht₀
    have hEq : t₀ = .ret r := by rw [← ITree.fold_observe t₀, h_obs]; rfl
    rw [hEq, interp_ret]; exact DWP.ret ht₀
  | tau t₀' =>
    simp only [h_obs] at ht₀
    have hEq : t₀ = .tau t₀' := by rw [← ITree.fold_observe t₀, h_obs]; rfl
    rw [hEq, interp_tau]; exact DWP.tau ht₀
  | vis i k =>
    simp only [h_obs] at ht₀
    have hEq : t₀ = .vis i k := by rw [← ITree.fold_observe t₀, h_obs]; rfl
    rw [hEq, interp_vis]
    exact DWP.bind (h_link i _ s₀ (ewp₁.mono (fun _ _ hd => DWP.tau hd) ht₀))

/-- Horizontal handler linking for `DWLP` across `ITree.interp`. -/
theorem dwlp_interp {S : Type u} {E₁ E₂ : Effect.{u}} {R : Type u}
    {ewp₁ : StateEffectWP S E₁} {ewp₂ : StateEffectWP S E₂}
    (h : (i : E₁.I) → ITree E₂ (E₁.O i))
    (h_link : ∀ i (Q : E₁.O i → S → Prop) s₀,
      ewp₁.wp i Q s₀ → DWLP ewp₂ (h i) Q s₀)
    {t : ITree E₁ R} {post : R → S → Prop} {s : S}
    (h_dwlp : DWLP ewp₁ t post s) :
    DWLP ewp₂ (ITree.interp h t) post s := by
  let Inv : ITree E₂ R → S → Prop := fun u s₀ =>
    (∃ t₀, u = ITree.interp h t₀ ∧ DWLP ewp₁ t₀ post s₀) ∨
    (∃ (i : E₁.I) (m : ITree E₂ (E₁.O i)) (k : E₁.O i → ITree E₁ R),
      u = (m >>= fun o => .tau (ITree.interp h (k o))) ∧
      DWLP ewp₂ m (fun o s' => DWLP ewp₁ (k o) post s') s₀)
  have stepBind : ∀ (i : E₁.I) (m : ITree E₂ (E₁.O i))
      (k : E₁.O i → ITree E₁ R) (s₀ : S),
      DWLP ewp₂ m (fun o s' => DWLP ewp₁ (k o) post s') s₀ →
      match (m >>= fun o => .tau (ITree.interp h (k o))).observe with
      | .ret r => post r s₀
      | .tau u' => Inv u' s₀
      | .vis j c => ewp₂.wp j (fun o s' => Inv (c o) s') s₀ := by
    intro i m k s₀ hm
    rw [DWLP.unfold_eq] at hm
    cases hm_obs : m.observe with
    | ret o =>
      simp only [hm_obs] at hm
      have hEq : m = .ret o := by rw [← ITree.fold_observe m, hm_obs]; rfl
      rw [hEq, ret_bind, ITree.observe_tau]
      exact Or.inl ⟨k o, rfl, hm⟩
    | tau m' =>
      simp only [hm_obs] at hm
      have hEq : m = .tau m' := by rw [← ITree.fold_observe m, hm_obs]; rfl
      rw [hEq, tau_bind, ITree.observe_tau]
      exact Or.inr ⟨i, m', k, rfl, hm⟩
    | vis j c =>
      simp only [hm_obs] at hm
      have hEq : m = .vis j c := by rw [← ITree.fold_observe m, hm_obs]; rfl
      rw [hEq, vis_bind, ITree.observe_vis]
      exact ewp₂.mono (fun o₂ _ hd => Or.inr ⟨i, c o₂, k, rfl, hd⟩) hm
  refine DWLP.coinduct Inv ?_ (Or.inl ⟨t, rfl, h_dwlp⟩)
  intro u s₀ h_inv
  rcases h_inv with ⟨t₀, rfl, ht₀⟩ | ⟨i, m, k, rfl, hm⟩
  · rw [DWLP.unfold_eq] at ht₀
    cases h_obs : t₀.observe with
    | ret r =>
      simp only [h_obs] at ht₀
      have hEq : t₀ = .ret r := by rw [← ITree.fold_observe t₀, h_obs]; rfl
      rw [hEq, interp_ret, ITree.observe_ret]; exact ht₀
    | tau t₀' =>
      simp only [h_obs] at ht₀
      have hEq : t₀ = .tau t₀' := by rw [← ITree.fold_observe t₀, h_obs]; rfl
      rw [hEq, interp_tau, ITree.observe_tau]; exact Or.inl ⟨t₀', rfl, ht₀⟩
    | vis i k =>
      simp only [h_obs] at ht₀
      have hEq : t₀ = .vis i k := by rw [← ITree.fold_observe t₀, h_obs]; rfl
      rw [hEq, interp_vis]
      exact stepBind i (h i) k s₀ (h_link i _ s₀ ht₀)
  · exact stepBind i m k s₀ hm

/-- Stateful handler linking for `DWP` across `ITree.interpState`. -/
theorem dwp_interpState {H : Type u} {E₁ E₂ : Effect.{u}} {R : Type u}
    {ewp₁ : StateEffectWP H E₁} {ewp₂ : EffectWP E₂}
    (h : (i : E₁.I) → H → ITree E₂ (E₁.O i × H))
    (h_link : ∀ i (Q : E₁.O i → H → Prop) st,
      ewp₁.wp i Q st →
      DWP ewp₂ (h i st) (fun pair _ => Q pair.1 pair.2) PUnit.unit)
    {t : ITree E₁ R} {post : R → H → Prop} {st : H}
    (h_dwp : DWP ewp₁ t post st) :
    DWP ewp₂ (ITree.interpState h t st) (fun pair _ => post pair.1 pair.2) PUnit.unit := by
  refine DWP.induct
    (fun t₀ st₀ => DWP ewp₂ (ITree.interpState h t₀ st₀)
      (fun pair _ => post pair.1 pair.2) PUnit.unit) ?_ h_dwp
  intro t₀ st₀ ht₀
  cases h_obs : t₀.observe with
  | ret r =>
    simp only [h_obs] at ht₀
    have hEq : t₀ = .ret r := by rw [← ITree.fold_observe t₀, h_obs]; rfl
    rw [hEq, interpState_ret]; exact DWP.ret ht₀
  | tau t₀' =>
    simp only [h_obs] at ht₀
    have hEq : t₀ = .tau t₀' := by rw [← ITree.fold_observe t₀, h_obs]; rfl
    rw [hEq, interpState_tau]; exact DWP.tau ht₀
  | vis i k =>
    simp only [h_obs] at ht₀
    have hEq : t₀ = .vis i k := by rw [← ITree.fold_observe t₀, h_obs]; rfl
    rw [hEq, interpState_vis]
    apply DWP.bind
    refine DWP.mono ?_ (h_link i _ st₀ (ewp₁.mono (fun _ _ hd => DWP.tau hd) ht₀))
    rintro ⟨o, st'⟩ _ hq; exact hq

/-- Stateful handler linking for `DWLP` across `ITree.interpState`. -/
theorem dwlp_interpState {H : Type u} {E₁ E₂ : Effect.{u}} {R : Type u}
    {ewp₁ : StateEffectWP H E₁} {ewp₂ : EffectWP E₂}
    (h : (i : E₁.I) → H → ITree E₂ (E₁.O i × H))
    (h_link : ∀ i (Q : E₁.O i → H → Prop) st,
      ewp₁.wp i Q st →
      DWLP ewp₂ (h i st) (fun pair _ => Q pair.1 pair.2) PUnit.unit)
    {t : ITree E₁ R} {post : R → H → Prop} {st : H}
    (h_dwlp : DWLP ewp₁ t post st) :
    DWLP ewp₂ (ITree.interpState h t st) (fun pair _ => post pair.1 pair.2) PUnit.unit := by
  let Inv : ITree E₂ (R × H) → PUnit.{u + 1} → Prop := fun u _ =>
    (∃ t₀ st₀, u = ITree.interpState h t₀ st₀ ∧ DWLP ewp₁ t₀ post st₀) ∨
    (∃ (i : E₁.I) (m : ITree E₂ (E₁.O i × H)) (k : E₁.O i → ITree E₁ R),
      u = (m >>= fun (o, st') => .tau (ITree.interpState h (k o) st')) ∧
      DWLP ewp₂ m (fun pair _ => DWLP ewp₁ (k pair.1) post pair.2) PUnit.unit)
  have stepBind : ∀ (i : E₁.I) (m : ITree E₂ (E₁.O i × H))
      (k : E₁.O i → ITree E₁ R),
      DWLP ewp₂ m (fun pair _ => DWLP ewp₁ (k pair.1) post pair.2) PUnit.unit →
      match (m >>= fun (o, st') => .tau (ITree.interpState h (k o) st')).observe with
      | .ret pair => post pair.1 pair.2
      | .tau u' => Inv u' PUnit.unit
      | .vis j c => ewp₂.wp j (fun o s' => Inv (c o) s') PUnit.unit := by
    intro i m k hm
    rw [DWLP.unfold_eq] at hm
    cases hm_obs : m.observe with
    | ret pair =>
      rcases pair with ⟨o, st'⟩
      simp only [hm_obs] at hm
      have hEq : m = .ret (o, st') := by rw [← ITree.fold_observe m, hm_obs]; rfl
      rw [hEq, ret_bind, ITree.observe_tau]
      exact Or.inl ⟨k o, st', rfl, hm⟩
    | tau m' =>
      simp only [hm_obs] at hm
      have hEq : m = .tau m' := by rw [← ITree.fold_observe m, hm_obs]; rfl
      rw [hEq, tau_bind, ITree.observe_tau]
      exact Or.inr ⟨i, m', k, rfl, hm⟩
    | vis j c =>
      simp only [hm_obs] at hm
      have hEq : m = .vis j c := by rw [← ITree.fold_observe m, hm_obs]; rfl
      rw [hEq, vis_bind, ITree.observe_vis]
      exact ewp₂.mono (fun o₂ _ hd => Or.inr ⟨i, c o₂, k, rfl, hd⟩) hm
  refine DWLP.coinduct Inv ?_ (Or.inl ⟨t, st, rfl, h_dwlp⟩)
  intro u ⟨⟩ h_inv
  rcases h_inv with ⟨t₀, st₀, hu, ht₀⟩ | ⟨i, m, k, hu, hm⟩
  · subst hu
    rw [DWLP.unfold_eq] at ht₀
    cases h_obs : t₀.observe with
    | ret r =>
      simp only [h_obs] at ht₀
      have hEq : t₀ = .ret r := by rw [← ITree.fold_observe t₀, h_obs]; rfl
      rw [hEq, interpState_ret, ITree.observe_ret]; exact ht₀
    | tau t₀' =>
      simp only [h_obs] at ht₀
      have hEq : t₀ = .tau t₀' := by rw [← ITree.fold_observe t₀, h_obs]; rfl
      rw [hEq, interpState_tau, ITree.observe_tau]; exact Or.inl ⟨t₀', st₀, rfl, ht₀⟩
    | vis i k =>
      simp only [h_obs] at ht₀
      have hEq : t₀ = .vis i k := by rw [← ITree.fold_observe t₀, h_obs]; rfl
      rw [hEq, interpState_vis]
      have hsb := stepBind i (h i st₀) k (h_link i _ st₀ ht₀)
      cases hb : (h i st₀ >>= fun (o, s') => .tau (ITree.interpState h (k o) s')).observe <;>
        simp only [hb] at hsb ⊢ <;> exact hsb
  · subst hu
    have hsb := stepBind i m k hm
    cases hb : (m >>= fun (o, st') => .tau (ITree.interpState h (k o) st')).observe <;>
      simp only [hb] at hsb ⊢ <;> exact hsb

/-! ## 5. Computable Fuel-Bounded Coalgebra Stepping (`wpCoalBounded`) -/

/--
Fuel-bounded recursive predicate-transformer stepping directly on an `ITreeF`
coalgebra `step : State → ITreeF E R State`.
-/
def wpCoalBounded {S State : Type u} {E : Effect.{u}} {R : Type u}
    (fuel : Nat) (ewp : StateEffectWP S E)
    (step : State → ITreeF E R State)
    (Q : R → S → Prop) (st : State) (s : S) : Prop :=
  match fuel with
  | 0 => False
  | fuel' + 1 =>
    match step st with
    | .ret r => Q r s
    | .tau st' => wpCoalBounded fuel' ewp step Q st' s
    | .vis i k => ewp.wp i (fun o s' => wpCoalBounded fuel' ewp step Q (k o) s') s

/-- Soundness of `wpCoalBounded` for total correctness (`DWP` on `ITree.cofix`). -/
theorem dwp_cofix_of_wpCoalBounded {S State : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {step : State → ITreeF E R State}
    {Q : R → S → Prop} :
    (fuel : Nat) → ∀ {st : State} {s : S},
      wpCoalBounded fuel ewp step Q st s →
      DWP ewp (ITree.cofix step st) Q s
  | 0, _, _, h => False.elim h
  | fuel' + 1, st, s, h => by
    rw [DWP.unfold_eq, ITree.observe_cofix]
    unfold wpCoalBounded at h
    cases h_st : step st <;> simp only [h_st, ITreeF.map] at h ⊢
    · exact h
    · exact dwp_cofix_of_wpCoalBounded fuel' h
    · exact ewp.mono (fun _ _ hw => dwp_cofix_of_wpCoalBounded fuel' hw) h

/-- Soundness of `wpCoalBounded` for partial correctness (`DWLP` on `ITree.cofix`). -/
theorem dwlp_cofix_of_wpCoalBounded {S State : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {step : State → ITreeF E R State}
    {Q : R → S → Prop} {fuel : Nat} {st : State} {s : S}
    (h : wpCoalBounded fuel ewp step Q st s) :
    DWLP ewp (ITree.cofix step st) Q s :=
  (dwp_cofix_of_wpCoalBounded fuel h).toDWLP

/-! ## 6. `Std.Do.WP` & `Std.Do.WPMonad` Integration -/

section StdDo

open Std.Do

instance {E : Effect.{u}} [p : PureEffectWP E] : WP (ITree E) .pure where
  wp t :=
    { trans := fun Q =>
        ULift.up (DWLP p.ewp t (fun r _ => (Q.1 r).down) PUnit.unit)
      conjunctiveRaw := by
        intro Q₁ Q₂
        apply SPred.bientails.of_eq
        ext
        exact DWLP.conj_iff p.ewp t _ _ PUnit.unit }

instance {E : Effect.{u}} [p : PureEffectWP E] : WPMonad (ITree E) .pure where
  wp_pure a := by
    ext Q
    exact DWLP.ret_iff p.ewp a _ PUnit.unit
  wp_bind x f := by
    ext Q
    exact DWLP.bind_iff p.ewp x f _ PUnit.unit

/-- Strip a leading `.tau` step inside a `Std.Do.Triple` (`⦃P⦄ .tau t ⦃Q⦄`). -/
theorem Triple.tau {E : Effect.{u}} {R : Type u} [p : PureEffectWP E]
    (t : ITree E R) (P : Assertion .pure) (Q : PostCond R .pure)
    (h : ⦃P⦄ t ⦃Q⦄) : ⦃P⦄ ITree.tau t ⦃Q⦄ := by
  intro hp
  have ht : DWLP p.ewp t (fun r _ => (Q.1 r).down) PUnit.unit := h hp
  exact (DWLP.tau_iff p.ewp t _ PUnit.unit).2 ht

/-- Bridge a `Std.Do.Triple` on `ITree E R` directly to `DWLP`. -/
theorem Triple.toDWLP {E : Effect.{u}} {R : Type u} [p : PureEffectWP E]
    {t : ITree E R} {P : Prop} {Q : R → Prop}
    (htriple : ⦃⌜P⌝⦄ t ⦃⇓ r => ⌜Q r⌝⦄) (hp : P) :
    DWLP p.ewp t (fun r _ => Q r) PUnit.unit :=
  htriple hp

end StdDo

end Anneal.ITreeWP
