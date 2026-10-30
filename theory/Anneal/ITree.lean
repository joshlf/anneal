import Trusted
import Anneal.Refinement
import Anneal.Effect

namespace Anneal.ITree

open Trusted.Refinement
open Trusted.CoInd
open Trusted.Effect
open Trusted.ITree

/-!
Metatheory of coinductive interaction trees (`ITree E R`), leveraging Lean 4's
native `coinductive_fixpoint`, `LawfulMonad`, and `List` library (`#100`,
`#103`):

1. **Strong bisimulation & monad laws**: `StrongBisim t u ↔ t = u`,
   `LawfulMonad (ITree E)`, and `@[simp]` constructor equations for `bind`,
   `iter`, `interp`, and `interpState`.
2. **2×2 coinductive equivalence & Smyth refinement hierarchy**:
   - `Eutt` (equivalence up to finite `.tau`s, preserving divergence),
   - `WeakSim` (naive forward simulation: `fail = ⊥`, `stuck = ⊥`),
   - `WeakCSim` (progress-guarded complete similarity),
   - `WeakRef` (Smyth partial refinement: `fail = ⊤`, `stuck = ⊥`),
   - `TotalWeakRef` (divergence-sensitive Smyth total refinement).
3. **Layer 1A adequacy**: `UBClosedPrefixes` characterization,
   `WeakRef.toPartial_le`, and `WeakRef.toPrefixPartial_le`.
4. **Infinite executions & temporal/stream modalities**: `CoAlways` ($\Box P$),
   `Eventually` ($\Diamond P$), `InfinitelyOften` ($\Box\Diamond P$),
   `Stream'`, and `FollowsStream` (including determinism).
5. **Skolemized environment strategies & foreign/ISA bridge contracts**:
   `EnvStrategy` (`reaches_iff_exists_strategy`) and `BridgeContract`.
-/

universe u

/-! ## 1. Strong Bisimulation, Propositional Equality, and `LawfulMonad` -/

/-- Lockstep coinductive strong bisimulation on `ITree E R`. -/
def StrongBisim {E : Effect.{u}} {R : Type u} (t u : ITree E R) : Prop :=
  match t.observe, u.observe with
  | .ret r₁, .ret r₂ => r₁ = r₂
  | .tau t', .tau u' => StrongBisim t' u'
  | .vis i₁ k₁, .vis i₂ k₂ =>
    ∃ h : i₁ = i₂, ∀ o : E.O i₁, StrongBisim (k₁ o) (k₂ (h ▸ o))
  | _, _ => False
coinductive_fixpoint

theorem StrongBisim.refl {E : Effect.{u}} {R : Type u} (t : ITree E R) :
    StrongBisim t t := by
  refine StrongBisim.coinduct (fun a b => a = b) ?_ t t rfl
  intro a b hab; subst hab
  cases a.observe with
  | ret _ => rfl
  | tau _ => rfl
  | vis _ _ => exact ⟨rfl, fun _ => rfl⟩

/-- Strong bisimulation coincides with propositional equality on `ITree E R`. -/
theorem strongBisim_iff_eq {E : Effect.{u}} {R : Type u}
    (t u : ITree E R) : StrongBisim t u ↔ t = u := by
  refine ⟨fun h => ?_, fun h => h ▸ StrongBisim.refl t⟩
  apply CoInd.approx_eq
  intro n
  induction n generalizing t u with
  | zero => cases t.approx 0; cases u.approx 0; rfl
  | succ k ih =>
    have hUnf : (ITree.fold t.observe).approx (k + 1) =
        (ITree.fold u.observe).approx (k + 1) := by
      rw [StrongBisim.eq_def] at h
      cases ht : t.observe <;> cases hu : u.observe <;>
        simp only [ht, hu] at h
      · subst h; rfl
      · dsimp [ITree.fold, CoInd.fold]
        congr; funext ⟨⟩; exact ih _ _ h
      · rcases h with ⟨hi, hk⟩
        subst hi
        dsimp [ITree.fold, CoInd.fold]
        congr; funext o; exact ih _ _ (hk o)
    simpa [ITree.fold_observe] using hUnf

theorem ITree.eq_of_observe_eq {E : Effect.{u}} {R : Type u}
    {t u : ITree E R} (h : t.observe = u.observe) : t = u := by
  rw [← ITree.fold_observe t, ← ITree.fold_observe u, h]

private def bindStep {E : Effect.{u}} {R S : Type u} (k : R → ITree E S) :
    ITree E R ⊕ ITree E S → ITreeF E S (ITree E R ⊕ ITree E S)
  | .inl cur =>
    match cur.observe with
    | .ret r => (k r).observe.map .inr
    | .tau cur' => .tau (.inl cur')
    | .vis i c => .vis i (fun o => .inl (c o))
  | .inr o => o.observe.map .inr

private theorem bind_inr_eq {E : Effect.{u}} {R S : Type u}
    (k : R → ITree E S) (out : ITree E S) :
    ITree.cofix (bindStep k) (.inr out) = out := by
  rw [← strongBisim_iff_eq]
  refine StrongBisim.coinduct
    (fun a b => a = ITree.cofix (bindStep k) (Sum.inr b)) ?_ _ out rfl
  intro a b hab; subst hab
  rw [ITree.observe_cofix]; dsimp only [bindStep]
  cases b.observe with
  | ret _ => dsimp only [ITreeF.map]
  | tau _ => dsimp only [ITreeF.map]
  | vis _ _ => dsimp only [ITreeF.map]; exact ⟨rfl, fun _ => rfl⟩

@[simp]
theorem observe_bind_ret {E : Effect.{u}} {R S : Type u}
    (r : R) (k : R → ITree E S) :
    (ITree.ret r >>= k).observe = (k r).observe := by
  change (ITree.cofix (bindStep k) (.inl (ITree.ret r))).observe = (k r).observe
  rw [ITree.observe_cofix]; dsimp only [bindStep]; rw [ITree.observe_ret]; dsimp only
  cases hk : (k r).observe <;> simp [ITreeF.map, bind_inr_eq]

@[simp]
theorem ret_bind {E : Effect.{u}} {R S : Type u}
    (r : R) (k : R → ITree E S) :
    (ITree.ret (E := E) r >>= k) = k r :=
  ITree.eq_of_observe_eq (observe_bind_ret r k)

@[simp]
theorem tau_bind {E : Effect.{u}} {R S : Type u}
    (t : ITree E R) (k : R → ITree E S) :
    (ITree.tau t >>= k) = ITree.tau (t >>= k) := by
  apply ITree.eq_of_observe_eq
  change (ITree.cofix (bindStep k) (.inl (ITree.tau t))).observe =
    (ITree.tau (ITree.cofix (bindStep k) (.inl t))).observe
  rw [ITree.observe_cofix]; dsimp [bindStep]; rw [ITree.observe_tau, ITree.observe_tau]
  rfl

@[simp]
theorem vis_bind {E : Effect.{u}} {R S : Type u}
    (i : E.I) (c : E.O i → ITree E R) (k : R → ITree E S) :
    (ITree.vis i c >>= k) = ITree.vis i (fun o => c o >>= k) := by
  apply ITree.eq_of_observe_eq
  change (ITree.cofix (bindStep k) (.inl (ITree.vis i c))).observe =
    (ITree.vis i (fun o => ITree.cofix (bindStep k) (.inl (c o)))).observe
  rw [ITree.observe_cofix]; dsimp [bindStep]; rw [ITree.observe_vis, ITree.observe_vis]
  rfl

@[simp]
theorem bind_ret {E : Effect.{u}} {R : Type u} (t : ITree E R) :
    (t >>= ITree.ret) = t := by
  rw [← strongBisim_iff_eq]
  refine StrongBisim.coinduct (fun a b => a = (b >>= ITree.ret)) ?_ _ t rfl
  intro a b hab; subst hab
  cases hb : b.observe with
  | ret r =>
    have hEq : b = .ret r := by rw [← ITree.fold_observe b, hb]; rfl
    subst hEq; simp
  | tau b' =>
    have hEq : b = .tau b' := by rw [← ITree.fold_observe b, hb]; rfl
    subst hEq; simp
  | vis i c =>
    have hEq : b = .vis i c := by rw [← ITree.fold_observe b, hb]; rfl
    subst hEq; rw [vis_bind, ITree.observe_vis]; exact ⟨rfl, fun _ => rfl⟩

theorem bind_assoc_itree {E : Effect.{u}} {R S T : Type u}
    (t : ITree E R) (f : R → ITree E S) (g : S → ITree E T) :
    ((t >>= f) >>= g) = (t >>= fun r => f r >>= g) := by
  rw [← strongBisim_iff_eq]
  refine StrongBisim.coinduct
    (fun a b => a = b ∨ ∃ x : ITree E R, a = ((x >>= f) >>= g) ∧
      b = (x >>= fun r => f r >>= g))
    ?_ _ _ (Or.inr ⟨t, rfl, rfl⟩)
  intro a b h
  rcases h with rfl | ⟨x, rfl, rfl⟩
  · cases a.observe with
    | ret _ => rfl
    | tau _ => exact Or.inl rfl
    | vis _ _ => exact ⟨rfl, fun _ => Or.inl rfl⟩
  · cases hx : x.observe with
    | ret r =>
      have hEq : x = .ret r := by rw [← ITree.fold_observe x, hx]; rfl
      subst hEq; simp only [ret_bind]
      cases (f r >>= g).observe with
      | ret _ => rfl
      | tau _ => exact Or.inl rfl
      | vis _ _ => exact ⟨rfl, fun _ => Or.inl rfl⟩
    | tau x' =>
      have hEq : x = .tau x' := by rw [← ITree.fold_observe x, hx]; rfl
      subst hEq; simp only [tau_bind, ITree.observe_tau]
      exact Or.inr ⟨x', rfl, rfl⟩
    | vis i c =>
      have hEq : x = .vis i c := by rw [← ITree.fold_observe x, hx]; rfl
      subst hEq; rw [vis_bind, vis_bind, vis_bind, ITree.observe_vis, ITree.observe_vis]
      exact ⟨rfl, fun o => Or.inr ⟨c o, rfl, rfl⟩⟩

instance {E : Effect.{u}} : LawfulMonad (ITree E) := LawfulMonad.mk'
  (id_map := fun x => bind_ret x)
  (pure_bind := fun x f => ret_bind x f)
  (bind_assoc := fun x f g => bind_assoc_itree x f g)

@[simp]
theorem observe_spin {E : Effect.{u}} {R : Type u} :
    (ITree.spin (E := E) (R := R)).observe = .tau ITree.spin := by
  unfold ITree.spin; rw [ITree.observe_cofix]; rfl

theorem spin_diverges {E : Effect.{u}} {R : Type u} :
    Diverges (ITree.spin (E := E) (R := R)) := by
  refine Diverges.coinduct (· = ITree.spin) ?_ ITree.spin rfl
  intro t ht; subst ht; rw [observe_spin]

/-- Unfolding law for `ITree.iter`. -/
theorem iter_unfold {E : Effect.{u}} {I R : Type u}
    (body : I → ITree E (I ⊕ R)) (init : I) :
    ITree.iter body init =
      (body init >>= Sum.elim (fun next => ITree.tau (ITree.iter body next))
        ITree.ret) := by
  let stepFn : ITree E (I ⊕ R) → ITreeF E R (ITree E (I ⊕ R)) :=
    fun cur =>
      match cur.observe with
      | .ret (.inr r) => .ret r
      | .ret (.inl next) => .tau (body next)
      | .tau cur' => .tau cur'
      | .vis i k => .vis i k
  let cont : I ⊕ R → ITree E R :=
    Sum.elim (fun next => ITree.tau (ITree.iter body next)) ITree.ret
  rw [← strongBisim_iff_eq]
  refine StrongBisim.coinduct
    (fun a b => a = b ∨ ∃ cur : ITree E (I ⊕ R),
      a = ITree.cofix stepFn cur ∧ b = (cur >>= cont))
    ?_ _ _ (Or.inr ⟨body init, rfl, rfl⟩)
  intro a b h
  rcases h with rfl | ⟨cur, rfl, rfl⟩
  · cases a.observe with
    | ret _ => rfl
    | tau _ => exact Or.inl rfl
    | vis _ _ => exact ⟨rfl, fun _ => Or.inl rfl⟩
  · rw [ITree.observe_cofix]
    cases hc : cur.observe with
    | ret sr =>
      have hEq : cur = .ret sr := by rw [← ITree.fold_observe cur, hc]; rfl
      cases sr with
      | inr r =>
        rw [hEq]; simp [stepFn, cont, ITreeF.map]
      | inl next =>
        rw [hEq]; simp only [stepFn, cont, Sum.elim_inl, ret_bind,
          ITree.observe_ret, ITreeF.map, ITree.observe_tau]
        exact Or.inl rfl
    | tau cur' =>
      have hEq : cur = .tau cur' := by rw [← ITree.fold_observe cur, hc]; rfl
      rw [hEq]; simp only [stepFn, tau_bind, ITree.observe_tau, ITreeF.map]
      exact Or.inr ⟨cur', rfl, rfl⟩
    | vis i k =>
      have hEq : cur = .vis i k := by rw [← ITree.fold_observe cur, hc]; rfl
      rw [hEq, vis_bind]; dsimp only [stepFn]
      rw [ITree.observe_vis, ITree.observe_vis]; dsimp only [ITreeF.map]
      exact ⟨rfl, fun o => Or.inr ⟨k o, rfl, rfl⟩⟩

@[simp]
theorem interp_ret {E₁ E₂ : Effect.{u}} {R : Type u}
    (h : (i : E₁.I) → ITree E₂ (E₁.O i)) (r : R) :
    ITree.interp h (.ret r) = .ret r := by
  apply ITree.eq_of_observe_eq
  unfold ITree.interp; rw [ITree.observe_cofix]; dsimp only [ITree.interpStep]
  rw [ITree.observe_ret]; rfl

@[simp]
theorem interp_tau {E₁ E₂ : Effect.{u}} {R : Type u}
    (h : (i : E₁.I) → ITree E₂ (E₁.O i)) (t : ITree E₁ R) :
    ITree.interp h (.tau t) = .tau (ITree.interp h t) := by
  apply ITree.eq_of_observe_eq
  unfold ITree.interp; rw [ITree.observe_cofix]; dsimp only [ITree.interpStep]
  rw [ITree.observe_tau]; dsimp only [ITreeF.map]; rw [ITree.observe_tau]

theorem interp_vis {E₁ E₂ : Effect.{u}} {R : Type u}
    (h : (i : E₁.I) → ITree E₂ (E₁.O i))
    (i : E₁.I) (k : E₁.O i → ITree E₁ R) :
    ITree.interp h (.vis i k) =
      (h i >>= fun o => .tau (ITree.interp h (k o))) := by
  rw [← strongBisim_iff_eq]
  refine StrongBisim.coinduct
    (fun a b => a = b ∨
      (a = ITree.interp h (.vis i k) ∧
        b = (h i >>= fun o => .tau (ITree.interp h (k o)))) ∨
      ∃ u : ITree E₂ (E₁.O i),
        a = ITree.cofix (ITree.interpStep h) (.inr ⟨i, u, k⟩) ∧
        b = (u >>= fun o => .tau (ITree.interp h (k o))))
    ?_ _ _ (Or.inr (Or.inl ⟨rfl, rfl⟩))
  intro a b hab
  rcases hab with rfl | ⟨rfl, rfl⟩ | ⟨u, rfl, rfl⟩
  · cases a.observe with
    | ret _ => rfl
    | tau _ => exact Or.inl rfl
    | vis _ _ => exact ⟨rfl, fun _ => Or.inl rfl⟩
  · unfold ITree.interp
    rw [ITree.observe_cofix]; dsimp only [ITree.interpStep]; rw [ITree.observe_vis]; dsimp only
    cases hu : (h i).observe with
    | ret o =>
      have hEq : h i = .ret o := by rw [← ITree.fold_observe (h i), hu]; rfl
      rw [hEq, ret_bind]; dsimp only [ITreeF.map]; rw [ITree.observe_tau]
      exact Or.inl rfl
    | tau u' =>
      have hEq : h i = .tau u' := by rw [← ITree.fold_observe (h i), hu]; rfl
      rw [hEq, tau_bind]; dsimp only [ITreeF.map]; rw [ITree.observe_tau]
      exact Or.inr (Or.inr ⟨u', rfl, rfl⟩)
    | vis j k₂ =>
      have hEq : h i = .vis j k₂ := by rw [← ITree.fold_observe (h i), hu]; rfl
      rw [hEq, vis_bind]; dsimp only [ITreeF.map]; rw [ITree.observe_vis]
      exact ⟨rfl, fun o₂ => Or.inr (Or.inr ⟨k₂ o₂, rfl, rfl⟩)⟩
  · rw [ITree.observe_cofix]; dsimp only [ITree.interpStep]
    cases hu : u.observe with
    | ret o =>
      have hEq : u = .ret o := by rw [← ITree.fold_observe u, hu]; rfl
      rw [hEq, ret_bind]; dsimp only [ITreeF.map]; rw [ITree.observe_tau]
      exact Or.inl rfl
    | tau u' =>
      have hEq : u = .tau u' := by rw [← ITree.fold_observe u, hu]; rfl
      rw [hEq, tau_bind]; dsimp only [ITreeF.map]; rw [ITree.observe_tau]
      exact Or.inr (Or.inr ⟨u', rfl, rfl⟩)
    | vis j k₂ =>
      have hEq : u = .vis j k₂ := by rw [← ITree.fold_observe u, hu]; rfl
      rw [hEq, vis_bind]; dsimp only [ITreeF.map]; rw [ITree.observe_vis]
      exact ⟨rfl, fun o₂ => Or.inr (Or.inr ⟨k₂ o₂, rfl, rfl⟩)⟩

@[simp]
theorem interpState_ret {E₁ E₂ : Effect.{u}} {S R : Type u}
    (h : (i : E₁.I) → S → ITree E₂ (E₁.O i × S)) (r : R) (s : S) :
    ITree.interpState h (.ret r) s = .ret (r, s) := by
  apply ITree.eq_of_observe_eq
  unfold ITree.interpState; rw [ITree.observe_cofix]; dsimp only [ITree.interpStateStep]
  rw [ITree.observe_ret]; rfl

@[simp]
theorem interpState_tau {E₁ E₂ : Effect.{u}} {S R : Type u}
    (h : (i : E₁.I) → S → ITree E₂ (E₁.O i × S)) (t : ITree E₁ R) (s : S) :
    ITree.interpState h (.tau t) s = .tau (ITree.interpState h t s) := by
  apply ITree.eq_of_observe_eq
  unfold ITree.interpState; rw [ITree.observe_cofix]; dsimp only [ITree.interpStateStep]
  rw [ITree.observe_tau]; dsimp only [ITreeF.map]; rw [ITree.observe_tau]

theorem interpState_vis {E₁ E₂ : Effect.{u}} {S R : Type u}
    (h : (i : E₁.I) → S → ITree E₂ (E₁.O i × S))
    (i : E₁.I) (k : E₁.O i → ITree E₁ R) (s : S) :
    ITree.interpState h (.vis i k) s =
      (h i s >>= fun (o, s') => .tau (ITree.interpState h (k o) s')) := by
  rw [← strongBisim_iff_eq]
  refine StrongBisim.coinduct
    (fun a b => a = b ∨
      (a = ITree.interpState h (.vis i k) s ∧
        b = (h i s >>= fun (o, s') => .tau (ITree.interpState h (k o) s'))) ∨
      ∃ u : ITree E₂ (E₁.O i × S),
        a = ITree.cofix (ITree.interpStateStep h) (.inr ⟨i, u, k⟩) ∧
        b = (u >>= fun (o, s') => .tau (ITree.interpState h (k o) s')))
    ?_ _ _ (Or.inr (Or.inl ⟨rfl, rfl⟩))
  intro a b hab
  rcases hab with rfl | ⟨rfl, rfl⟩ | ⟨u, rfl, rfl⟩
  · cases a.observe with
    | ret _ => rfl
    | tau _ => exact Or.inl rfl
    | vis _ _ => exact ⟨rfl, fun _ => Or.inl rfl⟩
  · unfold ITree.interpState
    rw [ITree.observe_cofix]; dsimp only [ITree.interpStateStep]; rw [ITree.observe_vis]; dsimp only
    cases hu : (h i s).observe with
    | ret os =>
      rcases os with ⟨o, s'⟩
      have hEq : h i s = .ret (o, s') := by rw [← ITree.fold_observe (h i s), hu]; rfl
      rw [hEq, ret_bind]; dsimp only [ITreeF.map]; rw [ITree.observe_tau]
      exact Or.inl rfl
    | tau u' =>
      have hEq : h i s = .tau u' := by rw [← ITree.fold_observe (h i s), hu]; rfl
      rw [hEq, tau_bind]; dsimp only [ITreeF.map]; rw [ITree.observe_tau]
      exact Or.inr (Or.inr ⟨u', rfl, rfl⟩)
    | vis j k₂ =>
      have hEq : h i s = .vis j k₂ := by rw [← ITree.fold_observe (h i s), hu]; rfl
      rw [hEq, vis_bind]; dsimp only [ITreeF.map]; rw [ITree.observe_vis]
      exact ⟨rfl, fun o₂ => Or.inr (Or.inr ⟨k₂ o₂, rfl, rfl⟩)⟩
  · rw [ITree.observe_cofix]; dsimp only [ITree.interpStateStep]
    cases hu : u.observe with
    | ret os =>
      rcases os with ⟨o, s'⟩
      have hEq : u = .ret (o, s') := by rw [← ITree.fold_observe u, hu]; rfl
      rw [hEq, ret_bind]; dsimp only [ITreeF.map]; rw [ITree.observe_tau]
      exact Or.inl rfl
    | tau u' =>
      have hEq : u = .tau u' := by rw [← ITree.fold_observe u, hu]; rfl
      rw [hEq, tau_bind]; dsimp only [ITreeF.map]; rw [ITree.observe_tau]
      exact Or.inr (Or.inr ⟨u', rfl, rfl⟩)
    | vis j k₂ =>
      have hEq : u = .vis j k₂ := by rw [← ITree.fold_observe u, hu]; rfl
      rw [hEq, vis_bind]; dsimp only [ITreeF.map]; rw [ITree.observe_vis]
      exact ⟨rfl, fun o₂ => Or.inr (Or.inr ⟨k₂ o₂, rfl, rfl⟩)⟩

/-! ## 2. `TauStar` Determinism and 2×2 Coinductive Refinement Hierarchy -/

theorem TauStar.trans {E : Effect.{u}} {R : Type u}
    {a b c : ITree E R} (h₁ : TauStar a b) (h₂ : TauStar b c) :
    TauStar a c := by
  induction h₁ with
  | refl => exact h₂
  | step htau _ ih => exact .step htau (ih h₂)

/-- Silent `.tau` transitions are confluent. -/
theorem TauStar.confluent {E : Effect.{u}} {R : Type u}
    {a b c : ITree E R} (h₁ : TauStar a b) (h₂ : TauStar a c) :
    TauStar b c ∨ TauStar c b := by
  induction h₁ generalizing c with
  | refl => exact Or.inl h₂
  | @step x x' y hx _ ih =>
    cases h₂ with
    | refl => exact Or.inr (.step hx ‹TauStar x' y›)
    | step hx₂ hrest =>
      rw [hx] at hx₂; injection hx₂ with heq; subst heq
      exact ih hrest

/-- At most one stabilized (`.ret` or `.vis`) node is reachable via `TauStar`. -/
theorem TauStar.unique_nonTau {E : Effect.{u}} {R : Type u}
    {a b c : ITree E R}
    (hb : TauStar a b) (hc : TauStar a c)
    (hnb : ∀ w, b.observe ≠ .tau w) (hnc : ∀ w, c.observe ≠ .tau w) :
    b = c := by
  rcases TauStar.confluent hb hc with hbc | hcb
  · cases hbc with
    | refl => rfl
    | step htau => exact False.elim (hnb _ htau)
  · cases hcb with
    | refl => rfl
    | step htau => exact False.elim (hnc _ htau)

theorem TauStar.bind {E : Effect.{u}} {R S : Type u}
    {t t' : ITree E R} (k : R → ITree E S) (h : TauStar t t') :
    TauStar (t >>= k) (t' >>= k) := by
  induction h with
  | refl => exact .refl _
  | @step a a' _ ha _ ih =>
    have htau : a = .tau a' := by rw [← ITree.fold_observe a, ha]; rfl
    rw [htau, tau_bind]
    exact .step (ITree.observe_tau _) ih

theorem Reaches.of_tauStar {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {a b c : ITree E R} {tr : List (Event E)}
    (h₁ : TauStar a b) (h₂ : Reaches b tr c) : Reaches a tr c := by
  induction h₁ with
  | refl => exact h₂
  | step htau _ ih => exact .tau htau (ih h₂)

theorem Diverges.of_tau {E : Effect.{u}} {R : Type u}
    {t t' : ITree E R} (ht : t.observe = .tau t') (hd : Diverges t) :
    Diverges t' := by
  rw [Diverges.eq_def, ht] at hd; exact hd

theorem Diverges.not_nonTau {E : Effect.{u}} {R : Type u}
    {t t' : ITree E R} (hd : Diverges t) (hs : TauStar t t')
    (hn : ∀ w, t'.observe ≠ .tau w) : False := by
  induction hs with
  | @refl u =>
    rw [Diverges.eq_def] at hd
    cases h : u.observe <;> rw [h] at hd
    · exact hd
    · exact hn _ h
    · exact hd
  | step htau _ ih => exact ih (Diverges.of_tau htau hd) hn

/-- Equivalence up to finite `.tau` transitions, preserving divergence. -/
def Eutt {E : Effect.{u}} {R : Type u} (t u : ITree E R) : Prop :=
  (∃ t' u' r, TauStar t t' ∧ TauStar u u' ∧
    t'.observe = .ret r ∧ u'.observe = .ret r) ∨
  (∃ t' u' i k₁ k₂, TauStar t t' ∧ TauStar u u' ∧
    t'.observe = .vis i k₁ ∧ u'.observe = .vis i k₂ ∧
    ∀ o, Eutt (k₁ o) (k₂ o)) ∨
  (∃ t' u', t.observe = .tau t' ∧ u.observe = .tau u' ∧ Eutt t' u')
coinductive_fixpoint

theorem Eutt.refl {E : Effect.{u}} {R : Type u} (t : ITree E R) :
    Eutt t t := by
  refine Eutt.coinduct (fun a b => a = b) ?_ t t rfl
  intro a b hab; subst hab
  cases ha : a.observe with
  | ret r => exact Or.inl ⟨a, a, r, .refl a, .refl a, ha, ha⟩
  | vis i k =>
    exact Or.inr (Or.inl ⟨a, a, i, k, k, .refl a, .refl a, ha, ha, fun _ => rfl⟩)
  | tau a' => exact Or.inr (Or.inr ⟨a', a', rfl, rfl, rfl⟩)

theorem Eutt.symm {E : Effect.{u}} {R : Type u} {t u : ITree E R}
    (h : Eutt t u) : Eutt u t := by
  refine Eutt.coinduct (fun a b => Eutt b a) ?_ u t h
  intro a b hba
  rw [Eutt.eq_def] at hba
  rcases hba with ⟨b', a', r, hb, ha, hbr, har⟩ |
    ⟨b', a', i, k₂, k₁, hb, ha, hbv, hav, hk⟩ | ⟨b', a', hb, ha, h'⟩
  · exact Or.inl ⟨a', b', r, ha, hb, har, hbr⟩
  · exact Or.inr (Or.inl ⟨a', b', i, k₁, k₂, ha, hb, hav, hbv, hk⟩)
  · exact Or.inr (Or.inr ⟨a', b', ha, hb, h'⟩)

theorem Eutt.tau_left {E : Effect.{u}} {R : Type u} (t : ITree E R) :
    Eutt (.tau t) t := by
  refine Eutt.coinduct (fun a b => a = b ∨ a = .tau b) ?_ (.tau t) t (Or.inr rfl)
  intro a b hab
  rcases hab with rfl | rfl
  · cases ha : a.observe with
    | ret r => exact Or.inl ⟨a, a, r, .refl a, .refl a, ha, ha⟩
    | vis i k =>
      exact Or.inr (Or.inl ⟨a, a, i, k, k, .refl a, .refl a, ha, ha, fun _ => Or.inl rfl⟩)
    | tau a' => exact Or.inr (Or.inr ⟨a', a', rfl, rfl, Or.inl rfl⟩)
  · cases hb : b.observe with
    | ret r =>
      exact Or.inl ⟨b, b, r, .step (ITree.observe_tau b) (.refl b), .refl b, hb, hb⟩
    | vis i k =>
      exact Or.inr (Or.inl ⟨b, b, i, k, k,
        .step (ITree.observe_tau b) (.refl b), .refl b, hb, hb, fun _ => Or.inl rfl⟩)
    | tau b' =>
      refine Or.inr (Or.inr ⟨b, b', ITree.observe_tau b, rfl, Or.inr ?_⟩)
      rw [← ITree.fold_observe b, hb]; rfl

theorem Eutt.tau_right {E : Effect.{u}} {R : Type u} (t : ITree E R) :
    Eutt t (.tau t) :=
  (Eutt.tau_left t).symm

/-- Shared one-step forward action simulation body. -/
def WeakSimBody {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (Rel : ITree E R → ITree E R → Prop) (a b : ITree E R) : Prop :=
  (∀ a' r, TauStar a a' → a'.observe = .ret r →
    ∃ b', TauStar b b' ∧ b'.observe = .ret r) ∧
  (∀ a' i k₁ (o : E.O i),
    TauStar a a' → a'.observe = .vis i k₁ → ¬ FaultEffect.isFault i →
      ∃ b' k₂, TauStar b b' ∧ b'.observe = .vis i k₂ ∧ Rel (k₁ o) (k₂ o))

@[partial_fixpoint_monotone]
theorem WeakSimBody.monotone_coind {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {α : Type _} [Lean.Order.PartialOrder α]
    (f : α → ITree E R → ITree E R → Lean.Order.ReverseImplicationOrder)
    (hf : Lean.Order.monotone f) (a b : ITree E R) :
    @Lean.Order.monotone _ _ _ Lean.Order.ReverseImplicationOrder.instOrder
      (fun x => WeakSimBody (f x) a b) := by
  intro x y hxy ⟨hret, hvis⟩
  exact ⟨hret, fun a' i k₁ o hs hv hnf =>
    let ⟨b', k₂, hsb, hvb, hr⟩ := hvis a' i k₁ o hs hv hnf
    ⟨b', k₂, hsb, hvb, hf x y hxy (k₁ o) (k₂ o) hr⟩⟩

/--
1. Naive weak forward simulation (`WeakSim`): both `fail` and `stuck` sit at `⊥`,
so `WeakSim (.fail err) (.ret r)` holds spuriously.
-/
def WeakSim {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (a b : ITree E R) : Prop :=
  WeakSimBody WeakSim a b
coinductive_fixpoint

/-- `t` can silently reach `.ret r` or an inhabited non-fault `.vis i k`. -/
def HasObservableAction {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (t : ITree E R) : Prop :=
  (∃ t' r, TauStar t t' ∧ t'.observe = .ret r) ∨
  (∃ t' i k, Nonempty (E.O i) ∧
    TauStar t t' ∧ t'.observe = .vis i k ∧ ¬ FaultEffect.isFault i)

/--
2. Complete weak similarity (`WeakCSim`, CTree-style): guards progress via
`¬ HasObservableAction a → ¬ HasObservableAction b`, preventing `stuck` from
refining active programs while still conflating `fail` and `stuck`.
-/
def WeakCSim {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (a b : ITree E R) : Prop :=
  (¬ HasObservableAction a → ¬ HasObservableAction b) ∧
  WeakSimBody WeakCSim a b
coinductive_fixpoint

/--
3. Smyth partial-correctness refinement (`WeakRef`):
when `¬ FaultNow b`, `a` must not fault now (`¬ FaultNow a`) and must simulate
`b`'s visible actions (`WeakSimBody`). Places `fail` at `⊤` and `stuck` at `⊥`.
-/
def WeakRef {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (a b : ITree E R) : Prop :=
  ¬ FaultNow b → ¬ FaultNow a ∧ WeakSimBody WeakRef a b
coinductive_fixpoint

/--
4. Divergence-sensitive Smyth total-correctness refinement (`TotalWeakRef`):
strengthens `WeakRef` with `Diverges a → Diverges b`.
-/
def TotalWeakRef {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (a b : ITree E R) : Prop :=
  ¬ FaultNow b →
    ¬ FaultNow a ∧ (Diverges a → Diverges b) ∧ WeakSimBody TotalWeakRef a b
coinductive_fixpoint

/-! ## 3. Algebraic Laws & Separation of the 2×2 Refinement Lattice -/

theorem WeakRef.refl {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (t : ITree E R) : WeakRef t t := by
  refine WeakRef.coinduct (fun a b => a = b) ?_ t t rfl
  intro a b hab hnb; subst hab
  exact ⟨hnb, ⟨fun a' r hs hr => ⟨a', hs, hr⟩,
    fun a' i k _ hs hv _ => ⟨a', k, hs, hv, rfl⟩⟩⟩

theorem WeakRef.trans {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {a b c : ITree E R} (h₁ : WeakRef a b) (h₂ : WeakRef b c) :
    WeakRef a c := by
  refine WeakRef.coinduct
    (fun x z => ∃ y, WeakRef x y ∧ WeakRef y z) ?_ a c ⟨b, h₁, h₂⟩
  intro x z ⟨y, hxy, hyz⟩ hnz
  rw [WeakRef.eq_def] at hxy hyz
  obtain ⟨hny, hret_yz, hvis_yz⟩ := hyz hnz
  obtain ⟨hnx, hret_xy, hvis_xy⟩ := hxy hny
  refine ⟨hnx, ?_, ?_⟩
  · intro x' r hs hr
    obtain ⟨y', hsy, hyr⟩ := hret_xy x' r hs hr
    exact hret_yz y' r hsy hyr
  · intro x' i k₁ o hs hv hnf
    obtain ⟨y', k₂, hsy, hyv, hrel₁⟩ := hvis_xy x' i k₁ o hs hv hnf
    obtain ⟨z', k₃, hsz, hzv, hrel₂⟩ := hvis_yz y' i k₂ o hsy hyv hnf
    exact ⟨z', k₃, hsz, hzv, ⟨k₂ o, hrel₁, hrel₂⟩⟩

theorem TotalWeakRef.refl {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (t : ITree E R) : TotalWeakRef t t := by
  refine TotalWeakRef.coinduct (fun a b => a = b) ?_ t t rfl
  intro a b hab hnb; subst hab
  exact ⟨hnb, id, ⟨fun a' r hs hr => ⟨a', hs, hr⟩,
    fun a' i k _ hs hv _ => ⟨a', k, hs, hv, rfl⟩⟩⟩

theorem TotalWeakRef.trans {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {a b c : ITree E R} (h₁ : TotalWeakRef a b) (h₂ : TotalWeakRef b c) :
    TotalWeakRef a c := by
  refine TotalWeakRef.coinduct
    (fun x z => ∃ y, TotalWeakRef x y ∧ TotalWeakRef y z) ?_ a c ⟨b, h₁, h₂⟩
  intro x z ⟨y, hxy, hyz⟩ hnz
  rw [TotalWeakRef.eq_def] at hxy hyz
  obtain ⟨hny, hdiv_yz, hret_yz, hvis_yz⟩ := hyz hnz
  obtain ⟨hnx, hdiv_xy, hret_xy, hvis_xy⟩ := hxy hny
  refine ⟨hnx, fun hd => hdiv_yz (hdiv_xy hd), ?_, ?_⟩
  · intro x' r hs hr
    obtain ⟨y', hsy, hyr⟩ := hret_xy x' r hs hr
    exact hret_yz y' r hsy hyr
  · intro x' i k₁ o hs hv hnf
    obtain ⟨y', k₂, hsy, hyv, hrel₁⟩ := hvis_xy x' i k₁ o hs hv hnf
    obtain ⟨z', k₃, hsz, hzv, hrel₂⟩ := hvis_yz y' i k₂ o hsy hyv hnf
    exact ⟨z', k₃, hsz, hzv, ⟨k₂ o, hrel₁, hrel₂⟩⟩

theorem TotalWeakRef.toWeakRef {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {a b : ITree E R} (h : TotalWeakRef a b) : WeakRef a b := by
  refine WeakRef.coinduct TotalWeakRef ?_ a b h
  intro x y hxy hny
  rw [TotalWeakRef.eq_def] at hxy
  obtain ⟨hnx, _, hbody⟩ := hxy hny
  exact ⟨hnx, hbody⟩

theorem faultNow_fail {Err : Type u} {E : Effect.{u}} {R : Type u}
    [FaultEffect E] [Subeffect (FailE Err) E] [LawfulSubeffect (FailE Err) E]
    (err : Err) :
    FaultNow (ITree.fail (E := E) (R := R) err) := by
  refine ⟨ITree.fail err, Subeffect.injReq (Sub := FailE Err) (.fail err),
    fun o => ITree.ret (Subeffect.projAns (Sub := FailE Err) (.fail err) o) >>=
      PEmpty.elim, .refl _, ?_, ?_⟩
  · unfold ITree.fail ITree.triggerSub; rw [vis_bind, ITree.observe_vis]
  · exact (LawfulSubeffect.isFault_injReq (Sub := FailE Err) (Sup := E)
      (.fail err)).mpr trivial

theorem not_faultNow_ret {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (r : R) : ¬ FaultNow (ITree.ret (E := E) r) := by
  rintro ⟨a', _, _, hs, hv, _⟩
  cases hs with
  | refl => rw [ITree.observe_ret] at hv; nomatch hv
  | step htau => rw [ITree.observe_ret] at htau; nomatch htau

/-- `ITree.fail err` is the top element `⊤` of `TotalWeakRef` and `WeakRef`. -/
theorem TotalWeakRef.fail_top {Err : Type u} {E : Effect.{u}} {R : Type u}
    [FaultEffect E] [Subeffect (FailE Err) E] [LawfulSubeffect (FailE Err) E]
    (err : Err) (t : ITree E R) :
    TotalWeakRef t (ITree.fail (E := E) err) := by
  rw [TotalWeakRef.eq_def]
  intro hnf; exact False.elim (hnf (faultNow_fail err))

theorem WeakRef.fail_top {Err : Type u} {E : Effect.{u}} {R : Type u}
    [FaultEffect E] [Subeffect (FailE Err) E] [LawfulSubeffect (FailE Err) E]
    (err : Err) (t : ITree E R) :
    WeakRef t (ITree.fail (E := E) err) :=
  (TotalWeakRef.fail_top err t).toWeakRef

theorem not_weakRef_fail_ret {Err : Type u} {E : Effect.{u}} {R : Type u}
    [FaultEffect E] [Subeffect (FailE Err) E] [LawfulSubeffect (FailE Err) E]
    (err : Err) (r : R) :
    ¬ WeakRef (ITree.fail (E := E) err) (.ret r) := by
  intro h; rw [WeakRef.eq_def] at h
  exact (h (not_faultNow_ret r)).1 (faultNow_fail err)

private theorem observe_stuck {E : Effect.{u}} {R : Type u}
    [Subeffect (PickE PEmpty) E] :
    (ITree.stuck (E := E) (R := R)).observe =
      .vis (Subeffect.injReq (Sub := PickE PEmpty) (PickReq.pick : (PickE PEmpty).I))
        (fun o => ITree.ret (Subeffect.projAns (Sub := PickE PEmpty)
          (PickReq.pick : (PickE PEmpty).I) o) >>= PEmpty.elim) :=
  (congrArg ITree.observe
    (vis_bind (Subeffect.injReq (Sub := PickE PEmpty) (PickReq.pick : (PickE PEmpty).I))
      _ PEmpty.elim)).trans (ITree.observe_vis _ _)

private theorem not_isFault_stuck_req {E : Effect.{u}}
    [FaultEffect E] [Subeffect (PickE PEmpty) E] [LawfulSubeffect (PickE PEmpty) E] :
    ¬ FaultEffect.isFault
      (Subeffect.injReq (Sub := PickE PEmpty) (Sup := E)
        (PickReq.pick : (PickE PEmpty).I)) :=
  fun hf => (LawfulSubeffect.isFault_injReq (Sub := PickE PEmpty) (Sup := E)
    (PickReq.pick : (PickE PEmpty).I)).mp hf

/-- `ITree.stuck` (`PickE PEmpty`) is the bottom element `⊥` of `TotalWeakRef` and `WeakRef`. -/
theorem TotalWeakRef.stuck_bot {E : Effect.{u}} {R : Type u}
    [FaultEffect E] [Subeffect (PickE PEmpty) E]
    [LawfulSubeffect (PickE PEmpty) E]
    (t : ITree E R) :
    TotalWeakRef (ITree.stuck (E := E)) t := by
  rw [TotalWeakRef.eq_def]
  have hObs := observe_stuck (E := E) (R := R)
  intro _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨a', _, _, hs, hv, hf⟩
    cases hs with
    | refl =>
      rw [hObs] at hv; injection hv with hi _; subst hi
      exact not_isFault_stuck_req hf
    | step htau => rw [hObs] at htau; nomatch htau
  · intro hd; rw [Diverges.eq_def, hObs] at hd; exact False.elim hd
  · intro a' r hs hr
    cases hs with
    | refl => rw [hObs] at hr; nomatch hr
    | step htau => rw [hObs] at htau; nomatch htau
  · intro a' i k₁ o hs hv _
    cases hs with
    | refl =>
      rw [hObs] at hv; injection hv with hi _; subst hi
      exact PEmpty.elim (Subeffect.projAns (Sub := PickE PEmpty)
        (PickReq.pick : (PickE PEmpty).I) o)
    | step htau => rw [hObs] at htau; nomatch htau

theorem WeakRef.stuck_bot {E : Effect.{u}} {R : Type u}
    [FaultEffect E] [Subeffect (PickE PEmpty) E]
    [LawfulSubeffect (PickE PEmpty) E]
    (t : ITree E R) :
    WeakRef (ITree.stuck (E := E)) t :=
  (TotalWeakRef.stuck_bot t).toWeakRef

/-- Naive `WeakSim` unsoundly places `ITree.fail err` at `⊥`! -/
theorem weakSim_fail_any {Err : Type u} {E : Effect.{u}} {R : Type u}
    [FaultEffect E] [Subeffect (FailE Err) E] [LawfulSubeffect (FailE Err) E]
    (err : Err) (t : ITree E R) :
    WeakSim (ITree.fail (E := E) err) t := by
  rw [WeakSim.eq_def]
  have hObs : (ITree.fail (E := E) (R := R) err).observe =
      .vis (Subeffect.injReq (Sub := FailE Err) (.fail err))
        (fun o => ITree.ret (Subeffect.projAns (Sub := FailE Err) (.fail err) o) >>=
          PEmpty.elim) := by
    unfold ITree.fail ITree.triggerSub; rw [vis_bind, ITree.observe_vis]
  refine ⟨fun a' r hs hr => ?_, fun a' i k₁ _ hs hv hnf => ?_⟩
  · cases hs with
    | refl => rw [hObs] at hr; nomatch hr
    | step htau => rw [hObs] at htau; nomatch htau
  · cases hs with
    | refl =>
      rw [hObs] at hv; injection hv with hi _; subst hi
      exact False.elim (hnf ((LawfulSubeffect.isFault_injReq
        (Sub := FailE Err) (Sup := E) (.fail err)).mpr trivial))
    | step htau => rw [hObs] at htau; nomatch htau

/-- `WeakCSim` rejects `stuck` refining `ret r`, yet conflates `fail` and `stuck`. -/
theorem not_weakCSim_stuck_ret {E : Effect.{u}} {R : Type u}
    [FaultEffect E] [Subeffect (PickE PEmpty) E]
    [LawfulSubeffect (PickE PEmpty) E]
    (r : R) :
    ¬ WeakCSim (ITree.stuck (E := E)) (.ret r) := by
  intro h; rw [WeakCSim.eq_def] at h
  have hObs := observe_stuck (E := E) (R := R)
  have hNoStuck : ¬ HasObservableAction (ITree.stuck (E := E) (R := R)) := by
    rintro (⟨t', r', hs, hr⟩ | ⟨t', i, k, ⟨o⟩, hs, hv, _⟩)
    · cases hs with
      | refl => rw [hObs] at hr; nomatch hr
      | step htau => rw [hObs] at htau; nomatch htau
    · cases hs with
      | refl =>
        rw [hObs] at hv; injection hv with hi _; subst hi
        exact PEmpty.elim (Subeffect.projAns (Sub := PickE PEmpty)
          (PickReq.pick : (PickE PEmpty).I) o)
      | step htau => rw [hObs] at htau; nomatch htau
  exact h.1 hNoStuck (Or.inl ⟨.ret r, r, .refl _, ITree.observe_ret r⟩)

theorem weakCSim_fail_stuck {Err : Type u} {E : Effect.{u}} {R : Type u}
    [FaultEffect E]
    [Subeffect (FailE Err) E] [LawfulSubeffect (FailE Err) E]
    [Subeffect (PickE PEmpty) E] [LawfulSubeffect (PickE PEmpty) E]
    (err : Err) :
    WeakCSim (ITree.fail (E := E) (R := R) err) ITree.stuck := by
  rw [WeakCSim.eq_def]
  have hFail : (ITree.fail (E := E) (R := R) err).observe =
      .vis (Subeffect.injReq (Sub := FailE Err) ((FailReq.fail err) : (FailE Err).I))
        (fun o => ITree.ret (Subeffect.projAns (Sub := FailE Err)
          ((FailReq.fail err) : (FailE Err).I) o) >>= PEmpty.elim) :=
    (congrArg ITree.observe
      (vis_bind (Subeffect.injReq (Sub := FailE Err) ((FailReq.fail err) : (FailE Err).I))
        _ PEmpty.elim)).trans (ITree.observe_vis _ _)
  have hStuck := observe_stuck (E := E) (R := R)
  refine ⟨fun _ => ?_, fun a' r hs hr => ?_, fun a' i k₁ _ hs hv hnf => ?_⟩
  · rintro (⟨t', r', hs, hr⟩ | ⟨t', i, k, ⟨o⟩, hs, hv, _⟩)
    · cases hs with
      | refl => rw [hStuck] at hr; nomatch hr
      | step htau => rw [hStuck] at htau; nomatch htau
    · cases hs with
      | refl =>
        rw [hStuck] at hv; injection hv with hi _; subst hi
        exact PEmpty.elim (Subeffect.projAns (Sub := PickE PEmpty)
          (PickReq.pick : (PickE PEmpty).I) o)
      | step htau => rw [hStuck] at htau; nomatch htau
  · cases hs with
    | refl => rw [hFail] at hr; nomatch hr
    | step htau => rw [hFail] at htau; nomatch htau
  · cases hs with
    | refl =>
      rw [hFail] at hv; injection hv with hi _; subst hi
      exact False.elim (hnf ((LawfulSubeffect.isFault_injReq
        (Sub := FailE Err) (Sup := E) (.fail err)).mpr trivial))
    | step htau => rw [hFail] at htau; nomatch htau

/-- Silent `spin` refines every tree under partial-correctness `WeakRef`. -/
theorem WeakRef.spin_bot {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (t : ITree E R) : WeakRef ITree.spin t := by
  rw [WeakRef.eq_def]; intro _
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, _, _, hs, hv, _⟩
    exact Diverges.not_nonTau spin_diverges hs (fun _ hw => by rw [hv] at hw; nomatch hw)
  · intro _ _ hs hr
    exact False.elim
      (Diverges.not_nonTau spin_diverges hs (fun _ hw => by rw [hr] at hw; nomatch hw))
  · intro _ _ _ _ hs hv _
    exact False.elim
      (Diverges.not_nonTau spin_diverges hs (fun _ hw => by rw [hv] at hw; nomatch hw))

/-- Under `TotalWeakRef`, `spin` does NOT refine `ret r`. -/
theorem not_spin_totalWeakRef_ret {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (r : R) : ¬ TotalWeakRef (ITree.spin (E := E)) (.ret r) := by
  intro h; rw [TotalWeakRef.eq_def] at h
  have hdiv : Diverges (ITree.ret (E := E) r) :=
    (h (not_faultNow_ret r)).2.1 spin_diverges
  rw [Diverges.eq_def, ITree.observe_ret] at hdiv; exact hdiv

private theorem eutt_step_nonTau {E : Effect.{u}} {R : Type u}
    {a a' b : ITree E R} (hs : TauStar a a') (he : Eutt a b) :
    (∀ r, a'.observe = .ret r → ∃ b', TauStar b b' ∧ b'.observe = .ret r) ∧
    (∀ i k₁, a'.observe = .vis i k₁ →
      ∃ b' k₂, TauStar b b' ∧ b'.observe = .vis i k₂ ∧
        ∀ o, Eutt (k₁ o) (k₂ o)) := by
  induction hs generalizing b with
  | @refl x =>
    rw [Eutt.eq_def] at he
    refine ⟨fun r hr => ?_, fun i k₁ hv => ?_⟩
    · rcases he with ⟨t', u', r', ht, hu, htr, hur⟩ |
        ⟨t', _, _, _, _, ht, _, htv, _, _⟩ | ⟨_, _, htau, _, _⟩
      · have hEq := TauStar.unique_nonTau (.refl x) ht
          (fun _ hw => by rw [hr] at hw; nomatch hw)
          (fun _ hw => by rw [htr] at hw; nomatch hw)
        subst hEq; rw [hr] at htr; injection htr with hrr; subst hrr
        exact ⟨u', hu, hur⟩
      · have hEq := TauStar.unique_nonTau (.refl x) ht
          (fun _ hw => by rw [hr] at hw; nomatch hw)
          (fun _ hw => by rw [htv] at hw; nomatch hw)
        subst hEq; rw [hr] at htv; nomatch htv
      · rw [hr] at htau; nomatch htau
    · rcases he with ⟨t', _, _, ht, _, htr, _⟩ |
        ⟨t', u', j, c₁, c₂, ht, hu, htv, huv, hk⟩ | ⟨_, _, htau, _, _⟩
      · have hEq := TauStar.unique_nonTau (.refl x) ht
          (fun _ hw => by rw [hv] at hw; nomatch hw)
          (fun _ hw => by rw [htr] at hw; nomatch hw)
        subst hEq; rw [hv] at htr; nomatch htr
      · have hEq := TauStar.unique_nonTau (.refl x) ht
          (fun _ hw => by rw [hv] at hw; nomatch hw)
          (fun _ hw => by rw [htv] at hw; nomatch hw)
        subst hEq; rw [hv] at htv; injection htv with hij hkc; subst hij
        have hkeq : k₁ = c₁ := eq_of_heq hkc; subst hkeq
        exact ⟨u', c₂, hu, huv, hk⟩
      · rw [hv] at htau; nomatch htau
  | @step x x' y hx _ ih =>
    rw [Eutt.eq_def] at he
    rcases he with ⟨t', u', r, ht, hu, htr, hur⟩ |
      ⟨t', u', j, c₁, c₂, ht, hu, htv, huv, hk⟩ | ⟨t', u', hx₂, hu, he'⟩
    · cases ht with
      | refl => rw [hx] at htr; nomatch htr
      | step hx₂ hrest =>
        rw [hx] at hx₂; injection hx₂ with hxx; subst hxx
        exact ih (by rw [Eutt.eq_def]; exact Or.inl ⟨t', u', r, hrest, hu, htr, hur⟩)
    · cases ht with
      | refl => rw [hx] at htv; nomatch htv
      | step hx₂ hrest =>
        rw [hx] at hx₂; injection hx₂ with hxx; subst hxx
        exact ih (by rw [Eutt.eq_def]; exact Or.inr (Or.inl ⟨t', u', j, c₁, c₂, hrest, hu, htv, huv, hk⟩))
    · rw [hx] at hx₂; injection hx₂ with hxx; subst hxx
      obtain ⟨ihRet, ihVis⟩ := ih he'
      exact ⟨fun r hr =>
          let ⟨b', hb', hbr⟩ := ihRet r hr
          ⟨b', .step hu hb', hbr⟩,
        fun i k₁ hv =>
          let ⟨b', k₂, hb', hbv, hk⟩ := ihVis i k₁ hv
          ⟨b', k₂, .step hu hb', hbv, hk⟩⟩

/-- `Eutt` embeds into `TotalWeakRef` (and hence into `WeakRef`). -/
theorem Eutt.toTotalWeakRef {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {a b : ITree E R} (h : Eutt a b) : TotalWeakRef a b := by
  refine TotalWeakRef.coinduct Eutt ?_ a b h
  intro x y hxy hny
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨x', i, k₁, hs, hv, hf⟩
    obtain ⟨y', k₂, hsy, hyv, _⟩ := (eutt_step_nonTau hs hxy).2 i k₁ hv
    exact hny ⟨y', i, k₂, hsy, hyv, hf⟩
  · intro hdiv
    refine Diverges.coinduct (fun w => ∃ v, Diverges v ∧ Eutt v w) ?_ y ⟨x, hdiv, hxy⟩
    intro w ⟨v, hdv, hvw⟩
    rw [Eutt.eq_def] at hvw
    rcases hvw with ⟨t', _, _, ht, _, htr, _⟩ |
      ⟨t', _, _, _, _, ht, _, htv, _, _⟩ | ⟨v', w', hv, hw, hvw'⟩
    · exact False.elim
        (Diverges.not_nonTau hdv ht (fun _ hw => by rw [htr] at hw; nomatch hw))
    · exact False.elim
        (Diverges.not_nonTau hdv ht (fun _ hw => by rw [htv] at hw; nomatch hw))
    · rw [hw]; exact ⟨v', Diverges.of_tau hv hdv, hvw'⟩
  · intro x' r hs hr
    exact (eutt_step_nonTau hs hxy).1 r hr
  · intro x' i k₁ o hs hv _
    obtain ⟨y', k₂, hsy, hyv, hk⟩ := (eutt_step_nonTau hs hxy).2 i k₁ hv
    exact ⟨y', k₂, hsy, hyv, hk o⟩

theorem Eutt.toWeakRef {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {a b : ITree E R} (h : Eutt a b) : WeakRef a b :=
  h.toTotalWeakRef.toWeakRef

/-! ## 4. Monadic `bind` Congruence and Layer 1A Soundness Bridges -/

private theorem tauStar_bind_inv {E : Effect.{u}} {R S : Type u}
    {t : ITree E R} {k : R → ITree E S} {w : ITree E S}
    (hs : TauStar (t >>= k) w) (hnw : ∀ z, w.observe ≠ .tau z) :
    (∃ t', TauStar t t' ∧ (∀ z, t'.observe ≠ .tau z) ∧
      (∀ r, t'.observe ≠ .ret r) ∧ w = (t' >>= k)) ∨
    (∃ t' r, TauStar t t' ∧ t'.observe = .ret r ∧ TauStar (k r) w) := by
  generalize hu : (t >>= k) = u at hs
  induction hs generalizing t with
  | refl =>
    subst hu
    cases ht : t.observe with
    | ret r =>
      have hEq : t = .ret r := by rw [← ITree.fold_observe t, ht]; rfl
      have hbind : (t >>= k) = k r := by rw [hEq, ret_bind]
      exact Or.inr ⟨t, r, .refl t, ht, hbind ▸ .refl _⟩
    | tau t' =>
      have hEq : t = .tau t' := by rw [← ITree.fold_observe t, ht]; rfl
      exfalso; apply hnw (t' >>= k)
      rw [hEq, tau_bind, ITree.observe_tau]
    | vis i c =>
      refine Or.inl ⟨t, .refl t, ?_, ?_, rfl⟩
      · intro z hz; rw [ht] at hz; nomatch hz
      · intro r hr; rw [ht] at hr; nomatch hr
  | @step u₁ u₂ w hu₁ hrest ih =>
    subst hu
    cases ht : t.observe with
    | ret r =>
      have hEq : t = .ret r := by rw [← ITree.fold_observe t, ht]; rfl
      have hbind : (t >>= k) = k r := by rw [hEq, ret_bind]
      rw [hbind] at hu₁
      exact Or.inr ⟨t, r, .refl t, ht, .step hu₁ hrest⟩
    | tau t' =>
      have hEq : t = .tau t' := by rw [← ITree.fold_observe t, ht]; rfl
      have hbind : (t >>= k) = .tau (t' >>= k) := by rw [hEq, tau_bind]
      rw [hbind, ITree.observe_tau] at hu₁
      injection hu₁ with hu₂
      rcases ih (t := t') hnw hu₂ with ⟨t'', hs', hnt, hnr, hw⟩ | ⟨t'', r, hs', htr, hkw⟩
      · exact Or.inl ⟨t'', .step ht hs', hnt, hnr, hw⟩
      · exact Or.inr ⟨t'', r, .step ht hs', htr, hkw⟩
    | vis i c =>
      have hEq : t = .vis i c := by rw [← ITree.fold_observe t, ht]; rfl
      have hbind : (t >>= k).observe = .vis i (fun o => c o >>= k) := by
        rw [hEq, vis_bind, ITree.observe_vis]
      rw [hbind] at hu₁; nomatch hu₁

/-- Monadic `bind` congruence for `WeakRef`. -/
theorem WeakRef.bind {E : Effect.{u}} {R S : Type u} [FaultEffect E]
    {t₁ t₂ : ITree E R} {k₁ k₂ : R → ITree E S}
    (ht : WeakRef t₁ t₂) (hk : ∀ r, WeakRef (k₁ r) (k₂ r)) :
    WeakRef (t₁ >>= k₁) (t₂ >>= k₂) := by
  refine WeakRef.coinduct
    (fun a b => WeakRef a b ∨
      ∃ x₁ x₂ : ITree E R, a = (x₁ >>= k₁) ∧ b = (x₂ >>= k₂) ∧ WeakRef x₁ x₂)
    ?_ _ _ (Or.inr ⟨t₁, t₂, rfl, rfl, ht⟩)
  intro a b hab hnb
  rcases hab with hdirect | ⟨x₁, x₂, rfl, rfl, hx⟩
  · rw [WeakRef.eq_def] at hdirect
    obtain ⟨hna, hret, hvis⟩ := hdirect hnb
    exact ⟨hna, hret, fun a' i c₁ o hs hv hnf =>
      let ⟨b', c₂, hsb, hvb, hr⟩ := hvis a' i c₁ o hs hv hnf
      ⟨b', c₂, hsb, hvb, Or.inl hr⟩⟩
  · have hnx₂ : ¬ FaultNow x₂ := by
      rintro ⟨x₂', i, c₂, hs₂, hv₂, hf⟩
      apply hnb
      refine ⟨x₂' >>= k₂, i, fun o => c₂ o >>= k₂, TauStar.bind k₂ hs₂, ?_, hf⟩
      rw [← ITree.fold_observe x₂', hv₂]; change (ITree.vis i c₂ >>= k₂).observe = _; simp
    rw [WeakRef.eq_def] at hx
    obtain ⟨hnx₁, hret_x, hvis_x⟩ := hx hnx₂
    have hnk₂_of_ret : ∀ {x₂' r}, TauStar x₂ x₂' → x₂'.observe = .ret r → ¬ FaultNow (k₂ r) := by
      intro x₂' r hs₂ hxr₂ ⟨u₂, j, cu₂, hsu₂, hvu₂, hfu₂⟩
      apply hnb
      have heq₂ : (x₂' >>= k₂) = k₂ r := by
        rw [← ITree.fold_observe x₂', hxr₂]; change (ITree.ret r >>= k₂) = _; simp
      exact ⟨u₂, j, cu₂, TauStar.trans (TauStar.bind k₂ hs₂) (heq₂ ▸ hsu₂), hvu₂, hfu₂⟩
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨w, i, cw, hsw, hvw, hfw⟩
      rcases tauStar_bind_inv hsw (fun z hz => by rw [hvw] at hz; nomatch hz) with
        ⟨x₁', hs₁, hnt, hnr, rfl⟩ | ⟨x₁', r, hs₁, hxr, hkw⟩
      · cases hx₁' : x₁'.observe with
        | ret r => exact hnr r hx₁'
        | tau z => exact hnt z hx₁'
        | vis j c₁ =>
          have : (x₁' >>= k₁).observe = .vis j (fun o => c₁ o >>= k₁) := by
            rw [← ITree.fold_observe x₁', hx₁']; change (ITree.vis j c₁ >>= k₁).observe = _; simp
          rw [this] at hvw; injection hvw with hij _; subst hij
          exact hnx₁ ⟨x₁', j, c₁, hs₁, hx₁', hfw⟩
      · obtain ⟨x₂', hs₂, hxr₂⟩ := hret_x x₁' r hs₁ hxr
        have hkr := hk r; rw [WeakRef.eq_def] at hkr
        exact (hkr (hnk₂_of_ret hs₂ hxr₂)).1 ⟨w, i, cw, hkw, hvw, hfw⟩
    · intro w s hsw hws
      rcases tauStar_bind_inv hsw (fun z hz => by rw [hws] at hz; nomatch hz) with
        ⟨x₁', _, hnt, hnr, rfl⟩ | ⟨x₁', r, hs₁, hxr, hkw⟩
      · cases hx₁' : x₁'.observe with
        | ret r => exact False.elim (hnr r hx₁')
        | tau z => exact False.elim (hnt z hx₁')
        | vis j c₁ =>
          have : (x₁' >>= k₁).observe = .vis j (fun o => c₁ o >>= k₁) := by
            rw [← ITree.fold_observe x₁', hx₁']; change (ITree.vis j c₁ >>= k₁).observe = _; simp
          rw [this] at hws; nomatch hws
      · obtain ⟨x₂', hs₂, hxr₂⟩ := hret_x x₁' r hs₁ hxr
        have hkr := hk r; rw [WeakRef.eq_def] at hkr
        obtain ⟨u₂, hsu₂, hur₂⟩ := (hkr (hnk₂_of_ret hs₂ hxr₂)).2.1 w s hkw hws
        have heq₂ : (x₂' >>= k₂) = k₂ r := by
          rw [← ITree.fold_observe x₂', hxr₂]; change (ITree.ret r >>= k₂) = _; simp
        exact ⟨u₂, TauStar.trans (TauStar.bind k₂ hs₂) (heq₂ ▸ hsu₂), hur₂⟩
    · intro w i cw o hsw hvw hnf
      rcases tauStar_bind_inv hsw (fun z hz => by rw [hvw] at hz; nomatch hz) with
        ⟨x₁', hs₁, hnt, hnr, rfl⟩ | ⟨x₁', r, hs₁, hxr, hkw⟩
      · cases hx₁' : x₁'.observe with
        | ret r => exact False.elim (hnr r hx₁')
        | tau z => exact False.elim (hnt z hx₁')
        | vis j c₁ =>
          have heq₁ : (x₁' >>= k₁).observe = .vis j (fun o => c₁ o >>= k₁) := by
            rw [← ITree.fold_observe x₁', hx₁']; change (ITree.vis j c₁ >>= k₁).observe = _; simp
          rw [heq₁] at hvw; injection hvw with hij hcw; subst hij
          have hcweq : cw = (fun o' => c₁ o' >>= k₁) := eq_of_heq hcw.symm; subst hcweq
          obtain ⟨x₂', c₂, hs₂, hxv₂, hrel⟩ := hvis_x x₁' j c₁ o hs₁ hx₁' hnf
          have heq₂ : (x₂' >>= k₂).observe = .vis j (fun o' => c₂ o' >>= k₂) := by
            rw [← ITree.fold_observe x₂', hxv₂]; change (ITree.vis j c₂ >>= k₂).observe = _; simp
          exact ⟨x₂' >>= k₂, fun o' => c₂ o' >>= k₂, TauStar.bind k₂ hs₂, heq₂,
            Or.inr ⟨c₁ o, c₂ o, rfl, rfl, hrel⟩⟩
      · obtain ⟨x₂', hs₂, hxr₂⟩ := hret_x x₁' r hs₁ hxr
        have hkr := hk r; rw [WeakRef.eq_def] at hkr
        obtain ⟨u₂, cu₂, hsu₂, hvu₂, hrel⟩ :=
          (hkr (hnk₂_of_ret hs₂ hxr₂)).2.2 w i cw o hkw hvw hnf
        have heq₂ : (x₂' >>= k₂) = k₂ r := by
          rw [← ITree.fold_observe x₂', hxr₂]; change (ITree.ret r >>= k₂) = _; simp
        exact ⟨u₂, cu₂, TauStar.trans (TauStar.bind k₂ hs₂) (heq₂ ▸ hsu₂), hvu₂, Or.inl hrel⟩

/-- Immediate fault makes `UBClosedPrefixes t` the literal top element `⊤`. -/
theorem ubClosedPrefixes_eq_top_of_faultNow {E : Effect.{u}} {R : Type u}
    [FaultEffect E] {t : ITree E R} (hf : FaultNow t) :
    ∀ p : TreePrefix E R, UBClosedPrefixes t p :=
  fun _ => Or.inr ⟨[], List.nil_prefix, ⟨t, .refl t, hf⟩⟩

/-- When `TreeSafe t` holds, `UBClosedPrefixes t` coincides with `HasTreePrefix t`. -/
theorem ubClosedPrefixes_eq_of_treeSafe {E : Effect.{u}} {R : Type u}
    [FaultEffect E] {t : ITree E R} (hs : TreeSafe t) :
    UBClosedPrefixes t = HasTreePrefix t := by
  funext p; apply propext
  refine ⟨fun h => ?_, Or.inl⟩
  rcases h with hp | ⟨tr₀, _, u, hreach, hf⟩
  · exact hp
  · exact False.elim (hs tr₀ u hreach hf)

theorem treeNoUBSpec_holds_ubClosedPrefixes_iff {E : Effect.{u}} {R : Type u}
    [FaultEffect E] (t : ITree E R) :
    (TreeNoUBSpec E R).holds (UBClosedPrefixes t) ↔ TreeSafe t := by
  refine ⟨fun h tr u hreach hf => ?_, fun hs p hp => ?_⟩
  · have hmem : UBClosedPrefixes t ⟨tr, .fault⟩ := Or.inl ⟨u, hreach, hf⟩
    exact h hmem
  · rw [ubClosedPrefixes_eq_of_treeSafe hs] at hp
    cases ho : p.outcome with
    | running => trivial
    | ret _ => trivial
    | fault =>
      simp only [HasTreePrefix, ho] at hp
      rcases hp with ⟨u, hreach, hf⟩
      exact hs p.trace u hreach hf

theorem reaches_trans {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {t u w : ITree E R} {tr₁ tr₂ : List (Event E)}
    (h₁ : Reaches t tr₁ u) (h₂ : Reaches u tr₂ w) :
    Reaches t (tr₁ ++ tr₂) w := by
  induction h₁ with
  | refl => simpa using h₂
  | tau htau _ ih => exact .tau htau (ih h₂)
  | vis hv hnf o _ ih => exact .vis hv hnf o (ih h₂)

theorem treeSafe_residual {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {t u : ITree E R} {tr : List (Event E)}
    (hs : TreeSafe t) (hr : Reaches t tr u) : TreeSafe u :=
  fun _ _ hr₂ => hs _ _ (reaches_trans hr hr₂)

theorem weakRef_tau_left {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {a a' b : ITree E R} (htau : a.observe = .tau a') (h : WeakRef a b) :
    WeakRef a' b :=
  WeakRef.trans (Eutt.tau_right _ |>.toWeakRef |> fun hr => by
    have heq : a = .tau a' := by rw [← ITree.fold_observe a, htau]; rfl
    exact heq ▸ hr) h

theorem weakRef_simulates_reaches {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {a a' b : ITree E R} {tr : List (Event E)}
    (href : WeakRef a b) (hsafe : TreeSafe b) (hr : Reaches a tr a') :
    ∃ b', Reaches b tr b' ∧ WeakRef a' b' := by
  induction hr generalizing b with
  | refl => exact ⟨b, .refl b, href⟩
  | @tau x x' _ _ htau _ ih =>
    exact ih (weakRef_tau_left htau href) hsafe
  | @vis x _ i k₁ _ hv hnf o _ ih =>
    have hnb : ¬ FaultNow b := hsafe [] b (.refl b)
    rw [WeakRef.eq_def] at href
    obtain ⟨_, _, hvis⟩ := href hnb
    obtain ⟨b₁, k₂, hsb₁, hvb₁, hrel⟩ := hvis x i k₁ o (.refl x) hv hnf
    have hreach_ko : Reaches b [⟨i, o⟩] (k₂ o) :=
      Reaches.of_tauStar hsb₁ (.vis hvb₁ hnf o (.refl _))
    obtain ⟨b', hrb', hrel'⟩ := ih hrel (treeSafe_residual hsafe hreach_ko)
    exact ⟨b', Reaches.of_tauStar hsb₁ (.vis hvb₁ hnf o hrb'), hrel'⟩

/-- Soundness of coinductive `WeakRef` with respect to Layer 1A `ITree.toPartial`. -/
theorem WeakRef.toPartial_le {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {a b : ITree E R} (href : WeakRef a b) :
    a.toPartial ≤ b.toPartial := by
  intro hsafe_b
  have hsafe_a : TreeSafe a := by
    intro tr a' hra
    obtain ⟨b', hrb', hrel'⟩ := weakRef_simulates_reaches href hsafe_b hra
    rw [WeakRef.eq_def] at hrel'
    exact (hrel' (hsafe_b tr b' hrb')).1
  refine ⟨hsafe_a, fun ⟨tr, r⟩ ⟨a', hra, har⟩ => ?_⟩
  obtain ⟨b₁, hrb₁, hrel₁⟩ := weakRef_simulates_reaches href hsafe_b hra
  rw [WeakRef.eq_def] at hrel₁
  obtain ⟨b', hsb', hbr'⟩ :=
    (hrel₁ (hsafe_b tr b₁ hrb₁)).2.1 a' r (.refl a') har
  have hreach_b' : Reaches b tr b' := by
    simpa using reaches_trans hrb₁ (Reaches.of_tauStar hsb' (.refl b'))
  exact ⟨b', hreach_b', hbr'⟩

/-- Soundness of coinductive `WeakRef` with respect to Layer 1A `ITree.toPrefixPartial`. -/
theorem WeakRef.toPrefixPartial_le {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {a b : ITree E R} (href : WeakRef a b) :
    a.toPrefixPartial ≤ b.toPrefixPartial := by
  intro hsafe_b
  obtain ⟨hsafe_a, hret_le⟩ := href.toPartial_le hsafe_b
  refine ⟨hsafe_a, fun p hp => ?_⟩
  cases ho : p.outcome with
  | running =>
    simp only [ITree.toPrefixPartial, HasTreePrefix, ho] at hp ⊢
    rcases hp with ⟨a', hra⟩
    obtain ⟨b', hrb', _⟩ := weakRef_simulates_reaches href hsafe_b hra
    exact ⟨b', hrb'⟩
  | ret r =>
    simp only [ITree.toPrefixPartial, HasTreePrefix, ho] at hp ⊢
    exact hret_le (p.trace, r) hp
  | fault =>
    simp only [ITree.toPrefixPartial, HasTreePrefix, ho] at hp
    rcases hp with ⟨a', hra, hfa⟩
    exact False.elim (hsafe_a p.trace a' hra hfa)

/-! ## 5. Infinite Executions, Temporal Modalities, and Infinite Streams -/

theorem productive_not_diverges {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {t : ITree E R} (hp : Productive t) : ¬ Diverges t := by
  intro hd
  obtain ⟨u', hs, hnt⟩ := hp [] t (.refl t)
  exact Diverges.not_nonTau hd hs hnt

theorem productive_not_mayDiverge {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {t : ITree E R} (hp : Productive t) : ¬ MayDiverge t := by
  rintro ⟨tr, u, hru, hdu⟩
  obtain ⟨u', hs, hnt⟩ := hp tr u hru
  exact Diverges.not_nonTau hdu hs hnt

/-- Coinductive safety/invariance modality ($\Box P$) over all finite & infinite paths. -/
def CoAlways {E : Effect.{u}} {R : Type u}
    (P : ITree E R → Prop) (t : ITree E R) : Prop :=
  P t ∧
    match t.observe with
    | .ret _ => True
    | .tau t' => CoAlways P t'
    | .vis _ k => ∀ o, CoAlways P (k o)
coinductive_fixpoint

theorem CoAlways.extract {E : Effect.{u}} {R : Type u}
    {P : ITree E R → Prop} {t : ITree E R} (h : CoAlways P t) : P t := by
  rw [CoAlways.eq_def] at h; exact h.1

theorem CoAlways.reaches {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {P : ITree E R → Prop} {t u : ITree E R} {tr : List (Event E)}
    (h : CoAlways P t) (hr : Reaches t tr u) : CoAlways P u := by
  induction hr with
  | refl => exact h
  | tau htau _ ih =>
    rw [CoAlways.eq_def, htau] at h; exact ih h.2
  | vis hv _ o _ ih =>
    rw [CoAlways.eq_def, hv] at h; exact ih (h.2 o)

/--
Inductive eventuality / liveness modality ($\Diamond P$) respecting demonic
vs. angelic `EffectOwner` quantification.
-/
inductive Eventually {E : Effect.{u}} {R : Type u}
    [EffectOwner E] [FaultEffect E] (P : ITree E R → Prop) :
    ITree E R → Prop where
  | here {t} : P t → Eventually P t
  | tau {t t'} : t.observe = .tau t' → Eventually P t' → Eventually P t
  | visDemonic {t i k} :
      t.observe = .vis i k →
      EffectOwner.owner i = .demonic →
      ¬ FaultEffect.isFault i →
      Nonempty (E.O i) →
      (∀ o, Eventually P (k o)) →
      Eventually P t
  | visAngelic {t i k} (o : E.O i) :
      t.observe = .vis i k →
      EffectOwner.owner i = .angelic →
      ¬ FaultEffect.isFault i →
      Eventually P (k o) →
      Eventually P t

/-- Coinductive Büchi liveness modality ($\Box\Diamond P$). -/
def InfinitelyOften {E : Effect.{u}} {R : Type u}
    [EffectOwner E] [FaultEffect E]
    (P : ITree E R → Prop) (t : ITree E R) : Prop :=
  CoAlways (Eventually P) t

/-- Infinite stream of values represented as `Nat → α`. -/
abbrev Stream' (α : Type u) : Type u := Nat → α

def Stream'.head {α : Type u} (s : Stream' α) : α := s 0
def Stream'.tail {α : Type u} (s : Stream' α) : Stream' α := fun n => s (n + 1)

/-- Coinductive infinite-trace correspondence between `t` and `s : Stream' α`. -/
def FollowsStream {α R : Type u}
    (t : ITree (ObsE α) R) (s : Stream' α) : Prop :=
  ∃ t' k,
    TauStar t t' ∧
    t'.observe = .vis (.emit (s.head)) k ∧
    FollowsStream (k PUnit.unit) s.tail
coinductive_fixpoint

/-- Infinite streams followed by a deterministic observation tree are unique. -/
theorem followsStream_deterministic {α R : Type u}
    {t : ITree (ObsE α) R} {s₁ s₂ : Stream' α}
    (h₁ : FollowsStream t s₁) (h₂ : FollowsStream t s₂) : s₁ = s₂ := by
  funext n
  induction n generalizing t s₁ s₂ with
  | zero =>
    rw [FollowsStream.eq_def] at h₁ h₂
    rcases h₁ with ⟨t₁, k₁, hs₁, hv₁, _⟩
    rcases h₂ with ⟨t₂, k₂, hs₂, hv₂, _⟩
    have hEq := TauStar.unique_nonTau hs₁ hs₂
      (fun _ hw => by rw [hv₁] at hw; nomatch hw)
      (fun _ hw => by rw [hv₂] at hw; nomatch hw)
    subst hEq
    rw [hv₁] at hv₂
    injection hv₂ with hem _; injection hem
  | succ m ih =>
    rw [FollowsStream.eq_def] at h₁ h₂
    rcases h₁ with ⟨t₁, k₁, hs₁, hv₁, hf₁⟩
    rcases h₂ with ⟨t₂, k₂, hs₂, hv₂, hf₂⟩
    have hEq := TauStar.unique_nonTau hs₁ hs₂
      (fun _ hw => by rw [hv₁] at hw; nomatch hw)
      (fun _ hw => by rw [hv₂] at hw; nomatch hw)
    subst hEq
    rw [hv₁] at hv₂
    injection hv₂ with _ hk
    subst hk
    exact ih hf₁ hf₂

/-! ## 6. Skolemized Environment Strategies & Foreign/ISA Bridge Contracts -/

/-- History-dependent environment strategy supplying answers to non-fault requests. -/
abbrev EnvStrategy (E : Effect.{u}) [FaultEffect E] : Type u :=
  List (Event E) → (i : E.I) → ¬ FaultEffect.isFault i → E.O i

/-- Default environment strategy for any `[InhabitedDemonic E]` effect signature. -/
noncomputable def EnvStrategy.default (E : Effect.{u})
    [FaultEffect E] [InhabitedDemonic E] : EnvStrategy E :=
  fun _ i hnf => Classical.choice (InhabitedDemonic.nonempty_of_nonFault i hnf)

/-- Execution reachability against a fixed deterministic environment strategy `σ`. -/
inductive ReachesWithStrategy {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (σ : EnvStrategy E) :
    List (Event E) → ITree E R → List (Event E) → ITree E R → Prop where
  | refl (hist : List (Event E)) (t : ITree E R) :
      ReachesWithStrategy σ hist t [] t
  | tau {hist tr} {t t' u : ITree E R} :
      t.observe = .tau t' →
      ReachesWithStrategy σ hist t' tr u →
      ReachesWithStrategy σ hist t tr u
  | vis {hist tr} {t u : ITree E R} {i : E.I} {k : E.O i → ITree E R}
      (hv : t.observe = .vis i k)
      (hnf : ¬ FaultEffect.isFault i) :
      ReachesWithStrategy σ (hist ++ [⟨i, σ hist i hnf⟩]) (k (σ hist i hnf)) tr u →
      ReachesWithStrategy σ hist t (⟨i, σ hist i hnf⟩ :: tr) u

theorem reaches_of_reachesWithStrategy {E : Effect.{u}} {R : Type u}
    [FaultEffect E] {σ : EnvStrategy E} {hist tr : List (Event E)}
    {t u : ITree E R} (h : ReachesWithStrategy σ hist t tr u) :
    Reaches t tr u := by
  induction h with
  | refl => exact .refl _
  | tau htau _ ih => exact .tau htau ih
  | vis hv hnf _ ih => exact .vis hv hnf _ ih

/--
Construct an explicit `EnvStrategy E` replaying `fullTrace` whenever requests
have decidable equality, falling back to `fallback` off-trace.
-/
def strategyOfTrace {E : Effect.{u}} [FaultEffect E] [DecidableEq E.I]
    (fallback : EnvStrategy E) (fullTrace : List (Event E)) : EnvStrategy E :=
  fun hist i hnf =>
    match fullTrace[hist.length]? with
    | some ev => if h : ev.req = i then h ▸ ev.ans else fallback hist i hnf
    | none => fallback hist i hnf

private theorem strategyOfTrace_hit {E : Effect.{u}} [FaultEffect E] [DecidableEq E.I]
    (fallback : EnvStrategy E) (hist suffix : List (Event E))
    (i : E.I) (o : E.O i) (hnf : ¬ FaultEffect.isFault i) :
    strategyOfTrace fallback (hist ++ ⟨i, o⟩ :: suffix) hist i hnf = o := by
  simp [strategyOfTrace]

private theorem reachesWithStrategy_replay {E : Effect.{u}} {R : Type u}
    [FaultEffect E] [DecidableEq E.I] (fallback : EnvStrategy E)
    {t u : ITree E R} {tr : List (Event E)} (hr : Reaches t tr u) :
    ∀ hist : List (Event E),
      ReachesWithStrategy (strategyOfTrace fallback (hist ++ tr)) hist t tr u := by
  induction hr with
  | refl t₀ => exact fun hist => .refl hist t₀
  | tau htau _ ih => exact fun hist => .tau htau (ih hist)
  | @vis _ u₀ i k tail hv hnf o _ ih =>
    intro hist
    let full := hist ++ ⟨i, o⟩ :: tail
    have hhit : strategyOfTrace fallback full hist i hnf = o :=
      strategyOfTrace_hit fallback hist tail i o hnf
    have hcont : ReachesWithStrategy (strategyOfTrace fallback full)
        (hist ++ [⟨i, o⟩]) (k o) tail u₀ := by
      have h := ih (hist ++ [⟨i, o⟩])
      rw [List.append_assoc] at h
      exact h
    have hstep : ReachesWithStrategy (strategyOfTrace fallback full)
        (hist ++ [⟨i, strategyOfTrace fallback full hist i hnf⟩])
        (k (strategyOfTrace fallback full hist i hnf)) tail u₀ := by
      simpa [hhit] using hcont
    have hvis := ReachesWithStrategy.vis
      (σ := strategyOfTrace fallback full) (hist := hist) hv hnf hstep
    simpa [hhit] using hvis

/--
Constructive Skolemization: for any effect `E` with `[DecidableEq E.I]` and a
fallback strategy `fallback`, existential trace reachability `Reaches t tr u`
holds iff some deterministic `EnvStrategy E` drives `t` to `u` along `tr`.
-/
theorem reaches_iff_exists_strategy {E : Effect.{u}} {R : Type u}
    [FaultEffect E] [DecidableEq E.I] (fallback : EnvStrategy E)
    {t u : ITree E R} {tr : List (Event E)} :
    Reaches t tr u ↔ ∃ σ : EnvStrategy E, ReachesWithStrategy σ [] t tr u :=
  ⟨fun hr => ⟨strategyOfTrace fallback tr, by simpa using reachesWithStrategy_replay fallback hr []⟩,
   fun ⟨_, hs⟩ => reaches_of_reachesWithStrategy hs⟩

/--
Classical Skolemization for any `[InhabitedDemonic E]` effect signature without
requiring decidable request equality.
-/
theorem reaches_iff_exists_strategy_inhabited {E : Effect.{u}} {R : Type u}
    [FaultEffect E] [InhabitedDemonic E]
    {t u : ITree E R} {tr : List (Event E)} :
    Reaches t tr u ↔ ∃ σ : EnvStrategy E, ReachesWithStrategy σ [] t tr u := by
  letI : DecidableEq E.I := Classical.typeDecidableEq E.I
  exact reaches_iff_exists_strategy (EnvStrategy.default E)

/--
Axiomatic pre/post specification of a foreign function or inline-assembly
boundary (`BridgeContract`).
-/
structure BridgeContract (State Obs : Type u) : Type u where
  /-- Safety precondition required upon entering the boundary. -/
  pre : State → Prop
  /-- Relational postcondition over `(preState, emittedObs, postState)`. -/
  post : State → Obs → State → Prop

/--
Interpret a `BridgeContract State Obs` directly as an `ITree E (Outcome State)`
over any open effect row `E` supporting `FailE FailureKind`,
`PickE (Obs × State)`, `PickE PEmpty`, and `ObsE Obs`:
- Violation of `B.pre s` faults via `ITree.fail .ub` (`⊤`).
- Satisfaction of `B.pre s` demonically picks `(obs, s')`; branches outside
  `B.post s obs s'` halt miraculously via `ITree.stuck` (`⊥`), while valid
  branches emit `obs` and return `.normal s'`.
-/
def bridgeTree {State Obs : Type} {E : Effect.{0}}
    [Subeffect (FailE FailureKind) E]
    [Subeffect (PickE (Obs × State)) E]
    [Subeffect (PickE PEmpty.{1}) E]
    [Subeffect (ObsE Obs) E]
    (B : BridgeContract State Obs)
    [∀ s, Decidable (B.pre s)]
    [∀ s obs s', Decidable (B.post s obs s')]
    (s : State) : ITree E (Outcome State) :=
  if B.pre s then do
    let (obs, s') ← ITree.pick (α := Obs × State) (E := E)
    if B.post s obs s' then
      ITree.emit (E := E) obs
      pure (.normal s')
    else
      ITree.stuck (E := E)
  else
    ITree.fail (E := E) FailureKind.ub

/--
Weakening preconditions and strengthening postconditions of a `BridgeContract`
yields a sound coinductive `WeakRef` refinement on `bridgeTree`.
-/
theorem BridgeContract.weakRef {State Obs : Type} {E : Effect.{0}}
    [FaultEffect E]
    [Subeffect (FailE FailureKind) E] [LawfulSubeffect (FailE FailureKind) E]
    [Subeffect (PickE (Obs × State)) E]
    [Subeffect (PickE PEmpty.{1}) E] [LawfulSubeffect (PickE PEmpty.{1}) E]
    [Subeffect (ObsE Obs) E]
    (B_low B_high : BridgeContract State Obs)
    [∀ s, Decidable (B_low.pre s)] [∀ s obs s', Decidable (B_low.post s obs s')]
    [∀ s, Decidable (B_high.pre s)] [∀ s obs s', Decidable (B_high.post s obs s')]
    (h_pre : ∀ s, B_high.pre s → B_low.pre s)
    (h_post : ∀ s obs s', B_high.pre s → B_low.post s obs s' → B_high.post s obs s')
    (s : State) :
    WeakRef (bridgeTree (E := E) B_low s) (bridgeTree (E := E) B_high s) := by
  unfold bridgeTree
  by_cases hp : B_high.pre s
  · simp only [hp, h_pre s hp, ↓reduceIte]
    refine WeakRef.bind (WeakRef.refl _) fun (obs, s') => ?_
    by_cases hq : B_low.post s obs s'
    · simp only [hq, h_post s obs s' hp hq, ↓reduceIte]
      exact WeakRef.refl _
    · simp only [hq, ↓reduceIte]
      exact WeakRef.stuck_bot _
  · simp only [hp, ↓reduceIte]
    exact WeakRef.fail_top FailureKind.ub _

end Anneal.ITree
