import Trusted
import Anneal.Refinement
import Anneal.Effect
import Anneal.ITree

namespace Anneal.Pass

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Anneal.Refinement
open Anneal.Effect
open Anneal.ITree

/-!
Coalgebraic interaction-tree machines (`ITreeMachine`), `List.filterMap`-based
cross-effect observation projections (`EffectObs`, `WeakObsRef`), certificate
checkers, and CFG forwarder elimination (`CFGSystem` and `.tau`-erasing
`TauCFGSystem`, `#99`, `#100`).

By projecting raw `List (Event E)` traces via Lean's standard `List.filterMap`
and `List.IsPrefix` (`<+:`) rather than duplicating operational transition
relations, cross-effect compiler passes, `.tau`-erasing optimizer passes, and
Layer 1A `Language` / `Semantics` adequacy follow concisely and compositionally.
-/

universe u u₁ u₂ u₃ v₁ v₂

/-! ## 1. Certificate-Checked Pass Validators -/

/-- Verified boolean certificate checker for a `VerifierPass`. -/
structure VerifiedVerifierChecker
    {Prog₁ : Type u₁} {Prog₂ : Type u₂} {Cert : Type u₃}
    {Beh₁ : Type v₁} {Beh₂ : Type v₂} [LE Beh₁] [LE Beh₂]
    (S₁ : Semantics Prog₁ Beh₁) (S₂ : Semantics Prog₂ Beh₂)
    (G₂ : Spec Beh₂) (π_v : Beh₂ → Beh₁)
    (check : Prog₁ → Prog₂ → Cert → Bool) : Prop where
  sound : ∀ {p₁ p₂ cert}, check p₁ p₂ cert = true →
    VerifierPass S₁ S₂ G₂ π_v p₁ p₂

/-- Verified boolean certificate checker for a `CompilerPass`. -/
structure VerifiedCompilerChecker
    {Prog₁ : Type u₁} {Prog₂ : Type u₂} {Cert : Type u₃}
    {Beh₁ : Type v₁} {Beh₂ : Type v₂} [LE Beh₁] [LE Beh₂]
    (S₁ : Semantics Prog₁ Beh₁) (S₂ : Semantics Prog₂ Beh₂)
    (G₁ : Spec Beh₁) (π_c : Beh₁ → Beh₂)
    (check : Prog₁ → Prog₂ → Cert → Bool) : Prop where
  sound : ∀ {p₁ p₂ cert}, check p₁ p₂ cert = true →
    CompilerPass S₁ S₂ G₁ π_c p₁ p₂

/-- Verified boolean certificate checker for an `ExactPass`. -/
structure VerifiedExactChecker
    {Prog₁ : Type u₁} {Prog₂ : Type u₂} {Cert : Type u₃}
    {Beh₁ : Type v₁} {Beh₂ : Type v₂} [LE Beh₁] [LE Beh₂]
    (S₁ : Semantics Prog₁ Beh₁) (S₂ : Semantics Prog₂ Beh₂)
    (π_fwd : Beh₁ → Beh₂) (π_bwd : Beh₂ → Beh₁)
    (check : Prog₁ → Prog₂ → Cert → Bool) : Prop where
  sound : ∀ {p₁ p₂ cert}, check p₁ p₂ cert = true →
    ExactPass S₁ S₂ π_fwd π_bwd p₁ p₂

theorem VerifiedExactChecker.toVerifierChecker
    {Prog₁ : Type u₁} {Prog₂ : Type u₂} {Cert : Type u₃}
    {Beh₁ : Type v₁} {Beh₂ : Type v₂} [LE Beh₁] [LE Beh₂]
    {S₁ : Semantics Prog₁ Beh₁} {S₂ : Semantics Prog₂ Beh₂}
    {π_fwd : Beh₁ → Beh₂} {π_bwd : Beh₂ → Beh₁}
    {check : Prog₁ → Prog₂ → Cert → Bool}
    (h : VerifiedExactChecker S₁ S₂ π_fwd π_bwd check) (G₂ : Spec Beh₂) :
    VerifiedVerifierChecker S₁ S₂ G₂ π_bwd check where
  sound hc := (h.sound hc).toVerifierPass G₂

theorem VerifiedExactChecker.toCompilerChecker
    {Prog₁ : Type u₁} {Prog₂ : Type u₂} {Cert : Type u₃}
    {Beh₁ : Type v₁} {Beh₂ : Type v₂} [LE Beh₁] [LE Beh₂]
    {S₁ : Semantics Prog₁ Beh₁} {S₂ : Semantics Prog₂ Beh₂}
    {π_fwd : Beh₁ → Beh₂} {π_bwd : Beh₂ → Beh₁}
    {check : Prog₁ → Prog₂ → Cert → Bool}
    (h : VerifiedExactChecker S₁ S₂ π_fwd π_bwd check) (G₁ : Spec Beh₁) :
    VerifiedCompilerChecker S₁ S₂ G₁ π_fwd check where
  sound hc := (h.sound hc).toCompilerPass G₁

/-! ## 2. Coalgebraic `ITreeMachine` and `List.filterMap` Observation Projection -/

/-- Coalgebraic machine unfolding `Prog` into `ITree E R` from `init p`. -/
structure ITreeMachine (Prog State : Type u) (E : Effect.{u}) (R : Type u) :
    Type (u + 1) where
  init : Prog → State
  step : Prog → State → ITreeF E R State

/-- Interaction tree unfolded from state `s` of program `p`. -/
def ITreeMachine.tree {Prog State : Type u} {E : Effect.{u}} {R : Type u}
    (M : ITreeMachine Prog State E R) (p : Prog) (s : State) : ITree E R :=
  ITree.cofix (M.step p) s

/-- Full interaction tree of program `p` starting at `M.init p`. -/
def ITreeMachine.run {Prog State : Type u} {E : Effect.{u}} {R : Type u}
    (M : ITreeMachine Prog State E R) (p : Prog) : ITree E R :=
  M.tree p (M.init p)

/-- Compositional per-event observation filter `Event E → Option Obs`. -/
structure EffectObs (E : Effect.{u}) (Obs : Type u) : Type u where
  obsOf : Event E → Option Obs

/-- Erase all events of `E` (`FailE`, `PickE`, `WitnessE`, internal `StateE`). -/
def EffectObs.erase (E : Effect.{u}) (Obs : Type u) : EffectObs E Obs :=
  ⟨fun _ => none⟩

/-- Project `ObsE Obs` events to `some ev`. -/
def EffectObs.emit (Obs : Type u) : EffectObs (ObsE Obs) Obs :=
  ⟨fun ev => match ev.req with | .emit x => some x⟩

/-- Coproduct of two `EffectObs` filters into a common `Obs` alphabet. -/
def EffectObs.sum {E₁ E₂ : Effect.{u}} {Obs : Type u}
    (p₁ : EffectObs E₁ Obs) (p₂ : EffectObs E₂ Obs) :
    EffectObs (SumE E₁ E₂) Obs where
  obsOf ev :=
    match ev with
    | ⟨.inl i₁, o₁⟩ => p₁.obsOf ⟨i₁, o₁⟩
    | ⟨.inr i₂, o₂⟩ => p₂.obsOf ⟨i₂, o₂⟩

/-- Projected execution prefix over observation alphabet `Obs` and return `R`. -/
structure ObsPrefix (Obs R : Type u) : Type u where
  trace : List Obs
  outcome : TreePrefixOutcome R
  deriving DecidableEq, Repr

/-- Raw projected prefix set of `t` via `List.filterMap proj.obsOf`. -/
def HasObsPrefix {E : Effect.{u}} {Obs R : Type u} [FaultEffect E]
    (proj : EffectObs E Obs) (t : ITree E R) :
    BehaviorSet (ObsPrefix Obs R) :=
  fun p =>
    match p.outcome with
    | .running => ∃ tr u, Reaches t tr u ∧ tr.filterMap proj.obsOf = p.trace
    | .ret r => ∃ tr, ReachesRet t tr r ∧ tr.filterMap proj.obsOf = p.trace
    | .fault =>
      ∃ tr u, Reaches t tr u ∧ FaultNow u ∧ tr.filterMap proj.obsOf = p.trace

/-- Prefix-preserving UB-closed projected behaviors via `List.IsPrefix` (`<+:`). -/
def UBClosedObsPrefixes {E : Effect.{u}} {Obs R : Type u} [FaultEffect E]
    (proj : EffectObs E Obs) (t : ITree E R) :
    BehaviorSet (ObsPrefix Obs R) :=
  fun p =>
    HasObsPrefix proj t p ∨
      ∃ tr₀, tr₀ <+: p.trace ∧ HasObsPrefix proj t ⟨tr₀, .fault⟩

/-- Canonical downward-closed safety specification on `ObsPrefix Obs R`. -/
def NoUBObsSpec (Obs R : Type u) : Spec (BehaviorSet (ObsPrefix Obs R)) :=
  BehaviorSet.allSpec (fun p => p.outcome.isSafe)

/-- Project `t : ITree E R` into Layer 1A's Smyth `Partial` domain over `ObsPrefix`. -/
def toObsPartial {E : Effect.{u}} {Obs R : Type u} [FaultEffect E]
    (proj : EffectObs E Obs) (t : ITree E R) :
    Partial (BehaviorSet (ObsPrefix Obs R)) where
  defined := TreeSafe t
  val _ := HasObsPrefix proj t

/-- UB-closed prefix `Semantics` of an `ITreeMachine`. -/
def MachineSemantics {Prog State : Type u} {E : Effect.{u}} [FaultEffect E]
    {Obs R : Type u} (M : ITreeMachine Prog State E R)
    (proj : EffectObs E Obs) : Semantics Prog (BehaviorSet (ObsPrefix Obs R)) :=
  fun p => UBClosedObsPrefixes proj (M.run p)

/-- Layer 1A `Language` packaging an `ITreeMachine` with `EffectObs`. -/
def ITreeMachine.toLanguage {Prog State Obs R : Type} {E : Effect.{0}}
    [FaultEffect E] (M : ITreeMachine Prog State E R)
    (proj : EffectObs E Obs) : Language where
  Prog := Prog
  Query := Unit
  Out := ObsPrefix Obs R
  sem p _ := toObsPartial proj (M.run p)

theorem ubClosedObsPrefixes_eq_of_treeSafe {E : Effect.{u}} {Obs R : Type u}
    [FaultEffect E] (proj : EffectObs E Obs) {t : ITree E R} (hs : TreeSafe t) :
    UBClosedObsPrefixes proj t = HasObsPrefix proj t := by
  funext p; apply propext
  refine ⟨fun h => ?_, Or.inl⟩
  rcases h with hp | ⟨tr₀, _, tr, u, hru, hfu, _⟩
  · exact hp
  · exact False.elim (hs tr u hru hfu)

theorem noUBObsSpec_holds_iff_treeSafe {E : Effect.{u}} {Obs R : Type u}
    [FaultEffect E] (proj : EffectObs E Obs) (t : ITree E R) :
    (NoUBObsSpec Obs R).holds (UBClosedObsPrefixes proj t) ↔ TreeSafe t := by
  refine ⟨fun h tr u hru hfu => ?_, fun hs p hp => ?_⟩
  · have hmem : UBClosedObsPrefixes proj t ⟨tr.filterMap proj.obsOf, .fault⟩ :=
      Or.inl ⟨tr, u, hru, hfu, rfl⟩
    exact h hmem
  · rw [ubClosedObsPrefixes_eq_of_treeSafe proj hs] at hp
    cases ho : p.outcome with
    | running => trivial
    | ret _ => trivial
    | fault =>
      simp only [HasObsPrefix, ho] at hp
      rcases hp with ⟨tr, u, hru, hfu, _⟩
      exact hs tr u hru hfu

/-- Non-vacuity: every `ITree` admits at least the safe initial running prefix. -/
theorem exists_safe_obsPrefix {E : Effect.{u}} {Obs R : Type u} [FaultEffect E]
    (proj : EffectObs E Obs) (t : ITree E R) :
    ∃ p : ObsPrefix Obs R, p.outcome.isSafe ∧ UBClosedObsPrefixes proj t p :=
  ⟨⟨[], .running⟩, trivial, Or.inl ⟨[], t, .refl t, rfl⟩⟩

/-! ## 3. Cross-Effect Coinductive Weak Refinement (`WeakObsRef`) & `Eutt` -/

/-- One-step body of cross-effect observation refinement. -/
def WeakObsBody {E₁ E₂ : Effect.{u}} {Obs R : Type u}
    [FaultEffect E₁] [FaultEffect E₂]
    (p₁ : EffectObs E₁ Obs) (p₂ : EffectObs E₂ Obs)
    (Rel : ITree E₁ R → ITree E₂ R → Prop)
    (a : ITree E₁ R) (b : ITree E₂ R) : Prop :=
  (∀ a' r, TauStar a a' → a'.observe = .ret r →
    ∃ tr₂ b', Reaches b tr₂ b' ∧ tr₂.filterMap p₂.obsOf = [] ∧
      b'.observe = .ret r) ∧
  (∀ a' i₁ k₁ (o₁ : E₁.O i₁),
    TauStar a a' → a'.observe = .vis i₁ k₁ → ¬ FaultEffect.isFault i₁ →
      ∃ tr₂ b', Reaches b tr₂ b' ∧
        tr₂.filterMap p₂.obsOf = (p₁.obsOf ⟨i₁, o₁⟩).toList ∧
        Rel (k₁ o₁) b')

@[partial_fixpoint_monotone]
theorem WeakObsBody.monotone_coind {E₁ E₂ : Effect.{u}} {Obs R : Type u}
    [FaultEffect E₁] [FaultEffect E₂]
    (p₁ : EffectObs E₁ Obs) (p₂ : EffectObs E₂ Obs)
    {α : Type _} [Lean.Order.PartialOrder α]
    (f : α → ITree E₁ R → ITree E₂ R → Lean.Order.ReverseImplicationOrder)
    (hf : Lean.Order.monotone f) (a : ITree E₁ R) (b : ITree E₂ R) :
    @Lean.Order.monotone _ _ _ Lean.Order.ReverseImplicationOrder.instOrder
      (fun x => WeakObsBody p₁ p₂ (f x) a b) := by
  intro x y hxy ⟨hret, hvis⟩
  exact ⟨hret, fun a' i₁ k₁ o₁ hs hv hnf =>
    let ⟨tr₂, b', hrb, htr, hr⟩ := hvis a' i₁ k₁ o₁ hs hv hnf
    ⟨tr₂, b', hrb, htr, hf x y hxy (k₁ o₁) b' hr⟩⟩

/--
Cross-effect Smyth partial refinement between `a : ITree E₁ R` and
`b : ITree E₂ R` modulo observation projections `p₁` and `p₂`.
-/
def WeakObsRef {E₁ E₂ : Effect.{u}} {Obs R : Type u}
    [FaultEffect E₁] [FaultEffect E₂]
    (p₁ : EffectObs E₁ Obs) (p₂ : EffectObs E₂ Obs)
    (a : ITree E₁ R) (b : ITree E₂ R) : Prop :=
  TreeSafe b → ¬ FaultNow a ∧ WeakObsBody p₁ p₂ (WeakObsRef p₁ p₂) a b
coinductive_fixpoint

/-- Same-effect `WeakRef` lifts directly to `WeakObsRef`. -/
theorem WeakObsRef.of_weakRef {E : Effect.{u}} {Obs R : Type u} [FaultEffect E]
    (proj : EffectObs E Obs) {a b : ITree E R} (h : WeakRef a b) :
    WeakObsRef proj proj a b := by
  refine WeakObsRef.coinduct proj proj WeakRef ?_ a b h
  intro x y hxy hsb
  have hny : ¬ FaultNow y := hsb [] y (.refl y)
  rw [WeakRef.eq_def] at hxy
  obtain ⟨hnx, hret, hvis⟩ := hxy hny
  refine ⟨hnx, ?_, ?_⟩
  · intro x' r hs hxr
    obtain ⟨y', hsy, hyr⟩ := hret x' r hs hxr
    exact ⟨[], y', Reaches.of_tauStar hsy (.refl y'), rfl, hyr⟩
  · intro x' i k₁ o hs hxv hnf
    obtain ⟨y₁, k₂, hsy, hyv, hrel⟩ := hvis x' i k₁ o hs hxv hnf
    refine ⟨[⟨i, o⟩], k₂ o,
      Reaches.of_tauStar hsy (.vis hyv hnf o (.refl _)), ?_, hrel⟩
    cases h : proj.obsOf ⟨i, o⟩ <;> simp [List.filterMap, h]

private theorem weakObsRef_tau_left {E₁ E₂ : Effect.{u}} {Obs R : Type u}
    [FaultEffect E₁] [FaultEffect E₂]
    {p₁ : EffectObs E₁ Obs} {p₂ : EffectObs E₂ Obs}
    {a a' : ITree E₁ R} {b : ITree E₂ R}
    (htau : a.observe = .tau a') (href : WeakObsRef p₁ p₂ a b) :
    WeakObsRef p₁ p₂ a' b := by
  rw [WeakObsRef.eq_def] at href ⊢
  intro hsb
  obtain ⟨hna, hret, hvis⟩ := href hsb
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨u, i, k, hsu, hvu, hfu⟩
    exact hna ⟨u, i, k, .step htau hsu, hvu, hfu⟩
  · intro u r hsu hur
    exact hret u r (.step htau hsu) hur
  · intro u i k o hsu hvu hnf
    exact hvis u i k o (.step htau hsu) hvu hnf

private theorem filterMap_cons_eq_toList_append {α β : Type u}
    (f : α → Option β) (x : α) (xs : List α) :
    (x :: xs).filterMap f = (f x).toList ++ xs.filterMap f := by
  cases h : f x <;> simp [List.filterMap, h]

private theorem weakObsRef_simulates_reaches {E₁ E₂ : Effect.{u}} {Obs R : Type u}
    [FaultEffect E₁] [FaultEffect E₂]
    {p₁ : EffectObs E₁ Obs} {p₂ : EffectObs E₂ Obs}
    {a a' : ITree E₁ R} {b : ITree E₂ R} {tr₁ : List (Event E₁)}
    (href : WeakObsRef p₁ p₂ a b) (hsb : TreeSafe b) (hra : Reaches a tr₁ a') :
    ∃ tr₂ b', Reaches b tr₂ b' ∧
      tr₂.filterMap p₂.obsOf = tr₁.filterMap p₁.obsOf ∧
      WeakObsRef p₁ p₂ a' b' := by
  induction hra generalizing b with
  | refl => exact ⟨[], b, .refl b, rfl, href⟩
  | @tau x x' _ _ htau _ ih =>
    exact ih (weakObsRef_tau_left htau href) hsb
  | @vis x _ i₁ k₁ _ hv hnf o₁ _ ih =>
    rw [WeakObsRef.eq_def] at href
    obtain ⟨_, _, hvis⟩ := href hsb
    obtain ⟨tr₂₁, b₁, hrb₁, htr₁, hrel₁⟩ := hvis x i₁ k₁ o₁ (.refl x) hv hnf
    obtain ⟨tr₂₂, b', hrb₂, htr₂, hrel'⟩ :=
      ih hrel₁ (treeSafe_residual hsb hrb₁)
    refine ⟨tr₂₁ ++ tr₂₂, b', reaches_trans hrb₁ hrb₂, ?_, hrel'⟩
    rw [List.filterMap_append, htr₁, htr₂, filterMap_cons_eq_toList_append]

/-- Soundness of `WeakObsRef` on Layer 1A Smyth `Partial` domains. -/
theorem WeakObsRef.toObsPartial_le {E₁ E₂ : Effect.{u}} {Obs R : Type u}
    [FaultEffect E₁] [FaultEffect E₂]
    {p₁ : EffectObs E₁ Obs} {p₂ : EffectObs E₂ Obs}
    {a : ITree E₁ R} {b : ITree E₂ R}
    (href : WeakObsRef p₁ p₂ a b) :
    toObsPartial p₁ a ≤ toObsPartial p₂ b := by
  intro hsb
  have hsa : TreeSafe a := by
    intro tr₁ a' hra
    obtain ⟨tr₂, b', hrb', _, hrel'⟩ := weakObsRef_simulates_reaches href hsb hra
    rw [WeakObsRef.eq_def] at hrel'
    exact (hrel' (treeSafe_residual hsb hrb')).1
  refine ⟨hsa, fun p hp => ?_⟩
  cases ho : p.outcome with
  | running =>
    simp only [toObsPartial, HasObsPrefix, ho] at hp ⊢
    rcases hp with ⟨tr₁, a', hra, htr⟩
    obtain ⟨tr₂, b', hrb', htr₂, _⟩ := weakObsRef_simulates_reaches href hsb hra
    exact ⟨tr₂, b', hrb', htr₂.trans htr⟩
  | ret r =>
    simp only [toObsPartial, HasObsPrefix, ho] at hp ⊢
    rcases hp with ⟨tr₁, ⟨a', hra, har⟩, htr⟩
    obtain ⟨tr₂₁, b₁, hrb₁, htr₁, hrel₁⟩ := weakObsRef_simulates_reaches href hsb hra
    rw [WeakObsRef.eq_def] at hrel₁
    obtain ⟨tr₂₂, b', hrb₂, htr₂, hbr⟩ :=
      (hrel₁ (treeSafe_residual hsb hrb₁)).2.1 a' r (.refl a') har
    refine ⟨tr₂₁ ++ tr₂₂, ⟨b', reaches_trans hrb₁ hrb₂, hbr⟩, ?_⟩
    rw [List.filterMap_append, htr₁, htr₂, List.append_nil, htr]
  | fault =>
    simp only [toObsPartial, HasObsPrefix, ho] at hp
    rcases hp with ⟨tr₁, a', hra, hfa, _⟩
    exact False.elim (hsa tr₁ a' hra hfa)

/-- Soundness of `WeakObsRef` on UB-closed `MachineSemantics`. -/
theorem WeakObsRef.ubClosedObsPrefixes_le {E₁ E₂ : Effect.{u}} {Obs R : Type u}
    [FaultEffect E₁] [FaultEffect E₂]
    {p₁ : EffectObs E₁ Obs} {p₂ : EffectObs E₂ Obs}
    {a : ITree E₁ R} {b : ITree E₂ R}
    (href : WeakObsRef p₁ p₂ a b)
    (hguard : (NoUBObsSpec Obs R).holds (UBClosedObsPrefixes p₂ b)) :
    UBClosedObsPrefixes p₁ a ≤ UBClosedObsPrefixes p₂ b := by
  have hsb : TreeSafe b := (noUBObsSpec_holds_iff_treeSafe p₂ b).mp hguard
  obtain ⟨hsa, hle⟩ := href.toObsPartial_le hsb
  rw [ubClosedObsPrefixes_eq_of_treeSafe p₁ hsa,
    ubClosedObsPrefixes_eq_of_treeSafe p₂ hsb]
  exact hle

/-- Cross-effect `CompilerPass` induced by `WeakObsRef (M_tgt.run q) (M_src.run p)`. -/
theorem compilerPass_of_weakObsRef
    {ProgSrc StateSrc ProgTgt StateTgt : Type u}
    {E_src E_tgt : Effect.{u}} [FaultEffect E_src] [FaultEffect E_tgt]
    {Obs R : Type u}
    (M_src : ITreeMachine ProgSrc StateSrc E_src R) (p_src : EffectObs E_src Obs)
    (M_tgt : ITreeMachine ProgTgt StateTgt E_tgt R) (p_tgt : EffectObs E_tgt Obs)
    {p : ProgSrc} {q : ProgTgt}
    (href : WeakObsRef p_tgt p_src (M_tgt.run q) (M_src.run p)) :
    CompilerPass (MachineSemantics M_src p_src) (MachineSemantics M_tgt p_tgt)
      (NoUBObsSpec Obs R) id p q :=
  fun hg => href.ubClosedObsPrefixes_le hg

/-- Cross-effect Layer 1A `Compiles` induced by `WeakObsRef`. -/
theorem compiles_of_weakObsRef
    {ProgSrc StateSrc ProgTgt StateTgt Obs R : Type}
    {E_src E_tgt : Effect.{0}} [FaultEffect E_src] [FaultEffect E_tgt]
    (M_src : ITreeMachine ProgSrc StateSrc E_src R) (p_src : EffectObs E_src Obs)
    (M_tgt : ITreeMachine ProgTgt StateTgt E_tgt R) (p_tgt : EffectObs E_tgt Obs)
    {p : ProgSrc} {q : ProgTgt}
    (href : WeakObsRef p_tgt p_src (M_tgt.run q) (M_src.run p)) :
    Compiles (M_src.toLanguage p_src) (M_tgt.toLanguage p_tgt) id p q :=
  fun _ => href.toObsPartial_le

/-- `VerifierPass` induced by `WeakRef (M_src.run p) (M_ver.run q)`. -/
theorem verifierPass_of_weakRef
    {ProgSrc StateSrc ProgVer StateVer : Type u}
    {E : Effect.{u}} [FaultEffect E] {Obs R : Type u}
    (M_src : ITreeMachine ProgSrc StateSrc E R)
    (M_ver : ITreeMachine ProgVer StateVer E R)
    (proj : EffectObs E Obs)
    {p : ProgSrc} {q : ProgVer}
    (href : WeakRef (M_src.run p) (M_ver.run q)) :
    VerifierPass (MachineSemantics M_src proj) (MachineSemantics M_ver proj)
      (NoUBObsSpec Obs R) id p q :=
  fun hg => (WeakObsRef.of_weakRef proj href).ubClosedObsPrefixes_le hg

private theorem eutt_simulates_reaches {E : Effect.{u}} {R : Type u}
    [FaultEffect E] {a a' b : ITree E R} {tr : List (Event E)}
    (hr : Reaches a tr a') (he : Eutt a b) :
    ∃ b', Reaches b tr b' ∧ Eutt a' b' := by
  induction hr generalizing b with
  | refl => exact ⟨b, .refl b, he⟩
  | @tau x x' _ _ htau _ ih =>
    rw [Eutt.eq_def] at he
    rcases he with ⟨t', u', r, ht, hu, htr, hur⟩ |
      ⟨t', u', i, k₁, k₂, ht, hu, htv, huv, hk⟩ | ⟨t', u', hx₂, hb, he'⟩
    · cases ht with
      | refl => rw [htau] at htr; nomatch htr
      | step hx₂ hrest =>
        rw [htau] at hx₂; injection hx₂ with hxx; subst hxx
        exact ih (by rw [Eutt.eq_def]; exact Or.inl ⟨t', u', r, hrest, hu, htr, hur⟩)
    · cases ht with
      | refl => rw [htau] at htv; nomatch htv
      | step hx₂ hrest =>
        rw [htau] at hx₂; injection hx₂ with hxx; subst hxx
        exact ih (by rw [Eutt.eq_def]; exact Or.inr (Or.inl ⟨t', u', i, k₁, k₂, hrest, hu, htv, huv, hk⟩))
    · rw [htau] at hx₂; injection hx₂ with hxx; subst hxx
      obtain ⟨b', hrb', he''⟩ := ih he'
      exact ⟨b', .tau hb hrb', he''⟩
  | @vis x _ i k₁ _ hv hnf o _ ih =>
    rw [Eutt.eq_def] at he
    rcases he with ⟨t', _, _, ht, _, htr, _⟩ |
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
      obtain ⟨b', hrb', he'⟩ := ih (hk o)
      exact ⟨b', Reaches.of_tauStar hu (.vis huv hnf o hrb'), he'⟩
    · rw [hv] at htau; nomatch htau

private theorem eutt_hasObsPrefix_le {E : Effect.{u}} {Obs R : Type u}
    [FaultEffect E] (proj : EffectObs E Obs) {a b : ITree E R} (he : Eutt a b) :
    HasObsPrefix proj a ≤ HasObsPrefix proj b := by
  intro p hp
  cases ho : p.outcome with
  | running =>
    simp only [HasObsPrefix, ho] at hp ⊢
    rcases hp with ⟨tr, a', hra, htr⟩
    obtain ⟨b', hrb', _⟩ := eutt_simulates_reaches hra he
    exact ⟨tr, b', hrb', htr⟩
  | ret r =>
    simp only [HasObsPrefix, ho] at hp ⊢
    rcases hp with ⟨tr, ⟨a', hra, har⟩, htr⟩
    obtain ⟨b₁, hrb₁, he₁⟩ := eutt_simulates_reaches hra he
    rw [Eutt.eq_def] at he₁
    rcases he₁ with ⟨t', u', r', ht, hu, htr', hur⟩ |
      ⟨t', _, _, _, _, ht, _, htv, _, _⟩ | ⟨_, _, htau, _, _⟩
    · have hEq := TauStar.unique_nonTau (.refl a') ht
        (fun _ hw => by rw [har] at hw; nomatch hw)
        (fun _ hw => by rw [htr'] at hw; nomatch hw)
      subst hEq; rw [har] at htr'; injection htr' with hrr; subst hrr
      refine ⟨tr, ⟨u', ?_, hur⟩, htr⟩
      simpa using reaches_trans hrb₁ (Reaches.of_tauStar hu (.refl u'))
    · have hEq := TauStar.unique_nonTau (.refl a') ht
        (fun _ hw => by rw [har] at hw; nomatch hw)
        (fun _ hw => by rw [htv] at hw; nomatch hw)
      subst hEq; rw [har] at htv; nomatch htv
    · rw [har] at htau; nomatch htau
  | fault =>
    simp only [HasObsPrefix, ho] at hp ⊢
    rcases hp with ⟨tr, a', hra, ⟨a'', i, k₁, hsa'', hva'', hfi⟩, htr⟩
    have hra'' : Reaches a tr a'' := by
      simpa using reaches_trans hra (Reaches.of_tauStar hsa'' (.refl a''))
    obtain ⟨b'', hrb'', he''⟩ := eutt_simulates_reaches hra'' he
    rw [Eutt.eq_def] at he''
    rcases he'' with ⟨t', _, _, ht, _, htr', _⟩ |
      ⟨t', u', j, _, c₂, ht, hu, htv, huv, _⟩ | ⟨_, _, htau, _, _⟩
    · have hEq := TauStar.unique_nonTau (.refl a'') ht
        (fun _ hw => by rw [hva''] at hw; nomatch hw)
        (fun _ hw => by rw [htr'] at hw; nomatch hw)
      subst hEq; rw [hva''] at htr'; nomatch htr'
    · have hEq := TauStar.unique_nonTau (.refl a'') ht
        (fun _ hw => by rw [hva''] at hw; nomatch hw)
        (fun _ hw => by rw [htv] at hw; nomatch hw)
      subst hEq; rw [hva''] at htv; injection htv with hij _; subst hij
      exact ⟨tr, b'', hrb'', ⟨u', i, c₂, hu, huv, hfi⟩, htr⟩
    · rw [hva''] at htau; nomatch htau

/-- `ExactPass` unconditionally induced by `Eutt (M₁.run p₁) (M₂.run p₂)`. -/
theorem exactPass_of_eutt
    {Prog₁ State₁ Prog₂ State₂ : Type u}
    {E : Effect.{u}} [FaultEffect E] {Obs R : Type u}
    (M₁ : ITreeMachine Prog₁ State₁ E R)
    (M₂ : ITreeMachine Prog₂ State₂ E R)
    (proj : EffectObs E Obs)
    {p₁ : Prog₁} {p₂ : Prog₂}
    (he : Eutt (M₁.run p₁) (M₂.run p₂)) :
    ExactPass (MachineSemantics M₁ proj) (MachineSemantics M₂ proj)
      id id p₁ p₂ where
  up_refines _ _ hp :=
    hp.elim (fun h => Or.inl (eutt_hasObsPrefix_le proj he _ h))
      (fun ⟨tr₀, hpre, hf⟩ => Or.inr ⟨tr₀, hpre, eutt_hasObsPrefix_le proj he _ hf⟩)
  down_refines _ _ hp :=
    hp.elim (fun h => Or.inl (eutt_hasObsPrefix_le proj he.symm _ h))
      (fun ⟨tr₀, hpre, hf⟩ => Or.inr ⟨tr₀, hpre, eutt_hasObsPrefix_le proj he.symm _ hf⟩)

/-! ## 4. Resolved-Label and `.tau`-Erasing CFG Forwarder Elimination -/

/-- Resolved-label CFG forwarder interface (`#99 §9`). -/
structure CFGSystem (Prog State : Type u) (E : Effect.{u}) (Val : Type u)
    (BlockId : Type) : Type (u + 1) where
  machine : ITreeMachine Prog State E (Outcome Val)
  pc : State → BlockId
  resolveLabel : Prog → BlockId → BlockId
  isForwarder : Prog → BlockId → BlockId → Prop
  redirectEdges : Prog → BlockId → BlockId → Prog

def PureJumpLaw {Prog State : Type u} {E : Effect.{u}} {Val : Type u}
    {BlockId : Type} (sys : CFGSystem Prog State E Val BlockId) : Prop :=
  ∀ p b c, b ≠ c → sys.isForwarder p b c →
    ∀ l, sys.resolveLabel (sys.redirectEdges p b c) l = sys.resolveLabel p l

def TargetLabelIndependenceLaw {Prog State : Type u} {E : Effect.{u}}
    {Val : Type u} {BlockId : Type}
    (sys : CFGSystem Prog State E Val BlockId) : Prop :=
  ∀ p b c, b ≠ c → sys.isForwarder p b c →
    sys.machine.init (sys.redirectEdges p b c) = sys.machine.init p

def PCDispatchLaw {Prog State : Type u} {E : Effect.{u}} {Val : Type u}
    {BlockId : Type} (sys : CFGSystem Prog State E Val BlockId) : Prop :=
  ∀ p b c, b ≠ c → sys.isForwarder p b c →
    (∀ l, sys.resolveLabel (sys.redirectEdges p b c) l = sys.resolveLabel p l) →
    ∀ s, sys.machine.step (sys.redirectEdges p b c) s = sys.machine.step p s

theorem tree_eq_of_step_eq {Prog State : Type u} {E : Effect.{u}} {R : Type u}
    (M : ITreeMachine Prog State E R) {p₁ p₂ : Prog}
    (hstep : ∀ s, M.step p₂ s = M.step p₁ s) (s : State) :
    M.tree p₂ s = M.tree p₁ s := by
  unfold ITreeMachine.tree; rw [funext hstep]

theorem eliminateForwarder_run_eq
    {Prog State : Type u} {E : Effect.{u}} {Val : Type u} {BlockId : Type}
    (sys : CFGSystem Prog State E Val BlockId)
    (hpure : PureJumpLaw sys) (hindep : TargetLabelIndependenceLaw sys)
    (hdispatch : PCDispatchLaw sys)
    (p : Prog) (b c : BlockId) (hne : b ≠ c) (hfwd : sys.isForwarder p b c) :
    sys.machine.run (sys.redirectEdges p b c) = sys.machine.run p := by
  unfold ITreeMachine.run
  rw [hindep p b c hne hfwd]
  exact tree_eq_of_step_eq sys.machine
    (hdispatch p b c hne hfwd (hpure p b c hne hfwd)) (sys.machine.init p)

theorem eliminateForwarder_exactPass
    {Prog State Obs Val : Type u} {E : Effect.{u}} [FaultEffect E]
    {BlockId : Type}
    (sys : CFGSystem Prog State E Val BlockId)
    (proj : EffectObs E Obs)
    (hpure : PureJumpLaw sys) (hindep : TargetLabelIndependenceLaw sys)
    (hdispatch : PCDispatchLaw sys)
    (p : Prog) (b c : BlockId) (hne : b ≠ c) (hfwd : sys.isForwarder p b c) :
    ExactPass (MachineSemantics sys.machine proj)
      (MachineSemantics sys.machine proj) id id
      p (sys.redirectEdges p b c) :=
  exactPass_of_eutt sys.machine sys.machine proj
    (eliminateForwarder_run_eq sys hpure hindep hdispatch p b c hne hfwd ▸
      Eutt.refl _)

/-- `.tau`-erasing CFG forwarder interface where `b ↦ goto c` steps via `.tau`. -/
structure TauCFGSystem (Prog State : Type u) (E : Effect.{u}) (Val : Type u)
    (BlockId : Type) : Type (u + 1) where
  machine : ITreeMachine Prog State E (Outcome Val)
  isForwarder : Prog → BlockId → BlockId → Prop
  redirectEdges : Prog → BlockId → BlockId → Prog
  retarget : BlockId → BlockId → State → State

/-- Coalgebraic laws for `.tau`-erasing forwarder elimination (`b ≠ c`). -/
structure TauForwarderLaw {Prog State : Type u} {E : Effect.{u}} {Val : Type u}
    {BlockId : Type} (sys : TauCFGSystem Prog State E Val BlockId) : Prop where
  init_eq : ∀ p b c, b ≠ c → sys.isForwarder p b c →
    sys.machine.init (sys.redirectEdges p b c) =
      sys.retarget b c (sys.machine.init p)
  retarget_idem : ∀ b c, b ≠ c → ∀ s,
    sys.retarget b c (sys.retarget b c s) = sys.retarget b c s
  forwarder_tau : ∀ p b c, b ≠ c → sys.isForwarder p b c → ∀ s,
    s = sys.retarget b c s ∨
      sys.machine.step p s = .tau (sys.retarget b c s)
  step_commutes : ∀ p b c, b ≠ c → sys.isForwarder p b c → ∀ s,
    sys.retarget b c s = s →
      sys.machine.step (sys.redirectEdges p b c) s =
        (sys.machine.step p s).map (sys.retarget b c)

/-- Eliminating a `.tau` forwarder block preserves the `ITree` up to `Eutt`. -/
theorem eliminateTauForwarder_eutt
    {Prog State : Type u} {E : Effect.{u}} {Val : Type u} {BlockId : Type}
    (sys : TauCFGSystem Prog State E Val BlockId) (law : TauForwarderLaw sys)
    (p : Prog) (b c : BlockId) (hne : b ≠ c) (hfwd : sys.isForwarder p b c) :
    Eutt (sys.machine.run p) (sys.machine.run (sys.redirectEdges p b c)) := by
  let r := sys.retarget b c
  let p' := sys.redirectEdges p b c
  have htau_r : ∀ s, TauStar (sys.machine.tree p s) (sys.machine.tree p (r s)) := by
    intro s
    rcases law.forwarder_tau p b c hne hfwd s with heq | hst
    · dsimp only [r]; rw [← heq]; exact .refl _
    · refine .step ?_ (.refl _)
      unfold ITreeMachine.tree; rw [ITree.observe_cofix, hst]; rfl
  refine Eutt.coinduct
    (fun t₁ t₂ => ∃ sr, r sr = sr ∧
      TauStar t₁ (sys.machine.tree p sr) ∧ t₂ = sys.machine.tree p' sr)
    ?_ _ _
    ⟨r (sys.machine.init p), law.retarget_idem b c hne _,
      htau_r _, congrArg (sys.machine.tree p') (law.init_eq p b c hne hfwd)⟩
  intro t₁ t₂ ⟨sr, hfix, htau, ht₂⟩; subst ht₂
  have hcomm := law.step_commutes p b c hne hfwd sr hfix
  cases hsp : sys.machine.step p sr with
  | ret out =>
    have h₁ : (sys.machine.tree p sr).observe = .ret out := by
      unfold ITreeMachine.tree; rw [ITree.observe_cofix, hsp]; rfl
    have h₂ : (sys.machine.tree p' sr).observe = .ret out := by
      unfold ITreeMachine.tree; rw [ITree.observe_cofix, hcomm, hsp]; rfl
    exact Or.inl ⟨_, _, out, htau, .refl _, h₁, h₂⟩
  | vis i k =>
    have h₁ : (sys.machine.tree p sr).observe =
        .vis i (fun o => sys.machine.tree p (k o)) := by
      unfold ITreeMachine.tree; rw [ITree.observe_cofix, hsp]; rfl
    have h₂ : (sys.machine.tree p' sr).observe =
        .vis i (fun o => sys.machine.tree p' (r (k o))) := by
      unfold ITreeMachine.tree; rw [ITree.observe_cofix, hcomm, hsp]; rfl
    exact Or.inr (Or.inl ⟨_, _, i, _, _, htau, .refl _, h₁, h₂,
      fun o => ⟨r (k o), law.retarget_idem b c hne (k o), htau_r (k o), rfl⟩⟩)
  | tau s_next =>
    have h₁ : (sys.machine.tree p sr).observe =
        .tau (sys.machine.tree p s_next) := by
      unfold ITreeMachine.tree; rw [ITree.observe_cofix, hsp]; rfl
    have h₂ : (sys.machine.tree p' sr).observe =
        .tau (sys.machine.tree p' (r s_next)) := by
      unfold ITreeMachine.tree; rw [ITree.observe_cofix, hcomm, hsp]; rfl
    cases htau with
    | refl =>
      exact Or.inr (Or.inr ⟨_, _, h₁, h₂,
        ⟨r s_next, law.retarget_idem b c hne s_next, htau_r s_next, rfl⟩⟩)
    | step ht₁ hrest =>
      exact Or.inr (Or.inr ⟨_, _, ht₁, h₂,
        ⟨r s_next, law.retarget_idem b c hne s_next,
          TauStar.trans hrest (.step h₁ (htau_r s_next)), rfl⟩⟩)

theorem eliminateTauForwarder_exactPass
    {Prog State Obs Val : Type u} {E : Effect.{u}} [FaultEffect E]
    {BlockId : Type}
    (sys : TauCFGSystem Prog State E Val BlockId) (proj : EffectObs E Obs)
    (law : TauForwarderLaw sys)
    (p : Prog) (b c : BlockId) (hne : b ≠ c) (hfwd : sys.isForwarder p b c) :
    ExactPass (MachineSemantics sys.machine proj)
      (MachineSemantics sys.machine proj) id id
      p (sys.redirectEdges p b c) :=
  exactPass_of_eutt sys.machine sys.machine proj
    (eliminateTauForwarder_eutt sys law p b c hne hfwd)

end Anneal.Pass
