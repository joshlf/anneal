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

Sections 5–8 instantiate gap-preserving equivalence
(`Anneal.Refinement.ContextEquiv`) on `ITreeF` coalgebras and `MirStepNode`:
gap-aware outcome classification (`ExecFault`, `GapTag`), fuel-indexed stepping
(`runStepsWithGap`, `runMirStepsWithGap`), multi-step and call-handler
congruence, certificate checkers (`VerifiedContextChecker`), and adequacy for
the interaction tree unfolded by `ITree.cofix`.
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

universe w₁ w₂ w₃ w₄ w₅ w₆ w₇

/-! ## 5. Gap-Aware Outcome Classification and Fuel-Indexed Stepping

Bounded evaluation of an `ITreeF` coalgebra into `OutcomeWithGap`, keeping three
kinds of non-value results apart:

- `ExecFault.ub`: undefined behavior (`FailureKind.ub`);
- `ExecFault.panic` / `ExecFault.abort`: *defined* runtime failures
  (`Outcome.panic` / `Outcome.abort`), never identified with UB;
- `GapTag`: modeling and budget gaps of the interpreter
  (`FailureKind.unsupported`, `FailureKind.outOfFuel`, unresolved callees, and
  the evaluator's own exhausted fuel), which always become `.gap` and never
  `.ok` or `.fault`.
-/

/-- Runtime faults of an execution: undefined behavior or a defined failure. -/
inductive ExecFault : Type where
  /-- Undefined behavior (`FailureKind.ub`). -/
  | ub
  /-- Defined unwinding panic (`Outcome.panic`). -/
  | panic
  /-- Defined process abort (`Outcome.abort`). -/
  | abort
  deriving DecidableEq

/-- `.ub` is undefined behavior; `.panic` and `.abort` are defined failures. -/
def ExecFault.isUB : ExecFault → Prop
  | .ub => True
  | .panic => False
  | .abort => False

instance ExecFault.instDecidableIsUB : (e : ExecFault) → Decidable e.isUB
  | .ub => isTrue trivial
  | .panic => isFalse (fun h => h)
  | .abort => isFalse (fun h => h)

/--
Modeling and budget gaps of the interpreter. `unsupported`, `budget` and
`unresolved` carry the site (for MIR, the `DefPath` of the body being executed
or of the unresolved callee), so gaps reached at different sites are different
gaps.

`outOfFuel` is reserved for the budget of the bounded evaluator itself (or of a
handler whose budget grows with it): it is the only gap that a larger `fuel`
can lift, and the fuel-free semantics `gapBehaviors` does not report it.
-/
inductive GapTag (Site : Type u) : Type u where
  /-- Fail-closed unmodeled construct reached while executing `site`. -/
  | unsupported (site : Site)
  /-- The stepped machine itself reported an exhausted budget at `site`. -/
  | budget (site : Site)
  /-- Call to `site` that the callee environment does not resolve. -/
  | unresolved (site : Site)
  /-- The evaluator's own step budget ran out before the execution finished. -/
  | outOfFuel
  deriving DecidableEq

/--
Seal an inner evaluator's `GapTag.outOfFuel` into a site-tagged `GapTag.budget`
so that a fixed-budget callee summary never collides with the outer evaluator's
own `outOfFuel` sentinel.
-/
def GapTag.sealOutOfFuel {Site : Type u} (site : Site) : GapTag Site → GapTag Site
  | .outOfFuel => .budget site
  | g => g

theorem GapTag.sealOutOfFuel_ne_outOfFuel {Site : Type u} (site : Site)
    (g : GapTag Site) : g.sealOutOfFuel site ≠ .outOfFuel := by
  cases g <;> exact fun h => by cases h

theorem GapTag.sealOutOfFuel_idem {Site : Type u} (site : Site)
    (g : GapTag Site) : (g.sealOutOfFuel site).sealOutOfFuel site = g.sealOutOfFuel site := by
  cases g <;> rfl

theorem GapTag.sealOutOfFuel_eq_self {Site : Type u} (site : Site) {g : GapTag Site}
    (hne : g ≠ .outOfFuel) : g.sealOutOfFuel site = g := by
  cases g with
  | outOfFuel => exact False.elim (hne rfl)
  | unsupported _ => rfl
  | budget _ => rfl
  | unresolved _ => rfl

/-- Classify a defined halting `Outcome`: never a gap and never UB. -/
def classifyOutcome {Gap : Type u₁} {Val : Type u₂} :
    Outcome Val → OutcomeWithGap ExecFault Gap Val
  | .normal v => .ok v
  | .panic => .fault .panic
  | .abort => .fault .abort

/--
Classify an operational `FailureKind` raised at `site`: `.ub` is the runtime
fault `ExecFault.ub`, while `.unsupported` and `.outOfFuel` are site-tagged
gaps. A failure raised by the stepped machine is never the evaluator's own
`GapTag.outOfFuel`, so it stays visible in the fuel-free semantics.
-/
def classifyFailure {Site : Type u₁} {Val : Type u₂} (site : Site) :
    FailureKind → OutcomeWithGap ExecFault (GapTag Site) Val
  | .ub => .fault .ub
  | .unsupported => .gap (.unsupported site)
  | .outOfFuel => .gap (.budget site)

theorem classifyOutcome_isGapFree {Gap : Type u₁} {Val : Type u₂}
    (out : Outcome Val) :
    (classifyOutcome (Gap := Gap) out).isGapFree := by
  cases out <;> exact trivial

/-- Defined halting outcomes are defined: a panic or abort is never UB. -/
theorem classifyOutcome_isDefined {Gap : Type u₁} {Val : Type u₂}
    (out : Outcome Val) :
    (classifyOutcome (Gap := Gap) out).isDefined ExecFault.isUB := by
  cases out with
  | normal v => exact trivial
  | panic => exact fun h => h
  | abort => exact fun h => h

theorem classifyOutcome_ne_ub {Gap : Type u₁} {Val : Type u₂}
    (out : Outcome Val) :
    classifyOutcome (Gap := Gap) out ≠ .fault .ub := by
  cases out <;> exact fun h => by cases h

theorem classifyOutcome_injective {Gap : Type u₁} {Val : Type u₂}
    {out₁ out₂ : Outcome Val}
    (h : classifyOutcome (Gap := Gap) out₁ = classifyOutcome out₂) :
    out₁ = out₂ := by
  cases out₁ <;> cases out₂ <;> first | rfl | (cases h; rfl) | cases h

/--
Every defined `ExecFault` outcome (`isDefined ExecFault.isUB`) is the
classification of a unique defined `Outcome Val`.
-/
theorem exists_classifyOutcome_of_isDefined {Gap : Type u₁} {Val : Type u₂}
    {o : OutcomeWithGap ExecFault Gap Val} (h : o.isDefined ExecFault.isUB) :
    ∃ out : Outcome Val, o = classifyOutcome out := by
  cases o with
  | ok v => exact ⟨.normal v, rfl⟩
  | fault e =>
    cases e with
    | ub => exact False.elim (h trivial)
    | panic => exact ⟨.panic, rfl⟩
    | abort => exact ⟨.abort, rfl⟩
  | gap g => exact False.elim h

/--
Gap- and UB-erased Layer 1A projection of an `ExecFault` behavior set directly
into `Partial (BehaviorSet (Outcome Val))`: defined precisely when the set has
no gaps and no UB faults, and preserving `.normal`, `.panic`, and `.abort`.
-/
def OutcomeSet.toOutcomePartial {Gap : Type u₁} {Val : Type u₂}
    (S : OutcomeSet ExecFault Gap Val) :
    Partial (BehaviorSet (Outcome Val)) where
  defined := OutcomeSet.Defined ExecFault.isUB S
  val _ out := S (classifyOutcome out)

/-- Layer 1A `Outcome Val` semantics erasing both `Gap` and `.ub`. -/
def outcomeSemantics {Prog : Type u₁} {Query : Type u} {Gap : Type u₂}
    {Val : Type u₃} (sem : Prog → GapSem Query ExecFault Gap Val) :
    Semantics Prog (Query → Partial (BehaviorSet (Outcome Val))) :=
  fun p q => OutcomeSet.toOutcomePartial (sem p q)

/-- Layer 1A `Language` projecting `ExecFault` gap-aware semantics to `Outcome Val`. -/
def outcomeLanguage {Prog Query Gap Val : Type}
    (sem : Prog → GapSem Query ExecFault Gap Val) : Language where
  Prog := Prog
  Query := Query
  Out := Outcome Val
  sem p q := OutcomeSet.toOutcomePartial (sem p q)

theorem ContextEquiv.toOutcomeExactPass_eq {Prog₁ : Type u₁} {Prog₂ : Type u₂}
    {Query : Type u} {Gap : Type w₁} {Val : Type w₂}
    {sem₁ : Prog₁ → GapSem Query ExecFault Gap Val}
    {sem₂ : Prog₂ → GapSem Query ExecFault Gap Val}
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ContextEquiv (· = ·) (· = ·) (sem₁ p₁) (sem₂ p₂)) :
    ExactPass (outcomeSemantics sem₁) (outcomeSemantics sem₂) id id p₁ p₂ where
  up_refines _ q h₂ :=
    ⟨((h q).defined_iff (fun _ _ he => he ▸ Iff.rfl)).mpr h₂,
     fun out hout => (h q).subset_of_eq (classifyOutcome out) hout⟩
  down_refines _ q h₁ :=
    ⟨((h q).defined_iff (fun _ _ he => he ▸ Iff.rfl)).mp h₁,
     fun out hout => (h q).superset_of_eq (classifyOutcome out) hout⟩

private theorem forbid_toOutcomePartial_le {Gap₁ : Type w₁} {Gap₂ : Type w₂}
    {Val : Type w₃}
    {S₁ : OutcomeSet ExecFault Gap₁ Val} {S₂ : OutcomeSet ExecFault Gap₂ Val}
    (h : OutcomeSetEquiv (GapForbidEq (· = ·) (· = ·)) S₁ S₂) :
    OutcomeSet.toOutcomePartial S₂ ≤ OutcomeSet.toOutcomePartial S₁ := by
  intro h₁
  have h₂ : OutcomeSet.Defined ExecFault.isUB S₂ := by
    intro o₂ ho₂
    obtain ⟨o₁, ho₁, hr⟩ := h.backward ho₂
    exact (hr.isDefined_iff (fun _ _ he => he ▸ Iff.rfl)).mp (h₁ ho₁)
  refine ⟨h₂, fun out hout => ?_⟩
  obtain ⟨o₁, ho₁, hr⟩ := h.backward hout
  obtain ⟨out₁, rfl⟩ := exists_classifyOutcome_of_isDefined (h₁ ho₁)
  have heq : out₁ = out := by
    cases out₁ <;> cases out <;> first | exact congrArg Outcome.normal hr | rfl | cases hr
  exact heq.symm ▸ ho₁

/--
Exact gap-free `ProgramEquiv` across arbitrary distinct gap alphabets `Gap₁`
and `Gap₂` induces an identity-observation `ExactPass` on the gap-erased
`Outcome Val` Layer 1A projection.
-/
theorem ProgramEquiv.toOutcomeExactPass_eq {Prog₁ : Type u₁} {Prog₂ : Type u₂}
    {Query : Type u} {Gap₁ : Type w₁} {Gap₂ : Type w₂} {Val : Type w₃}
    {sem₁ : Prog₁ → GapSem Query ExecFault Gap₁ Val}
    {sem₂ : Prog₂ → GapSem Query ExecFault Gap₂ Val}
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ProgramEquiv (· = ·) (· = ·) (sem₁ p₁) (sem₂ p₂)) :
    ExactPass (outcomeSemantics sem₁) (outcomeSemantics sem₂) id id p₁ p₂ where
  up_refines _ q := forbid_toOutcomePartial_le ((h q).flip.mono (fun _ _ hr =>
    GapForbidEq.mono (fun _ _ hv => Eq.symm hv) (fun _ _ he => Eq.symm he) hr.flip))
  down_refines _ q := forbid_toOutcomePartial_le (h q)

/-- Relate two halting `Outcome`s by `rVal` on normal returns and equality on panics/aborts. -/
def Outcome.Rel {Val₁ : Type u₁} {Val₂ : Type u₂} (rVal : Val₁ → Val₂ → Prop) :
    Outcome Val₁ → Outcome Val₂ → Prop
  | .normal v₁, .normal v₂ => rVal v₁ v₂
  | .panic, .panic => True
  | .abort, .abort => True
  | .normal _, .panic => False
  | .normal _, .abort => False
  | .panic, .normal _ => False
  | .panic, .abort => False
  | .abort, .normal _ => False
  | .abort, .panic => False

/-- Observation map on `Outcome Val` behaviors via `BehaviorSet.relImage (Outcome.Rel rVal)`. -/
def outcomeObsMap {Query : Type u} {Val₁ : Type u₁} {Val₂ : Type u₂}
    (rVal : Val₁ → Val₂ → Prop) :
    (Query → Partial (BehaviorSet (Outcome Val₁))) →
      Query → Partial (BehaviorSet (Outcome Val₂)) :=
  fun b q => Partial.map (BehaviorSet.relImage (Outcome.Rel rVal)) (b q)

theorem outcomeObsMap_monotone {Query : Type u} {Val₁ : Type u₁} {Val₂ : Type u₂}
    (rVal : Val₁ → Val₂ → Prop) :
    Monotone (outcomeObsMap (Query := Query) rVal) :=
  fun _ _ h q =>
    Partial.map_monotone (BehaviorSet.relImage_monotone (Outcome.Rel rVal)) (h q)

private theorem toOutcomePartial_le {Gap : Type w₁} {Val₁ : Type w₂} {Val₂ : Type w₃}
    {rVal : Val₁ → Val₂ → Prop}
    {S₁ : OutcomeSet ExecFault Gap Val₁} {S₂ : OutcomeSet ExecFault Gap Val₂}
    (h : OutcomeSetEquiv (GapEqErr rVal (· = ·)) S₁ S₂) :
    OutcomeSet.toOutcomePartial S₂ ≤
      Partial.map (BehaviorSet.relImage (Outcome.Rel rVal))
        (OutcomeSet.toOutcomePartial S₁) := by
  intro h₁
  refine ⟨(h.defined_iff (fun _ _ he => he ▸ Iff.rfl)).mp h₁, fun out₂ hout₂ => ?_⟩
  obtain ⟨o₁, ho₁, hr⟩ := h.backward hout₂
  obtain ⟨out₁, rfl⟩ := exists_classifyOutcome_of_isDefined (h₁ ho₁)
  refine ⟨out₁, ho₁, ?_⟩
  cases out₁ <;> cases out₂ <;> first | exact hr | exact trivial | cases hr

theorem ContextEquiv.toOutcomeExactPass {Prog₁ : Type u₁} {Prog₂ : Type u₂}
    {Query : Type u} {Gap : Type w₁} {Val₁ : Type w₂} {Val₂ : Type w₃}
    {rVal : Val₁ → Val₂ → Prop}
    {sem₁ : Prog₁ → GapSem Query ExecFault Gap Val₁}
    {sem₂ : Prog₂ → GapSem Query ExecFault Gap Val₂}
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ContextEquiv rVal (· = ·) (sem₁ p₁) (sem₂ p₂)) :
    ExactPass (outcomeSemantics sem₁) (outcomeSemantics sem₂)
      (outcomeObsMap rVal) (outcomeObsMap (fun v₂ v₁ => rVal v₁ v₂)) p₁ p₂ where
  up_refines _ q := toOutcomePartial_le ((h q).flip.mono (fun _ _ hr =>
    GapEqErr.mono (fun _ _ hv => hv) (fun _ _ he => Eq.symm he) hr.flip))
  down_refines _ q := toOutcomePartial_le (h q)

/--
Query-scoped specification transfer across `outcomeLanguage`: requires
`ContextEquivOn pre` only on queries where `spec` is defined.
-/
theorem ContextEquivOn.outcomeTransfer_spec {Prog₁ Prog₂ Query Gap Val : Type}
    {pre : Query → Prop}
    {sem₁ : Prog₁ → GapSem Query ExecFault Gap Val}
    {sem₂ : Prog₂ → GapSem Query ExecFault Gap Val}
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ContextEquivOn pre (· = ·) (· = ·) (sem₁ p₁) (sem₂ p₂))
    {spec : (outcomeLanguage sem₁).Behavior}
    (hPre : ∀ q, (spec q).defined → pre q)
    (h₁ : (outcomeLanguage sem₁).sem p₁ ≤ spec) :
    (outcomeLanguage sem₂).sem p₂ ≤ spec := by
  intro q hspec
  obtain ⟨hd₁, hle₁⟩ := h₁ q hspec
  have hq := hPre q hspec
  have hd₂ : OutcomeSet.Defined ExecFault.isUB (sem₂ p₂ q) :=
    ((h q hq).defined_iff (fun _ _ he => he ▸ Iff.rfl)).mp hd₁
  exact ⟨hd₂, fun out hout => hle₁ out ((h q hq).superset_of_eq (classifyOutcome out) hout)⟩

/--
Transfer any Layer 1A specification across `outcomeLanguage` along an exact
`ContextEquiv`, even when both programs hit shared modeling gaps outside the
specification's `safetyPre`.
-/
theorem ContextEquiv.outcomeTransfer_spec {Prog₁ Prog₂ Query Gap Val : Type}
    {sem₁ : Prog₁ → GapSem Query ExecFault Gap Val}
    {sem₂ : Prog₂ → GapSem Query ExecFault Gap Val}
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ContextEquiv (· = ·) (· = ·) (sem₁ p₁) (sem₂ p₂))
    {spec : (outcomeLanguage sem₁).Behavior}
    (h₁ : (outcomeLanguage sem₁).sem p₁ ≤ spec) :
    (outcomeLanguage sem₂).sem p₂ ≤ spec :=
  ContextEquivOn.outcomeTransfer_spec (pre := fun _ => True)
    (fun q _ => h q) (fun _ _ => trivial) h₁

/-- `.unsupported` always classifies as the site-tagged gap. -/
@[simp]
theorem classifyFailure_unsupported {Site : Type u₁} {Val : Type u₂} (site : Site) :
    classifyFailure (Val := Val) site .unsupported = .gap (.unsupported site) :=
  rfl

@[simp]
theorem classifyFailure_ub {Site : Type u₁} {Val : Type u₂} (site : Site) :
    classifyFailure (Val := Val) site .ub = .fault .ub := rfl

@[simp]
theorem classifyFailure_outOfFuel {Site : Type u₁} {Val : Type u₂} (site : Site) :
    classifyFailure (Val := Val) site .outOfFuel = .gap (.budget site) := rfl

/-- A halting outcome is never the evaluator's budget gap. -/
theorem classifyOutcome_ne_outOfFuel {Site : Type u₁} {Val : Type u₂}
    (out : Outcome Val) :
    classifyOutcome (Gap := GapTag Site) out ≠ .gap .outOfFuel := by
  cases out <;> exact fun h => by cases h

/-- A failure of the stepped machine is never the evaluator's budget gap. -/
theorem classifyFailure_ne_outOfFuel {Site : Type u₁} {Val : Type u₂}
    (site : Site) (kind : FailureKind) :
    classifyFailure (Val := Val) site kind ≠ .gap .outOfFuel := by
  cases kind <;> exact fun h => by cases h

/-- A classified failure is gap-free exactly when it is UB. -/
theorem classifyFailure_isGapFree_iff {Site : Type u₁} {Val : Type u₂}
    (site : Site) (kind : FailureKind) :
    (classifyFailure (Val := Val) site kind).isGapFree ↔ kind = .ub := by
  cases kind with
  | ub => exact ⟨fun _ => rfl, fun _ => trivial⟩
  | unsupported => exact ⟨False.elim, fun h => by cases h⟩
  | outOfFuel => exact ⟨False.elim, fun h => by cases h⟩

/-- A classified failure is never a value and never a defined failure. -/
theorem classifyFailure_fault_iff {Site : Type u₁} {Val : Type u₂}
    (site : Site) (kind : FailureKind) (e : ExecFault) :
    classifyFailure (Val := Val) site kind = .fault e ↔ kind = .ub ∧ e = .ub := by
  cases kind with
  | ub =>
    exact ⟨fun h => by cases h; exact ⟨rfl, rfl⟩, fun h => by cases h.2; rfl⟩
  | unsupported => exact ⟨fun h => (by cases h), fun h => by cases h.1⟩
  | outOfFuel => exact ⟨fun h => (by cases h), fun h => by cases h.1⟩

/-! ### Deterministic gap-classified machines -/

/-- Result of one deterministic gap-classified step: continue or halt. -/
inductive GapStep (State : Type u) (Fault : Type u₁) (Gap : Type u₂)
    (Val : Type u₃) : Type (max u u₁ u₂ u₃) where
  /-- Continue execution at `s`. -/
  | next (s : State)
  /-- Halt with outcome `out`. -/
  | done (out : OutcomeWithGap Fault Gap Val)

/--
Relate two step results: continuing states by `R`, halting outcomes by
`GapEqErr rVal rFault`. A continuing step never matches a halting step.
-/
def GapStep.Rel {State₁ : Type u} {State₂ : Type v₁} {Fault₁ : Type u₁}
    {Fault₂ : Type v₂} {Gap : Type u₂} {Val₁ : Type u₃} {Val₂ : Type w₁}
    (R : State₁ → State₂ → Prop)
    (rVal : Val₁ → Val₂ → Prop) (rFault : Fault₁ → Fault₂ → Prop) :
    GapStep State₁ Fault₁ Gap Val₁ → GapStep State₂ Fault₂ Gap Val₂ → Prop
  | .next s₁, .next s₂ => R s₁ s₂
  | .next _, .done _ => False
  | .done _, .next _ => False
  | .done o₁, .done o₂ => GapEqErr rVal rFault o₁ o₂

theorem GapStep.Rel.flip {State₁ : Type u} {State₂ : Type v₁} {Fault₁ : Type u₁}
    {Fault₂ : Type v₂} {Gap : Type u₂} {Val₁ : Type u₃} {Val₂ : Type w₁}
    {R : State₁ → State₂ → Prop}
    {rVal : Val₁ → Val₂ → Prop} {rFault : Fault₁ → Fault₂ → Prop}
    {n₁ : GapStep State₁ Fault₁ Gap Val₁} {n₂ : GapStep State₂ Fault₂ Gap Val₂}
    (h : GapStep.Rel R rVal rFault n₁ n₂) :
    GapStep.Rel (fun s₂ s₁ => R s₁ s₂) (fun v₂ v₁ => rVal v₁ v₂)
      (fun e₂ e₁ => rFault e₁ e₂) n₂ n₁ := by
  cases n₁ <;> cases n₂ <;> first | exact GapEqErr.flip h | exact h

private theorem exists_add_succ_of_lt {n fuel : Nat} (h : n < fuel) :
    ∃ k, fuel = n + (k + 1) := by
  obtain ⟨k, hk⟩ := Nat.le.dest h
  exact ⟨k, hk.symm.trans (Nat.add_right_comm n 1 k)⟩

section GapMachine

variable {State : Type u} {Fault : Type u₁} {Site : Type u₂} {Val : Type u₃}

/--
Run at most `fuel` steps of the gap-classified machine `next` from `s`.
Exhausting the budget is the gap `GapTag.outOfFuel`, never a value or a fault.
-/
def runGapSteps (next : State → GapStep State Fault (GapTag Site) Val) :
    Nat → State → OutcomeWithGap Fault (GapTag Site) Val
  | 0, _ => .gap .outOfFuel
  | fuel + 1, s =>
    match next s with
    | .next s' => runGapSteps next fuel s'
    | .done out => out

variable (next : State → GapStep State Fault (GapTag Site) Val)

@[simp]
theorem runGapSteps_zero (s : State) :
    runGapSteps next 0 s = .gap .outOfFuel := rfl

theorem runGapSteps_succ (fuel : Nat) (s : State) :
    runGapSteps next (fuel + 1) s =
      match next s with
      | .next s' => runGapSteps next fuel s'
      | .done out => out := rfl

theorem runGapSteps_succ_of_next {s s' : State} (h : next s = .next s')
    (fuel : Nat) :
    runGapSteps next (fuel + 1) s = runGapSteps next fuel s' := by
  rw [runGapSteps_succ, h]

theorem runGapSteps_succ_of_done {s : State}
    {out : OutcomeWithGap Fault (GapTag Site) Val} (h : next s = .done out)
    (fuel : Nat) :
    runGapSteps next (fuel + 1) s = out := by
  rw [runGapSteps_succ, h]

/--
Fuel monotonicity: once a run finishes with anything other than `.outOfFuel`,
every larger budget produces the same outcome.
-/
theorem runGapSteps_fuel_mono {o : OutcomeWithGap Fault (GapTag Site) Val}
    (ho : o ≠ .gap .outOfFuel) {fuel : Nat} {s : State}
    (h : runGapSteps next fuel s = o) (extra : Nat) :
    runGapSteps next (fuel + extra) s = o := by
  induction fuel generalizing s with
  | zero => exact absurd h.symm ho
  | succ fuel ih =>
    rw [Nat.add_right_comm, runGapSteps_succ]
    rw [runGapSteps_succ] at h
    cases hn : next s with
    | next s' => rw [hn] at h; exact ih h
    | done out => rw [hn] at h; exact h

/-- Fuel monotonicity in `≤` form. -/
theorem runGapSteps_fuel_mono_le {s : State} {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    (hne : runGapSteps next fuel s ≠ .gap .outOfFuel) :
    runGapSteps next fuel' s = runGapSteps next fuel s := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  exact runGapSteps_fuel_mono next hne rfl k

/-- Runs with different budgets agree whenever neither is out of fuel. -/
theorem runGapSteps_agree {s : State} {fuel₁ fuel₂ : Nat}
    (h₁ : runGapSteps next fuel₁ s ≠ .gap .outOfFuel)
    (h₂ : runGapSteps next fuel₂ s ≠ .gap .outOfFuel) :
    runGapSteps next fuel₁ s = runGapSteps next fuel₂ s :=
  (runGapSteps_fuel_mono next h₁ rfl fuel₂).symm.trans
    ((congrArg (fun n => runGapSteps next n s) (Nat.add_comm fuel₁ fuel₂)).trans
      (runGapSteps_fuel_mono next h₂ rfl fuel₁))

/-- `s` reaches `s'` in exactly `n` continuing (non-halting) steps. -/
inductive GapReach (next : State → GapStep State Fault (GapTag Site) Val) :
    Nat → State → State → Prop where
  | refl (s : State) : GapReach next 0 s s
  | step {n : Nat} {s s' s'' : State} :
      next s = .next s' → GapReach next n s' s'' → GapReach next (n + 1) s s''

theorem GapReach.snoc {n : Nat} {s t u : State} (h : GapReach next n s t)
    (hn : next t = .next u) : GapReach next (n + 1) s u := by
  induction h with
  | refl s => exact .step hn (.refl u)
  | step hs _ ih => exact .step hs (ih hn)

/-- A prefix of `n` continuing steps consumes exactly `n` units of fuel. -/
theorem runGapSteps_of_reach {n : Nat} {s s' : State}
    (h : GapReach next n s s') (fuel : Nat) :
    runGapSteps next (n + fuel) s = runGapSteps next fuel s' := by
  induction h with
  | refl s => rw [Nat.zero_add]
  | step hs _ ih =>
    rw [Nat.add_right_comm, runGapSteps_succ_of_next next hs]
    exact ih

/-- A budget not exceeding a prefix of continuing steps runs out of fuel. -/
theorem runGapSteps_outOfFuel_of_reach {n : Nat} {s s' : State}
    (h : GapReach next n s s') {fuel : Nat} (hle : fuel ≤ n) :
    runGapSteps next fuel s = .gap .outOfFuel := by
  induction h generalizing fuel with
  | refl s =>
    cases Nat.eq_zero_of_le_zero hle
    rfl
  | step hs _ ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      rw [runGapSteps_succ_of_next next hs]
      exact ih (Nat.le_of_succ_le_succ hle)

/--
Fuel-free behavior set of a gap-classified machine: the outcomes produced with
some finite budget. It is empty for a run that never finishes and a singleton
otherwise (`gapBehaviors_unique`).
-/
def gapBehaviors (s : State) : OutcomeSet Fault (GapTag Site) Val :=
  fun o => o ≠ .gap .outOfFuel ∧ ∃ fuel, runGapSteps next fuel s = o

theorem gapBehaviors_of_run {s : State} {fuel : Nat}
    (h : runGapSteps next fuel s ≠ .gap .outOfFuel) :
    gapBehaviors next s (runGapSteps next fuel s) :=
  ⟨h, fuel, rfl⟩

theorem gapBehaviors_unique {s : State}
    {o₁ o₂ : OutcomeWithGap Fault (GapTag Site) Val}
    (h₁ : gapBehaviors next s o₁) (h₂ : gapBehaviors next s o₂) : o₁ = o₂ := by
  obtain ⟨hne₁, fuel₁, rfl⟩ := h₁
  obtain ⟨hne₂, fuel₂, rfl⟩ := h₂
  exact runGapSteps_agree next hne₁ hne₂

/-- With a sufficient budget the fuel-free behavior set is the bounded run. -/
theorem gapBehaviors_iff_of_run {s : State} {fuel : Nat}
    (h : runGapSteps next fuel s ≠ .gap .outOfFuel)
    (o : OutcomeWithGap Fault (GapTag Site) Val) :
    gapBehaviors next s o ↔ o = runGapSteps next fuel s :=
  ⟨fun ho => gapBehaviors_unique next ho (gapBehaviors_of_run next h),
   fun ho => ho ▸ gapBehaviors_of_run next h⟩

/-- Every fuel-free behavior satisfies a predicate established for one finished run. -/
theorem gapBehaviors_all_of_run {s : State} {fuel : Nat}
    {P : OutcomeWithGap Fault (GapTag Site) Val → Prop}
    (hne : runGapSteps next fuel s ≠ .gap .outOfFuel)
    (hP : P (runGapSteps next fuel s)) :
    ∀ ⦃o⦄, gapBehaviors next s o → P o :=
  fun _ ho => (gapBehaviors_iff_of_run next hne _).mp ho ▸ hP

/-- A prefix of continuing steps does not change the fuel-free behavior set. -/
theorem gapBehaviors_reach_iff {n : Nat} {s s' : State}
    (h : GapReach next n s s') (o : OutcomeWithGap Fault (GapTag Site) Val) :
    gapBehaviors next s o ↔ gapBehaviors next s' o := by
  constructor
  · rintro ⟨hne, fuel, hf⟩
    rcases Nat.lt_or_ge n fuel with hlt | hge
    · obtain ⟨k, rfl⟩ := exists_add_succ_of_lt hlt
      exact ⟨hne, k + 1, (runGapSteps_of_reach next h (k + 1)).symm.trans hf⟩
    · exact absurd ((runGapSteps_outOfFuel_of_reach next h hge).symm.trans hf).symm hne
  · rintro ⟨hne, fuel, hf⟩
    exact ⟨hne, n + fuel, (runGapSteps_of_reach next h fuel).trans hf⟩

end GapMachine

/-! ### Lockstep and stuttering simulation up to identical gaps -/

section GapSimulation

variable {State₁ : Type u} {State₂ : Type v₁} {Fault₁ : Type u₁} {Fault₂ : Type v₂}
  {Site : Type u₂} {Val₁ : Type u₃} {Val₂ : Type w₁}
  {next₁ : State₁ → GapStep State₁ Fault₁ (GapTag Site) Val₁}
  {next₂ : State₂ → GapStep State₂ Fault₂ (GapTag Site) Val₂}
  {R : State₁ → State₂ → Prop}
  {rVal : Val₁ → Val₂ → Prop} {rFault : Fault₁ → Fault₂ → Prop}

/--
Lockstep congruence: if related states always step to related results, the two
bounded runs are `GapEqErr`-related for *every* budget, including runs that end
in an identical gap.
-/
theorem runGapSteps_lockstep
    (hsim : ∀ s₁ s₂, R s₁ s₂ → GapStep.Rel R rVal rFault (next₁ s₁) (next₂ s₂))
    (fuel : Nat) {s₁ : State₁} {s₂ : State₂} (h : R s₁ s₂) :
    GapEqErr rVal rFault (runGapSteps next₁ fuel s₁) (runGapSteps next₂ fuel s₂) := by
  induction fuel generalizing s₁ s₂ with
  | zero => exact (rfl : GapTag.outOfFuel = GapTag.outOfFuel)
  | succ fuel ih =>
    have hstep := hsim s₁ s₂ h
    rw [runGapSteps_succ, runGapSteps_succ]
    cases h₁ : next₁ s₁ with
    | next t₁ =>
      cases h₂ : next₂ s₂ with
      | next t₂ => rw [h₁, h₂] at hstep; exact ih hstep
      | done o₂ => rw [h₁, h₂] at hstep; exact False.elim hstep
    | done o₁ =>
      cases h₂ : next₂ s₂ with
      | next t₂ => rw [h₁, h₂] at hstep; exact False.elim hstep
      | done o₂ => rw [h₁, h₂] at hstep; exact hstep

private theorem gapBehaviors_forward_of_stutter
    (hsim : ∀ s₁ s₂, R s₁ s₂ → ∃ n₁ n₂ t₁ t₂,
      GapReach next₁ n₁ s₁ t₁ ∧ GapReach next₂ n₂ s₂ t₂ ∧
        GapStep.Rel R rVal rFault (next₁ t₁) (next₂ t₂))
    (bound : Nat) :
    ∀ (fuel : Nat) (s₁ : State₁) (s₂ : State₂), fuel ≤ bound → R s₁ s₂ →
      runGapSteps next₁ fuel s₁ ≠ .gap .outOfFuel →
      ∃ o₂, gapBehaviors next₂ s₂ o₂ ∧
        GapEqErr rVal rFault (runGapSteps next₁ fuel s₁) o₂ := by
  induction bound with
  | zero =>
    intro fuel s₁ s₂ hb _ hne
    cases Nat.eq_zero_of_le_zero hb
    exact absurd rfl hne
  | succ bound ih =>
    intro fuel s₁ s₂ hb hR hne
    obtain ⟨n₁, n₂, t₁, t₂, hr₁, hr₂, hrel⟩ := hsim s₁ s₂ hR
    rcases Nat.lt_or_ge n₁ fuel with hlt | hge
    · obtain ⟨k, rfl⟩ := exists_add_succ_of_lt hlt
      have hk : k ≤ bound :=
        Nat.le_trans (Nat.le_add_left k n₁) (Nat.le_of_succ_le_succ hb)
      rw [runGapSteps_of_reach next₁ hr₁ (k + 1)] at hne ⊢
      rw [runGapSteps_succ] at hne ⊢
      cases h₁ : next₁ t₁ with
      | next u₁ =>
        cases h₂ : next₂ t₂ with
        | next u₂ =>
          rw [h₁, h₂] at hrel
          rw [h₁] at hne
          obtain ⟨o₂, ho₂, hro⟩ := ih k u₁ u₂ hk hrel hne
          exact ⟨o₂, (gapBehaviors_reach_iff next₂ (hr₂.snoc next₂ h₂) o₂).mpr ho₂, hro⟩
        | done o₂ => rw [h₁, h₂] at hrel; exact False.elim hrel
      | done o₁ =>
        cases h₂ : next₂ t₂ with
        | next u₂ => rw [h₁, h₂] at hrel; exact False.elim hrel
        | done o₂ =>
          rw [h₁, h₂] at hrel
          rw [h₁] at hne
          have hne₂ : o₂ ≠ .gap .outOfFuel := fun h₀ =>
            hne (GapEqErr.gap_iff_right.mp (h₀ ▸ hrel))
          refine ⟨o₂, ⟨hne₂, n₂ + 1, ?_⟩, hrel⟩
          rw [runGapSteps_of_reach next₂ hr₂ 1, runGapSteps_succ_of_done next₂ h₂]
    · exact absurd (runGapSteps_outOfFuel_of_reach next₁ hr₁ hge) hne

/--
Stuttering congruence: if from related states both machines can take some
(possibly different) number of continuing steps and then step to related
results, their fuel-free behavior sets are equivalent up to identical gaps. A
refactoring may therefore change the number of internal steps freely.
-/
theorem gapBehaviors_equiv_of_stutter
    (hsim : ∀ s₁ s₂, R s₁ s₂ → ∃ n₁ n₂ t₁ t₂,
      GapReach next₁ n₁ s₁ t₁ ∧ GapReach next₂ n₂ s₂ t₂ ∧
        GapStep.Rel R rVal rFault (next₁ t₁) (next₂ t₂))
    {s₁ : State₁} {s₂ : State₂} (h : R s₁ s₂) :
    OutcomeSetEquiv (GapEqErr rVal rFault)
      (gapBehaviors next₁ s₁) (gapBehaviors next₂ s₂) := by
  constructor
  · rintro o₁ ⟨hne, fuel, rfl⟩
    exact gapBehaviors_forward_of_stutter hsim fuel fuel s₁ s₂ (Nat.le_refl fuel) h hne
  · rintro o₂ ⟨hne, fuel, rfl⟩
    obtain ⟨o₁, ho₁, hro⟩ :=
      gapBehaviors_forward_of_stutter (R := fun s₂ s₁ => R s₁ s₂)
        (rVal := fun v₂ v₁ => rVal v₁ v₂) (rFault := fun e₂ e₁ => rFault e₁ e₂)
        (fun s₂ s₁ hR => by
          obtain ⟨n₁, n₂, t₁, t₂, hr₁, hr₂, hrel⟩ := hsim s₁ s₂ hR
          exact ⟨n₂, n₁, t₂, t₁, hr₂, hr₁, hrel.flip⟩)
        fuel fuel s₂ s₁ (Nat.le_refl fuel) h hne
    exact ⟨o₁, ho₁, GapEqErr.flip_iff.mp hro⟩

/--
Lockstep simulation also relates the fuel-free behavior sets (the stuttering
congruence with empty prefixes).
-/
theorem gapBehaviors_equiv_of_lockstep
    (hsim : ∀ s₁ s₂, R s₁ s₂ → GapStep.Rel R rVal rFault (next₁ s₁) (next₂ s₂))
    {s₁ : State₁} {s₂ : State₂} (h : R s₁ s₂) :
    OutcomeSetEquiv (GapEqErr rVal rFault)
      (gapBehaviors next₁ s₁) (gapBehaviors next₂ s₂) :=
  gapBehaviors_equiv_of_stutter
    (fun s₁ s₂ hR => ⟨0, 0, s₁, s₂, .refl s₁, .refl s₂, hsim s₁ s₂ hR⟩) h

end GapSimulation


/-! ### Gap-classified stepping of `ITreeF` coalgebras -/

section ITreeFStepping

variable {State Val Site : Type} {E : Effect.{0}}

/--
One gap-classified step of an `ITreeF` coalgebra whose effect row starts with
`FailE FailureKind`. Requests of the remaining row `E` are resolved by the
handler `handle` (for MIR: observations are erased and external calls are
delegated to a callee environment); a fault or gap of the handler halts the
caller with that same fault or gap.
-/
def gapStep
    (step : State → ITreeF (SumE (FailE FailureKind) E) (Outcome Val) State)
    (site : State → Site)
    (handle : (i : E.I) → OutcomeWithGap ExecFault (GapTag Site) (E.O i))
    (s : State) : GapStep State ExecFault (GapTag Site) Val :=
  match step s with
  | .ret out => .done (classifyOutcome out)
  | .tau s' => .next s'
  | .vis (.inl (.fail kind)) _ => .done (classifyFailure (site s) kind)
  | .vis (.inr i) k =>
    match handle i with
    | .ok o => .next (k o)
    | .fault e => .done (.fault e)
    | .gap g => .done (.gap g)

/--
Fuel-indexed multi-step evaluator of an `ITreeF` coalgebra into
`OutcomeWithGap`: `.ret (.normal v)` is `.ok v`, `.ret .panic` / `.ret .abort`
are the defined faults, `FailureKind.ub` is `ExecFault.ub`, and
`FailureKind.unsupported`, `FailureKind.outOfFuel` and an exhausted budget are
gaps (`GapTag.unsupported`, `GapTag.budget` and `GapTag.outOfFuel`).
-/
def runStepsWithGap
    (step : State → ITreeF (SumE (FailE FailureKind) E) (Outcome Val) State)
    (site : State → Site)
    (handle : (i : E.I) → OutcomeWithGap ExecFault (GapTag Site) (E.O i))
    (fuel : Nat) (s : State) : OutcomeWithGap ExecFault (GapTag Site) Val :=
  runGapSteps (gapStep step site handle) fuel s

/-- Fuel-indexed gap-aware evaluation of an `ITreeMachine` program. -/
def ITreeMachine.runWithGap {Prog : Type}
    (M : ITreeMachine Prog State (SumE (FailE FailureKind) E) (Outcome Val))
    (site : State → Site)
    (handle : (i : E.I) → OutcomeWithGap ExecFault (GapTag Site) (E.O i))
    (fuel : Nat) (p : Prog) : OutcomeWithGap ExecFault (GapTag Site) Val :=
  runStepsWithGap (M.step p) site handle fuel (M.init p)

variable
  {step : State → ITreeF (SumE (FailE FailureKind) E) (Outcome Val) State}
  {site : State → Site}
  {handle : (i : E.I) → OutcomeWithGap ExecFault (GapTag Site) (E.O i)}

theorem gapStep_of_ret {s : State} {out : Outcome Val} (h : step s = .ret out) :
    gapStep step site handle s = .done (classifyOutcome out) := by
  unfold gapStep; rw [h]

theorem gapStep_of_tau {s s' : State} (h : step s = .tau s') :
    gapStep step site handle s = .next s' := by
  unfold gapStep; rw [h]

theorem gapStep_of_fail {s : State} {kind : FailureKind}
    {k : PEmpty → State} (h : step s = .vis (.inl (.fail kind)) k) :
    gapStep step site handle s = .done (classifyFailure (site s) kind) := by
  unfold gapStep; rw [h]

theorem gapStep_of_vis {s : State} {i : E.I} {k : E.O i → State}
    (h : step s = .vis (.inr i) k) :
    gapStep step site handle s =
      match handle i with
      | .ok o => .next (k o)
      | .fault e => .done (.fault e)
      | .gap g => .done (.gap g) := by
  unfold gapStep; rw [h]

@[simp]
theorem runStepsWithGap_zero (s : State) :
    runStepsWithGap step site handle 0 s = .gap .outOfFuel := rfl

/-- A halting node yields its classified outcome with any positive budget. -/
theorem runStepsWithGap_of_ret {s : State} {out : Outcome Val}
    (h : step s = .ret out) (fuel : Nat) :
    runStepsWithGap step site handle (fuel + 1) s = classifyOutcome out :=
  runGapSteps_succ_of_done _ (gapStep_of_ret h) fuel

/-- A silent step consumes one unit of fuel. -/
theorem runStepsWithGap_of_tau {s s' : State} (h : step s = .tau s')
    (fuel : Nat) :
    runStepsWithGap step site handle (fuel + 1) s =
      runStepsWithGap step site handle fuel s' :=
  runGapSteps_succ_of_next _ (gapStep_of_tau h) fuel

/-- A fault node yields its classified failure with any positive budget. -/
theorem runStepsWithGap_of_fail {s : State} {kind : FailureKind}
    {k : PEmpty → State} (h : step s = .vis (.inl (.fail kind)) k) (fuel : Nat) :
    runStepsWithGap step site handle (fuel + 1) s =
      classifyFailure (site s) kind :=
  runGapSteps_succ_of_done _ (gapStep_of_fail h) fuel

/--
`FailureKind.unsupported` always becomes the gap tagged with the current site:
never a value, never a fault.
-/
theorem runStepsWithGap_of_unsupported {s : State} {k : PEmpty → State}
    (h : step s = .vis (.inl (.fail .unsupported)) k) (fuel : Nat) :
    runStepsWithGap step site handle (fuel + 1) s = .gap (.unsupported (site s)) :=
  runStepsWithGap_of_fail h fuel

/--
Call-handler law: a handled request is the monadic `bind` of the handler's
outcome with the rest of the run. A gap of the handler (for example a shared
unmodeled callee) is therefore the outcome of the whole run.
-/
theorem runStepsWithGap_of_vis {s : State} {i : E.I} {k : E.O i → State}
    (h : step s = .vis (.inr i) k) (fuel : Nat) :
    runStepsWithGap step site handle (fuel + 1) s =
      (handle i).bind (fun o => runStepsWithGap step site handle fuel (k o)) := by
  unfold runStepsWithGap
  rw [runGapSteps_succ, gapStep_of_vis h]
  cases handle i <;> rfl

/--
One-step agreement of two coalgebra nodes executed at sites `site₁` and
`site₂`: equal halting outcomes up to `rVal`, `R`-related successors, the same
failure kind (at the same site unless it is `FailureKind.ub`, since gaps are
site-tagged), or the same request with `R`-related continuations.
-/
inductive StepNodeRel {State₁ State₂ Val₁ Val₂ : Type}
    (R : State₁ → State₂ → Prop) (rVal : Val₁ → Val₂ → Prop)
    (site₁ site₂ : Site) :
    ITreeF (SumE (FailE FailureKind) E) (Outcome Val₁) State₁ →
      ITreeF (SumE (FailE FailureKind) E) (Outcome Val₂) State₂ → Prop where
  | normal {v₁ : Val₁} {v₂ : Val₂} : rVal v₁ v₂ →
      StepNodeRel R rVal site₁ site₂ (.ret (.normal v₁)) (.ret (.normal v₂))
  | panic : StepNodeRel R rVal site₁ site₂ (.ret .panic) (.ret .panic)
  | abort : StepNodeRel R rVal site₁ site₂ (.ret .abort) (.ret .abort)
  | tau {s₁ : State₁} {s₂ : State₂} : R s₁ s₂ →
      StepNodeRel R rVal site₁ site₂ (.tau s₁) (.tau s₂)
  | fail {kind : FailureKind} {k₁ : PEmpty → State₁} {k₂ : PEmpty → State₂} :
      (kind ≠ .ub → site₁ = site₂) →
      StepNodeRel R rVal site₁ site₂
        (.vis (.inl (.fail kind)) k₁) (.vis (.inl (.fail kind)) k₂)
  | vis {i : E.I} {k₁ : E.O i → State₁} {k₂ : E.O i → State₂} :
      (∀ o, R (k₁ o) (k₂ o)) →
      StepNodeRel R rVal site₁ site₂ (.vis (.inr i) k₁) (.vis (.inr i) k₂)

end ITreeFStepping

section ITreeFCongruence

variable {State₁ State₂ Val₁ Val₂ Site : Type} {E : Effect.{0}}
  {step₁ : State₁ → ITreeF (SumE (FailE FailureKind) E) (Outcome Val₁) State₁}
  {step₂ : State₂ → ITreeF (SumE (FailE FailureKind) E) (Outcome Val₂) State₂}
  {site₁ : State₁ → Site} {site₂ : State₂ → Site}
  {handle₁ handle₂ : (i : E.I) → OutcomeWithGap ExecFault (GapTag Site) (E.O i)}
  {R : State₁ → State₂ → Prop} {rVal : Val₁ → Val₂ → Prop}
  {rFault : ExecFault → ExecFault → Prop}

/--
Handler-relational one-step agreement of two coalgebra nodes: generalizes
`StepNodeRel` by allowing distinct handled requests `i₁` and `i₂` (for example,
two external `MirCallReq`s carrying related memories with distinct borrow-tag
counters) and requiring `R (k₁ o₁) (k₂ o₂)` only on answer pairs `(o₁, o₂)`
related by `rAns` where `GapEqErr rAns rFault (handle₁ i₁) (handle₂ i₂)`.
-/
inductive StepNodeRelWith {State₁ State₂ Val₁ Val₂ Site : Type} {E : Effect.{0}}
    (handle₁ : (i : E.I) → OutcomeWithGap ExecFault (GapTag Site) (E.O i))
    (handle₂ : (i : E.I) → OutcomeWithGap ExecFault (GapTag Site) (E.O i))
    (R : State₁ → State₂ → Prop) (rVal : Val₁ → Val₂ → Prop)
    (rFault : ExecFault → ExecFault → Prop)
    (site₁ site₂ : Site) :
    ITreeF (SumE (FailE FailureKind) E) (Outcome Val₁) State₁ →
      ITreeF (SumE (FailE FailureKind) E) (Outcome Val₂) State₂ → Prop where
  | normal {v₁ : Val₁} {v₂ : Val₂} : rVal v₁ v₂ →
      StepNodeRelWith handle₁ handle₂ R rVal rFault site₁ site₂
        (.ret (.normal v₁)) (.ret (.normal v₂))
  | panic :
      StepNodeRelWith handle₁ handle₂ R rVal rFault site₁ site₂
        (.ret .panic) (.ret .panic)
  | abort :
      StepNodeRelWith handle₁ handle₂ R rVal rFault site₁ site₂
        (.ret .abort) (.ret .abort)
  | tau {s₁ : State₁} {s₂ : State₂} : R s₁ s₂ →
      StepNodeRelWith handle₁ handle₂ R rVal rFault site₁ site₂
        (.tau s₁) (.tau s₂)
  | fail {kind : FailureKind} {k₁ : PEmpty → State₁} {k₂ : PEmpty → State₂} :
      (kind ≠ .ub → site₁ = site₂) →
      StepNodeRelWith handle₁ handle₂ R rVal rFault site₁ site₂
        (.vis (.inl (.fail kind)) k₁) (.vis (.inl (.fail kind)) k₂)
  | vis {i₁ i₂ : E.I} {k₁ : E.O i₁ → State₁} {k₂ : E.O i₂ → State₂}
      (rAns : E.O i₁ → E.O i₂ → Prop) :
      GapEqErr rAns rFault (handle₁ i₁) (handle₂ i₂) →
      (∀ o₁ o₂, handle₁ i₁ = .ok o₁ → handle₂ i₂ = .ok o₂ →
        rAns o₁ o₂ → R (k₁ o₁) (k₂ o₂)) →
      StepNodeRelWith handle₁ handle₂ R rVal rFault site₁ site₂
        (.vis (.inr i₁) k₁) (.vis (.inr i₂) k₂)

theorem gapStep_rel_of_stepNodeRelWith (hFault : ∀ e, rFault e e)
    {s₁ : State₁} {s₂ : State₂}
    (h : StepNodeRelWith handle₁ handle₂ R rVal rFault
      (site₁ s₁) (site₂ s₂) (step₁ s₁) (step₂ s₂)) :
    GapStep.Rel R rVal rFault (gapStep step₁ site₁ handle₁ s₁)
      (gapStep step₂ site₂ handle₂ s₂) := by
  generalize h₁ : step₁ s₁ = n₁ at h
  generalize h₂ : step₂ s₂ = n₂ at h
  cases h with
  | normal hv => rw [gapStep_of_ret h₁, gapStep_of_ret h₂]; exact hv
  | panic => rw [gapStep_of_ret h₁, gapStep_of_ret h₂]; exact hFault .panic
  | abort => rw [gapStep_of_ret h₁, gapStep_of_ret h₂]; exact hFault .abort
  | tau hR => rw [gapStep_of_tau h₁, gapStep_of_tau h₂]; exact hR
  | @fail kind k₁ k₂ hsite =>
    rw [gapStep_of_fail h₁, gapStep_of_fail h₂]
    cases kind with
    | ub => exact hFault .ub
    | unsupported =>
      exact congrArg GapTag.unsupported (hsite (fun h => by cases h))
    | outOfFuel => exact congrArg GapTag.budget (hsite (fun h => by cases h))
  | @vis i₁ i₂ k₁ k₂ rAns hAns hk =>
    rw [gapStep_of_vis h₁, gapStep_of_vis h₂]
    cases ho₁ : handle₁ i₁ with
    | ok o₁ =>
      cases ho₂ : handle₂ i₂ with
      | ok o₂ => rw [ho₁, ho₂] at hAns; exact hk o₁ o₂ ho₁ ho₂ hAns
      | fault _ => rw [ho₁, ho₂] at hAns; exact False.elim hAns
      | gap _ => rw [ho₁, ho₂] at hAns; exact False.elim hAns
    | fault e₁ =>
      cases ho₂ : handle₂ i₂ with
      | ok _ => rw [ho₁, ho₂] at hAns; exact False.elim hAns
      | fault e₂ => rw [ho₁, ho₂] at hAns; exact hAns
      | gap _ => rw [ho₁, ho₂] at hAns; exact False.elim hAns
    | gap g₁ =>
      cases ho₂ : handle₂ i₂ with
      | ok _ => rw [ho₁, ho₂] at hAns; exact False.elim hAns
      | fault _ => rw [ho₁, ho₂] at hAns; exact False.elim hAns
      | gap g₂ => rw [ho₁, ho₂] at hAns; exact hAns

theorem StepNodeRel.toWith
    (hh : ∀ i, GapEqErr (· = ·) rFault (handle₁ i) (handle₂ i))
    {s₁ s₂ : Site}
    {n₁ : ITreeF (SumE (FailE FailureKind) E) (Outcome Val₁) State₁}
    {n₂ : ITreeF (SumE (FailE FailureKind) E) (Outcome Val₂) State₂}
    (h : StepNodeRel R rVal s₁ s₂ n₁ n₂) :
    StepNodeRelWith handle₁ handle₂ R rVal rFault s₁ s₂ n₁ n₂ := by
  cases h with
  | normal hv => exact .normal hv
  | panic => exact .panic
  | abort => exact .abort
  | tau hR => exact .tau hR
  | fail hs => exact .fail hs
  | vis hk => exact .vis (· = ·) (hh _) (fun o _ _ _ he => he ▸ hk o)

/--
Agreeing coalgebra nodes resolved by related handlers give related
gap-classified steps. The handlers may fault or gap arbitrarily: no
gap-freedom of the callee environment is assumed.
-/
theorem gapStep_rel_of_stepNodeRel (hFault : ∀ e, rFault e e)
    (hh : ∀ i, GapEqErr (· = ·) rFault (handle₁ i) (handle₂ i))
    {s₁ : State₁} {s₂ : State₂}
    (h : StepNodeRel R rVal (site₁ s₁) (site₂ s₂) (step₁ s₁) (step₂ s₂)) :
    GapStep.Rel R rVal rFault (gapStep step₁ site₁ handle₁ s₁)
      (gapStep step₂ site₂ handle₂ s₂) :=
  gapStep_rel_of_stepNodeRelWith hFault (h.toWith hh)

/--
Multi-step congruence for a refactored caller: if related states of the two
coalgebras always present agreeing nodes, then for **every** shared callee
environment `handle` (gap-free or not) and every budget, the two bounded runs
are related up to identical gaps.
-/
theorem runStepsWithGap_congr
    (hsim : ∀ s₁ s₂, R s₁ s₂ →
      StepNodeRel R rVal (site₁ s₁) (site₂ s₂) (step₁ s₁) (step₂ s₂))
    (handle : (i : E.I) → OutcomeWithGap ExecFault (GapTag Site) (E.O i))
    (fuel : Nat) {s₁ : State₁} {s₂ : State₂} (h : R s₁ s₂) :
    GapEqErr rVal (· = ·) (runStepsWithGap step₁ site₁ handle fuel s₁)
      (runStepsWithGap step₂ site₂ handle fuel s₂) :=
  runGapSteps_lockstep
    (fun s₁ s₂ hR => gapStep_rel_of_stepNodeRel (fun _ => rfl)
      (fun i => GapEqErr.refl (fun _ => rfl) (fun _ => rfl) (handle i))
      (hsim s₁ s₂ hR))
    fuel h

/--
Multi-step congruence under related callee environments: a refactored caller
run against a refactored callee environment is related to the original pair,
as long as the environments agree up to identical gaps.
-/
theorem runStepsWithGap_congr_handle (hFault : ∀ e, rFault e e)
    (hsim : ∀ s₁ s₂, R s₁ s₂ →
      StepNodeRel R rVal (site₁ s₁) (site₂ s₂) (step₁ s₁) (step₂ s₂))
    (hh : ∀ i, GapEqErr (· = ·) rFault (handle₁ i) (handle₂ i))
    (fuel : Nat) {s₁ : State₁} {s₂ : State₂} (h : R s₁ s₂) :
    GapEqErr rVal rFault (runStepsWithGap step₁ site₁ handle₁ fuel s₁)
      (runStepsWithGap step₂ site₂ handle₂ fuel s₂) :=
  runGapSteps_lockstep
    (fun s₁ s₂ hR => gapStep_rel_of_stepNodeRel hFault hh (hsim s₁ s₂ hR)) fuel h

/--
Stuttering multi-step congruence for `ITreeF` coalgebras under related callee
environments: related states may take different numbers of silent or erased
continuing steps (`GapReach`) before synchronizing on agreeing `StepNodeRel`
nodes, and their fuel-free behavior sets remain equivalent up to identical gaps.
-/
theorem gapBehaviors_equiv_of_stutter_step (hFault : ∀ e, rFault e e)
    (hsim : ∀ s₁ s₂, R s₁ s₂ → ∃ n₁ n₂ t₁ t₂,
      GapReach (gapStep step₁ site₁ handle₁) n₁ s₁ t₁ ∧
      GapReach (gapStep step₂ site₂ handle₂) n₂ s₂ t₂ ∧
      StepNodeRel R rVal (site₁ t₁) (site₂ t₂) (step₁ t₁) (step₂ t₂))
    (hh : ∀ i, GapEqErr (· = ·) rFault (handle₁ i) (handle₂ i))
    {s₁ : State₁} {s₂ : State₂} (h : R s₁ s₂) :
    OutcomeSetEquiv (GapEqErr rVal rFault)
      (gapBehaviors (gapStep step₁ site₁ handle₁) s₁)
      (gapBehaviors (gapStep step₂ site₂ handle₂) s₂) :=
  gapBehaviors_equiv_of_stutter
    (fun a b hR => by
      obtain ⟨n₁, n₂, t₁, t₂, hr₁, hr₂, hnode⟩ := hsim a b hR
      exact ⟨n₁, n₂, t₁, t₂, hr₁, hr₂, gapStep_rel_of_stepNodeRel hFault hh hnode⟩)
    h

theorem gapBehaviors_equiv_of_stutter_step_with (hFault : ∀ e, rFault e e)
    (hsim : ∀ s₁ s₂, R s₁ s₂ → ∃ n₁ n₂ t₁ t₂,
      GapReach (gapStep step₁ site₁ handle₁) n₁ s₁ t₁ ∧
      GapReach (gapStep step₂ site₂ handle₂) n₂ s₂ t₂ ∧
      StepNodeRelWith handle₁ handle₂ R rVal rFault
        (site₁ t₁) (site₂ t₂) (step₁ t₁) (step₂ t₂))
    {s₁ : State₁} {s₂ : State₂} (h : R s₁ s₂) :
    OutcomeSetEquiv (GapEqErr rVal rFault)
      (gapBehaviors (gapStep step₁ site₁ handle₁) s₁)
      (gapBehaviors (gapStep step₂ site₂ handle₂) s₂) :=
  gapBehaviors_equiv_of_stutter
    (fun a b hR => by
      obtain ⟨n₁, n₂, t₁, t₂, hr₁, hr₂, hnode⟩ := hsim a b hR
      exact ⟨n₁, n₂, t₁, t₂, hr₁, hr₂, gapStep_rel_of_stepNodeRelWith hFault hnode⟩)
    h

end ITreeFCongruence

section SharedState

variable {State Val Site : Type} {E : Effect.{0}}
  {step : State → ITreeF (SumE (FailE FailureKind) E) (Outcome Val) State}
  {site : State → Site}

/-- Every node agrees with itself at the same site. -/
theorem StepNodeRel.refl
    (n : ITreeF (SumE (FailE FailureKind) E) (Outcome Val) State) (x : Site) :
    StepNodeRel (· = ·) (· = ·) x x n n := by
  cases n with
  | ret out =>
    cases out with
    | normal v => exact .normal rfl
    | panic => exact .panic
    | abort => exact .abort
  | tau s => exact .tau rfl
  | vis i k =>
    cases i with
    | inl f =>
      cases f with
      | fail kind => exact .fail (fun _ => rfl)
    | inr j => exact .vis (fun _ => rfl)

/--
Shared unchanged code is related to itself for every budget and every callee
environment, with no gap-freedom obligation, including when it steps to
`FailureKind.unsupported`.
-/
theorem runStepsWithGap_refl
    (handle : (i : E.I) → OutcomeWithGap ExecFault (GapTag Site) (E.O i))
    (fuel : Nat) (s : State) :
    GapEqErr (· = ·) (· = ·) (runStepsWithGap step site handle fuel s)
      (runStepsWithGap step site handle fuel s) :=
  GapEqErr.refl (fun _ => rfl) (fun _ => rfl) _

/--
Shared unchanged caller under a refactored callee environment: environments
that agree up to identical gaps give runs that agree up to identical gaps.
-/
theorem runStepsWithGap_handle_congr {rFault : ExecFault → ExecFault → Prop}
    (hFault : ∀ e, rFault e e)
    {handle₁ handle₂ : (i : E.I) → OutcomeWithGap ExecFault (GapTag Site) (E.O i)}
    (hh : ∀ i, GapEqErr (· = ·) rFault (handle₁ i) (handle₂ i))
    (fuel : Nat) (s : State) :
    GapEqErr (· = ·) rFault (runStepsWithGap step site handle₁ fuel s)
      (runStepsWithGap step site handle₂ fuel s) :=
  runStepsWithGap_congr_handle (R := (· = ·)) hFault
    (fun s₁ s₂ hs => by cases hs; exact StepNodeRel.refl (step s₁) (site s₁))
    hh fuel rfl

/--
A handled request `i : E.I` is reachable from `s` under `handle` when `s`
reaches some state `t` along continuing `gapStep` transitions where `step t`
emits `.vis (.inr i) k`.
-/
def StepRequestReachable
    (step : State → ITreeF (SumE (FailE FailureKind) E) (Outcome Val) State)
    (site : State → Site)
    (handle : (i : E.I) → OutcomeWithGap ExecFault (GapTag Site) (E.O i))
    (s : State) (i : E.I) : Prop :=
  ∃ n t k, GapReach (gapStep step site handle) n s t ∧ step t = .vis (.inr i) k

theorem StepRequestReachable.of_step
    {handle : (i : E.I) → OutcomeWithGap ExecFault (GapTag Site) (E.O i)}
    {s s' : State} {i : E.I}
    (hn : gapStep step site handle s = .next s')
    (h : StepRequestReachable step site handle s' i) :
    StepRequestReachable step site handle s i := by
  obtain ⟨n, t, k, hr, ht⟩ := h
  exact ⟨n + 1, t, k, .step hn hr, ht⟩

/--
Inductive-invariant criterion for `StepRequestReachable`: if `I` holds at `s`,
is preserved by continuing `gapStep` steps, and implies `P i` at every handled
request `.vis (.inr i) k`, then every reachable request satisfies `P`.
-/
theorem stepRequestReachable_of_inv
    {handle : (i : E.I) → OutcomeWithGap ExecFault (GapTag Site) (E.O i)}
    {I : State → Prop} {P : E.I → Prop} {s : State}
    (hInit : I s)
    (hStep : ∀ t t', I t → gapStep step site handle t = .next t' → I t')
    (hReq : ∀ t i k, I t → step t = .vis (.inr i) k → P i) :
    ∀ i, StepRequestReachable step site handle s i → P i := by
  intro i hreach
  obtain ⟨n, t, k, hr, ht⟩ := hreach
  have hIt : I t := by
    clear ht
    induction hr with
    | refl _ => exact hInit
    | step hn _ ih => exact ih (hStep _ _ hInit hn)
  exact hReq t i k hIt ht

/--
Reachable-request bounded handler congruence: `handle₁` and `handle₂` need only
agree on requests `i` actually reachable from `s` under `handle₁` (enabling
incremental modular summary linking where `handle₂` adds summaries for unrelated
callees not called from `s`).
-/
theorem runStepsWithGap_handle_congr_on {rFault : ExecFault → ExecFault → Prop}
    (hFault : ∀ e, rFault e e)
    {handle₁ handle₂ : (i : E.I) → OutcomeWithGap ExecFault (GapTag Site) (E.O i)}
    {s : State}
    (hh : ∀ i, StepRequestReachable step site handle₁ s i →
      GapEqErr (· = ·) rFault (handle₁ i) (handle₂ i))
    (fuel : Nat) :
    GapEqErr (· = ·) rFault (runStepsWithGap step site handle₁ fuel s)
      (runStepsWithGap step site handle₂ fuel s) := by
  induction fuel generalizing s with
  | zero => exact (rfl : GapTag.outOfFuel = GapTag.outOfFuel)
  | succ fuel ih =>
    cases hs : step s with
    | ret out =>
      rw [runStepsWithGap_of_ret hs, runStepsWithGap_of_ret hs]
      exact GapEqErr.refl (fun _ => rfl) hFault _
    | tau s' =>
      rw [runStepsWithGap_of_tau hs, runStepsWithGap_of_tau hs]
      exact ih (fun i hi => hh i (hi.of_step (gapStep_of_tau hs)))
    | vis idx k =>
      cases idx with
      | inl f =>
        cases f with
        | fail kind =>
          rw [runStepsWithGap_of_fail hs, runStepsWithGap_of_fail hs]
          exact GapEqErr.refl (fun _ => rfl) hFault _
      | inr i =>
        have hi := hh i ⟨0, s, k, .refl s, hs⟩
        rw [runStepsWithGap_of_vis hs, runStepsWithGap_of_vis hs]
        cases ho₁ : handle₁ i with
        | ok o₁ =>
          cases ho₂ : handle₂ i with
          | ok o₂ =>
            rw [ho₁, ho₂] at hi
            cases (hi : o₁ = o₂)
            have hn : gapStep step site handle₁ s = .next (k o₁) := by
              rw [gapStep_of_vis hs, ho₁]
            exact ih (fun j hj => hh j (hj.of_step hn))
          | fault _ => rw [ho₁, ho₂] at hi; exact False.elim hi
          | gap _ => rw [ho₁, ho₂] at hi; exact False.elim hi
        | fault e₁ =>
          cases ho₂ : handle₂ i with
          | ok _ => rw [ho₁, ho₂] at hi; exact False.elim hi
          | fault _ => rw [ho₁, ho₂] at hi; exact hi
          | gap _ => rw [ho₁, ho₂] at hi; exact False.elim hi
        | gap g₁ =>
          cases ho₂ : handle₂ i with
          | ok _ => rw [ho₁, ho₂] at hi; exact False.elim hi
          | fault _ => rw [ho₁, ho₂] at hi; exact False.elim hi
          | gap _ => rw [ho₁, ho₂] at hi; exact hi

/--
Reachable-request fuel-free handler congruence: `gapBehaviors` is invariant
under extending or refactoring `handle` outside the requests reachable from `s`.
-/
theorem gapBehaviors_handle_congr_on {rFault : ExecFault → ExecFault → Prop}
    (hFault : ∀ e, rFault e e)
    {handle₁ handle₂ : (i : E.I) → OutcomeWithGap ExecFault (GapTag Site) (E.O i)}
    {s : State}
    (hh : ∀ i, StepRequestReachable step site handle₁ s i →
      GapEqErr (· = ·) rFault (handle₁ i) (handle₂ i)) :
    OutcomeSetEquiv (GapEqErr (· = ·) rFault)
      (gapBehaviors (gapStep step site handle₁) s)
      (gapBehaviors (gapStep step site handle₂) s) where
  forward := by
    rintro o₁ ⟨hne₁, fuel, rfl⟩
    have hr : GapEqErr (· = ·) rFault
        (runGapSteps (gapStep step site handle₁) fuel s)
        (runGapSteps (gapStep step site handle₂) fuel s) :=
      runStepsWithGap_handle_congr_on hFault hh fuel
    exact ⟨_, ⟨fun h₀ => hne₁ (GapEqErr.gap_iff_right.mp (h₀ ▸ hr)), fuel, rfl⟩, hr⟩
  backward := by
    rintro o₂ ⟨hne₂, fuel, rfl⟩
    have hr : GapEqErr (· = ·) rFault
        (runGapSteps (gapStep step site handle₁) fuel s)
        (runGapSteps (gapStep step site handle₂) fuel s) :=
      runStepsWithGap_handle_congr_on hFault hh fuel
    exact ⟨_, ⟨fun h₀ => hne₂ (GapEqErr.gap_iff.mp (h₀ ▸ hr)), fuel, rfl⟩, hr⟩

end SharedState

/-! ## 6. Certificate Checkers for Gap-Preserving Equivalence -/

/-- Verified boolean certificate checker for gap-preserving `ContextEquiv`. -/
structure VerifiedContextChecker
    {Prog₁ : Type u₁} {Prog₂ : Type u₂} {Cert : Type u₃} {Query : Type u}
    {Fault₁ : Type v₁} {Fault₂ : Type v₂} {Gap : Type w₁}
    {Val₁ : Type w₂} {Val₂ : Type w₃}
    (rVal : Val₁ → Val₂ → Prop) (rFault : Fault₁ → Fault₂ → Prop)
    (sem₁ : Prog₁ → GapSem Query Fault₁ Gap Val₁)
    (sem₂ : Prog₂ → GapSem Query Fault₂ Gap Val₂)
    (check : Prog₁ → Prog₂ → Cert → Bool) : Prop where
  sound : ∀ {p₁ p₂ cert}, check p₁ p₂ cert = true →
    ContextEquiv rVal rFault (sem₁ p₁) (sem₂ p₂)

/-- Verified boolean certificate checker for gap-free `ProgramEquiv`. -/
structure VerifiedProgramChecker
    {Prog₁ : Type u₁} {Prog₂ : Type u₂} {Cert : Type u₃} {Query : Type u}
    {Fault₁ : Type v₁} {Fault₂ : Type v₂} {Gap : Type w₁}
    {Val₁ : Type w₂} {Val₂ : Type w₃}
    (rVal : Val₁ → Val₂ → Prop) (rFault : Fault₁ → Fault₂ → Prop)
    (sem₁ : Prog₁ → GapSem Query Fault₁ Gap Val₁)
    (sem₂ : Prog₂ → GapSem Query Fault₂ Gap Val₂)
    (check : Prog₁ → Prog₂ → Cert → Bool) : Prop where
  sound : ∀ {p₁ p₂ cert}, check p₁ p₂ cert = true →
    ProgramEquiv rVal rFault (sem₁ p₁) (sem₂ p₂)

/-- Verified boolean certificate checker for gap-freedom of a single program. -/
structure VerifiedGapFreeChecker
    {Prog : Type u₁} {Cert : Type u₃} {Query : Type u}
    {Fault : Type v₁} {Gap : Type w₁} {Val : Type w₂}
    (sem : Prog → GapSem Query Fault Gap Val)
    (check : Prog → Cert → Bool) : Prop where
  sound : ∀ {p cert}, check p cert = true → AllGapFree (sem p)

/-- Verified boolean certificate checker for query-scoped gap-freedom (`GapFreeOn pre`). -/
structure VerifiedGapFreeOnChecker
    {Prog : Type u₁} {Cert : Type u₃} {Query : Type u}
    {Fault : Type v₁} {Gap : Type w₁} {Val : Type w₂}
    (pre : Query → Prop)
    (sem : Prog → GapSem Query Fault Gap Val)
    (check : Prog → Cert → Bool) : Prop where
  sound : ∀ {p cert}, check p cert = true → GapFreeOn pre (sem p)

/-- Verified boolean certificate checker for query-scoped `ProgramEquivOn pre`. -/
structure VerifiedProgramOnChecker
    {Prog₁ : Type u₁} {Prog₂ : Type u₂} {Cert : Type u₃} {Query : Type u}
    {Fault₁ : Type v₁} {Fault₂ : Type v₂} {Gap : Type w₁}
    {Val₁ : Type w₂} {Val₂ : Type w₃}
    (pre : Query → Prop)
    (rVal : Val₁ → Val₂ → Prop) (rFault : Fault₁ → Fault₂ → Prop)
    (sem₁ : Prog₁ → GapSem Query Fault₁ Gap Val₁)
    (sem₂ : Prog₂ → GapSem Query Fault₂ Gap Val₂)
    (check : Prog₁ → Prog₂ → Cert → Bool) : Prop where
  sound : ∀ {p₁ p₂ cert}, check p₁ p₂ cert = true →
    ProgramEquivOn pre rVal rFault (sem₁ p₁) (sem₂ p₂)

private theorem bool_and_split {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

section Checkers

variable {Prog₁ : Type u₁} {Prog₂ : Type u₂} {Cert : Type u₃} {Query : Type u}
  {Fault₁ : Type v₁} {Fault₂ : Type v₂} {Gap : Type w₁}
  {Val₁ : Type w₂} {Val₂ : Type w₃}
  {rVal : Val₁ → Val₂ → Prop} {rFault : Fault₁ → Fault₂ → Prop}
  {sem₁ : Prog₁ → GapSem Query Fault₁ Gap Val₁}
  {sem₂ : Prog₂ → GapSem Query Fault₂ Gap Val₂}
  {check : Prog₁ → Prog₂ → Cert → Bool}

/--
The syntactic-identity checker is a sound `ContextEquiv` checker for *any*
semantics: unchanged programs need no gap-freedom certificate.
-/
theorem VerifiedContextChecker.identity {Prog : Type u₁} [DecidableEq Prog]
    {Fault : Type v₁} {Val : Type w₂}
    (sem : Prog → GapSem Query Fault Gap Val) :
    VerifiedContextChecker (· = ·) (· = ·) sem sem
      (fun p₁ p₂ (_ : PUnit.{u₃ + 1}) => decide (p₁ = p₂)) where
  sound hc := by
    cases of_decide_eq_true hc
    exact ContextEquiv.refl (fun _ => rfl) (fun _ => rfl) _

/--
Compose two `ContextEquiv` checkers through an intermediate program carried in
the certificate.
-/
theorem VerifiedContextChecker.comp
    {Prog₃ : Type w₄} {Cert' : Type w₅} {Fault₃ : Type w₆} {Val₃ : Type w₇}
    {rVal' : Val₂ → Val₃ → Prop} {rFault' : Fault₂ → Fault₃ → Prop}
    {sem₃ : Prog₃ → GapSem Query Fault₃ Gap Val₃}
    {check' : Prog₂ → Prog₃ → Cert' → Bool}
    (h₁₂ : VerifiedContextChecker rVal rFault sem₁ sem₂ check)
    (h₂₃ : VerifiedContextChecker rVal' rFault' sem₂ sem₃ check') :
    VerifiedContextChecker
      (fun v₁ v₃ => ∃ v₂, rVal v₁ v₂ ∧ rVal' v₂ v₃)
      (fun e₁ e₃ => ∃ e₂, rFault e₁ e₂ ∧ rFault' e₂ e₃) sem₁ sem₃
      (fun p₁ p₃ (c : Prog₂ × Cert × Cert') =>
        check p₁ c.1 c.2.1 && check' c.1 p₃ c.2.2) where
  sound hc :=
    have hb := bool_and_split hc
    (h₁₂.sound hb.1).comp (h₂₃.sound hb.2)

/--
Upgrade a `ContextEquiv` checker with a gap-freedom checker for the baseline to
a gap-free `ProgramEquiv` checker. No gap-freedom certificate is needed for the
refactored program.
-/
theorem VerifiedContextChecker.toProgramChecker {GCert : Type w₅}
    {gapCheck : Prog₁ → GCert → Bool}
    (h : VerifiedContextChecker rVal rFault sem₁ sem₂ check)
    (hg : VerifiedGapFreeChecker sem₁ gapCheck) :
    VerifiedProgramChecker rVal rFault sem₁ sem₂
      (fun p₁ p₂ (c : Cert × GCert) => check p₁ p₂ c.1 && gapCheck p₁ c.2) where
  sound hc :=
    have hb := bool_and_split hc
    (h.sound hb.1).toProgramEquiv (hg.sound hb.2)

/-- A `ProgramEquiv` checker also certifies gap-freedom of the refactoring. -/
theorem VerifiedProgramChecker.gapFree_right
    (h : VerifiedProgramChecker rVal rFault sem₁ sem₂ check)
    {p₁ : Prog₁} {p₂ : Prog₂} {cert : Cert} (hc : check p₁ p₂ cert = true) :
    AllGapFree (sem₂ p₂) :=
  (h.sound hc).gapFree_right

theorem VerifiedProgramChecker.toContextChecker
    (h : VerifiedProgramChecker rVal rFault sem₁ sem₂ check) :
    VerifiedContextChecker rVal rFault sem₁ sem₂ check where
  sound hc := (h.sound hc).toContextEquiv

/--
A `ContextEquiv` checker whose fault relation preserves UB-ness is a verified
`ExactPass` checker on the Layer 1A projections.
-/
theorem VerifiedContextChecker.toExactChecker
    {isUB₁ : Fault₁ → Prop} {isUB₂ : Fault₂ → Prop}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    (h : VerifiedContextChecker rVal rFault sem₁ sem₂ check) :
    VerifiedExactChecker (gapSemantics isUB₁ sem₁) (gapSemantics isUB₂ sem₂)
      (gapObsMap rVal rFault)
      (gapObsMap (fun v₂ v₁ => rVal v₁ v₂) (fun e₂ e₁ => rFault e₁ e₂))
      check where
  sound hc := (h.sound hc).toExactPass hUB

theorem VerifiedContextChecker.toCompilerChecker
    {isUB₁ : Fault₁ → Prop} {isUB₂ : Fault₂ → Prop}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    (h : VerifiedContextChecker rVal rFault sem₁ sem₂ check)
    (G₁ : Spec (Query → Partial (OutcomeSet Fault₁ Gap Val₁))) :
    VerifiedCompilerChecker (gapSemantics isUB₁ sem₁) (gapSemantics isUB₂ sem₂)
      G₁ (gapObsMap rVal rFault) check :=
  (h.toExactChecker hUB).toCompilerChecker G₁

theorem VerifiedContextChecker.toVerifierChecker
    {isUB₁ : Fault₁ → Prop} {isUB₂ : Fault₂ → Prop}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    (h : VerifiedContextChecker rVal rFault sem₁ sem₂ check)
    (G₂ : Spec (Query → Partial (OutcomeSet Fault₂ Gap Val₂))) :
    VerifiedVerifierChecker (gapSemantics isUB₁ sem₁) (gapSemantics isUB₂ sem₂)
      G₂ (gapObsMap (fun v₂ v₁ => rVal v₁ v₂) (fun e₂ e₁ => rFault e₁ e₂))
      check :=
  (h.toExactChecker hUB).toVerifierChecker G₂

/--
`ContextEquiv` checker plus a gap-freedom certificate for the baseline gives a
verified `ExactPass` checker whose accepted pairs are both gap-free.
-/
theorem VerifiedContextChecker.toExactChecker_of_gapFree {GCert : Type w₅}
    {gapCheck : Prog₁ → GCert → Bool}
    {isUB₁ : Fault₁ → Prop} {isUB₂ : Fault₂ → Prop}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    (h : VerifiedContextChecker rVal rFault sem₁ sem₂ check)
    (hg : VerifiedGapFreeChecker sem₁ gapCheck) :
    VerifiedExactChecker (gapSemantics isUB₁ sem₁) (gapSemantics isUB₂ sem₂)
      (gapObsMap rVal rFault)
      (gapObsMap (fun v₂ v₁ => rVal v₁ v₂) (fun e₂ e₁ => rFault e₁ e₂))
      (fun p₁ p₂ (c : Cert × GCert) => check p₁ p₂ c.1 && gapCheck p₁ c.2) ∧
    ∀ {p₁ p₂} {c : Cert × GCert},
      (check p₁ p₂ c.1 && gapCheck p₁ c.2) = true →
        AllGapFree (sem₁ p₁) ∧ AllGapFree (sem₂ p₂) :=
  ⟨(h.toProgramChecker hg).toContextChecker.toExactChecker hUB,
   fun hc =>
     have hp := (h.toProgramChecker hg).sound hc
     ⟨hp.gapFree_left, hp.gapFree_right⟩⟩

/--
Same-relation transitive composition of two `ContextEquiv` checkers without
introducing an existential relation wrapper.
-/
theorem VerifiedContextChecker.trans
    {Prog₃ : Type w₄} {Cert' : Type w₅} {Fault : Type v₁} {Val : Type w₂}
    {rVal : Val → Val → Prop} {rFault : Fault → Fault → Prop}
    {sem₁ : Prog₁ → GapSem Query Fault Gap Val}
    {sem₂ : Prog₂ → GapSem Query Fault Gap Val}
    {sem₃ : Prog₃ → GapSem Query Fault Gap Val}
    {check : Prog₁ → Prog₂ → Cert → Bool}
    {check' : Prog₂ → Prog₃ → Cert' → Bool}
    (hVal : ∀ a b c, rVal a b → rVal b c → rVal a c)
    (hFault : ∀ a b c, rFault a b → rFault b c → rFault a c)
    (h₁₂ : VerifiedContextChecker rVal rFault sem₁ sem₂ check)
    (h₂₃ : VerifiedContextChecker rVal rFault sem₂ sem₃ check') :
    VerifiedContextChecker rVal rFault sem₁ sem₃
      (fun p₁ p₃ (c : Prog₂ × Cert × Cert') =>
        check p₁ c.1 c.2.1 && check' c.1 p₃ c.2.2) where
  sound hc :=
    have hb := bool_and_split hc
    (h₁₂.sound hb.1).trans hVal hFault (h₂₃.sound hb.2)

/-- Exact `ContextEquiv` checker induces an identity-observation `ExactPass` checker. -/
theorem VerifiedContextChecker.toExactChecker_eq {Prog : Type u₁}
    {Fault : Type v₁} {Val : Type w₂} {isUB : Fault → Prop}
    {sem : Prog → GapSem Query Fault Gap Val}
    {check : Prog → Prog → Cert → Bool}
    (h : VerifiedContextChecker (· = ·) (· = ·) sem sem check) :
    VerifiedExactChecker (gapSemantics isUB sem) (gapSemantics isUB sem)
      id id check where
  sound hc := (h.sound hc).toExactPass_eq

/--
Upgrade a `ContextEquiv` checker with a query-scoped gap-freedom checker
(`GapFreeOn pre`) for the baseline to a `ProgramEquivOn pre` checker.
-/
theorem VerifiedContextChecker.toProgramOnChecker {GCert : Type w₅}
    {pre : Query → Prop} {gapCheck : Prog₁ → GCert → Bool}
    (h : VerifiedContextChecker rVal rFault sem₁ sem₂ check)
    (hg : VerifiedGapFreeOnChecker pre sem₁ gapCheck) :
    VerifiedProgramOnChecker pre rVal rFault sem₁ sem₂
      (fun p₁ p₂ (c : Cert × GCert) => check p₁ p₂ c.1 && gapCheck p₁ c.2) where
  sound hc :=
    have hb := bool_and_split hc
    (h.sound hb.1).toProgramEquivOn (hg.sound hb.2)

theorem VerifiedProgramOnChecker.gapFree_right {pre : Query → Prop}
    (h : VerifiedProgramOnChecker pre rVal rFault sem₁ sem₂ check)
    {p₁ : Prog₁} {p₂ : Prog₂} {cert : Cert} (hc : check p₁ p₂ cert = true) :
    GapFreeOn pre (sem₂ p₂) :=
  (h.sound hc).gapFree_right

/--
Query-scoped upgrade: `ContextEquiv` checker plus a `GapFreeOn pre` certificate
for the baseline yields a verified `ExactPass` checker over `{q // pre q}` whose
accepted pairs are both gap-free on `pre`.
-/
theorem VerifiedContextChecker.toExactChecker_of_gapFreeOn {GCert : Type w₅}
    {pre : Query → Prop} {gapCheck : Prog₁ → GCert → Bool}
    {isUB₁ : Fault₁ → Prop} {isUB₂ : Fault₂ → Prop}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    (h : VerifiedContextChecker rVal rFault sem₁ sem₂ check)
    (hg : VerifiedGapFreeOnChecker pre sem₁ gapCheck) :
    VerifiedExactChecker
        (gapSemantics isUB₁ (fun p => (sem₁ p).restrict pre))
        (gapSemantics isUB₂ (fun p => (sem₂ p).restrict pre))
        (gapObsMap rVal rFault)
        (gapObsMap (fun v₂ v₁ => rVal v₁ v₂) (fun e₂ e₁ => rFault e₁ e₂))
        (fun p₁ p₂ (c : Cert × GCert) => check p₁ p₂ c.1 && gapCheck p₁ c.2) ∧
      ∀ {p₁ p₂} {c : Cert × GCert},
        (check p₁ p₂ c.1 && gapCheck p₁ c.2) = true →
          GapFreeOn pre (sem₁ p₁) ∧ GapFreeOn pre (sem₂ p₂) :=
  ⟨{ sound := fun hc => ((h.toProgramOnChecker hg).sound hc).toContextEquivOn.toExactPass hUB },
   fun hc =>
     have hp := (h.toProgramOnChecker hg).sound hc
     ⟨hp.gapFree_left, hp.gapFree_right⟩⟩

/--
Exact-relation query-scoped upgrade: `VerifiedContextChecker (· = ·) (· = ·)`
paired with a `VerifiedGapFreeOnChecker pre` for the baseline yields an
identity-observation `VerifiedExactChecker` over `{q // pre q}` whose accepted
pairs are both gap-free on `pre`.
-/
theorem VerifiedContextChecker.toExactChecker_eq_of_gapFreeOn
    {Prog : Type u₁} {GCert : Type w₅} {Fault : Type v₁} {Val : Type w₂}
    {pre : Query → Prop} {isUB : Fault → Prop}
    {sem : Prog → GapSem Query Fault Gap Val}
    {check : Prog → Prog → Cert → Bool}
    {gapCheck : Prog → GCert → Bool}
    (h : VerifiedContextChecker (· = ·) (· = ·) sem sem check)
    (hg : VerifiedGapFreeOnChecker pre sem gapCheck) :
    VerifiedExactChecker
        (gapSemantics isUB (fun p => (sem p).restrict pre))
        (gapSemantics isUB (fun p => (sem p).restrict pre))
        id id
        (fun p₁ p₂ (c : Cert × GCert) => check p₁ p₂ c.1 && gapCheck p₁ c.2) ∧
      ∀ {p₁ p₂} {c : Cert × GCert},
        (check p₁ p₂ c.1 && gapCheck p₁ c.2) = true →
          GapFreeOn pre (sem p₁) ∧ GapFreeOn pre (sem p₂) :=
  ⟨{ sound := fun hc =>
       have hb := bool_and_split hc
       ContextEquiv.toExactPass_eq
         (sem := fun p => (sem p).restrict pre)
         (contextEquivOn_iff_restrict.mp ((h.sound hb.1).on pre)) },
   fun hc =>
     have hp := (h.toProgramOnChecker hg).sound hc
     ⟨hp.gapFree_left, hp.gapFree_right⟩⟩

end Checkers


/-! ### Fuel-free equivalence from bounded runs -/

section BoundedToFuelFree

variable {State₁ : Type u} {State₂ : Type v₁} {Fault₁ : Type u₁} {Fault₂ : Type v₂}
  {Site : Type u₂} {Val₁ : Type u₃} {Val₂ : Type w₁}
  {next₁ : State₁ → GapStep State₁ Fault₁ (GapTag Site) Val₁}
  {next₂ : State₂ → GapStep State₂ Fault₂ (GapTag Site) Val₂}
  {rVal : Val₁ → Val₂ → Prop} {rFault : Fault₁ → Fault₂ → Prop}

/--
Two bounded runs (with possibly different budgets) that finish with related
outcomes determine equivalent fuel-free behavior sets.
-/
theorem gapBehaviors_equiv_of_runs {s₁ : State₁} {s₂ : State₂} {fuel₁ fuel₂ : Nat}
    (hne : runGapSteps next₁ fuel₁ s₁ ≠ .gap .outOfFuel)
    (h : GapEqErr rVal rFault (runGapSteps next₁ fuel₁ s₁)
      (runGapSteps next₂ fuel₂ s₂)) :
    OutcomeSetEquiv (GapEqErr rVal rFault)
      (gapBehaviors next₁ s₁) (gapBehaviors next₂ s₂) := by
  have hne₂ : runGapSteps next₂ fuel₂ s₂ ≠ .gap .outOfFuel := fun h₀ =>
    hne (GapEqErr.gap_iff_right.mp (h₀ ▸ h))
  constructor
  · intro o₁ ho₁
    cases (gapBehaviors_iff_of_run next₁ hne o₁).mp ho₁
    exact ⟨_, gapBehaviors_of_run next₂ hne₂, h⟩
  · intro o₂ ho₂
    cases (gapBehaviors_iff_of_run next₂ hne₂ o₂).mp ho₂
    exact ⟨_, gapBehaviors_of_run next₁ hne, h⟩

/--
For two finished bounded runs, equivalence of the fuel-free behavior sets is
exactly `GapEqErr` of the two outcomes. The forward direction is the tool for
*refuting* an equivalence from two concrete runs.
-/
theorem gapBehaviors_equiv_iff_of_runs {s₁ : State₁} {s₂ : State₂}
    {fuel₁ fuel₂ : Nat}
    (hne₁ : runGapSteps next₁ fuel₁ s₁ ≠ .gap .outOfFuel)
    (hne₂ : runGapSteps next₂ fuel₂ s₂ ≠ .gap .outOfFuel) :
    OutcomeSetEquiv (GapEqErr rVal rFault)
        (gapBehaviors next₁ s₁) (gapBehaviors next₂ s₂) ↔
      GapEqErr rVal rFault (runGapSteps next₁ fuel₁ s₁)
        (runGapSteps next₂ fuel₂ s₂) := by
  constructor
  · intro h
    obtain ⟨o₂, ho₂, hr⟩ := h.forward (gapBehaviors_of_run next₁ hne₁)
    cases (gapBehaviors_iff_of_run next₂ hne₂ o₂).mp ho₂
    exact hr
  · exact gapBehaviors_equiv_of_runs hne₁

/-- A finished bounded run that is gap-free makes the fuel-free set gap-free. -/
theorem neverGap_gapBehaviors_of_run {s₁ : State₁} {fuel : Nat}
    (h : (runGapSteps next₁ fuel s₁).isGapFree) :
    NeverGap (gapBehaviors next₁ s₁) :=
  gapBehaviors_all_of_run next₁ (fun h₀ => by rw [h₀] at h; exact h) h

/--
A finished bounded run that is defined (gap-free and not UB) makes the
fuel-free set defined.
-/
theorem defined_gapBehaviors_of_run {isUB : Fault₁ → Prop} {s₁ : State₁}
    {fuel : Nat} (h : (runGapSteps next₁ fuel s₁).isDefined isUB) :
    OutcomeSet.Defined isUB (gapBehaviors next₁ s₁) :=
  gapBehaviors_all_of_run next₁
    (fun h₀ => by rw [h₀] at h; exact h) h

end BoundedToFuelFree

/-! ## 7. `MirStepNode` Instantiation over `V2026_06_01` MIR

`stepMirState body : MirExecState → MirStepNode` is an `ITreeF` coalgebra over
`MirEffect = SumE MirFailE (SumE MirObsE MirCallE)`. Its gap-aware evaluator
erases `MirObsE` observations, delegates unresolved `MirCallE` calls to a callee
environment, and tags every `MirStepNode.unsupported` with the `DefPath` of the
body whose code was executing.
-/

section MirGap

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/--
MIR execution state preserving gap-site attribution across post-call
continuations. While `.running s`, the active failure site is computed directly
from `s` via `mirRunningFailSite body s` (so a stale site can never be attached
to a running state); when an external-call continuation (`resumeExternalCall`
or `resumeExternalTailCall`) transitions directly into `.faulted fk`, the
`site` payload retains the `DefPath` of the frame that owned the failing
destination rather than falling back to the root `body.defPath`.
-/
inductive MirSiteState : Type where
  | running (s : MachineState)
  | halted (out : MirOutcome)
  | faulted (fk : FailureKind) (site : DefPath)

/-- Project `MirSiteState` back to its underlying `MirExecState`. -/
def MirSiteState.exec : MirSiteState → MirExecState
  | .running s => .running s
  | .halted out => .halted out
  | .faulted fk _ => .faulted fk

/--
Shared helper classifying whether the active terminator delegates a destination
write to `caller.callerBody` (`forReturn = true` for `TerminatorKind.return_`,
`forReturn = false` for `TerminatorKind.tailCall`).
-/
private def mirTerminatorCallerSite (curBody : CapturedMir) (s : MachineState)
    (forReturn : Bool) : DefPath :=
  match s.memory.callStack with
  | [] => curBody.defPath
  | caller :: _ =>
    match Trusted.Sequence.get? curBody.basicBlocks s.frame.blockIdx with
    | none => curBody.defPath
    | some bb =>
      if s.frame.stmtIdx == Trusted.Sequence.length bb.statements then
        match bb.terminator.kind with
        | .return_ => if forReturn then caller.callerBody.defPath else curBody.defPath
        | .tailCall _ _ => if forReturn then curBody.defPath else caller.callerBody.defPath
        | _ => curBody.defPath
      else curBody.defPath

/--
Failure-owner `DefPath` for an immediate `MirStepNode.unsupported` or budget
failure raised while stepping `s` under root `body`.

- When the active body's `phase` is `.other _`, `stepMirFn` fails closed before
  consulting `basicBlocks`, so the gap belongs to `(s.memory.activeCallee.getD body).defPath`.
- When a modeled-phase inline callee (`s.memory.callStack = caller :: _`)
  executes `TerminatorKind.return_`, the only `MirStepNode.unsupported` outcome
  comes from `writeReturnDestination` failing on `caller.destination`, so the
  gap belongs to `caller.callerBody.defPath` (consistent with `mirPostCallSite`
  for `TerminatorKind.tailCall`).
- Otherwise, the gap belongs to `(s.memory.activeCallee.getD body).defPath`.
-/
def mirRunningFailSite (body : CapturedMir) (s : MachineState) : DefPath :=
  let curBody := s.memory.activeCallee.getD body
  match curBody.phase with
  | .other _ => curBody.defPath
  | _ => mirTerminatorCallerSite curBody s true

/--
Destination-owner `DefPath` for a `.faulted` state produced from `s` in `body`:
for a non-root `TerminatorKind.tailCall` (`s.memory.callStack = caller :: _`),
`resumeExternalTailCall` writes into `caller.callerBody`; otherwise
`resumeExternalCall` writes into the active frame `(s.memory.activeCallee.getD body)`.
-/
def mirPostCallSite (body : CapturedMir) (s : MachineState) : DefPath :=
  mirTerminatorCallerSite (s.memory.activeCallee.getD body) s false

/-- Embed a `MirExecState` into `MirSiteState` under root `body`. -/
def mirSiteOfExec (body : CapturedMir) : MirExecState → MirSiteState
  | .running s => .running s
  | .halted out => .halted out
  | .faulted fk => .faulted fk body.defPath

/-- Advance `MirSiteState` across a `stepMirState body` child `es'`. -/
def mirNextSiteState (body : CapturedMir) (st : MirSiteState) :
    MirExecState → MirSiteState
  | .running s' => .running s'
  | .halted out => .halted out
  | .faulted fk =>
    match st with
    | .running s => .faulted fk (mirPostCallSite body s)
    | .halted _ => .faulted fk body.defPath
    | .faulted _ site => .faulted fk site

/-- Site-preserving coalgebra lifting `stepMirState body` to `MirSiteState`. -/
def stepMirSiteState (body : CapturedMir) (st : MirSiteState) :
    ITreeF MirEffect MirOutcome MirSiteState :=
  (stepMirState body st.exec).map (mirNextSiteState body st)

/-- Effective failure-owner `DefPath` of a `MirSiteState` under root `body`. -/
def mirSiteOfState (body : CapturedMir) : MirSiteState → DefPath
  | .running s => mirRunningFailSite body s
  | .halted _ => body.defPath
  | .faulted _ site => site

/--
External-callee fault that bypasses the caller's unwind continuation: undefined
behavior (`ub`) only. Callee panics and aborts must be returned via
`MirCallAns.panicked` and `MirCallAns.aborted` so the caller's `UnwindAction`
(`cleanup`, `terminate`, `unreachable`, `continue_`) always executes faithfully
and never hides UB under a `nounwind` (`UnwindAction.unreachable`) call.
-/
inductive CalleeFault : Type where
  /-- Undefined behavior inside the external callee. -/
  | ub
  deriving DecidableEq

/--
Callee environment: gap-aware semantics of the external calls a body makes.
Normal returns, panics, and aborts flow through `MirCallAns` into the caller's
continuation (`resumeExternalCall` / `resumeExternalDivergingCall` /
`resumeExternalTailCall`); only callee UB (`CalleeFault.ub`) and modeling gaps
(`GapTag DefPath`) short-circuit the caller directly.
-/
abbrev MirCallEnv : Type :=
  MirCallReq → OutcomeWithGap CalleeFault (GapTag DefPath) MirCallAns

/--
A `MirCallEnv` is sealed when it never emits the outer evaluator's own
`GapTag.outOfFuel` sentinel (converting inner callee fuel exhaustion to
site-tagged `GapTag.budget req.defPath` via `GapTag.sealOutOfFuel`).
-/
def MirCallEnv.IsSealed (env : MirCallEnv) : Prop :=
  ∀ req, env req ≠ .gap .outOfFuel

/-- Seal any `MirCallEnv` by mapping `.gap .outOfFuel` to `.gap (.budget req.defPath)`. -/
def MirCallEnv.seal (env : MirCallEnv) : MirCallEnv :=
  fun req => (env req).mapGap (·.sealOutOfFuel req.defPath)

/-- Closed-world environment: every external call is an `unresolved` gap. -/
def MirCallEnv.unresolved : MirCallEnv :=
  fun req => .gap (.unresolved req.defPath)

/--
Environment of memory-preserving callee summaries: `f defPath args` is the
gap-aware result of calling `defPath` on `args`. Defined callee failures
(`.fault .panic`, `.fault .abort`) are routed through `MirCallAns.panicked` and
`MirCallAns.aborted` so the caller's `UnwindAction` runs faithfully, and inner
`.outOfFuel` gaps are sealed to `.budget req.defPath` so they never collide with
the outer caller evaluator's step budget.
-/
def MirCallEnv.ofPure
    (f : DefPath → List Value → OutcomeWithGap ExecFault (GapTag DefPath) Value) :
    MirCallEnv :=
  fun req =>
    match f req.defPath req.args with
    | .ok v => .ok (.returned v req.memory)
    | .fault .panic => .ok (.panicked req.memory)
    | .fault .abort => .ok .aborted
    | .fault .ub => .fault .ub
    | .gap g => .gap (g.sealOutOfFuel req.defPath)

/--
Lift a `MirReturn`-producing gap-aware callee summary into a sealed `MirCallEnv`
(for callees whose panics do not mutate caller-visible memory prior to
unwinding; for stateful panics that mutate memory before unwinding, use
`MirCallEnv.ofCallSummary`).
-/
def MirCallEnv.ofMirOutcome
    (f : MirCallReq → OutcomeWithGap ExecFault (GapTag DefPath) MirReturn) :
    MirCallEnv :=
  fun req =>
    match f req with
    | .ok (v, memAfter) => .ok (.returned v memAfter)
    | .fault .panic => .ok (.panicked req.memory)
    | .fault .abort => .ok .aborted
    | .fault .ub => .fault .ub
    | .gap g => .gap (g.sealOutOfFuel req.defPath)

/--
Lift a full stateful `MirCallAns`-producing callee summary (including stateful
post-panic `MirCallAns.panicked memAfter`) into a sealed `MirCallEnv`.
-/
def MirCallEnv.ofCallSummary
    (f : MirCallReq → OutcomeWithGap CalleeFault (GapTag DefPath) MirCallAns) :
    MirCallEnv :=
  MirCallEnv.seal f

theorem MirCallEnv.isSealed_seal (env : MirCallEnv) : (MirCallEnv.seal env).IsSealed := by
  intro req
  dsimp only [MirCallEnv.seal]
  cases env req with
  | ok _ => exact fun h => by cases h
  | fault _ => exact fun h => by cases h
  | gap g =>
    intro h
    exact GapTag.sealOutOfFuel_ne_outOfFuel req.defPath g (OutcomeWithGap.gap.inj h)

theorem MirCallEnv.isSealed_unresolved : MirCallEnv.unresolved.IsSealed :=
  fun _ h => by cases h

theorem MirCallEnv.isSealed_ofPure
    (f : DefPath → List Value → OutcomeWithGap ExecFault (GapTag DefPath) Value) :
    (MirCallEnv.ofPure f).IsSealed := by
  intro req
  unfold MirCallEnv.ofPure
  cases f req.defPath req.args with
  | ok _ => exact fun h => by cases h
  | fault e => cases e <;> exact fun h => by cases h
  | gap g =>
    intro h
    exact GapTag.sealOutOfFuel_ne_outOfFuel req.defPath g (OutcomeWithGap.gap.inj h)

theorem MirCallEnv.isSealed_ofMirOutcome
    (f : MirCallReq → OutcomeWithGap ExecFault (GapTag DefPath) MirReturn) :
    (MirCallEnv.ofMirOutcome f).IsSealed := by
  intro req
  unfold MirCallEnv.ofMirOutcome
  cases f req with
  | ok _ => exact fun h => by cases h
  | fault e => cases e <;> exact fun h => by cases h
  | gap g =>
    intro h
    exact GapTag.sealOutOfFuel_ne_outOfFuel req.defPath g (OutcomeWithGap.gap.inj h)

theorem MirCallEnv.isSealed_ofCallSummary
    (f : MirCallReq → OutcomeWithGap CalleeFault (GapTag DefPath) MirCallAns) :
    (MirCallEnv.ofCallSummary f).IsSealed :=
  MirCallEnv.isSealed_seal f

/-- An external-call answer preserves the caller's suspended `callStack`. -/
def MirCallAns.PreservesCallStack (req : MirCallReq) : MirCallAns → Prop
  | .returned _ memAfter => memAfter.callStack = req.memory.callStack
  | .panicked memAfter => memAfter.callStack = req.memory.callStack
  | .aborted => True

/-- Every `.ok` answer returned by `env` preserves the caller's `callStack`. -/
def MirCallEnv.PreservesCallStack (env : MirCallEnv) : Prop :=
  ∀ req ans, env req = .ok ans → MirCallAns.PreservesCallStack req ans

/--
Restore the caller's suspended frame metadata (`callees`, `traitImpls`,
`callStack`, `activeCallee`, `activeProtectors`, and existing `fnPtrs`) onto a
`Memory` returned by a **stateful** callee summary that executed starting from
`before` (so `after` already carries the caller's `borrows`, `globals`,
`callerLocals`, and monotonic tag/alloc counters). For a **standalone** summary
executed from an isolated fresh `initMachineState`, use
`Memory.preserveCallerMemory` instead so caller borrows and globals are never
wiped.
-/
def Memory.restoreCallerFrame (before after : Memory) : Memory :=
  { after with
    callees := before.callees
    traitImpls := before.traitImpls
    callStack := before.callStack
    activeCallee := before.activeCallee
    activeProtectors := before.activeProtectors
    fnPtrs := List.append after.fnPtrs before.fnPtrs }

theorem Memory.callFramePreserved_restoreCallerFrame (before after : Memory) :
    Trusted.VerificationResult.callFramePreserved before
      (Memory.restoreCallerFrame before after) :=
  ⟨rfl, rfl, rfl, rfl, ⟨after.fnPtrs, rfl⟩⟩

/--
Preserve the caller's entire `Memory` (`borrows`, `globals`, `callerLocals`,
`traitImpls`, allocator/tag/protector counters, and call frame) across a
**standalone** callee run started from an isolated initial state, retaining any
newly reified `fnPtrs` returned by the callee.
-/
def Memory.preserveCallerMemory (before after : Memory) : Memory :=
  { before with fnPtrs := List.append after.fnPtrs before.fnPtrs }

theorem Memory.callFramePreserved_preserveCallerMemory (before after : Memory) :
    Trusted.VerificationResult.callFramePreserved before
      (Memory.preserveCallerMemory before after) :=
  ⟨rfl, rfl, rfl, rfl, ⟨after.fnPtrs, rfl⟩⟩

theorem Memory.callFramePreserved_refl (mem : Memory) :
    Trusted.VerificationResult.callFramePreserved mem mem :=
  ⟨rfl, rfl, rfl, rfl, ⟨[], rfl⟩⟩

/--
An external-call answer satisfies `Trusted.VerificationResult.callFramePreserved`
against `req.memory`.
-/
def MirCallAns.PreservesCallFrame (req : MirCallReq) : MirCallAns → Prop
  | .returned _ memAfter =>
    Trusted.VerificationResult.callFramePreserved req.memory memAfter
  | .panicked memAfter =>
    Trusted.VerificationResult.callFramePreserved req.memory memAfter
  | .aborted => True

/-- Every `.ok` answer returned by `env` satisfies `callFramePreserved`. -/
def MirCallEnv.PreservesCallFrame (env : MirCallEnv) : Prop :=
  ∀ req ans, env req = .ok ans → MirCallAns.PreservesCallFrame req ans

theorem MirCallAns.PreservesCallFrame.toPreservesCallStack {req : MirCallReq}
    {ans : MirCallAns} (h : MirCallAns.PreservesCallFrame req ans) :
    MirCallAns.PreservesCallStack req ans := by
  cases ans with
  | returned _ _ => exact h.2.1
  | panicked _ => exact h.2.1
  | aborted => exact trivial

theorem MirCallEnv.PreservesCallFrame.toPreservesCallStack {env : MirCallEnv}
    (h : env.PreservesCallFrame) : env.PreservesCallStack :=
  fun req ans ho => (h req ans ho).toPreservesCallStack

theorem MirCallEnv.unresolved_preservesCallFrame :
    MirCallEnv.unresolved.PreservesCallFrame :=
  fun _ _ h => by cases h

theorem MirCallEnv.ofPure_preservesCallFrame
    (f : DefPath → List Value → OutcomeWithGap ExecFault (GapTag DefPath) Value) :
    (MirCallEnv.ofPure f).PreservesCallFrame := by
  intro req ans h
  unfold MirCallEnv.ofPure at h
  cases hf : f req.defPath req.args with
  | ok v => rw [hf] at h; cases h; exact Memory.callFramePreserved_refl req.memory
  | fault e =>
    rw [hf] at h
    cases e with
    | ub => cases h
    | panic => cases h; exact Memory.callFramePreserved_refl req.memory
    | abort => cases h; exact trivial
  | gap g => rw [hf] at h; cases h

theorem MirCallEnv.unresolved_preservesCallStack :
    MirCallEnv.unresolved.PreservesCallStack :=
  MirCallEnv.unresolved_preservesCallFrame.toPreservesCallStack

theorem MirCallEnv.ofPure_preservesCallStack
    (f : DefPath → List Value → OutcomeWithGap ExecFault (GapTag DefPath) Value) :
    (MirCallEnv.ofPure f).PreservesCallStack :=
  (MirCallEnv.ofPure_preservesCallFrame f).toPreservesCallStack

/--
Lift a **stateful** `MirReturn`-producing summary (executed starting from
`req.memory`) into a sealed, frame-preserving `MirCallEnv` via
`Memory.restoreCallerFrame` (keeping `memAfter`'s heap/borrow mutations while
restoring caller call-frame metadata). Do NOT use this on disconnected
standalone runs starting from empty `initMachineState` (which would wipe out
caller `borrows`, `globals`, and `callerLocals`); use `MirCallEnv.ofStandaloneOutcome`
or `MirCallEnv.ofStandaloneBody` for standalone runs.
-/
def MirCallEnv.ofStatefulOutcome
    (f : MirCallReq → OutcomeWithGap ExecFault (GapTag DefPath) MirReturn) :
    MirCallEnv :=
  fun req =>
    match f req with
    | .ok (v, memAfter) =>
      .ok (.returned v (Memory.restoreCallerFrame req.memory memAfter))
    | .fault .panic => .ok (.panicked req.memory)
    | .fault .abort => .ok .aborted
    | .fault .ub => .fault .ub
    | .gap g => .gap (g.sealOutOfFuel req.defPath)

theorem MirCallEnv.isSealed_ofStatefulOutcome
    (f : MirCallReq → OutcomeWithGap ExecFault (GapTag DefPath) MirReturn) :
    (MirCallEnv.ofStatefulOutcome f).IsSealed := by
  intro req
  unfold MirCallEnv.ofStatefulOutcome
  cases f req with
  | ok _ => exact fun h => by cases h
  | fault e => cases e <;> exact fun h => by cases h
  | gap g =>
    intro h
    exact GapTag.sealOutOfFuel_ne_outOfFuel req.defPath g (OutcomeWithGap.gap.inj h)

theorem MirCallEnv.ofStatefulOutcome_preservesCallFrame
    (f : MirCallReq → OutcomeWithGap ExecFault (GapTag DefPath) MirReturn) :
    (MirCallEnv.ofStatefulOutcome f).PreservesCallFrame := by
  intro req ans h
  unfold MirCallEnv.ofStatefulOutcome at h
  cases hf : f req with
  | ok vm =>
    rw [hf] at h
    cases vm
    cases h
    exact Memory.callFramePreserved_restoreCallerFrame req.memory _
  | fault e =>
    rw [hf] at h
    cases e with
    | ub => cases h
    | panic => cases h; exact Memory.callFramePreserved_refl req.memory
    | abort => cases h; exact trivial
  | gap g => rw [hf] at h; cases h

/--
Lift a **standalone** `MirReturn`-producing summary (such as `runMirWithGap` on
an external `CapturedMir` body, whose fresh `initMachineState` starts with empty
`borrows`, `callStack = []`, and `activeCallee = none`) into a sealed,
caller-memory-preserving `MirCallEnv` via `Memory.preserveCallerMemory`. Unlike
raw `MirCallEnv.ofMirOutcome` or `MirCallEnv.ofStatefulOutcome`, this preserves
both the caller's call frame AND the caller's live `borrows`, `globals`,
`callerLocals`, `traitImpls`, and allocator/tag counters.
-/
def MirCallEnv.ofStandaloneOutcome
    (f : MirCallReq → OutcomeWithGap ExecFault (GapTag DefPath) MirReturn) :
    MirCallEnv :=
  fun req =>
    match f req with
    | .ok (v, memAfter) =>
      .ok (.returned v (Memory.preserveCallerMemory req.memory memAfter))
    | .fault .panic => .ok (.panicked req.memory)
    | .fault .abort => .ok .aborted
    | .fault .ub => .fault .ub
    | .gap g => .gap (g.sealOutOfFuel req.defPath)

theorem MirCallEnv.isSealed_ofStandaloneOutcome
    (f : MirCallReq → OutcomeWithGap ExecFault (GapTag DefPath) MirReturn) :
    (MirCallEnv.ofStandaloneOutcome f).IsSealed := by
  intro req
  unfold MirCallEnv.ofStandaloneOutcome
  cases f req with
  | ok _ => exact fun h => by cases h
  | fault e => cases e <;> exact fun h => by cases h
  | gap g =>
    intro h
    exact GapTag.sealOutOfFuel_ne_outOfFuel req.defPath g (OutcomeWithGap.gap.inj h)

theorem MirCallEnv.ofStandaloneOutcome_preservesCallFrame
    (f : MirCallReq → OutcomeWithGap ExecFault (GapTag DefPath) MirReturn) :
    (MirCallEnv.ofStandaloneOutcome f).PreservesCallFrame := by
  intro req ans h
  unfold MirCallEnv.ofStandaloneOutcome at h
  cases hf : f req with
  | ok vm =>
    rw [hf] at h
    cases vm
    cases h
    exact Memory.callFramePreserved_preserveCallerMemory req.memory _
  | fault e =>
    rw [hf] at h
    cases e with
    | ub => cases h
    | panic => cases h; exact Memory.callFramePreserved_refl req.memory
    | abort => cases h; exact trivial
  | gap g => rw [hf] at h; cases h

/--
Two `MirCallReq`s targeting the same `defPath` and `args` (even with different
caller `Memory` states, such as distinct borrow-tag counters) produce
`GapEqErr`-related outcomes under `MirCallEnv.ofPure f`.
-/
theorem MirCallEnv.ofPure_rel_of_same_target
    (f : DefPath → List Value → OutcomeWithGap ExecFault (GapTag DefPath) Value)
    {req₁ req₂ : MirCallReq}
    (hPath : req₁.defPath = req₂.defPath) (hArgs : req₁.args = req₂.args) :
    GapEqErr
      (fun a₁ a₂ =>
        (∃ v, a₁ = .returned v req₁.memory ∧ a₂ = .returned v req₂.memory) ∨
        (a₁ = .panicked req₁.memory ∧ a₂ = .panicked req₂.memory) ∨
        (a₁ = .aborted ∧ a₂ = .aborted))
      (· = ·)
      (MirCallEnv.ofPure f req₁) (MirCallEnv.ofPure f req₂) := by
  unfold MirCallEnv.ofPure
  rw [← hPath, ← hArgs]
  cases f req₁.defPath req₁.args with
  | ok v => exact Or.inl ⟨v, rfl, rfl⟩
  | fault e =>
    cases e with
    | ub => exact (rfl : CalleeFault.ub = CalleeFault.ub)
    | panic => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | abort => exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  | gap g =>
    exact (rfl : g.sealOutOfFuel req₁.defPath = g.sealOutOfFuel req₁.defPath)

/--
Handler for the non-fault MIR effects: erase observations, delegate calls, and
unconditionally seal any callee `.gap .outOfFuel` into `.gap (.budget req.defPath)`
at the handler boundary so no raw `MirCallEnv` can collide with the outer
evaluator's step-budget sentinel.
-/
def mirGapHandle (env : MirCallEnv) :
    (i : (SumE MirObsE MirCallE).I) →
      OutcomeWithGap ExecFault (GapTag DefPath) ((SumE MirObsE MirCallE).O i)
  | .inl (.emit _) => .ok PUnit.unit
  | .inr (.call req) =>
    ((env req).mapFault (fun _ => .ub)).mapGap (·.sealOutOfFuel req.defPath)

/-- Extract an `.ok` callee answer from `mirGapHandle env (.inr (.call req))`. -/
theorem mirGapHandle_call_eq_ok {env : MirCallEnv} {req : MirCallReq} {ans : MirCallAns}
    (h : mirGapHandle env (.inr (.call req)) = .ok ans) :
    env req = .ok ans := by
  dsimp only [mirGapHandle] at h
  cases he : env req with
  | ok a => rw [he] at h; cases h; rfl
  | fault _ => rw [he] at h; cases h
  | gap _ => rw [he] at h; cases h

/-- For a sealed environment, `mirGapHandle` acts as `mapFault` on external calls. -/
theorem mirGapHandle_call_of_isSealed {env : MirCallEnv} (hSealed : env.IsSealed)
    (req : MirCallReq) :
    mirGapHandle env (.inr (.call req)) = (env req).mapFault (fun _ => .ub) := by
  dsimp only [mirGapHandle]
  cases he : env req with
  | ok _ => rfl
  | fault _ => rfl
  | gap g =>
    dsimp only [OutcomeWithGap.mapFault, OutcomeWithGap.mapGap]
    rw [GapTag.sealOutOfFuel_eq_self req.defPath (fun hg => hSealed req (hg ▸ he))]
    rfl

/--
`mirGapHandle (MirCallEnv.ofPure f)` relates any two `MirCallReq`s targeting
the same `defPath` and `args`, even when their caller `Memory` states differ.
-/
theorem MirCallEnv.mirGapHandle_ofPure_rel_of_same_target
    (f : DefPath → List Value → OutcomeWithGap ExecFault (GapTag DefPath) Value)
    {req₁ req₂ : MirCallReq}
    (hPath : req₁.defPath = req₂.defPath) (hArgs : req₁.args = req₂.args) :
    GapEqErr
      (fun a₁ a₂ =>
        (∃ v, a₁ = .returned v req₁.memory ∧ a₂ = .returned v req₂.memory) ∨
        (a₁ = .panicked req₁.memory ∧ a₂ = .panicked req₂.memory) ∨
        (a₁ = .aborted ∧ a₂ = .aborted))
      (· = ·)
      (mirGapHandle (MirCallEnv.ofPure f) (.inr (.call req₁)))
      (mirGapHandle (MirCallEnv.ofPure f) (.inr (.call req₂))) := by
  rw [mirGapHandle_call_of_isSealed (MirCallEnv.isSealed_ofPure f) req₁,
    mirGapHandle_call_of_isSealed (MirCallEnv.isSealed_ofPure f) req₂]
  exact (MirCallEnv.ofPure_rel_of_same_target f hPath hArgs).mapFault_congr
    (fun _ _ _ => rfl)

/-- Extract the underlying pure summary result from a `.returned` handler answer. -/
theorem MirCallEnv.mirGapHandle_ofPure_eq_ok_returned
    {f : DefPath → List Value → OutcomeWithGap ExecFault (GapTag DefPath) Value}
    {req : MirCallReq} {v : Value} {mem : Memory}
    (h : mirGapHandle (MirCallEnv.ofPure f) (.inr (.call req)) =
      .ok (.returned v mem)) :
    f req.defPath req.args = .ok v ∧ mem = req.memory := by
  dsimp only [mirGapHandle, MirCallEnv.ofPure] at h
  cases hf : f req.defPath req.args with
  | ok w =>
    rw [hf] at h
    cases h
    exact ⟨rfl, rfl⟩
  | fault e =>
    rw [hf] at h
    cases e <;> cases h
  | gap g =>
    rw [hf] at h
    cases h

/-- One site-preserving gap-classified step of `body` against `env`. -/
def mirSiteGapStep (env : MirCallEnv) (body : CapturedMir) :
    MirSiteState → GapStep MirSiteState ExecFault (GapTag DefPath) MirReturn :=
  gapStep (stepMirSiteState body) (mirSiteOfState body) (mirGapHandle env)

/-- Fuel-indexed site-preserving gap-aware evaluator over `stepMirSiteState body`. -/
def runMirSiteStepsWithGap (env : MirCallEnv) (body : CapturedMir) (fuel : Nat)
    (st : MirSiteState) : OutcomeWithGap ExecFault (GapTag DefPath) MirReturn :=
  runGapSteps (mirSiteGapStep env body) fuel st

/--
Fuel-indexed gap-aware evaluator starting from `MirExecState` (via
`mirSiteOfExec body s`, preserving active-callee and return-destination gap
sites across post-call continuations).
-/
def runMirStepsWithGap (env : MirCallEnv) (body : CapturedMir) (fuel : Nat)
    (s : MirExecState) : OutcomeWithGap ExecFault (GapTag DefPath) MirReturn :=
  runMirSiteStepsWithGap env body fuel (mirSiteOfExec body s)

/-- Run `body` on `args` with inline callee bodies `callees`. -/
def runMirWithGap (env : MirCallEnv) (callees : List CapturedMir)
    (body : CapturedMir) (fuel : Nat) (args : List Value) :
    OutcomeWithGap ExecFault (GapTag DefPath) MirReturn :=
  runMirStepsWithGap env body fuel
    (.running (initMachineStateWithCallees body args callees))

/-- Deterministic fuel-indexed gap-aware semantics of `body` over arguments. -/
def mirGapSem (env : MirCallEnv) (callees : List CapturedMir) (fuel : Nat)
    (body : CapturedMir) :
    GapSem (List Value) ExecFault (GapTag DefPath) MirReturn :=
  GapSem.det (runMirWithGap env callees body fuel)

/-- Fuel-free gap-aware semantics of `body` over arguments. -/
def mirGapBehaviors (env : MirCallEnv) (callees : List CapturedMir)
    (body : CapturedMir) :
    GapSem (List Value) ExecFault (GapTag DefPath) MirReturn :=
  fun args => gapBehaviors (mirSiteGapStep env body)
    (mirSiteOfExec body (.running (initMachineStateWithCallees body args callees)))

/-- Layer 1A `Language` of `CapturedMir` bodies under gap-aware semantics. -/
def mirGapLanguage (env : MirCallEnv) (callees : List CapturedMir) : Language :=
  gapLanguage ExecFault.isUB (mirGapBehaviors env callees)

variable {env : MirCallEnv} {body : CapturedMir}

theorem runMirSiteStepsWithGap_eq (fuel : Nat) (st : MirSiteState) :
    runMirSiteStepsWithGap env body fuel st =
      runStepsWithGap (stepMirSiteState body) (mirSiteOfState body) (mirGapHandle env)
        fuel st := rfl

theorem runMirStepsWithGap_eq (fuel : Nat) (s : MirExecState) :
    runMirStepsWithGap env body fuel s =
      runStepsWithGap (stepMirSiteState body) (mirSiteOfState body) (mirGapHandle env)
        fuel (mirSiteOfExec body s) := rfl

theorem mirPostCallSite_of_root {s : MachineState}
    (hAct : s.memory.activeCallee = none) (hStack : s.memory.callStack = []) :
    mirPostCallSite body s = body.defPath := by
  unfold mirPostCallSite mirTerminatorCallerSite
  rw [hAct, hStack]
  rfl

theorem mirNextSiteState_of_root {s : MachineState}
    (hAct : s.memory.activeCallee = none) (hStack : s.memory.callStack = [])
    (es' : MirExecState) :
    mirNextSiteState body (mirSiteOfExec body (.running s)) es' =
      mirSiteOfExec body es' := by
  cases es' with
  | running s' => rfl
  | halted out => rfl
  | faulted fk =>
    dsimp only [mirNextSiteState, mirSiteOfExec]
    rw [mirPostCallSite_of_root hAct hStack]

/--
Root-frame external-call `bind` law: when `s` is at the root frame
(`activeCallee = none`, `callStack = []`) and emits an external call `req` with
continuation `k`, `runMirStepsWithGap` is the monadic `bind` of the sealed
handler outcome `((env req).mapFault (fun _ => .ub)).mapGap (·.sealOutOfFuel req.defPath)`
with `runMirStepsWithGap` on `k ans`.
-/
theorem runMirStepsWithGap_of_root_extCall {s : MachineState}
    {req : MirCallReq} {k : MirCallAns → MirExecState}
    (hAct : s.memory.activeCallee = none) (hStack : s.memory.callStack = [])
    (hStep : stepMirFn body s = .vis (.inr (.inr (.call req))) k) (fuel : Nat) :
    runMirStepsWithGap env body (fuel + 1) (.running s) =
      (((env req).mapFault (fun _ => .ub)).mapGap (·.sealOutOfFuel req.defPath)).bind
        (fun ans => runMirStepsWithGap env body fuel (k ans)) := by
  have hSiteStep : stepMirSiteState body (mirSiteOfExec body (.running s)) =
      .vis (.inr (.inr (.call req)))
        (fun ans => mirNextSiteState body (mirSiteOfExec body (.running s)) (k ans)) := by
    unfold stepMirSiteState mirSiteOfExec
    dsimp only [MirSiteState.exec, stepMirState]
    rw [hStep]
    rfl
  have hVis := runStepsWithGap_of_vis (step := stepMirSiteState body)
    (site := mirSiteOfState body) (handle := mirGapHandle env) hSiteStep fuel
  change runStepsWithGap (stepMirSiteState body) (mirSiteOfState body)
      (mirGapHandle env) (fuel + 1) (mirSiteOfExec body (.running s)) = _
  rw [hVis]
  dsimp only [mirGapHandle]
  cases env req with
  | ok ans =>
    dsimp only [OutcomeWithGap.mapFault, OutcomeWithGap.mapGap, OutcomeWithGap.bind]
    rw [mirNextSiteState_of_root hAct hStack (k ans)]
    rfl
  | fault _ => rfl
  | gap _ => rfl

/-- Sealed specialization of `runMirStepsWithGap_of_root_extCall`. -/
theorem runMirStepsWithGap_of_root_extCall_sealed {s : MachineState}
    {req : MirCallReq} {k : MirCallAns → MirExecState}
    (hSealed : env.IsSealed)
    (hAct : s.memory.activeCallee = none) (hStack : s.memory.callStack = [])
    (hStep : stepMirFn body s = .vis (.inr (.inr (.call req))) k) (fuel : Nat) :
    runMirStepsWithGap env body (fuel + 1) (.running s) =
      ((env req).mapFault (fun _ => .ub)).bind (fun ans =>
        runMirStepsWithGap env body fuel (k ans)) := by
  rw [runMirStepsWithGap_of_root_extCall hAct hStack hStep fuel]
  change (mirGapHandle env (.inr (.call req))).bind _ = _
  rw [mirGapHandle_call_of_isSealed hSealed req]
  rfl

/--
A `MirStepNode.unsupported` step is always the gap tagged with the failure-owner
`DefPath` (`mirRunningFailSite body s`): never a value and never a fault.
-/
theorem runMirStepsWithGap_of_unsupported {s : MachineState}
    (h : stepMirFn body s = MirStepNode.unsupported) (fuel : Nat) :
    runMirStepsWithGap env body (fuel + 1) (.running s) =
      .gap (.unsupported (mirRunningFailSite body s)) := by
  have hs : stepMirSiteState body (mirSiteOfExec body (.running s)) =
      .vis (.inl (.fail .unsupported))
        (fun x => PEmpty.elim x) := by
    unfold stepMirSiteState mirSiteOfExec
    dsimp only [MirSiteState.exec, stepMirState]
    rw [h]
    dsimp only [MirStepNode.unsupported, MirStepNode.fail, ITreeF.map]
    congr
    funext x
    exact PEmpty.elim x
  exact runStepsWithGap_of_unsupported (step := stepMirSiteState body)
    (site := mirSiteOfState body) (s := mirSiteOfExec body (.running s)) hs fuel

/-- A `MirStepNode.fail .ub` step is the runtime fault `ExecFault.ub`. -/
theorem runMirStepsWithGap_of_ub {s : MachineState}
    (h : stepMirFn body s = MirStepNode.fail .ub) (fuel : Nat) :
    runMirStepsWithGap env body (fuel + 1) (.running s) = .fault .ub := by
  have hs : stepMirSiteState body (mirSiteOfExec body (.running s)) =
      .vis (.inl (.fail .ub)) (fun x => PEmpty.elim x) := by
    unfold stepMirSiteState mirSiteOfExec
    dsimp only [MirSiteState.exec, stepMirState]
    rw [h]
    dsimp only [MirStepNode.fail, ITreeF.map]
    congr
    funext x
    exact PEmpty.elim x
  exact runStepsWithGap_of_fail (step := stepMirSiteState body)
    (site := mirSiteOfState body) (s := mirSiteOfExec body (.running s)) hs fuel

/-- A halted execution state yields its classified `Outcome`. -/
theorem runMirStepsWithGap_halted (out : MirOutcome) (fuel : Nat) :
    runMirStepsWithGap env body (fuel + 1) (.halted out) = classifyOutcome out :=
  runStepsWithGap_of_ret (step := stepMirSiteState body)
    (site := mirSiteOfState body)
    (s := mirSiteOfExec body (.halted out)) rfl fuel

/-- A body whose phase is not a modeled runtime phase steps to `.unsupported`. -/
theorem stepMirFn_of_phase_other {s : MachineState} {name : String}
    (h : (s.memory.activeCallee.getD body).phase = .other name) :
    stepMirFn body s = MirStepNode.unsupported := by
  delta stepMirFn
  dsimp only
  rw [h]

theorem mirRunningFailSite_of_phase_other {s : MachineState} {name : String}
    (h : (s.memory.activeCallee.getD body).phase = .other name) :
    mirRunningFailSite body s = (s.memory.activeCallee.getD body).defPath := by
  unfold mirRunningFailSite
  dsimp only
  rw [h]

theorem mirRunningFailSite_of_callStack_nil {s : MachineState}
    (hStack : s.memory.callStack = []) :
    mirRunningFailSite body s = (s.memory.activeCallee.getD body).defPath := by
  unfold mirRunningFailSite mirTerminatorCallerSite
  dsimp only
  rw [hStack]
  cases (s.memory.activeCallee.getD body).phase <;> rfl

/--
Shared unmodeled callee: from *any* state executing a body with an unmodeled
phase, under *any* root body and callee environment, the run is the gap tagged
with that body's `DefPath`. No property of the caller is needed.
-/
theorem runMirStepsWithGap_of_phase_other {s : MachineState} {name : String}
    (h : (s.memory.activeCallee.getD body).phase = .other name) (fuel : Nat) :
    runMirStepsWithGap env body (fuel + 1) (.running s) =
      .gap (.unsupported (s.memory.activeCallee.getD body).defPath) := by
  rw [runMirStepsWithGap_of_unsupported (stepMirFn_of_phase_other h) fuel,
    mirRunningFailSite_of_phase_other h]

/--
While a callee frame is active the root body is irrelevant: two different root
bodies take the same step from the same state.
-/
theorem stepMirFn_eq_of_activeCallee {body₁ body₂ callee : CapturedMir}
    {s : MachineState} (h : s.memory.activeCallee = some callee) :
    stepMirFn body₁ s = stepMirFn body₂ s := by
  delta stepMirFn
  dsimp only
  rw [h]
  rfl

theorem mirRunningFailSite_eq_of_activeCallee {body₁ body₂ callee : CapturedMir}
    {s : MachineState} (h : s.memory.activeCallee = some callee) :
    mirRunningFailSite body₁ s = mirRunningFailSite body₂ s := by
  unfold mirRunningFailSite
  rw [h]
  rfl

theorem mirPostCallSite_eq_of_activeCallee {body₁ body₂ callee : CapturedMir}
    {s : MachineState} (h : s.memory.activeCallee = some callee) :
    mirPostCallSite body₁ s = mirPostCallSite body₂ s := by
  unfold mirPostCallSite
  rw [h]
  rfl

theorem stepMirSiteState_eq_of_activeCallee {body₁ body₂ callee : CapturedMir}
    {s : MachineState} (h : s.memory.activeCallee = some callee) :
    stepMirSiteState body₁ (.running s) = stepMirSiteState body₂ (.running s) := by
  unfold stepMirSiteState
  dsimp only [MirSiteState.exec]
  have hstep : stepMirState body₁ (.running s) = stepMirState body₂ (.running s) :=
    stepMirFn_eq_of_activeCallee h
  have hnext : mirNextSiteState body₁ (.running s) =
      mirNextSiteState body₂ (.running s) := by
    funext es'
    cases es' with
    | running _ => rfl
    | halted _ => rfl
    | faulted _ =>
      dsimp only [mirNextSiteState]
      rw [mirPostCallSite_eq_of_activeCallee h]
  rw [hstep, hnext]

/--
While an inline callee frame is active, two different root bodies take the
identical `mirSiteGapStep`: both the coalgebra transition and the failure-owner
`DefPath` depend only on the active callee and call stack, never on the root body.
-/
theorem mirSiteGapStep_eq_of_activeCallee {body₁ body₂ callee : CapturedMir}
    {s : MachineState} (h : s.memory.activeCallee = some callee) :
    mirSiteGapStep env body₁ (.running s) = mirSiteGapStep env body₂ (.running s) := by
  unfold mirSiteGapStep gapStep
  rw [stepMirSiteState_eq_of_activeCallee h,
    show mirSiteOfState body₁ (.running s) = mirSiteOfState body₂ (.running s) from
      mirRunningFailSite_eq_of_activeCallee h]

/--
Non-running `MirSiteState` transitions (`halted` or `faulted`) are completely
independent of the root `body` because `.faulted` already carries the owning
frame's `DefPath`.
-/
theorem mirSiteGapStep_eq_of_nonRunning {body₁ body₂ : CapturedMir}
    {st : MirSiteState} (h : ∀ s, st ≠ .running s) :
    mirSiteGapStep env body₁ st = mirSiteGapStep env body₂ st := by
  cases st with
  | running s => exact False.elim (h s rfl)
  | halted out => rfl
  | faulted fk site => rfl

/--
Multi-step congruence for a refactored MIR caller over `MirSiteState`: if
related states of `body₁` and `body₂` always present agreeing step nodes, the
two bounded runs are related up to identical gaps for every callee environment
and budget.
-/
theorem runMirSiteStepsWithGap_congr {body₁ body₂ : CapturedMir}
    {R : MirSiteState → MirSiteState → Prop} {rVal : MirReturn → MirReturn → Prop}
    (hsim : ∀ s₁ s₂, R s₁ s₂ →
      StepNodeRel R rVal (mirSiteOfState body₁ s₁) (mirSiteOfState body₂ s₂)
        (stepMirSiteState body₁ s₁) (stepMirSiteState body₂ s₂))
    (env : MirCallEnv) (fuel : Nat) {s₁ s₂ : MirSiteState} (h : R s₁ s₂) :
    GapEqErr rVal (· = ·) (runMirSiteStepsWithGap env body₁ fuel s₁)
      (runMirSiteStepsWithGap env body₂ fuel s₂) :=
  runStepsWithGap_congr hsim (mirGapHandle env) fuel h

/--
Stuttering multi-step congruence for MIR bodies under related callee
environments over `MirSiteState`.
-/
theorem mirGapBehaviors_equiv_of_stutter {env₁ env₂ : MirCallEnv}
    {body₁ body₂ : CapturedMir} {R : MirSiteState → MirSiteState → Prop}
    {rVal : MirReturn → MirReturn → Prop}
    {rFault : ExecFault → ExecFault → Prop} (hFault : ∀ e, rFault e e)
    (henv : ∀ req, GapEqErr (· = ·) (· = ·) (env₁ req) (env₂ req))
    (hsim : ∀ s₁ s₂, R s₁ s₂ → ∃ n₁ n₂ t₁ t₂,
      GapReach (mirSiteGapStep env₁ body₁) n₁ s₁ t₁ ∧
      GapReach (mirSiteGapStep env₂ body₂) n₂ s₂ t₂ ∧
      StepNodeRel R rVal (mirSiteOfState body₁ t₁) (mirSiteOfState body₂ t₂)
        (stepMirSiteState body₁ t₁) (stepMirSiteState body₂ t₂))
    {s₁ s₂ : MirSiteState} (h : R s₁ s₂) :
    OutcomeSetEquiv (GapEqErr rVal rFault)
      (gapBehaviors (mirSiteGapStep env₁ body₁) s₁)
      (gapBehaviors (mirSiteGapStep env₂ body₂) s₂) :=
  gapBehaviors_equiv_of_stutter_step hFault hsim
    (fun i => by
      cases i with
      | inl obs => cases obs; exact (rfl : PUnit.unit = PUnit.unit)
      | inr call =>
        cases call with
        | call req =>
          exact ((henv req).mapFault_congr (fun _ _ _ => hFault .ub)).mapGap_congr _)
    h

/-- Stuttering multi-step congruence for two MIR bodies sharing a callee environment. -/
theorem mirGapBehaviors_equiv_of_stutter_shared_env {env : MirCallEnv}
    {body₁ body₂ : CapturedMir} {R : MirSiteState → MirSiteState → Prop}
    {rVal : MirReturn → MirReturn → Prop}
    (hsim : ∀ s₁ s₂, R s₁ s₂ → ∃ n₁ n₂ t₁ t₂,
      GapReach (mirSiteGapStep env body₁) n₁ s₁ t₁ ∧
      GapReach (mirSiteGapStep env body₂) n₂ s₂ t₂ ∧
      StepNodeRel R rVal (mirSiteOfState body₁ t₁) (mirSiteOfState body₂ t₂)
        (stepMirSiteState body₁ t₁) (stepMirSiteState body₂ t₂))
    {s₁ s₂ : MirSiteState} (h : R s₁ s₂) :
    OutcomeSetEquiv (GapEqErr rVal (· = ·))
      (gapBehaviors (mirSiteGapStep env body₁) s₁)
      (gapBehaviors (mirSiteGapStep env body₂) s₂) :=
  mirGapBehaviors_equiv_of_stutter (fun _ => rfl)
    (fun req => GapEqErr.refl (fun _ => rfl) (fun _ => rfl) (env req)) hsim h

/--
Handler-relational stuttering congruence for MIR bodies: allows distinct
`MirCallReq`s (`req₁ ≠ req₂`, e.g., related caller memories with different
borrow-tag histories) and restricts continuation obligations to answers actually
produced by `env₁` and `env₂`.
-/
theorem mirGapBehaviors_equiv_of_stutter_with {env₁ env₂ : MirCallEnv}
    {body₁ body₂ : CapturedMir} {R : MirSiteState → MirSiteState → Prop}
    {rVal : MirReturn → MirReturn → Prop}
    {rFault : ExecFault → ExecFault → Prop} (hFault : ∀ e, rFault e e)
    (hsim : ∀ s₁ s₂, R s₁ s₂ → ∃ n₁ n₂ t₁ t₂,
      GapReach (mirSiteGapStep env₁ body₁) n₁ s₁ t₁ ∧
      GapReach (mirSiteGapStep env₂ body₂) n₂ s₂ t₂ ∧
      StepNodeRelWith (mirGapHandle env₁) (mirGapHandle env₂)
        R rVal rFault (mirSiteOfState body₁ t₁) (mirSiteOfState body₂ t₂)
        (stepMirSiteState body₁ t₁) (stepMirSiteState body₂ t₂))
    {s₁ s₂ : MirSiteState} (h : R s₁ s₂) :
    OutcomeSetEquiv (GapEqErr rVal rFault)
      (gapBehaviors (mirSiteGapStep env₁ body₁) s₁)
      (gapBehaviors (mirSiteGapStep env₂ body₂) s₂) :=
  gapBehaviors_equiv_of_stutter_step_with hFault hsim h

/--
An unchanged MIR body under two callee environments that agree up to identical
gaps: the runs agree up to identical gaps.
-/
theorem runMirStepsWithGap_env_congr {env₁ env₂ : MirCallEnv}
    {rFault : ExecFault → ExecFault → Prop} (hFault : ∀ e, rFault e e)
    (henv : ∀ req, GapEqErr (· = ·) (· = ·) (env₁ req) (env₂ req))
    (fuel : Nat) (s : MirExecState) :
    GapEqErr (· = ·) rFault (runMirStepsWithGap env₁ body fuel s)
      (runMirStepsWithGap env₂ body fuel s) :=
  runStepsWithGap_handle_congr (step := stepMirSiteState body)
    (site := mirSiteOfState body) (handle₁ := mirGapHandle env₁)
    (handle₂ := mirGapHandle env₂) hFault
    (fun i => by
      cases i with
      | inl obs => cases obs; exact (rfl : PUnit.unit = PUnit.unit)
      | inr call =>
        cases call with
        | call req =>
          exact ((henv req).mapFault_congr (fun _ _ _ => hFault .ub)).mapGap_congr _)
    fuel (mirSiteOfExec body s)

/--
Fuel-free callee-environment congruence: an unchanged MIR body executed under
two `GapEqErr`-equivalent callee environments satisfies `ContextEquiv` on all
argument lists, without any gap-freedom assumption on the callees.
-/
theorem mirGapBehaviors_env_congr {env₁ env₂ : MirCallEnv}
    {callees : List CapturedMir}
    (henv : ∀ req, GapEqErr (· = ·) (· = ·) (env₁ req) (env₂ req)) :
    ContextEquiv (· = ·) (· = ·)
      (mirGapBehaviors env₁ callees body)
      (mirGapBehaviors env₂ callees body) :=
  fun args =>
    mirGapBehaviors_equiv_of_stutter (R := (· = ·)) (fun _ => rfl) henv
      (fun s₁ s₂ hs => by
        cases hs
        exact ⟨0, 0, s₁, s₁, .refl s₁, .refl s₁,
          StepNodeRel.refl (stepMirSiteState body s₁) (mirSiteOfState body s₁)⟩)
      rfl

/-- Stateful fuel-indexed gap-aware MIR evaluator over `(args, mem)`. -/
def runMirStatefulWithGap (env : MirCallEnv) (callees : List CapturedMir)
    (body : CapturedMir) (fuel : Nat) (q : List Value × Memory) :
    OutcomeWithGap ExecFault (GapTag DefPath) MirReturn :=
  runMirStepsWithGap env body fuel
    (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
      body q.1 q.2 callees))

/-- Stateful fuel-free gap-aware MIR semantics over `(args, mem)`. -/
def mirStatefulGapBehaviors (env : MirCallEnv) (callees : List CapturedMir)
    (body : CapturedMir) :
    GapSem (List Value × Memory) ExecFault (GapTag DefPath) MirReturn :=
  fun q => gapBehaviors (mirSiteGapStep env body)
    (mirSiteOfExec body (.running
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
        body q.1 q.2 callees)))

/--
Frame-preserving modular `MirCallEnv` built from standalone `CapturedMir` callee
bodies via `runMirWithGap` at step budget `fuel`.
-/
def MirCallEnv.ofStandaloneBody (callees : List CapturedMir) (fuel : Nat)
    (lookup : DefPath → Option CapturedMir) : MirCallEnv :=
  MirCallEnv.ofStandaloneOutcome (fun req =>
    match lookup req.defPath with
    | some calleeBody => runMirWithGap MirCallEnv.unresolved callees calleeBody fuel req.args
    | none => .gap (.unresolved req.defPath))

theorem MirCallEnv.isSealed_ofStandaloneBody (callees : List CapturedMir) (fuel : Nat)
    (lookup : DefPath → Option CapturedMir) :
    (MirCallEnv.ofStandaloneBody callees fuel lookup).IsSealed :=
  MirCallEnv.isSealed_ofStandaloneOutcome _

theorem MirCallEnv.ofStandaloneBody_preservesCallFrame (callees : List CapturedMir)
    (fuel : Nat) (lookup : DefPath → Option CapturedMir) :
    (MirCallEnv.ofStandaloneBody callees fuel lookup).PreservesCallFrame :=
  MirCallEnv.ofStandaloneOutcome_preservesCallFrame _

/--
An external `MirCallReq` is reachable from `st` under `env` and `body` when
`st` reaches a `stepMirSiteState` node emitting `.call req`.
-/
def MirCallReachable (env : MirCallEnv) (body : CapturedMir)
    (st : MirSiteState) (req : MirCallReq) : Prop :=
  StepRequestReachable (stepMirSiteState body) (mirSiteOfState body)
    (mirGapHandle env) st (.inr (.call req))

private theorem mirGapHandle_call_eq_seal (env : MirCallEnv) (req : MirCallReq) :
    mirGapHandle env (.inr (.call req)) = (env.seal req).mapFault (fun _ => .ub) := by
  dsimp only [mirGapHandle, MirCallEnv.seal]
  cases env req <;> rfl

/--
Reachable-request bounded callee-environment congruence: `env₁` and `env₂` need
only agree (after handler sealing) on external calls actually reachable from `s`.
-/
theorem runMirStepsWithGap_env_congr_on {env₁ env₂ : MirCallEnv}
    {rFault : ExecFault → ExecFault → Prop} (hFault : ∀ e, rFault e e)
    {s : MirExecState}
    (henv : ∀ req, MirCallReachable env₁ body (mirSiteOfExec body s) req →
      GapEqErr (· = ·) (· = ·) (env₁.seal req) (env₂.seal req))
    (fuel : Nat) :
    GapEqErr (· = ·) rFault (runMirStepsWithGap env₁ body fuel s)
      (runMirStepsWithGap env₂ body fuel s) := by
  refine runStepsWithGap_handle_congr_on (step := stepMirSiteState body)
    (site := mirSiteOfState body) (handle₁ := mirGapHandle env₁)
    (handle₂ := mirGapHandle env₂) hFault ?_ fuel
  intro i hreach
  cases i with
  | inl obs => cases obs; exact (rfl : PUnit.unit = PUnit.unit)
  | inr call =>
    cases call with
    | call req =>
      rw [mirGapHandle_call_eq_seal env₁ req, mirGapHandle_call_eq_seal env₂ req]
      exact (henv req hreach).mapFault_congr (fun _ _ _ => hFault .ub)

/--
Reachable-request fuel-free callee-environment congruence: extending or
refactoring `env₁` into `env₂` on callees never invoked by `(body, args)`
preserves `mirGapBehaviors` up to `OutcomeSetEquiv`!
-/
theorem mirGapBehaviors_env_congr_on {env₁ env₂ : MirCallEnv}
    {callees : List CapturedMir} {args : List Value}
    (henv : ∀ req,
      MirCallReachable env₁ body
        (mirSiteOfExec body (.running (initMachineStateWithCallees body args callees))) req →
      GapEqErr (· = ·) (· = ·) (env₁.seal req) (env₂.seal req)) :
    OutcomeSetEquiv (GapEqErr (· = ·) (· = ·))
      (mirGapBehaviors env₁ callees body args)
      (mirGapBehaviors env₂ callees body args) := by
  refine gapBehaviors_handle_congr_on (step := stepMirSiteState body)
    (site := mirSiteOfState body) (handle₁ := mirGapHandle env₁)
    (handle₂ := mirGapHandle env₂) (fun _ => rfl) ?_
  intro i hreach
  cases i with
  | inl obs => cases obs; exact (rfl : PUnit.unit = PUnit.unit)
  | inr call =>
    cases call with
    | call req =>
      rw [mirGapHandle_call_eq_seal env₁ req, mirGapHandle_call_eq_seal env₂ req]
      exact (henv req hreach).mapFault_congr (fun _ _ _ => rfl)

/--
Stateful reachable-request fuel-free callee-environment congruence over `(args, mem)`.
-/
theorem mirStatefulGapBehaviors_env_congr_on {env₁ env₂ : MirCallEnv}
    {callees : List CapturedMir} {q : List Value × Memory}
    (henv : ∀ req,
      MirCallReachable env₁ body
        (mirSiteOfExec body (.running
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            body q.1 q.2 callees))) req →
      GapEqErr (· = ·) (· = ·) (env₁.seal req) (env₂.seal req)) :
    OutcomeSetEquiv (GapEqErr (· = ·) (· = ·))
      (mirStatefulGapBehaviors env₁ callees body q)
      (mirStatefulGapBehaviors env₂ callees body q) := by
  refine gapBehaviors_handle_congr_on (step := stepMirSiteState body)
    (site := mirSiteOfState body) (handle₁ := mirGapHandle env₁)
    (handle₂ := mirGapHandle env₂) (fun _ => rfl) ?_
  intro i hreach
  cases i with
  | inl obs => cases obs; exact (rfl : PUnit.unit = PUnit.unit)
  | inr call =>
    cases call with
    | call req =>
      rw [mirGapHandle_call_eq_seal env₁ req, mirGapHandle_call_eq_seal env₂ req]
      exact (henv req hreach).mapFault_congr (fun _ _ _ => rfl)

/--
Computable fail-closed checker verifying that execution from `st` finishes
within `fuel` steps and every external call emitted along the path has its
`defPath` accepted by `pred`. Returns `false` if fuel runs out.
-/
def mirRequestsAllIn (env : MirCallEnv) (body : CapturedMir)
    (pred : DefPath → Bool) : Nat → MirSiteState → Bool
  | 0, _ => false
  | fuel + 1, st =>
    let hereOk : Bool :=
      match stepMirSiteState body st with
      | .vis (.inr (.inr (.call req))) _ => pred req.defPath
      | _ => true
    hereOk &&
      match mirSiteGapStep env body st with
      | .next st' => mirRequestsAllIn env body pred fuel st'
      | .done _ => true

/--
Soundness of `mirRequestsAllIn`: whenever the bounded checker returns `true`,
every `MirCallReachable` request along the execution satisfies `pred req.defPath = true`.
-/
theorem mirCallReachable_of_requestsAllIn {env : MirCallEnv} {body : CapturedMir}
    {pred : DefPath → Bool} {fuel : Nat} {st : MirSiteState}
    (hCheck : mirRequestsAllIn env body pred fuel st = true)
    {req : MirCallReq} (hreach : MirCallReachable env body st req) :
    pred req.defPath = true := by
  obtain ⟨n, t, k, hr, ht⟩ := hreach
  induction fuel generalizing st n with
  | zero => cases hCheck
  | succ fuel ih =>
    unfold mirRequestsAllIn at hCheck
    have hsplit := bool_and_split hCheck
    cases hr with
    | refl =>
      have hHere := hsplit.1
      rw [ht] at hHere
      exact hHere
    | @step _ _ s' _ hn hr' =>
      have hNext := hsplit.2
      change mirSiteGapStep env body st = .next s' at hn
      rw [hn] at hNext
      exact ih (st := s') (n := _) hNext hr'

/--
One-step reflective callee-environment congruence: if `mirRequestsAllIn` certifies
that every external call emitted by `(body, args)` satisfies `pred`, then `env₁`
and `env₂` need only agree on `pred`-matching callees!
-/
theorem mirGapBehaviors_env_congr_of_requestsAllIn {env₁ env₂ : MirCallEnv}
    {callees : List CapturedMir} {args : List Value}
    {pred : DefPath → Bool} {fuel : Nat}
    (hCheck : mirRequestsAllIn env₁ body pred fuel
      (mirSiteOfExec body (.running (initMachineStateWithCallees body args callees))) = true)
    (henv : ∀ req, pred req.defPath = true →
      GapEqErr (· = ·) (· = ·) (env₁.seal req) (env₂.seal req)) :
    OutcomeSetEquiv (GapEqErr (· = ·) (· = ·))
      (mirGapBehaviors env₁ callees body args)
      (mirGapBehaviors env₂ callees body args) :=
  mirGapBehaviors_env_congr_on (fun req hreach =>
    henv req (mirCallReachable_of_requestsAllIn hCheck hreach))

/--
Stateful one-step reflective callee-environment congruence via `mirRequestsAllIn`.
-/
theorem mirStatefulGapBehaviors_env_congr_of_requestsAllIn {env₁ env₂ : MirCallEnv}
    {callees : List CapturedMir} {q : List Value × Memory}
    {pred : DefPath → Bool} {fuel : Nat}
    (hCheck : mirRequestsAllIn env₁ body pred fuel
      (mirSiteOfExec body (.running
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          body q.1 q.2 callees))) = true)
    (henv : ∀ req, pred req.defPath = true →
      GapEqErr (· = ·) (· = ·) (env₁.seal req) (env₂.seal req)) :
    OutcomeSetEquiv (GapEqErr (· = ·) (· = ·))
      (mirStatefulGapBehaviors env₁ callees body q)
      (mirStatefulGapBehaviors env₂ callees body q) :=
  mirStatefulGapBehaviors_env_congr_on (fun req hreach =>
    henv req (mirCallReachable_of_requestsAllIn hCheck hreach))

/-- Fuel monotonicity of bounded MIR runs. -/
theorem runMirWithGap_fuel_mono {callees : List CapturedMir} {fuel fuel' : Nat}
    {args : List Value} (hle : fuel ≤ fuel')
    (hne : runMirWithGap env callees body fuel args ≠ .gap .outOfFuel) :
    runMirWithGap env callees body fuel' args =
      runMirWithGap env callees body fuel args :=
  runGapSteps_fuel_mono_le _ hle hne

/-- With a sufficient budget, the fuel-free semantics is the bounded run. -/
theorem mirGapBehaviors_iff_of_run {callees : List CapturedMir} {fuel : Nat}
    {args : List Value}
    (h : runMirWithGap env callees body fuel args ≠ .gap .outOfFuel)
    (o : OutcomeWithGap ExecFault (GapTag DefPath) MirReturn) :
    mirGapBehaviors env callees body args o ↔
      o = runMirWithGap env callees body fuel args :=
  gapBehaviors_iff_of_run _ h o

/--
Two bounded MIR runs (with possibly different budgets) that finish with related
outcomes determine equivalent fuel-free behavior sets.
-/
theorem mirGapBehaviors_equiv_of_runs {env₁ env₂ : MirCallEnv}
    {callees₁ callees₂ : List CapturedMir} {body₁ body₂ : CapturedMir}
    {rVal : MirReturn → MirReturn → Prop} {rFault : ExecFault → ExecFault → Prop}
    {fuel₁ fuel₂ : Nat} {args₁ args₂ : List Value}
    (hne : runMirWithGap env₁ callees₁ body₁ fuel₁ args₁ ≠ .gap .outOfFuel)
    (h : GapEqErr rVal rFault (runMirWithGap env₁ callees₁ body₁ fuel₁ args₁)
      (runMirWithGap env₂ callees₂ body₂ fuel₂ args₂)) :
    OutcomeSetEquiv (GapEqErr rVal rFault)
      (mirGapBehaviors env₁ callees₁ body₁ args₁)
      (mirGapBehaviors env₂ callees₂ body₂ args₂) :=
  gapBehaviors_equiv_of_runs hne h

/--
For two finished bounded MIR runs, equivalence of the fuel-free behavior sets
is exactly `GapEqErr` of the two outcomes.
-/
theorem mirGapBehaviors_equiv_iff_of_runs {env₁ env₂ : MirCallEnv}
    {callees₁ callees₂ : List CapturedMir} {body₁ body₂ : CapturedMir}
    {rVal : MirReturn → MirReturn → Prop} {rFault : ExecFault → ExecFault → Prop}
    {fuel₁ fuel₂ : Nat} {args₁ args₂ : List Value}
    (hne₁ : runMirWithGap env₁ callees₁ body₁ fuel₁ args₁ ≠ .gap .outOfFuel)
    (hne₂ : runMirWithGap env₂ callees₂ body₂ fuel₂ args₂ ≠ .gap .outOfFuel) :
    OutcomeSetEquiv (GapEqErr rVal rFault)
        (mirGapBehaviors env₁ callees₁ body₁ args₁)
        (mirGapBehaviors env₂ callees₂ body₂ args₂) ↔
      GapEqErr rVal rFault (runMirWithGap env₁ callees₁ body₁ fuel₁ args₁)
        (runMirWithGap env₂ callees₂ body₂ fuel₂ args₂) :=
  gapBehaviors_equiv_iff_of_runs hne₁ hne₂

/-- A finished gap-free bounded MIR run makes the fuel-free semantics gap-free. -/
theorem neverGap_mirGapBehaviors_of_run {callees : List CapturedMir} {fuel : Nat}
    {args : List Value}
    (h : (runMirWithGap env callees body fuel args).isGapFree) :
    NeverGap (mirGapBehaviors env callees body args) :=
  neverGap_gapBehaviors_of_run h

/-- A finished defined bounded MIR run makes the fuel-free semantics defined. -/
theorem defined_mirGapBehaviors_of_run {callees : List CapturedMir} {fuel : Nat}
    {args : List Value}
    (h : (runMirWithGap env callees body fuel args).isDefined ExecFault.isUB) :
    OutcomeSet.Defined ExecFault.isUB (mirGapBehaviors env callees body args) :=
  defined_gapBehaviors_of_run h

/-- Exact fault matching preserves UB-ness. -/
theorem ExecFault.eq_preserves_isUB :
    ∀ e₁ e₂ : ExecFault, e₁ = e₂ → (e₁.isUB ↔ e₂.isUB) :=
  fun _ _ h => h ▸ Iff.rfl

/--
A fault relation that identifies UB with a defined panic does not preserve
UB-ness, so it never satisfies the side condition of the Layer 1A bridges.
-/
theorem ExecFault.not_preserves_isUB_of_ub_panic
    {rFault : ExecFault → ExecFault → Prop} (h : rFault .ub .panic) :
    ¬ ∀ e₁ e₂ : ExecFault, rFault e₁ e₂ → (e₁.isUB ↔ e₂.isUB) :=
  fun hUB => (hUB .ub .panic h).mp trivial

/--
Exact `ContextEquiv` of two MIR bodies induces an identity-observation
`ExactPass` on their Layer 1A projections (gaps and UB undefined, panics and
aborts defined), with no gap-freedom obligation on shared callees.
-/
theorem mirContextEquiv_exactPass {callees : List CapturedMir}
    {body₁ body₂ : CapturedMir}
    (h : ContextEquiv (· = ·) (· = ·) (mirGapBehaviors env callees body₁)
      (mirGapBehaviors env callees body₂)) :
    ExactPass (gapSemantics ExecFault.isUB (mirGapBehaviors env callees))
      (gapSemantics ExecFault.isUB (mirGapBehaviors env callees)) id id
      body₁ body₂ :=
  h.toExactPass_eq

/-- Exact `ContextEquiv` of two MIR bodies induces Layer 1A `Compiles`. -/
theorem mirContextEquiv_compiles {callees : List CapturedMir}
    {body₁ body₂ : CapturedMir}
    (h : ContextEquiv (· = ·) (· = ·) (mirGapBehaviors env callees body₁)
      (mirGapBehaviors env callees body₂)) :
    Compiles (mirGapLanguage env callees) (mirGapLanguage env callees) id
      body₁ body₂ :=
  fun q => OutcomeSet.toPartial_le_of_subset (h q).superset_of_eq

/--
Query-scoped upgrade for MIR bodies: when the baseline is gap-free and UB-free
on `pre`, exact `ContextEquivOn pre` is gap-free `ProgramEquivOn pre`, and the
refactored body is gap-free and UB-free on `pre` as well.
-/
theorem mirContextEquivOn_toProgramEquivOn {Query : Type}
    {pre : Query → Prop}
    {sem₁ sem₂ : GapSem Query ExecFault (GapTag DefPath) MirReturn}
    (h : ContextEquivOn pre (· = ·) (· = ·) sem₁ sem₂)
    (h₁ : ∀ q, pre q → OutcomeSet.Defined ExecFault.isUB (sem₁ q)) :
    ProgramEquivOn pre (· = ·) (· = ·) sem₁ sem₂ ∧
      ∀ q, pre q → OutcomeSet.Defined ExecFault.isUB (sem₂ q) :=
  h.toProgramEquivOn_of_defined ExecFault.eq_preserves_isUB h₁

end MirGap


/-! ## 8. Adequacy of Gap-Aware Stepping for the Interaction-Tree Semantics

The gap-aware evaluator steps the same coalgebra that `ITree.cofix` unfolds.
Every continuing step of the evaluator is a `.tau` or an answered non-fault
request of the tree, so a value reported by the evaluator is a value the tree
returns (`ReachesRet`), and a step-level failure reached by the evaluator is a
reachable fault of the tree (so the tree is not `TreeSafe`).
-/

section GapMachineWitness

variable {State : Type u} {Fault : Type u₁} {Site : Type u₂} {Val : Type u₃}
  (next : State → GapStep State Fault (GapTag Site) Val)

/--
A bounded run that is not out of fuel halts at a state reached by continuing
steps: the outcome is produced by one halting step.
-/
theorem runGapSteps_witness {fuel : Nat} {s : State}
    (hne : runGapSteps next fuel s ≠ .gap .outOfFuel) :
    ∃ n s', GapReach next n s s' ∧ next s' = .done (runGapSteps next fuel s) := by
  induction fuel generalizing s with
  | zero => exact absurd rfl hne
  | succ fuel ih =>
    cases hn : next s with
    | next t =>
      rw [runGapSteps_succ_of_next next hn] at hne ⊢
      obtain ⟨n, s', hr, hd⟩ := ih hne
      exact ⟨n + 1, s', .step hn hr, hd⟩
    | done out =>
      rw [runGapSteps_succ_of_done next hn]
      exact ⟨0, s, .refl s, hn⟩

/--
Constructive fuel dichotomy for any machine that never halts directly with the
evaluator's own `.gap .outOfFuel` sentinel: for every `fuel` and `s`, either
the machine takes `fuel` continuing steps and returns `.gap .outOfFuel`, or the
run finishes with an outcome distinct from `.gap .outOfFuel`.
-/
theorem runGapSteps_dichotomy
    (hNoDoneOOF : ∀ s, next s ≠ .done (.gap .outOfFuel))
    (fuel : Nat) (s : State) :
    (runGapSteps next fuel s = .gap .outOfFuel ∧ ∃ s', GapReach next fuel s s') ∨
      runGapSteps next fuel s ≠ .gap .outOfFuel := by
  induction fuel generalizing s with
  | zero => exact Or.inl ⟨rfl, s, .refl s⟩
  | succ fuel ih =>
    cases hn : next s with
    | next t =>
      rw [runGapSteps_succ_of_next next hn]
      rcases ih t with ⟨hoof, s', hr⟩ | hne
      · exact Or.inl ⟨hoof, s', .step hn hr⟩
      · exact Or.inr hne
    | done out =>
      rw [runGapSteps_succ_of_done next hn]
      exact Or.inr (fun h₀ => hNoDoneOOF s (h₀ ▸ hn))

/--
For a machine that never halts with `.done (.gap .outOfFuel)`, the fuel-free
behavior set is empty if and only if every bounded run exhausts its fuel.
-/
theorem gapBehaviors_empty_iff
    (hNoDoneOOF : ∀ s, next s ≠ .done (.gap .outOfFuel)) (s : State) :
    (∀ o, ¬ gapBehaviors next s o) ↔
      ∀ fuel, runGapSteps next fuel s = .gap .outOfFuel := by
  constructor
  · intro hemp fuel
    rcases runGapSteps_dichotomy next hNoDoneOOF fuel s with ⟨hoof, _⟩ | hne
    · exact hoof
    · exact False.elim (hemp _ (gapBehaviors_of_run next hne))
  · intro hall o ho
    obtain ⟨hne, fuel, hrun⟩ := ho
    exact hne (hrun.symm.trans (hall fuel))

end GapMachineWitness

/--
Constructive coalgebra homomorphism theorem: whenever `π : S₁ → S₂` commutes
with `step₁` and `step₂`, `ITree.cofix step₁ s = ITree.cofix step₂ (π s)`.
-/
theorem cofix_hom_eq {E : Effect.{u}} {R S₁ S₂ : Type u}
    (step₁ : S₁ → ITreeF E R S₁) (step₂ : S₂ → ITreeF E R S₂)
    (π : S₁ → S₂) (hπ : ∀ s, (step₁ s).map π = step₂ (π s)) (s : S₁) :
    ITree.cofix step₁ s = ITree.cofix step₂ (π s) := by
  refine ITree.bisim_eq
    (fun t₁ t₂ => ∃ x, t₁ = ITree.cofix step₁ x ∧ t₂ = ITree.cofix step₂ (π x))
    ?_ ⟨s, rfl, rfl⟩
  rintro _ _ ⟨x, rfl, rfl⟩
  rw [ITree.observe_cofix, ITree.observe_cofix, ← hπ x]
  cases step₁ x with
  | ret _ => rfl
  | tau x' => exact ⟨x', rfl, rfl⟩
  | vis i k => exact ⟨rfl, fun o => ⟨k o, rfl, rfl⟩⟩

section Adequacy

variable {State Val Site : Type} {E : Effect.{0}}
  {step : State → ITreeF (SumE (FailE FailureKind) E) (Outcome Val) State}
  {site : State → Site}
  {handle : (i : E.I) → OutcomeWithGap ExecFault (GapTag Site) (E.O i)}

/-- Under a sealed handler, `gapStep` never halts with `.done (.gap .outOfFuel)`. -/
theorem gapStep_ne_done_outOfFuel (hSealed : ∀ i : E.I, handle i ≠ .gap .outOfFuel)
    (s : State) : gapStep step site handle s ≠ .done (.gap .outOfFuel) := by
  cases hs : step s with
  | ret out =>
    rw [gapStep_of_ret hs]
    exact fun h => classifyOutcome_ne_outOfFuel out (GapStep.done.inj h)
  | tau t => rw [gapStep_of_tau hs]; exact fun h => by cases h
  | vis i k =>
    cases i with
    | inl f =>
      cases f with
      | fail kind =>
        rw [gapStep_of_fail hs]
        exact fun h => classifyFailure_ne_outOfFuel (site s) kind (GapStep.done.inj h)
    | inr j =>
      rw [gapStep_of_vis hs]
      cases ho : handle j with
      | ok _ => exact fun h => by cases h
      | fault _ => exact fun h => by cases h
      | gap g =>
        intro h
        cases GapStep.done.inj h
        exact hSealed j ho

/-- A continuing step is a `.tau` or a request answered `.ok` by the handler. -/
theorem gapStep_next_cases {s s' : State}
    (h : gapStep step site handle s = .next s') :
    step s = .tau s' ∨
      ∃ (i : E.I) (k : E.O i → State) (o : E.O i),
        step s = .vis (.inr i) k ∧ handle i = .ok o ∧ s' = k o := by
  cases hs : step s with
  | ret out => rw [gapStep_of_ret hs] at h; cases h
  | tau t => rw [gapStep_of_tau hs] at h; cases h; exact Or.inl rfl
  | vis i k =>
    cases i with
    | inl f =>
      cases f with
      | fail kind => rw [gapStep_of_fail hs] at h; cases h
    | inr j =>
      rw [gapStep_of_vis hs] at h
      cases ho : handle j with
      | ok o => rw [ho] at h; cases h; exact Or.inr ⟨j, k, o, rfl, ho, rfl⟩
      | fault e => rw [ho] at h; cases h
      | gap g => rw [ho] at h; cases h

/--
A halting step that reports a value is a `.ret (.normal v)` node: neither a
failure of the machine nor a fault or gap of the handler is ever a value.
-/
theorem gapStep_done_ok {s : State} {v : Val}
    (h : gapStep step site handle s = .done (.ok v)) :
    step s = .ret (.normal v) := by
  cases hs : step s with
  | ret out =>
    rw [gapStep_of_ret hs] at h
    cases out with
    | normal w => cases h; rfl
    | panic => cases h
    | abort => cases h
  | tau t => rw [gapStep_of_tau hs] at h; cases h
  | vis i k =>
    cases i with
    | inl f =>
      cases f with
      | fail kind =>
        rw [gapStep_of_fail hs] at h
        cases kind <;> cases h
    | inr j =>
      rw [gapStep_of_vis hs] at h
      cases ho : handle j with
      | ok o => rw [ho] at h; cases h
      | fault e => rw [ho] at h; cases h
      | gap g => rw [ho] at h; cases h

/--
A halting step that reports a defined outcome (`.ok v`, `.fault .panic`, or
`.fault .abort`) must come from a `.ret out` node whenever the handler only
produces UB faults (never defined faults).
-/
theorem gapStep_done_defined
    (hNoDefFault : ∀ (i : E.I) (e : ExecFault), handle i = .fault e → e.isUB)
    {s : State} {o : OutcomeWithGap ExecFault (GapTag Site) Val}
    (h : gapStep step site handle s = .done o)
    (hdef : o.isDefined ExecFault.isUB) :
    ∃ out : Outcome Val, step s = .ret out ∧ o = classifyOutcome out := by
  cases hs : step s with
  | ret out =>
    rw [gapStep_of_ret hs] at h
    cases h
    exact ⟨out, rfl, rfl⟩
  | tau t => rw [gapStep_of_tau hs] at h; cases h
  | vis i k =>
    cases i with
    | inl f =>
      cases f with
      | fail kind =>
        rw [gapStep_of_fail hs] at h
        cases h
        cases kind with
        | ub => exact False.elim (hdef trivial)
        | unsupported => exact False.elim hdef
        | outOfFuel => exact False.elim hdef
    | inr j =>
      rw [gapStep_of_vis hs] at h
      cases ho : handle j with
      | ok a => rw [ho] at h; cases h
      | fault e =>
        rw [ho] at h
        cases h
        exact False.elim (hdef (hNoDefFault j e ho))
      | gap g =>
        rw [ho] at h
        cases h
        exact False.elim hdef

variable [FaultEffect E]

/--
Continuing steps of the evaluator are reachability in the unfolded interaction
tree, provided the handled effect row `E` has no fault requests.
-/
theorem reaches_of_gapReach (hE : ∀ i : E.I, ¬ FaultEffect.isFault i)
    {n : Nat} {s s' : State}
    (h : GapReach (gapStep step site handle) n s s') :
    ∃ tr, Reaches (ITree.cofix step s) tr (ITree.cofix step s') := by
  induction h with
  | refl s => exact ⟨[], .refl _⟩
  | @step n s t s'' hn _ ih =>
    obtain ⟨tr, hr⟩ := ih
    rcases gapStep_next_cases hn with hs | ⟨i, k, o, hs, _, rfl⟩
    · exact ⟨tr, .tau (by rw [ITree.observe_cofix, hs]; rfl) hr⟩
    · exact ⟨_, .vis (i := Sum.inr i) (by rw [ITree.observe_cofix, hs]; rfl) (hE i) o hr⟩

/--
Soundness of reported values: if the gap-aware evaluator returns `.ok v`, the
unfolded interaction tree returns `.normal v` along some trace.
-/
theorem runStepsWithGap_ok_reachesRet (hE : ∀ i : E.I, ¬ FaultEffect.isFault i)
    {fuel : Nat} {s : State} {v : Val}
    (h : runStepsWithGap step site handle fuel s = .ok v) :
    ∃ tr, ReachesRet (ITree.cofix step s) tr (.normal v) := by
  have hrun : runGapSteps (gapStep step site handle) fuel s = .ok v := h
  have hne : runGapSteps (gapStep step site handle) fuel s ≠ .gap .outOfFuel :=
    fun h₀ => by rw [hrun] at h₀; cases h₀
  obtain ⟨n, s', hr, hd⟩ := runGapSteps_witness _ hne
  rw [hrun] at hd
  obtain ⟨tr, hreach⟩ := reaches_of_gapReach hE hr
  exact ⟨tr, _, hreach, by rw [ITree.observe_cofix, gapStep_done_ok hd]; rfl⟩

/--
Soundness of all defined outcomes (`.normal`, `.panic`, and `.abort`): whenever
the handler never emits defined faults, every defined outcome returned by
`runStepsWithGap` is reached by `ITree.cofix step s`.
-/
theorem runStepsWithGap_defined_reachesRet
    (hE : ∀ i : E.I, ¬ FaultEffect.isFault i)
    (hNoDefFault : ∀ (i : E.I) (e : ExecFault), handle i = .fault e → e.isUB)
    {fuel : Nat} {s : State} {out : Outcome Val}
    (h : runStepsWithGap step site handle fuel s = classifyOutcome out) :
    ∃ tr, ReachesRet (ITree.cofix step s) tr out := by
  have hrun : runGapSteps (gapStep step site handle) fuel s = classifyOutcome out := h
  have hne : runGapSteps (gapStep step site handle) fuel s ≠ .gap .outOfFuel :=
    hrun ▸ classifyOutcome_ne_outOfFuel out
  obtain ⟨n, s', hr, hd⟩ := runGapSteps_witness _ hne
  rw [hrun] at hd
  obtain ⟨out', hret, heq⟩ := gapStep_done_defined hNoDefFault hd (classifyOutcome_isDefined out)
  cases classifyOutcome_injective heq
  obtain ⟨tr, hreach⟩ := reaches_of_gapReach hE hr
  exact ⟨tr, _, hreach, by rw [ITree.observe_cofix, hret]; rfl⟩

/--
A step-level failure reached by the evaluator is a reachable fault of the
unfolded interaction tree: the tree is not `TreeSafe`. In particular a reached
`FailureKind.unsupported` (a gap of the evaluator) and a reached
`FailureKind.ub` are both "undefined" in the Layer 1A projection of the tree.
-/
theorem not_treeSafe_of_gapReach_fail (hE : ∀ i : E.I, ¬ FaultEffect.isFault i)
    {n : Nat} {s s' : State} {kind : FailureKind} {k : PEmpty → State}
    (h : GapReach (gapStep step site handle) n s s')
    (hs : step s' = .vis (.inl (.fail kind)) k) :
    ¬ TreeSafe (ITree.cofix step s) := by
  intro hsafe
  obtain ⟨tr, hreach⟩ := reaches_of_gapReach hE h
  exact hsafe tr _ hreach
    ⟨_, Sum.inl (FailReq.fail kind), _, .refl _,
      by rw [ITree.observe_cofix, hs]; rfl, trivial⟩

/--
An undefined outcome of the evaluator (UB or a gap other than `.outOfFuel`)
that is not a fault or gap of the handler comes from a failure node of the
stepped machine, so the unfolded interaction tree is not `TreeSafe`. The
evaluator and the Layer 1A projection of the tree therefore agree that such a
run is undefined.
-/
theorem not_treeSafe_of_runStepsWithGap (hE : ∀ i : E.I, ¬ FaultEffect.isFault i)
    {fuel : Nat} {s : State} {o : OutcomeWithGap ExecFault (GapTag Site) Val}
    (h : runStepsWithGap step site handle fuel s = o)
    (hne : o ≠ .gap .outOfFuel) (hundef : ¬ o.isDefined ExecFault.isUB)
    (hfault : ∀ i e, handle i = .fault e → o ≠ .fault e)
    (hgap : ∀ i g, handle i = .gap g → o ≠ .gap g) :
    ¬ TreeSafe (ITree.cofix step s) := by
  have hrun : runGapSteps (gapStep step site handle) fuel s = o := h
  obtain ⟨n, s', hr, hd⟩ := runGapSteps_witness _ (hrun ▸ hne)
  rw [hrun] at hd
  cases hs : step s' with
  | ret out =>
    rw [gapStep_of_ret hs] at hd
    cases hd
    exact absurd (classifyOutcome_isDefined out) hundef
  | tau t => rw [gapStep_of_tau hs] at hd; cases hd
  | vis i k =>
    cases i with
    | inl f =>
      cases f with
      | fail kind => exact not_treeSafe_of_gapReach_fail hE hr hs
    | inr j =>
      rw [gapStep_of_vis hs] at hd
      cases ho : handle j with
      | ok a => rw [ho] at hd; cases hd
      | fault e => rw [ho] at hd; cases hd; exact absurd rfl (hfault j e ho)
      | gap g => rw [ho] at hd; cases hd; exact absurd rfl (hgap j g ho)

private theorem tauStar_to_reaches {F : Effect} [FaultEffect F] {R : Type}
    {a b : ITree F R} (hts : TauStar a b) : Reaches a [] b := by
  induction hts with
  | refl => exact .refl _
  | step htau _ ih => exact .tau htau ih

private theorem reaches_append_tauStar {F : Effect} [FaultEffect F] {R : Type}
    {t u u' : ITree F R} {tr : List (Event F)}
    (hr : Reaches t tr u) (hts : TauStar u u') : Reaches t tr u' := by
  induction hr with
  | refl => exact tauStar_to_reaches hts
  | tau htau _ ih => exact .tau htau (ih hts)
  | vis hv hnf o _ ih => exact .vis hv hnf o (ih hts)

private theorem reaches_cofix_of_defined
    (hSealed : ∀ i : E.I, handle i ≠ .gap .outOfFuel)
    (hSub : ∀ (i : E.I) (o : E.O i), handle i = .ok o → ∀ o' : E.O i, o' = o)
    (hNoDefFault : ∀ (i : E.I) (e : ExecFault), handle i = .fault e → e.isUB)
    {s : State} {tr : List (Event (SumE (FailE FailureKind) E))}
    {u : ITree (SumE (FailE FailureKind) E) (Outcome Val)}
    (hreach : Reaches (ITree.cofix step s) tr u)
    (hDef : OutcomeSet.Defined ExecFault.isUB
      (gapBehaviors (gapStep step site handle) s)) :
    ∃ s', u = ITree.cofix step s' ∧
      OutcomeSet.Defined ExecFault.isUB
        (gapBehaviors (gapStep step site handle) s') ∧
      ∀ o, gapBehaviors (gapStep step site handle) s' o →
        gapBehaviors (gapStep step site handle) s o := by
  generalize ht₀ : ITree.cofix step s = t₀ at hreach
  induction hreach generalizing s with
  | refl =>
    subst ht₀
    exact ⟨s, rfl, hDef, fun _ ho => ho⟩
  | @tau x x' _ _ htau _ ih =>
    subst ht₀
    rw [ITree.observe_cofix] at htau
    cases hs : step s with
    | ret _ => rw [hs] at htau; cases htau
    | vis _ _ => rw [hs] at htau; cases htau
    | tau s' =>
      rw [hs] at htau
      injection htau with hx'
      have hback : ∀ o, gapBehaviors (gapStep step site handle) s' o →
          gapBehaviors (gapStep step site handle) s o :=
        fun o ho => (gapBehaviors_reach_iff _ (.step (gapStep_of_tau hs) (.refl s')) o).mpr ho
      obtain ⟨s'', hu, hDef'', hb''⟩ := ih (fun _ ho => hDef (hback _ ho)) hx'
      exact ⟨s'', hu, hDef'', fun o ho => hback o (hb'' o ho)⟩
  | @vis x _ idx c _ hv hnf o' _ ih =>
    subst ht₀
    rw [ITree.observe_cofix] at hv
    cases hs : step s with
    | ret _ => rw [hs] at hv; cases hv
    | tau _ => rw [hs] at hv; cases hv
    | vis i k =>
      cases i with
      | inl f =>
        cases f with
        | fail _ =>
          rw [hs] at hv
          injection hv with hij _
          cases hij
          exact False.elim (hnf trivial)
      | inr j =>
        rw [hs] at hv
        injection hv with hij hkj
        cases hij
        cases eq_of_heq hkj
        dsimp only [SumE] at k o' ⊢
        cases ho : handle j with
        | ok o =>
          have hoo' : o' = o := hSub j o ho o'
          subst hoo'
          have hstep : gapStep step site handle s = .next (k o') := by
            rw [gapStep_of_vis hs, ho]
          have hback : ∀ out, gapBehaviors (gapStep step site handle) (k o') out →
              gapBehaviors (gapStep step site handle) s out :=
            fun out hm => (gapBehaviors_reach_iff _ (.step hstep (.refl _)) out).mpr hm
          obtain ⟨s'', hu, hDef'', hb''⟩ := ih (fun _ hm => hDef (hback _ hm)) rfl
          exact ⟨s'', hu, hDef'', fun out hm => hback out (hb'' out hm)⟩
        | fault e =>
          have hstep : gapStep step site handle s = .done (.fault e) := by
            rw [gapStep_of_vis hs, ho]
          have hmem : gapBehaviors (gapStep step site handle) s (.fault e) :=
            ⟨(fun h₀ => by cases h₀), 1, runGapSteps_succ_of_done _ hstep 0⟩
          exact False.elim (hDef hmem (hNoDefFault j e ho))
        | gap g =>
          have hstep : gapStep step site handle s = .done (.gap g) := by
            rw [gapStep_of_vis hs, ho]
          have hne : (OutcomeWithGap.gap g :
              OutcomeWithGap ExecFault (GapTag Site) Val) ≠ .gap .outOfFuel := by
            intro h₀
            cases OutcomeWithGap.gap.inj h₀
            exact hSealed j ho
          have hmem : gapBehaviors (gapStep step site handle) s (.gap g) :=
            ⟨hne, 1, runGapSteps_succ_of_done _ hstep 0⟩
          exact False.elim (hDef hmem)

/--
Fuel-free, termination-free `TreeSafe` adequacy: for any sealed,
subsingleton-answering, UB-only-faulting handler, `OutcomeSet.Defined` on
`gapBehaviors` implies `TreeSafe (ITree.cofix step s)` constructively — covering
both terminating executions and silently or reactively diverging loops.
-/
theorem treeSafe_of_gapBehaviors_defined
    (hE : ∀ i : E.I, ¬ FaultEffect.isFault i)
    (hSealed : ∀ i : E.I, handle i ≠ .gap .outOfFuel)
    (hSub : ∀ (i : E.I) (o : E.O i), handle i = .ok o → ∀ o' : E.O i, o' = o)
    (hNoDefFault : ∀ (i : E.I) (e : ExecFault), handle i = .fault e → e.isUB)
    {s : State}
    (hDef : OutcomeSet.Defined ExecFault.isUB
      (gapBehaviors (gapStep step site handle) s)) :
    TreeSafe (ITree.cofix step s) := by
  intro tr u hreach ⟨u', idx, c, hts, hvu', hfi⟩
  obtain ⟨s', rfl, hDef', _⟩ :=
    reaches_cofix_of_defined hSealed hSub hNoDefFault (reaches_append_tauStar hreach hts) hDef
  rw [ITree.observe_cofix] at hvu'
  cases hs : step s' with
  | ret _ => rw [hs] at hvu'; cases hvu'
  | tau _ => rw [hs] at hvu'; cases hvu'
  | vis i k =>
    cases i with
    | inl f =>
      cases f with
      | fail kind =>
        have hmem : gapBehaviors (gapStep step site handle) s'
            (classifyFailure (site s') kind) :=
          ⟨classifyFailure_ne_outOfFuel (site s') kind, 1, runStepsWithGap_of_fail hs 0⟩
        have hd := hDef' hmem
        cases kind with
        | ub => exact hd trivial
        | unsupported => exact hd
        | outOfFuel => exact hd
    | inr j =>
      rw [hs] at hvu'
      injection hvu' with hij _
      cases hij
      exact hE j hfi

/--
Fuel-free return adequacy under `OutcomeSet.Defined`: `(ITree.cofix step s)`
returns `out` along some trace if and only if `gapBehaviors` contains
`classifyOutcome out`.
-/
theorem reachesRet_iff_gapBehaviors_of_defined
    (hE : ∀ i : E.I, ¬ FaultEffect.isFault i)
    (hSealed : ∀ i : E.I, handle i ≠ .gap .outOfFuel)
    (hSub : ∀ (i : E.I) (o : E.O i), handle i = .ok o → ∀ o' : E.O i, o' = o)
    (hNoDefFault : ∀ (i : E.I) (e : ExecFault), handle i = .fault e → e.isUB)
    {s : State}
    (hDef : OutcomeSet.Defined ExecFault.isUB
      (gapBehaviors (gapStep step site handle) s))
    (out : Outcome Val) :
    (∃ tr, ReachesRet (ITree.cofix step s) tr out) ↔
      gapBehaviors (gapStep step site handle) s (classifyOutcome out) := by
  constructor
  · rintro ⟨tr, u, hreach, hu⟩
    obtain ⟨s', rfl, _, hback⟩ :=
      reaches_cofix_of_defined hSealed hSub hNoDefFault hreach hDef
    rw [ITree.observe_cofix] at hu
    cases hs : step s' with
    | ret out' =>
      rw [hs] at hu
      injection hu with heq
      subst heq
      exact hback _ ⟨classifyOutcome_ne_outOfFuel out', 1, runStepsWithGap_of_ret hs 0⟩
    | tau _ => rw [hs] at hu; cases hu
    | vis _ _ => rw [hs] at hu; cases hu
  · rintro ⟨_, fuel, hrun⟩
    exact runStepsWithGap_defined_reachesRet hE hNoDefFault hrun

end Adequacy

section MirAdequacy

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-- `stepMirSiteState body` unfolds to the exact same `ITree` as `stepMirState body`. -/
theorem cofix_stepMirSiteState_eq (body : CapturedMir) (st : MirSiteState) :
    ITree.cofix (stepMirSiteState body) st =
      ITree.cofix (stepMirState body) st.exec := by
  refine cofix_hom_eq (stepMirSiteState body) (stepMirState body)
    MirSiteState.exec (fun x => ?_) st
  unfold stepMirSiteState
  have hexec : ∀ es' : MirExecState, (mirNextSiteState body x es').exec = es' := by
    intro es'
    cases es' <;> cases x <;> rfl
  cases stepMirState body x.exec with
  | ret _ => rfl
  | tau es' => exact congrArg ITreeF.tau (hexec es')
  | vis i k =>
    dsimp only [ITreeF.map]
    congr
    funext o
    exact hexec (k o)

theorem cofix_stepMirSiteState_eq_mirTree (body : CapturedMir) (s : MachineState) :
    ITree.cofix (stepMirSiteState body) (mirSiteOfExec body (.running s)) =
      mirTree body s :=
  cofix_stepMirSiteState_eq body (mirSiteOfExec body (.running s))

/-- Observations and external calls are not fault requests. -/
theorem mirHandled_not_fault :
    ∀ i : (SumE MirObsE MirCallE).I, ¬ FaultEffect.isFault i := by
  intro i
  cases i <;> exact fun h => h

/-- `mirGapHandle env` never produces a defined fault: only callee UB faults. -/
theorem mirGapHandle_noDefFault (env : MirCallEnv) :
    ∀ (i : (SumE MirObsE MirCallE).I) (e : ExecFault),
      mirGapHandle env i = .fault e → e.isUB := by
  intro i e h
  cases i with
  | inl obs => cases obs; cases h
  | inr call =>
    cases call with
    | call req =>
      dsimp only [mirGapHandle] at h
      cases he : env req with
      | ok _ => rw [he] at h; cases h
      | fault _ => rw [he] at h; cases h; trivial
      | gap _ => rw [he] at h; cases h

/--
Unconditional handler sealing: for *every* `env : MirCallEnv` (even a raw
environment returning `.gap .outOfFuel`), `mirGapHandle env` never emits the
outer evaluator's `.gap .outOfFuel` sentinel.
-/
theorem mirGapHandle_ne_outOfFuel (env : MirCallEnv) :
    ∀ i : (SumE MirObsE MirCallE).I, mirGapHandle env i ≠ .gap .outOfFuel := by
  intro i h
  cases i with
  | inl obs => cases obs; cases h
  | inr call =>
    cases call with
    | call req =>
      dsimp only [mirGapHandle] at h
      cases he : env req with
      | ok _ => rw [he] at h; cases h
      | fault _ => rw [he] at h; cases h
      | gap g =>
        rw [he] at h
        exact GapTag.sealOutOfFuel_ne_outOfFuel req.defPath g (OutcomeWithGap.gap.inj h)

theorem mirGapHandle_sealed {env : MirCallEnv} (_ : env.IsSealed) :
    ∀ i : (SumE MirObsE MirCallE).I, mirGapHandle env i ≠ .gap .outOfFuel :=
  mirGapHandle_ne_outOfFuel env

/-- `mirSiteGapStep env body` never halts with `.done (.gap .outOfFuel)`. -/
theorem mirSiteGapStep_ne_done_outOfFuel (env : MirCallEnv) (body : CapturedMir)
    (st : MirSiteState) :
    mirSiteGapStep env body st ≠ .done (.gap .outOfFuel) :=
  gapStep_ne_done_outOfFuel (mirGapHandle_ne_outOfFuel env) st

/--
Unconditional empty-behavior characterization: for *every* `env : MirCallEnv`,
`mirGapBehaviors` is empty if and only if every bounded run exhausts its fuel
(genuine divergence, never a leaked callee `.outOfFuel`).
-/
theorem mirGapBehaviors_empty_iff (env : MirCallEnv) (callees : List CapturedMir)
    (body : CapturedMir) (args : List Value) :
    (∀ o, ¬ mirGapBehaviors env callees body args o) ↔
      ∀ fuel, runMirWithGap env callees body fuel args = .gap .outOfFuel :=
  gapBehaviors_empty_iff (mirSiteGapStep env body)
    (mirSiteGapStep_ne_done_outOfFuel env body) _

/-- Under `MirCallEnv.unresolved`, only `MirObsE` (whose answer type is `PUnit`) is answered. -/
theorem mirGapHandle_unresolved_subsingleton :
    ∀ (i : (SumE MirObsE MirCallE).I) (o : (SumE MirObsE MirCallE).O i),
      mirGapHandle MirCallEnv.unresolved i = .ok o → ∀ o', o' = o := by
  intro i o h o'
  cases i with
  | inl obs => cases obs; cases o; cases o'; rfl
  | inr call => cases call; cases h

variable {env : MirCallEnv} {body : CapturedMir}

/--
Soundness of reported values against the trusted semantics: a value returned
by the gap-aware evaluator from state `s` is returned by `mirTree body s`.
-/
theorem runMirStepsWithGap_ok_reachesRet {fuel : Nat} {s : MachineState}
    {r : MirReturn} (h : runMirStepsWithGap env body fuel (.running s) = .ok r) :
    ∃ tr, ReachesRet (mirTree body s) tr (.normal r) := by
  rw [← cofix_stepMirSiteState_eq_mirTree body s]
  exact runStepsWithGap_ok_reachesRet (step := stepMirSiteState body)
    (site := mirSiteOfState body) (handle := mirGapHandle env) mirHandled_not_fault h

/--
Soundness of all defined MIR outcomes (`.normal`, `.panic`, and `.abort`)
against the trusted `mirTree`, for *every* callee environment `env`.
-/
theorem runMirStepsWithGap_defined_reachesRet {fuel : Nat} {s : MachineState}
    {out : MirOutcome}
    (h : runMirStepsWithGap env body fuel (.running s) = classifyOutcome out) :
    ∃ tr, ReachesRet (mirTree body s) tr out := by
  rw [← cofix_stepMirSiteState_eq_mirTree body s]
  exact runStepsWithGap_defined_reachesRet (step := stepMirSiteState body)
    (site := mirSiteOfState body) (handle := mirGapHandle env)
    mirHandled_not_fault (mirGapHandle_noDefFault env) h

theorem runMirWithGap_ok_reachesRet {callees : List CapturedMir} {fuel : Nat}
    {args : List Value} {r : MirReturn}
    (h : runMirWithGap env callees body fuel args = .ok r) :
    ∃ tr, ReachesRet
      (mirTree body (initMachineStateWithCallees body args callees)) tr (.normal r) :=
  runMirStepsWithGap_ok_reachesRet h

theorem runMirWithGap_defined_reachesRet {callees : List CapturedMir} {fuel : Nat}
    {args : List Value} {out : MirOutcome}
    (h : runMirWithGap env callees body fuel args = classifyOutcome out) :
    ∃ tr, ReachesRet
      (mirTree body (initMachineStateWithCallees body args callees)) tr out :=
  runMirStepsWithGap_defined_reachesRet h

/-- Every value of the fuel-free semantics is returned by the trusted `mirTree`. -/
theorem mirGapBehaviors_ok_reachesRet {callees : List CapturedMir}
    {args : List Value} {r : MirReturn}
    (h : mirGapBehaviors env callees body args (.ok r)) :
    ∃ tr, ReachesRet
      (mirTree body (initMachineStateWithCallees body args callees)) tr (.normal r) := by
  obtain ⟨_, _, hrun⟩ := h
  exact runMirWithGap_ok_reachesRet hrun

/-- Every defined outcome (`.normal`, `.panic`, `.abort`) of `mirGapBehaviors` is returned by `mirTree`. -/
theorem mirGapBehaviors_defined_reachesRet {callees : List CapturedMir}
    {args : List Value} {out : MirOutcome}
    (h : mirGapBehaviors env callees body args (classifyOutcome out)) :
    ∃ tr, ReachesRet
      (mirTree body (initMachineStateWithCallees body args callees)) tr out := by
  obtain ⟨_, _, hrun⟩ := h
  exact runMirWithGap_defined_reachesRet hrun

/--
Fuel-free, termination-free `MirNoUBTree` adequacy: if `mirGapBehaviors` is
`OutcomeSet.Defined` under `MirCallEnv.unresolved` (whether terminating or
diverging), the trusted `mirTree` satisfies `MirNoUBTree`.
-/
theorem mirNoUBTree_of_mirGapBehaviors_defined {callees : List CapturedMir}
    {args : List Value}
    (hDef : OutcomeSet.Defined ExecFault.isUB
      (mirGapBehaviors MirCallEnv.unresolved callees body args)) :
    MirNoUBTree (mirTree body (initMachineStateWithCallees body args callees)) := by
  unfold MirNoUBTree
  rw [← cofix_stepMirSiteState_eq_mirTree body
    (initMachineStateWithCallees body args callees)]
  exact treeSafe_of_gapBehaviors_defined
    mirHandled_not_fault
    (mirGapHandle_ne_outOfFuel MirCallEnv.unresolved)
    mirGapHandle_unresolved_subsingleton
    (mirGapHandle_noDefFault MirCallEnv.unresolved)
    hDef

/--
Fuel-free return characterization under `OutcomeSet.Defined`: the trusted
`mirTree` returns `out` along some trace iff `mirGapBehaviors` contains
`classifyOutcome out`.
-/
theorem mirReachesRet_iff_mirGapBehaviors_of_defined {callees : List CapturedMir}
    {args : List Value}
    (hDef : OutcomeSet.Defined ExecFault.isUB
      (mirGapBehaviors MirCallEnv.unresolved callees body args))
    (out : MirOutcome) :
    (∃ tr, ReachesRet
      (mirTree body (initMachineStateWithCallees body args callees)) tr out) ↔
      mirGapBehaviors MirCallEnv.unresolved callees body args (classifyOutcome out) := by
  rw [← cofix_stepMirSiteState_eq_mirTree body
    (initMachineStateWithCallees body args callees)]
  exact reachesRet_iff_gapBehaviors_of_defined
    mirHandled_not_fault
    (mirGapHandle_ne_outOfFuel MirCallEnv.unresolved)
    mirGapHandle_unresolved_subsingleton
    (mirGapHandle_noDefFault MirCallEnv.unresolved)
    hDef out

/--
Full two-way adequacy against the trusted `mirTree` under the closed-world
environment: a defined bounded run (`.normal`, `.panic`, or `.abort`) implies
`MirNoUBTree`, reachability of `out`, and uniqueness of the returned `MirOutcome`.
-/
theorem mirTree_adequate_of_defined {callees : List CapturedMir} {fuel : Nat}
    {args : List Value} {out : MirOutcome}
    (h : runMirWithGap MirCallEnv.unresolved callees body fuel args =
      classifyOutcome out) :
    MirNoUBTree (mirTree body (initMachineStateWithCallees body args callees)) ∧
      (∃ tr, ReachesRet
        (mirTree body (initMachineStateWithCallees body args callees)) tr out) ∧
      (∀ tr out', ReachesRet
        (mirTree body (initMachineStateWithCallees body args callees)) tr out' →
          out' = out) := by
  have hDef : OutcomeSet.Defined ExecFault.isUB
      (mirGapBehaviors MirCallEnv.unresolved callees body args) :=
    defined_mirGapBehaviors_of_run (h ▸ classifyOutcome_isDefined out)
  have hne : runMirWithGap MirCallEnv.unresolved callees body fuel args ≠ .gap .outOfFuel :=
    h ▸ classifyOutcome_ne_outOfFuel out
  refine ⟨mirNoUBTree_of_mirGapBehaviors_defined hDef,
    runMirWithGap_defined_reachesRet h, fun tr out' hrr => ?_⟩
  have hm := (mirReachesRet_iff_mirGapBehaviors_of_defined hDef out').mp ⟨tr, hrr⟩
  have heq := (mirGapBehaviors_iff_of_run hne (classifyOutcome out')).mp hm
  exact classifyOutcome_injective (heq.trans h)

/-- Fuel-free two-way adequacy: a defined outcome in `mirGapBehaviors` implies `MirNoUBTree` and unique return. -/
theorem mirTree_adequate_of_mirGapBehaviors_defined {callees : List CapturedMir}
    {args : List Value} {out : MirOutcome}
    (h : mirGapBehaviors MirCallEnv.unresolved callees body args (classifyOutcome out)) :
    MirNoUBTree (mirTree body (initMachineStateWithCallees body args callees)) ∧
      (∃ tr, ReachesRet
        (mirTree body (initMachineStateWithCallees body args callees)) tr out) ∧
      (∀ tr out', ReachesRet
        (mirTree body (initMachineStateWithCallees body args callees)) tr out' →
          out' = out) := by
  obtain ⟨_, _, hrun⟩ := h
  exact mirTree_adequate_of_defined hrun

/--
Fuel-free, termination-free Layer 1A `ITree.toPartial` bridge: if `body₁` and
`body₂` satisfy `ContextEquivOn pre` under `MirCallEnv.unresolved` and `body₁`
is `OutcomeSet.Defined` on `args` (`pre args`) — with NO fuel witness and NO
termination assumption, covering both terminating bodies and diverging loops —
then BOTH trusted `mirTree`s satisfy `MirNoUBTree` and have equal trace-erased
`ITree.toPartial` semantics.
-/
theorem mirContextEquivOn_toPartial_eq_of_defined {callees : List CapturedMir}
    {body₁ body₂ : CapturedMir} {pre : List Value → Prop}
    (hEq : ContextEquivOn pre (· = ·) (· = ·)
      (mirGapBehaviors MirCallEnv.unresolved callees body₁)
      (mirGapBehaviors MirCallEnv.unresolved callees body₂))
    {args : List Value} (hpre : pre args)
    (hDef₁ : OutcomeSet.Defined ExecFault.isUB
      (mirGapBehaviors MirCallEnv.unresolved callees body₁ args)) :
    let t₁ := mirTree body₁ (initMachineStateWithCallees body₁ args callees)
    let t₂ := mirTree body₂ (initMachineStateWithCallees body₂ args callees)
    MirNoUBTree t₁ ∧ MirNoUBTree t₂ ∧
      Partial.map (BehaviorSet.map Prod.snd) t₁.toPartial =
        Partial.map (BehaviorSet.map Prod.snd) t₂.toPartial := by
  dsimp only
  have hDef₂ : OutcomeSet.Defined ExecFault.isUB
      (mirGapBehaviors MirCallEnv.unresolved callees body₂ args) :=
    ((hEq args hpre).defined_iff ExecFault.eq_preserves_isUB).mp hDef₁
  have hs₁ := mirNoUBTree_of_mirGapBehaviors_defined hDef₁
  have hs₂ := mirNoUBTree_of_mirGapBehaviors_defined hDef₂
  refine ⟨hs₁, hs₂, Partial.ext ⟨fun _ => hs₂, fun _ => hs₁⟩ (fun _ _ => ?_)⟩
  funext out; apply propext
  constructor
  · rintro ⟨⟨tr₁, out'⟩, hrr₁, rfl⟩
    have hm₁ := (mirReachesRet_iff_mirGapBehaviors_of_defined hDef₁ out').mp ⟨tr₁, hrr₁⟩
    have hm₂ := (hEq args hpre).subset_of_eq (classifyOutcome out') hm₁
    obtain ⟨tr₂, hrr₂⟩ :=
      (mirReachesRet_iff_mirGapBehaviors_of_defined hDef₂ out').mpr hm₂
    exact ⟨⟨tr₂, out'⟩, hrr₂, rfl⟩
  · rintro ⟨⟨tr₂, out'⟩, hrr₂, rfl⟩
    have hm₂ := (mirReachesRet_iff_mirGapBehaviors_of_defined hDef₂ out').mp ⟨tr₂, hrr₂⟩
    have hm₁ := (hEq args hpre).superset_of_eq (classifyOutcome out') hm₂
    obtain ⟨tr₁, hrr₁⟩ :=
      (mirReachesRet_iff_mirGapBehaviors_of_defined hDef₁ out').mpr hm₁
    exact ⟨⟨tr₁, out'⟩, hrr₁, rfl⟩

/--
End-to-end Layer 1A bridge to the trusted `mirTree` from a single bounded
baseline run (corollary of `mirContextEquivOn_toPartial_eq_of_defined`).
-/
theorem mirContextEquivOn_toPartial_eq {callees : List CapturedMir}
    {body₁ body₂ : CapturedMir} {pre : List Value → Prop}
    (hEq : ContextEquivOn pre (· = ·) (· = ·)
      (mirGapBehaviors MirCallEnv.unresolved callees body₁)
      (mirGapBehaviors MirCallEnv.unresolved callees body₂))
    {args : List Value} (hpre : pre args) {fuel : Nat} {out : MirOutcome}
    (hBase : runMirWithGap MirCallEnv.unresolved callees body₁ fuel args =
      classifyOutcome out) :
    let t₁ := mirTree body₁ (initMachineStateWithCallees body₁ args callees)
    let t₂ := mirTree body₂ (initMachineStateWithCallees body₂ args callees)
    MirNoUBTree t₁ ∧ MirNoUBTree t₂ ∧
      Partial.map (BehaviorSet.map Prod.snd) t₁.toPartial =
        Partial.map (BehaviorSet.map Prod.snd) t₂.toPartial :=
  mirContextEquivOn_toPartial_eq_of_defined hEq hpre
    (defined_mirGapBehaviors_of_run (hBase ▸ classifyOutcome_isDefined out))

/--
Under the closed-world environment, a run ending in UB, an `unsupported` gap,
or a machine-reported `budget` gap reaches a fault of the trusted `mirTree`:
the trusted Layer 1A semantics of the body is undefined on these arguments,
exactly like the gap-aware one.
-/
private theorem not_mirTree_safe_of_run_undefined {s : MachineState} {fuel : Nat}
    {o : OutcomeWithGap ExecFault (GapTag DefPath) MirReturn}
    (h : runMirStepsWithGap MirCallEnv.unresolved body fuel (.running s) = o)
    (ho : o = .fault .ub ∨ (∃ site, o = .gap (.unsupported site)) ∨
      (∃ site, o = .gap (.budget site))) :
    ¬ MirNoUBTree (mirTree body s) := by
  unfold MirNoUBTree
  rw [← cofix_stepMirSiteState_eq_mirTree body s]
  refine not_treeSafe_of_runStepsWithGap (step := stepMirSiteState body)
    (site := mirSiteOfState body) (handle := mirGapHandle MirCallEnv.unresolved)
    mirHandled_not_fault h ?_ ?_ ?_ ?_
  · rcases ho with rfl | ⟨site, rfl⟩ | ⟨site, rfl⟩ <;> exact fun h₀ => by cases h₀
  · rcases ho with rfl | ⟨site, rfl⟩ | ⟨site, rfl⟩
    · exact fun hd => hd trivial
    · exact fun hd => hd
    · exact fun hd => hd
  · intro i e hi
    cases i with
    | inl obs =>
      cases obs with
      | emit ev => cases hi
    | inr call =>
      cases call with
      | call req => cases hi
  · intro i g hi
    cases i with
    | inl obs =>
      cases obs with
      | emit ev => cases hi
    | inr call =>
      cases call with
      | call req =>
        cases hi
        rcases ho with rfl | ⟨site, rfl⟩ | ⟨site, rfl⟩ <;> exact fun h₀ => by cases h₀

theorem not_mirNoUBTree_of_run_undefined {callees : List CapturedMir} {fuel : Nat}
    {args : List Value} {o : OutcomeWithGap ExecFault (GapTag DefPath) MirReturn}
    (h : runMirWithGap MirCallEnv.unresolved callees body fuel args = o)
    (ho : o = .fault .ub ∨ (∃ site, o = .gap (.unsupported site)) ∨
      (∃ site, o = .gap (.budget site))) :
    ¬ MirNoUBTree (mirTree body (initMachineStateWithCallees body args callees)) :=
  not_mirTree_safe_of_run_undefined h ho

/--
Under *any* callee environment `env`, if a bounded run ends in a non-`outOfFuel`
gap `g` that `env.seal` never emits (accounting for both direct gaps of `env`
and `.budget req.defPath` gaps produced by sealing callee `.outOfFuel`), that
gap comes from a `MirFailE` node of the stepped MIR body, so `mirTree` is not
`MirNoUBTree`.
-/
theorem not_mirNoUBTree_of_run_gap_not_from_env {callees : List CapturedMir}
    {fuel : Nat} {args : List Value} {g : GapTag DefPath}
    (h : runMirWithGap env callees body fuel args = .gap g)
    (hne : g ≠ .outOfFuel) (hEnv : ∀ req, env.seal req ≠ .gap g) :
    ¬ MirNoUBTree (mirTree body (initMachineStateWithCallees body args callees)) := by
  unfold MirNoUBTree
  rw [← cofix_stepMirSiteState_eq_mirTree body
    (initMachineStateWithCallees body args callees)]
  refine not_treeSafe_of_runStepsWithGap (step := stepMirSiteState body)
    (site := mirSiteOfState body) (handle := mirGapHandle env)
    mirHandled_not_fault h (fun h₀ => hne (OutcomeWithGap.gap.inj h₀))
    (fun hd => hd) (fun _ _ _ h₀ => by cases h₀) ?_
  intro i g' hi hEq
  cases OutcomeWithGap.gap.inj hEq
  cases i with
  | inl obs =>
    cases obs with
    | emit ev => cases hi
  | inr call =>
    cases call with
    | call req =>
      dsimp only [mirGapHandle] at hi
      cases he : env req with
      | ok _ => rw [he] at hi; cases hi
      | fault _ => rw [he] at hi; cases hi
      | gap g₀ =>
        rw [he] at hi
        cases OutcomeWithGap.gap.inj hi
        exact hEnv req (by dsimp only [MirCallEnv.seal]; rw [he]; rfl)

/--
Converse `MirNoUBTree` adequacy for closed-world MIR bodies: if the trusted
`mirTree` satisfies `MirNoUBTree` and execution never hits an `.unresolved`
external call, then `mirGapBehaviors MirCallEnv.unresolved` is
`OutcomeSet.Defined` (no UB and no modeling/budget gaps).
-/
theorem mirGapBehaviors_defined_of_mirNoUBTree {callees : List CapturedMir}
    {args : List Value}
    (hSafe : MirNoUBTree (mirTree body (initMachineStateWithCallees body args callees)))
    (hClosed : ∀ site,
      ¬ mirGapBehaviors MirCallEnv.unresolved callees body args (.gap (.unresolved site))) :
    OutcomeSet.Defined ExecFault.isUB
      (mirGapBehaviors MirCallEnv.unresolved callees body args) := by
  intro o ho
  obtain ⟨hne, fuel, hrun⟩ := ho
  cases o with
  | ok _ => exact trivial
  | fault e =>
    cases e with
    | ub => exact False.elim (not_mirNoUBTree_of_run_undefined hrun (Or.inl rfl) hSafe)
    | panic => exact fun h => h
    | abort => exact fun h => h
  | gap g =>
    cases g with
    | unsupported site =>
      exact False.elim
        (not_mirNoUBTree_of_run_undefined hrun (Or.inr (Or.inl ⟨site, rfl⟩)) hSafe)
    | budget site =>
      exact False.elim
        (not_mirNoUBTree_of_run_undefined hrun (Or.inr (Or.inr ⟨site, rfl⟩)) hSafe)
    | unresolved site =>
      exact False.elim (hClosed site ⟨hne, fuel, hrun⟩)
    | outOfFuel => exact False.elim (hne rfl)

/--
Full closed-world equivalence between `OutcomeSet.Defined` of `mirGapBehaviors`
and `MirNoUBTree` of the trusted `mirTree` whenever no `.unresolved` external
call is reached.
-/
theorem mirGapBehaviors_defined_iff_mirNoUBTree {callees : List CapturedMir}
    {args : List Value}
    (hClosed : ∀ site,
      ¬ mirGapBehaviors MirCallEnv.unresolved callees body args (.gap (.unresolved site))) :
    OutcomeSet.Defined ExecFault.isUB
        (mirGapBehaviors MirCallEnv.unresolved callees body args) ↔
      MirNoUBTree (mirTree body (initMachineStateWithCallees body args callees)) :=
  ⟨mirNoUBTree_of_mirGapBehaviors_defined,
   fun hSafe => mirGapBehaviors_defined_of_mirNoUBTree hSafe hClosed⟩

/-- Trace-erased Layer 1A semantics of the trusted `mirTree` with inline `callees`. -/
def mirTreeTraceErasedSem (callees : List CapturedMir) :
    Semantics CapturedMir (List Value → Partial (BehaviorSet MirOutcome)) :=
  fun body args =>
    Partial.map (BehaviorSet.map Prod.snd)
      (mirTree body (initMachineStateWithCallees body args callees)).toPartial

/-- Trace-erased Layer 1A semantics of the trusted `MirLang` (`callees = []`). -/
def mirLangTraceErasedSem :
    Semantics CapturedMir (List Value → Partial (BehaviorSet MirOutcome)) :=
  fun body args =>
    Partial.map (BehaviorSet.map Prod.snd) (MirLang.sem body args)

/--
Unconditional closed-world Layer 1A `ITree.toPartial` equality (requiring NO
definedness hypothesis `hDef₁`, covering defined returns, panics, aborts,
diverging loops, UB, and shared `.unsupported`/`.budget` gaps alike): whenever
`body₁` and `body₂` are `ContextEquivOn pre` under `MirCallEnv.unresolved` and
`body₁` does not reach an `.unresolved` external call on `args`, their trusted
`mirTree`s have identical trace-erased `ITree.toPartial` semantics on `args`.
-/
theorem mirContextEquivOn_mirTree_toPartial_eq {callees : List CapturedMir}
    {body₁ body₂ : CapturedMir} {pre : List Value → Prop}
    (hEq : ContextEquivOn pre (· = ·) (· = ·)
      (mirGapBehaviors MirCallEnv.unresolved callees body₁)
      (mirGapBehaviors MirCallEnv.unresolved callees body₂))
    {args : List Value} (hpre : pre args)
    (hClosed : ∀ site,
      ¬ mirGapBehaviors MirCallEnv.unresolved callees body₁ args (.gap (.unresolved site))) :
    mirTreeTraceErasedSem callees body₁ args =
      mirTreeTraceErasedSem callees body₂ args := by
  have hClosed₂ : ∀ site,
      ¬ mirGapBehaviors MirCallEnv.unresolved callees body₂ args (.gap (.unresolved site)) :=
    fun site hm₂ => hClosed site ((hEq args hpre).superset_of_eq _ hm₂)
  refine Partial.ext ⟨fun h₁ => ?_, fun h₂ => ?_⟩ (fun h₁ h₂ => ?_)
  · have hDef₁ := mirGapBehaviors_defined_of_mirNoUBTree h₁ hClosed
    exact (mirContextEquivOn_toPartial_eq_of_defined hEq hpre hDef₁).2.1
  · have hDef₂ := mirGapBehaviors_defined_of_mirNoUBTree h₂ hClosed₂
    have hDef₁ := ((hEq args hpre).defined_iff ExecFault.eq_preserves_isUB).mpr hDef₂
    exact mirNoUBTree_of_mirGapBehaviors_defined hDef₁
  · have hDef₁ := mirGapBehaviors_defined_of_mirNoUBTree h₁ hClosed
    have hValOfEq : ∀ (p q : Partial (BehaviorSet MirOutcome))
        (hp : p.defined) (hq : q.defined), p = q → p.val hp = q.val hq := by
      rintro p _ hp hq rfl; rfl
    exact hValOfEq _ _ h₁ h₂
      (mirContextEquivOn_toPartial_eq_of_defined hEq hpre hDef₁).2.2

/--
Query-restricted `ExactPass` directly on the trusted `mirTree` (trace-erased):
any `ContextEquivOn pre` between closed-world MIR bodies induces an
identity-observation `ExactPass` over `{ args // pre args }`, even when both
bodies share `.unsupported` modeling gaps, UB, or diverging loops.
-/
theorem mirContextEquivOn_mirTree_exactPass {callees : List CapturedMir}
    {body₁ body₂ : CapturedMir} {pre : List Value → Prop}
    (hEq : ContextEquivOn pre (· = ·) (· = ·)
      (mirGapBehaviors MirCallEnv.unresolved callees body₁)
      (mirGapBehaviors MirCallEnv.unresolved callees body₂))
    (hClosed : ∀ args, pre args → ∀ site,
      ¬ mirGapBehaviors MirCallEnv.unresolved callees body₁ args (.gap (.unresolved site))) :
    ExactPass
      (fun b (q : { args : List Value // pre args }) => mirTreeTraceErasedSem callees b q.1)
      (fun b (q : { args : List Value // pre args }) => mirTreeTraceErasedSem callees b q.1)
      id id body₁ body₂ where
  up_refines _ q := by
    dsimp only [id]
    rw [mirContextEquivOn_mirTree_toPartial_eq hEq q.2 (hClosed q.1 q.2)]
    exact fun h => ⟨h, fun _ hx => hx⟩
  down_refines _ q := by
    dsimp only [id]
    rw [mirContextEquivOn_mirTree_toPartial_eq hEq q.2 (hClosed q.1 q.2)]
    exact fun h => ⟨h, fun _ hx => hx⟩

/--
Full-domain `ExactPass` directly on the trusted `mirTree` (trace-erased) for
closed-world MIR bodies with inline `callees`.
-/
theorem mirContextEquiv_mirTree_exactPass {callees : List CapturedMir}
    {body₁ body₂ : CapturedMir}
    (hEq : ContextEquiv (· = ·) (· = ·)
      (mirGapBehaviors MirCallEnv.unresolved callees body₁)
      (mirGapBehaviors MirCallEnv.unresolved callees body₂))
    (hClosed : ∀ args site,
      ¬ mirGapBehaviors MirCallEnv.unresolved callees body₁ args (.gap (.unresolved site))) :
    ExactPass (mirTreeTraceErasedSem callees) (mirTreeTraceErasedSem callees)
      id id body₁ body₂ where
  up_refines _ args := by
    dsimp only [id]
    rw [mirContextEquivOn_mirTree_toPartial_eq (pre := fun _ => True)
      (fun a _ => hEq a) trivial (hClosed args)]
    exact fun h => ⟨h, fun _ hx => hx⟩
  down_refines _ args := by
    dsimp only [id]
    rw [mirContextEquivOn_mirTree_toPartial_eq (pre := fun _ => True)
      (fun a _ => hEq a) trivial (hClosed args)]
    exact fun h => ⟨h, fun _ hx => hx⟩

/--
Direct `ExactPass` on the trusted `MirLang` (trace-erased, `callees = []`):
any exact `ContextEquiv` between self-contained MIR bodies induces an
identity-observation `ExactPass` on `MirLang`.
-/
theorem mirContextEquiv_mirLang_exactPass {body₁ body₂ : CapturedMir}
    (hEq : ContextEquiv (· = ·) (· = ·)
      (mirGapBehaviors MirCallEnv.unresolved [] body₁)
      (mirGapBehaviors MirCallEnv.unresolved [] body₂))
    (hClosed : ∀ args site,
      ¬ mirGapBehaviors MirCallEnv.unresolved [] body₁ args (.gap (.unresolved site))) :
    ExactPass mirLangTraceErasedSem mirLangTraceErasedSem id id body₁ body₂ :=
  mirContextEquiv_mirTree_exactPass hEq hClosed

/-! ### `Trusted.VerificationResult` Contract & Certificate Transfer + Open-World `mirHandledTreeWithCallees` Bridges -/

/--
Transfer `Trusted.VerificationResult.MirContractHoldsWithSafetyAndCallees` from
`body₁` to `body₂` along a return-value `ContextEquivOn safetyPre` (`r₁.1 = r₂.1`),
requiring `hClosed` **only on `safetyPre`** (so `¬ safetyPre` may freely call
unresolved external functions or hit `.unsupported` gaps, and `body₂` may differ
in post-return `Memory` metadata such as borrow-tag counters!).
-/
theorem mirContractHoldsWithSafetyAndCallees_of_contextEquiv
    {callees : List CapturedMir} {body₁ body₂ : CapturedMir}
    {safetyPre pre : List Value → Prop} {post : List Value → Value → Prop}
    (hEq : ContextEquivOn safetyPre (fun r₁ r₂ : MirReturn => r₁.1 = r₂.1) (· = ·)
      (mirGapBehaviors MirCallEnv.unresolved callees body₁)
      (mirGapBehaviors MirCallEnv.unresolved callees body₂))
    (hClosed : ∀ args, safetyPre args → ∀ site,
      ¬ mirGapBehaviors MirCallEnv.unresolved callees body₁ args (.gap (.unresolved site)))
    (hBase : Trusted.VerificationResult.MirContractHoldsWithSafetyAndCallees
      body₁ callees safetyPre pre post) :
    Trusted.VerificationResult.MirContractHoldsWithSafetyAndCallees
      body₂ callees safetyPre pre post := by
  intro args hsafe
  obtain ⟨hs₁, hval₁⟩ := hBase args hsafe
  have hDef₁ := mirGapBehaviors_defined_of_mirNoUBTree hs₁ (hClosed args hsafe)
  have hDef₂ := ((hEq args hsafe).defined_iff ExecFault.eq_preserves_isUB).mp hDef₁
  have hs₂ := mirNoUBTree_of_mirGapBehaviors_defined hDef₂
  refine ⟨hs₂, fun outPair hrr₂ hp retVal mem₂' hout => ?_⟩
  rcases outPair with ⟨tr₂, out₂⟩
  dsimp only at hout
  subst hout
  have hm₂ :=
    (mirReachesRet_iff_mirGapBehaviors_of_defined hDef₂ (.normal (retVal, mem₂'))).mp ⟨tr₂, hrr₂⟩
  obtain ⟨o₁, hm₁, hr⟩ := (hEq args hsafe).backward hm₂
  obtain ⟨⟨retVal₁, mem₁'⟩, rfl, hret⟩ := GapEqErr.ok_iff_right.mp hr
  dsimp only at hret
  subst hret
  obtain ⟨tr₁, hrr₁⟩ := mirGapBehaviors_ok_reachesRet hm₁
  exact hval₁ (tr₁, .normal (retVal₁, mem₁')) hrr₁ hp retVal₁ mem₁' rfl

/--
`Defined`-witnessed specialization of `mirContractHoldsWithSafetyAndCallees_of_contextEquiv`,
needing NO separate `hClosed` hypothesis (since `OutcomeSet.Defined` on `safetyPre`
already rules out `.unresolved` gaps on `safetyPre`).
-/
theorem mirContractHoldsWithSafetyAndCallees_of_contextEquiv_defined
    {callees : List CapturedMir} {body₁ body₂ : CapturedMir}
    {safetyPre pre : List Value → Prop} {post : List Value → Value → Prop}
    (hEq : ContextEquivOn safetyPre (fun r₁ r₂ : MirReturn => r₁.1 = r₂.1) (· = ·)
      (mirGapBehaviors MirCallEnv.unresolved callees body₁)
      (mirGapBehaviors MirCallEnv.unresolved callees body₂))
    (hDef₁ : ∀ args, safetyPre args →
      OutcomeSet.Defined ExecFault.isUB
        (mirGapBehaviors MirCallEnv.unresolved callees body₁ args))
    (hBase : Trusted.VerificationResult.MirContractHoldsWithSafetyAndCallees
      body₁ callees safetyPre pre post) :
    Trusted.VerificationResult.MirContractHoldsWithSafetyAndCallees
      body₂ callees safetyPre pre post :=
  mirContractHoldsWithSafetyAndCallees_of_contextEquiv hEq
    (fun args hs _ hm => hDef₁ args hs hm) hBase

/--
Transfer a kernel-audited `Trusted.VerificationResult.VerificationResult`
certificate from `body₁` to `body₂` along `ContextEquivOn pre` (even when both
bodies call unresolved external functions or unmodeled helpers outside `pre`!).
-/
theorem VerificationResult.of_contextEquiv
    {callees : List CapturedMir} {body₁ body₂ : CapturedMir}
    {pre : List Value → Prop} {post : List Value → Value → Prop}
    (hEq : ContextEquivOn pre (fun r₁ r₂ : MirReturn => r₁.1 = r₂.1) (· = ·)
      (mirGapBehaviors MirCallEnv.unresolved callees body₁)
      (mirGapBehaviors MirCallEnv.unresolved callees body₂))
    (hClosed : ∀ args, pre args → ∀ site,
      ¬ mirGapBehaviors MirCallEnv.unresolved callees body₁ args (.gap (.unresolved site)))
    (hCert : Trusted.VerificationResult.VerificationResult
      { body := body₁, pre := pre, post := post, callees := callees }) :
    Trusted.VerificationResult.VerificationResult
      { body := body₂, pre := pre, post := post, callees := callees } :=
  ⟨mirContractHoldsWithSafetyAndCallees_of_contextEquiv hEq hClosed hCert.proof⟩

/--
Transfer `Trusted.VerificationResult.MirStatefulContractHoldsWithSafetyAndCallees`
from `body₁` to `body₂` along a relational `ContextEquivOn` on
`mirStatefulGapBehaviors MirCallEnv.unresolved`, supporting custom return
relations `rVal` (e.g., value equality when `post` is independent of internal
borrow-tag metadata) and requiring `hClosed` only on `safetyPre`.
-/
theorem mirStatefulContractHoldsWithSafetyAndCallees_of_contextEquiv
    {callees : List CapturedMir} {body₁ body₂ : CapturedMir}
    {rVal : MirReturn → MirReturn → Prop}
    {safetyPre pre : List Value → Memory → Prop}
    {post : List Value → Memory → Value → Memory → Prop}
    (hEq : ContextEquivOn (fun q => safetyPre q.1 q.2) rVal (· = ·)
      (mirStatefulGapBehaviors MirCallEnv.unresolved callees body₁)
      (mirStatefulGapBehaviors MirCallEnv.unresolved callees body₂))
    (hPost : ∀ args mem v₁ m₁ v₂ m₂,
      safetyPre args mem → pre args mem →
      rVal (v₁, m₁) (v₂, m₂) → post args mem v₁ m₁ → post args mem v₂ m₂)
    (hClosed : ∀ args mem, safetyPre args mem → ∀ site,
      ¬ mirStatefulGapBehaviors MirCallEnv.unresolved callees body₁ (args, mem)
          (.gap (.unresolved site)))
    (hBase : Trusted.VerificationResult.MirStatefulContractHoldsWithSafetyAndCallees
      body₁ callees safetyPre pre post) :
    Trusted.VerificationResult.MirStatefulContractHoldsWithSafetyAndCallees
      body₂ callees safetyPre pre post := by
  intro args mem hsafe
  obtain ⟨hs₁, hval₁⟩ := hBase args mem hsafe
  let s₁ := Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body₁ args mem callees
  let s₂ := Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body₂ args mem callees
  have hDef₁ : OutcomeSet.Defined ExecFault.isUB
      (mirStatefulGapBehaviors MirCallEnv.unresolved callees body₁ (args, mem)) := by
    intro o ho
    obtain ⟨hne, fuel, hrun⟩ := ho
    cases o with
    | ok _ => exact trivial
    | fault e =>
      cases e with
      | ub => exact False.elim (not_mirTree_safe_of_run_undefined hrun (Or.inl rfl) hs₁)
      | panic => exact fun h => h
      | abort => exact fun h => h
    | gap g =>
      cases g with
      | unresolved site => exact False.elim (hClosed args mem hsafe site ⟨hne, fuel, hrun⟩)
      | outOfFuel => exact False.elim (hne rfl)
      | unsupported site =>
        exact False.elim (not_mirTree_safe_of_run_undefined hrun (Or.inr (Or.inl ⟨site, rfl⟩)) hs₁)
      | budget site =>
        exact False.elim (not_mirTree_safe_of_run_undefined hrun (Or.inr (Or.inr ⟨site, rfl⟩)) hs₁)
  have hDef₂ := ((hEq (args, mem) hsafe).defined_iff ExecFault.eq_preserves_isUB).mp hDef₁
  have hs₂ : TreeSafe (Trusted.VerificationResult.mirStatefulTreeWithCallees
      body₂ args mem callees) := by
    change TreeSafe (mirTree body₂ s₂)
    rw [← cofix_stepMirSiteState_eq_mirTree body₂ s₂]
    exact treeSafe_of_gapBehaviors_defined mirHandled_not_fault
      (mirGapHandle_ne_outOfFuel MirCallEnv.unresolved)
      mirGapHandle_unresolved_subsingleton
      (mirGapHandle_noDefFault MirCallEnv.unresolved) hDef₂
  refine ⟨hs₂, fun outPair hrr₂ hp retVal₂ mem₂' hout => ?_⟩
  rcases outPair with ⟨tr₂, out₂⟩
  dsimp only at hout
  subst hout
  have hm₂ : mirStatefulGapBehaviors MirCallEnv.unresolved callees body₂ (args, mem)
      (classifyOutcome (.normal (retVal₂, mem₂'))) := by
    change ReachesRet (mirTree body₂ s₂) tr₂ (.normal (retVal₂, mem₂')) at hrr₂
    rw [← cofix_stepMirSiteState_eq_mirTree body₂ s₂] at hrr₂
    exact (reachesRet_iff_gapBehaviors_of_defined mirHandled_not_fault
      (mirGapHandle_ne_outOfFuel MirCallEnv.unresolved)
      mirGapHandle_unresolved_subsingleton
      (mirGapHandle_noDefFault MirCallEnv.unresolved) hDef₂ _).mp ⟨tr₂, hrr₂⟩
  obtain ⟨o₁, hm₁, hr⟩ := (hEq (args, mem) hsafe).backward hm₂
  obtain ⟨⟨retVal₁, mem₁'⟩, rfl, hret⟩ := GapEqErr.ok_iff_right.mp hr
  obtain ⟨_, _, hrun₁⟩ := hm₁
  obtain ⟨tr₁, hrr₁⟩ := runMirStepsWithGap_ok_reachesRet hrun₁
  exact hPost args mem retVal₁ mem₁' retVal₂ mem₂' hsafe hp hret
    (hval₁ (tr₁, .normal (retVal₁, mem₁')) hrr₁ hp retVal₁ mem₁' rfl)

/--
Transfer a kernel-audited `Trusted.VerificationResult.StatefulVerificationResult`
certificate from `body₁` to `body₂` along a relational `ContextEquivOn` on
`mirStatefulGapBehaviors MirCallEnv.unresolved`.
-/
theorem StatefulVerificationResult.of_contextEquiv
    {callees : List CapturedMir} {body₁ body₂ : CapturedMir}
    {rVal : MirReturn → MirReturn → Prop}
    {pre : List Value → Memory → Prop}
    {post : List Value → Memory → Value → Memory → Prop}
    (hEq : ContextEquivOn (fun q => pre q.1 q.2) rVal (· = ·)
      (mirStatefulGapBehaviors MirCallEnv.unresolved callees body₁)
      (mirStatefulGapBehaviors MirCallEnv.unresolved callees body₂))
    (hPost : ∀ args mem v₁ m₁ v₂ m₂,
      pre args mem → rVal (v₁, m₁) (v₂, m₂) → post args mem v₁ m₁ → post args mem v₂ m₂)
    (hClosed : ∀ args mem, pre args mem → ∀ site,
      ¬ mirStatefulGapBehaviors MirCallEnv.unresolved callees body₁ (args, mem)
          (.gap (.unresolved site)))
    (hCert : Trusted.VerificationResult.StatefulVerificationResult
      { body := body₁, pre := pre, post := post, callees := callees }) :
    Trusted.VerificationResult.StatefulVerificationResult
      { body := body₂, pre := pre, post := post, callees := callees } :=
  ⟨mirStatefulContractHoldsWithSafetyAndCallees_of_contextEquiv hEq
    (fun args mem v₁ m₁ v₂ m₂ hp _ => hPost args mem v₁ m₁ v₂ m₂ hp) hClosed hCert.proof⟩

/--
Embed any `MirCallEnv` into a trusted `Trusted.VerificationResult.ExternalCallHandler`
over `MirClosedEffect = SumE MirFailE MirObsE`, sealing callee `.outOfFuel` and
mapping gaps and callee UB to the corresponding `MirFailE` nodes.
-/
def MirCallEnv.toExternalCallHandler (env : MirCallEnv) (req : MirCallReq) :
    ITree Trusted.VerificationResult.MirClosedEffect MirCallAns :=
  match env.seal req with
  | .ok ans => ITree.ret ans
  | .fault .ub => ITree.fail FailureKind.ub
  | .gap (.budget _) => ITree.fail FailureKind.outOfFuel
  | .gap _ => ITree.fail FailureKind.unsupported

private def mirExtInterp (env : MirCallEnv) (body : CapturedMir) (st : MirSiteState) :
    ITree Trusted.VerificationResult.MirClosedEffect MirOutcome :=
  ITree.interp
    (Trusted.VerificationResult.handleMirExternalCalls env.toExternalCallHandler)
    (ITree.cofix (stepMirSiteState body) st)

private theorem fail_bind_observe {F : Type} {E : Effect} [Subeffect (FailE F) E]
    {α R : Type} (fk : F) (g : α → ITree E R) :
    (ITree.fail fk >>= g).observe =
      .vis (Subeffect.injReq (Sub := FailE F) (FailReq.fail fk))
        (fun o => PEmpty.elim (Subeffect.projAns (Sub := FailE F) (FailReq.fail fk) o)) := by
  unfold ITree.fail ITree.triggerSub
  rw [Anneal.ITree.bind_assoc_itree, Anneal.ITree.vis_bind, ITree.observe_vis]
  congr
  funext o
  rw [Anneal.ITree.ret_bind]
  exact PEmpty.elim (Subeffect.projAns (Sub := FailE F) (FailReq.fail fk) o)

private theorem triggerSub_bind_observe {Sub E : Effect} [Subeffect Sub E]
    {R : Type} (i : Sub.I) (g : Sub.O i → ITree E R) :
    (ITree.triggerSub i >>= g).observe =
      .vis (Subeffect.injReq (Sub := Sub) i)
        (fun o => g (Subeffect.projAns (Sub := Sub) i o)) := by
  unfold ITree.triggerSub
  rw [Anneal.ITree.vis_bind, ITree.observe_vis]
  congr
  funext o
  exact Anneal.ITree.ret_bind _ g

private theorem emit_closed_bind_observe (obs : MirObs)
    (g : PUnit.{1} → ITree Trusted.VerificationResult.MirClosedEffect MirOutcome) :
    (ITree.emit (E := Trusted.VerificationResult.MirClosedEffect) obs >>= g).observe =
      .vis (Subeffect.injReq (Sub := ObsE MirObs)
        (Sup := Trusted.VerificationResult.MirClosedEffect) (ObsReq.emit obs)) g :=
  triggerSub_bind_observe (Sub := ObsE MirObs)
    (E := Trusted.VerificationResult.MirClosedEffect) (ObsReq.emit obs) g

private theorem mirExtInterp_step_next {env : MirCallEnv} {body : CapturedMir}
    {st st' : MirSiteState}
    (hn : mirSiteGapStep env body st = .next st') :
    (mirExtInterp env body st).observe = .tau (mirExtInterp env body st') ∨
      ∃ (obs : MirObs) (k : PUnit.{1} → MirSiteState),
        st' = k PUnit.unit ∧
        (mirExtInterp env body st).observe =
          .vis (Subeffect.injReq (Sub := ObsE MirObs)
            (Sup := Trusted.VerificationResult.MirClosedEffect) (ObsReq.emit obs))
            (fun u => .tau (mirExtInterp env body (k u))) := by
  dsimp only [mirSiteGapStep] at hn
  have hUnf : ITree.cofix (stepMirSiteState body) st =
      ITree.fold ((stepMirSiteState body st).map (ITree.cofix (stepMirSiteState body))) := by
    rw [← ITree.fold_observe (ITree.cofix (stepMirSiteState body) st), ITree.observe_cofix]
  cases hs : stepMirSiteState body st with
  | ret out => rw [gapStep_of_ret hs] at hn; cases hn
  | tau s' =>
    rw [gapStep_of_tau hs] at hn
    injection hn with hst'
    subst hst'
    left
    dsimp only [mirExtInterp]
    rw [hUnf, hs]
    change (ITree.interp _ (.tau (ITree.cofix (stepMirSiteState body) s'))).observe = _
    rw [Anneal.ITree.interp_tau, ITree.observe_tau]
  | vis idx k =>
    have hB0 : mirExtInterp env body st =
        (Trusted.VerificationResult.handleMirExternalCalls env.toExternalCallHandler idx >>=
          fun o => .tau (mirExtInterp env body (k o))) := by
      dsimp only [mirExtInterp]
      rw [hUnf, hs]
      exact Anneal.ITree.interp_vis _ idx _
    cases idx with
    | inl f =>
      cases f with
      | fail fk => rw [gapStep_of_fail hs] at hn; cases hn
    | inr rest =>
      cases rest with
      | inl obsReq =>
        cases obsReq with
        | emit obs =>
          rw [gapStep_of_vis hs] at hn
          injection hn with hst'
          right
          refine ⟨obs, k, hst'.symm, ?_⟩
          have hB1 : mirExtInterp env body st =
              (ITree.emit obs >>= fun o => .tau (mirExtInterp env body (k o))) := hB0
          clear hs hst' hB0
          rw [hB1]
          exact emit_closed_bind_observe obs (fun o => .tau (mirExtInterp env body (k o)))
      | inr callReq =>
        cases callReq with
        | call req =>
          rw [gapStep_of_vis hs] at hn
          have hEqH : mirGapHandle env (.inr (.call req)) =
              (env.seal req).mapFault (fun _ => .ub) := by
            dsimp only [mirGapHandle, MirCallEnv.seal]
            cases env req <;> rfl
          rw [hEqH] at hn
          have hB1 : mirExtInterp env body st =
              (env.toExternalCallHandler req >>=
                fun o => .tau (mirExtInterp env body (k o))) := hB0
          cases hseal : env.seal req with
          | ok ans =>
            rw [hseal] at hn
            injection hn with hst'
            subst hst'
            left
            have hH : env.toExternalCallHandler req = ITree.ret ans := by
              unfold MirCallEnv.toExternalCallHandler; rw [hseal]
            rw [hB1, hH, Anneal.ITree.ret_bind, ITree.observe_tau]
          | fault _ => rw [hseal] at hn; cases hn
          | gap _ => rw [hseal] at hn; cases hn

private theorem mirExtInterp_step_done {env : MirCallEnv} {body : CapturedMir}
    {st : MirSiteState} {o : OutcomeWithGap ExecFault (GapTag DefPath) MirReturn}
    (hd : mirSiteGapStep env body st = .done o) :
    (∃ out, o = classifyOutcome out ∧ (mirExtInterp env body st).observe = .ret out) ∨
      (¬ o.isDefined ExecFault.isUB ∧ o ≠ .gap .outOfFuel ∧
        ∃ fk, (mirExtInterp env body st).observe =
          .vis (Subeffect.injReq (Sub := FailE FailureKind)
            (Sup := Trusted.VerificationResult.MirClosedEffect) (FailReq.fail fk))
            PEmpty.elim) := by
  dsimp only [mirSiteGapStep] at hd
  have hUnf : ITree.cofix (stepMirSiteState body) st =
      ITree.fold ((stepMirSiteState body st).map (ITree.cofix (stepMirSiteState body))) := by
    rw [← ITree.fold_observe (ITree.cofix (stepMirSiteState body) st), ITree.observe_cofix]
  cases hs : stepMirSiteState body st with
  | ret out =>
    rw [gapStep_of_ret hs] at hd
    injection hd with ho
    left
    refine ⟨out, ho.symm, ?_⟩
    dsimp only [mirExtInterp]
    rw [hUnf, hs]
    change (ITree.interp _ (.ret out)).observe = _
    rw [Anneal.ITree.interp_ret, ITree.observe_ret]
  | tau _ => rw [gapStep_of_tau hs] at hd; cases hd
  | vis idx k =>
    have hB0 : mirExtInterp env body st =
        (Trusted.VerificationResult.handleMirExternalCalls env.toExternalCallHandler idx >>=
          fun x => .tau (mirExtInterp env body (k x))) := by
      dsimp only [mirExtInterp]
      rw [hUnf, hs]
      exact Anneal.ITree.interp_vis _ idx _
    cases idx with
    | inl f =>
      cases f with
      | fail fk =>
        rw [gapStep_of_fail hs] at hd
        injection hd with ho
        subst ho
        right
        refine ⟨?_, classifyFailure_ne_outOfFuel _ fk, fk, ?_⟩
        · cases fk with
          | ub => exact fun h => h trivial
          | unsupported => exact fun h => h
          | outOfFuel => exact fun h => h
        · have hB1 : mirExtInterp env body st =
              (ITree.fail fk >>= fun x => .tau (mirExtInterp env body (k x))) := hB0
          rw [hB1, fail_bind_observe]; rfl
    | inr rest =>
      cases rest with
      | inl obsReq =>
        cases obsReq with
        | emit _ => rw [gapStep_of_vis hs] at hd; cases hd
      | inr callReq =>
        cases callReq with
        | call req =>
          rw [gapStep_of_vis hs] at hd
          have hEqH : mirGapHandle env (.inr (.call req)) =
              (env.seal req).mapFault (fun _ => .ub) := by
            dsimp only [mirGapHandle, MirCallEnv.seal]
            cases env req <;> rfl
          rw [hEqH] at hd
          have hB1 : mirExtInterp env body st =
              (env.toExternalCallHandler req >>=
                fun x => .tau (mirExtInterp env body (k x))) := hB0
          have hCallFail : ∀ fk : FailureKind,
              env.toExternalCallHandler req = ITree.fail fk →
              (mirExtInterp env body st).observe =
                .vis (Subeffect.injReq (Sub := FailE FailureKind)
                  (Sup := Trusted.VerificationResult.MirClosedEffect) (FailReq.fail fk))
                  PEmpty.elim := by
            intro fk hH
            rw [hB1, hH, fail_bind_observe]; rfl
          cases hseal : env.seal req with
          | ok _ => rw [hseal] at hd; cases hd
          | fault f =>
            cases f with
            | ub =>
              rw [hseal] at hd
              injection hd with ho
              subst ho
              right
              exact ⟨fun h => h trivial, (fun h => by cases h), .ub,
                hCallFail .ub (by unfold MirCallEnv.toExternalCallHandler; rw [hseal])⟩
          | gap g =>
            cases g with
            | budget _ =>
              rw [hseal] at hd
              injection hd with ho
              subst ho
              right
              exact ⟨fun h => h, (fun h => by cases h), .outOfFuel,
                hCallFail .outOfFuel (by unfold MirCallEnv.toExternalCallHandler; rw [hseal])⟩
            | unsupported _ =>
              rw [hseal] at hd
              injection hd with ho
              subst ho
              right
              exact ⟨fun h => h, (fun h => by cases h), .unsupported,
                hCallFail .unsupported (by unfold MirCallEnv.toExternalCallHandler; rw [hseal])⟩
            | unresolved _ =>
              rw [hseal] at hd
              injection hd with ho
              subst ho
              right
              exact ⟨fun h => h, (fun h => by cases h), .unsupported,
                hCallFail .unsupported (by unfold MirCallEnv.toExternalCallHandler; rw [hseal])⟩
            | outOfFuel =>
              exact False.elim (MirCallEnv.isSealed_seal env req hseal)

private theorem reaches_mirExtInterp_of_defined {env : MirCallEnv} {body : CapturedMir}
    {t₀ u : ITree Trusted.VerificationResult.MirClosedEffect MirOutcome}
    {tr : List (Event Trusted.VerificationResult.MirClosedEffect)}
    (hreach : Reaches t₀ tr u)
    {st : MirSiteState}
    (ht₀ : t₀ = mirExtInterp env body st ∨ t₀ = .tau (mirExtInterp env body st))
    (hDef : OutcomeSet.Defined ExecFault.isUB (gapBehaviors (mirSiteGapStep env body) st)) :
    ∃ st',
      (u = mirExtInterp env body st' ∨ u = .tau (mirExtInterp env body st')) ∧
      OutcomeSet.Defined ExecFault.isUB (gapBehaviors (mirSiteGapStep env body) st') ∧
      ∀ o, gapBehaviors (mirSiteGapStep env body) st' o →
        gapBehaviors (mirSiteGapStep env body) st o := by
  induction hreach generalizing st with
  | refl => exact ⟨st, ht₀, hDef, fun _ ho => ho⟩
  | @tau x x' _ _ htau _ ih =>
    rcases ht₀ with rfl | rfl
    · cases hm : mirSiteGapStep env body st with
      | done o =>
        rcases mirExtInterp_step_done hm with ⟨_, _, hret⟩ | ⟨_, _, _, hfail⟩
        · rw [hret] at htau; cases htau
        · rw [hfail] at htau; cases htau
      | next st' =>
        rcases mirExtInterp_step_next hm with htau' | ⟨_, _, _, hvis⟩
        · rw [htau'] at htau
          injection htau with hx'
          have hback : ∀ o, gapBehaviors (mirSiteGapStep env body) st' o →
              gapBehaviors (mirSiteGapStep env body) st o :=
            fun o ho => (gapBehaviors_reach_iff _ (.step hm (.refl st')) o).mpr ho
          obtain ⟨st'', hu, hDef'', hb''⟩ := ih (Or.inl hx'.symm) (fun _ ho => hDef (hback _ ho))
          exact ⟨st'', hu, hDef'', fun o ho => hback o (hb'' o ho)⟩
        · rw [hvis] at htau; cases htau
    · rw [ITree.observe_tau] at htau
      injection htau with hx'
      exact ih (Or.inl hx'.symm) hDef
  | @vis x _ idx c _ hv hnf o' _ ih =>
    rcases ht₀ with rfl | rfl
    · cases hm : mirSiteGapStep env body st with
      | done o =>
        rcases mirExtInterp_step_done hm with ⟨_, _, hret⟩ | ⟨_, _, fk, hfail⟩
        · rw [hret] at hv; cases hv
        · rw [hfail] at hv
          injection hv with hij _
          subst hij
          exact False.elim (hnf trivial)
      | next st' =>
        rcases mirExtInterp_step_next hm with htau' | ⟨obs, k, hst', hvis⟩
        · rw [htau'] at hv; cases hv
        · rw [hvis] at hv
          injection hv with hij hcj
          subst hij
          cases eq_of_heq hcj
          cases (o' : PUnit.{1})
          subst hst'
          have hback : ∀ o, gapBehaviors (mirSiteGapStep env body) (k PUnit.unit) o →
              gapBehaviors (mirSiteGapStep env body) st o :=
            fun o ho => (gapBehaviors_reach_iff _ (.step hm (.refl _)) o).mpr ho
          obtain ⟨st'', hu, hDef'', hb''⟩ := ih (Or.inr rfl) (fun _ ho => hDef (hback _ ho))
          exact ⟨st'', hu, hDef'', fun o ho => hback o (hb'' o ho)⟩
    · rw [ITree.observe_tau] at hv; cases hv

private theorem mirExtInterp_of_run {env : MirCallEnv} {body : CapturedMir}
    {fuel : Nat} {st : MirSiteState} {o : OutcomeWithGap ExecFault (GapTag DefPath) MirReturn}
    (hrun : runGapSteps (mirSiteGapStep env body) fuel st = o)
    (hne : o ≠ .gap .outOfFuel) :
    (¬ o.isDefined ExecFault.isUB → ¬ TreeSafe (mirExtInterp env body st)) ∧
      (∀ out, o = classifyOutcome out → ∃ tr, ReachesRet (mirExtInterp env body st) tr out) := by
  induction fuel generalizing st with
  | zero => exact False.elim (hne hrun.symm)
  | succ n ih =>
    rw [runGapSteps_succ] at hrun
    cases hm : mirSiteGapStep env body st with
    | done o' =>
      rw [hm] at hrun
      dsimp only at hrun
      subst hrun
      rcases mirExtInterp_step_done hm with ⟨out', rfl, hret⟩ | ⟨hnd, _, fk, hfail⟩
      · refine ⟨fun hd => False.elim (hd (classifyOutcome_isDefined out')), fun out heq => ?_⟩
        cases classifyOutcome_injective heq
        exact ⟨[], _, .refl _, hret⟩
      · exact ⟨fun _ hsafe => hsafe [] _ (.refl _) ⟨_, _, _, .refl _, hfail, trivial⟩,
          fun out heq => False.elim (hnd (by rw [heq]; exact classifyOutcome_isDefined out))⟩
    | next st' =>
      rw [hm] at hrun
      obtain ⟨ihUndef, ihRet⟩ := ih hrun
      rcases mirExtInterp_step_next hm with htau | ⟨obs, k, rfl, hvis⟩
      · refine ⟨fun hnd hsafe => ihUndef hnd (fun tr u hr => hsafe tr u (.tau htau hr)),
          fun out heq => ?_⟩
        obtain ⟨tr, u, hr, hu⟩ := ihRet out heq
        exact ⟨tr, u, .tau htau hr, hu⟩
      · refine ⟨fun hnd hsafe => ihUndef hnd (fun tr u hr =>
            hsafe _ u (.vis hvis (fun h => h) PUnit.unit (.tau (ITree.observe_tau _) hr))),
          fun out heq => ?_⟩
        obtain ⟨tr, u, hr, hu⟩ := ihRet out heq
        exact ⟨_, u, .vis hvis (fun h => h) PUnit.unit (.tau (ITree.observe_tau _) hr), hu⟩

/--
Open-world `TreeSafe ↔ Defined` adequacy for **every** `env : MirCallEnv` (with
ZERO `hClosed` side condition!): `mirHandledTreeWithCallees` under
`env.toExternalCallHandler` is `TreeSafe` if and only if `mirStatefulGapBehaviors`
is `OutcomeSet.Defined ExecFault.isUB`.
-/
theorem mirHandledTree_safe_iff_defined (env : MirCallEnv)
    (callees : List CapturedMir) (body : CapturedMir) (args : List Value) (mem : Memory) :
    TreeSafe (Trusted.VerificationResult.mirHandledTreeWithCallees
        body args mem callees env.toExternalCallHandler) ↔
      OutcomeSet.Defined ExecFault.isUB
        (mirStatefulGapBehaviors env callees body (args, mem)) := by
  let s₀ := Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem callees
  have hTree : Trusted.VerificationResult.mirHandledTreeWithCallees
      body args mem callees env.toExternalCallHandler =
      mirExtInterp env body (mirSiteOfExec body (.running s₀)) := by
    dsimp only [Trusted.VerificationResult.mirHandledTreeWithCallees, mirExtInterp]
    rw [cofix_stepMirSiteState_eq_mirTree]
    rfl
  rw [hTree]
  refine ⟨fun hSafe o ho => ?_, fun hDef tr u hreach hfn => ?_⟩
  · obtain ⟨hne, fuel, hrun⟩ := ho
    have hImp := (mirExtInterp_of_run hrun hne).1
    cases o with
    | ok _ => exact trivial
    | fault e =>
      cases e with
      | ub => exact False.elim (hImp (fun h => h trivial) hSafe)
      | panic => exact fun h => h
      | abort => exact fun h => h
    | gap _ => exact False.elim (hImp (fun h => h) hSafe)
  · obtain ⟨u', idx, c, hts, hvu', hfi⟩ := hfn
    obtain ⟨st', hu', hDef', _⟩ :=
      reaches_mirExtInterp_of_defined (reaches_append_tauStar hreach hts) (Or.inl rfl) hDef
    rcases hu' with rfl | rfl
    · cases hm : mirSiteGapStep env body st' with
      | done o =>
        rcases mirExtInterp_step_done hm with ⟨_, _, hret⟩ | ⟨hnd, hne, _, _⟩
        · rw [hret] at hvu'; cases hvu'
        · exact hnd (hDef' ⟨hne, 1, runGapSteps_succ_of_done _ hm 0⟩)
      | next _ =>
        rcases mirExtInterp_step_next hm with htau | ⟨_, _, _, hvis⟩
        · rw [htau] at hvu'; cases hvu'
        · rw [hvis] at hvu'
          injection hvu' with hij _
          subst hij
          exact hfi
    · rw [ITree.observe_tau] at hvu'; cases hvu'

/--
Open-world return characterization for **every** `env : MirCallEnv`: under
`OutcomeSet.Defined`, `mirHandledTreeWithCallees` returns `out` along some trace
iff `mirStatefulGapBehaviors` contains `classifyOutcome out`.
-/
theorem mirHandledTree_reachesRet_iff_of_defined {env : MirCallEnv}
    {callees : List CapturedMir} {body : CapturedMir} {args : List Value} {mem : Memory}
    (hDef : OutcomeSet.Defined ExecFault.isUB
      (mirStatefulGapBehaviors env callees body (args, mem)))
    (out : MirOutcome) :
    (∃ tr, ReachesRet (Trusted.VerificationResult.mirHandledTreeWithCallees
        body args mem callees env.toExternalCallHandler) tr out) ↔
      mirStatefulGapBehaviors env callees body (args, mem) (classifyOutcome out) := by
  let s₀ := Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem callees
  have hTree : Trusted.VerificationResult.mirHandledTreeWithCallees
      body args mem callees env.toExternalCallHandler =
      mirExtInterp env body (mirSiteOfExec body (.running s₀)) := by
    dsimp only [Trusted.VerificationResult.mirHandledTreeWithCallees, mirExtInterp]
    rw [cofix_stepMirSiteState_eq_mirTree]
    rfl
  rw [hTree]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨tr, u, hreach, hu⟩ := h
    obtain ⟨st', hu', hDef', hback⟩ :=
      reaches_mirExtInterp_of_defined hreach (Or.inl rfl) hDef
    rcases hu' with rfl | rfl
    · cases hm : mirSiteGapStep env body st' with
      | done o =>
        rcases mirExtInterp_step_done hm with ⟨out', rfl, hret⟩ | ⟨hnd, hne, _, _⟩
        · rw [hret] at hu
          injection hu with heq
          subst heq
          exact hback _ ⟨classifyOutcome_ne_outOfFuel out', 1, runGapSteps_succ_of_done _ hm 0⟩
        · exact False.elim (hnd (hDef' ⟨hne, 1, runGapSteps_succ_of_done _ hm 0⟩))
      | next _ =>
        rcases mirExtInterp_step_next hm with htau | ⟨_, _, _, hvis⟩
        · rw [htau] at hu; cases hu
        · rw [hvis] at hu; cases hu
    · rw [ITree.observe_tau] at hu; cases hu
  · obtain ⟨hne, fuel, hrun⟩ := h
    exact (mirExtInterp_of_run hrun hne).2 out rfl

/-- Trace-erased Layer 1A semantics of open-world `mirHandledTreeWithCallees`. -/
def mirHandledTraceErasedSem (env : MirCallEnv) (callees : List CapturedMir) :
    Semantics CapturedMir (List Value × Memory → Partial (BehaviorSet MirOutcome)) :=
  fun body q =>
    Partial.map (BehaviorSet.map Prod.snd)
      (Trusted.VerificationResult.mirHandledTreeWithCallees
        body q.1 q.2 callees env.toExternalCallHandler).toPartial

/--
Unconditional open-world `toPartial` equality on `mirHandledTreeWithCallees` for
**every** `env : MirCallEnv` (requiring NO `hClosed` and NO `hDef₁` hypothesis,
covering defined returns, panics, aborts, diverging loops, UB, `.unsupported`,
`.budget`, and `.unresolved` gaps alike!).
-/
theorem mirContextEquivOn_mirHandledTree_toPartial_eq {env : MirCallEnv}
    {callees : List CapturedMir} {body₁ body₂ : CapturedMir}
    {pre : List Value × Memory → Prop}
    (hEq : ContextEquivOn pre (· = ·) (· = ·)
      (mirStatefulGapBehaviors env callees body₁)
      (mirStatefulGapBehaviors env callees body₂))
    {q : List Value × Memory} (hpre : pre q) :
    mirHandledTraceErasedSem env callees body₁ q =
      mirHandledTraceErasedSem env callees body₂ q := by
  have hSafeIff :
      TreeSafe (Trusted.VerificationResult.mirHandledTreeWithCallees
          body₁ q.1 q.2 callees env.toExternalCallHandler) ↔
        TreeSafe (Trusted.VerificationResult.mirHandledTreeWithCallees
          body₂ q.1 q.2 callees env.toExternalCallHandler) := by
    rw [mirHandledTree_safe_iff_defined, mirHandledTree_safe_iff_defined]
    exact (hEq q hpre).defined_iff ExecFault.eq_preserves_isUB
  refine Partial.ext hSafeIff (fun h₁ h₂ => ?_)
  have hDef₁ := (mirHandledTree_safe_iff_defined env callees body₁ q.1 q.2).mp h₁
  have hDef₂ := (mirHandledTree_safe_iff_defined env callees body₂ q.1 q.2).mp h₂
  funext out
  apply propext
  refine ⟨fun hm₁ => ?_, fun hm₂ => ?_⟩
  · obtain ⟨⟨tr₁, out'⟩, hrr₁, rfl⟩ := hm₁
    have hg₁ := (mirHandledTree_reachesRet_iff_of_defined hDef₁ out').mp ⟨tr₁, hrr₁⟩
    have hg₂ := (hEq q hpre).subset_of_eq (classifyOutcome out') hg₁
    obtain ⟨tr₂, hrr₂⟩ := (mirHandledTree_reachesRet_iff_of_defined hDef₂ out').mpr hg₂
    exact ⟨(tr₂, out'), hrr₂, rfl⟩
  · obtain ⟨⟨tr₂, out'⟩, hrr₂, rfl⟩ := hm₂
    have hg₂ := (mirHandledTree_reachesRet_iff_of_defined hDef₂ out').mp ⟨tr₂, hrr₂⟩
    have hg₁ := (hEq q hpre).superset_of_eq (classifyOutcome out') hg₂
    obtain ⟨tr₁, hrr₁⟩ := (mirHandledTree_reachesRet_iff_of_defined hDef₁ out').mpr hg₁
    exact ⟨(tr₁, out'), hrr₁, rfl⟩

/--
Query-scoped open-world `ExactPass` on `mirHandledTraceErasedSem` for **every**
`env : MirCallEnv` (with zero `hClosed` side condition!).
-/
theorem mirContextEquivOn_mirHandledTree_exactPass {env : MirCallEnv}
    {callees : List CapturedMir} {body₁ body₂ : CapturedMir}
    {pre : List Value × Memory → Prop}
    (hEq : ContextEquivOn pre (· = ·) (· = ·)
      (mirStatefulGapBehaviors env callees body₁)
      (mirStatefulGapBehaviors env callees body₂)) :
    ExactPass
      (fun b (q : { q : List Value × Memory // pre q }) =>
        mirHandledTraceErasedSem env callees b q.1)
      (fun b (q : { q : List Value × Memory // pre q }) =>
        mirHandledTraceErasedSem env callees b q.1)
      id id body₁ body₂ where
  up_refines _ q := by
    dsimp only [id]
    rw [mirContextEquivOn_mirHandledTree_toPartial_eq hEq q.2]
    exact fun h => ⟨h, fun _ hx => hx⟩
  down_refines _ q := by
    dsimp only [id]
    rw [mirContextEquivOn_mirHandledTree_toPartial_eq hEq q.2]
    exact fun h => ⟨h, fun _ hx => hx⟩

/--
Unconditional full-domain `ExactPass` on `mirHandledTraceErasedSem` for **every**
`env : MirCallEnv` (with zero `hClosed` side condition!).
-/
theorem mirContextEquiv_mirHandledTree_exactPass {env : MirCallEnv}
    {callees : List CapturedMir} {body₁ body₂ : CapturedMir}
    (hEq : ContextEquiv (· = ·) (· = ·)
      (mirStatefulGapBehaviors env callees body₁)
      (mirStatefulGapBehaviors env callees body₂)) :
    ExactPass (mirHandledTraceErasedSem env callees)
      (mirHandledTraceErasedSem env callees) id id body₁ body₂ where
  up_refines _ q := by
    dsimp only [id]
    rw [mirContextEquivOn_mirHandledTree_toPartial_eq (pre := fun _ => True)
      (fun a _ => hEq a) trivial]
    exact fun h => ⟨h, fun _ hx => hx⟩
  down_refines _ q := by
    dsimp only [id]
    rw [mirContextEquivOn_mirHandledTree_toPartial_eq (pre := fun _ => True)
      (fun a _ => hEq a) trivial]
    exact fun h => ⟨h, fun _ hx => hx⟩

/--
Open-world relational contract transfer on `mirHandledTreeWithCallees` for
**every** `env : MirCallEnv` (requiring ZERO `hClosed` and allowing custom
return relations `rVal`, e.g., `r₁.1 = r₂.1` when a refactored body introduces
local borrows that change post-return memory metadata!).
-/
theorem mirClosedStatefulContract_of_contextEquiv {env : MirCallEnv}
    {callees : List CapturedMir} {body₁ body₂ : CapturedMir}
    {rVal : MirReturn → MirReturn → Prop}
    {safetyPre pre : List Value → Memory → Prop}
    {post : List Value → Memory → Value → Memory → Prop}
    (hEq : ContextEquivOn (fun q => safetyPre q.1 q.2) rVal (· = ·)
      (mirStatefulGapBehaviors env callees body₁)
      (mirStatefulGapBehaviors env callees body₂))
    (hPost : ∀ args mem v₁ m₁ v₂ m₂,
      safetyPre args mem → pre args mem →
      rVal (v₁, m₁) (v₂, m₂) → post args mem v₁ m₁ → post args mem v₂ m₂)
    (hBase :
      (fun args mem =>
        (Trusted.VerificationResult.mirHandledTreeWithCallees
          body₁ args mem callees env.toExternalCallHandler).toPartial) ≤
        Trusted.VerificationResult.MirClosedStatefulContractSpec safetyPre pre post) :
    (fun args mem =>
      (Trusted.VerificationResult.mirHandledTreeWithCallees
        body₂ args mem callees env.toExternalCallHandler).toPartial) ≤
      Trusted.VerificationResult.MirClosedStatefulContractSpec safetyPre pre post := by
  intro args mem hsafe
  obtain ⟨hs₁, hval₁⟩ := hBase args mem hsafe
  have hDef₁ := (mirHandledTree_safe_iff_defined env callees body₁ args mem).mp hs₁
  have hDef₂ := ((hEq (args, mem) hsafe).defined_iff ExecFault.eq_preserves_isUB).mp hDef₁
  have hs₂ := (mirHandledTree_safe_iff_defined env callees body₂ args mem).mpr hDef₂
  refine ⟨hs₂, fun outPair hrr₂ hp retVal₂ mem₂' hout => ?_⟩
  rcases outPair with ⟨tr₂, out₂⟩
  dsimp only at hout
  subst hout
  have hm₂ :=
    (mirHandledTree_reachesRet_iff_of_defined hDef₂ (.normal (retVal₂, mem₂'))).mp ⟨tr₂, hrr₂⟩
  obtain ⟨o₁, hm₁, hr⟩ := (hEq (args, mem) hsafe).backward hm₂
  obtain ⟨⟨retVal₁, mem₁'⟩, rfl, hret⟩ := GapEqErr.ok_iff_right.mp hr
  obtain ⟨tr₁, hrr₁⟩ :=
    (mirHandledTree_reachesRet_iff_of_defined hDef₁ (.normal (retVal₁, mem₁'))).mpr hm₁
  exact hPost args mem retVal₁ mem₁' retVal₂ mem₂' hsafe hp hret
    (hval₁ (tr₁, .normal (retVal₁, mem₁')) hrr₁ hp retVal₁ mem₁' rfl)

/--
Transfer a kernel-audited `Trusted.VerificationResult.ModularVerificationResult`
certificate from `body₁` to `body₂` whenever every external call handler
admitted by `envAssumed` is realized by a `MirCallEnv` under which `body₁` and
`body₂` are `ContextEquivOn` `pre` (supporting custom `rVal` such as return-value
equality across distinct borrow histories, with ZERO `hClosed` side condition!).
-/
theorem ModularVerificationResult.of_contextEquiv
    {callees : List CapturedMir} {body₁ body₂ : CapturedMir}
    {envAssumed : Trusted.VerificationResult.ExternalCallHandler → Prop}
    {rVal : MirReturn → MirReturn → Prop}
    {pre : List Value → Memory → Prop}
    {post : List Value → Memory → Value → Memory → Prop}
    (hHandlers : ∀ h, envAssumed h →
      ∃ env : MirCallEnv, h = env.toExternalCallHandler ∧
        ContextEquivOn (fun q => pre q.1 q.2) rVal (· = ·)
          (mirStatefulGapBehaviors env callees body₁)
          (mirStatefulGapBehaviors env callees body₂))
    (hPost : ∀ args mem v₁ m₁ v₂ m₂,
      pre args mem → rVal (v₁, m₁) (v₂, m₂) → post args mem v₁ m₁ → post args mem v₂ m₂)
    (hCert : Trusted.VerificationResult.ModularVerificationResult
      { body := body₁, envAssumed := envAssumed, pre := pre, post := post, callees := callees }) :
    Trusted.VerificationResult.ModularVerificationResult
      { body := body₂, envAssumed := envAssumed, pre := pre, post := post, callees := callees } :=
  ⟨fun h hAss => by
    obtain ⟨env, rfl, hEq⟩ := hHandlers h hAss
    exact mirClosedStatefulContract_of_contextEquiv hEq
      (fun args mem v₁ m₁ v₂ m₂ hp _ => hPost args mem v₁ m₁ v₂ m₂ hp)
      (hCert.proof env.toExternalCallHandler hAss)⟩

end MirAdequacy

end Anneal.Pass
