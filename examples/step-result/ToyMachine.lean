import Trusted
import Anneal.Refinement
import Anneal.Effect
import Anneal.ITree
import Anneal.Pass

/-!
Illustrative interaction-tree machines, cross-effect coinductive `WeakObsRef`
refinement, and Y-diagram composition (`#100`, `#103`).

1. `srcMachine` executes `SrcProg` over
   `SrcEffect := SumE (FailE FailureKind) (SumE (ObsE Nat) (PickE Bool))`.
2. `tgtMachine` executes deterministic `TgtProg` over the narrower effect
   `TgtEffect := SumE (FailE FailureKind) (ObsE Nat)`, where `compileProg`
   lowers demonic `PickE Bool` choices into silent `.tau` transitions.
3. `src_to_tgt_weakObsRef` proves cross-effect `WeakObsRef` via
   `WeakObsRef.coinduct`, yielding both `CompilerPass` (`compileProgPass`) and
   Layer 1A `Compiles` (`compileProgCompiles`).
4. `example_machine_compiled_correct` combines `compileProgPass` with a
   `VerifierPass` via `anneal_is_correct`.
-/

namespace ToyMachine

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Anneal.Refinement
open Anneal.Effect
open Anneal.ITree
open Anneal.Pass

/-- Source machine effect: faults, `Nat` observations, and demonic `Bool` choice. -/
abbrev SrcEffect : Effect.{0} :=
  SumE (FailE FailureKind) (SumE (ObsE Nat) (PickE Bool))

/-- Deterministic target effect with demonic `PickE Bool` erased. -/
abbrev TgtEffect : Effect.{0} :=
  SumE (FailE FailureKind) (ObsE Nat)

/-- Observation filter for `SrcEffect` projecting `ObsE Nat` events. -/
def srcProj : EffectObs SrcEffect Nat :=
  (EffectObs.erase (FailE FailureKind) Nat).sum
    ((EffectObs.emit Nat).sum (EffectObs.erase (PickE Bool) Nat))

/-- Observation filter for `TgtEffect` projecting `ObsE Nat` events. -/
def tgtProj : EffectObs TgtEffect Nat :=
  (EffectObs.erase (FailE FailureKind) Nat).sum (EffectObs.emit Nat)

/-- Source program syntax for the toy interaction-tree machine. -/
inductive SrcProg : Type where
  | stepEmit (tick : Nat) (rest : SrcProg)
  | demonicIf (onTrue onFalse : SrcProg)
  | divReturn (num den : Nat)
  | panicNow
  | loopForever (tick : Nat)

/-- One-step `ITreeF` coalgebra transition for `SrcProg`. -/
def srcStepFn (_prog : SrcProg) : SrcProg → ITreeF SrcEffect (Outcome Nat) SrcProg
  | .stepEmit tick rest => .vis (.inr (.inl (.emit tick))) (fun _ => rest)
  | .demonicIf onTrue onFalse =>
    .vis (.inr (.inr .pick)) (fun b : Bool => if b then onTrue else onFalse)
  | .divReturn _ 0 => .vis (.inl (.fail .ub)) PEmpty.elim
  | .divReturn num (d + 1) => .ret (.normal (num / (d + 1)))
  | .panicNow => .ret .panic
  | .loopForever tick =>
    .vis (.inr (.inl (.emit tick))) (fun _ => .loopForever tick)

def srcMachine : ITreeMachine SrcProg SrcProg SrcEffect (Outcome Nat) where
  init p := p
  step := srcStepFn

/-- Every source program admits at least the safe initial running prefix. -/
theorem srcMachine_non_vacuous (p : SrcProg) :
    ∃ pref : ObsPrefix Nat (Outcome Nat),
      pref.outcome.isSafe ∧ MachineSemantics srcMachine srcProj p pref :=
  exists_safe_obsPrefix srcProj (srcMachine.run p)

/-- Deterministic target program syntax produced by lowering `SrcProg`. -/
inductive TgtProg : Type where
  | stepEmit (tick : Nat) (rest : TgtProg)
  | tauStep (rest : TgtProg)
  | divReturn (num den : Nat)
  | panicNow
  | loopForever (tick : Nat)

/-- One-step deterministic `ITreeF` coalgebra transition for `TgtProg`. -/
def tgtStepFn (_prog : TgtProg) : TgtProg → ITreeF TgtEffect (Outcome Nat) TgtProg
  | .stepEmit tick rest => .vis (.inr (.emit tick)) (fun _ => rest)
  | .tauStep rest => .tau rest
  | .divReturn _ 0 => .vis (.inl (.fail .ub)) PEmpty.elim
  | .divReturn num (d + 1) => .ret (.normal (num / (d + 1)))
  | .panicNow => .ret .panic
  | .loopForever tick => .vis (.inr (.emit tick)) (fun _ => .loopForever tick)

def tgtMachine : ITreeMachine TgtProg TgtProg TgtEffect (Outcome Nat) where
  init q := q
  step := tgtStepFn

/-- Lower `SrcProg` to `TgtProg` by resolving `demonicIf` to `true` via `.tauStep`. -/
def compileProg : SrcProg → TgtProg
  | .stepEmit tick rest => .stepEmit tick (compileProg rest)
  | .demonicIf onTrue _ => .tauStep (compileProg onTrue)
  | .divReturn num den => .divReturn num den
  | .panicNow => .panicNow
  | .loopForever tick => .loopForever tick

private theorem observe_srcTree (p s : SrcProg) :
    (srcMachine.tree p s).observe = (srcStepFn p s).map (srcMachine.tree p) :=
  ITree.observe_cofix (srcStepFn p) s

private theorem observe_tgtTree (q s : TgtProg) :
    (tgtMachine.tree q s).observe = (tgtStepFn q s).map (tgtMachine.tree q) :=
  ITree.observe_cofix (tgtStepFn q) s

private theorem tgt_nonTau_sim
    {p : SrcProg} {q : TgtProg} :
    (s : SrcProg) → ∀ {a' : ITree TgtEffect (Outcome Nat)},
      TauStar (tgtMachine.tree q (compileProg s)) a' →
      TreeSafe (srcMachine.tree p s) →
      (∀ z, a'.observe ≠ .tau z) →
      ∃ tr₂ s',
        Reaches (srcMachine.tree p s) tr₂ (srcMachine.tree p s') ∧
        tr₂.filterMap srcProj.obsOf = [] ∧
        a' = tgtMachine.tree q (compileProg s') ∧
        ∀ z, (tgtMachine.tree q (compileProg s')).observe ≠ .tau z
  | .demonicIf onTrue onFalse, a', hs, hsafe, hnt => by
    have h_tgt : (tgtMachine.tree q (compileProg (.demonicIf onTrue onFalse))).observe =
        .tau (tgtMachine.tree q (compileProg onTrue)) := by
      rw [observe_tgtTree]; rfl
    have h_src : (srcMachine.tree p (.demonicIf onTrue onFalse)).observe =
        .vis (.inr (.inr .pick))
          (fun b : Bool => srcMachine.tree p (if b then onTrue else onFalse)) := by
      rw [observe_srcTree]; rfl
    cases hs with
    | refl => exact False.elim (hnt _ h_tgt)
    | step hx hrest =>
      rw [h_tgt] at hx; injection hx with hxx; subst hxx
      have hreach₁ :
          Reaches (srcMachine.tree p (.demonicIf onTrue onFalse))
            [⟨.inr (.inr .pick), true⟩] (srcMachine.tree p onTrue) :=
        .vis h_src (fun hf => hf) true (.refl _)
      obtain ⟨tr₂, s', hr₂, htr₂, ha', hnt'⟩ :=
        tgt_nonTau_sim onTrue hrest (treeSafe_residual hsafe hreach₁) hnt
      refine ⟨⟨.inr (.inr .pick), true⟩ :: tr₂, s',
        reaches_trans hreach₁ hr₂, ?_, ha', hnt'⟩
      simpa [List.filterMap, srcProj, EffectObs.sum, EffectObs.erase] using htr₂
  | .stepEmit tick rest, a', hs, _, _ => by
    have h_tgt : (tgtMachine.tree q (compileProg (.stepEmit tick rest))).observe =
        .vis (.inr (.emit tick)) (fun _ => tgtMachine.tree q (compileProg rest)) := by
      simp only [compileProg]; rw [observe_tgtTree]; rfl
    cases hs with
    | refl =>
      exact ⟨[], .stepEmit tick rest, .refl _, rfl, rfl,
        fun _ hw => by rw [h_tgt] at hw; nomatch hw⟩
    | step hx => rw [h_tgt] at hx; nomatch hx
  | .divReturn num 0, _, _, hsafe, _ => by
    have h_ub : (srcMachine.tree p (.divReturn num 0)).observe =
        .vis (.inl (.fail .ub)) (fun o => srcMachine.tree p (PEmpty.elim o)) := by
      rw [observe_srcTree]; rfl
    exact False.elim (hsafe [] _ (.refl _) ⟨_, _, _, .refl _, h_ub, trivial⟩)
  | .divReturn num (d + 1), a', hs, _, _ => by
    have h_tgt : (tgtMachine.tree q (compileProg (.divReturn num (d + 1)))).observe =
        .ret (.normal (num / (d + 1))) := by
      simp only [compileProg]; rw [observe_tgtTree]; rfl
    cases hs with
    | refl =>
      exact ⟨[], .divReturn num (d + 1), .refl _, rfl, rfl,
        fun _ hw => by rw [h_tgt] at hw; nomatch hw⟩
    | step hx => rw [h_tgt] at hx; nomatch hx
  | .panicNow, a', hs, _, _ => by
    have h_tgt : (tgtMachine.tree q (compileProg .panicNow)).observe = .ret .panic := by
      simp only [compileProg]; rw [observe_tgtTree]; rfl
    cases hs with
    | refl =>
      exact ⟨[], .panicNow, .refl _, rfl, rfl,
        fun _ hw => by rw [h_tgt] at hw; nomatch hw⟩
    | step hx => rw [h_tgt] at hx; nomatch hx
  | .loopForever tick, a', hs, _, _ => by
    have h_tgt : (tgtMachine.tree q (compileProg (.loopForever tick))).observe =
        .vis (.inr (.emit tick)) (fun _ => tgtMachine.tree q (.loopForever tick)) := by
      simp only [compileProg]; rw [observe_tgtTree]; rfl
    cases hs with
    | refl =>
      exact ⟨[], .loopForever tick, .refl _, rfl, rfl,
        fun _ hw => by rw [h_tgt] at hw; nomatch hw⟩
    | step hx => rw [h_tgt] at hx; nomatch hx

/-- Cross-effect coinductive `WeakObsRef` from `tgtMachine` to `srcMachine`. -/
theorem src_to_tgt_weakObsRef (p : SrcProg) :
    WeakObsRef tgtProj srcProj
      (tgtMachine.run (compileProg p)) (srcMachine.run p) := by
  refine WeakObsRef.coinduct tgtProj srcProj
    (fun a b => ∃ s : SrcProg,
      a = tgtMachine.tree (compileProg p) (compileProg s) ∧
      b = srcMachine.tree p s)
    ?_ _ _ ⟨p, rfl, rfl⟩
  rintro a b ⟨s, rfl, rfl⟩ hsafe
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a', i₁, k₁, hs, hv, hf⟩
    obtain ⟨tr₂, s', hr₂, _, rfl, _⟩ :=
      tgt_nonTau_sim s hs hsafe (fun _ hw => by rw [hv] at hw; nomatch hw)
    cases s' with
    | stepEmit _ _ =>
      simp only [compileProg] at hv; rw [observe_tgtTree] at hv
      injection hv with hi _; subst hi; exact hf
    | loopForever _ =>
      simp only [compileProg] at hv; rw [observe_tgtTree] at hv
      injection hv with hi _; subst hi; exact hf
    | demonicIf _ _ =>
      simp only [compileProg] at hv; rw [observe_tgtTree] at hv; nomatch hv
    | divReturn num den =>
      cases den with
      | zero =>
        have h_ub : (srcMachine.tree p (.divReturn num 0)).observe =
            .vis (.inl (.fail .ub)) (fun o => srcMachine.tree p (PEmpty.elim o)) := by
          rw [observe_srcTree]; rfl
        exact hsafe tr₂ _ hr₂ ⟨_, _, _, .refl _, h_ub, trivial⟩
      | succ d =>
        simp only [compileProg] at hv; rw [observe_tgtTree] at hv; nomatch hv
    | panicNow =>
      simp only [compileProg] at hv; rw [observe_tgtTree] at hv; nomatch hv
  · intro a' r hs har
    obtain ⟨tr₂, s', hr₂, htr₂, rfl, _⟩ :=
      tgt_nonTau_sim s hs hsafe (fun _ hw => by rw [har] at hw; nomatch hw)
    cases s' with
    | divReturn num den =>
      cases den with
      | zero =>
        simp only [compileProg] at har; rw [observe_tgtTree] at har; nomatch har
      | succ d =>
        simp only [compileProg] at har; rw [observe_tgtTree] at har
        injection har with hr_eq; subst hr_eq
        exact ⟨tr₂, _, hr₂, htr₂, by rw [observe_srcTree]; rfl⟩
    | panicNow =>
      simp only [compileProg] at har; rw [observe_tgtTree] at har
      injection har with hr_eq; subst hr_eq
      exact ⟨tr₂, _, hr₂, htr₂, by rw [observe_srcTree]; rfl⟩
    | stepEmit _ _ =>
      simp only [compileProg] at har; rw [observe_tgtTree] at har; nomatch har
    | demonicIf _ _ =>
      simp only [compileProg] at har; rw [observe_tgtTree] at har; nomatch har
    | loopForever _ =>
      simp only [compileProg] at har; rw [observe_tgtTree] at har; nomatch har
  · intro a' i₁ k₁ o₁ hs hv hnf
    obtain ⟨tr₂, s', hr₂, htr₂, rfl, _⟩ :=
      tgt_nonTau_sim s hs hsafe (fun _ hw => by rw [hv] at hw; nomatch hw)
    cases s' with
    | stepEmit tick rest =>
      simp only [compileProg] at hv; rw [observe_tgtTree] at hv
      injection hv with hi hk; subst hi
      have hk_eq := eq_of_heq hk; subst hk_eq
      have h_src : (srcMachine.tree p (.stepEmit tick rest)).observe =
          .vis (.inr (.inl (.emit tick))) (fun _ => srcMachine.tree p rest) := by
        rw [observe_srcTree]; rfl
      refine ⟨tr₂ ++ [⟨.inr (.inl (.emit tick)), PUnit.unit⟩], srcMachine.tree p rest,
        reaches_trans hr₂ (.vis h_src (fun hf => hf) PUnit.unit (.refl _)), ?_,
        ⟨rest, rfl, rfl⟩⟩
      rw [List.filterMap_append, htr₂]; rfl
    | loopForever tick =>
      simp only [compileProg] at hv; rw [observe_tgtTree] at hv
      injection hv with hi hk; subst hi
      have hk_eq := eq_of_heq hk; subst hk_eq
      have h_src : (srcMachine.tree p (.loopForever tick)).observe =
          .vis (.inr (.inl (.emit tick))) (fun _ => srcMachine.tree p (.loopForever tick)) := by
        rw [observe_srcTree]; rfl
      refine ⟨tr₂ ++ [⟨.inr (.inl (.emit tick)), PUnit.unit⟩],
        srcMachine.tree p (.loopForever tick),
        reaches_trans hr₂ (.vis h_src (fun hf => hf) PUnit.unit (.refl _)), ?_,
        ⟨.loopForever tick, rfl, rfl⟩⟩
      rw [List.filterMap_append, htr₂]; rfl
    | divReturn num den =>
      cases den with
      | zero =>
        simp only [compileProg] at hv; rw [observe_tgtTree] at hv
        injection hv with hi _; subst hi
        exact False.elim (hnf trivial)
      | succ d =>
        simp only [compileProg] at hv; rw [observe_tgtTree] at hv; nomatch hv
    | demonicIf _ _ =>
      simp only [compileProg] at hv; rw [observe_tgtTree] at hv; nomatch hv
    | panicNow =>
      simp only [compileProg] at hv; rw [observe_tgtTree] at hv; nomatch hv

/-- Flip `src_to_tgt_weakObsRef` into a Layer 1A `CompilerPass`. -/
theorem compileProgPass (p : SrcProg) :
    CompilerPass
      (MachineSemantics srcMachine srcProj)
      (MachineSemantics tgtMachine tgtProj)
      (NoUBObsSpec Nat (Outcome Nat)) id p (compileProg p) :=
  compilerPass_of_weakObsRef srcMachine srcProj tgtMachine tgtProj
    (src_to_tgt_weakObsRef p)

/-- Flip `src_to_tgt_weakObsRef` into a Layer 1A `Compiles` proof. -/
theorem compileProgCompiles (p : SrcProg) :
    Compiles
      (srcMachine.toLanguage srcProj)
      (tgtMachine.toLanguage tgtProj)
      id p (compileProg p) :=
  compiles_of_weakObsRef srcMachine srcProj tgtMachine tgtProj
    (src_to_tgt_weakObsRef p)

theorem idVerifierPass (p : SrcProg) :
    VerifierPass
      (MachineSemantics srcMachine srcProj)
      (MachineSemantics srcMachine srcProj)
      (NoUBObsSpec Nat (Outcome Nat)) id p p :=
  fun _ _ h => h

def sampleSrcProg : SrcProg :=
  .stepEmit 1 (.demonicIf (.divReturn 12 3) (.divReturn 20 5))

def HaltsNormalFourSpec : Spec (BehaviorSet (ObsPrefix Nat (Outcome Nat))) :=
  BehaviorSet.allSpec fun pref =>
    match pref.outcome with
    | .running => True
    | .ret (.normal v) => v = 4
    | .ret .panic | .ret .abort | .fault => False

theorem sampleSrcProg_treeSafe : TreeSafe (srcMachine.run sampleSrcProg) := by
  intro tr u hru ⟨u', i, k, hsu, hvu, hfi⟩
  have h₀ : (srcMachine.run sampleSrcProg).observe =
      .vis (.inr (.inl (.emit 1)))
        (fun _ => srcMachine.tree sampleSrcProg
          (.demonicIf (.divReturn 12 3) (.divReturn 20 5))) := by
    unfold ITreeMachine.run; rw [observe_srcTree]; rfl
  have h₁ : (srcMachine.tree sampleSrcProg
      (.demonicIf (.divReturn 12 3) (.divReturn 20 5))).observe =
      .vis (.inr (.inr .pick))
        (fun b : Bool => srcMachine.tree sampleSrcProg
          (if b then .divReturn 12 3 else .divReturn 20 5)) := by
    rw [observe_srcTree]; rfl
  have h_tau_vis : ∀ {x y : ITree SrcEffect (Outcome Nat)} {j c},
      x.observe = .vis j c → TauStar x y → x = y := by
    intro x y j c hv hs
    cases hs with
    | refl => rfl
    | step ht => rw [hv] at ht; nomatch ht
  cases hru with
  | refl =>
    have heq := h_tau_vis h₀ hsu; subst heq
    rw [h₀] at hvu; injection hvu with hi _; subst hi; exact hfi
  | tau ht => rw [h₀] at ht; nomatch ht
  | vis hv₁ _ _ hr₁ =>
    rw [h₀] at hv₁; injection hv₁ with hi₁ hk₁; subst hi₁
    have hk₁_eq := eq_of_heq hk₁; subst hk₁_eq
    cases hr₁ with
    | refl =>
      have heq := h_tau_vis h₁ hsu; subst heq
      rw [h₁] at hvu; injection hvu with hi _; subst hi; exact hfi
    | tau ht => rw [h₁] at ht; nomatch ht
    | vis hv₂ _ b hr₂ =>
      rw [h₁] at hv₂; injection hv₂ with hi₂ hk₂; subst hi₂
      have hk₂_eq := eq_of_heq hk₂; subst hk₂_eq
      let cond : Bool := b
      have h₂ : (srcMachine.tree sampleSrcProg
          (if cond then .divReturn 12 3 else .divReturn 20 5)).observe =
          .ret (.normal 4) := by
        cases cond <;> (rw [observe_srcTree]; rfl)
      cases hr₂ with
      | refl =>
        cases hsu with
        | refl => rw [h₂] at hvu; nomatch hvu
        | step ht => rw [h₂] at ht; nomatch ht
      | tau ht => rw [h₂] at ht; nomatch ht
      | vis hv₃ => rw [h₂] at hv₃; nomatch hv₃

theorem sampleSrcProg_noUB :
    (NoUBObsSpec Nat (Outcome Nat)).holds
      (MachineSemantics srcMachine srcProj sampleSrcProg) :=
  (noUBObsSpec_holds_iff_treeSafe srcProj _).mpr sampleSrcProg_treeSafe

theorem sampleSrcProg_haltsFour :
    HaltsNormalFourSpec.holds
      (MachineSemantics srcMachine srcProj sampleSrcProg) := by
  intro pref hp
  change UBClosedObsPrefixes srcProj (srcMachine.run sampleSrcProg) pref at hp
  rw [ubClosedObsPrefixes_eq_of_treeSafe srcProj sampleSrcProg_treeSafe] at hp
  have h₀ : (srcMachine.run sampleSrcProg).observe =
      .vis (.inr (.inl (.emit 1)))
        (fun _ => srcMachine.tree sampleSrcProg
          (.demonicIf (.divReturn 12 3) (.divReturn 20 5))) := by
    unfold ITreeMachine.run; rw [observe_srcTree]; rfl
  have h₁ : (srcMachine.tree sampleSrcProg
      (.demonicIf (.divReturn 12 3) (.divReturn 20 5))).observe =
      .vis (.inr (.inr .pick))
        (fun b : Bool => srcMachine.tree sampleSrcProg
          (if b then .divReturn 12 3 else .divReturn 20 5)) := by
    rw [observe_srcTree]; rfl
  cases ho : pref.outcome with
  | running => trivial
  | fault =>
    simp only [HasObsPrefix, ho] at hp
    rcases hp with ⟨tr, u, hru, hfu, _⟩
    exact sampleSrcProg_treeSafe tr u hru hfu
  | ret out =>
    simp only [HasObsPrefix, ho] at hp
    rcases hp with ⟨tr, ⟨u, hru, hur⟩, _⟩
    cases hru with
    | refl => rw [h₀] at hur; nomatch hur
    | tau ht => rw [h₀] at ht; nomatch ht
    | vis hv₁ _ _ hr₁ =>
      rw [h₀] at hv₁; injection hv₁ with hi₁ hk₁; subst hi₁
      have hk₁_eq := eq_of_heq hk₁; subst hk₁_eq
      cases hr₁ with
      | refl => rw [h₁] at hur; nomatch hur
      | tau ht => rw [h₁] at ht; nomatch ht
      | vis hv₂ _ b hr₂ =>
        rw [h₁] at hv₂; injection hv₂ with hi₂ hk₂; subst hi₂
        have hk₂_eq := eq_of_heq hk₂; subst hk₂_eq
        let cond : Bool := b
        have h₂ : (srcMachine.tree sampleSrcProg
            (if cond then .divReturn 12 3 else .divReturn 20 5)).observe =
            .ret (.normal 4) := by
          cases cond <;> (rw [observe_srcTree]; rfl)
        cases hr₂ with
        | refl =>
          rw [h₂] at hur; injection hur with hout; subst hout; rfl
        | tau ht => rw [h₂] at ht; nomatch ht
        | vis hv₃ => rw [h₂] at hv₃; nomatch hv₃

/-- End-to-end Y-diagram theorem transferring `HaltsNormalFourSpec` to `tgtMachine`. -/
theorem example_machine_compiled_correct :
    HaltsNormalFourSpec.holds
      (MachineSemantics tgtMachine tgtProj (compileProg sampleSrcProg)) :=
  anneal_is_correct
    (MachineSemantics srcMachine srcProj)
    (MachineSemantics srcMachine srcProj)
    (MachineSemantics tgtMachine tgtProj)
    (NoUBObsSpec Nat (Outcome Nat))
    (NoUBObsSpec Nat (Outcome Nat))
    some compileProg id monotone_id compileProgPass
    sampleSrcProg sampleSrcProg sampleSrcProg id rfl
    (idVerifierPass sampleSrcProg) (fun _ h => h)
    sampleSrcProg_noUB HaltsNormalFourSpec sampleSrcProg_haltsFour

end ToyMachine
