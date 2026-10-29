import Std.Do
import Trusted
import Anneal.Refinement
import Anneal.Effect
import Anneal.ITree
import Anneal.Pass
import Anneal.EffectWP
import Anneal.ITreeWP
import ToyMachine

/-!
Zero-axiom adequacy canaries, non-vacuity / excluded-miracle negative controls,
failure taxonomy witnesses, Smyth `WeakRef` vs. `WeakSim` / `WeakCSim` /
`TotalWeakRef` lattice duality, infinite reactive stream verification,
`BridgeContract` refinement, and `Std.Do.Triple` Hoare-logic verification over
`ITree`.
-/

namespace Canaries

open Std.Do
open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Anneal.Refinement
open Anneal.Effect
open Anneal.ITree
open Anneal.Pass
open Anneal.EffectWP
open Anneal.ITreeWP
open ToyMachine

private theorem observe_srcTree (p s : SrcProg) :
    (srcMachine.tree p s).observe =
      ITreeF.map (srcMachine.tree p) (srcStepFn p s) :=
  ITree.observe_cofix (srcStepFn p) s

/-! ## 1. Adequacy Canaries (`#83`) -/

def ubBeforeLoopProg : SrcProg :=
  .demonicIf (.divReturn 1 0) (.loopForever 9)

theorem canary_ub_before_infinite_loop :
    ¬ (NoUBObsSpec Nat (Outcome Nat)).holds
      (MachineSemantics srcMachine srcProj ubBeforeLoopProg) := by
  intro hsafe
  have h_choice : (srcMachine.run ubBeforeLoopProg).observe =
      .vis (.inr (.inr .pick))
        (fun b : Bool => srcMachine.tree ubBeforeLoopProg
          (if b then .divReturn 1 0 else .loopForever 9)) := by
    unfold ITreeMachine.run; rw [observe_srcTree]; rfl
  have h_ub : (srcMachine.tree ubBeforeLoopProg (.divReturn 1 0)).observe =
      .vis (.inl (.fail .ub))
        (fun o => srcMachine.tree ubBeforeLoopProg (PEmpty.elim o)) := by
    rw [observe_srcTree]; rfl
  have hreach : Reaches (srcMachine.run ubBeforeLoopProg)
      [⟨.inr (.inr .pick), true⟩]
      (srcMachine.tree ubBeforeLoopProg (.divReturn 1 0)) :=
    .vis h_choice (fun hf => hf) true (.refl _)
  have hts : TreeSafe (srcMachine.run ubBeforeLoopProg) :=
    (noUBObsSpec_holds_iff_treeSafe srcProj _).mp hsafe
  exact hts _ _ hreach ⟨_, _, _, .refl _, h_ub, trivial⟩

def discardedInvalidBranchProg : SrcProg :=
  .demonicIf (.divReturn 42 1) (.divReturn 0 0)

theorem canary_discarded_invalid_value :
    ¬ (NoUBObsSpec Nat (Outcome Nat)).holds
      (MachineSemantics srcMachine srcProj discardedInvalidBranchProg) := by
  intro hsafe
  have h_choice : (srcMachine.run discardedInvalidBranchProg).observe =
      .vis (.inr (.inr .pick))
        (fun b : Bool => srcMachine.tree discardedInvalidBranchProg
          (if b then .divReturn 42 1 else .divReturn 0 0)) := by
    unfold ITreeMachine.run; rw [observe_srcTree]; rfl
  have h_ub : (srcMachine.tree discardedInvalidBranchProg (.divReturn 0 0)).observe =
      .vis (.inl (.fail .ub))
        (fun o => srcMachine.tree discardedInvalidBranchProg (PEmpty.elim o)) := by
    rw [observe_srcTree]; rfl
  have hreach : Reaches (srcMachine.run discardedInvalidBranchProg)
      [⟨.inr (.inr .pick), false⟩]
      (srcMachine.tree discardedInvalidBranchProg (.divReturn 0 0)) :=
    .vis h_choice (fun hf => hf) false (.refl _)
  have hts : TreeSafe (srcMachine.run discardedInvalidBranchProg) :=
    (noUBObsSpec_holds_iff_treeSafe srcProj _).mp hsafe
  exact hts _ _ hreach ⟨_, _, _, .refl _, h_ub, trivial⟩

def safeLoopProg : SrcProg := .loopForever 7

private theorem loopForever_reaches_eq
    {tr : List (Event SrcEffect)} {u : ITree SrcEffect (Outcome Nat)}
    (hr : Reaches (srcMachine.tree safeLoopProg (.loopForever 7)) tr u) :
    u = srcMachine.tree safeLoopProg (.loopForever 7) := by
  have h_obs : (srcMachine.tree safeLoopProg (.loopForever 7)).observe =
      .vis (.inr (.inl (.emit 7)))
        (fun _ => srcMachine.tree safeLoopProg (.loopForever 7)) := by
    rw [observe_srcTree]; rfl
  generalize ht : srcMachine.tree safeLoopProg (.loopForever 7) = t₀ at hr ⊢
  induction hr with
  | refl => rfl
  | tau htau => subst ht; rw [h_obs] at htau; nomatch htau
  | vis hv _ _ _ ih =>
    subst ht; rw [h_obs] at hv; injection hv with hi hk; subst hi
    have hk_eq := eq_of_heq hk; subst hk_eq
    exact ih rfl

theorem safeLoopProg_treeSafe : TreeSafe (srcMachine.run safeLoopProg) := by
  intro tr u hru ⟨u', i, k, hsu, hvu, hfi⟩
  have hu : u = srcMachine.tree safeLoopProg (.loopForever 7) :=
    loopForever_reaches_eq hru
  subst hu
  have h_obs : (srcMachine.tree safeLoopProg (.loopForever 7)).observe =
      .vis (.inr (.inl (.emit 7)))
        (fun _ => srcMachine.tree safeLoopProg (.loopForever 7)) := by
    rw [observe_srcTree]; rfl
  cases hsu with
  | refl => rw [h_obs] at hvu; injection hvu with hi _; subst hi; exact hfi
  | step htau => rw [h_obs] at htau; nomatch htau

theorem canary_safe_infinite_loop :
    (NoUBObsSpec Nat (Outcome Nat)).holds
      (MachineSemantics srcMachine srcProj safeLoopProg) ∧
    ∀ tr out,
      ¬ MachineSemantics srcMachine srcProj safeLoopProg ⟨tr, .ret out⟩ := by
  refine ⟨(noUBObsSpec_holds_iff_treeSafe srcProj _).mpr safeLoopProg_treeSafe, ?_⟩
  intro tr out hp
  change UBClosedObsPrefixes srcProj (srcMachine.run safeLoopProg) ⟨tr, .ret out⟩ at hp
  rw [ubClosedObsPrefixes_eq_of_treeSafe srcProj safeLoopProg_treeSafe] at hp
  rcases hp with ⟨_, ⟨u, hru, hur⟩, _⟩
  have hu := loopForever_reaches_eq hru; subst hu
  have h_obs : (srcMachine.tree safeLoopProg (.loopForever 7)).observe =
      .vis (.inr (.inl (.emit 7)))
        (fun _ => srcMachine.tree safeLoopProg (.loopForever 7)) := by
    rw [observe_srcTree]; rfl
  rw [h_obs] at hur; nomatch hur

def secretBranchProg : SrcProg :=
  .demonicIf (.stepEmit 10 (.divReturn 0 1)) (.stepEmit 20 (.divReturn 0 1))

def SameTerminalTraceSpec : Spec (BehaviorSet (ObsPrefix Nat (Outcome Nat))) :=
  BehaviorSet.twoSafetySpec fun p₁ p₂ =>
    match p₁.outcome, p₂.outcome with
    | .ret (.normal _), .ret (.normal _) => p₁.trace = p₂.trace
    | _, _ => True

theorem canary_secret_branch_leakage :
    ¬ SameTerminalTraceSpec.holds
      (MachineSemantics srcMachine srcProj secretBranchProg) := by
  intro hct
  have h₀ : (srcMachine.run secretBranchProg).observe =
      .vis (.inr (.inr .pick))
        (fun b : Bool => srcMachine.tree secretBranchProg
          (if b then .stepEmit 10 (.divReturn 0 1)
           else .stepEmit 20 (.divReturn 0 1))) := by
    unfold ITreeMachine.run; rw [observe_srcTree]; rfl
  have h₁_t : (srcMachine.tree secretBranchProg (.stepEmit 10 (.divReturn 0 1))).observe =
      .vis (.inr (.inl (.emit 10)))
        (fun _ => srcMachine.tree secretBranchProg (.divReturn 0 1)) := by
    rw [observe_srcTree]; rfl
  have h₁_f : (srcMachine.tree secretBranchProg (.stepEmit 20 (.divReturn 0 1))).observe =
      .vis (.inr (.inl (.emit 20)))
        (fun _ => srcMachine.tree secretBranchProg (.divReturn 0 1)) := by
    rw [observe_srcTree]; rfl
  have h₂ : (srcMachine.tree secretBranchProg (.divReturn 0 1)).observe =
      .ret (.normal 0) := by
    rw [observe_srcTree]; rfl
  have hp₁ : MachineSemantics srcMachine srcProj secretBranchProg ⟨[10], .ret (.normal 0)⟩ :=
    Or.inl ⟨[⟨.inr (.inr .pick), true⟩, ⟨.inr (.inl (.emit 10)), PUnit.unit⟩],
      ⟨_, .vis h₀ (fun h => h) true (.vis h₁_t (fun h => h) PUnit.unit (.refl _)), h₂⟩, rfl⟩
  have hp₂ : MachineSemantics srcMachine srcProj secretBranchProg ⟨[20], .ret (.normal 0)⟩ :=
    Or.inl ⟨[⟨.inr (.inr .pick), false⟩, ⟨.inr (.inl (.emit 20)), PUnit.unit⟩],
      ⟨_, .vis h₀ (fun h => h) false (.vis h₁_f (fun h => h) PUnit.unit (.refl _)), h₂⟩, rfl⟩
  have heq : [10] = [20] := @hct ⟨[10], .ret (.normal 0)⟩ ⟨[20], .ret (.normal 0)⟩ hp₁ hp₂
  nomatch heq

/-! ## 2. Excluded-Miracle Non-Vacuity & Failure Taxonomy Controls -/

theorem vacuity_stuck_excluded_miracle :
    TreeSafe (ITree.stuck (E := PickE PEmpty.{1}) (R := Nat)) ∧
    ¬ DWP (pickWP PUnit PEmpty.{1})
        (ITree.stuck (E := PickE PEmpty.{1}) (R := Nat))
        (fun _ _ => True) PUnit.unit := by
  refine ⟨fun tr u hru ⟨u', i, _, _, _, hfi⟩ => hfi, ?_⟩
  intro hdwp
  rw [DWP.unfold_eq] at hdwp
  have hObs : (ITree.stuck (E := PickE PEmpty.{1}) (R := Nat)).observe =
      .vis (PickReq.pick : (PickE PEmpty.{1}).I)
        (fun o => ITree.ret o >>= PEmpty.elim) :=
    (congrArg ITree.observe
      (vis_bind (E := PickE PEmpty.{1}) (PickReq.pick : (PickE PEmpty.{1}).I)
        ITree.ret PEmpty.elim)).trans (ITree.observe_vis _ _)
  rw [hObs] at hdwp
  rcases hdwp.1 with ⟨o⟩
  exact PEmpty.elim o

def NoPanicOrAbortObsSpec (Obs Val : Type) :
    Spec (BehaviorSet (ObsPrefix Obs (Outcome Val))) :=
  BehaviorSet.allSpec fun p =>
    match p.outcome with
    | .running | .ret (.normal _) => True
    | .ret .panic | .ret .abort | .fault => False

theorem failure_and_termination_taxonomy_control :
    ¬ (NoUBObsSpec Nat (Outcome Nat)).holds (· = ⟨[], .fault⟩) ∧
    ((NoUBObsSpec Nat (Outcome Nat)).holds (· = ⟨[], .ret .panic⟩) ∧
     ¬ (NoPanicOrAbortObsSpec Nat Nat).holds (· = ⟨[], .ret .panic⟩)) ∧
    ((NoUBObsSpec Nat (Outcome Nat)).holds (· = ⟨[], .ret .abort⟩) ∧
     ¬ (NoPanicOrAbortObsSpec Nat Nat).holds (· = ⟨[], .ret .abort⟩)) := by
  refine ⟨fun h => @h ⟨[], .fault⟩ rfl, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro _ rfl; trivial
  · intro h; exact @h ⟨[], .ret .panic⟩ rfl
  · rintro _ rfl; trivial
  · intro h; exact @h ⟨[], .ret .abort⟩ rfl

/-! ## 3. Foreign / ISA `BridgeContract` Refinement Witness (`#102`) -/

abbrev BridgeEffect : Effect.{0} :=
  SumE (FailE FailureKind)
    (SumE (PickE (Nat × Nat))
      (SumE (PickE PEmpty.{1}) (ObsE Nat)))

@[reducible]
def highBridge : BridgeContract Nat Nat where
  pre s := 1 ≤ s
  post s obs s' := obs = s ∧ s ≤ s'

@[reducible]
def lowBridge : BridgeContract Nat Nat where
  pre _ := True
  post s obs s' := obs = s ∧ s' = s + 1

theorem bridge_contract_refinement_witness (s : Nat) :
    WeakRef
      (bridgeTree (E := BridgeEffect) lowBridge s)
      (bridgeTree (E := BridgeEffect) highBridge s) :=
  BridgeContract.weakRef lowBridge highBridge
    (fun _ _ => trivial)
    (fun _ _ _ _ ⟨hobs, hs'⟩ => ⟨hobs, by omega⟩)
    s

/-! ## 4. Non-Time-Traveling Prefix Preservation Before Subsequent UB -/

def emitThenUBProg : SrcProg := .stepEmit 42 (.divReturn 1 0)

theorem canary_ubClosedObsPrefixes_excludes_mismatched_head :
    MachineSemantics srcMachine srcProj emitThenUBProg ⟨[42], .running⟩ ∧
    ¬ MachineSemantics srcMachine srcProj emitThenUBProg ⟨[99], .running⟩ := by
  have h₀ : (srcMachine.run emitThenUBProg).observe =
      .vis (.inr (.inl (.emit 42)))
        (fun _ => srcMachine.tree emitThenUBProg (.divReturn 1 0)) := by
    unfold ITreeMachine.run; rw [observe_srcTree]; rfl
  have h₁ : (srcMachine.tree emitThenUBProg (.divReturn 1 0)).observe =
      .vis (.inl (.fail .ub))
        (fun o => srcMachine.tree emitThenUBProg (PEmpty.elim o)) := by
    rw [observe_srcTree]; rfl
  have hreach_tr : ∀ {tr u},
      Reaches (srcMachine.run emitThenUBProg) tr u →
      tr.filterMap srcProj.obsOf = [] ∨ tr.filterMap srcProj.obsOf = [42] := by
    intro tr u hr
    cases hr with
    | refl => exact .inl rfl
    | tau ht => rw [h₀] at ht; nomatch ht
    | vis hv₁ _ _ hr₁ =>
      rw [h₀] at hv₁; injection hv₁ with hi₁ hk₁; subst hi₁
      have hk₁_eq := eq_of_heq hk₁; subst hk₁_eq
      cases hr₁ with
      | refl => exact .inr rfl
      | tau ht => rw [h₁] at ht; nomatch ht
      | vis hv₂ hnf _ _ =>
        rw [h₁] at hv₂; injection hv₂ with hi₂ _; subst hi₂
        exact False.elim (hnf trivial)
  refine ⟨Or.inl ⟨[⟨.inr (.inl (.emit 42)), PUnit.unit⟩], _,
    .vis h₀ (fun h => h) PUnit.unit (.refl _), rfl⟩, ?_⟩
  rintro (⟨tr, u, hru, htr⟩ | ⟨tr₀, hpref, tr, u, hru, hfu, htr₀⟩)
  · rcases hreach_tr hru with hnil | h42 <;> rw [htr] at *
    · nomatch hnil
    · nomatch h42
  · rcases hreach_tr hru with hnil | h42
    · rw [htr₀] at hnil; subst hnil
      cases hru with
      | refl =>
        rcases hfu with ⟨u', i, k, hsu, hvu, hfi⟩
        cases hsu with
        | refl => rw [h₀] at hvu; injection hvu with hi _; subst hi; exact hfi
        | step ht => rw [h₀] at ht; nomatch ht
      | tau ht => rw [h₀] at ht; nomatch ht
      | vis hv₁ =>
        rw [h₀] at hv₁; injection hv₁ with hi₁ _; subst hi₁
        nomatch htr₀
    · rw [htr₀] at h42; subst h42
      rcases hpref with ⟨t_rest, h_eq⟩
      nomatch h_eq

/-! ## 5. Smyth Refinement Lattice Duality, Infinite Streams, & `Std.Do.Triple` -/

abbrev LatticeEffect : Effect.{0} :=
  SumE (FailE FailureKind) (PickE PEmpty.{1})

theorem smyth_refinement_lattice_duality :
    WeakRef (ITree.stuck (E := LatticeEffect)) (ITree.ret 0) ∧
    WeakRef (ITree.ret (E := LatticeEffect) 0) (ITree.fail FailureKind.ub) ∧
    (WeakSim (ITree.fail (E := LatticeEffect) FailureKind.ub) (ITree.ret 0) ∧
     ¬ WeakRef (ITree.fail (E := LatticeEffect) FailureKind.ub) (ITree.ret 0)) ∧
    ¬ WeakCSim (ITree.stuck (E := LatticeEffect)) (ITree.ret 0) ∧
    WeakCSim (ITree.fail (E := LatticeEffect) (R := Nat) FailureKind.ub)
      (ITree.stuck (E := LatticeEffect)) ∧
    WeakRef (ITree.spin (E := LatticeEffect)) (ITree.ret 0) ∧
    ¬ TotalWeakRef (ITree.spin (E := LatticeEffect)) (ITree.ret 0) :=
  ⟨WeakRef.stuck_bot (ITree.ret 0),
   WeakRef.fail_top FailureKind.ub (ITree.ret 0),
   ⟨weakSim_fail_any FailureKind.ub (ITree.ret 0),
    not_weakRef_fail_ret FailureKind.ub 0⟩,
   not_weakCSim_stuck_ret (E := LatticeEffect) 0,
   weakCSim_fail_stuck (E := LatticeEffect) (R := Nat) FailureKind.ub,
   WeakRef.spin_bot (ITree.ret 0),
   not_spin_totalWeakRef_ret (E := LatticeEffect) 0⟩

/-- Infinite reactive counter server emitting `n, n + 1, n + 2, ...` forever. -/
def counterServer : Nat → ITree (ObsE Nat) PEmpty :=
  ITree.cofix fun k => .vis (.emit k) (fun _ => k + 1)

def natsFrom (n : Nat) : Stream' Nat := fun k => n + k

def EmitsEvenNow (t : ITree (ObsE Nat) PEmpty) : Prop :=
  ∃ m k, m % 2 = 0 ∧ t.observe = .vis (.emit m) k

private theorem observe_counterServer (k : Nat) :
    (counterServer k).observe =
      .vis (.emit k) (fun _ => counterServer (k + 1)) := by
  unfold counterServer; rw [ITree.observe_cofix]; rfl

theorem counterServer_treeSafe (n : Nat) : TreeSafe (counterServer n) :=
  fun _ _ _ ⟨_, _, _, _, _, hf⟩ => hf

theorem counterServer_follows_natsFrom (n : Nat) :
    FollowsStream (counterServer n) (natsFrom n) := by
  refine FollowsStream.coinduct
    (fun t s => ∃ k, t = counterServer k ∧ s = natsFrom k) ?_
    (counterServer n) (natsFrom n) ⟨n, rfl, rfl⟩
  rintro t s ⟨k, rfl, rfl⟩
  refine ⟨counterServer k, (fun _ => counterServer (k + 1)),
    .refl _, observe_counterServer k, k + 1, rfl, ?_⟩
  funext i; simp [Stream'.tail, natsFrom]; omega

theorem counterServer_infinitelyOften_even (n : Nat) :
    InfinitelyOften EmitsEvenNow (counterServer n) := by
  refine CoAlways.coinduct (Eventually EmitsEvenNow)
    (fun t => ∃ k, t = counterServer k) ?_
    (counterServer n) ⟨n, rfl⟩
  rintro t ⟨k, rfl⟩
  refine ⟨?_, ?_⟩
  · by_cases heven : k % 2 = 0
    · exact .here ⟨k, _, heven, observe_counterServer k⟩
    · have hodd : (k + 1) % 2 = 0 := by omega
      exact .visDemonic (observe_counterServer k) rfl (fun h => h) ⟨PUnit.unit⟩
        (fun _ => .here ⟨k + 1, _, hodd, observe_counterServer (k + 1)⟩)
  · simp only [observe_counterServer]
    exact fun _ => ⟨k + 1, rfl⟩

theorem infinite_reactive_stream_liveness (n : Nat) :
    TreeSafe (counterServer n) ∧
    FollowsStream (counterServer n) (natsFrom n) ∧
    InfinitelyOften EmitsEvenNow (counterServer n) :=
  ⟨counterServer_treeSafe n,
   counterServer_follows_natsFrom n,
   counterServer_infinitelyOften_even n⟩

/-- Monadic `do`-block over `ITree` verified directly via `Std.Do.Triple`. -/
def emitAndAddTwo (n : Nat) :
    ITree (SumE (FailE FailureKind) (ObsE Nat)) Nat := do
  ITree.emit n
  pure (n + 2)

theorem std_do_triple_itree_canary :
    ⦃⌜(40 : Nat) = 40⌝⦄ emitAndAddTwo 40 ⦃⇓ r => ⌜r = 42⌝⦄ ∧
    TreeSafe (emitAndAddTwo 40) := by
  have htriple : ⦃⌜(40 : Nat) = 40⌝⦄ emitAndAddTwo 40 ⦃⇓ r => ⌜r = 42⌝⦄ := by
    intro _
    apply DWLP.bind
    rw [DWLP.unfold_eq]
    change DWLP _ (ITree.ret PUnit.unit) _ PUnit.unit
    rw [DWLP.ret_iff]
    exact (DWLP.ret_iff _ 42 _ PUnit.unit).mpr rfl
  have hd : DWLP ((failWP PUnit FailureKind).sum (obsIgnoreWP PUnit Nat))
      (emitAndAddTwo 40) (fun r _ => r = 42) PUnit.unit :=
    Triple.toDWLP htriple rfl
  exact ⟨htriple, (dwlp_pure_adequacy hd).1⟩

end Canaries
