import Trusted
import Anneal.Refinement
import Anneal.Effect
import Anneal.ITree
import Anneal.Pass

/-!
Illustrative control-flow graph (CFG) machines, resolved-label and `.tau`-erasing
forwarder-block elimination, and certificate-checked verification passes
(`#99 §§7, 9`, `#100 §5`).
-/

namespace ToyCFG

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Anneal.Refinement
open Anneal.Effect
open Anneal.ITree
open Anneal.Pass

/-- Open effect signature for `CFGProg`: operational faults and `Nat` observations. -/
abbrev CFGEffect : Effect.{0} :=
  SumE (FailE FailureKind) (ObsE Nat)

/-- Observation filter for `CFGEffect`. -/
def cfgProj : EffectObs CFGEffect Nat :=
  (EffectObs.erase (FailE FailureKind) Nat).sum (EffectObs.emit Nat)

/-- Instructions inside a basic block of `CFGProg`. -/
inductive BlockInstr : Type where
  | forward (target : Nat)
  | emitAndGoto (obs target : Nat)
  | returnVal (val : Nat)
  | faultUB
  deriving DecidableEq, Repr

/-- Control-flow graph program with an `entry` label and `blocks` table. -/
structure CFGProg : Type where
  entry : Nat
  blocks : Nat → BlockInstr

def isForwardTo (instr : BlockInstr) (c : Nat) : Bool :=
  instr == .forward c

/-! ## 1. Resolved-Label `CFGSystem` (`#99 §9`) -/

def resolveLabel (p : CFGProg) (l : Nat) : Nat :=
  match p.blocks l with
  | .forward target => target
  | _ => l

def cfgStepFn (p : CFGProg) (s : Nat) : ITreeF CFGEffect (Outcome Nat) Nat :=
  match p.blocks (resolveLabel p s) with
  | .forward target => .vis (.inr (.emit 0)) (fun _ => resolveLabel p target)
  | .emitAndGoto obs target => .vis (.inr (.emit obs)) (fun _ => resolveLabel p target)
  | .returnVal val => .ret (.normal val)
  | .faultUB => .vis (.inl (.fail .ub)) PEmpty.elim

def cfgMachine : ITreeMachine CFGProg Nat CFGEffect (Outcome Nat) where
  init := CFGProg.entry
  step := cfgStepFn

def isForwarder (p : CFGProg) (b c : Nat) : Prop :=
  p.blocks b = .forward c ∧ resolveLabel p c = c

def redirectInstr (b c : Nat) : BlockInstr → BlockInstr
  | .emitAndGoto obs target =>
    .emitAndGoto obs (if target = b then c else target)
  | other => other

def redirectEdges (p : CFGProg) (b c : Nat) : CFGProg where
  entry := p.entry
  blocks l := redirectInstr b c (p.blocks l)

def cfgSystem : CFGSystem CFGProg Nat CFGEffect Nat Nat where
  machine := cfgMachine
  pc s := s
  resolveLabel := resolveLabel
  isForwarder := isForwarder
  redirectEdges := redirectEdges

@[simp]
theorem resolveLabel_redirectEdges (p : CFGProg) (b c l : Nat) :
    resolveLabel (redirectEdges p b c) l = resolveLabel p l := by
  simp only [resolveLabel, redirectEdges, redirectInstr]
  cases p.blocks l <;> rfl

theorem cfgSystem_pureJumpLaw : PureJumpLaw cfgSystem :=
  fun p b c _ _ l => resolveLabel_redirectEdges p b c l

theorem cfgSystem_targetLabelIndependenceLaw : TargetLabelIndependenceLaw cfgSystem :=
  fun _ _ _ _ _ => rfl

theorem resolveLabel_if_eq {p : CFGProg} {b c : Nat}
    (hfwd : isForwarder p b c) (target : Nat) :
    resolveLabel p (if target = b then c else target) = resolveLabel p target := by
  split
  · next heq =>
    subst heq
    have hb : resolveLabel p target = c := by unfold resolveLabel; rw [hfwd.1]
    exact hfwd.2.trans hb.symm
  · rfl

@[simp]
theorem redirectEdges_blocks (p : CFGProg) (b c l : Nat) :
    (redirectEdges p b c).blocks l = redirectInstr b c (p.blocks l) :=
  rfl

theorem cfgSystem_pcDispatchLaw : PCDispatchLaw cfgSystem := by
  intro p b c _ hfwd _ s
  simp only [cfgSystem, cfgMachine, cfgStepFn, resolveLabel_redirectEdges, redirectEdges_blocks]
  generalize resolveLabel p s = l
  cases p.blocks l <;> simp [redirectInstr, resolveLabel_if_eq hfwd]

theorem cfg_eliminateForwarder_exact
    (p : CFGProg) (b c : Nat) (hne : b ≠ c) (hfwd : isForwarder p b c) :
    ExactPass
      (MachineSemantics cfgMachine cfgProj)
      (MachineSemantics cfgMachine cfgProj)
      id id p (redirectEdges p b c) :=
  eliminateForwarder_exactPass cfgSystem cfgProj
    cfgSystem_pureJumpLaw cfgSystem_targetLabelIndependenceLaw
    cfgSystem_pcDispatchLaw p b c hne hfwd

/-! ## 2. Certificate-Checked Forwarder Pass -/

structure ForwarderCert (p₁ p₂ : CFGProg) : Type where
  b : Nat
  c : Nat
  eq_redirect : p₂ = redirectEdges p₁ b c

def checkForwarder (p₁ p₂ : CFGProg) (cert : ForwarderCert p₁ p₂) : Bool :=
  (cert.b != cert.c) &&
  isForwardTo (p₁.blocks cert.b) cert.c &&
  (resolveLabel p₁ cert.c == cert.c)

theorem checkForwarder_sound {p₁ p₂ : CFGProg} {cert : ForwarderCert p₁ p₂}
    (hcheck : checkForwarder p₁ p₂ cert = true) :
    ExactPass
      (MachineSemantics cfgMachine cfgProj)
      (MachineSemantics cfgMachine cfgProj)
      id id p₁ p₂ := by
  simp only [checkForwarder, isForwardTo, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hcheck
  rcases hcheck with ⟨⟨hne, hb⟩, hc⟩
  rw [cert.eq_redirect]
  exact cfg_eliminateForwarder_exact p₁ cert.b cert.c hne ⟨hb, hc⟩

/-! ## 3. True `.tau`-Erasing `TauCFGSystem` -/

def tauCfgStepFn (p : CFGProg) (s : Nat) : ITreeF CFGEffect (Outcome Nat) Nat :=
  match p.blocks s with
  | .forward target => .tau target
  | .emitAndGoto obs target => .vis (.inr (.emit obs)) (fun _ => target)
  | .returnVal val => .ret (.normal val)
  | .faultUB => .vis (.inl (.fail .ub)) PEmpty.elim

def tauCfgMachine : ITreeMachine CFGProg Nat CFGEffect (Outcome Nat) where
  init := CFGProg.entry
  step := tauCfgStepFn

def retargetBlock (b c s : Nat) : Nat :=
  if s = b then c else s

def redirectTauInstr (b c : Nat) : BlockInstr → BlockInstr
  | .forward target => .forward (retargetBlock b c target)
  | .emitAndGoto obs target => .emitAndGoto obs (retargetBlock b c target)
  | .returnVal val => .returnVal val
  | .faultUB => .faultUB

def redirectTauEdges (p : CFGProg) (b c : Nat) : CFGProg where
  entry := retargetBlock b c p.entry
  blocks l := redirectTauInstr b c (p.blocks l)

def isTauForwarder (p : CFGProg) (b c : Nat) : Prop :=
  p.blocks b = .forward c

def tauCfgSystem : TauCFGSystem CFGProg Nat CFGEffect Nat Nat where
  machine := tauCfgMachine
  isForwarder := isTauForwarder
  redirectEdges := redirectTauEdges
  retarget := retargetBlock

theorem tauCfgSystem_law : TauForwarderLaw tauCfgSystem where
  init_eq _ _ _ _ _ := rfl
  retarget_idem b c hne s := by
    unfold tauCfgSystem retargetBlock; dsimp only
    by_cases h : s = b <;> simp [h, Ne.symm hne]
  forwarder_tau p b c _ hfwd s := by
    unfold tauCfgSystem tauCfgMachine tauCfgStepFn retargetBlock; dsimp only
    by_cases h : s = b
    · subst h; rw [hfwd]; simp
    · simp [h]
  step_commutes p b c _ _ s _ := by
    unfold tauCfgSystem tauCfgMachine tauCfgStepFn redirectTauEdges redirectTauInstr
    dsimp only
    cases p.blocks s with
    | forward _ | emitAndGoto _ _ | returnVal _ => rfl
    | faultUB =>
      exact congrArg (ITreeF.vis (E := CFGEffect) (.inl (.fail .ub)))
        (funext fun o => PEmpty.elim o)

theorem tauCfg_eliminateForwarder_eutt
    (p : CFGProg) (b c : Nat) (hne : b ≠ c) (hfwd : isTauForwarder p b c) :
    Eutt (tauCfgMachine.run p) (tauCfgMachine.run (redirectTauEdges p b c)) :=
  eliminateTauForwarder_eutt tauCfgSystem tauCfgSystem_law p b c hne hfwd

theorem tauCfg_eliminateForwarder_exact
    (p : CFGProg) (b c : Nat) (hne : b ≠ c) (hfwd : isTauForwarder p b c) :
    ExactPass
      (MachineSemantics tauCfgMachine cfgProj)
      (MachineSemantics tauCfgMachine cfgProj)
      id id p (redirectTauEdges p b c) :=
  eliminateTauForwarder_exactPass tauCfgSystem cfgProj tauCfgSystem_law p b c hne hfwd

/-! ## 4. Concrete End-to-End CFG Program Proof -/

def rawCFGProg : CFGProg where
  entry := 0
  blocks
    | 0 => .emitAndGoto 5 1
    | 1 => .forward 2
    | _ => .returnVal 42

def cleanedCFGProg : CFGProg := redirectEdges rawCFGProg 1 2

def sampleCert : ForwarderCert rawCFGProg cleanedCFGProg := ⟨1, 2, rfl⟩

theorem sampleCert_valid : checkForwarder rawCFGProg cleanedCFGProg sampleCert = true := rfl

theorem sample_verifierPass :
    VerifierPass
      (MachineSemantics cfgMachine cfgProj)
      (MachineSemantics cfgMachine cfgProj)
      (NoUBObsSpec Nat (Outcome Nat)) id rawCFGProg cleanedCFGProg :=
  (checkForwarder_sound sampleCert_valid).toVerifierPass (NoUBObsSpec Nat (Outcome Nat))

def ReturnsFortyTwoSpec : Spec (BehaviorSet (ObsPrefix Nat (Outcome Nat))) :=
  BehaviorSet.allSpec fun pref =>
    match pref.outcome with
    | .ret (.normal v) => v = 42
    | .ret .panic | .ret .abort | .fault => False
    | .running => True

theorem cleanedCFGProg_treeSafe : TreeSafe (cfgMachine.run cleanedCFGProg) := by
  intro tr u hru ⟨u', i, k, hsu, hvu, hfi⟩
  have h₀ : (cfgMachine.run cleanedCFGProg).observe =
      .vis (.inr (.emit 5)) (fun _ => cfgMachine.tree cleanedCFGProg 2) := by
    unfold ITreeMachine.run ITreeMachine.tree; rw [ITree.observe_cofix]; rfl
  have h₂ : (cfgMachine.tree cleanedCFGProg 2).observe = .ret (.normal 42) := by
    unfold ITreeMachine.tree; rw [ITree.observe_cofix]; rfl
  cases hru with
  | refl =>
    cases hsu with
    | refl => rw [h₀] at hvu; injection hvu with hi _; subst hi; exact hfi
    | step ht => rw [h₀] at ht; nomatch ht
  | tau ht => rw [h₀] at ht; nomatch ht
  | vis hv₁ _ _ hr₁ =>
    rw [h₀] at hv₁; injection hv₁ with hi₁ hk₁; subst hi₁
    have hk₁_eq := eq_of_heq hk₁; subst hk₁_eq
    cases hr₁ with
    | refl =>
      cases hsu with
      | refl => rw [h₂] at hvu; nomatch hvu
      | step ht => rw [h₂] at ht; nomatch ht
    | tau ht => rw [h₂] at ht; nomatch ht
    | vis hv₂ => rw [h₂] at hv₂; nomatch hv₂

theorem cleanedCFGProg_verified :
    (NoUBObsSpec Nat (Outcome Nat)).holds (MachineSemantics cfgMachine cfgProj cleanedCFGProg) ∧
    ReturnsFortyTwoSpec.holds (MachineSemantics cfgMachine cfgProj cleanedCFGProg) := by
  refine ⟨(noUBObsSpec_holds_iff_treeSafe cfgProj _).mpr cleanedCFGProg_treeSafe, ?_⟩
  intro pref hp
  change UBClosedObsPrefixes cfgProj (cfgMachine.run cleanedCFGProg) pref at hp
  rw [ubClosedObsPrefixes_eq_of_treeSafe cfgProj cleanedCFGProg_treeSafe] at hp
  have h₀ : (cfgMachine.run cleanedCFGProg).observe =
      .vis (.inr (.emit 5)) (fun _ => cfgMachine.tree cleanedCFGProg 2) := by
    unfold ITreeMachine.run ITreeMachine.tree; rw [ITree.observe_cofix]; rfl
  have h₂ : (cfgMachine.tree cleanedCFGProg 2).observe = .ret (.normal 42) := by
    unfold ITreeMachine.tree; rw [ITree.observe_cofix]; rfl
  cases ho : pref.outcome with
  | running => trivial
  | fault =>
    simp only [HasObsPrefix, ho] at hp
    rcases hp with ⟨tr, u, hru, hfu, _⟩
    exact cleanedCFGProg_treeSafe tr u hru hfu
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
      | refl => rw [h₂] at hur; injection hur with hout; subst hout; rfl
      | tau ht => rw [h₂] at ht; nomatch ht
      | vis hv₂ => rw [h₂] at hv₂; nomatch hv₂

theorem example_cfg_end_to_end :
    ReturnsFortyTwoSpec.holds (MachineSemantics cfgMachine cfgProj rawCFGProg) :=
  anneal_is_correct
    (MachineSemantics cfgMachine cfgProj)
    (MachineSemantics cfgMachine cfgProj)
    (MachineSemantics cfgMachine cfgProj)
    (NoUBObsSpec Nat (Outcome Nat))
    (NoUBObsSpec Nat (Outcome Nat))
    some id id monotone_id (fun _ _ _ h => h)
    rawCFGProg rawCFGProg cleanedCFGProg id rfl
    sample_verifierPass (fun _ h => h)
    cleanedCFGProg_verified.1 ReturnsFortyTwoSpec cleanedCFGProg_verified.2

theorem rawCFGProg_tauForwarder_eutt :
    Eutt (tauCfgMachine.run rawCFGProg)
      (tauCfgMachine.run (redirectTauEdges rawCFGProg 1 2)) :=
  tauCfg_eliminateForwarder_eutt rawCFGProg 1 2 (by decide) rfl

end ToyCFG
