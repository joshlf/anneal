import Anneal.Refinement
import ToyYDiagram

/-!
Zero-axiom concrete witness and negative-control tests for Layer 1A
(`Trusted.Refinement` and `Anneal.Refinement`).
-/

namespace Anneal.Tests.ConcreteYDiagram

open Trusted.Refinement
open Anneal.Refinement
open Anneal.Examples.ToyYDiagram

/-! ## 1. Negative Control for Reversed `VerifierPass` Direction -/

def badProg : ToyMir := .both (.lit 4) (.divUnchecked 1 0)

theorem exploreLeft_badProg_is_noUB :
    ToyNoUB.holds (ToyMirSem (exploreLeft badProg)) := by
  intro o ho hub
  change o = .ok 4 at ho
  rw [ho] at hub; exact hub

theorem badProg_has_ub : ¬ ToyNoUB.holds (ToyMirSem badProg) := by
  intro h_noUB
  exact h_noUB (.inr rfl : ToyMirSem badProg .ub) trivial

theorem exploreLeft_not_verifierPass_on_badProg :
    ¬ VerifierPass ToyMirSem ToyMirSem ToyNoUB id badProg (exploreLeft badProg) := by
  intro h_vpass
  exact badProg_has_ub
    (VerifierPass.reflect_guard h_vpass (fun h => h) exploreLeft_badProg_is_noUB)

def ubOnLeft : ToyMir := .both (.divUnchecked 1 0) (.lit 4)

theorem exploreLeft_lifts_ub_counterexample :
    ¬ ToyNoUB.holds (ToyMirSem ubOnLeft) := by
  apply BugFinderPass.lift_counterexample (exploreLeft_is_bugFinderPass ubOnLeft) ToyNoUB
  intro h_noUB
  exact @h_noUB .ub rfl trivial

/-! ## 2. Negative Control for Non-Volatile Observation Erasure -/

structure StoreTrace where
  scratch : Nat
  volatileOut : Nat
  isUB : Bool

def eraseScratchTrace (t : StoreTrace) : StoreTrace := { t with scratch := 0 }
def π_eraseScratch : BehaviorSet StoreTrace → BehaviorSet StoreTrace :=
  BehaviorSet.map eraseScratchTrace

theorem π_eraseScratch_monotone : Monotone π_eraseScratch :=
  BehaviorSet.map_monotone eraseScratchTrace

def VolatileZeroedSpec : Spec (BehaviorSet StoreTrace) :=
  BehaviorSet.allSpec (fun t => t.volatileOut = 0)
def NonVolatileZeroedSpec : Spec (BehaviorSet StoreTrace) :=
  BehaviorSet.allSpec (fun t => t.scratch = 0)
def unzeroedScratchBeh : BehaviorSet StoreTrace := (· = ⟨42, 0, false⟩)

theorem unzeroedScratch_violates_source_spec :
    ¬ NonVolatileZeroedSpec.holds unzeroedScratchBeh := by
  intro h; cases @h ⟨42, 0, false⟩ rfl

theorem volatileZeroed_holds_on_erased :
    VolatileZeroedSpec.holds (π_eraseScratch unzeroedScratchBeh) := by
  rintro _ ⟨_, rfl, rfl⟩; rfl

/-! ## 3. Concrete 2-Safety Constant-Time Hyperproperty -/

structure LeakageTrace where
  secret : Nat
  pub : Nat
  leakage : Nat
  isUB : Bool

def LeakageNoUB : Spec (BehaviorSet LeakageTrace) :=
  BehaviorSet.forbidSpec (fun t => t.isUB = true)
def ConstantTimeSpec : Spec (BehaviorSet LeakageTrace) :=
  BehaviorSet.twoSafetySpec (fun t₁ t₂ => t₁.pub = t₂.pub → t₁.leakage = t₂.leakage)

def ctHighBeh : BehaviorSet LeakageTrace :=
  fun t => t.leakage = t.pub + 1 ∧ t.isUB = false
def ctLowBeh : BehaviorSet LeakageTrace :=
  fun t => t.secret = 0 ∧ t.leakage = t.pub + 1 ∧ t.isUB = false

theorem ctLow_guardedRefines_ctHigh :
    GuardedRefines LeakageNoUB id ctLowBeh ctHighBeh :=
  fun _ _ ⟨_, hleak, hub⟩ => ⟨hleak, hub⟩

theorem ctHigh_is_constantTime : ConstantTimeSpec.holds ctHighBeh := by
  rintro _ _ ⟨h₁, _⟩ ⟨h₂, _⟩ hpub; rw [h₁, h₂, hpub]

theorem ctHigh_noUB : LeakageNoUB.holds ctHighBeh := by
  rintro _ ⟨_, hub⟩ h_bad; rw [hub] at h_bad; cases h_bad

theorem ctLow_is_constantTime : ConstantTimeSpec.holds ctLowBeh :=
  GuardedRefines.transfer ctLow_guardedRefines_ctHigh ctHigh_noUB
    ConstantTimeSpec ctHigh_is_constantTime

def leakyBeh : BehaviorSet LeakageTrace :=
  fun t => t.leakage = t.secret ∧ t.isUB = false

theorem leakyBeh_not_constantTime : ¬ ConstantTimeSpec.holds leakyBeh := by
  intro h_ct
  cases @h_ct ⟨0, 7, 0, false⟩ ⟨1, 7, 1, false⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ rfl

/-! ## 4. Safe Functional Preconditions vs. Misplaced Safety Preconditions -/

theorem safe_contractSpec_preserves_wellFormed
    {L : Language} (funcPre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    L.ContractSpec (fun _ => True) funcPre post ≤ L.WellFormed :=
  Language.contractSpec_safe_refines_wellFormed funcPre post

theorem misplaced_contractSpec_violates_wellFormed
    {L : Language} (funcPre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (q : L.Query) (h_not_pre : ¬ funcPre q) :
    ¬ (L.ContractSpec funcPre (fun _ => True) post ≤ L.WellFormed) := by
  intro h_ref
  exact h_not_pre
    ((Language.refines_wellFormed_iff (L.ContractSpec funcPre (fun _ => True) post)).mp h_ref q)

def clampOrderedPre (q : DivQuery) : Prop := q.1 ≤ q.2
def clampBoundsPost (q : DivQuery) (out : Nat) : Prop := q.1 ≤ out ∧ out ≤ q.2

theorem concrete_safe_clamp_preserves_wellFormed :
    ToyMirLang.ContractSpec (fun _ => True) clampOrderedPre clampBoundsPost ≤
      ToyMirLang.WellFormed :=
  safe_contractSpec_preserves_wellFormed (L := ToyMirLang) clampOrderedPre clampBoundsPost

theorem concrete_misplaced_clamp_violates_wellFormed :
    ¬ (ToyMirLang.ContractSpec clampOrderedPre (fun _ => True) clampBoundsPost ≤
        ToyMirLang.WellFormed) :=
  misplaced_contractSpec_violates_wellFormed (L := ToyMirLang)
    clampOrderedPre clampBoundsPost (10, 3) (by unfold clampOrderedPre; dsimp; omega)

/-! ## 5. Per-Query `Partial` Witness and Negative Control on `ToyMirLang` -/

def safeDivContract : ToyMirLang.Behavior :=
  ToyMirLang.ContractSpec (fun _ => True) (fun q => q.2 ≠ 0) (fun q out => out = q.1 / q.2)

theorem verifQueryNormalize_safeDiv_refines_contract :
    ToyMirLang.sem (verifQueryNormalize .safeDiv) ≤ safeDivContract :=
  fun _ _ => ⟨⟨trivial, trivial⟩, fun _ ho _ => ho.elim id id⟩

theorem safeDiv_verified_wellFormed :
    ToyMirLang.sem .safeDiv ≤ ToyMirLang.WellFormed ∧
    ToyTargetLang.sem (compileQueryLeft .safeDiv) ≤ safeDivContract :=
  verify_through_passes
    (L_src := ToyMirLang) (L_v := ToyMirLang) (L_tgt := ToyTargetLang)
    monotone_id monotone_id
    (compileQueryLeft_compiles .safeDiv)
    (verifQueryNormalize_abstracts .safeDiv)
    verifQueryNormalize_safeDiv_refines_contract
    (safe_contractSpec_preserves_wellFormed (L := ToyMirLang)
      (fun q => q.2 ≠ 0) (fun q out => out = q.1 / q.2))

theorem unsafeDiv_violates_wellFormed :
    ¬ (ToyMirLang.sem .div ≤ ToyMirLang.WellFormed) := by
  intro h_wf
  exact ((Language.refines_wellFormed_iff (L := ToyMirLang)
    (ToyMirLang.sem .div)).mp h_wf (10, 0)) rfl

end Anneal.Tests.ConcreteYDiagram
