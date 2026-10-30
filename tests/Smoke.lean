import Anneal

namespace AnnealTests

open Trusted.Refinement

theorem smoke_claim : True := Anneal.trivial_witness

def singletonNatBeh (n : Nat) : BehaviorSet Nat := (· = n)
def natSem : Semantics Nat (BehaviorSet Nat) := singletonNatBeh
def natNoUB : Spec (BehaviorSet Nat) := BehaviorSet.forbidSpec (· = 0)
def natSpec (expected : Nat) : Spec (BehaviorSet Nat) := BehaviorSet.allSpec (· = expected)

/-- Layer 1A claim theorem whose statement references only `Trusted.Refinement`
while its proof exercises `Anneal.Refinement.anneal_is_correct`. -/
theorem layer1a_claim_origin_check :
    (Spec.pullback (π := id) (fun _ _ h => h) (natSpec 4)).holds (natSem 4) :=
  Anneal.Refinement.anneal_is_correct
    natSem natSem natSem natNoUB natNoUB
    some id id Anneal.Refinement.monotone_id
    (fun p => Anneal.Refinement.GuardedRefines.refl natNoUB (natSem p))
    4 4 4 id rfl
    (Anneal.Refinement.GuardedRefines.refl natNoUB (natSem 4))
    (fun _ h => h)
    (fun _ hx h0 => by rw [hx] at h0; cases h0)
    (Spec.pullback (π := id) (fun _ _ h => h) (natSpec 4))
    (fun _ hx => hx)

abbrev smokeIdLang : Language where
  Prog := Nat
  Query := Unit
  Out := Nat
  sem n _ := Partial.pure (· = n)

abbrev smokeIdCompiler : Compiler smokeIdLang smokeIdLang where
  compile := id
  π := id

instance : TrustedAssumption Prop where
  meaning p := p

def strictNoAssumptionPolicy : TrustPolicy Prop where
  isAllowed _ := False

/-- Layer 1A trust-policy verification envelope origin check (`DESIGN.md`). -/
theorem layer1a_trust_policy_origin_check :
    VerificationResultOn smokeIdCompiler strictNoAssumptionPolicy [] (7 : Nat)
      (fun _ => True) [smokeIdLang.Spec (fun _ (out : Nat) => out = 7)] :=
  Anneal.Refinement.verifyResultOn_single
    trivial
    (fun _ => ⟨Anneal.Refinement.monotone_id, fun _ _ => ⟨trivial, fun _ h => h⟩⟩)
    (fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    (fun _ _ => ⟨trivial, fun _ _ => trivial⟩)

end AnnealTests
