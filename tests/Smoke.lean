import Anneal

namespace AnnealTests

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

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

/-- Layer 1B claim theorem whose statement references only `Trusted.Refinement`,
`Trusted.Effect`, and `Trusted.ITree` (`toPartial` and `≤`), while its proof
exercises `Anneal.ITree.WeakRef.toPartial_le`, `Anneal.ITree.WeakRef.refl`, and
`Anneal.ITreeWP.dwlp_pure_adequacy`. -/
theorem layer1b_itree_claim_origin_check :
    (ITree.ret (E := FailE FailureKind) (7 : Nat)).toPartial ≤
      (ITree.ret (E := FailE FailureKind) (7 : Nat)).toPartial ∧
    TreeSafe (ITree.ret (E := FailE FailureKind) (7 : Nat)) :=
  ⟨Anneal.ITree.WeakRef.toPartial_le (Anneal.ITree.WeakRef.refl _),
   (Anneal.ITreeWP.dwlp_pure_adequacy
     (ewp := Anneal.EffectWP.failWP PUnit FailureKind)
     (t := ITree.ret (7 : Nat))
     (post := fun r => r = 7)
     ((Anneal.ITreeWP.DWLP.ret_iff
       (Anneal.EffectWP.failWP PUnit FailureKind) 7 (fun r _ => r = 7)
       PUnit.unit).mpr rfl)).1⟩

/-- Self-contained `CapturedMir` body `fn const_seven() -> u32 { 7 }` defined
using only `Trusted.*` and `Init.*` constants. -/
def smokeConstSevenBody : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir where
  defPath := "smoke::const_seven"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls :=
    [{ mutability := .mut
       ty := { kind := .uint .u32, layoutIdx := 0 }
       debugName := some "_0" }]
  basicBlocks :=
    [{ statements :=
         [{ kind :=
              .assign
                { local_ := 0, projection := [] }
                (.use (.constant
                  { ty := { kind := .uint .u32, layoutIdx := 0 }
                    val := .scalar (.int ⟨7, 4⟩) }))
            span := "smoke.rs:1:1" }]
       terminator := { kind := .return_, span := "smoke.rs:1:1" }
       isCleanup := false }]
  fnAbi := {
    args := []
    ret := {
      layout := {
        size := ⟨4⟩
        align := ⟨4⟩
        backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩)
        fields := .primitive
        variants := .single 0
        isUninhabited := false
      }
      mode := .direct
    }
    conv := .rust
    canUnwind := false
  }
  layouts := {
    pointerBits := 64
    isLittleEndian := true
    entries :=
      [{ size := ⟨4⟩
         align := ⟨4⟩
         backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩)
         fields := .primitive
         variants := .single 0
         isUninhabited := false }]
  }
  allocations := []

def smokeConstSevenClaim : Claim where
  body := smokeConstSevenBody
  pre args := args = []
  post _ ret := ret = .scalar ⟨7, 4⟩

def smokeConstSevenStatefulClaim : StatefulClaim where
  body := smokeConstSevenBody
  pre args mem := args = [] ∧ mem = emptyMemory
  post _ _ ret mem' := ret = .scalar ⟨7, 4⟩ ∧ mem' = emptyMemory

def smokeConstSevenTraceClaim : TraceClaim where
  body := smokeConstSevenBody
  pre args mem := args = [] ∧ mem = emptyMemory
  post _ _ tr out := tr = [] ∧ out = .normal (.scalar ⟨7, 4⟩, emptyMemory)

def smokeConstSevenTotalClaim : TotalClaim where
  body := smokeConstSevenBody
  pre args mem := args = [] ∧ mem = emptyMemory
  post _ _ ret mem' := ret = .scalar ⟨7, 4⟩ ∧ mem' = emptyMemory

def smokeConstSevenModularClaim : ModularClaim where
  body := smokeConstSevenBody
  envAssumed _ := True
  pre args mem := args = [] ∧ mem = emptyMemory
  post _ _ ret mem' := ret = .scalar ⟨7, 4⟩ ∧ mem' = emptyMemory

def smokeConstSevenEquivClaim : StatefulEquivClaim where
  implBody := smokeConstSevenBody
  specBody := smokeConstSevenBody
  pre args mem := args = [] ∧ mem = emptyMemory
  post _ _ ret mem' := ret = .scalar ⟨7, 4⟩ ∧ mem' = emptyMemory

def smokeCrateClaim : CrateClaim where
  crateName := "smoke"
  mirDialect := "V2026_06_01"
  items :=
    [{ identity := {
         defPath := "smoke::const_seven"
         mirDialect := "V2026_06_01"
         mirModuleSha256 := "0000000000000000000000000000000000000000000000000000000000000000"
       }
       certificate := VerificationResult smokeConstSevenClaim }]

theorem mir_verification_result_origin_check :
    VerificationResult smokeConstSevenClaim :=
  Anneal.Rustc.V2026_06_01.Lower.verifyMirBounded smokeConstSevenClaim 4
    (by
      rintro _ rfl retVal _ h_out
      injection h_out with h_pair; injection h_pair with h_ret _
      exact h_ret.symm)

theorem mir_stateful_verification_result_origin_check :
    StatefulVerificationResult smokeConstSevenStatefulClaim :=
  Anneal.Rustc.V2026_06_01.Lower.verifyStatefulMirBounded
    smokeConstSevenStatefulClaim 4
    (by
      rintro _ _ ⟨rfl, rfl⟩ retVal mem' h_out
      injection h_out with h_pair; injection h_pair with h_ret h_m
      exact ⟨h_ret.symm, h_m.symm⟩)

theorem mir_trace_verification_result_origin_check :
    TraceVerificationResult smokeConstSevenTraceClaim :=
  Anneal.Rustc.V2026_06_01.Lower.verifyTraceMirBounded
    smokeConstSevenTraceClaim 4
    (by rintro _ _ ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩)

theorem mir_total_verification_result_origin_check :
    TotalVerificationResult smokeConstSevenTotalClaim :=
  Anneal.Rustc.V2026_06_01.Lower.verifyTotalMirBounded
    smokeConstSevenTotalClaim 4
    (by rintro _ _ ⟨rfl, rfl⟩; exact ⟨.scalar ⟨7, 4⟩, emptyMemory, rfl, rfl, rfl⟩)

theorem mir_modular_verification_result_origin_check :
    ModularVerificationResult smokeConstSevenModularClaim :=
  ⟨fun h _ =>
    (Anneal.Rustc.V2026_06_01.Lower.verifyModularMirBounded
      { pre := fun _ => False, post := fun _ _ => False }
      smokeConstSevenBody
      (fun args mem => args = [] ∧ mem = emptyMemory)
      (fun _ _ ret mem' => ret = .scalar ⟨7, 4⟩ ∧ mem' = emptyMemory)
      4
      (by
        rintro _ _ ⟨rfl, rfl⟩ retVal mem' h_out
        injection h_out with h_pair; injection h_pair with h_ret h_m
        exact ⟨h_ret.symm, h_m.symm⟩)).proof
      h
      (fun _ _ h_abs => False.elim h_abs)⟩

theorem mir_stateful_equiv_verification_result_origin_check :
    StatefulEquivVerificationResult smokeConstSevenEquivClaim :=
  Anneal.Rustc.V2026_06_01.Lower.verifyStatefulEquivMirBounded
    smokeConstSevenEquivClaim 4 4
    (fun _ _ => (.scalar ⟨7, 4⟩, emptyMemory))
    (by rintro _ _ ⟨rfl, rfl⟩; exact ⟨rfl, rfl, rfl⟩)
    (by rintro _ _ ⟨rfl, rfl⟩; rfl)

theorem mir_crate_verification_result_origin_check :
    CrateVerificationResult smokeCrateClaim :=
  Anneal.Rustc.V2026_06_01.Lower.verifyCrateRollup
    smokeCrateClaim
    (by intro h; nomatch h)
    ⟨mir_verification_result_origin_check, trivial⟩

end AnnealTests
