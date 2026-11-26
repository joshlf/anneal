import Anneal.OleanSpecStrengthAuditor
import Lean.Data.Json

namespace Anneal.OleanSpecStrengthAuditorTests

open Trusted.ITree
open Trusted.MirSemantics
open Trusted.VerificationResult
open Anneal.OleanSpecStrengthAuditor

/-!
# Episode 2 Specification-Strength & 9-Vector Regression Suite

Exercises:
1. Constructive `#print axioms` checks (`[propext, Quot.sound]` or `{}`, zero `Classical.choice`)
   for `Anneal.OleanSpecStrengthAuditor`.
2. Type-level proofs for `V8` (vacuous precondition & modular rely), `V9a` (trivial postcondition),
   `V9b` (unimplementable postcondition), `K1` (realizable-input kills), `S5` (input sensitivity vs.
   singleton precondition and input-independent postcondition), `fxfs_storage_boundary`,
   `fuchsia_usercopy`, and the `weak_vmo_subslice_upper_bound_only` contrast.
3. `#guard_msgs`-pinned live regressions compiled and executed directly against the production
   `trusted/audit/OleanEnvAuditor.lean` module covering all 9 escape vectors (`V1`–`V9`) plus
   every B1..A4 spec-gate bypass (`R6`, `R7`, `R8`, `R11`, `A1-2`, `A1-4`, `A1-6`, `S3a/b`, `S5`,
   `A2-4b`, `A3-3a..e`, `B4-3`, `B4-4`, `B4-5`, `W6`, `B4-6`, `A4-3a..c`, `A4-5a/b`, `A4-7`, and
   `Classical.choice` certificate rejection).
-/

/-! ## Part 1: Constructive `#print axioms` Checks (Zero `Classical.choice`) -/

/-- info: 'Anneal.OleanSpecStrengthAuditor.fxfsVmoSubsliceMultiCert' does not depend on any axioms -/
#guard_msgs in
#print axioms fxfsVmoSubsliceMultiCert

/-- info: 'Anneal.OleanSpecStrengthAuditor.fxfsVmoSubslice_deterministic' does not depend on any axioms -/
#guard_msgs in
#print axioms fxfsVmoSubslice_deterministic

/-- info: 'Anneal.OleanSpecStrengthAuditor.fxfsVmoSubsliceInputSensitive' does not depend on any axioms -/
#guard_msgs in
#print axioms fxfsVmoSubsliceInputSensitive

/-- info: 'Anneal.OleanSpecStrengthAuditor.fuchsiaUsercopyCopyinMultiCert' does not depend on any axioms -/
#guard_msgs in
#print axioms fuchsiaUsercopyCopyinMultiCert

/-- info: 'Anneal.OleanSpecStrengthAuditor.fuchsiaUsercopyCopyin_deterministic' does not depend on any axioms -/
#guard_msgs in
#print axioms fuchsiaUsercopyCopyin_deterministic

/-- info: 'Anneal.OleanSpecStrengthAuditor.fuchsiaUsercopyCopyinInputSensitive' does not depend on any axioms -/
#guard_msgs in
#print axioms fuchsiaUsercopyCopyinInputSensitive

/-- info: 'Anneal.OleanSpecStrengthAuditor.fuchsiaUsercopyCopyinModularDirectMultiCert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fuchsiaUsercopyCopyinModularDirectMultiCert

/-- info: 'Anneal.OleanSpecStrengthAuditor.fuchsiaUsercopyCopyinModularDirectDetCert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fuchsiaUsercopyCopyinModularDirectDetCert

/--
info: 'Anneal.OleanSpecStrengthAuditor.fuchsiaUsercopyCopyinModularDirectInputSensitiveCert' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms fuchsiaUsercopyCopyinModularDirectInputSensitiveCert

/-- info: 'Anneal.OleanSpecStrengthAuditor.weakVmoSubsliceSingleCert' does not depend on any axioms -/
#guard_msgs in
#print axioms weakVmoSubsliceSingleCert

/-- info: 'Anneal.OleanSpecStrengthAuditor.truncatedVmoSubsliceMutant_survives_weak_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms truncatedVmoSubsliceMutant_survives_weak_spec

/-- info: 'Anneal.OleanSpecStrengthAuditor.weak_vmo_subslice_not_deterministic' does not depend on any axioms -/
#guard_msgs in
#print axioms weak_vmo_subslice_not_deterministic

/-- info: 'Anneal.OleanSpecStrengthAuditor.no_cert_of_vacuous_pre' does not depend on any axioms -/
#guard_msgs in
#print axioms no_cert_of_vacuous_pre

/-- info: 'Anneal.OleanSpecStrengthAuditor.no_cert_of_trivial_post' does not depend on any axioms -/
#guard_msgs in
#print axioms no_cert_of_trivial_post

/-- info: 'Anneal.OleanSpecStrengthAuditor.no_cert_of_unimplementable_post' does not depend on any axioms -/
#guard_msgs in
#print axioms no_cert_of_unimplementable_post

/-- info: 'Anneal.OleanSpecStrengthAuditor.no_modular_cert_of_vacuous_envAssumed' does not depend on any axioms -/
#guard_msgs in
#print axioms no_modular_cert_of_vacuous_envAssumed

/-- info: 'Anneal.OleanSpecStrengthAuditor.no_input_sensitive_cert_of_singleton_req' does not depend on any axioms -/
#guard_msgs in
#print axioms no_input_sensitive_cert_of_singleton_req

/-- info: 'Anneal.OleanSpecStrengthAuditor.no_input_sensitive_cert_of_input_independent_ens' does not depend on any axioms -/
#guard_msgs in
#print axioms no_input_sensitive_cert_of_input_independent_ens

/-! ## Part 2: Type-Level `V8` / `V9` / `K1` / `S5` / Real-Spec & Weak-Spec Proofs -/

theorem testV8_vacuousPre_impossible :
    SpecStrengthCert (fun (_ : Nat) => False) (fun (n y : Nat) => y = n) → False :=
  no_cert_of_vacuous_pre (fun _ h => h)

theorem testV8_vacuousModularRely_impossible :
    ModularSpecStrengthCert (fun _ => False) fuchsiaUsercopyCopyinPre fuchsiaUsercopyCopyinPost → False :=
  no_modular_cert_of_vacuous_envAssumed (fun _ h => h)

theorem testV9a_trivialPost_impossible :
    SpecStrengthCert (fun (_ : Nat) => True) (fun (_ _ : Nat) => True) → False :=
  no_cert_of_trivial_post (fun _ _ => trivial)

theorem testV9b_unimplementablePost_impossible :
    SpecStrengthCert (fun (_ : Nat) => True) (fun (_ _ : Nat) => False) → False :=
  no_cert_of_unimplementable_post (fun _ _ h => h)

/-- `K1`: A mutant kill is impossible at an input where the spec accepts no output. -/
theorem testNoVacuousKillAtUnimplementableInput :
    ∀ k : NamedMutantKill (fun (_ : Nat) => True) (fun (n y : Nat) => n = 0 ∧ y = 1),
      k.input = 1 → False := by
  intro k hIn
  exact no_kill_at_unimplementable_input (x := 1) (fun _ h => Nat.noConfusion h.1) k hIn

/-- `K1`: A kill is only constructible at a realizable input. -/
def testKillOnlyAtRealizableInput :
    NamedMutantKill (fun (_ : Nat) => True) (fun (n y : Nat) => n = 0 ∧ y = 1) where
  name := "realizable_zero"
  category := .wrongReturn
  input := 0
  inputValid := trivial
  referenceOutput := 1
  referenceAccepted := ⟨rfl, rfl⟩
  mutantOutput := 2
  mutantRejected := by intro h; exact absurd h.2 (by decide)

/-- `S5`: A single-point precondition (`n = 5`) still inhabits `DeterministicSpecCert`... -/
def testSinglePointSpecIsDeterministic :
    DeterministicSpecCert (fun n : Nat => n = 5) (fun n y : Nat => y = n + 1) where
  witnessInput := 5
  witnessValid := rfl
  referenceOutput := 6
  referenceAccepted := rfl
  mutantOutput := 7
  mutantDiffers := by decide
  realizable := fun n _ => ⟨n + 1, rfl⟩
  uniqueOutput := fun _ _ _ _ h1 h2 => h1.trans h2.symm

/-- `S5a`: ...yet provably CANNOT inhabit `InputSensitiveSpecCert`. -/
theorem testSinglePointSpecNotInputSensitive :
    InputSensitiveSpecCert (fun n : Nat => n = 5) (fun n y : Nat => y = n + 1) → False :=
  no_input_sensitive_cert_of_singleton_req (fun _ _ h1 h2 => h1.trans h2.symm)

/-- `S5b`: An input-independent postcondition (`y = 42`) provably CANNOT inhabit `InputSensitiveSpecCert`. -/
theorem testInputIndependentSpecNotInputSensitive :
    InputSensitiveSpecCert (fun _ : Nat => True) (fun _ y : Nat => y = 42) → False :=
  no_input_sensitive_cert_of_input_independent_ens (fun _ _ _ => Iff.rfl)

/-- Every deviating return value on any valid `fxfs` input is rejected by `fxfsVmoSubslice_deterministic`. -/
theorem testFxfsEveryDeviationKilled (args : List Value) (hPre : fxfsVmoSubslicePre args)
    (yRef yMut : Value) (hRef : fxfsVmoSubslicePost args yRef) (hne : yMut ≠ yRef) :
    ¬ fxfsVmoSubslicePost args yMut :=
  fxfsVmoSubslice_deterministic.killsEveryDeviation args hPre yRef yMut hRef hne

/-- Every deviating `(ret, mem')` on any valid `fuchsia_usercopy` input is rejected. -/
theorem testFuchsiaEveryDeviationKilled (args : List Value) (mem : Memory)
    (hPre : fuchsiaUsercopyCopyinPre args mem)
    (yRef yMut : Value × Memory)
    (hRef : fuchsiaUsercopyCopyinPost args mem yRef.1 yRef.2)
    (hne : yMut ≠ yRef) :
    ¬ fuchsiaUsercopyCopyinPost args mem yMut.1 yMut.2 :=
  fuchsiaUsercopyCopyin_deterministic.killsEveryDeviation (args, mem) hPre yRef yMut hRef hne

theorem testFxfsCategoriesCovered :
    fxfsVmoSubsliceMultiCert.coversCategory .wrongReturn = true ∧
    fxfsVmoSubsliceMultiCert.coversCategory .wrapOverflow = true ∧
    fxfsVmoSubsliceMultiCert.coversCategory .truncatedLength = true ∧
    fxfsVmoSubsliceMultiCert.coversCategory .swappedByteOrder = true ∧
    fxfsVmoSubsliceMultiCert.coversCategory .offByOneScalar = true ∧
    fxfsVmoSubsliceMultiCert.coversCategory .unpreservedFrame = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem testFuchsiaCategoriesCovered :
    fuchsiaUsercopyCopyinModularDirectMultiCert.coversCategory .wrongBranchTag = true ∧
    fuchsiaUsercopyCopyinModularDirectMultiCert.coversCategory .truncatedLength = true ∧
    fuchsiaUsercopyCopyinModularDirectMultiCert.coversCategory .offByOneScalar = true ∧
    fuchsiaUsercopyCopyinModularDirectMultiCert.coversCategory .unpreservedFrame = true ∧
    fuchsiaUsercopyCopyinModularDirectMultiCert.coversCategory .swappedByteOrder = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Part 3: Live Production `OleanEnvAuditor.lean` Regressions (`V1`–`V9` + B1..A4 Bypasses) -/

private def liveHarnessSource : String :=
r##"import OleanEnvAuditor
import Anneal.OleanSpecStrengthAuditor
import Lean.Elab.Command
import Lean.Meta.Basic
import Lean.Meta.WHNF

open Lean
open Trusted.ITree
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.MirSemantics
open Trusted.VerificationResult
open Anneal.OleanSpecStrengthAuditor
open OleanEnvAuditor

set_option linter.unusedVariables false
set_option linter.deprecated false
set_option warn.classDefReducibility false

/-! ### Helpers -/

def tagsOf (vs : Array Violation) : Array String :=
  let s : Std.HashSet String := vs.foldl (fun a v => a.insert v.tag) {}
  s.toArray.qsort (· < ·)

def fmtTags (label : String) (vs : Array Violation) : String :=
  s!"{label}: {tagsOf vs}"

/-! ### Vector V1..V6 Declarations -/

theorem v1_direct_sorry : True := by sorry

theorem v2_tactic_sorryAx : True := by
  exact sorryAx True false

axiom v3_custom_axiom : True
private axiom v3_private_axiom : True
theorem v3_uses_custom : True := v3_custom_axiom
theorem v3_uses_private : True := v3_private_axiom
def v3_trust_compiler : Bool := Lean.reduceBool true

theorem v4_native_decide : (2 + 2 == 4) = true := by native_decide

partial def v5_partial_loop (n : Nat) : Nat := v5_partial_loop (n + 1)
def v5_safe_gcd : Nat → Nat → Nat
  | 0, b => b
  | a + 1, b => v5_safe_gcd (b % (a + 1)) (a + 1)
termination_by a _ => a
decreasing_by exact Nat.mod_lt b (Nat.succ_pos a)

unsafe def v6_unsafe_fn (n : Nat) : Nat := n
def v6_ib_impl (n : Nat) : Nat := n + 1
@[implemented_by v6_ib_impl] def v6_implemented_by (n : Nat) : Nat := n
@[extern "anneal_test_c_sym"] def v6_extern_fn (n : Nat) : Nat := n
@[export anneal_test_exp_sym] def v6_export_fn (n : Nat) : Nat := n
def v6_csimp_src (a b : Nat) : Nat := a + b
def v6_csimp_alt (a b : Nat) : Nat := a + b
@[csimp] theorem v6_csimp_thm : @v6_csimp_src = @v6_csimp_alt := by
  funext a b; rfl
def v6_uses_csimp (a b : Nat) : Nat := v6_csimp_src a b
initialize v6_init_flag : Bool ← pure true

/-! ### Minimal CapturedMir & Claims for Claim-Bound Tests (R11 / A1-6 / A2-4b / V8 / V9) -/

def u64MirTy : Ty := { kind := .uint .u64, layoutIdx := 0 }

def defaultU64Layout : TypeLayout := {
  size := { bytes := 8 }, align := { bytes := 8 }
  backendRepr := .memory, fields := .primitive, variants := .single 0, isUninhabited := false
}

def defaultFnAbi : FnAbi := {
  args := [], ret := { layout := defaultU64Layout, mode := .direct }, conv := .rust, canUnwind := false
}

def ret10Block : BasicBlockData := {
  statements :=
    [ { kind := .assign { local_ := 0, projection := [] }
          (.use (.constant { ty := u64MirTy, val := .scalar (.int { bits := 10, sizeBytes := 8 }) }))
        span := "OleanSpecStrengthAuditorTests.lean" } ]
  terminator := { kind := .return_, span := "OleanSpecStrengthAuditorTests.lean" }
  isCleanup := false
}

def ret10Mir : CapturedMir := {
  defPath := "ep2::ret10"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls :=
    [ { mutability := .mut, ty := u64MirTy, debugName := none } ]
  basicBlocks := [ret10Block]
  fnAbi := defaultFnAbi
  layouts := emptyLayoutTable
  allocations := []
}

def ret10Pre (args : List Value) : Prop :=
  args = [.scalar { bits := 0, sizeBytes := 8 }] ∨ args = [.scalar { bits := 1, sizeBytes := 8 }]

def ret10Post (_args : List Value) (ret : Value) : Prop :=
  ret = .scalar { bits := 10, sizeBytes := 8 }

def ret10InitMem : Memory := (initMachineState ret10Mir []).memory

def ret10Claim : Claim :=
  { body := ret10Mir, pre := ret10Pre, post := ret10Post }

def ret10StatefulClaim : StatefulClaim :=
  { body := ret10Mir
    pre := fun args mem => ret10Pre args ∧ mem = ret10InitMem
    post := fun args mem ret mem' => ret10Post args ret ∧ mem' = mem }

def ret10TotalClaim : TotalClaim :=
  { body := ret10Mir
    pre := fun args mem => ret10Pre args ∧ mem = ret10InitMem
    post := fun args mem ret mem' => ret10Post args ret ∧ mem' = mem }

def ret10ModularClaim : ModularClaim :=
  { body := ret10Mir
    envAssumed := fuchsiaUsercopyCopyinRely
    pre := fun args mem => ret10Pre args ∧ mem = ret10InitMem
    post := fun args mem ret mem' => ret10Post args ret ∧ mem' = mem }

private theorem cofix_unfold {E : Trusted.Effect.Effect.{0}} {R S : Type}
    (step : S → ITreeF E R S) (s : S) :
    ITree.cofix step s = ITree.fold ((step s).map (ITree.cofix step)) := by
  rw [← ITree.fold_observe (ITree.cofix step s), ITree.observe_cofix]

private theorem mirTree_ret10_eq (args : List Value) :
    mirStatefulTreeWithCallees ret10Mir args ret10InitMem .nil =
      ITree.tau (ITree.ret (.normal (.scalar { bits := 10, sizeBytes := 8 }, ret10InitMem))) := by
  rw [mirStatefulTreeWithCallees, mirTree, cofix_unfold]
  have h1 : stepMirState ret10Mir
      (.running (initMachineStateWithMemoryAndCallees ret10Mir args ret10InitMem .nil)) =
      .tau (.running {
        frame := { blockIdx := 0, stmtIdx := 1, locals := [.init (.scalar { bits := 10, sizeBytes := 8 })] }
        memory := ret10InitMem }) := rfl
  rw [h1]
  change ITree.tau (ITree.cofix (stepMirState ret10Mir) _) = _
  congr 1
  rw [cofix_unfold]
  have h2 : stepMirState ret10Mir (.running {
        frame := { blockIdx := 0, stmtIdx := 1, locals := [.init (.scalar { bits := 10, sizeBytes := 8 })] }
        memory := ret10InitMem }) =
      .ret (.normal (.scalar { bits := 10, sizeBytes := 8 }, ret10InitMem)) := rfl
  rw [h2]
  rfl

private theorem tauStar_tau1_ret {E : Trusted.Effect.Effect.{0}} {R : Type} {r : R} {u : ITree E R}
    (h : TauStar (ITree.tau (ITree.ret (E := E) r)) u) :
    u = ITree.tau (ITree.ret r) ∨ u = ITree.ret r := by
  cases h with
  | refl => exact Or.inl rfl
  | step ho1 h1 =>
    rw [ITree.observe_tau] at ho1; injection ho1 with e1; subst e1
    cases h1 with
    | refl => exact Or.inr rfl
    | step ho2 _ => rw [ITree.observe_ret] at ho2; nomatch ho2

private theorem reaches_tau1_ret {E : Trusted.Effect.Effect.{0}} {R : Type}
    [Trusted.Effect.FaultEffect E] {r : R} {tr : List (Trusted.Effect.Event E)} {u : ITree E R}
    (h : Reaches (ITree.tau (ITree.ret (E := E) r)) tr u) :
    tr = [] ∧ (u = ITree.tau (ITree.ret r) ∨ u = ITree.ret r) := by
  cases h with
  | refl => exact ⟨rfl, Or.inl rfl⟩
  | tau ho1 h1 =>
    rw [ITree.observe_tau] at ho1; injection ho1 with e1; subst e1
    cases h1 with
    | refl => exact ⟨rfl, Or.inr rfl⟩
    | tau ho2 _ => rw [ITree.observe_ret] at ho2; nomatch ho2
    | vis ho2 _ _ _ => rw [ITree.observe_ret] at ho2; nomatch ho2
  | vis ho1 _ _ _ => rw [ITree.observe_tau] at ho1; nomatch ho1

private theorem treeSafe_tau1_ret {E : Trusted.Effect.Effect.{0}} {R : Type}
    [Trusted.Effect.FaultEffect E] (r : R) :
    TreeSafe (ITree.tau (ITree.ret (E := E) r)) := by
  intro tr u hr ⟨t', i, k, ht, ho, _⟩
  have ⟨_, hu⟩ := reaches_tau1_ret hr
  rcases hu with rfl | rfl
  · rcases tauStar_tau1_ret ht with rfl | rfl
    · rw [ITree.observe_tau] at ho; nomatch ho
    · rw [ITree.observe_ret] at ho; nomatch ho
  · cases ht with
    | refl => rw [ITree.observe_ret] at ho; nomatch ho
    | step h1 _ => rw [ITree.observe_ret] at h1; nomatch h1

private theorem reachesRet_tau1_ret {E : Trusted.Effect.Effect.{0}} {R : Type}
    [Trusted.Effect.FaultEffect E] {r ans : R} {tr : List (Trusted.Effect.Event E)}
    (h : ReachesRet (ITree.tau (ITree.ret (E := E) r)) tr ans) : ans = r := by
  rcases h with ⟨u, hr, ho⟩
  have ⟨_, hu⟩ := reaches_tau1_ret hr
  rcases hu with rfl | rfl
  · rw [ITree.observe_tau] at ho; nomatch ho
  · rw [ITree.observe_ret] at ho; injection ho with e; exact e.symm

private theorem productive_tau1_ret {E : Trusted.Effect.Effect.{0}} {R : Type}
    [Trusted.Effect.FaultEffect E] (r : R) :
    Productive (ITree.tau (ITree.ret (E := E) r)) := by
  intro tr u hr
  have ⟨_, hu⟩ := reaches_tau1_ret hr
  refine ⟨ITree.ret r, ?_, fun w hw => by rw [ITree.observe_ret] at hw; nomatch hw⟩
  rcases hu with rfl | rfl
  · exact TauStar.step (ITree.observe_tau _) (TauStar.refl _)
  · exact TauStar.refl _

private theorem not_mayDiverge_tau1_ret {E : Trusted.Effect.Effect.{0}} {R : Type}
    [Trusted.Effect.FaultEffect E] (r : R) :
    ¬ MayDiverge (ITree.tau (ITree.ret (E := E) r)) := by
  intro ⟨tr, u, hr, hd⟩
  have ⟨_, hu⟩ := reaches_tau1_ret hr
  have hRetNotDiv : ¬ Diverges (ITree.ret (E := E) r) := by
    intro h; rw [Diverges.eq_unfold, ITree.observe_ret] at h; exact h
  have hTau1NotDiv : ¬ Diverges (ITree.tau (ITree.ret (E := E) r)) := by
    intro h; rw [Diverges.eq_unfold, ITree.observe_tau] at h; exact hRetNotDiv h
  rcases hu with rfl | rfl
  · exact hTau1NotDiv hd
  · exact hRetNotDiv hd

private theorem interp_tau1_ret (h : ExternalCallHandler) (out : MirOutcome) :
    ITree.interp (handleMirExternalCalls h)
      (ITree.tau (ITree.ret (E := MirEffect) out)) =
      ITree.tau (ITree.ret (E := MirClosedEffect) out) := by
  rw [ITree.interp, cofix_unfold]
  simp only [ITree.interpStep, ITree.observe_tau, ITreeF.map]
  change ITree.tau (ITree.cofix (ITree.interpStep (handleMirExternalCalls h)) (.inl (ITree.ret out))) = _
  congr 1
  rw [cofix_unfold]
  simp only [ITree.interpStep, ITree.observe_ret, ITreeF.map]
  rfl

theorem ret10Claim_verified : VerificationResult ret10Claim := by
  refine ⟨fun args _ => ?_⟩
  have hTree : mirCallTreeWithCallees ret10Mir args .nil =
      ITree.tau (ITree.ret (.normal (.scalar { bits := 10, sizeBytes := 8 }, ret10InitMem))) :=
    mirTree_ret10_eq args
  refine ⟨?_, ?_⟩
  · dsimp [MirExecPartialWithCallees, ITree.toPartial, ret10Claim]; rw [hTree]; exact treeSafe_tau1_ret _
  · intro outPair hRet _ retVal mem' hNorm
    dsimp [MirExecPartialWithCallees, ITree.toPartial, ret10Claim] at hRet ⊢
    rw [hTree] at hRet
    have hOut := reachesRet_tau1_ret hRet
    rw [hOut] at hNorm
    injection hNorm with hPair
    injection hPair with hVal _
    exact hVal.symm

theorem ret10StatefulClaim_verified : StatefulVerificationResult ret10StatefulClaim := by
  refine ⟨fun args mem hPre => ?_⟩
  have hMem : mem = ret10InitMem := hPre.2
  subst hMem
  have hTree := mirTree_ret10_eq args
  refine ⟨?_, ?_⟩
  · dsimp [MirStatefulExecPartialWithCallees, ITree.toPartial, ret10StatefulClaim]; rw [hTree]; exact treeSafe_tau1_ret _
  · intro outPair hRet _ retVal mem' hNorm
    dsimp [MirStatefulExecPartialWithCallees, ITree.toPartial, ret10StatefulClaim] at hRet ⊢
    rw [hTree] at hRet
    have hOut := reachesRet_tau1_ret hRet
    rw [hOut] at hNorm
    injection hNorm with hPair
    injection hPair with hVal hMemEq
    exact ⟨hVal.symm, hMemEq.symm⟩

theorem ret10TotalClaim_verified : TotalVerificationResult ret10TotalClaim := by
  refine ⟨fun args mem hPre => ?_⟩
  have hMem : mem = ret10InitMem := hPre.2
  subst hMem
  dsimp [ret10TotalClaim]
  rw [mirTree_ret10_eq args]
  refine ⟨treeSafe_tau1_ret _, productive_tau1_ret _, not_mayDiverge_tau1_ret _, ?_⟩
  intro tr out hRet
  have hOut := reachesRet_tau1_ret hRet
  exact ⟨.scalar { bits := 10, sizeBytes := 8 }, ret10InitMem, hOut, rfl, rfl⟩

theorem ret10ModularClaim_verified : ModularVerificationResult ret10ModularClaim := by
  refine ⟨fun h _ args mem hPre => ?_⟩
  have hMem : mem = ret10InitMem := hPre.2
  subst hMem
  have hTree : mirHandledTreeWithCallees ret10Mir args ret10InitMem .nil h =
      ITree.tau (ITree.ret (.normal (.scalar { bits := 10, sizeBytes := 8 }, ret10InitMem))) := by
    dsimp [mirHandledTreeWithCallees]
    rw [mirTree_ret10_eq args]
    exact interp_tau1_ret h _
  refine ⟨?_, ?_⟩
  · dsimp [ITree.toPartial, ret10ModularClaim]; rw [hTree]; exact treeSafe_tau1_ret _
  · intro outPair hRet _ retVal mem' hNorm
    dsimp [ITree.toPartial, ret10ModularClaim] at hRet ⊢
    rw [hTree] at hRet
    have hOut := reachesRet_tau1_ret hRet
    rw [hOut] at hNorm
    injection hNorm with hPair
    injection hPair with hVal hMemEq
    exact ⟨hVal.symm, hMemEq.symm⟩

-- Non-theorem claim (`A1-6` rejection test)
axiom nonTheoremClaimAx : VerificationResult ret10Claim

-- Constructive certificates for `ret10*` claims
def ret10MultiCert : MultiMutantSpecCert ret10Pre ret10Post where
  kills :=
    [ { name := "wrong_ret", category := .wrongReturn
        input := [.scalar { bits := 0, sizeBytes := 8 }], inputValid := Or.inl rfl
        referenceOutput := .scalar { bits := 10, sizeBytes := 8 }, referenceAccepted := rfl
        mutantOutput := .scalar { bits := 0, sizeBytes := 8 }
        mutantRejected := by intro h; injection h with hs; injection hs with hb; exact absurd hb (by decide) }
    , { name := "off_by_one", category := .offByOneScalar
        input := [.scalar { bits := 0, sizeBytes := 8 }], inputValid := Or.inl rfl
        referenceOutput := .scalar { bits := 10, sizeBytes := 8 }, referenceAccepted := rfl
        mutantOutput := .scalar { bits := 11, sizeBytes := 8 }
        mutantRejected := by intro h; injection h with hs; injection hs with hb; exact absurd hb (by decide) } ]
  nonEmpty := by intro h; nomatch h

def ret10DetCert : DeterministicSpecCert ret10Pre ret10Post where
  witnessInput := [.scalar { bits := 0, sizeBytes := 8 }]
  witnessValid := Or.inl rfl
  referenceOutput := .scalar { bits := 10, sizeBytes := 8 }
  referenceAccepted := rfl
  mutantOutput := .scalar { bits := 11, sizeBytes := 8 }
  mutantDiffers := by intro h; injection h with hs; injection hs with hb; exact absurd hb (by decide)
  realizable := fun _ _ => ⟨.scalar { bits := 10, sizeBytes := 8 }, rfl⟩
  uniqueOutput := fun _ _ _ _ h1 h2 => h1.trans h2.symm

def ret10StatefulMultiCert :
    MultiMutantSpecCert (uncurryPre ret10StatefulClaim.pre) (uncurryPost ret10StatefulClaim.post) where
  kills :=
    [ { name := "wrong_ret", category := .wrongReturn
        input := ([.scalar { bits := 0, sizeBytes := 8 }], ret10InitMem), inputValid := ⟨Or.inl rfl, rfl⟩
        referenceOutput := (.scalar { bits := 10, sizeBytes := 8 }, ret10InitMem), referenceAccepted := ⟨rfl, rfl⟩
        mutantOutput := (.scalar { bits := 0, sizeBytes := 8 }, ret10InitMem)
        mutantRejected := by intro ⟨h, _⟩; injection h with hs; injection hs with hb; exact absurd hb (by decide) } ]
  nonEmpty := by intro h; nomatch h

def ret10ModularMultiCert :
    ModularMultiMutantSpecCert ret10ModularClaim.envAssumed ret10ModularClaim.pre ret10ModularClaim.post where
  envNonVacuous := fuchsiaUsercopyCopyinRely_nonVacuous
  specCert := ret10StatefulMultiCert

def ret10ModularDetCert :
    ModularDeterministicSpecCert ret10ModularClaim.envAssumed ret10ModularClaim.pre ret10ModularClaim.post where
  envNonVacuous := fuchsiaUsercopyCopyinRely_nonVacuous
  specCert :=
    { witnessInput := ([.scalar { bits := 0, sizeBytes := 8 }], ret10InitMem)
      witnessValid := ⟨Or.inl rfl, rfl⟩
      referenceOutput := (.scalar { bits := 10, sizeBytes := 8 }, ret10InitMem)
      referenceAccepted := ⟨rfl, rfl⟩
      mutantOutput := (.scalar { bits := 11, sizeBytes := 8 }, ret10InitMem)
      mutantDiffers := by intro h; have h1 := congrArg Prod.fst h; injection h1 with hs; injection hs with hb; exact absurd hb (by decide)
      realizable := fun ⟨_, mem⟩ _ => ⟨(.scalar { bits := 10, sizeBytes := 8 }, mem), rfl, rfl⟩
      uniqueOutput := fun ⟨_, _⟩ ⟨r1, m1⟩ ⟨r2, m2⟩ _ ⟨hr1, hm1⟩ ⟨hr2, hm2⟩ => by
        dsimp [uncurryPost, ret10ModularClaim, ret10Post] at hr1 hm1 hr2 hm2
        rw [hr1.trans hr2.symm, hm1.trans hm2.symm] }

-- Wrong rely modular cert (`A1-6` negative)
def wrongRelyModularMultiCert :
    ModularMultiMutantSpecCert (fun _ => True) ret10ModularClaim.pre ret10ModularClaim.post where
  envNonVacuous := ⟨fuchsiaHermeticStubWitnessHandler, trivial⟩
  specCert := ret10StatefulMultiCert

-- Vacuous (`V8`) and Trivial (`V9`) claims
def v8VacuousClaim : Claim :=
  { body := ret10Mir, pre := fun _ => False, post := ret10Post }
theorem v8VacuousClaim_verified : VerificationResult v8VacuousClaim :=
  ⟨fun _ h => False.elim h⟩

def v9TrivialClaim : Claim :=
  { body := ret10Mir, pre := ret10Pre, post := fun _ _ => True }
theorem v9TrivialClaim_verified : VerificationResult v9TrivialClaim := by
  refine ⟨fun args _ => ?_⟩
  have hTree : mirCallTreeWithCallees ret10Mir args .nil =
      ITree.tau (ITree.ret (.normal (.scalar { bits := 10, sizeBytes := 8 }, ret10InitMem))) :=
    mirTree_ret10_eq args
  refine ⟨by dsimp [MirExecPartialWithCallees, ITree.toPartial, v9TrivialClaim]; rw [hTree]; exact treeSafe_tau1_ret _,
          fun _ _ _ _ _ _ => trivial⟩

-- `A1-4`: `sorry`-faked `MultiMutantSpecCert` with empty/missing categories
def a14SorryMultiCert : MultiMutantSpecCert ret10Pre ret10Post := by sorry

-- `Classical.choice` certificate (must be rejected under constructive policy!)
noncomputable def classicalCert : SpecStrengthCert ret10Pre ret10Post :=
  let _ : Nat := Classical.choice ⟨0⟩
  ret10MultiCert.toSpecStrengthCert

/-! ### `A3-3a..e`: `_sunfold` Spec-Gate Spoof Canaries -/

-- A3-3a: `_sunfold` makes vacuous pre/post look like `ret10Pre`/`ret10Post`
def a3VacPre (_ : List Value) : Prop := False
def a3VacPost (_ : List Value) (_ : Value) : Prop := True
def a3VacClaim : Claim := { body := ret10Mir, pre := a3VacPre, post := a3VacPost }
theorem a3VacClaim_verified : VerificationResult a3VacClaim :=
  ⟨fun _ h => False.elim h⟩
def a3VacPre._sunfold : List Value → Prop := ret10Pre
def a3VacPost._sunfold : List Value → Value → Prop := ret10Post

-- A3-3b: `_sunfold` fakes `kills` to include `.unpreservedFrame`
def a3WeakKills : List (NamedMutantKill ret10Pre ret10Post) := ret10MultiCert.kills
def a3WeakCert : MultiMutantSpecCert ret10Pre ret10Post :=
  { kills := a3WeakKills, nonEmpty := by intro h; dsimp [a3WeakKills, ret10MultiCert] at h; nomatch h }
def a3WeakKills._sunfold : List (NamedMutantKill ret10Pre ret10Post) :=
  { name := "fake_frame", category := .unpreservedFrame
    input := [.scalar { bits := 0, sizeBytes := 8 }], inputValid := Or.inl rfl
    referenceOutput := .scalar { bits := 10, sizeBytes := 8 }, referenceAccepted := rfl
    mutantOutput := .scalar { bits := 99, sizeBytes := 8 }, mutantRejected := by sorry } :: ret10MultiCert.kills

-- A3-3c: `_sunfold` hides a weak shadowing `ItemSpec` instance
instance a3StrongInst : ItemSpec "ep2::a3c" where
  pre := ret10Pre
  post := ret10Post
def a3Hide : Type 1 := ItemSpec "ep2::a3c"
def a3ShadowWeak : a3Hide := { pre := fun _ => False, post := fun _ _ => True }
def a3Hide._sunfold : Type 1 := PUnit
def a3cCert : MultiMutantSpecCert a3StrongInst.pre a3StrongInst.post := ret10MultiCert

-- A3-3d: `_sunfold` lets `Unit.unit` masquerade as `SpecStrengthCert`
def a3FakeCertTy : Type := Unit
def a3UnitCert : a3FakeCertTy := ()
def a3FakeCertTy._sunfold : Type := SpecStrengthCert ret10Pre ret10Post

-- A3-3e: `_sunfold` lets `True.intro` masquerade as `VerificationResult`
def a3FakeClaimTy : Prop := True
theorem a3TrivClaim : a3FakeClaimTy := trivial
def a3FakeClaimTy._sunfold : Prop := VerificationResult ret10Claim

/-! ### `R7`, `A1-2a..d`, `S3a/b`, `B4-4`, `B4-6`, `A4-3`, `A4-5`, `A4-7` Instance Canaries -/

-- R7: duplicate instance shadowing
instance r7Strong : ItemSpec "ep2::r7" where pre := ret10Pre; post := ret10Post
def r7ErasedWeak : ItemSpec "ep2::r7" where pre := fun _ => False; post := fun _ _ => True
def r7Cert : MultiMutantSpecCert r7Strong.pre r7Strong.post := ret10MultiCert

-- A1-2a: let-wrapped instance shadowing
instance a12aStrong : ItemSpec "ep2::a12a" where pre := ret10Pre; post := ret10Post
def a12aLetWeak : (let T := ItemSpec "ep2::a12a"; T) := { pre := fun _ => False, post := fun _ _ => True }
def a12aCert : MultiMutantSpecCert a12aStrong.pre a12aStrong.post := ret10MultiCert

-- A1-2b: beta-redex instance shadowing
instance a12bStrong : ItemSpec "ep2::a12b" where pre := ret10Pre; post := ret10Post
def a12bBetaWeak : ((fun s => ItemSpec s) "ep2::a12b") := { pre := fun _ => False, post := fun _ _ => True }
def a12bCert : MultiMutantSpecCert a12bStrong.pre a12bStrong.post := ret10MultiCert

-- A1-2c: 9-deep alias shadowing
instance a12cStrong : ItemSpec "ep2::a12c" where pre := ret10Pre; post := ret10Post
abbrev A1D0 := ItemSpec "ep2::a12c"
abbrev A1D1 := A1D0
abbrev A1D2 := A1D1
abbrev A1D3 := A1D2
abbrev A1D4 := A1D3
abbrev A1D5 := A1D4
abbrev A1D6 := A1D5
abbrev A1D7 := A1D6
abbrev A1D8 := A1D7
abbrev A1D9 := A1D8
def a12cDeepWeak : A1D9 := { pre := fun _ => False, post := fun _ _ => True }
def a12cCert : MultiMutantSpecCert a12cStrong.pre a12cStrong.post := ret10MultiCert

-- A1-2d: projection-typed instance shadowing
instance a12dStrong : ItemSpec "ep2::a12d" where pre := ret10Pre; post := ret10Post
abbrev A1Pair : Type 1 × Type := (ItemSpec "ep2::a12d", Nat)
def a12dProjWeak : A1Pair.1 := { pre := fun _ => False, post := fun _ _ => True }
def a12dCert : MultiMutantSpecCert a12dStrong.pre a12dStrong.post := ret10MultiCert

-- S3a: subclass chain shadowing
class S3Ext extends ItemSpec "ep2::s3a"
instance s3aExtWeak : S3Ext where pre := fun _ => False; post := fun _ _ => True
instance s3aExtStrong : S3Ext where pre := ret10Pre; post := ret10Post
def s3aCert : MultiMutantSpecCert ret10Pre ret10Post := ret10MultiCert

-- S3b: parametric instance argument shadowing
class S3Cfg where
  p : List Value → Prop
  q : List Value → Value → Prop
instance s3bCfgWeak : S3Cfg where
  p := fun _ => False
  q := fun _ _ => True
instance s3bCfgStrong : S3Cfg where
  p := ret10Pre
  q := ret10Post
instance s3bFromCfg [c : S3Cfg] : ItemSpec "ep2::s3b" where
  pre := c.p
  post := c.q
def s3bCert : MultiMutantSpecCert ret10Pre ret10Post := ret10MultiCert

-- Clean single-instance positive control (for B4-4d & A4-3c)
instance cleanSingleInst : ItemSpec "ep2::clean_single" where pre := ret10Pre; post := ret10Post
def cleanSingleCert : MultiMutantSpecCert cleanSingleInst.pre cleanSingleInst.post := ret10MultiCert

-- B4-4b: strong instance shadowed by Nat.rec-typed weak def (tests `iota := false` reset)
instance b44bStrong : ItemSpec "ep2::b44b" where pre := ret10Pre; post := ret10Post
def b44bNatRecWeak : Nat.rec (motive := fun _ => Type 1) (ItemSpec "ep2::b44b") (fun _ _ => PUnit) 0 :=
  { pre := fun _ => False, post := fun _ _ => True }
def b44bCert : MultiMutantSpecCert b44bStrong.pre b44bStrong.post := ret10MultiCert

-- B4-6: pure normalizer recursor, quotient, indexed family (W4), 70-deep alias under proj,
-- structure-eta, K-recursor, and stuck-variable control
def b46NatRecWeak : Nat.rec (motive := fun _ => Type 1) (ItemSpec "ep2::b46_natrec") (fun _ _ => PUnit) 0 :=
  { pre := fun _ => False, post := fun _ _ => True }

def b46QuotWeak :
    Quot.lift (r := fun (_ _ : Unit) => True) (fun _ => ItemSpec "ep2::b46_quot") (fun _ _ _ => rfl)
      (Quot.mk _ ()) :=
  { pre := fun _ => False, post := fun _ _ => True }

inductive B46Vec : Nat → Type where
  | nil : B46Vec 0
  | cons (n : Nat) (x : Bool) (v : B46Vec n) : B46Vec (n + 1)

def b46IndexedWeak :
    B46Vec.rec (motive := fun _ _ => Type 1) PUnit
      (fun _ b _ _ => Bool.rec PUnit (ItemSpec "ep2::b46_idx") b)
      (B46Vec.cons 0 true B46Vec.nil) :=
  { pre := fun _ => False, post := fun _ _ => True }

def b46P0 : Type 1 × Type := (ItemSpec "ep2::b46_p70", Nat)
def b46P1 := b46P0
def b46P2 := b46P1
def b46P3 := b46P2
def b46P4 := b46P3
def b46P5 := b46P4
def b46P6 := b46P5
def b46P7 := b46P6
def b46P8 := b46P7
def b46P9 := b46P8
def b46P10 := b46P9
def b46P11 := b46P10
def b46P12 := b46P11
def b46P13 := b46P12
def b46P14 := b46P13
def b46P15 := b46P14
def b46P16 := b46P15
def b46P17 := b46P16
def b46P18 := b46P17
def b46P19 := b46P18
def b46P20 := b46P19
def b46P21 := b46P20
def b46P22 := b46P21
def b46P23 := b46P22
def b46P24 := b46P23
def b46P25 := b46P24
def b46P26 := b46P25
def b46P27 := b46P26
def b46P28 := b46P27
def b46P29 := b46P28
def b46P30 := b46P29
def b46P31 := b46P30
def b46P32 := b46P31
def b46P33 := b46P32
def b46P34 := b46P33
def b46P35 := b46P34
def b46P36 := b46P35
def b46P37 := b46P36
def b46P38 := b46P37
def b46P39 := b46P38
def b46P40 := b46P39
def b46P41 := b46P40
def b46P42 := b46P41
def b46P43 := b46P42
def b46P44 := b46P43
def b46P45 := b46P44
def b46P46 := b46P45
def b46P47 := b46P46
def b46P48 := b46P47
def b46P49 := b46P48
def b46P50 := b46P49
def b46P51 := b46P50
def b46P52 := b46P51
def b46P53 := b46P52
def b46P54 := b46P53
def b46P55 := b46P54
def b46P56 := b46P55
def b46P57 := b46P56
def b46P58 := b46P57
def b46P59 := b46P58
def b46P60 := b46P59
def b46P61 := b46P60
def b46P62 := b46P61
def b46P63 := b46P62
def b46P64 := b46P63
def b46P65 := b46P64
def b46P66 := b46P65
def b46P67 := b46P66
def b46P68 := b46P67
def b46P69 := b46P68
def b46P70 := b46P69
def b46Proj70Weak : b46P70.1 := { pre := fun _ => False, post := fun _ _ => True }

def b46KRecWeak : Eq.rec (motive := fun _ _ => Type 1) (ItemSpec "ep2::b46_krec") (Eq.refl (0 : Nat)) :=
  { pre := fun _ => False, post := fun _ _ => True }

def b46StuckControl (n : Nat) : Nat.rec (motive := fun _ => Type) Nat (fun _ _ => Bool) n :=
  match n with
  | 0 => (0 : Nat)
  | _ + 1 => true

-- A4-3a/b: Core.State.cache.instLevelValue & withExporting
instance a43Strong : ItemSpec "ep2::a43" where pre := ret10Pre; post := ret10Post
def a4CoreCacheAlias : Type 1 := ItemSpec "ep2::a43"
def a43Weak : a4CoreCacheAlias := { pre := fun _ => False, post := fun _ _ => True }
def a43Cert : MultiMutantSpecCert a43Strong.pre a43Strong.post := ret10MultiCert

#eval show MetaM Unit from do
  let env ← getEnv
  let ctx := SpecAuditCtx.forLiveMeta env 400
  -- V1..V6
  IO.println (fmtTags "V1_direct_sorry" (auditDeclsForSpec env ctx #[``v1_direct_sorry] false))
  IO.println (fmtTags "V2_tactic_sorryAx" (auditDeclsForSpec env ctx #[``v2_tactic_sorryAx] false))
  IO.println (fmtTags "V3_custom_axiom" (auditDeclsForSpec env ctx #[``v3_uses_custom] false))
  IO.println (fmtTags "V3_private_axiom" (auditDeclsForSpec env ctx #[``v3_uses_private] false))
  IO.println (fmtTags "V3_trust_compiler" (auditDeclsForSpec env ctx #[``v3_trust_compiler] false))
  IO.println (fmtTags "V4_native_decide" (auditDeclsForSpec env ctx #[``v4_native_decide] false))
  IO.println (fmtTags "V5_partial" (auditDeclsForSpec env ctx #[``v5_partial_loop] false))
  IO.println (fmtTags "V5_safe_gcd" (auditDeclsForSpec env ctx #[``v5_safe_gcd] false))
  IO.println (fmtTags "V6_unsafe" (auditDeclsForSpec env ctx #[``v6_unsafe_fn] false))
  IO.println (fmtTags "V6_implemented_by" (auditDeclsForSpec env ctx #[``v6_implemented_by] false))
  IO.println (fmtTags "V6_extern" (auditDeclsForSpec env ctx #[``v6_extern_fn] false))
  IO.println (fmtTags "V6_export" (auditDeclsForSpec env ctx #[``v6_export_fn] false))
  IO.println (fmtTags "V6_csimp" (auditDeclsForSpec env ctx #[``v6_uses_csimp] false))
  IO.println (fmtTags "V6_init" (auditDeclsForSpec env ctx #[``v6_init_flag] false))

  -- V8 / V9 / Classical.choice / R6 / R8 / R11 / A1-4 / A1-6 / A2-4b
  IO.println (fmtTags "V8_vacuous_claim_wrong_cert"
    (← auditClaimSpecStrength ``v8VacuousClaim_verified ``ret10MultiCert))
  IO.println (fmtTags "V9_trivial_claim_wrong_cert"
    (← auditClaimSpecStrength ``v9TrivialClaim_verified ``ret10MultiCert))
  IO.println (fmtTags "V9_classical_cert_rejected"
    (← auditClaimSpecStrength ``ret10Claim_verified ``classicalCert))
  IO.println (fmtTags "A1_4_sorry_before_coverage"
    (← auditClaimSpecStrength ``ret10Claim_verified ``a14SorryMultiCert #["unpreservedFrame"]))
  IO.println (fmtTags "R8_coverage_gap"
    (← auditClaimSpecStrength ``ret10Claim_verified ``ret10MultiCert #["wrongReturn", "unpreservedFrame"]))
  IO.println (fmtTags "R11_stateless_claim_ok"
    (← auditClaimSpecStrength ``ret10Claim_verified ``ret10MultiCert #["wrongReturn", "offByOneScalar"]))
  IO.println (fmtTags "R11_stateless_det_ok"
    (← auditClaimSpecStrength ``ret10Claim_verified ``ret10DetCert (requireDeterministic := true)))
  IO.println (fmtTags "A1_6_stateful_claim_ok"
    (← auditClaimSpecStrength ``ret10StatefulClaim_verified ``ret10StatefulMultiCert #["wrongReturn"]))
  IO.println (fmtTags "A1_6_total_claim_ok"
    (← auditClaimSpecStrength ``ret10TotalClaim_verified ``ret10StatefulMultiCert #["wrongReturn"]))
  IO.println (fmtTags "A1_6_modular_multi_ok"
    (← auditClaimSpecStrength ``ret10ModularClaim_verified ``ret10ModularMultiCert #["wrongReturn"]))
  IO.println (fmtTags "A1_6_modular_det_ok"
    (← auditClaimSpecStrength ``ret10ModularClaim_verified ``ret10ModularDetCert (requireDeterministic := true)))
  IO.println (fmtTags "A1_6_modular_wrong_rely"
    (← auditClaimSpecStrength ``ret10ModularClaim_verified ``wrongRelyModularMultiCert))
  IO.println (fmtTags "A1_6_non_theorem_claim_rejected"
    (← auditClaimSpecStrength ``nonTheoremClaimAx ``ret10MultiCert))
  IO.println (fmtTags "S5_det_rejected_for_input_sensitive"
    (← auditClaimSpecStrength ``ret10Claim_verified ``ret10DetCert (requireInputSensitive := true)))
  IO.println (fmtTags "A2_4b_modular_input_sensitive_ok"
    (← auditSpecStrengthCert ``fuchsiaUsercopyCopyinModularDirectInputSensitiveCert
      (.modular (mkConst ``fuchsiaUsercopyCopyinRely) (mkConst ``fuchsiaUsercopyCopyinPre) (mkConst ``fuchsiaUsercopyCopyinPost))
      (requireInputSensitive := true)))

  -- A3-3a..e: `_sunfold` spec-gate exploits
  IO.println (fmtTags "A3_3a_sunfold_vacuous_claim"
    (← auditClaimSpecStrength ``a3VacClaim_verified ``ret10MultiCert))
  IO.println (fmtTags "A3_3b_sunfold_fake_coverage"
    (← auditClaimSpecStrength ``ret10Claim_verified ``a3WeakCert #["unpreservedFrame"]))
  IO.println (fmtTags "A3_3c_sunfold_hidden_shadow"
    (← auditItemSpecStrengthBySynth .item "ep2::a3c" ``a3cCert))
  IO.println (fmtTags "A3_3d_sunfold_unit_as_cert"
    (← auditSpecStrengthCert ``a3UnitCert (.direct (mkConst ``ret10Pre) (mkConst ``ret10Post))))
  IO.println (fmtTags "A3_3e_sunfold_trivial_as_claim"
    (← auditClaimSpecStrength ``a3TrivClaim ``ret10MultiCert))

  -- R7, A1-2a..d, S3a/b
  IO.println (fmtTags "R7_duplicate_shadow"
    (← auditItemSpecStrengthBySynth .item "ep2::r7" ``r7Cert))
  IO.println (fmtTags "A1_2a_let_shadow"
    (← auditItemSpecStrengthBySynth .item "ep2::a12a" ``a12aCert))
  IO.println (fmtTags "A1_2b_beta_shadow"
    (← auditItemSpecStrengthBySynth .item "ep2::a12b" ``a12bCert))
  IO.println (fmtTags "A1_2c_deep_alias_shadow"
    (← auditItemSpecStrengthBySynth .item "ep2::a12c" ``a12cCert))
  IO.println (fmtTags "A1_2d_proj_shadow"
    (← auditItemSpecStrengthBySynth .item "ep2::a12d" ``a12dCert))
  IO.println (fmtTags "S3a_subclass_chain_shadow"
    (← auditItemSpecStrengthBySynth .item "ep2::s3a" ``s3aCert))
  IO.println (fmtTags "S3b_parametric_chain_shadow"
    (← auditItemSpecStrengthBySynth .item "ep2::s3b" ``s3bCert))

  -- B4-3: warm Meta cache replaying `_sunfold`
  let _ ← withOptions (·.set `smartUnfolding true) do
    Meta.withTransparency .all (Meta.whnf (mkConst ``a3Hide))
  IO.println (fmtTags "B4_3_warm_meta_cache"
    (← auditItemSpecStrengthBySynth .item "ep2::a3c" ``a3cCert))

  -- B4-4: hostile caller Meta.Config (`zeta := false`, `iota := false`, `customCanUnfoldPredicate?`)
  let b44a ← Meta.withConfig (fun c => { c with zeta := false }) <|
    auditItemSpecStrengthBySynth .item "ep2::a12a" ``a12aCert
  IO.println (fmtTags "B4_4a_zeta_false" b44a)
  let b44b ← Meta.withConfig (fun c => { c with iota := false }) <|
    auditItemSpecStrengthBySynth .item "ep2::b44b" ``b44bCert
  IO.println (fmtTags "B4_4b_iota_false" b44b)
  let b44c ← withReader (fun (ctx : Meta.Context) => { ctx with customCanUnfoldPredicate? := some (fun _ _ => pure false) }) <|
    auditItemSpecStrengthBySynth .item "ep2::a12c" ``a12cCert
  IO.println (fmtTags "B4_4c_custom_unfold_pred" b44c)
  let b44d ← Meta.withConfig (fun c => { c with zeta := false, iota := false }) <|
    auditItemSpecStrengthBySynth .item "ep2::clean_single" ``cleanSingleCert #["wrongReturn"]
  IO.println (fmtTags "B4_4d_hostile_config_clean_control" b44d)

  -- B4-5 & W6: unassigned mvar vs free variable vs caller-assigned mvar
  let mPre ← Meta.mkFreshExprMVar (some (mkForall `x .default (mkApp (mkConst ``List [Level.zero]) (mkConst ``Value)) (mkSort Level.zero)))
  IO.println (fmtTags "B4_5a_unassigned_mvar"
    (← auditSpecStrengthCert ``ret10MultiCert (.direct mPre (mkConst ``ret10Post))))
  let mUnderLam := Expr.lam `x (mkApp (mkConst ``List [Level.zero]) (mkConst ``Value)) (mkApp mPre (.bvar 0)) .default
  IO.println (fmtTags "B4_5b_mvar_under_binder"
    (← auditSpecStrengthCert ``ret10MultiCert (.direct mUnderLam (mkConst ``ret10Post))))
  let fvarRes ← Meta.withLocalDeclD `fv (mkForall `x .default (mkApp (mkConst ``List [Level.zero]) (mkConst ``Value)) (mkSort Level.zero)) fun fv =>
    auditSpecStrengthCert ``ret10MultiCert (.direct fv (mkConst ``ret10Post))
  IO.println (fmtTags "B4_5d_fvar_rejected" fvarRes)
  mPre.mvarId!.assign (mkConst ``ret10Pre)
  IO.println (fmtTags "B4_5e_assigned_mvar_ok"
    (← auditSpecStrengthCert ``ret10MultiCert (.direct mPre (mkConst ``ret10Post))))

  -- B4-6: pure normalizer recursor, quotient, indexed family, 70-deep proj, K-rec, controls
  -- (evaluated BEFORE introducing fail-closed native-evaluator / exponential-budget canaries)
  let checkPureMeta (label : String) (defId : String) (expected : Array Name) : MetaM Unit := do
    let p := specInstanceCandidates env `Trusted.VerificationResult.ItemSpec defId 256
    let m ← specInstanceCandidatesMeta `Trusted.VerificationResult.ItemSpec defId 256
    IO.println s!"{label}: pure={p == expected} meta={m == expected}"
  checkPureMeta "B4_6a_natrec" "ep2::b46_natrec" #[``b46NatRecWeak]
  checkPureMeta "B4_6b_quot" "ep2::b46_quot" #[``b46QuotWeak]
  checkPureMeta "B4_6c_proj70" "ep2::b46_p70" #[``b46Proj70Weak]
  checkPureMeta "B4_6d_indexed_vec" "ep2::b46_idx" #[``b46IndexedWeak]
  checkPureMeta "B4_6e_k_recursor" "ep2::b46_krec" #[``b46KRecWeak]
  checkPureMeta "B4_6h_unspecified_zero_fp" "ep2::nobody_specifies_this" #[]
  checkPureMeta "B4_6i_real_model_exact_one"
    "anneal_model::fxfs_storage_boundary::vmo_subslice_bounds_valid" #[``instFxfsModelItemSpec]

  -- A4-3a/b/c: Core.State.cache.instLevelValue poisoning, withExporting, hostile Options
  modifyThe Core.State fun s =>
    { s with cache := { s.cache with instLevelValue := s.cache.instLevelValue.insert ``a4CoreCacheAlias ([], mkConst ``PUnit [Level.one]) } }
  IO.println (fmtTags "A4_3a_core_cache_poison"
    (← auditItemSpecStrengthBySynth .item "ep2::a43" ``a43Cert))
  let a43b ← Lean.withExporting (isExporting := true) <|
    auditItemSpecStrengthBySynth .item "ep2::a43" ``a43Cert
  IO.println (fmtTags "A4_3b_withExporting" a43b)
  let a43c ← withOptions (·.set `synthInstance.maxHeartbeats 1) <|
    auditItemSpecStrengthBySynth .item "ep2::clean_single" ``cleanSingleCert #["wrongReturn"]
  IO.println (fmtTags "A4_3c_hostile_options_control" a43c)

/-! ### Episode 2 `B1` regressions (declared before the fail-closed native / budget canaries) -/

-- B1-1: theorem-headed major premise. Lean's kernel δ-unfolds theorems exactly like definitions,
-- `Meta.whnf` never does (`getUnfoldableConst?` answers `none` for `.thm` at every transparency).
-- `b11ThmWeak` uses no axiom and no native code; the kernel accepts it as `ItemSpec "ep2::b11"`.
theorem b11Acc : Acc (fun (_ _ : Nat) => False) 0 := Acc.intro 0 (fun _ h => False.elim h)
instance b11Strong : ItemSpec "ep2::b11" where pre := ret10Pre; post := ret10Post
-- (The elaborator cannot see through `b11Acc` either, so the value is transported along an
-- equation that holds by proof irrelevance; the declared type is the `Acc.rec` term itself.)
theorem b11TyEq :
    @Acc.rec Nat (fun _ _ => False) (fun _ _ => Type 1) (fun _ _ _ => ItemSpec "ep2::b11") 0 b11Acc
      = ItemSpec "ep2::b11" :=
  @congrArg _ _ b11Acc (Acc.intro 0 (fun _ h => False.elim h))
    (fun h => @Acc.rec Nat (fun _ _ => False) (fun _ _ => Type 1) (fun _ _ _ => ItemSpec "ep2::b11") 0 h)
    rfl
def b11ThmWeak :
    @Acc.rec Nat (fun _ _ => False) (fun _ _ => Type 1) (fun _ _ _ => ItemSpec "ep2::b11") 0 b11Acc :=
  cast b11TyEq.symm { pre := fun _ => False, post := fun _ _ => True }
def b11Cert : MultiMutantSpecCert b11Strong.pre b11Strong.post := ret10MultiCert

-- B1-6: a universe-polymorphic `sorry` certificate must report `sorryAxiomReached` (audit first).
def b16PolySorryCert.{u} : (fun (_ : Sort u) => MultiMutantSpecCert ret10Pre ret10Post) PUnit := sorry

-- A2-7: an erased global instance (`attribute [-instance]`) must fail `isGlobalInstanceRegistered`
-- even in live `MetaM` when `useSynthInstance := false`.
instance a27ErasedInst : ItemSpec "ep2::a27_erased" where pre := ret10Pre; post := ret10Post
attribute [-instance] a27ErasedInst
def a27Cert : MultiMutantSpecCert a27ErasedInst.pre a27ErasedInst.post := ret10MultiCert

#eval show MetaM Unit from do
  let env ← getEnv
  let p := specInstanceCandidates env `Trusted.VerificationResult.ItemSpec "ep2::b11" 256
  let m ← specInstanceCandidatesMeta `Trusted.VerificationResult.ItemSpec "ep2::b11" 256
  let expected := #[``b11Strong, ``b11ThmWeak]
  IO.println s!"B1_1_theorem_major_scanners: pure={p == expected} meta={m == expected}"
  IO.println (fmtTags "B1_1_theorem_major_synth_gate"
    (← auditItemSpecStrengthBySynth .item "ep2::b11" ``b11Cert))
  IO.println (fmtTags "B1_1_theorem_major_gate_no_synth"
    (← auditItemSpecStrengthBySynth .item "ep2::b11" ``b11Cert (useSynthInstance := false)))
  let pc := specInstanceCandidates env `Trusted.VerificationResult.ItemSpec "ep2::nobody_specifies_this" 256
  let mc ← specInstanceCandidatesMeta `Trusted.VerificationResult.ItemSpec "ep2::nobody_specifies_this" 256
  IO.println s!"B1_1_theorem_major_zero_fp_control: pure={pc == #[]} meta={mc == #[]}"
  IO.println (fmtTags "B1_6_poly_sorry_cert_reports_sorry"
    (← auditSpecStrengthCert ``b16PolySorryCert (.direct (mkConst ``ret10Pre) (mkConst ``ret10Post))))
  IO.println (fmtTags "A2_7_erased_instance_rejected_no_synth"
    (← auditItemSpecStrengthBySynth .item "ep2::a27_erased" ``a27Cert (useSynthInstance := false)))

-- A4-5a: `Lean.reduceBool` canary (fails closed in both scanners: never evaluated natively)
def a4RbFlag : Bool := true
instance a4RbStrong : ItemSpec "ep2::a4rb" where pre := ret10Pre; post := ret10Post
def a4RbWeak : Bool.rec (motive := fun _ => Type 1) PUnit (ItemSpec "ep2::a4rb") (Lean.reduceBool a4RbFlag) :=
  { pre := fun _ => False, post := fun _ _ => True }
def a4RbCert : MultiMutantSpecCert a4RbStrong.pre a4RbStrong.post := ret10MultiCert

#eval show MetaM Unit from do
  let env ← getEnv
  let p := specInstanceCandidates env `Trusted.VerificationResult.ItemSpec "ep2::a4rb" 256
  let m ← specInstanceCandidatesMeta `Trusted.VerificationResult.ItemSpec "ep2::a4rb" 256
  let expected := #[``a4RbStrong, ``a4RbWeak]
  IO.println s!"A4_5a_reduceBool: pure={p == expected} meta={m == expected}"

-- A4-5b: `Lean.reduceNat` kernel-vs-Meta.whnf asymmetry
def a4RnVal : Nat := 0
instance a4RnStrong : ItemSpec "ep2::a4rn" where pre := ret10Pre; post := ret10Post
def a4RnWeakVal : ItemSpec "ep2::a4rn" where pre := fun _ => False; post := fun _ _ => True
-- Add `a4RnKernelWeak` directly through Lean's kernel: Lean's kernel reduces `Lean.reduceNat a4RnVal`
-- to `.lit (.natVal 0)` and ACCEPTS `a4RnKernelWeak`, whereas `Meta.whnf` leaves `Nat.rec` stuck!
run_cmd Elab.Command.liftCoreM do
  let natTy := mkConst ``Nat
  let u2 := Level.succ (Level.succ Level.zero)
  let u3 := Level.succ u2
  let motive := Expr.lam `k natTy (mkSort u2) .default
  let zCase := mkApp (mkConst ``ItemSpec) (mkStrLit "ep2::a4rn")
  let sCase := Expr.lam `_ natTy (Expr.lam `_ (mkSort u2) (mkConst ``PUnit [u2]) .default) .default
  let maj := mkApp (mkConst ``Lean.reduceNat) (mkConst ``a4RnVal)
  let ty := mkApp4 (mkConst ``Nat.rec [u3]) motive zCase sCase maj
  addDecl (.defnDecl {
    name := `a4RnKernelWeak, levelParams := [], type := ty,
    value := mkConst ``a4RnWeakVal, hints := .abbrev, safety := .safe
  })
def a4RnCert : MultiMutantSpecCert a4RnStrong.pre a4RnStrong.post := ret10MultiCert

#eval show MetaM Unit from do
  let env ← getEnv
  let p := specInstanceCandidates env `Trusted.VerificationResult.ItemSpec "ep2::a4rn" 256
  let m ← specInstanceCandidatesMeta `Trusted.VerificationResult.ItemSpec "ep2::a4rn" 256
  -- `a4RbWeak` is listed too: a type that reaches a kernel-native evaluator is never normalized.
  IO.println s!"A4_5b_reduceNat_asymmetry: pure={p.contains `a4RnKernelWeak && p.contains ``a4RnStrong} meta={m == #[``a4RbWeak, `a4RnKernelWeak, ``a4RnStrong, ``a4RnWeakVal]}"
  IO.println (fmtTags "A4_5b_reduceNat_synth_gate"
    (← auditItemSpecStrengthBySynth .item "ep2::a4rn" ``a4RnCert))

-- A4-7: 26-deep binary-branching type (`2^26 > 67M` steps under per-branch fuel!)
noncomputable section
def b0 : Bool := true
def b1 : Bool := Bool.rec b0 b0 b0
def b2 : Bool := Bool.rec b1 b1 b1
def b3 : Bool := Bool.rec b2 b2 b2
def b4 : Bool := Bool.rec b3 b3 b3
def b5 : Bool := Bool.rec b4 b4 b4
def b6 : Bool := Bool.rec b5 b5 b5
def b7 : Bool := Bool.rec b6 b6 b6
def b8 : Bool := Bool.rec b7 b7 b7
def b9 : Bool := Bool.rec b8 b8 b8
def b10 : Bool := Bool.rec b9 b9 b9
def b11 : Bool := Bool.rec b10 b10 b10
def b12 : Bool := Bool.rec b11 b11 b11
def b13 : Bool := Bool.rec b12 b12 b12
def b14 : Bool := Bool.rec b13 b13 b13
def b15 : Bool := Bool.rec b14 b14 b14
def b16 : Bool := Bool.rec b15 b15 b15
def b17 : Bool := Bool.rec b16 b16 b16
def b18 : Bool := Bool.rec b17 b17 b17
def b19 : Bool := Bool.rec b18 b18 b18
def b20 : Bool := Bool.rec b19 b19 b19
def b21 : Bool := Bool.rec b20 b20 b20
def b22 : Bool := Bool.rec b21 b21 b21
def b23 : Bool := Bool.rec b22 b22 b22
def b24 : Bool := Bool.rec b23 b23 b23
def b25 : Bool := Bool.rec b24 b24 b24
def b26 : Bool := Bool.rec b25 b25 b25
def a47ExpWeak : Bool.rec (motive := fun _ => Type 1) PUnit (ItemSpec "ep2::a47") b26 :=
  { pre := fun _ => False, post := fun _ _ => True }
end

#eval show MetaM Unit from do
  let env ← getEnv
  let t0 ← IO.monoMsNow
  let a47Cands := specInstanceCandidates env `Trusted.VerificationResult.ItemSpec "ep2::a47" 256
  let dt := (← IO.monoMsNow) - t0
  IO.println s!"A4_7_exp_branching_linear_budget: listed={a47Cands.contains ``a47ExpWeak} fast={decide (dt < 2000)}"

/-! ### Episode 2 `B1` regressions (pure normalizer vs. kernel literals, native evaluators) -/

-- B1-2: the kernel converts a string literal under a projection to `String.ofList [..]` and keeps
-- reducing; the pure normalizer must not call `"abc".1` a certain stuck term.
instance b12Strong : ItemSpec "ep2::b12" where pre := ret10Pre; post := ret10Post
def b12StrWeak :
    @List.rec UInt8 (fun _ => Type 1) PUnit (fun _ _ _ => ItemSpec "ep2::b12")
      ("abc" : String).toByteArray.data.toList :=
  { pre := fun _ => False, post := fun _ _ => True }

-- B1-3: the kernel evaluates `Nat.gcd` on literals with GMP; whatever the body of `Nat.gcd` does
-- (well-founded recursion through theorems), the pure normalizer must not call it stuck.
instance b13Strong : ItemSpec "ep2::b13" where pre := ret10Pre; post := ret10Post
def b13GcdWeak : Nat.rec (motive := fun _ => Type 1) (ItemSpec "ep2::b13") (fun _ _ => PUnit) (Nat.gcd 0 0) :=
  { pre := fun _ => False, post := fun _ _ => True }

#eval show MetaM Unit from do
  let env ← getEnv
  let p12 := specInstanceCandidates env `Trusted.VerificationResult.ItemSpec "ep2::b12" 256
  let m12 ← specInstanceCandidatesMeta `Trusted.VerificationResult.ItemSpec "ep2::b12" 256
  IO.println s!"B1_2_string_literal_projection: pure={p12.contains ``b12StrWeak} meta={m12.contains ``b12StrWeak}"
  let p13 := specInstanceCandidates env `Trusted.VerificationResult.ItemSpec "ep2::b13" 256
  let m13 ← specInstanceCandidatesMeta `Trusted.VerificationResult.ItemSpec "ep2::b13" 256
  IO.println s!"B1_3_kernel_nat_gmp_major: pure={p13.contains ``b13GcdWeak} meta={m13.contains ``b13GcdWeak}"
  -- B1-4: a type that reaches `Lean.reduceBool` / `Lean.reduceNat` is never handed to `Meta.whnf`
  -- (that would run compiled code of the audited module inside the auditor): it is a candidate for
  -- every `defId`, including one nobody specifies, in the `MetaM` scanner as well.
  let m14 ← specInstanceCandidatesMeta `Trusted.VerificationResult.ItemSpec "ep2::b14_unrelated" 256
  IO.println s!"B1_4_native_evaluator_never_run: reduceBool={m14.contains ``a4RbWeak} reduceNat={m14.contains `a4RnKernelWeak} clean={!m14.contains ``b11ThmWeak && !m14.contains ``b13GcdWeak}"

/-! ### Episode 2 `A1` regressions (`expected` native-evaluator guard, poly-sorry claim ordering,
    parameterized dependent-recursor & higher-order shadows, `String.rec` literal major) -/

-- A1-2b: universe-polymorphic `sorry` claim theorem reports `sorryAxiomReached`, not `specStrengthCertInvalidType`.
theorem a12bPolySorryClaim.{u} : let _ := PUnit.{u}; VerificationResult ret10Claim := by sorry

-- A1-3: parameterized dependent-recursor (typeclass-gated & Bool-gated) and higher-order type-family shadows.
instance a13Strong : ItemSpec "ep2::a13" where pre := ret10Pre; post := ret10Post
class A13Flag where ok : Bool
instance : A13Flag where ok := true
def a13CondShadow [f : A13Flag] : Bool.rec (motive := fun _ => Type 1) PUnit (ItemSpec "ep2::a13") f.ok :=
  match f with | ⟨false⟩ => PUnit.unit | ⟨true⟩ => { pre := fun _ => False, post := fun _ _ => True }
def a13BoolShadow (b : Bool) : Bool.rec (motive := fun _ => Type 1) PUnit (ItemSpec "ep2::a13") b :=
  match b with | false => PUnit.unit | true => { pre := fun _ => False, post := fun _ _ => True }
def a13HigherOrderShadow (F : Type 1 → Type 1) (x : F (ItemSpec "ep2::a13")) : F (ItemSpec "ep2::a13") := x
def a13Cert : MultiMutantSpecCert a13Strong.pre a13Strong.post := ret10MultiCert

-- A1-4: `String.rec` with a string literal major premise.
instance a14StrStrong : ItemSpec "ep2::a14str" where pre := ret10Pre; post := ret10Post
def a14StrRecWeak :
    String.rec (motive := fun _ => Type 1)
      (fun ba _ => match ba.data.size with | 5 => ItemSpec "ep2::a14str" | _ => PUnit)
      "hello" :=
  { pre := fun _ => False, post := fun _ _ => True }

#eval show MetaM Unit from do
  let env ← getEnv
  -- A1-2a: live `expected` reaching `Lean.reduceBool` is rejected BEFORE any MetaM/kernel normalization.
  let preTy := mkForall `_ .default (mkApp (mkConst ``List [Level.zero]) (mkConst ``Value)) (mkSort Level.zero)
  let evilPre := mkApp4 (mkConst ``Bool.rec [Level.succ Level.zero])
    (Expr.lam `_ (mkConst ``Bool) preTy .default)
    (Expr.lam `_ (mkApp (mkConst ``List [Level.zero]) (mkConst ``Value)) (mkConst ``False) .default)
    (mkConst ``ret10Pre)
    (mkApp (mkConst ``Lean.reduceBool) (mkConst ``a4RbFlag))
  IO.println (fmtTags "A1_2a_expected_native_rejected"
    (← auditSpecStrengthCert ``ret10MultiCert (.direct evilPre (mkConst ``ret10Post))))
  IO.println (fmtTags "A1_2b_poly_sorry_claim_reports_sorry"
    (← auditClaimSpecStrength ``a12bPolySorryClaim ``ret10MultiCert))
  let p13 := specInstanceCandidates env `Trusted.VerificationResult.ItemSpec "ep2::a13" 256
  let m13 ← specInstanceCandidatesMeta `Trusted.VerificationResult.ItemSpec "ep2::a13" 256
  IO.println s!"A1_3_dep_rec_shadow: pure={p13.contains ``a13CondShadow && p13.contains ``a13BoolShadow && p13.contains ``a13HigherOrderShadow} meta={m13.contains ``a13CondShadow && m13.contains ``a13BoolShadow && m13.contains ``a13HigherOrderShadow}"
  -- (After the native-evaluator canaries every `defId` is ambiguous in this file, so the gate line
  -- also checks that the dependent shadows themselves are named among the candidates.)
  let g13 ← auditItemSpecStrengthBySynth .item "ep2::a13" ``a13Cert (useSynthInstance := false)
  IO.println s!"{fmtTags "A1_3_dep_rec_synth_gate" g13} names={g13.any (fun v => (v.detail.splitOn "a13CondShadow").length > 1 && (v.detail.splitOn "a13BoolShadow").length > 1)}"
  let p14 := specInstanceCandidates env `Trusted.VerificationResult.ItemSpec "ep2::a14str" 256
  let m14s ← specInstanceCandidatesMeta `Trusted.VerificationResult.ItemSpec "ep2::a14str" 256
  IO.println s!"A1_4_string_rec_literal: pure={p14.contains ``a14StrRecWeak} meta={m14s.contains ``a14StrRecWeak}"

/-! ### Episode 2 `B2` regressions (forged registered-instance entries) -/

-- B2-1: an instance entry stored directly with `instanceExtension.add` (bypassing `addInstance`'s
-- "return type is a class" check) for a variable-concluding constant, keyed like `ItemSpec d`, makes
-- `ItemSpec d` resolve to a weak payload that no declaration type exposes under `ItemSpec`.
instance b21Strong : ItemSpec "ep2::b21" where pre := ret10Pre; post := ret10Post
class B21Holder (T : Type 1) where val : T
instance b21HolderInst : B21Holder (ItemSpec "ep2::b21") := ⟨{ pre := fun _ => False, post := fun _ _ => True }⟩
def b21Universal {T : Type 1} [h : B21Holder T] : T := h.val
def b21Cert : MultiMutantSpecCert b21Strong.pre b21Strong.post := ret10MultiCert
run_cmd Elab.Command.liftTermElabM do
  let keys ← Meta.DiscrTree.mkPath (mkApp (mkConst ``ItemSpec) (mkStrLit "ep2::b21"))
  let ent : Meta.InstanceEntry := { keys := keys, val := mkConst ``b21Universal, priority := 5000, globalName? := some ``b21Universal, synthOrder := #[1], attrKind := AttributeKind.global }
  Meta.instanceExtension.add ent AttributeKind.global
theorem b21ResolvesWeak : (inferInstance : ItemSpec "ep2::b21").pre [] = False := rfl

#eval show MetaM Unit from do
  let env ← getEnv
  let ctx := SpecAuditCtx.forLiveMeta env 400
  let ec := instanceEntryCandidates env ctx.toolchainProv `Trusted.VerificationResult.ItemSpec "ep2::b21" 256
  IO.println s!"B2_1_forged_instance_entry_scan: listed={ec.contains ``b21Universal} strongListed={ec.contains ``b21Strong}"
  -- (Every `defId` is ambiguous in this file after the native-evaluator canaries, so the check is
  -- that the forged entry itself is named among the candidates.)
  let g1 ← auditItemSpecStrengthBySynth .item "ep2::b21" ``b21Cert (useSynthInstance := false)
  IO.println s!"{fmtTags "B2_1_forged_instance_entry_gate_no_synth" g1} names={g1.any (fun v => (v.detail.splitOn "b21Universal").length > 1)}"
  let g2 ← auditItemSpecStrengthBySynth .item "ep2::b21" ``b21Cert
  IO.println s!"{fmtTags "B2_1_forged_instance_entry_gate_synth" g2} names={g2.any (fun v => (v.detail.splitOn "b21Universal").length > 1)}"

/-! ### Episode 2 `A2` regressions (`.proj` / `recInfo` / `.local` / `default_instance` forged entries) -/

-- A2-1a: `.proj`-headed forged instance (`[c : A21aCarrier] → c.ty`) keyed like `ItemSpec "ep2::a21a"`.
instance a21aStrong : ItemSpec "ep2::a21a" where pre := ret10Pre; post := ret10Post
class A21aCarrier : Type 2 where
  ty : Type 1
  inst : ty
instance a21aCarrierInst : A21aCarrier where
  ty := ItemSpec "ep2::a21a"
  inst := { pre := fun _ => False, post := fun _ _ => True }
def a21aProjUniv [c : A21aCarrier] : c.ty := c.inst
def a21aCert : MultiMutantSpecCert a21aStrong.pre a21aStrong.post := ret10MultiCert
run_cmd Elab.Command.liftTermElabM do
  let keys ← Meta.DiscrTree.mkPath (mkApp (mkConst ``ItemSpec) (mkStrLit "ep2::a21a"))
  let ent : Meta.InstanceEntry := { keys := keys, val := mkConst ``a21aProjUniv, priority := 5000, globalName? := some ``a21aProjUniv, synthOrder := #[0], attrKind := AttributeKind.global }
  Meta.instanceExtension.add ent AttributeKind.global
theorem a21aResolvesWeak : (inferInstance : ItemSpec "ep2::a21a").pre [] = False := rfl

-- A2-1b: `recInfo`-headed forged instance (`Bool.rec _ s.a s.b s.tag`) keyed like `ItemSpec "ep2::a21b"`.
instance a21bStrong : ItemSpec "ep2::a21b" where pre := ret10Pre; post := ret10Post
class A21bSum : Type 2 where
  tag : Bool
  a : Type 1
  b : Type 1
  inst : Bool.rec (motive := fun _ => Type 1) a b tag
instance a21bSumInst : A21bSum where
  tag := false
  a := ItemSpec "ep2::a21b"
  b := PUnit
  inst := { pre := fun _ => False, post := fun _ _ => True }
def a21bRecUniv [s : A21bSum] : Bool.rec (motive := fun _ => Type 1) s.a s.b s.tag := s.inst
def a21bCert : MultiMutantSpecCert a21bStrong.pre a21bStrong.post := ret10MultiCert
run_cmd Elab.Command.liftTermElabM do
  let keys ← Meta.DiscrTree.mkPath (mkApp (mkConst ``ItemSpec) (mkStrLit "ep2::a21b"))
  let ent : Meta.InstanceEntry := { keys := keys, val := mkConst ``a21bRecUniv, priority := 5000, globalName? := some ``a21bRecUniv, synthOrder := #[0], attrKind := AttributeKind.global }
  Meta.instanceExtension.add ent AttributeKind.global
theorem a21bResolvesWeak : (inferInstance : ItemSpec "ep2::a21b").pre [] = False := rfl

-- A2-3: `.local` forged instance stored ONLY in `stateStack` (never in `newEntries` or `getModuleEntries`).
instance a23Strong : ItemSpec "ep2::a23" where pre := ret10Pre; post := ret10Post
class A23Holder (T : Type 1) where val : T
instance a23HolderInst : A23Holder (ItemSpec "ep2::a23") := ⟨{ pre := fun _ => False, post := fun _ _ => True }⟩
def a23LocUniv {T : Type 1} [h : A23Holder T] : T := h.val
def a23Cert : MultiMutantSpecCert a23Strong.pre a23Strong.post := ret10MultiCert
run_cmd Elab.Command.liftTermElabM do
  let keys ← Meta.DiscrTree.mkPath (mkApp (mkConst ``ItemSpec) (mkStrLit "ep2::a23"))
  let ent : Meta.InstanceEntry := { keys := keys, val := mkConst ``a23LocUniv, priority := 5000, globalName? := some ``a23LocUniv, synthOrder := #[1], attrKind := AttributeKind.local }
  Meta.instanceExtension.add ent AttributeKind.local
theorem a23ResolvesWeak : (inferInstance : ItemSpec "ep2::a23").pre [] = False := rfl

-- A2-6 + A3-2: forged `Meta.defaultInstanceExtension` entries (both under `ItemSpec` and under an
-- arbitrary class key in live `MetaM`).
def a26DefUniv [c : A21aCarrier] : c.ty := c.inst
def a32AliasDefUniv [c : A21aCarrier] : c.ty := c.inst
run_cmd Elab.Command.liftCoreM do
  modifyEnv fun env =>
    let env := Meta.defaultInstanceExtension.addEntry env { className := ``ItemSpec, instanceName := ``a26DefUniv, priority := 1000 }
    Meta.defaultInstanceExtension.addEntry env { className := `A32AliasClass, instanceName := ``a32AliasDefUniv, priority := 1000 }

#eval show MetaM Unit from do
  let env ← getEnv
  let ctx := SpecAuditCtx.forLiveMeta env 400
  let ecProj := instanceEntryCandidates env ctx.toolchainProv `Trusted.VerificationResult.ItemSpec "ep2::a21a" 256
  let ecRec := instanceEntryCandidates env ctx.toolchainProv `Trusted.VerificationResult.ItemSpec "ep2::a21b" 256
  let ecLoc := instanceEntryCandidates env ctx.toolchainProv `Trusted.VerificationResult.ItemSpec "ep2::a23" 256
  IO.println s!"A2_1a_proj_forged_scan: listed={ecProj.contains ``a21aProjUniv} defInst={ecProj.contains ``a26DefUniv} aliasDefInst={ecProj.contains ``a32AliasDefUniv}"
  IO.println s!"A2_1b_rec_forged_scan: listed={ecRec.contains ``a21bRecUniv}"
  IO.println s!"A2_3_local_stateStack_scan: listed={ecLoc.contains ``a23LocUniv}"
  let gp ← auditItemSpecStrengthBySynth .item "ep2::a21a" ``a21aCert (useSynthInstance := false)
  let gr ← auditItemSpecStrengthBySynth .item "ep2::a21b" ``a21bCert (useSynthInstance := false)
  let gl ← auditItemSpecStrengthBySynth .item "ep2::a23" ``a23Cert (useSynthInstance := false)
  IO.println s!"{fmtTags "A2_1a_proj_forged_gate" gp} names={gp.any (fun v => (v.detail.splitOn "a21aProjUniv").length > 1)}"
  IO.println s!"{fmtTags "A2_1b_rec_forged_gate" gr} names={gr.any (fun v => (v.detail.splitOn "a21bRecUniv").length > 1)}"
  IO.println s!"{fmtTags "A2_3_local_stateStack_gate" gl} names={gl.any (fun v => (v.detail.splitOn "a23LocUniv").length > 1)}"
"##

private def collectPartsJson (baseDir : System.FilePath) (modName : String) : IO Lean.Json := do
  let mut olean : Array Lean.Json := #[]
  for ext in #["olean", "olean.server", "olean.private"] do
    let p := baseDir / s!"{modName}.{ext}"
    if ← p.pathExists then olean := olean.push (Lean.toJson p.toString)
  let mut ir : Array Lean.Json := #[]
  for ext in #["ir.sig", "ir"] do
    let p := baseDir / s!"{modName}.{ext}"
    if ← p.pathExists then ir := ir.push (Lean.toJson p.toString)
  return Lean.Json.arr #[Lean.Json.arr olean, Lean.Json.arr ir]

private def runLiveAuditorHarness : IO Unit := do
  let pid ← IO.Process.getPID
  let nanos ← IO.monoNanosNow
  let tmpDir : System.FilePath := s!"/tmp/anneal_ep2_tests_{pid}_{nanos}"
  IO.FS.createDirAll tmpDir
  try
    let leanBin := (← IO.getEnv "LEAN").getD "lean"
    let basePath := (← IO.getEnv "LEAN_PATH").getD ""
    let childPath := if basePath.isEmpty then tmpDir.toString else s!"{tmpDir}:{basePath}"
    let buildOut ← IO.Process.output {
      cmd := leanBin
      args := #["-DwarningAsError=true", "-o", (tmpDir / "OleanEnvAuditor.olean").toString,
                "trusted/audit/OleanEnvAuditor.lean"]
    }
    if buildOut.exitCode != 0 then
      throw <| IO.userError s!"OleanEnvAuditor.lean build failed ({buildOut.exitCode}):\n{buildOut.stdout}\n{buildOut.stderr}"
    let harnessPath := tmpDir / "Ep2LiveHarness.lean"
    IO.FS.writeFile harnessPath liveHarnessSource
    let runOut ← IO.Process.output {
      cmd := leanBin
      args := #[harnessPath.toString]
      env := #[("LEAN_PATH", some childPath)]
    }
    if runOut.exitCode != 0 then
      throw <| IO.userError s!"Ep2LiveHarness failed ({runOut.exitCode}):\n{runOut.stdout}\n{runOut.stderr}"
    for line in runOut.stdout.splitOn "\n" do
      if !line.isEmpty && !line.startsWith tmpDir.toString then
        IO.println line
    -- Vector V7 (statement-origin leak vs proof-only use) via compiled `.olean` + live `OleanEnvAuditor.lean`.
    let prefOut ← IO.Process.output { cmd := leanBin, args := #["--print-prefix"] }
    if prefOut.exitCode != 0 then
      throw <| IO.userError s!"lean --print-prefix failed: {prefOut.stderr}"
    let sysroot := prefOut.stdout.trimAscii.toString
    let v7Dir := tmpDir / "v7"
    IO.FS.createDirAll v7Dir
    IO.FS.writeFile (v7Dir / "V7Theory.lean") "prelude\nimport Init.Prelude\ndef UntrustedProp : Prop := True\n"
    IO.FS.writeFile (v7Dir / "V7Leak.lean") "prelude\nimport V7Theory\ntheorem leaked : UntrustedProp := True.intro\n"
    IO.FS.writeFile (v7Dir / "V7Ok.lean") "prelude\nimport V7Theory\ntheorem proofOnly : True := (fun (_ : UntrustedProp) => True.intro) True.intro\n"
    let v7Path := if basePath.isEmpty then v7Dir.toString else s!"{v7Dir}:{basePath}"
    for m in #["V7Theory", "V7Leak", "V7Ok"] do
      let cOut ← IO.Process.output {
        cmd := leanBin
        args := #["-R", v7Dir.toString, "-o", (v7Dir / s!"{m}.olean").toString, (v7Dir / s!"{m}.lean").toString]
        env := #[("LEAN_PATH", some v7Path)]
      }
      if cOut.exitCode != 0 then
        throw <| IO.userError s!"V7 compile {m} failed: {cOut.stdout}\n{cOut.stderr}"
    let pTheory ← collectPartsJson v7Dir "V7Theory"
    let pLeak ← collectPartsJson v7Dir "V7Leak"
    let pOk ← collectPartsJson v7Dir "V7Ok"
    let runV7 (label : String) (modName : String) (modParts : Lean.Json) : IO Unit := do
      let reqPath := v7Dir / s!"{label}.req.json"
      let resPath := v7Dir / s!"{label}.res.json"
      let req := Lean.Json.mkObj [
        ("mode", Lean.toJson "olean-audit"),
        ("sysroot", Lean.toJson sysroot),
        ("foundation", Lean.toJson (#["Init.Prelude"] : Array String)),
        ("artifacts", Lean.Json.arr #[
          Lean.Json.arr #[Lean.toJson "V7Theory", pTheory],
          Lean.Json.arr #[Lean.toJson modName, modParts]]),
        ("roots", Lean.toJson (#["V7Theory", modName] : Array String)),
        ("modules", Lean.toJson (#["V7Theory", modName] : Array String)),
        ("axioms", Lean.Json.arr #[
          Lean.Json.arr #[Lean.toJson "propext", Lean.toJson "Init.Core"],
          Lean.Json.arr #[Lean.toJson "Quot.sound", Lean.toJson "Init.Prelude"],
          Lean.Json.arr #[Lean.toJson "Classical.choice", Lean.toJson "Init.Prelude"]]),
        ("claimModules", Lean.toJson (#[modName] : Array String)),
        ("statementForbidden", Lean.toJson (#["V7Theory"] : Array String)),
        ("statementUnfold", Lean.toJson (#[modName] : Array String)),
        ("scope", Lean.toJson label)
      ]
      IO.FS.writeFile reqPath req.compress
      let _ ← IO.Process.output {
        cmd := leanBin
        args := #["--run", "trusted/audit/OleanEnvAuditor.lean", reqPath.toString, resPath.toString]
      }
      let respText ← IO.FS.readFile resPath
      let respJson ← IO.ofExcept (Lean.Json.parse respText)
      let isOk : Bool := (respJson.getObjValAs? Bool "ok").toOption.getD false
      let hasLeak : Bool := decide ((respText.splitOn "statementOriginLeak").length > 1)
      IO.println s!"{label}: ok={isOk} statementOriginLeak={hasLeak}"
    runV7 "V7_statement_leak" "V7Leak" pLeak
    runV7 "V7_proof_only_ok" "V7Ok" pOk
  finally
    IO.FS.removeDirAll tmpDir
  let stillExists ← tmpDir.pathExists
  IO.println s!"tmp_clean={!stillExists}"

/--
info: V1_direct_sorry: #[sorryAxiomReached]
V2_tactic_sorryAx: #[sorryAxiomReached]
V3_custom_axiom: #[unapprovedAxiom]
V3_private_axiom: #[unapprovedAxiom]
V3_trust_compiler: #[nativeDecideReached]
V4_native_decide: #[nativeDecideReached]
V5_partial: #[partialOrUnsafeRecDependency]
V5_safe_gcd: #[]
V6_unsafe: #[unsafeDeclaration]
V6_implemented_by: #[compilerOverrideAttribute]
V6_extern: #[compilerOverrideAttribute]
V6_export: #[compilerOverrideAttribute]
V6_csimp: #[compilerOverrideAttribute]
V6_init: #[compilerOverrideAttribute]
V8_vacuous_claim_wrong_cert: #[specStrengthCertInvalidType]
V9_trivial_claim_wrong_cert: #[specStrengthCertInvalidType]
V9_classical_cert_rejected: #[unapprovedAxiom]
A1_4_sorry_before_coverage: #[sorryAxiomReached]
R8_coverage_gap: #[specStrengthCoverageGap]
R11_stateless_claim_ok: #[]
R11_stateless_det_ok: #[]
A1_6_stateful_claim_ok: #[]
A1_6_total_claim_ok: #[]
A1_6_modular_multi_ok: #[]
A1_6_modular_det_ok: #[]
A1_6_modular_wrong_rely: #[specStrengthCertInvalidType]
A1_6_non_theorem_claim_rejected: #[specStrengthCertInvalidType]
S5_det_rejected_for_input_sensitive: #[specStrengthCertInvalidType]
A2_4b_modular_input_sensitive_ok: #[]
A3_3a_sunfold_vacuous_claim: #[specStrengthCertInvalidType]
A3_3b_sunfold_fake_coverage: #[specStrengthCoverageGap]
A3_3c_sunfold_hidden_shadow: #[specInstanceAmbiguous]
A3_3d_sunfold_unit_as_cert: #[specStrengthCertInvalidType]
A3_3e_sunfold_trivial_as_claim: #[specStrengthCertInvalidType]
R7_duplicate_shadow: #[specInstanceAmbiguous]
A1_2a_let_shadow: #[specInstanceAmbiguous]
A1_2b_beta_shadow: #[specInstanceAmbiguous]
A1_2c_deep_alias_shadow: #[specInstanceAmbiguous]
A1_2d_proj_shadow: #[specInstanceAmbiguous]
S3a_subclass_chain_shadow: #[specInstanceAmbiguous]
S3b_parametric_chain_shadow: #[specInstanceAmbiguous]
B4_3_warm_meta_cache: #[specInstanceAmbiguous]
B4_4a_zeta_false: #[specInstanceAmbiguous]
B4_4b_iota_false: #[specInstanceAmbiguous]
B4_4c_custom_unfold_pred: #[specInstanceAmbiguous]
B4_4d_hostile_config_clean_control: #[]
B4_5a_unassigned_mvar: #[specStrengthCertInvalidType]
B4_5b_mvar_under_binder: #[specStrengthCertInvalidType]
B4_5d_fvar_rejected: #[specStrengthCertInvalidType]
B4_5e_assigned_mvar_ok: #[]
B4_6a_natrec: pure=true meta=true
B4_6b_quot: pure=true meta=true
B4_6c_proj70: pure=true meta=true
B4_6d_indexed_vec: pure=true meta=true
B4_6e_k_recursor: pure=true meta=true
B4_6h_unspecified_zero_fp: pure=true meta=true
B4_6i_real_model_exact_one: pure=true meta=true
A4_3a_core_cache_poison: #[specInstanceAmbiguous]
A4_3b_withExporting: #[specInstanceAmbiguous]
A4_3c_hostile_options_control: #[]
B1_1_theorem_major_scanners: pure=true meta=true
B1_1_theorem_major_synth_gate: #[specInstanceAmbiguous]
B1_1_theorem_major_gate_no_synth: #[specInstanceAmbiguous]
B1_1_theorem_major_zero_fp_control: pure=true meta=true
B1_6_poly_sorry_cert_reports_sorry: #[sorryAxiomReached]
A2_7_erased_instance_rejected_no_synth: #[specStrengthCertMissing]
A4_5a_reduceBool: pure=true meta=true
A4_5b_reduceNat_asymmetry: pure=true meta=true
A4_5b_reduceNat_synth_gate: #[specInstanceAmbiguous]
A4_7_exp_branching_linear_budget: listed=true fast=true
B1_2_string_literal_projection: pure=true meta=true
B1_3_kernel_nat_gmp_major: pure=true meta=true
B1_4_native_evaluator_never_run: reduceBool=true reduceNat=true clean=true
A1_2a_expected_native_rejected: #[nativeDecideReached]
A1_2b_poly_sorry_claim_reports_sorry: #[sorryAxiomReached]
A1_3_dep_rec_shadow: pure=true meta=true
A1_3_dep_rec_synth_gate: #[specInstanceAmbiguous] names=true
A1_4_string_rec_literal: pure=true meta=true
B2_1_forged_instance_entry_scan: listed=true strongListed=true
B2_1_forged_instance_entry_gate_no_synth: #[specInstanceAmbiguous] names=true
B2_1_forged_instance_entry_gate_synth: #[specInstanceAmbiguous] names=true
A2_1a_proj_forged_scan: listed=true defInst=true aliasDefInst=true
A2_1b_rec_forged_scan: listed=true
A2_3_local_stateStack_scan: listed=true
A2_1a_proj_forged_gate: #[specInstanceAmbiguous] names=true
A2_1b_rec_forged_gate: #[specInstanceAmbiguous] names=true
A2_3_local_stateStack_gate: #[specInstanceAmbiguous] names=true
V7_statement_leak: ok=false statementOriginLeak=true
V7_proof_only_ok: ok=true statementOriginLeak=false
tmp_clean=true
-/
#guard_msgs in
#eval runLiveAuditorHarness

end Anneal.OleanSpecStrengthAuditorTests
