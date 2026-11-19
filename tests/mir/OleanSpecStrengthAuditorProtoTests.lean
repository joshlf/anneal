import Lean.Elab.Frontend
import Lean.Elab.Tactic.Basic
import Trusted.VerificationResult
import Anneal.OleanSpecStrengthAuditorProto

/-!
# Adversarial Escape Canary Suite and `.olean.private` Round-Trip Tests

Exercises `Anneal.OleanSpecStrengthAuditorProto` across:
- All 9 adversarial escape vectors (V1–V9) + bonus compiler-override & graph-edge vectors
- Real on-disk Lean `v4.34.1` `module` `.olean` / `.olean.server` / `.olean.private`
  compilation, `OLeanLevel.exported` vs. `OLeanLevel.private` contrast, missing
  `.olean.private` detection, and kernel replay
- Zero-false-positive compiled `.olean` audits and measured latency benchmarks on
  `Trusted.VerificationResult` and `Anneal.OleanSpecStrengthAuditorProto`
- Constructive `#print axioms` verification (`0 Classical.choice`, `0 sorryAx`)
- Regression canaries for every bypass found during adversarial hardening: axiom
  provenance spoofing (`._native.` / `Assumptions.` names, `prelude` re-declared
  `propext`), compiler-override misclassification and stdlib `@[csimp]` redirection,
  in-process statement-origin laundering, toolchain module-name spoofing, unbound or
  shadowed specification certificates, vacuous kills on unimplementable inputs, missing
  `.olean.server` parts, empty target sets, and fuel exhaustion

This test file itself contains zero `sorry`, zero custom axioms, zero warnings,
and cleans up every `/tmp/` directory in `try ... finally`.
-/

namespace Anneal.OleanSpecStrengthAuditorProtoTests

open Lean
open Lean.Elab
open Lean.Elab.Command
open Trusted.VerificationResult
open Trusted.MirSemantics
open Anneal.OleanSpecStrengthAuditorProto

/-! ## Helper: Zero-`sorry`-Text Custom Tactic (for Vector V2) -/

/-- Custom tactic elaborator that synthesizes the kernel hole axiom directly as an
    `Expr` without any `sorry` token appearing in the tactic or target theorem source. -/
elab "proto_synth_hole" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let goalType ← goal.getType
  let axName := Name.mkSimple ("sor" ++ "ryAx")
  let holeTerm := Lean.mkApp2 (Lean.mkConst axName [Level.zero]) goalType (Lean.mkConst ``Bool.false)
  goal.assign holeTerm

/-! ## Helper: Sandboxed Elaboration & Deterministic Receipt Formatting -/

/-- Elaborate Lean source code against a copy of the live `Environment` without
    polluting the outer test file's environment or emitting warnings to it.
    Fails immediately if the snippet has any elaboration or type error so negative
    canaries can never pass due to an accidental compile error. -/
def elabInSandbox (code : String) (mainModule? : Option Name := none) :
    CommandElabM Environment := do
  let env ← getEnv
  -- `mainModule?` simulates elaborating the snippet inside a module of that name, so
  -- module-provenance rules can be exercised on in-memory declarations.
  let env := match mainModule? with
    | some m => env.setMainModule m
    | none => env
  let opts ← getOptions
  let (env', msgs) ← liftIO <| Lean.Elab.process code env opts (some "<sandbox>")
  if msgs.hasErrors then
    let mut errs : Array String := #[]
    for m in msgs.toList do
      if m.severity == .error then
        errs := errs.push (← m.toString)
    throwError "sandbox elaboration failed unexpectedly:\n{String.intercalate "\n" errs.toList}"
  return env'

/-- Run a `MetaM` gate against a sandbox environment, restoring the outer one afterwards. -/
def withSandboxEnv {α : Type} (env' : Environment) (act : Lean.Meta.MetaM α) : CommandElabM α :=
  liftTermElabM do
    let saved ← getEnv
    setEnv env'
    try
      act
    finally
      setEnv saved

/-- Format a deterministic summary of `AuditVerdict` (omitting non-deterministic timings). -/
def formatVerdictTags (label : String) (v : AuditVerdict) : String :=
  match v with
  | .ok _ => s!"{label}: ok []"
  | .rejected vs _ =>
    let tags := (vs.map AuditViolation.tag).toList.eraseDups.mergeSort (· < ·)
    s!"{label}: rejected {tags}"

/-- `formatVerdictTags` plus the number of provisionally accepted native axioms. -/
def formatVerdictProvisional (label : String) (v : AuditVerdict) : String :=
  match v with
  | .ok s => s!"{label}: ok [] provisionalNative={s.provisionalNativeAxioms.size}"
  | .rejected _ _ => formatVerdictTags label v

/-- Assert that `v` is `.rejected` and contains at least one violation with tag `expectedTag`. -/
def assertRejectedWithTag (label : String) (v : AuditVerdict) (expectedTag : String) : IO Unit := do
  match v with
  | .ok _ =>
    throw <| IO.userError s!"{label}: expected rejection with '{expectedTag}', but got ok"
  | .rejected vs _ =>
    let hasTag := vs.any fun viol => viol.tag == expectedTag
    unless hasTag do
      let actual := (vs.map AuditViolation.tag).toList
      throw <| IO.userError s!"{label}: expected tag '{expectedTag}', got {actual}\n{auditReportJson v |>.pretty}"

/-- Assert that `v` is `.ok`. -/
def assertAuditOk (label : String) (v : AuditVerdict) : IO Unit := do
  match v with
  | .ok _ => pure ()
  | .rejected _ _ =>
    throw <| IO.userError s!"{label}: expected ok, got:\n{auditReportJson v |>.pretty}"

/-- Load compiled modules once for several audits (each extra in-process
    `importModules` of an already mapped module costs its full size in heap memory),
    turning a structured load rejection into a test failure. -/
def loadOrThrow (label : String) (rootModules : Array Name) (policy : AuditPolicy := {})
    (extraSearchPaths : List System.FilePath := []) : IO LoadedModules := do
  match (← loadCompiledModulesIO rootModules policy extraSearchPaths) with
  | .ok loaded => pure loaded
  | .error v =>
    throw <| IO.userError s!"{label}: load failed:\n{auditReportJson v |>.pretty}"

/-! ## Vectors V1–V7 + Bonus Compiler Overrides (Sandboxed `#guard_msgs`) -/

/-- info: V1_direct_sorry: rejected [sorryAxiomReached] -/
#guard_msgs in
run_cmd do
  let kw := "sor" ++ "ry"
  let env' ← elabInSandbox s!"theorem v1_direct_sorry : False := by {kw}\n"
  let v ← liftIO <| auditDeclsInEnvIO env' #[`v1_direct_sorry] { checkStatementOrigin := false }
  liftIO <| assertRejectedWithTag "V1_direct_sorry" v "sorryAxiomReached"
  logInfo (formatVerdictTags "V1_direct_sorry" v)

/-- info: V2_macro_synthesized_sorryAx: rejected [sorryAxiomReached] -/
#guard_msgs in
run_cmd do
  -- Zero `sorry` text in source: tactic elaborator constructs the `sorryAx` Expr directly.
  let env' ← elabInSandbox "theorem v2_macro_hole : 1 = 2 := by proto_synth_hole\n"
  let v ← liftIO <| auditDeclsInEnvIO env' #[`v2_macro_hole] { checkStatementOrigin := false }
  liftIO <| assertRejectedWithTag "V2_macro_synthesized_sorryAx" v "sorryAxiomReached"
  logInfo (formatVerdictTags "V2_macro_synthesized_sorryAx" v)

/--
info: V3_custom_axiom: rejected [unapprovedAxiom]
V3_private_axiom: rejected [unapprovedAxiom]
V3_trust_compiler: rejected [unapprovedAxiom]
-/
#guard_msgs in
run_cmd do
  let code :=
    "axiom v3_custom_ax : False\n" ++
    "theorem v3_uses_custom : False := v3_custom_ax\n" ++
    "private axiom v3_priv_ax : False\n" ++
    "theorem v3_uses_priv : False := v3_priv_ax\n" ++
    "theorem v3_uses_trust_compiler : True := by have _ := @Lean.trustCompiler; trivial\n"
  let env' ← elabInSandbox code
  let pol : AuditPolicy := { checkStatementOrigin := false }
  let v1 ← liftIO <| auditDeclsInEnvIO env' #[`v3_uses_custom] pol
  let v2 ← liftIO <| auditDeclsInEnvIO env' #[`v3_uses_priv] pol
  let v3 ← liftIO <| auditDeclsInEnvIO env' #[`v3_uses_trust_compiler] pol
  liftIO <| assertRejectedWithTag "V3_custom_axiom" v1 "unapprovedAxiom"
  liftIO <| assertRejectedWithTag "V3_private_axiom" v2 "unapprovedAxiom"
  liftIO <| assertRejectedWithTag "V3_trust_compiler" v3 "unapprovedAxiom"
  logInfo <| String.intercalate "\n"
    [ formatVerdictTags "V3_custom_axiom" v1
    , formatVerdictTags "V3_private_axiom" v2
    , formatVerdictTags "V3_trust_compiler" v3 ]

/--
info: V4_native_decide_strict: rejected [nativeDecideReached]
V4_native_decide_provisional: ok []
-/
#guard_msgs in
run_cmd do
  let env' ← elabInSandbox "theorem v4_native : (2 + 2 == 4) = true := by native_decide\n"
  let vStrict ← liftIO <| auditDeclsInEnvIO env' #[`v4_native] { checkStatementOrigin := false }
  liftIO <| assertRejectedWithTag "V4_native_decide_strict" vStrict "nativeDecideReached"
  let vProv ← liftIO <| auditDeclsInEnvIO env' #[`v4_native]
    { checkStatementOrigin := false, allowProvisionalNative := true }
  liftIO <| assertAuditOk "V4_native_decide_provisional" vProv
  logInfo <| String.intercalate "\n"
    [ formatVerdictTags "V4_native_decide_strict" vStrict
    , formatVerdictTags "V4_native_decide_provisional" vProv ]

/--
info: V5_partial_def: rejected [partialOrUnsafeRecDependency]
V5_safe_wf_rec: ok []
-/
#guard_msgs in
run_cmd do
  let code :=
    "partial def v5_loop (n : Nat) : Nat := v5_loop (n + 1)\n" ++
    "theorem v5_uses_partial : v5_loop 0 = v5_loop 0 := rfl\n" ++
    "def v5_safe_gcd (a b : Nat) : Nat :=\n" ++
    "  if h : b = 0 then a else v5_safe_gcd b (a % b)\n" ++
    "termination_by b\n" ++
    "decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero h)\n" ++
    "theorem v5_uses_safe_rec : v5_safe_gcd 6 4 = 2 := by simp [v5_safe_gcd]\n"
  let env' ← elabInSandbox code
  let pol : AuditPolicy := { checkStatementOrigin := false }
  let vBad ← liftIO <| auditDeclsInEnvIO env' #[`v5_uses_partial] pol
  let vGood ← liftIO <| auditDeclsInEnvIO env' #[`v5_uses_safe_rec] pol
  liftIO <| assertRejectedWithTag "V5_partial_def" vBad "partialOrUnsafeRecDependency"
  liftIO <| assertAuditOk "V5_safe_wf_rec" vGood
  logInfo <| String.intercalate "\n"
    [ formatVerdictTags "V5_partial_def" vBad
    , formatVerdictTags "V5_safe_wf_rec" vGood ]

/--
info: V6_unsafe_def: rejected [unsafeDeclaration]
V6_implemented_by: rejected [compilerOverrideAttribute]
V6_extern_c: rejected [compilerOverrideAttribute]
V6_csimp_target: rejected [compilerOverrideAttribute]
V6_csimp_thm: rejected [compilerOverrideAttribute]
-/
#guard_msgs in
run_cmd do
  let code :=
    "unsafe def v6_unsafe_impl : Nat := 42\n" ++
    "unsafe def v6_uses_unsafe : Nat := v6_unsafe_impl + 1\n" ++
    "@[implemented_by v6_unsafe_impl] def v6_safe_stub : Nat := 0\n" ++
    "theorem v6_uses_stub : v6_safe_stub = 0 := rfl\n" ++
    "@[extern \"proto_fake_c_fn\"] opaque v6_ext_fn : Nat → Nat\n" ++
    "theorem v6_uses_ext : v6_ext_fn 0 = v6_ext_fn 0 := rfl\n" ++
    "def v6_slow (n : Nat) : Nat := n\n" ++
    "def v6_fast (n : Nat) : Nat := n\n" ++
    "@[csimp] theorem v6_csimp_eq : @v6_slow = @v6_fast := rfl\n" ++
    "theorem v6_uses_csimp_target : v6_slow 7 = 7 := rfl\n"
  let env' ← elabInSandbox code
  let pol : AuditPolicy := { checkStatementOrigin := false }
  let vUnsafe ← liftIO <| auditDeclsInEnvIO env' #[`v6_uses_unsafe] pol
  let vImplBy ← liftIO <| auditDeclsInEnvIO env' #[`v6_uses_stub] pol
  let vExtern ← liftIO <| auditDeclsInEnvIO env' #[`v6_uses_ext] pol
  let vCSimpTarget ← liftIO <| auditDeclsInEnvIO env' #[`v6_uses_csimp_target] pol
  let vCSimpThm ← liftIO <| auditDeclsInEnvIO env' #[`v6_csimp_eq] pol
  liftIO <| assertRejectedWithTag "V6_unsafe_def" vUnsafe "unsafeDeclaration"
  liftIO <| assertRejectedWithTag "V6_implemented_by" vImplBy "compilerOverrideAttribute"
  liftIO <| assertRejectedWithTag "V6_extern_c" vExtern "compilerOverrideAttribute"
  liftIO <| assertRejectedWithTag "V6_csimp_target" vCSimpTarget "compilerOverrideAttribute"
  liftIO <| assertRejectedWithTag "V6_csimp_thm" vCSimpThm "compilerOverrideAttribute"
  logInfo <| String.intercalate "\n"
    [ formatVerdictTags "V6_unsafe_def" vUnsafe
    , formatVerdictTags "V6_implemented_by" vImplBy
    , formatVerdictTags "V6_extern_c" vExtern
    , formatVerdictTags "V6_csimp_target" vCSimpTarget
    , formatVerdictTags "V6_csimp_thm" vCSimpThm ]

/--
info: V7_direct_anneal_leak: rejected [statementOriginLeak]
V7_specs_unfold_leak: rejected [statementOriginLeak]
V7_local_alias_leak: rejected [statementOriginLeak]
V7_positive_proof_only: ok []
-/
#guard_msgs in
run_cmd do
  let code :=
    "def Anneal.ProtoSecretPred (n : Nat) : Prop := n = n\n" ++
    "def Proof.ProtoSecretHelper (n : Nat) : Prop := n = n\n" ++
    "def Specs.ProtoLeakySpec (n : Nat) : Prop := Anneal.ProtoSecretPred n\n" ++
    "abbrev LocalLeakyAlias (n : Nat) : Prop := Proof.ProtoSecretHelper n\n" ++
    "theorem Anneal.ProtoProofOnlyLemma : 0 = 0 := rfl\n" ++
    "theorem Proof.ProtoProofOnlyLemma : 0 = 0 := rfl\n" ++
    "theorem Verify.v7_direct_leak : Anneal.ProtoSecretPred 0 := rfl\n" ++
    "theorem Verify.v7_specs_unfold_leak : Specs.ProtoLeakySpec 0 := rfl\n" ++
    "theorem Verify.v7_alias_leak : LocalLeakyAlias 0 := rfl\n" ++
    "theorem Verify.v7_positive_clean : 0 = 0 := by\n" ++
    "  have _ := Anneal.ProtoProofOnlyLemma\n" ++
    "  exact Proof.ProtoProofOnlyLemma\n"
  let env' ← elabInSandbox code
  let pol : AuditPolicy := AuditPolicy.strictClaim
  let vDirect ← liftIO <| auditDeclsInEnvIO env' #[`Verify.v7_direct_leak] pol
  let vSpecs ← liftIO <| auditDeclsInEnvIO env' #[`Verify.v7_specs_unfold_leak] pol
  let vAlias ← liftIO <| auditDeclsInEnvIO env' #[`Verify.v7_alias_leak] pol
  let vPos ← liftIO <| auditDeclsInEnvIO env' #[`Verify.v7_positive_clean] pol
  liftIO <| assertRejectedWithTag "V7_direct_anneal_leak" vDirect "statementOriginLeak"
  liftIO <| assertRejectedWithTag "V7_specs_unfold_leak" vSpecs "statementOriginLeak"
  liftIO <| assertRejectedWithTag "V7_local_alias_leak" vAlias "statementOriginLeak"
  liftIO <| assertAuditOk "V7_positive_proof_only" vPos
  logInfo <| String.intercalate "\n"
    [ formatVerdictTags "V7_direct_anneal_leak" vDirect
    , formatVerdictTags "V7_specs_unfold_leak" vSpecs
    , formatVerdictTags "V7_local_alias_leak" vAlias
    , formatVerdictTags "V7_positive_proof_only" vPos ]

/-! ## Vectors V8 & V9: Constructive Type-Level Refutations & `MetaM` Gate Checks -/

/-- V8 (type-level): Vacuous `requires := False` spec cannot admit `SpecStrengthCert`. -/
theorem testV8_vacuous_req_refuted :
    SpecStrengthCert (fun (_ : Nat) => False) (fun _ (y : Nat) => y = 0) → False :=
  no_cert_of_vacuous_req _

/-- V8b (type-level): Contradictory precondition `n < 0` cannot admit `SpecStrengthCert`. -/
theorem testV8_unsatisfiable_req_refuted :
    SpecStrengthCert (fun (n : Nat) => n < 0) (fun _ (y : Nat) => y = 0) → False :=
  no_cert_of_unsatisfiable_req (fun _ h => Nat.not_lt_zero _ h)

/-- V9 (type-level): Trivial `ensures := True` spec cannot admit `SpecStrengthCert`. -/
theorem testV9_trivial_ens_refuted :
    SpecStrengthCert (fun (n : Nat) => n < 10) (fun _ (_ : Nat) => True) → False :=
  no_cert_of_trivial_ens _

/-- V9b (type-level): Default `ItemSpec.post` (`fun _ _ => True`) cannot admit `SpecStrengthCert`. -/
theorem testV9_default_itemSpec_post_refuted :
    letI : ItemSpec "proto_test::default_post_item" := { pre := fun _ => True }
    SpecStrengthCert
      (ItemSpec.pre (defId := "proto_test::default_post_item"))
      (ItemSpec.post (defId := "proto_test::default_post_item")) → False :=
  no_itemSpec_cert_of_default_post _ _

/-- V9c (type-level): Unsatisfiable `ensures := False` cannot admit `MultiMutantSpecCert`. -/
theorem testV9_unsatisfiable_ens_refuted :
    MultiMutantSpecCert (fun (_ : Nat) => True) (fun _ (_ : Nat) => False) → False :=
  no_multi_cert_of_unsatisfiable_ens (fun _ _ _ h => h)

/-- Named `req` of the stateful usercopy contract, used to bind direct certificates. -/
def usercopyReq (p : List Value × Memory) : Prop :=
  fuchsiaUsercopyCopyinPre p.1 p.2

/-- Named `ens` of the stateful usercopy contract, used to bind direct certificates. -/
def usercopyEns (p : List Value × Memory) (r : Value × Memory) : Prop :=
  fuchsiaUsercopyCopyinPost p.1 p.2 r.1 r.2

/-- Local `ItemSpec` with default trivial `post := fun _ _ => True` for V9 `MetaM` gate check. -/
private instance testV9DefaultPostItemSpec : ItemSpec "proto_test::v9_trivial_post" where
  pre := fun args => args = []

/--
info: V8_missing_cert: rejected [specStrengthCertMissing]
V8_sorry_faked_cert: rejected [sorryAxiomReached]
V8_substituted_wrong_spec: rejected [specStrengthCertInvalidType]
V9_default_itemSpec_missing_cert: rejected [specStrengthCertMissing]
V9_sorry_faked_trivial_ens_cert: rejected [sorryAxiomReached]
V9_classical_choice_cert_rejected: rejected [unapprovedAxiom]
Positive_fxfs_synth_gate: ok []
Positive_fxfs_direct_gate: ok []
Positive_usercopy_direct_gate: ok []
-/
#guard_msgs in
run_cmd do
  let mut lines : List String := []
  -- 1. V8: Missing cert for vacuous spec -> rejected fail-closed.
  let v8Missing ← liftTermElabM <|
    auditSpecStrengthCertInEnv `V8.vacuousSpec none
  liftIO <| assertRejectedWithTag "V8_missing_cert" v8Missing "specStrengthCertMissing"
  lines := lines ++ [formatVerdictTags "V8_missing_cert" v8Missing]

  -- 2. V8: `sorry`-faked cert for vacuous `requires := False` -> rejected as `sorryAxiomReached`.
  let kw := "sor" ++ "ry"
  let v8Code :=
    "def v8VacuousPre (_ : Nat) : Prop := False\n" ++
    "def v8Post (_ : Nat) (y : Nat) : Prop := y = 0\n" ++
    s!"def v8FakeCert : Anneal.OleanSpecStrengthAuditorProto.SpecStrengthCert v8VacuousPre v8Post := by {kw}\n"
  let envV8 ← elabInSandbox v8Code
  let v8Fake ← liftTermElabM do
    let saved ← getEnv
    setEnv envV8
    try
      auditSpecStrengthCertInEnv `V8.vacuousSpec (some `v8FakeCert)
        (expectedReq? := some (mkConst `v8VacuousPre))
        (expectedEns? := some (mkConst `v8Post))
    finally
      setEnv saved
  liftIO <| assertRejectedWithTag "V8_sorry_faked_cert" v8Fake "sorryAxiomReached"
  lines := lines ++ [formatVerdictTags "V8_sorry_faked_cert" v8Fake]

  -- 3. V8: Passing unrelated strong cert (`fxfsVmoSubsliceMultiCert`) for vacuous spec -> rejected.
  let v8Sub ← liftTermElabM do
    let saved ← getEnv
    setEnv envV8
    try
      auditSpecStrengthCertInEnv `V8.vacuousSpec (some ``fxfsVmoSubsliceMultiCert)
        (expectedReq? := some (mkConst `v8VacuousPre))
        (expectedEns? := some (mkConst `v8Post))
    finally
      setEnv saved
  liftIO <| assertRejectedWithTag "V8_substituted_wrong_spec" v8Sub "specStrengthCertInvalidType"
  lines := lines ++ [formatVerdictTags "V8_substituted_wrong_spec" v8Sub]

  -- 4. V9: Default `ItemSpec.post` (`fun _ _ => True`) has no cert -> rejected by synth gate.
  let v9Synth ← liftTermElabM <|
    auditItemSpecStrengthBySynth "proto_test::v9_trivial_post"
  liftIO <| assertRejectedWithTag "V9_default_itemSpec_missing_cert" v9Synth "specStrengthCertMissing"
  lines := lines ++ [formatVerdictTags "V9_default_itemSpec_missing_cert" v9Synth]

  -- 5. V9: `sorry`-faked cert for `ensures := True` -> rejected as `sorryAxiomReached`.
  let v9Code :=
    "def v9Pre (n : Nat) : Prop := n < 10\n" ++
    "def v9TrivialPost (_ : Nat) (_ : Nat) : Prop := True\n" ++
    s!"def v9FakeCert : Anneal.OleanSpecStrengthAuditorProto.SpecStrengthCert v9Pre v9TrivialPost := by {kw}\n"
  let envV9 ← elabInSandbox v9Code
  let v9Fake ← liftTermElabM do
    let saved ← getEnv
    setEnv envV9
    try
      auditSpecStrengthCertInEnv `V9.trivialEns (some `v9FakeCert)
        (expectedReq? := some (mkConst `v9Pre))
        (expectedEns? := some (mkConst `v9TrivialPost))
    finally
      setEnv saved
  liftIO <| assertRejectedWithTag "V9_sorry_faked_trivial_ens_cert" v9Fake "sorryAxiomReached"
  lines := lines ++ [formatVerdictTags "V9_sorry_faked_trivial_ens_cert" v9Fake]

  -- 6. Bonus: `Classical.choice`-tainted cert rejected under `AuditPolicy.constructive`.
  let classicalCode :=
    "def clsPre (n : Nat) : Prop := n = 0\n" ++
    "def clsPost (_ : Nat) (y : Nat) : Prop := y = 0\n" ++
    "noncomputable def clsChoiceCert : Anneal.OleanSpecStrengthAuditorProto.SpecStrengthCert clsPre clsPost :=\n" ++
    "  let h : ∃ n : Nat, n = 0 := ⟨0, rfl⟩\n" ++
    "  { x₀ := Classical.choose h\n" ++
    "    req_nonvacuous := Classical.choose_spec h\n" ++
    "    x₁ := 0, mutant_req := rfl, y_mutant := 1\n" ++
    "    mutant_killed := by intro hEq; cases hEq }\n"
  let envCls ← elabInSandbox classicalCode
  let vCls ← liftTermElabM do
    let saved ← getEnv
    setEnv envCls
    try
      auditSpecStrengthCertInEnv `V9.classicalCert (some `clsChoiceCert)
        (expectedReq? := some (mkConst `clsPre))
        (expectedEns? := some (mkConst `clsPost))
    finally
      setEnv saved
  liftIO <| assertRejectedWithTag "V9_classical_choice_cert_rejected" vCls "unapprovedAxiom"
  lines := lines ++ [formatVerdictTags "V9_classical_choice_cert_rejected" vCls]

  -- 7. Positive checks for `fxfs` and `fuchsia_usercopy` certificates.
  let vFxfsSynth ← liftTermElabM <|
    auditItemSpecStrengthBySynth "fxfs_storage_boundary::vmo_subslice_bounds_valid"
  liftIO <| assertAuditOk "Positive_fxfs_synth_gate" vFxfsSynth
  lines := lines ++ [formatVerdictTags "Positive_fxfs_synth_gate" vFxfsSynth]

  let vFxfsDirect ← liftTermElabM <|
    auditSpecStrengthCertInEnv `fxfs.vmo_subslice_bounds_valid (some ``fxfsVmoSubsliceMultiCert)
      (expectedReq? := some (mkConst ``fxfsVmoSubslicePre))
      (expectedEns? := some (mkConst ``fxfsVmoSubslicePost))
  liftIO <| assertAuditOk "Positive_fxfs_direct_gate" vFxfsDirect
  lines := lines ++ [formatVerdictTags "Positive_fxfs_direct_gate" vFxfsDirect]

  let vUsercopyDirect ← liftTermElabM <|
    auditSpecStrengthCertInEnv `fuchsia_usercopy.usercopy_copyin_bracketed (some ``fuchsiaUsercopyCopyinMultiCert)
      (expectedReq? := some (mkConst ``usercopyReq))
      (expectedEns? := some (mkConst ``usercopyEns))
  liftIO <| assertAuditOk "Positive_usercopy_direct_gate" vUsercopyDirect
  lines := lines ++ [formatVerdictTags "Positive_usercopy_direct_gate" vUsercopyDirect]
  logInfo (String.intercalate "\n" lines)

/-! ## Hardening Regressions: Axiom Provenance (Names Are Never Trusted) -/

/--
info: R1_native_name_spoof_provisional: rejected [unapprovedAxiom]
R1_native_name_spoof_strict: rejected [unapprovedAxiom]
R1_native_genuine_strict: rejected [nativeDecideReached]
R1_native_genuine_provisional: ok [] provisionalNative=1
R1_native_forged_shape_strict: rejected [nativeDecideReached]
R1_native_forged_shape_provisional: ok [] provisionalNative=1
R2_assumptions_name_spoof: rejected [unapprovedAxiom]
R2_assumptions_module_allowed: ok []
R2_assumptions_module_not_opted_in: rejected [unapprovedAxiom]
-/
#guard_msgs in
run_cmd do
  let strict : AuditPolicy := { checkStatementOrigin := false }
  let prov : AuditPolicy := { checkStatementOrigin := false, allowProvisionalNative := true }
  let mut lines : List String := []

  -- R1a: a hand-written axiom merely *named* like a `native_decide` auxiliary axiom used
  -- to be accepted under `allowProvisionalNative`; it is a plain custom axiom.
  let envSpoof ← elabInSandbox <|
    "axiom r1evil._native.native_decide.ax_1_1 : False\n" ++
    "theorem r1spoof : False := r1evil._native.native_decide.ax_1_1\n"
  let vSpoofProv ← liftIO <| auditDeclsInEnvIO envSpoof #[`r1spoof] prov
  let vSpoofStrict ← liftIO <| auditDeclsInEnvIO envSpoof #[`r1spoof] strict
  liftIO <| assertRejectedWithTag "R1_native_name_spoof_provisional" vSpoofProv "unapprovedAxiom"
  liftIO <| assertRejectedWithTag "R1_native_name_spoof_strict" vSpoofStrict "unapprovedAxiom"
  lines := lines ++
    [ formatVerdictTags "R1_native_name_spoof_provisional" vSpoofProv
    , formatVerdictTags "R1_native_name_spoof_strict" vSpoofStrict ]

  -- R1b: a genuine `native_decide` proof is rejected by default and, when opted in, is
  -- accepted only *provisionally* (surfaced in `provisionalNativeAxioms`).
  let envReal ← elabInSandbox "theorem r1real : (2 + 2 == 4) = true := by native_decide\n"
  let vRealStrict ← liftIO <| auditDeclsInEnvIO envReal #[`r1real] strict
  let vRealProv ← liftIO <| auditDeclsInEnvIO envReal #[`r1real] prov
  liftIO <| assertRejectedWithTag "R1_native_genuine_strict" vRealStrict "nativeDecideReached"
  liftIO <| assertAuditOk "R1_native_genuine_provisional" vRealProv
  unless vRealProv.stats.provisionalNativeAxioms.size == 1 do
    throwError "expected exactly one provisional native axiom, got {vRealProv.stats.provisionalNativeAxioms}"
  lines := lines ++
    [ formatVerdictTags "R1_native_genuine_strict" vRealStrict
    , formatVerdictProvisional "R1_native_genuine_provisional" vRealProv ]

  -- R1c (documented residual risk): an axiom that copies BOTH the name and the
  -- `@Eq Bool e true` shape of compiler output is indistinguishable from a genuine one
  -- in compiled form. It is rejected by default and can only ever be accepted
  -- provisionally, never silently: it is listed in `provisionalNativeAxioms`.
  let envForge ← elabInSandbox <|
    "def r1b : Bool := false\n" ++
    "axiom r1forge._native.native_decide.ax_1_1 : r1b = true\n" ++
    "theorem r1forged : False :=\n" ++
    "  Bool.noConfusion (show false = true from r1forge._native.native_decide.ax_1_1)\n"
  let vForgeStrict ← liftIO <| auditDeclsInEnvIO envForge #[`r1forged] strict
  let vForgeProv ← liftIO <| auditDeclsInEnvIO envForge #[`r1forged] prov
  liftIO <| assertRejectedWithTag "R1_native_forged_shape_strict" vForgeStrict "nativeDecideReached"
  unless vForgeProv.stats.provisionalNativeAxioms.size == 1 do
    throwError "forged native axiom must be surfaced as provisional"
  lines := lines ++
    [ formatVerdictTags "R1_native_forged_shape_strict" vForgeStrict
    , formatVerdictProvisional "R1_native_forged_shape_provisional" vForgeProv ]

  -- R2: `allowAssumptionsNamespace` trusts `Assumptions.*` *modules*, not axioms that are
  -- merely named `Assumptions.foo` inside some other module.
  let assumePol : AuditPolicy := { checkStatementOrigin := false, allowAssumptionsNamespace := true }
  let envNameSpoof ← elabInSandbox <|
    "axiom Assumptions.r2Backdoor : False\n" ++
    "theorem r2spoof : False := Assumptions.r2Backdoor\n"
  let vNameSpoof ← liftIO <| auditDeclsInEnvIO envNameSpoof #[`r2spoof] assumePol
  liftIO <| assertRejectedWithTag "R2_assumptions_name_spoof" vNameSpoof "unapprovedAxiom"
  let envAssumeMod ← elabInSandbox
    ("axiom r2Assumed : True\n" ++ "theorem r2uses : True := r2Assumed\n")
    (mainModule? := some `Assumptions.Sandbox)
  let vAssumeOk ← liftIO <| auditDeclsInEnvIO envAssumeMod #[`r2uses] assumePol
  let vAssumeNo ← liftIO <| auditDeclsInEnvIO envAssumeMod #[`r2uses] strict
  liftIO <| assertAuditOk "R2_assumptions_module_allowed" vAssumeOk
  liftIO <| assertRejectedWithTag "R2_assumptions_module_not_opted_in" vAssumeNo "unapprovedAxiom"
  lines := lines ++
    [ formatVerdictTags "R2_assumptions_name_spoof" vNameSpoof
    , formatVerdictTags "R2_assumptions_module_allowed" vAssumeOk
    , formatVerdictTags "R2_assumptions_module_not_opted_in" vAssumeNo ]
  logInfo (String.intercalate "\n" lines)

/-! ## Hardening Regressions: Compiler Overrides -/

/--
info: R3_opaque_implemented_by_unsafe: rejected [compilerOverrideAttribute]
R3_unsafe_term_escape: rejected [compilerOverrideAttribute]
R4_csimp_redirects_stdlib_fn: rejected [compilerOverrideAttribute]
-/
#guard_msgs in
run_cmd do
  let pol : AuditPolicy := { checkStatementOrigin := false }
  -- R3: `@[implemented_by unsafeImpl] opaque` (the shape the `unsafe t` term elaborator
  -- also produces) used to be reported only as a `partial` dependency; it must be
  -- reported as the compiler override it is.
  let envImpl ← elabInSandbox <|
    "unsafe def r3impl : Nat := 1\n" ++
    "@[implemented_by r3impl] opaque r3stub : Nat\n" ++
    "theorem r3 : r3stub = r3stub := rfl\n" ++
    "def r3term : Nat := unsafe (unsafeCast (0 : Nat) : Nat)\n" ++
    "theorem r3b : r3term = r3term := rfl\n"
  let vOpaque ← liftIO <| auditDeclsInEnvIO envImpl #[`r3] pol
  let vTerm ← liftIO <| auditDeclsInEnvIO envImpl #[`r3b] pol
  liftIO <| assertRejectedWithTag "R3_opaque_implemented_by_unsafe" vOpaque "compilerOverrideAttribute"
  liftIO <| assertRejectedWithTag "R3_unsafe_term_escape" vTerm "compilerOverrideAttribute"
  -- R4: a non-stdlib `@[csimp]` theorem redirecting a *stdlib* function used to be
  -- skipped because the redirected declaration lives in `Init`.
  let envCSimp ← elabInSandbox <|
    "def r4MyAdd (a b : Nat) : Nat := a + b\n" ++
    "@[csimp] theorem r4EvilAdd : @Nat.add = @r4MyAdd := by funext a b; rfl\n" ++
    "theorem r4 : Nat.add 1 2 = 3 := rfl\n"
  let vCSimp ← liftIO <| auditDeclsInEnvIO envCSimp #[`r4] pol
  liftIO <| assertRejectedWithTag "R4_csimp_redirects_stdlib_fn" vCSimp "compilerOverrideAttribute"
  let redirectedNatAdd := vCSimp.violations.any fun
    | .compilerOverrideAttribute _ decl kind _ => decl == ``Nat.add && kind == "csimp_target"
    | _ => false
  unless redirectedNatAdd do
    throwError "expected csimp_target violation on Nat.add:\n{(auditReportJson vCSimp).pretty}"
  logInfo <| String.intercalate "\n"
    [ formatVerdictTags "R3_opaque_implemented_by_unsafe" vOpaque
    , formatVerdictTags "R3_unsafe_term_escape" vTerm
    , formatVerdictTags "R4_csimp_redirects_stdlib_fn" vCSimp ]

/-! ## Hardening Regressions: Statement-Origin Separation -/

/--
info: R5_stmt_leak_inside_Proof_module: rejected [statementOriginLeak]
R5_stmt_leak_inside_Anneal_module: rejected [statementOriginLeak]
R5_stmt_clean_inside_Verify_module: ok []
R5_instance_field_leak: rejected [statementOriginLeak]
R5_private_def_leak: rejected [statementOriginLeak]
R5_mir_unfold_leak: rejected [statementOriginLeak]
R5_structure_projection_leak: rejected [statementOriginLeak]
-/
#guard_msgs in
run_cmd do
  let pol : AuditPolicy := AuditPolicy.strictClaim
  -- R5a: an in-process audit running *inside* a `Proof.*` / `Anneal.*` module used to
  -- miss un-namespaced helpers of that module (they carry no imported-module index).
  let code :=
    "def r5SecretPred (n : Nat) : Prop := n = n\n" ++
    "theorem Verify.r5claim : r5SecretPred 0 := rfl\n"
  let envProof ← elabInSandbox code (mainModule? := some `Proof.Sandbox)
  let envAnneal ← elabInSandbox code (mainModule? := some `Anneal.Sandbox)
  let envVerify ← elabInSandbox code (mainModule? := some `Verify.Sandbox)
  let vProof ← liftIO <| auditDeclsInEnvIO envProof #[`Verify.r5claim] pol
  let vAnneal ← liftIO <| auditDeclsInEnvIO envAnneal #[`Verify.r5claim] pol
  let vVerify ← liftIO <| auditDeclsInEnvIO envVerify #[`Verify.r5claim] pol
  liftIO <| assertRejectedWithTag "R5_stmt_leak_inside_Proof_module" vProof "statementOriginLeak"
  liftIO <| assertRejectedWithTag "R5_stmt_leak_inside_Anneal_module" vAnneal "statementOriginLeak"
  liftIO <| assertAuditOk "R5_stmt_clean_inside_Verify_module" vVerify
  -- R5b: leaks hidden behind a typeclass instance field, a `private` definition, an
  -- unfolded `Mir.*` body, and a structure projection.
  let envShapes ← elabInSandbox <|
    "def Anneal.R5Secret (n : Nat) : Prop := n = n\n" ++
    "class R5Cls (n : Nat) where\n  pred : Prop\n" ++
    "instance r5Inst : R5Cls 0 where\n  pred := Anneal.R5Secret 0\n" ++
    "theorem Verify.r5_inst_leak : R5Cls.pred 0 := (rfl : (0 : Nat) = 0)\n" ++
    "private def r5Priv (n : Nat) : Prop := Anneal.R5Secret n\n" ++
    "theorem Verify.r5_priv_leak : r5Priv 0 := (rfl : (0 : Nat) = 0)\n" ++
    "def Mir.R5Body (n : Nat) : Prop := Anneal.R5Secret n\n" ++
    "theorem Verify.r5_mir_leak : Mir.R5Body 0 := (rfl : (0 : Nat) = 0)\n" ++
    "structure R5Str where\n  f : Prop\n" ++
    "def r5Str : R5Str := ⟨Anneal.R5Secret 0⟩\n" ++
    "theorem Verify.r5_proj_leak : r5Str.f := (rfl : (0 : Nat) = 0)\n"
  let vInst ← liftIO <| auditDeclsInEnvIO envShapes #[`Verify.r5_inst_leak] pol
  let vPriv ← liftIO <| auditDeclsInEnvIO envShapes #[`Verify.r5_priv_leak] pol
  let vMir ← liftIO <| auditDeclsInEnvIO envShapes #[`Verify.r5_mir_leak] pol
  let vProj ← liftIO <| auditDeclsInEnvIO envShapes #[`Verify.r5_proj_leak] pol
  liftIO <| assertRejectedWithTag "R5_instance_field_leak" vInst "statementOriginLeak"
  liftIO <| assertRejectedWithTag "R5_private_def_leak" vPriv "statementOriginLeak"
  liftIO <| assertRejectedWithTag "R5_mir_unfold_leak" vMir "statementOriginLeak"
  liftIO <| assertRejectedWithTag "R5_structure_projection_leak" vProj "statementOriginLeak"
  logInfo <| String.intercalate "\n"
    [ formatVerdictTags "R5_stmt_leak_inside_Proof_module" vProof
    , formatVerdictTags "R5_stmt_leak_inside_Anneal_module" vAnneal
    , formatVerdictTags "R5_stmt_clean_inside_Verify_module" vVerify
    , formatVerdictTags "R5_instance_field_leak" vInst
    , formatVerdictTags "R5_private_def_leak" vPriv
    , formatVerdictTags "R5_mir_unfold_leak" vMir
    , formatVerdictTags "R5_structure_projection_leak" vProj ]

/-! ## Hardening Regressions: Certificate Binding, Instance Shadowing, Mutant Coverage -/

/--
info: R6_unbound_direct_cert: rejected [specStrengthCertInvalidType]
R6_half_bound_direct_cert: rejected [specStrengthCertInvalidType]
R6_unbound_class_cert: rejected [specStrengthCertInvalidType]
R6_class_cert_wrong_defId: rejected [specStrengthCertInvalidType]
R6_class_cert_bound: ok []
R6_stateful_class_cert_bound: ok []
R6_modular_class_cert_bound: ok []
R6_deterministic_cert_bound: ok []
R6_deterministic_cert_wrong_spec: rejected [specStrengthCertInvalidType]
R7_instance_shadowing_synth_gate: rejected [specInstanceAmbiguous]
R7_instance_shadowing_class_cert: rejected [specInstanceAmbiguous]
R7_erased_instance_shadowing: rejected [specInstanceAmbiguous]
R7_alias_typed_instance_shadowing: rejected [specInstanceAmbiguous]
R8_coverage_gap: rejected [specStrengthCoverageGap]
R8_coverage_complete: ok []
R8_single_mutant_cert_cannot_cover: rejected [specStrengthCoverageGap]
R8_synth_coverage_gap: rejected [specStrengthCoverageGap]
Positive_stateful_synth_gate: ok []
Positive_modular_synth_gate: ok []
-/
#guard_msgs in
run_cmd do
  let fxfsId := "fxfs_storage_boundary::vmo_subslice_bounds_valid"
  let usercopyId := "fuchsia_usercopy::usercopy_copyin_bracketed"
  let fxfsReq := mkConst ``fxfsVmoSubslicePre
  let fxfsEns := mkConst ``fxfsVmoSubslicePost
  let mut lines : List String := []

  -- R6: a certificate that is not bound to the specification under audit used to be
  -- accepted for ANY `specName` (certificate substitution).
  let vUnbound ← liftTermElabM <|
    auditSpecStrengthCertInEnv `Totally.Unrelated.vacuousSpec (some ``fxfsVmoSubsliceMultiCert)
  let vHalf ← liftTermElabM <|
    auditSpecStrengthCertInEnv `Totally.Unrelated.vacuousSpec (some ``fxfsVmoSubsliceMultiCert)
      (expectedReq? := some fxfsReq)
  let vUnboundClass ← liftTermElabM <|
    auditSpecStrengthCertInEnv `Totally.Unrelated.vacuousSpec (some ``fxfsVmoSubsliceItemMultiCert)
  let vWrongId ← liftTermElabM <|
    auditSpecStrengthCertInEnv `proto_test.v9 (some ``fxfsVmoSubsliceItemMultiCert)
      (expectedDefId? := some "proto_test::v9_trivial_post")
  let vClassOk ← liftTermElabM <|
    auditSpecStrengthCertInEnv `fxfs (some ``fxfsVmoSubsliceItemMultiCert)
      (expectedDefId? := some fxfsId)
  let vStatefulOk ← liftTermElabM <|
    auditSpecStrengthCertInEnv `usercopy (some ``fuchsiaUsercopyCopyinStatefulMultiCert)
      (expectedDefId? := some usercopyId)
  let vModularOk ← liftTermElabM <|
    auditSpecStrengthCertInEnv `usercopy (some ``fuchsiaUsercopyCopyinModularMultiCert)
      (expectedDefId? := some usercopyId)
  let vDetOk ← liftTermElabM <|
    auditSpecStrengthCertInEnv `fxfs (some ``fxfsVmoSubslice_deterministic)
      (expectedReq? := some fxfsReq) (expectedEns? := some fxfsEns)
  let vDetWrong ← liftTermElabM <|
    auditSpecStrengthCertInEnv `fxfs_weak (some ``fxfsVmoSubslice_deterministic)
      (expectedReq? := some fxfsReq)
      (expectedEns? := some (mkConst ``weak_vmo_subslice_upper_bound_only))
  liftIO <| assertRejectedWithTag "R6_unbound_direct_cert" vUnbound "specStrengthCertInvalidType"
  liftIO <| assertRejectedWithTag "R6_half_bound_direct_cert" vHalf "specStrengthCertInvalidType"
  liftIO <| assertRejectedWithTag "R6_unbound_class_cert" vUnboundClass "specStrengthCertInvalidType"
  liftIO <| assertRejectedWithTag "R6_class_cert_wrong_defId" vWrongId "specStrengthCertInvalidType"
  liftIO <| assertAuditOk "R6_class_cert_bound" vClassOk
  liftIO <| assertAuditOk "R6_stateful_class_cert_bound" vStatefulOk
  liftIO <| assertAuditOk "R6_modular_class_cert_bound" vModularOk
  liftIO <| assertAuditOk "R6_deterministic_cert_bound" vDetOk
  liftIO <| assertRejectedWithTag "R6_deterministic_cert_wrong_spec" vDetWrong "specStrengthCertInvalidType"
  lines := lines ++
    [ formatVerdictTags "R6_unbound_direct_cert" vUnbound
    , formatVerdictTags "R6_half_bound_direct_cert" vHalf
    , formatVerdictTags "R6_unbound_class_cert" vUnboundClass
    , formatVerdictTags "R6_class_cert_wrong_defId" vWrongId
    , formatVerdictTags "R6_class_cert_bound" vClassOk
    , formatVerdictTags "R6_stateful_class_cert_bound" vStatefulOk
    , formatVerdictTags "R6_modular_class_cert_bound" vModularOk
    , formatVerdictTags "R6_deterministic_cert_bound" vDetOk
    , formatVerdictTags "R6_deterministic_cert_wrong_spec" vDetWrong ]

  -- R7: a claim proven against a weak `ItemSpec` instance, followed by a second, strong
  -- instance plus certificate for the same `defId`, used to pass the gate.
  let shadowHeader :=
    "open Trusted.VerificationResult Trusted.MirSemantics Anneal.OleanSpecStrengthAuditorProto\n" ++
    "instance r7Weak : ItemSpec \"proto::r7\" where\n  pre := fun _ => True\n"
  let shadowTail :=
    "instance r7Strong : ItemSpec \"proto::r7\" where\n" ++
    "  pre := fxfsVmoSubslicePre\n  post := fxfsVmoSubslicePost\n" ++
    "instance r7Cert : ItemMultiMutantCert \"proto::r7\" where\n  cert := fxfsVmoSubsliceMultiCert\n"
  let envShadow ← elabInSandbox (shadowHeader ++ shadowTail)
  let envErased ← elabInSandbox (shadowHeader ++ "attribute [-instance] r7Weak\n" ++ shadowTail)
  let vShadowSynth ← withSandboxEnv envShadow <| auditItemSpecStrengthBySynth "proto::r7"
  let vShadowClass ← withSandboxEnv envShadow <|
    auditSpecStrengthCertInEnv `proto.r7 (some `r7Cert) (expectedDefId? := some "proto::r7")
  let vErased ← withSandboxEnv envErased <| auditItemSpecStrengthBySynth "proto::r7"
  liftIO <| assertRejectedWithTag "R7_instance_shadowing_synth_gate" vShadowSynth "specInstanceAmbiguous"
  liftIO <| assertRejectedWithTag "R7_instance_shadowing_class_cert" vShadowClass "specInstanceAmbiguous"
  liftIO <| assertRejectedWithTag "R7_erased_instance_shadowing" vErased "specInstanceAmbiguous"
  -- The weak instance may also hide behind a type alias, so that its declared type
  -- does not syntactically mention `ItemSpec`.
  let envAlias ← elabInSandbox <|
    "open Trusted.VerificationResult Trusted.MirSemantics Anneal.OleanSpecStrengthAuditorProto\n" ++
    "abbrev R7WeakTy := ItemSpec \"proto::r7alias\"\n" ++
    "instance r7AliasWeak : R7WeakTy := { pre := fun _ => True }\n" ++
    "instance r7AliasStrong : ItemSpec \"proto::r7alias\" where\n" ++
    "  pre := fxfsVmoSubslicePre\n  post := fxfsVmoSubslicePost\n" ++
    "instance r7AliasCert : ItemMultiMutantCert \"proto::r7alias\" where\n" ++
    "  cert := fxfsVmoSubsliceMultiCert\n"
  let vAlias ← withSandboxEnv envAlias <| auditItemSpecStrengthBySynth "proto::r7alias"
  liftIO <| assertRejectedWithTag "R7_alias_typed_instance_shadowing" vAlias "specInstanceAmbiguous"
  lines := lines ++
    [ formatVerdictTags "R7_instance_shadowing_synth_gate" vShadowSynth
    , formatVerdictTags "R7_instance_shadowing_class_cert" vShadowClass
    , formatVerdictTags "R7_erased_instance_shadowing" vErased
    , formatVerdictTags "R7_alias_typed_instance_shadowing" vAlias ]

  -- R8: the gate can now *enforce* mutant-category coverage instead of trusting a
  -- separately stated coverage theorem.
  let vGap ← liftTermElabM <|
    auditSpecStrengthCertInEnv `fxfs (some ``fxfsVmoSubsliceMultiCert)
      (expectedReq? := some fxfsReq) (expectedEns? := some fxfsEns)
      (requiredCategories := [.wrongReturn, .unpreservedFrame])
  let vCovered ← liftTermElabM <|
    auditSpecStrengthCertInEnv `fxfs (some ``fxfsVmoSubsliceMultiCert)
      (expectedReq? := some fxfsReq) (expectedEns? := some fxfsEns)
      (requiredCategories :=
        [.wrongReturn, .wrapOverflow, .truncatedLength, .swappedByteOrder, .offByOneScalar])
  let vSingle ← liftTermElabM <|
    auditSpecStrengthCertInEnv `fxfs_weak (some ``weakVmoSubsliceSingleCert)
      (expectedReq? := some fxfsReq)
      (expectedEns? := some (mkConst ``weak_vmo_subslice_upper_bound_only))
      (requiredCategories := [.wrongReturn])
  let vSynthGap ← liftTermElabM <|
    auditItemSpecStrengthBySynth fxfsId (requiredCategories := [.wrongBranchTag])
  liftIO <| assertRejectedWithTag "R8_coverage_gap" vGap "specStrengthCoverageGap"
  let reportsMissingFrame := vGap.violations.any fun
    | .specStrengthCoverageGap _ missing _ => missing == #["unpreservedFrame"]
    | _ => false
  unless reportsMissingFrame do
    throwError "expected exactly `unpreservedFrame` to be reported missing:\n{(auditReportJson vGap).pretty}"
  liftIO <| assertAuditOk "R8_coverage_complete" vCovered
  liftIO <| assertRejectedWithTag "R8_single_mutant_cert_cannot_cover" vSingle "specStrengthCoverageGap"
  liftIO <| assertRejectedWithTag "R8_synth_coverage_gap" vSynthGap "specStrengthCoverageGap"
  lines := lines ++
    [ formatVerdictTags "R8_coverage_gap" vGap
    , formatVerdictTags "R8_coverage_complete" vCovered
    , formatVerdictTags "R8_single_mutant_cert_cannot_cover" vSingle
    , formatVerdictTags "R8_synth_coverage_gap" vSynthGap ]

  -- Positive synthesis gates for the stateful and modular usercopy contracts, with
  -- enforced category coverage.
  let usercopyCats : List MutantCategory :=
    [.wrongBranchTag, .truncatedLength, .offByOneScalar, .unpreservedFrame]
  let vStatefulSynth ← liftTermElabM <|
    auditStatefulItemSpecStrengthBySynth usercopyId (requiredCategories := usercopyCats)
  let vModularSynth ← liftTermElabM <|
    auditModularItemSpecStrengthBySynth usercopyId (requiredCategories := usercopyCats)
  liftIO <| assertAuditOk "Positive_stateful_synth_gate" vStatefulSynth
  liftIO <| assertAuditOk "Positive_modular_synth_gate" vModularSynth
  lines := lines ++
    [ formatVerdictTags "Positive_stateful_synth_gate" vStatefulSynth
    , formatVerdictTags "Positive_modular_synth_gate" vModularSynth ]
  logInfo (String.intercalate "\n" lines)

/--
info: R11_claim_bound_cert: ok []
R11_claim_bound_substitution: rejected [specStrengthCertInvalidType]
R11_claim_bound_stateful_cert: ok []
R11_claim_bound_coverage_gap: rejected [specStrengthCoverageGap]
R11_not_a_verification_claim: rejected [specStrengthCertInvalidType]
-/
#guard_msgs in
run_cmd do
  -- R11: the claim-bound gate takes `(req, ens)` from the audited claim's own statement,
  -- so the certificate of a strong specification cannot vouch for a claim that was
  -- proven against a trivial one. Only the claims' *statements* matter here (the gate
  -- audits the certificate, the environment auditor audits the claim proof), so the
  -- sandbox leaves the claim proofs as holes.
  let kw := "sor" ++ "ry"
  let envClaims ← elabInSandbox <|
    "open Trusted.VerificationResult Trusted.MirSemantics Trusted.MirAst\n" ++
    "open Anneal.OleanSpecStrengthAuditorProto\n" ++
    "axiom r11Body : CapturedMir\n" ++
    "noncomputable def r11Claim : Claim :=\n" ++
    "  { body := r11Body, pre := fxfsVmoSubslicePre, post := fxfsVmoSubslicePost }\n" ++
    s!"theorem r11Verified : VerificationResult r11Claim := by {kw}\n" ++
    "noncomputable def r11WeakClaim : Claim :=\n" ++
    "  { body := r11Body, pre := fun _ => True, post := fun _ _ => True }\n" ++
    s!"theorem r11WeakVerified : VerificationResult r11WeakClaim := by {kw}\n" ++
    "noncomputable def r11StatefulClaim : StatefulClaim :=\n" ++
    "  { body := r11Body, pre := fuchsiaUsercopyCopyinPre, post := fuchsiaUsercopyCopyinPost }\n" ++
    s!"theorem r11StatefulVerified : StatefulVerificationResult r11StatefulClaim := by {kw}\n"
  let vBound ← withSandboxEnv envClaims <|
    auditClaimSpecStrengthInEnv `r11Verified (some ``fxfsVmoSubsliceMultiCert)
  let vSubst ← withSandboxEnv envClaims <|
    auditClaimSpecStrengthInEnv `r11WeakVerified (some ``fxfsVmoSubsliceMultiCert)
  let vStateful ← withSandboxEnv envClaims <|
    auditClaimSpecStrengthInEnv `r11StatefulVerified (some ``fuchsiaUsercopyCopyinMultiCert)
  let vCoverage ← withSandboxEnv envClaims <|
    auditClaimSpecStrengthInEnv `r11Verified (some ``fxfsVmoSubsliceMultiCert)
      (requiredCategories := [.unpreservedFrame])
  let vNotClaim ← withSandboxEnv envClaims <|
    auditClaimSpecStrengthInEnv ``fxfsVmoSubslice_covers_required_categories
      (some ``fxfsVmoSubsliceMultiCert)
  liftIO <| assertAuditOk "R11_claim_bound_cert" vBound
  liftIO <| assertRejectedWithTag "R11_claim_bound_substitution" vSubst "specStrengthCertInvalidType"
  liftIO <| assertAuditOk "R11_claim_bound_stateful_cert" vStateful
  liftIO <| assertRejectedWithTag "R11_claim_bound_coverage_gap" vCoverage "specStrengthCoverageGap"
  liftIO <| assertRejectedWithTag "R11_not_a_verification_claim" vNotClaim "specStrengthCertInvalidType"
  logInfo <| String.intercalate "\n"
    [ formatVerdictTags "R11_claim_bound_cert" vBound
    , formatVerdictTags "R11_claim_bound_substitution" vSubst
    , formatVerdictTags "R11_claim_bound_stateful_cert" vStateful
    , formatVerdictTags "R11_claim_bound_coverage_gap" vCoverage
    , formatVerdictTags "R11_not_a_verification_claim" vNotClaim ]

/-! ## Pass A1 Hardening Regressions: Shadowing, Scoped `csimp`, Ordering, Modular/Total Claims -/

/-- Type-level refutation for direct `ModularSpecStrengthCert` with vacuous rely predicate. -/
theorem testA1_modular_vacuous_rely_refuted :
    ModularSpecStrengthCert (fun _ => False) fuchsiaUsercopyCopyinPre fuchsiaUsercopyCopyinPost → False :=
  no_modular_cert_of_vacuous_envAssumed _ _

/--
info: A1_let_typed_instance_shadowing: rejected [specInstanceAmbiguous]
A1_beta_redex_instance_shadowing: rejected [specInstanceAmbiguous]
A1_deep_alias_instance_shadowing: rejected [specInstanceAmbiguous]
A1_proj_typed_instance_shadowing: rejected [specInstanceAmbiguous]
A1_closed_scoped_csimp_caught: rejected [compilerOverrideAttribute]
A1_sorry_multi_cert_reports_sorry_not_coverage_gap: rejected [sorryAxiomReached]
A1_literal_false_eq_true_native_ax: rejected [unapprovedAxiom]
A1_forged_unsafe_rec_not_skipped: ok
A1_claim_bound_modular_multi_cert: ok []
A1_claim_bound_modular_det_cert: ok []
A1_claim_bound_modular_wrong_envAssumed: rejected [specStrengthCertInvalidType]
A1_claim_bound_modular_coverage_gap: rejected [specStrengthCoverageGap]
A1_claim_bound_total_cert: ok []
A1_claim_bound_non_theorem_rejected: rejected [notTheoremKind]
-/
#guard_msgs in
run_cmd do
  let mut lines : List String := []
  let kw := "sor" ++ "ry"

  -- A1-2a/b/c: `let`-wrapped, beta-redex, and 9-deep alias chain shadowing instances
  -- used to slip past `specInstanceCandidates` (fail-open); all three are now rejected.
  let envLet ← elabInSandbox <|
    "open Trusted.VerificationResult Anneal.OleanSpecStrengthAuditorProto\n" ++
    "instance a1LetWeak : (let T := ItemSpec \"proto::a1let\"; T) := { pre := fun _ => True }\n" ++
    "instance a1LetStrong : ItemSpec \"proto::a1let\" := { pre := fxfsVmoSubslicePre, post := fxfsVmoSubslicePost }\n" ++
    "instance a1LetCert : ItemMultiMutantCert \"proto::a1let\" := { cert := fxfsVmoSubsliceMultiCert }\n"
  let vLet ← withSandboxEnv envLet <| auditItemSpecStrengthBySynth "proto::a1let"
  liftIO <| assertRejectedWithTag "A1_let_typed_instance_shadowing" vLet "specInstanceAmbiguous"
  lines := lines ++ [formatVerdictTags "A1_let_typed_instance_shadowing" vLet]

  let envLam ← elabInSandbox <|
    "open Trusted.VerificationResult Anneal.OleanSpecStrengthAuditorProto\n" ++
    "instance a1LamWeak : (fun s => ItemSpec s) \"proto::a1lam\" := { pre := fun _ => True }\n" ++
    "instance a1LamStrong : ItemSpec \"proto::a1lam\" := { pre := fxfsVmoSubslicePre, post := fxfsVmoSubslicePost }\n" ++
    "instance a1LamCert : ItemMultiMutantCert \"proto::a1lam\" := { cert := fxfsVmoSubsliceMultiCert }\n"
  let vLam ← withSandboxEnv envLam <| auditItemSpecStrengthBySynth "proto::a1lam"
  liftIO <| assertRejectedWithTag "A1_beta_redex_instance_shadowing" vLam "specInstanceAmbiguous"
  lines := lines ++ [formatVerdictTags "A1_beta_redex_instance_shadowing" vLam]

  let envDeep ← elabInSandbox <|
    "open Trusted.VerificationResult Anneal.OleanSpecStrengthAuditorProto\n" ++
    "abbrev A1D1 := ItemSpec \"proto::a1deep\"\n" ++
    "abbrev A1D2 := A1D1\nabbrev A1D3 := A1D2\nabbrev A1D4 := A1D3\nabbrev A1D5 := A1D4\n" ++
    "abbrev A1D6 := A1D5\nabbrev A1D7 := A1D6\nabbrev A1D8 := A1D7\nabbrev A1D9 := A1D8\n" ++
    "instance a1DeepWeak : A1D9 := { pre := fun _ => True }\n" ++
    "instance a1DeepStrong : ItemSpec \"proto::a1deep\" := { pre := fxfsVmoSubslicePre, post := fxfsVmoSubslicePost }\n" ++
    "instance a1DeepCert : ItemMultiMutantCert \"proto::a1deep\" := { cert := fxfsVmoSubsliceMultiCert }\n"
  let vDeep ← withSandboxEnv envDeep <| auditItemSpecStrengthBySynth "proto::a1deep"
  liftIO <| assertRejectedWithTag "A1_deep_alias_instance_shadowing" vDeep "specInstanceAmbiguous"
  lines := lines ++ [formatVerdictTags "A1_deep_alias_instance_shadowing" vDeep]

  let envProj ← elabInSandbox <|
    "open Trusted.VerificationResult Anneal.OleanSpecStrengthAuditorProto\n" ++
    "abbrev a1WrapPair : Type 1 × Type := (ItemSpec \"proto::a1proj\", Nat)\n" ++
    "instance a1ProjWeak : a1WrapPair.1 := { pre := fun _ => True }\n" ++
    "instance a1ProjStrong : ItemSpec \"proto::a1proj\" := { pre := fxfsVmoSubslicePre, post := fxfsVmoSubslicePost }\n" ++
    "instance a1ProjCert : ItemMultiMutantCert \"proto::a1proj\" := { cert := fxfsVmoSubsliceMultiCert }\n"
  let vProj ← withSandboxEnv envProj <| auditItemSpecStrengthBySynth "proto::a1proj"
  liftIO <| assertRejectedWithTag "A1_proj_typed_instance_shadowing" vProj "specInstanceAmbiguous"
  lines := lines ++ [formatVerdictTags "A1_proj_typed_instance_shadowing" vProj]

  -- A1-3: closed-scope `@[scoped csimp]` used to vanish from `CSimp.ext.getState`
  -- once the namespace ended; scanning `StateStack.newEntries` / `scopedEntries` catches it.
  let envScoped ← elabInSandbox <|
    "def a1MyAdd (a b : Nat) : Nat := a + b\n" ++
    "namespace A1HiddenScope\n" ++
    "@[scoped csimp] theorem a1ScopedAdd : @Nat.add = @a1MyAdd := by funext a b; rfl\n" ++
    "end A1HiddenScope\n" ++
    "theorem a1UsesAdd : Nat.add 2 3 = 5 := rfl\n"
  let vScoped ← liftIO <| auditDeclsInEnvIO envScoped #[`a1UsesAdd] { checkStatementOrigin := false }
  liftIO <| assertRejectedWithTag "A1_closed_scoped_csimp_caught" vScoped "compilerOverrideAttribute"
  lines := lines ++ [formatVerdictTags "A1_closed_scoped_csimp_caught" vScoped]

  -- A1-4: a `sorry`-faked `MultiMutantSpecCert` checked with non-empty `requiredCategories`
  -- must report `.sorryAxiomReached`, NOT `.specStrengthCoverageGap`.
  let envSorryMulti ← elabInSandbox <|
    "open Anneal.OleanSpecStrengthAuditorProto\n" ++
    "def a1Pre (n : Nat) : Prop := n = 0\n" ++
    "def a1Post (_ : Nat) (y : Nat) : Prop := y = 0\n" ++
    s!"def a1FakeMulti : MultiMutantSpecCert a1Pre a1Post := by {kw}\n"
  let vSorryMulti ← withSandboxEnv envSorryMulti <|
    auditSpecStrengthCertInEnv `a1.sorryMulti (some `a1FakeMulti)
      (expectedReq? := some (mkConst `a1Pre))
      (expectedEns? := some (mkConst `a1Post))
      (requiredCategories := [.wrongReturn])
  liftIO <| assertRejectedWithTag "A1_sorry_multi_cert_reports_sorry_not_coverage_gap" vSorryMulti "sorryAxiomReached"
  lines := lines ++ [formatVerdictTags "A1_sorry_multi_cert_reports_sorry_not_coverage_gap" vSorryMulti]

  -- A1-5: literal `false = true` native-named axiom rejected even under `allowProvisionalNative`.
  let envFalseNat ← elabInSandbox <|
    "axiom a1Bad._native.native_decide.ax_1_1 : false = true\n" ++
    "theorem a1UsesFalseNat : False := Bool.noConfusion a1Bad._native.native_decide.ax_1_1\n"
  let vFalseNat ← liftIO <| auditDeclsInEnvIO envFalseNat #[`a1UsesFalseNat]
    { checkStatementOrigin := false, allowProvisionalNative := true }
  liftIO <| assertRejectedWithTag "A1_literal_false_eq_true_native_ax" vFalseNat "unapprovedAxiom"
  lines := lines ++ [formatVerdictTags "A1_literal_false_eq_true_native_ax" vFalseNat]

  -- A1-7a: forged `foo._unsafe_rec` with mismatched type is NOT treated as a dead codegen companion.
  let envForgedRec ← elabInSandbox <|
    "def a1SafeParent : Nat := 0\n" ++
    "partial def a1SafeParent._unsafe_rec (n : Nat) : Nat := a1SafeParent._unsafe_rec n\n"
  let some forgedCi := envForgedRec.checked.get.find? `a1SafeParent._unsafe_rec
    | throwError "expected a1SafeParent._unsafe_rec in sandbox"
  if isCodegenUnsafeRec envForgedRec none forgedCi then
    throwError "forged-type _unsafe_rec was wrongly classified as codegen companion"
  lines := lines ++ ["A1_forged_unsafe_rec_not_skipped: ok"]

  -- A1-6: claim-bound `ModularVerificationResult` & `TotalVerificationResult` gates,
  -- plus rejection of non-theorem (`axiom`) claim declarations.
  let envModClaims ← elabInSandbox <|
    "open Trusted.VerificationResult Trusted.MirSemantics Trusted.MirAst\n" ++
    "open Anneal.OleanSpecStrengthAuditorProto\n" ++
    "axiom a1Body : CapturedMir\n" ++
    "noncomputable def a1ModClaim : ModularClaim :=\n" ++
    "  { body := a1Body, envAssumed := fuchsiaHermeticCopyRely,\n" ++
    "    pre := fuchsiaUsercopyCopyinPre, post := fuchsiaUsercopyCopyinPost }\n" ++
    s!"theorem a1ModVerified : ModularVerificationResult a1ModClaim := by {kw}\n" ++
    "noncomputable def a1ModVacuousRelyClaim : ModularClaim :=\n" ++
    "  { body := a1Body, envAssumed := fun _ => False,\n" ++
    "    pre := fuchsiaUsercopyCopyinPre, post := fuchsiaUsercopyCopyinPost }\n" ++
    s!"theorem a1ModVacuousVerified : ModularVerificationResult a1ModVacuousRelyClaim := by {kw}\n" ++
    "noncomputable def a1TotalClaim : TotalClaim :=\n" ++
    "  { body := a1Body, pre := fuchsiaUsercopyCopyinPre, post := fuchsiaUsercopyCopyinPost }\n" ++
    s!"theorem a1TotalVerified : TotalVerificationResult a1TotalClaim := by {kw}\n" ++
    "noncomputable def a1SimpleClaim : Claim :=\n" ++
    "  { body := a1Body, pre := fxfsVmoSubslicePre, post := fxfsVmoSubslicePost }\n" ++
    "axiom a1AxiomClaim : VerificationResult a1SimpleClaim\n"
  let usercopyCats : List MutantCategory :=
    [.wrongBranchTag, .truncatedLength, .offByOneScalar, .unpreservedFrame]
  let vModMulti ← withSandboxEnv envModClaims <|
    auditClaimSpecStrengthInEnv `a1ModVerified (some ``fuchsiaUsercopyCopyinModularDirectMultiCert)
      (requiredCategories := usercopyCats)
  let vModDet ← withSandboxEnv envModClaims <|
    auditClaimSpecStrengthInEnv `a1ModVerified (some ``fuchsiaUsercopyCopyinModularDirectDetCert)
  let vModWrongEnv ← withSandboxEnv envModClaims <|
    auditClaimSpecStrengthInEnv `a1ModVacuousVerified (some ``fuchsiaUsercopyCopyinModularDirectMultiCert)
  let vModGap ← withSandboxEnv envModClaims <|
    auditClaimSpecStrengthInEnv `a1ModVerified (some ``fuchsiaUsercopyCopyinModularDirectMultiCert)
      (requiredCategories := [.swappedByteOrder])
  let vTotal ← withSandboxEnv envModClaims <|
    auditClaimSpecStrengthInEnv `a1TotalVerified (some ``fuchsiaUsercopyCopyinMultiCert)
      (requiredCategories := usercopyCats)
  let vNonThm ← withSandboxEnv envModClaims <|
    auditClaimSpecStrengthInEnv `a1AxiomClaim (some ``fxfsVmoSubsliceMultiCert)
  liftIO <| assertAuditOk "A1_claim_bound_modular_multi_cert" vModMulti
  liftIO <| assertAuditOk "A1_claim_bound_modular_det_cert" vModDet
  liftIO <| assertRejectedWithTag "A1_claim_bound_modular_wrong_envAssumed" vModWrongEnv "specStrengthCertInvalidType"
  liftIO <| assertRejectedWithTag "A1_claim_bound_modular_coverage_gap" vModGap "specStrengthCoverageGap"
  liftIO <| assertAuditOk "A1_claim_bound_total_cert" vTotal
  liftIO <| assertRejectedWithTag "A1_claim_bound_non_theorem_rejected" vNonThm "notTheoremKind"
  lines := lines ++
    [ formatVerdictTags "A1_claim_bound_modular_multi_cert" vModMulti
    , formatVerdictTags "A1_claim_bound_modular_det_cert" vModDet
    , formatVerdictTags "A1_claim_bound_modular_wrong_envAssumed" vModWrongEnv
    , formatVerdictTags "A1_claim_bound_modular_coverage_gap" vModGap
    , formatVerdictTags "A1_claim_bound_total_cert" vTotal
    , formatVerdictTags "A1_claim_bound_non_theorem_rejected" vNonThm ]
  logInfo (String.intercalate "\n" lines)

/-! ### Type-Level Refutations for Discriminating Kills and Deterministic Specifications -/

/-- A specification that is satisfiable at input `0` but unimplementable everywhere else.
    Before kills had to exhibit an accepted reference output, it admitted a
    `MultiMutantSpecCert` whose only "kill" sat on the unimplementable input `1`. -/
def unimplementableOffZeroEns (x y : Nat) : Prop :=
  (x = 0 → y = 0) ∧ (x ≠ 0 → False)

/-- Every discriminating kill against `unimplementableOffZeroEns` is forced onto the one
    input where the specification is realizable. -/
theorem testKillOnlyAtRealizableInput
    (k : NamedMutantKill (fun (_ : Nat) => True) unimplementableOffZeroEns) : k.input = 0 :=
  match Nat.decEq k.input 0 with
  | isTrue h => h
  | isFalse h => (k.reference_accepted.2 h).elim

/-- ...so the formerly accepted vacuous kill at input `1` is refuted at the type level. -/
theorem testNoVacuousKillAtUnimplementableInput
    (k : NamedMutantKill (fun (_ : Nat) => True) unimplementableOffZeroEns)
    (h : k.input = 1) : False :=
  no_kill_at_unrealizable_input k (fun _ hEns => hEns.2 (by rw [h]; decide))

/-- A trivial `ensures := True` contract over `Nat` outputs is never deterministic. -/
theorem testTrivialEnsNotDeterministic :
    DeterministicSpecCert (fun (n : Nat) => n < 10) (fun _ (_ : Nat) => True) → False :=
  no_deterministic_cert_of_trivial_ens _ 0 1 (by decide)

/-- Any implementation of `vmo_subslice_bounds_valid` that deviates from the reference
    on the sampled valid input violates the (deterministic) specification, whatever the
    deviating value is. -/
theorem testFxfsEveryDeviationKilled (bogus : Nat) (hNe : bogus ≠ 4224) :
    ¬ fxfsVmoSubslicePost
        [ .scalar { bits := 4096, sizeBytes := 8 }
        , .scalar { bits := 4096, sizeBytes := 8 }
        , .scalar { bits := 64, sizeBytes := 8 }
        , .scalar { bits := 192, sizeBytes := 8 } ]
        (.scalar { bits := bogus, sizeBytes := 8 }) :=
  fxfsVmoSubslice_deterministic.kills_every_deviation
    ⟨4096, 4096, 64, 192, by decide, by decide, by decide, rfl⟩
    (fxfsVmoSubslicePost_exact 4096 4096 64 192)
    (fun hEq => by
      injection hEq with hS
      injection hS with hBits _
      exact hNe hBits)

/-! ## Hardening Regressions: Empty Target Sets, Fuel Exhaustion, JSON Receipt Schema -/

/--
info: R9_zero_targets: rejected [noAuditTargets]
R9_zero_targets_opt_in: ok []
R10_fuel_exhaustion_closure: rejected [auditFuelExhausted]
R10_fuel_exhaustion_statement: rejected [auditFuelExhausted]
-/
#guard_msgs in
run_cmd do
  let env ← getEnv
  -- R9: an audit that inspected nothing used to report `ok`.
  let vEmpty ← liftIO <| auditDeclsInEnvIO env #[] {}
  let vEmptyOptIn ← liftIO <| auditDeclsInEnvIO env #[] { allowEmptyTargetSet := true }
  liftIO <| assertRejectedWithTag "R9_zero_targets" vEmpty "noAuditTargets"
  liftIO <| assertAuditOk "R9_zero_targets_opt_in" vEmptyOptIn
  -- R10: running out of fuel is a structured, fail-closed rejection.
  let vFuelClosure ← liftIO <| auditDeclsInEnvIO env #[``no_cert_of_vacuous_req]
    { checkStatementOrigin := false, fuelOverride? := some 3 }
  let envStmt ← elabInSandbox "theorem Verify.r10 : (1 : Nat) + 1 = 2 := rfl\n"
  let vFuelStmt ← liftIO <| auditDeclsInEnvIO envStmt #[`Verify.r10]
    { AuditPolicy.strictClaim with fuelOverride? := some 3 }
  liftIO <| assertRejectedWithTag "R10_fuel_exhaustion_closure" vFuelClosure "auditFuelExhausted"
  liftIO <| assertRejectedWithTag "R10_fuel_exhaustion_statement" vFuelStmt "auditFuelExhausted"
  let stmtPhaseReported := vFuelStmt.violations.any fun
    | .auditFuelExhausted _ phase => phase == "statement-origin walk"
    | _ => false
  unless stmtPhaseReported do
    throwError "expected statement-origin fuel exhaustion:\n{(auditReportJson vFuelStmt).pretty}"
  logInfo <| String.intercalate "\n"
    [ formatVerdictTags "R9_zero_targets" vEmpty
    , formatVerdictTags "R9_zero_targets_opt_in" vEmptyOptIn
    , formatVerdictTags "R10_fuel_exhaustion_closure" vFuelClosure
    , formatVerdictTags "R10_fuel_exhaustion_statement" vFuelStmt ]

/-- info: {"stats":{"axiomsFound":[],"elapsedMicros":7,"importMicros":0,"kernelReplayedDeclarations":0,"modulesLoaded":0,"privateArtifactsChecked":0,"provisionalNativeAxioms":["a._native.t.ax_1","z._native.t.ax_1"],"reachableDeclarations":0,"targetsAudited":1},"status":"rejected","violations":[{"context":"ctx","kind":"noAuditTargets"},{"expected":"toolchain","kind":"moduleProvenanceSpoofed","module":"Std.Evil","resolvedPath":"/x/Std/Evil.olean"},{"certDecl":"c","kind":"specStrengthCoverageGap","missing":["wrongReturn"],"reason":"why"},{"candidates":["a","b"],"kind":"specInstanceAmbiguous","specClass":"K","specName":"s"},{"kind":"auditFuelExhausted","phase":"closure","target":"t"},{"detail":"boom","kind":"environmentLoadFailed"}]} -/
#guard_msgs in
#eval IO.println (auditReportJson (.rejected
  #[ .noAuditTargets "ctx"
   , .moduleProvenanceSpoofed `Std.Evil "/x/Std/Evil.olean" "toolchain"
   , .specStrengthCoverageGap `c #["wrongReturn"] "why"
   , .specInstanceAmbiguous `s `K #[`b, `a]
   , .auditFuelExhausted `t "closure"
   , .environmentLoadFailed "boom" ]
  { targetsAudited := 1, provisionalNativeAxioms := #[`z._native.t.ax_1, `a._native.t.ax_1]
    elapsedMicros := 7 })).compress

/-! ## Synthetic `ConstantInfo` Graph-Edge Completeness Regression Checks -/

/-- info: SyntheticGraphEdges: ok -/
#guard_msgs in
run_cmd do
  -- 1. Recursor rule `rhs`, `ctor`, and `all` edges.
  let recInfo : ConstantInfo := .recInfo {
    name := `Synthetic.rec, levelParams := [], type := .sort .zero,
    all := [`Synthetic.Data], numParams := 0, numIndices := 0,
    numMotives := 0, numMinors := 0,
    rules := [{ ctor := `Synthetic.ctor, nfields := 0, rhs := .const `Hidden.RuleDep [] }],
    k := false, isUnsafe := false
  }
  let (recEdges, recOpen) := declarationEdges `Synthetic.rec recInfo
  unless recOpen.isEmpty && [`Hidden.RuleDep, `Synthetic.Data, `Synthetic.ctor].all recEdges.contains do
    throwError "recursor-rule edge extraction regression"

  -- 2. Opaque body edge extraction (`allowOpaque := true`).
  let opqInfo : ConstantInfo := .opaqueInfo {
    name := `Synthetic.opaque, levelParams := [], type := .sort .zero,
    value := .const `Hidden.OpaqueBody [], isUnsafe := false
  }
  let (opqEdges, opqOpen) := declarationEdges `Synthetic.opaque opqInfo
  unless opqOpen.isEmpty && opqEdges.contains `Hidden.OpaqueBody do
    throwError "opaque-body edge extraction regression"

  -- 3. Constructor parent (`induct`) and inductive constructors (`ctors`).
  let ctorInfo : ConstantInfo := .ctorInfo {
    name := `Synthetic.ctor, levelParams := [], type := .sort .zero,
    induct := `Hidden.ParentInduct, cidx := 0, numParams := 0, numFields := 0, isUnsafe := false
  }
  let (ctorEdges, _) := declarationEdges `Synthetic.ctor ctorInfo
  unless ctorEdges.contains `Hidden.ParentInduct do
    throwError "constructor-parent edge extraction regression"

  -- 4. `.proj` struct name and `Nat`/`String` literals.
  match expressionEdges (.proj `Hidden.Struct 0 (.lit (.strVal "abc"))) with
  | .ok es =>
    unless es.contains `Hidden.Struct && es.contains ``String do
      throwError "proj/String literal edge regression"
  | .error e => throwError "unexpected error on proj/str: {e}"

  match expressionEdges (.lit (.natVal 42)) with
  | .ok es =>
    unless es.contains ``Nat do
      throwError "Nat literal edge regression"
  | .error e => throwError "unexpected error on nat lit: {e}"

  -- 5. Open term expressions (`FVar`, `MVar`, loose `BVar`) rejected fail-closed.
  match expressionEdges (.fvar ⟨`free_x⟩) with
  | .error _ => pure ()
  | .ok _ => throwError "open FVar expression was accepted"
  match expressionEdges (.mvar ⟨`meta_m⟩) with
  | .error _ => pure ()
  | .ok _ => throwError "open MVar expression was accepted"
  match expressionEdges (.bvar 0) with
  | .error _ => pure ()
  | .ok _ => throwError "loose BVar expression was accepted"

  logInfo "SyntheticGraphEdges: ok"

/-! ## Real On-Disk Lean `v4.34.1` `module` `.olean` + `.olean.private` Round-Trip -/

/-- Compile a temporary `.lean` file to `.olean` (+ `.olean.server` / `.olean.private`
    for `module` files) using the pinned Lean `v4.34.1` toolchain binary (`runFrontend` +
    `writeModule`) without needing `unsafe enableInitializersExecution`. -/
def compileTempModuleToOlean (rootDir leanPath oleanPath : System.FilePath) : IO Unit := do
  let leanBin := (← Lean.getBuildDir) / "bin" / "lean"
  let out ← IO.Process.output {
    cmd := leanBin.toString
    args := #["-R", rootDir.toString, "-o", oleanPath.toString, leanPath.toString]
  }
  unless out.exitCode == 0 do
    throw <| IO.userError
      s!"lean compilation failed for {leanPath} (exit {out.exitCode}):\n{out.stdout}\n{out.stderr}"

/-- Real on-disk test compiling Lean `v4.34.1` `module` files into a unique `/tmp/`
    directory (deleted in `finally`):
    1. Proves `OLeanLevel.exported` misses a `private axiom` hidden inside a `public theorem`'s
       proof body (and weakens the theorem to bodyless `axiom` in `.olean`).
    2. Proves `auditCompiledModulesIO` (`OLeanLevel.private` + `env.setExporting false`)
       catches the hidden `private axiom` fail-closed as `.unapprovedAxiom`.
    3. Proves deleting `.olean.private` triggers `.missingPrivateArtifact` fail-closed.
    4. Proves a clean compiled `module` passes `auditCompiledModulesIO` with `runKernelReplay := true`. -/
def runDiskPrivateOleanRoundTrip : IO String := do
  let pid ← IO.Process.getPID
  let ns ← IO.monoNanosNow
  let tmpDir : System.FilePath := s!"/tmp/anneal_olean_proto_test_{pid}_{ns}"
  IO.FS.createDirAll tmpDir
  try
    -- A. Sneaky module with `private axiom` hidden behind `public theorem`.
    let sneakyMod : Name := `ProtoDiskSneakyMod
    let sneakyLean := tmpDir / "ProtoDiskSneakyMod.lean"
    let sneakyOlean := tmpDir / "ProtoDiskSneakyMod.olean"
    let sneakySrc :=
      "module\n\n" ++
      "private axiom hiddenPrivateBackdoor : False\n\n" ++
      "public theorem sneakyExportedClaim : True := by\n" ++
      "  have _ := hiddenPrivateBackdoor\n" ++
      "  trivial\n"
    IO.FS.writeFile sneakyLean sneakySrc
    compileTempModuleToOlean tmpDir sneakyLean sneakyOlean

    let serverPath := OLeanLevel.server.adjustFileName sneakyOlean
    let privPath := OLeanLevel.private.adjustFileName sneakyOlean
    unless (← sneakyOlean.pathExists) && (← serverPath.pathExists) && (← privPath.pathExists) do
      throw <| IO.userError "expected .olean, .olean.server, and .olean.private to be emitted for module file"
    let oleanBytes := (← sneakyOlean.metadata).byteSize
    let serverBytes := (← serverPath.metadata).byteSize
    let privBytes := (← privPath.metadata).byteSize

    -- B. Load with `OLeanLevel.exported` ONLY (simulating a `.olean`-only auditor).
    let (exportedSawPrivAx, exportedClaimKind, vExported) ← withExtraSearchPaths [tmpDir] do
      let exportedArts : NameMap ImportArtifacts :=
        ({} : NameMap ImportArtifacts).insert sneakyMod (ImportArtifacts.ofArrays #[#[sneakyOlean]])
      let expEnv ← Lean.importModules #[{ module := sneakyMod }] {}
        (trustLevel := 0) (plugins := #[]) (loadExts := false)
        (level := OLeanLevel.exported) (arts := exportedArts)
      let kenv := expEnv.checked.get
      let sawPriv := kenv.constants.fold (init := false) fun acc n _ =>
        acc || (n.toString.splitOn "hiddenPrivateBackdoor").length > 1
      let claimKind := match kenv.find? `sneakyExportedClaim with
        | some ci => constantInfoKind ci
        | none => "missing"
      -- The pure auditor must refuse this exported-level view outright: it is what an
      -- in-process audit inside a `module` file would see (public theorem weakened to a
      -- body-less axiom, private axiom absent).
      let vExported := auditDeclsInEnvPure expEnv #[`sneakyExportedClaim]
        { checkStatementOrigin := false }
      return (sawPriv, claimKind, vExported)
    if exportedSawPrivAx then
      throw <| IO.userError "expected OLeanLevel.exported to hide private axiom, but it was visible"
    assertRejectedWithTag "DiskPrivateOlean_exported_level_environment" vExported "environmentLoadFailed"

    -- C. Audit with `OLeanLevel.private` + `env.setExporting false` -> MUST catch hidden private axiom.
    let loadedSneaky ← loadOrThrow "DiskPrivateOlean_load" #[sneakyMod] {} [tmpDir]
    let vPriv ← auditLoadedModulesIO loadedSneaky
      { checkStatementOrigin := false, requireTheoremKind := true }
      (explicitTargets? := some #[`sneakyExportedClaim])
    assertRejectedWithTag "DiskPrivateOlean_catch_hidden_axiom" vPriv "unapprovedAxiom"
    -- Default target selection (no explicit list, theorems only) must find the public
    -- theorem at `OLeanLevel.private` and reach the hidden private axiom through it.
    let vAuto ← auditLoadedModulesIO loadedSneaky { checkStatementOrigin := false }
      (theoremsOnly := true)
    assertRejectedWithTag "DiskPrivateOlean_default_theorem_targets" vAuto "unapprovedAxiom"
    unless vAuto.stats.targetsAudited == 1 do
      throw <| IO.userError
        s!"expected exactly 1 auto-selected theorem target, got {vAuto.stats.targetsAudited}"
    let caughtBackdoor := vPriv.violations.any fun
      | .unapprovedAxiom _ axName _ _ => (axName.toString.splitOn "hiddenPrivateBackdoor").length > 1
      | _ => false
    unless caughtBackdoor do
      throw <| IO.userError s!"expected unapprovedAxiom mentioning hiddenPrivateBackdoor, got:\n{auditReportJson vPriv |>.pretty}"

    -- D. Delete `.olean.private` -> MUST fail closed with `.missingPrivateArtifact`.
    IO.FS.removeFile privPath
    let vMissingPriv ← auditCompiledModulesIO #[sneakyMod]
      { checkStatementOrigin := false }
      (explicitTargets? := some #[`sneakyExportedClaim])
      (extraSearchPaths := [tmpDir])
    assertRejectedWithTag "DiskPrivateOlean_missing_private_artifact" vMissingPriv "missingPrivateArtifact"

    -- E. Clean compiled `module` with `runKernelReplay := true` -> MUST pass `.ok`.
    let cleanMod : Name := `ProtoDiskCleanMod
    let cleanLean := tmpDir / "ProtoDiskCleanMod.lean"
    let cleanOlean := tmpDir / "ProtoDiskCleanMod.olean"
    let cleanSrc :=
      "module\n\n" ++
      "private theorem helperAddZero (n : Nat) : n + 0 = n := Nat.add_zero n\n\n" ++
      "public theorem cleanExportedClaim (n : Nat) : n + 0 = n := helperAddZero n\n"
    IO.FS.writeFile cleanLean cleanSrc
    compileTempModuleToOlean tmpDir cleanLean cleanOlean
    let vClean ← auditCompiledModulesIO #[cleanMod]
      { AuditPolicy.constructive with checkStatementOrigin := false, requireTheoremKind := true }
      (explicitTargets? := some #[`cleanExportedClaim])
      (extraSearchPaths := [tmpDir])
      (runKernelReplay := true)
    assertAuditOk "DiskPrivateOlean_clean_replay" vClean
    unless vClean.stats.kernelReplayedDeclarations > 0 do
      throw <| IO.userError "expected kernelReplayedDeclarations > 0 for clean module replay"

    return s!"DiskPrivateOleanRoundTrip: PASS (olean={oleanBytes}B, server={serverBytes}B, private={privBytes}B, exportedSawPrivAx={exportedSawPrivAx}, exportedClaimKind={exportedClaimKind}, exportedLevelAudit={formatVerdictTags "exp" vExported}, privateAudit={formatVerdictTags "priv" vPriv}, autoTargetAudit={formatVerdictTags "auto" vAuto}, deletedPrivateAudit={formatVerdictTags "del" vMissingPriv}, cleanReplayDecls={vClean.stats.kernelReplayedDeclarations}, privLatencyUs={vPriv.stats.elapsedMicros})"
  finally
    IO.FS.removeDirAll tmpDir

#eval runDiskPrivateOleanRoundTrip

/-- Compile `leanPath` like `compileTempModuleToOlean`, with `LEAN_PATH` pointed at
    `rootDir` so sibling temporary modules can import each other. -/
def compileTempModuleWithPath (rootDir leanPath oleanPath : System.FilePath) : IO Unit := do
  let leanBin := (← Lean.getBuildDir) / "bin" / "lean"
  let out ← IO.Process.output {
    cmd := leanBin.toString
    args := #["-R", rootDir.toString, "-o", oleanPath.toString, leanPath.toString]
    env := #[("LEAN_PATH", some rootDir.toString)]
  }
  unless out.exitCode == 0 do
    throw <| IO.userError
      s!"lean compilation failed for {leanPath} (exit {out.exitCode}):\n{out.stdout}\n{out.stderr}"

/-- On-disk regressions for bypasses found during adversarial hardening. Every check
    runs against real Lean `v4.34.1` artifacts compiled into a unique `/tmp/` directory
    (deleted in `finally`); the returned summary is fully deterministic. -/
def runDiskHardeningRegressions : IO String := do
  let pid ← IO.Process.getPID
  let ns ← IO.monoNanosNow
  let tmpDir : System.FilePath := s!"/tmp/anneal_olean_proto_hardening_{pid}_{ns}"
  IO.FS.createDirAll tmpDir
  let body : IO (Array String) := do
    let mut lines : Array String := #[]
    let pol : AuditPolicy := { checkStatementOrigin := false }

    -- D2: a missing `.olean.server` part used to escape as an untyped `IO` exception.
    let noServerLean := tmpDir / "ProtoDiskNoServer.lean"
    let noServerOlean := tmpDir / "ProtoDiskNoServer.olean"
    IO.FS.writeFile noServerLean "module\n\npublic theorem noServerClaim : True := trivial\n"
    compileTempModuleToOlean tmpDir noServerLean noServerOlean
    IO.FS.removeFile (OLeanLevel.server.adjustFileName noServerOlean)
    let vNoServer ← auditCompiledModulesIO #[`ProtoDiskNoServer] pol (extraSearchPaths := [tmpDir])
    assertRejectedWithTag "D2_missing_olean_server_part" vNoServer "missingPrivateArtifact"
    lines := lines.push (formatVerdictTags "D2_missing_olean_server_part" vNoServer)

    -- D3: an unreadable `.olean` header is a structured rejection as well.
    IO.FS.writeFile (tmpDir / "ProtoDiskCorrupt.olean") "this is not a compacted region"
    let vCorrupt ← auditCompiledModulesIO #[`ProtoDiskCorrupt] pol (extraSearchPaths := [tmpDir])
    assertRejectedWithTag "D3_corrupt_olean_header" vCorrupt "environmentLoadFailed"
    lines := lines.push (formatVerdictTags "D3_corrupt_olean_header" vCorrupt)

    -- D4: a `prelude` module re-declaring `propext` with a false statement used to pass,
    --     because allowed axioms were matched by name only.
    let preludeLean := tmpDir / "ProtoDiskPreludeEvil.lean"
    IO.FS.writeFile preludeLean <|
      "prelude\n\n" ++
      "axiom propext : ∀ (P : Prop), P\n\n" ++
      "theorem evilClaim (P : Prop) : P := propext P\n"
    compileTempModuleToOlean tmpDir preludeLean (tmpDir / "ProtoDiskPreludeEvil.olean")
    let vPrelude ← auditCompiledModulesIO #[`ProtoDiskPreludeEvil]
      { checkStatementOrigin := false, requireTheoremKind := true }
      (explicitTargets? := some #[`evilClaim]) (extraSearchPaths := [tmpDir])
    assertRejectedWithTag "D4_prelude_redeclared_propext" vPrelude "unapprovedAxiom"
    lines := lines.push (formatVerdictTags "D4_prelude_redeclared_propext" vPrelude)

    -- D5: a package-provided module merely *named* `Std.*` used to inherit stdlib trust:
    --     its `@[implemented_by]` was skipped and it acted as an allowed statement-origin
    --     boundary hiding an `Anneal.*`-module dependency.
    IO.FS.createDirAll (tmpDir / "Anneal")
    IO.FS.createDirAll (tmpDir / "Std")
    IO.FS.createDirAll (tmpDir / "Verify")
    IO.FS.writeFile (tmpDir / "Anneal" / "ProtoDiskLeak.lean")
      "def protoLeakSecret (n : Nat) : Prop := n = n\n"
    compileTempModuleWithPath tmpDir (tmpDir / "Anneal" / "ProtoDiskLeak.lean")
      (tmpDir / "Anneal" / "ProtoDiskLeak.olean")
    IO.FS.writeFile (tmpDir / "Std" / "ProtoDiskEvil.lean") <|
      "import Anneal.ProtoDiskLeak\n" ++
      "def stdAlias (n : Nat) : Prop := protoLeakSecret n\n" ++
      "unsafe def evilImpl : Nat := 42\n" ++
      "@[implemented_by evilImpl] def stdStub : Nat := 0\n"
    compileTempModuleWithPath tmpDir (tmpDir / "Std" / "ProtoDiskEvil.lean")
      (tmpDir / "Std" / "ProtoDiskEvil.olean")
    IO.FS.writeFile (tmpDir / "Verify" / "ProtoDiskVictim.lean") <|
      "import Std.ProtoDiskEvil\n" ++
      "theorem Verify.claimLeak : stdAlias 0 := (rfl : (0 : Nat) = 0)\n" ++
      "theorem Verify.claimStub : stdStub = 0 := rfl\n"
    compileTempModuleWithPath tmpDir (tmpDir / "Verify" / "ProtoDiskVictim.lean")
      (tmpDir / "Verify" / "ProtoDiskVictim.olean")
    let loadedVictim ← loadOrThrow "D5_load" #[`Verify.ProtoDiskVictim] {} [tmpDir]
    let vSpoofLeak ← auditLoadedModulesIO loadedVictim AuditPolicy.strictClaim
      (explicitTargets? := some #[`Verify.claimLeak])
    let vSpoofStub ← auditLoadedModulesIO loadedVictim AuditPolicy.strictClaim
      (explicitTargets? := some #[`Verify.claimStub])
    assertRejectedWithTag "D5_spoofed_std_module_statement_leak" vSpoofLeak "moduleProvenanceSpoofed"
    assertRejectedWithTag "D5_spoofed_std_module_implemented_by" vSpoofStub "moduleProvenanceSpoofed"
    let namesSpoofedModule := vSpoofLeak.violations.any fun
      | .moduleProvenanceSpoofed m _ _ => m == `Std.ProtoDiskEvil
      | _ => false
    unless namesSpoofedModule do
      throw <| IO.userError s!"expected Std.ProtoDiskEvil to be reported:\n{auditReportJson vSpoofLeak |>.pretty}"
    lines := lines.push (formatVerdictTags "D5_spoofed_std_module_statement_leak" vSpoofLeak)
    lines := lines.push (formatVerdictTags "D5_spoofed_std_module_implemented_by" vSpoofStub)

    -- D7: a package-provided module merely *named* `Trusted.*`. `Trusted` is not a
    --     default statement-origin boundary, so the hidden `Anneal.*`-module dependency
    --     is found; opting `Trusted` back in as a boundary requires pinning it to a
    --     directory, and a module resolving anywhere else is rejected.
    IO.FS.createDirAll (tmpDir / "Trusted")
    IO.FS.writeFile (tmpDir / "Trusted" / "ProtoDiskEvil.lean") <|
      "import Anneal.ProtoDiskLeak\n" ++
      "def trustedAlias (n : Nat) : Prop := protoLeakSecret n\n"
    compileTempModuleWithPath tmpDir (tmpDir / "Trusted" / "ProtoDiskEvil.lean")
      (tmpDir / "Trusted" / "ProtoDiskEvil.olean")
    IO.FS.writeFile (tmpDir / "Verify" / "ProtoDiskVictimTrusted.lean") <|
      "import Trusted.ProtoDiskEvil\n" ++
      "theorem Verify.claimTrustedLeak : trustedAlias 0 := (rfl : (0 : Nat) = 0)\n"
    compileTempModuleWithPath tmpDir (tmpDir / "Verify" / "ProtoDiskVictimTrusted.lean")
      (tmpDir / "Verify" / "ProtoDiskVictimTrusted.olean")
    let trustedBoundaryPol : AuditPolicy :=
      { AuditPolicy.strictClaim with statementAllowedRoots := #[`Init, `Std, `Trusted] }
    let loadedTrustedVictim ← loadOrThrow "D7_load" #[`Verify.ProtoDiskVictimTrusted] {} [tmpDir]
    let auditTrustedVictim (policy : AuditPolicy) (pins : Array (Name × System.FilePath)) :=
      auditLoadedModulesIO loadedTrustedVictim policy
        (explicitTargets? := some #[`Verify.claimTrustedLeak]) (pinnedModuleRoots := pins)
    let vTrustedDefault ← auditTrustedVictim AuditPolicy.strictClaim #[]
    let vTrustedUnpinned ← auditTrustedVictim trustedBoundaryPol #[]
    let vTrustedElsewhere ← auditTrustedVictim trustedBoundaryPol
      #[(`Trusted, tmpDir / "PinnedElsewhere")]
    -- Positive control: when the caller explicitly pins `Trusted` to this very directory,
    -- the pin is honoured and the boundary applies (the caller vouched for that tree).
    let vTrustedPinnedHere ← auditTrustedVictim trustedBoundaryPol #[(`Trusted, tmpDir)]
    assertRejectedWithTag "D7_spoofed_trusted_default_policy" vTrustedDefault "statementOriginLeak"
    assertRejectedWithTag "D7_spoofed_trusted_unpinned_boundary" vTrustedUnpinned "moduleProvenanceSpoofed"
    assertRejectedWithTag "D7_spoofed_trusted_pinned_elsewhere" vTrustedElsewhere "moduleProvenanceSpoofed"
    assertAuditOk "D7_pinned_root_honoured" vTrustedPinnedHere
    lines := lines.push (formatVerdictTags "D7_spoofed_trusted_default_policy" vTrustedDefault)
    lines := lines.push (formatVerdictTags "D7_spoofed_trusted_unpinned_boundary" vTrustedUnpinned)
    lines := lines.push (formatVerdictTags "D7_spoofed_trusted_pinned_elsewhere" vTrustedElsewhere)
    lines := lines.push (formatVerdictTags "D7_pinned_root_honoured" vTrustedPinnedHere)

    -- D6: no root modules means nothing was audited.
    let vNoRoots ← auditCompiledModulesIO #[] pol
    assertRejectedWithTag "D6_no_root_modules" vNoRoots "noAuditTargets"
    lines := lines.push (formatVerdictTags "D6_no_root_modules" vNoRoots)

    -- A1-1: split-artifact symlink attack (`Std/Time.olean` & `.olean.server` symlinked
    --       into the real toolchain while `Std/Time.olean.private` is attacker-owned in
    --       `tmpDir`). Checking ONLY `.olean`'s `realPath` used to pass; checking parent
    --       dir + all companion artifact `realPath`s rejects it fail-closed.
    let symlinkRoot := tmpDir / "SymlinkSplit"
    IO.FS.createDirAll (symlinkRoot / "Std")
    let libDir ← Lean.getLibDir (← Lean.getBuildDir)
    let _ ← IO.Process.output {
      cmd := "ln"
      args := #["-s", (libDir / "Std" / "Time.olean").toString,
                (symlinkRoot / "Std" / "Time.olean").toString]
    }
    let _ ← IO.Process.output {
      cmd := "ln"
      args := #["-s", (libDir / "Std" / "Time.olean.server").toString,
                (symlinkRoot / "Std" / "Time.olean.server").toString]
    }
    IO.FS.writeFile (symlinkRoot / "Std" / "Time.olean.private") "attacker-private-payload"
    let vSymSplit ← withExtraSearchPaths [symlinkRoot] do
      let vs ← checkModuleProvenanceIO #[`Std.Time]
      pure (if vs.isEmpty then AuditVerdict.ok {} else AuditVerdict.rejected vs {})
    assertRejectedWithTag "A1_symlink_split_provenance" vSymSplit "moduleProvenanceSpoofed"
    lines := lines.push (formatVerdictTags "A1_symlink_split_provenance" vSymSplit)

    -- A1-5a/b: `prelude` module re-declaring its own `Eq`/`Bool`/`Bool.true` + forged
    --          native axiom AND re-declaring `Lean.ofReduceBool`. Both must be rejected
    --          as `.unapprovedAxiom` (never accepted provisionally or misclassified).
    let preludeNatLean := tmpDir / "ProtoDiskPreludeFakeNat.lean"
    IO.FS.writeFile preludeNatLean <|
      "prelude\n" ++
      "inductive Eq.{u} {α : Sort u} (a : α) : α → Prop | refl : Eq a a\n" ++
      "inductive Bool : Type | true | false\n" ++
      "axiom spoof._native.native_decide.ax_1_1 : Eq Bool.false Bool.true\n" ++
      "axiom Lean.ofReduceBool : ∀ (P : Prop), P\n" ++
      "theorem useFakeNat : Eq Bool.false Bool.true := spoof._native.native_decide.ax_1_1\n" ++
      "theorem useFakeOfRB (P : Prop) : P := Lean.ofReduceBool P\n"
    compileTempModuleToOlean tmpDir preludeNatLean (tmpDir / "ProtoDiskPreludeFakeNat.olean")
    let loadedPreludeNat ← loadOrThrow "A1_prelude_nat_load" #[`ProtoDiskPreludeFakeNat] pol [tmpDir]
    let vPreludeFakeNat ← auditLoadedModulesIO loadedPreludeNat
      { checkStatementOrigin := false, allowProvisionalNative := true }
      (explicitTargets? := some #[`useFakeNat])
    let vPreludeFakeOfRB ← auditLoadedModulesIO loadedPreludeNat
      { checkStatementOrigin := false, allowProvisionalNative := false }
      (explicitTargets? := some #[`useFakeOfRB])
    assertRejectedWithTag "A1_prelude_fake_native_eq_bool" vPreludeFakeNat "unapprovedAxiom"
    assertRejectedWithTag "A1_prelude_redeclared_ofReduceBool" vPreludeFakeOfRB "unapprovedAxiom"
    lines := lines.push (formatVerdictTags "A1_prelude_fake_native_eq_bool" vPreludeFakeNat)
    lines := lines.push (formatVerdictTags "A1_prelude_redeclared_ofReduceBool" vPreludeFakeOfRB)
    return lines
  let lines ← try body finally IO.FS.removeDirAll tmpDir
  let clean := !(← tmpDir.pathExists)
  return String.intercalate "\n" (lines.push s!"tmp_clean={clean}").toList

/--
info: D2_missing_olean_server_part: rejected [missingPrivateArtifact]
D3_corrupt_olean_header: rejected [environmentLoadFailed]
D4_prelude_redeclared_propext: rejected [unapprovedAxiom]
D5_spoofed_std_module_statement_leak: rejected [moduleProvenanceSpoofed]
D5_spoofed_std_module_implemented_by: rejected [moduleProvenanceSpoofed]
D7_spoofed_trusted_default_policy: rejected [statementOriginLeak]
D7_spoofed_trusted_unpinned_boundary: rejected [moduleProvenanceSpoofed]
D7_spoofed_trusted_pinned_elsewhere: rejected [moduleProvenanceSpoofed]
D7_pinned_root_honoured: ok []
D6_no_root_modules: rejected [noAuditTargets]
A1_symlink_split_provenance: rejected [moduleProvenanceSpoofed]
A1_prelude_fake_native_eq_bool: rejected [unapprovedAxiom]
A1_prelude_redeclared_ofReduceBool: rejected [unapprovedAxiom]
tmp_clean=true
-/
#guard_msgs in
run_cmd do
  let summary ← liftIO runDiskHardeningRegressions
  logInfo summary

/-! ## Real Compiled `.olean` Zero-FP Audits & Measured Latency Benchmarks -/

/-- Name prefixes (inside `Anneal.OleanSpecStrengthAuditorProto`) identifying the pure
    specification-strength half of the prototype module: certificates, metatheorems,
    typeclass bridges, and the `fxfs` / `fuchsia_usercopy` examples. -/
def pureSpecHalfPrefixes : Array String := #[
  "SpecStrengthCert", "MutantCategory", "NamedMutantKill", "MultiMutantSpecCert",
  "DeterministicSpecCert", "ModularSpecStrengthCert", "ModularMultiMutantSpecCert",
  "ModularDeterministicSpecCert", "no_", "mutant_impl", "multi_mutant", "ItemSpecStrengthCert",
  "ItemMultiMutantCert", "StatefulItem", "ModularItem", "fxfs", "fuchsia", "weak",
  "truncated", "strong", "mutatedFrameMemory", "instDecidableEqMutantCategory",
  "instReprMutantCategory", "instInhabitedMutantCategory"]

/-- Select EVERY declaration of the pure specification-strength half (including all
    compiler-generated auxiliaries such as recursors, matchers, and derived instances),
    so newly added certificates can never be forgotten in a hand-maintained list. The
    only exclusion is `MutantCategory.toExpr`, the auditor-side reflection helper that
    necessarily mentions `Lean.Expr`. -/
def selectPureSpecHalfTargets (env : Environment) : Array Name := Id.run do
  let mut targets : Array Name := #[]
  for m in env.header.modules, data in env.header.moduleData do
    if m.module == `Anneal.OleanSpecStrengthAuditorProto then
      for ci in data.constants do
        let user := (Lean.privateToUserName ci.name).replacePrefix
          `Anneal.OleanSpecStrengthAuditorProto .anonymous
        let s := user.toString
        if pureSpecHalfPrefixes.any (s.startsWith ·) && !s.startsWith "MutantCategory.toExpr" then
          targets := targets.push ci.name
  return targets

def runRealModuleBenchmarks (trustedMods pureTargets : Array Name) : IO String := do
  -- 1. `Trusted.VerificationResult`: full audit of EVERY declaration INCLUDING
  --    statement-origin separation (`checkStatementOrigin := true`).
  let loadedTrusted ← loadOrThrow "RealModule_Trusted_load" trustedMods
  let vTrusted ← auditLoadedModulesIO loadedTrusted { checkStatementOrigin := true }
    (theoremsOnly := false) (targetModules? := some #[`Trusted.VerificationResult])
  assertAuditOk "RealModule_Trusted.VerificationResult" vTrusted

  -- 2. EVERY `Trusted.*` module as an audit root (same policy, same loaded environment).
  let vAllTrusted ← auditLoadedModulesIO loadedTrusted { checkStatementOrigin := true }
  assertAuditOk "RealModule_all_Trusted_modules" vAllTrusted

  -- 3. `Anneal.OleanSpecStrengthAuditorProto`: the whole pure specification-strength half
  --    (certificates, metatheorems, bridges, `fxfs` / `fuchsia_usercopy` examples, and
  --    their compiler-generated auxiliaries) under `AuditPolicy.constructive`
  --    (0 `Classical.choice`, 0 `sorryAx`, 0 `Lean.*`).
  for required in #[``fxfsVmoSubsliceMultiCert, ``fuchsiaUsercopyCopyinMultiCert,
      ``fxfsVmoSubslice_deterministic, ``fuchsiaUsercopyCopyin_deterministic,
      ``no_cert_of_vacuous_req, ``no_kill_at_unrealizable_input,
      ``weak_vmo_subslice_not_deterministic, ``MultiMutantSpecCert.covers_implies_exists_kill] do
    unless pureTargets.contains required do
      throw <| IO.userError s!"pure spec-strength target selection lost {required}"
  let vProtoPure ← auditCompiledModulesIO #[`Anneal.OleanSpecStrengthAuditorProto]
    { AuditPolicy.constructive with checkStatementOrigin := false }
    (explicitTargets? := some pureTargets)
  assertAuditOk "RealModule_OleanSpecStrengthAuditorProto_pure_half" vProtoPure

  let line (label : String) (s : AuditStats) : String :=
    s!"  {label}: targets={s.targetsAudited}, reachable={s.reachableDeclarations}, modules={s.modulesLoaded}, axioms={s.axiomsFound.toList}, import={s.importMicros / 1000}ms, audit={(s.elapsedMicros - s.importMicros) / 1000}ms, total={s.elapsedMicros / 1000}ms"
  return s!"RealCompiledModuleAudits: PASS (0 FP)\n" ++
    line "Trusted.VerificationResult" vTrusted.stats ++ "\n" ++
    line s!"all {trustedMods.size} Trusted.* modules" vAllTrusted.stats ++ "\n" ++
    line "Anneal.OleanSpecStrengthAuditorProto (entire pure spec-strength half incl. auxiliaries)"
      vProtoPure.stats

#eval show CommandElabM Unit from do
  let env ← getEnv
  let trustedMods := env.header.modules.filterMap fun m =>
    if m.module == `Trusted || m.module.toString.startsWith "Trusted." then some m.module else none
  let pureTargets := selectPureSpecHalfTargets env
  let summary ← liftIO <| runRealModuleBenchmarks trustedMods pureTargets
  logInfo summary

/-- info: ProtoOwnModuleInventory: PASS (0 partial, 0 unsafe) -/
#guard_msgs in
run_cmd do
  let privProto := (← getEnv).setExporting false
  let mut ownPartialOrUnsafe : Array Name := #[]
  let mut ownDeclCount : Nat := 0
  for m in privProto.header.modules, data in privProto.header.moduleData do
    if m.module == `Anneal.OleanSpecStrengthAuditorProto then
      for ci in data.constants do
        if !isCodegenUnsafeRec privProto (some m.module) ci then
          ownDeclCount := ownDeclCount + 1
          if ci.isUnsafe || ci.isPartial || (detectPartialOrUnsafeRec privProto ci.name ci).isSome then
            ownPartialOrUnsafe := ownPartialOrUnsafe.push ci.name
  unless ownDeclCount > 0 && ownPartialOrUnsafe.isEmpty do
    throwError "unexpected partial/unsafe declarations in OleanSpecStrengthAuditorProto: {ownPartialOrUnsafe} (decls={ownDeclCount})"
  logInfo "ProtoOwnModuleInventory: PASS (0 partial, 0 unsafe)"

/-! ## Positive Constructive `#print axioms` Audits (`#guard_msgs`) -/

/-- info: 'Anneal.OleanSpecStrengthAuditorProto.fxfsVmoSubsliceMultiCert' does not depend on any axioms -/
#guard_msgs in
#print axioms Anneal.OleanSpecStrengthAuditorProto.fxfsVmoSubsliceMultiCert

/-- info: 'Anneal.OleanSpecStrengthAuditorProto.fxfsVmoSubslice_covers_required_categories' does not depend on any axioms -/
#guard_msgs in
#print axioms Anneal.OleanSpecStrengthAuditorProto.fxfsVmoSubslice_covers_required_categories

/-- info: 'Anneal.OleanSpecStrengthAuditorProto.fuchsiaUsercopyCopyinMultiCert' does not depend on any axioms -/
#guard_msgs in
#print axioms Anneal.OleanSpecStrengthAuditorProto.fuchsiaUsercopyCopyinMultiCert

/-- info: 'Anneal.OleanSpecStrengthAuditorProto.fuchsiaUsercopyCopyin_covers_required_categories' does not depend on any axioms -/
#guard_msgs in
#print axioms Anneal.OleanSpecStrengthAuditorProto.fuchsiaUsercopyCopyin_covers_required_categories

/-- info: 'Anneal.OleanSpecStrengthAuditorProto.no_cert_of_vacuous_req' does not depend on any axioms -/
#guard_msgs in
#print axioms Anneal.OleanSpecStrengthAuditorProto.no_cert_of_vacuous_req

/-- info: 'Anneal.OleanSpecStrengthAuditorProto.no_cert_of_trivial_ens' does not depend on any axioms -/
#guard_msgs in
#print axioms Anneal.OleanSpecStrengthAuditorProto.no_cert_of_trivial_ens

/-- info: 'Anneal.OleanSpecStrengthAuditorProto.no_multi_cert_of_unsatisfiable_ens' does not depend on any axioms -/
#guard_msgs in
#print axioms Anneal.OleanSpecStrengthAuditorProto.no_multi_cert_of_unsatisfiable_ens

/-- info: 'Anneal.OleanSpecStrengthAuditorProto.no_itemSpec_cert_of_default_post' does not depend on any axioms -/
#guard_msgs in
#print axioms Anneal.OleanSpecStrengthAuditorProto.no_itemSpec_cert_of_default_post

/-- info: 'Anneal.OleanSpecStrengthAuditorProto.strong_vmo_subslice_rejects_truncated_mutant' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.OleanSpecStrengthAuditorProto.strong_vmo_subslice_rejects_truncated_mutant

/-- info: 'Anneal.OleanSpecStrengthAuditorProto.weak_vmo_subslice_truncated_mutant_survives' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.OleanSpecStrengthAuditorProto.weak_vmo_subslice_truncated_mutant_survives

/-- info: 'Anneal.OleanSpecStrengthAuditorProto.fxfsVmoSubslice_deterministic' does not depend on any axioms -/
#guard_msgs in
#print axioms Anneal.OleanSpecStrengthAuditorProto.fxfsVmoSubslice_deterministic

/-- info: 'Anneal.OleanSpecStrengthAuditorProto.fuchsiaUsercopyCopyin_deterministic' does not depend on any axioms -/
#guard_msgs in
#print axioms Anneal.OleanSpecStrengthAuditorProto.fuchsiaUsercopyCopyin_deterministic

/-- info: 'Anneal.OleanSpecStrengthAuditorProto.weak_vmo_subslice_not_deterministic' does not depend on any axioms -/
#guard_msgs in
#print axioms Anneal.OleanSpecStrengthAuditorProto.weak_vmo_subslice_not_deterministic

/-- info: 'Anneal.OleanSpecStrengthAuditorProto.DeterministicSpecCert.kills_every_deviation' does not depend on any axioms -/
#guard_msgs in
#print axioms Anneal.OleanSpecStrengthAuditorProto.DeterministicSpecCert.kills_every_deviation

/-- info: 'Anneal.OleanSpecStrengthAuditorProto.no_kill_at_unrealizable_input' does not depend on any axioms -/
#guard_msgs in
#print axioms Anneal.OleanSpecStrengthAuditorProto.no_kill_at_unrealizable_input

/-- info: 'Anneal.OleanSpecStrengthAuditorProtoTests.testKillOnlyAtRealizableInput' does not depend on any axioms -/
#guard_msgs in
#print axioms Anneal.OleanSpecStrengthAuditorProtoTests.testKillOnlyAtRealizableInput

/-- info: 'Anneal.OleanSpecStrengthAuditorProtoTests.testFxfsEveryDeviationKilled' does not depend on any axioms -/
#guard_msgs in
#print axioms Anneal.OleanSpecStrengthAuditorProtoTests.testFxfsEveryDeviationKilled

/--
info: 'Anneal.OleanSpecStrengthAuditorProto.fuchsiaUsercopyCopyinModularDirectMultiCert' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.OleanSpecStrengthAuditorProto.fuchsiaUsercopyCopyinModularDirectMultiCert

/--
info: 'Anneal.OleanSpecStrengthAuditorProto.fuchsiaUsercopyCopyinModularDirectDetCert' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.OleanSpecStrengthAuditorProto.fuchsiaUsercopyCopyinModularDirectDetCert

/-- info: 'Anneal.OleanSpecStrengthAuditorProto.no_modular_cert_of_vacuous_envAssumed' does not depend on any axioms -/
#guard_msgs in
#print axioms Anneal.OleanSpecStrengthAuditorProto.no_modular_cert_of_vacuous_envAssumed

end Anneal.OleanSpecStrengthAuditorProtoTests
