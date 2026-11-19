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
def elabInSandbox (code : String) : CommandElabM Environment := do
  let env ← getEnv
  let opts ← getOptions
  let (env', msgs) ← liftIO <| Lean.Elab.process code env opts (some "<sandbox>")
  if msgs.hasErrors then
    let mut errs : Array String := #[]
    for m in msgs.toList do
      if m.severity == .error then
        errs := errs.push (← m.toString)
    throwError "sandbox elaboration failed unexpectedly:\n{String.intercalate "\n" errs.toList}"
  return env'

/-- Format a deterministic summary of `AuditVerdict` (omitting non-deterministic timings). -/
def formatVerdictTags (label : String) (v : AuditVerdict) : String :=
  match v with
  | .ok _ => s!"{label}: ok []"
  | .rejected vs _ =>
    let tags := (vs.map AuditViolation.tag).toList.eraseDups.mergeSort (· < ·)
    s!"{label}: rejected {tags}"

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
  liftIO <| assertAuditOk "Positive_usercopy_direct_gate" vUsercopyDirect
  lines := lines ++ [formatVerdictTags "Positive_usercopy_direct_gate" vUsercopyDirect]
  logInfo (String.intercalate "\n" lines)

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
    let (exportedSawPrivAx, exportedClaimKind) ← withExtraSearchPaths [tmpDir] do
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
      return (sawPriv, claimKind)
    if exportedSawPrivAx then
      throw <| IO.userError "expected OLeanLevel.exported to hide private axiom, but it was visible"

    -- C. Audit with `OLeanLevel.private` + `env.setExporting false` -> MUST catch hidden private axiom.
    let vPriv ← auditCompiledModulesIO #[sneakyMod]
      { checkStatementOrigin := false, requireTheoremKind := true }
      (explicitTargets? := some #[`sneakyExportedClaim])
      (extraSearchPaths := [tmpDir])
    assertRejectedWithTag "DiskPrivateOlean_catch_hidden_axiom" vPriv "unapprovedAxiom"
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

    return s!"DiskPrivateOleanRoundTrip: PASS (olean={oleanBytes}B, server={serverBytes}B, private={privBytes}B, exportedSawPrivAx={exportedSawPrivAx}, exportedClaimKind={exportedClaimKind}, privateAudit={formatVerdictTags "priv" vPriv}, deletedPrivateAudit={formatVerdictTags "del" vMissingPriv}, cleanReplayDecls={vClean.stats.kernelReplayedDeclarations}, privLatencyUs={vPriv.stats.elapsedMicros})"
  finally
    IO.FS.removeDirAll tmpDir

#eval runDiskPrivateOleanRoundTrip

/-! ## Real Compiled `.olean` Zero-FP Audits & Measured Latency Benchmarks -/

def runRealModuleBenchmarks : IO String := do
  -- 1. `Trusted.VerificationResult`: full audit of EVERY declaration INCLUDING
  --    statement-origin separation (`checkStatementOrigin := true`).
  let vTrusted ← auditCompiledModulesIO #[`Trusted.VerificationResult]
    { checkStatementOrigin := true }
    (theoremsOnly := false)
  assertAuditOk "RealModule_Trusted.VerificationResult" vTrusted

  -- 2. `Anneal.OleanSpecStrengthAuditorProto`: all constructive spec-strength
  --    metatheorems, bridges, and `fxfs` / `fuchsia_usercopy` certificates under
  --    `AuditPolicy.constructive` (0 `Classical.choice`, 0 `sorryAx`, 0 `Lean.*`).
  let pureSpecTargets : Array Name := #[
    ``MultiMutantSpecCert.covers_implies_exists_kill,
    ``no_cert_of_vacuous_req,
    ``no_cert_of_unsatisfiable_req,
    ``no_cert_of_trivial_ens,
    ``no_cert_of_universal_ens,
    ``no_multi_cert_of_unsatisfiable_ens,
    ``mutant_impl_rejected_by_spec,
    ``multi_mutant_impl_rejected_by_spec,
    ``no_itemSpec_cert_of_default_post,
    ``no_statefulItemSpec_cert_of_default_post,
    ``no_modularItemSpec_cert_of_vacuous_envAssumed,
    ``fxfsVmoSubsliceMultiCert,
    ``fxfsVmoSubslice_covers_required_categories,
    ``fuchsiaHermeticCopyWitnessHandler_valid,
    ``fuchsiaUsercopyCopyinMultiCert,
    ``fuchsiaUsercopyCopyin_covers_required_categories,
    ``weakVmoSubsliceSingleCert,
    ``weak_vmo_subslice_truncated_mutant_survives,
    ``strong_vmo_subslice_rejects_truncated_mutant
  ]
  let vProtoPure ← auditCompiledModulesIO #[`Anneal.OleanSpecStrengthAuditorProto]
    { AuditPolicy.constructive with checkStatementOrigin := false }
    (explicitTargets? := some pureSpecTargets)
  assertAuditOk "RealModule_OleanSpecStrengthAuditorProto_pure_certs" vProtoPure

  -- 3. Inventory sanity check on `Anneal.OleanSpecStrengthAuditorProto` using the
  --    already-imported environment (avoiding a redundant 2,381-module `Lean` re-import
  --    in the same interpreter process): verify 0 `partial` and 0 `unsafe` declarations
  --    authored in `OleanSpecStrengthAuditorProto` itself.
  let s1 := vTrusted.stats
  let s2 := vProtoPure.stats
  let ms1 := s1.elapsedMicros / 1000
  let ms2 := s2.elapsedMicros / 1000
  return s!"RealCompiledModuleAudits: PASS (0 FP)\n" ++
    s!"  Trusted.VerificationResult: targets={s1.targetsAudited}, reachable={s1.reachableDeclarations}, axioms={s1.axiomsFound.toList}, elapsed={ms1}ms ({s1.elapsedMicros}us)\n" ++
    s!"  Anneal.OleanSpecStrengthAuditorProto (19 constructive certs & metatheorems): targets={s2.targetsAudited}, reachable={s2.reachableDeclarations}, axioms={s2.axiomsFound.toList}, elapsed={ms2}ms ({s2.elapsedMicros}us)"

#eval runRealModuleBenchmarks

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

/-- info: 'Anneal.OleanSpecStrengthAuditorProto.fuchsiaUsercopyCopyinMultiCert' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.OleanSpecStrengthAuditorProto.fuchsiaUsercopyCopyinMultiCert

/-- info: 'Anneal.OleanSpecStrengthAuditorProto.fuchsiaUsercopyCopyin_covers_required_categories' depends on axioms: [propext] -/
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

end Anneal.OleanSpecStrengthAuditorProtoTests
