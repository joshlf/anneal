import Anneal.ReplayKeyAndTamperAuditPrototype

/-!
# Concrete Regression & Axiom-Audit Tests for `Anneal.ReplayKeyAndTamperAuditPrototype`

Exercises:
1. `#guard_msgs in #print axioms` confirming zero `sorryAx`, zero `Lean.ofReduceBool`,
   zero `Lean.ofReduceNat`, zero `Lean.trustCompiler`, and zero custom axioms on every core theorem.
2. Constructive regression tests for all 4 `lean4#16677` (`issue16675`) bypasses, the
   `TrustedBoundary` (`downstreamAudit` L408 / `verifyAudit` L607) `replayLocals` overwrite exploit,
   `lowmem_lean` mutual `.all` blocks (both `thmDecl` and `opaqueDecl`) + all 7 malformed `.all` forms,
   `pillar_1` native-reduction bans + provisional scoping, and all 18 `bensherman` vectors (`V01`–`V18`).
3. Edge-case tests for comment/string/char-literal source stripping, open expressions,
   `expressionEdges` literal/projection edges, `extraConstNames` provenance, `_unsafe_rec` spoofing,
   and statement-vs-proof origin separation.
4. Pass-`B1` regressions: closure-walk truncation, the transitive-closure and semantic soundness
   theorems instantiated on the baseline package, role/origin/flag spoofing, the inductive and
   quotient replay bypasses (including key-ALIGNED ones), provisional native scoping, and lexer
   desynchronisation / token gluing in the source scanner.
-/

namespace Anneal.ReplayKeyAndTamperAuditProtoTests

open Anneal.ReplayKeyAndTamperAuditPrototype

/-! ## Section 1: Kernel Axiom Hygiene (`#guard_msgs in #print axioms`) -/

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.validInventory_length_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms validInventory_length_eq

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.validInventory_constNames_nodup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms validInventory_constNames_nodup

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.validInventory_key_eq_ci_name' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms validInventory_key_eq_ci_name

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.validInventory_lookup_bijection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms validInventory_lookup_bijection

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.validInventory_mutual_all_wf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms validInventory_mutual_all_wf

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.validPackage_axiom_closure_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms validPackage_axiom_closure_sound

/-- info: 'Anneal.ReplayKeyAndTamperAuditPrototype.kernelEnv_no_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms kernelEnv_no_false

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.kernel_sound_at_fuel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms kernel_sound_at_fuel

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.kernelCheckDecl_preserves_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms kernelCheckDecl_preserves_sound

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.replayCleanEnv_preserves_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms replayCleanEnv_preserves_sound

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.standardBaseEnv_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms standardBaseEnv_sound

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.auditAndReplayPackage_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms auditAndReplayPackage_sound

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.validBaselinePackage_no_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms validBaselinePackage_no_false

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.issue16675_recursor_bypass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms issue16675_recursor_bypass

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.trustedBoundary_overwrite_bypass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms trustedBoundary_overwrite_bypass

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.V06_tamper_ext_isolated_rejection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms V06_tamper_ext_isolated_rejection

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.V09_replay_only_isolated_rejection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms V09_replay_only_isolated_rejection

/-- info: 'Anneal.ReplayKeyAndTamperAuditPrototype.walkGraph_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms walkGraph_sound

/-- info: 'Anneal.ReplayKeyAndTamperAuditPrototype.walkGraph_reaches_subset' depends on axioms: [propext] -/
#guard_msgs in #print axioms walkGraph_reaches_subset

/-- info: 'Anneal.ReplayKeyAndTamperAuditPrototype.statementOrigins_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms statementOrigins_sound

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.auditAndReplayPackage_global_names_nodup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms auditAndReplayPackage_global_names_nodup

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.auditAndReplayPackage_closure_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms auditAndReplayPackage_closure_sound

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.auditAndReplayPackage_verifyRoots_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms auditAndReplayPackage_verifyRoots_sound

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.kernelEnv_prop_types_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms kernelEnv_prop_types_true

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.auditAndReplayPackage_semantic_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms auditAndReplayPackage_semantic_sound

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.legacyClosureWalk_truncation_bypass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms legacyClosureWalk_truncation_bypass

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.issue16675_induct_bypass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms issue16675_induct_bypass

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.issue16675_induct_all_aligned_key_bypass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms issue16675_induct_all_aligned_key_bypass

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.issue16675_quot_aligned_key_bypass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms issue16675_quot_aligned_key_bypass

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.roleSpoof_labels_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms roleSpoof_labels_rejected

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.statementOrigin_laundering_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms statementOrigin_laundering_rejected

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.sourceScanner_lexer_desync_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms sourceScanner_lexer_desync_rejected

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.pillar1_provisional_scoping' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms pillar1_provisional_scoping

/-! ## Section 2: Direct Verification of All Vulnerability Exploits & 18 Tamper Vectors -/

example := issue16675_recursor_bypass
example := issue16675_ctor_bypass
example := issue16675_quot_bypass
example := issue16675_thm_dup_bypass
example := trustedBoundary_overwrite_bypass
example := mutual_thm_false_rejection_and_sound_acceptance
example := malformedAll_all_seven_rejected
example := pillar1_native_reduction_all_rejected
example := V01_hijack_macro_rejected
example := V02_hijack_elab_rejected
example := V03_skip_kernel_tc_rejected_both_layers
example := V04_unref_axiom_rejected
example := V05_shadow_sorry_rejected
example := V06_tamper_ext_isolated_rejection
example := V07_local_elab_bad_rejected
example := V08_nonlocal_elab_bad_rejected
example := V09_replay_only_isolated_rejection
example := V10_hooks_bad_all_four_rejected
example := V11_scoped_attrs_bad_all_three_rejected
example := V12_inst_and_coe_bad_and_benign_defs_ok
example := V13_reducibility_bad_both_layers_rejected
example := V14_import_all_and_private_instance_rejected
example := V15_export_shadow_and_spoofed_defs_rejected
example := V16_term_delab_bad_all_three_rejected
example := V17_missing_olean_server_rejected
example := V18_missing_olean_private_rejected
example := validBaselinePackage_accepted
example := validBaselinePackage_no_false
example := statementTheoryLeak_rejected
example := spoofedUnsafeRec_rejected

/-! ## Section 3: Additional Edge-Case Regression Tests -/

/-- Valid 2-declaration mutual `opaqueDecl` block (`lowmem_lean` `cl/1027843093`). -/
def mutualOpaqueA : SymName := SymName.ofList ["Proof", "Opq", "opa"]
def mutualOpaqueB : SymName := SymName.ofList ["Proof", "Opq", "opb"]
def mutualOpaqueModName : SymName := SymName.ofList ["Proof", "Opq"]

def mutualOpaqueMod : ModuleInventory :=
  mkAlignedModule mutualOpaqueModName .proof [
    { name := mutualOpaqueA, kind := .opaqueDecl, type := .const SymName.natName,
      value? := some (.natLit 1), hasValue := true,
      all := [mutualOpaqueA, mutualOpaqueB], originModule := mutualOpaqueModName },
    { name := mutualOpaqueB, kind := .opaqueDecl, type := .const SymName.natName,
      value? := some (.natLit 2), hasValue := true,
      all := [mutualOpaqueA, mutualOpaqueB], originModule := mutualOpaqueModName }
  ]

theorem mutual_opaque_naive_rejects_hardened_accepts :
    (naiveSingleAllCheck mutualOpaqueMod).isOk = false ∧
    validateReplayInventory mutualOpaqueMod = .ok () ∧
    (auditAndReplayPackage defaultUnconditionalConfig
      { baseEnv := standardBaseDecls, modules := [mutualOpaqueMod] }).isOk = true :=
  ⟨rfl, rfl, rfl⟩

/-- Char literal `'"'` MUST NOT swallow subsequent forbidden `debug.skipKernelTC` into string mode! -/
theorem sourceScanner_charQuote_does_not_mask_skipKernelTC :
    SourceScanner.scanSourceDefenseInDepth defaultUnconditionalConfig topicProofModName .proof
      "def q := '\"'\nset_option debug.skipKernelTC true" =
      .error (.forbiddenSourceOption topicProofModName "debug.skipKernelTC") :=
  rfl

/-- Additional forbidden source options: `backward.privateInPublic`, `hygiene false`, `quotPrecheck false`. -/
theorem sourceScanner_extra_forbidden_options :
    SourceScanner.scanSourceDefenseInDepth defaultUnconditionalConfig topicProofModName .proof
      "set_option backward.privateInPublic true" =
      .error (.forbiddenSourceOption topicProofModName "backward.privateInPublic") ∧
    SourceScanner.scanSourceDefenseInDepth defaultUnconditionalConfig topicProofModName .proof
      "set_option hygiene false" =
      .error (.forbiddenSourceOption topicProofModName "hygiene false") ∧
    SourceScanner.scanSourceDefenseInDepth defaultUnconditionalConfig topicProofModName .proof
      "set_option quotPrecheck false" =
      .error (.forbiddenSourceOption topicProofModName "quotPrecheck false") :=
  ⟨rfl, rfl, rfl⟩

/-- Comments and strings containing `hygiene false`, `quotPrecheck false`, `decide +native` produce ZERO false positives. -/
theorem sourceScanner_comments_and_strings_no_false_positive :
    SourceScanner.scanSourceDefenseInDepth defaultUnconditionalConfig topicProofModName .proof
      "-- hygiene false\n/- quotPrecheck false -/\ntheorem ok := trivial" = .ok () ∧
    SourceScanner.scanSourceDefenseInDepth defaultUnconditionalConfig topicProofModName .proof
      "def s := \"decide +native bv_decide\"\ntheorem ok := trivial" = .ok () :=
  ⟨rfl, rfl⟩

/-- `expressionEdges` rejects `.fvar`, `.mvar`, and unbound `.bvar`, and records `Nat`, `String`, and `.proj` struct edges. -/
theorem expressionEdges_open_and_literal_proj_tests :
    ExprSkeleton.expressionEdges (SymName.mkSimple "e1") (.fvar 0) =
      .error (.openExpression (SymName.mkSimple "e1")) ∧
    ExprSkeleton.expressionEdges (SymName.mkSimple "e2") (.mvar 0) =
      .error (.openExpression (SymName.mkSimple "e2")) ∧
    ExprSkeleton.expressionEdges (SymName.mkSimple "e3") (.bvar 0) =
      .error (.openExpression (SymName.mkSimple "e3")) ∧
    ExprSkeleton.expressionEdges (SymName.mkSimple "e4") (.lam (.const SymName.natName) (.bvar 0)) =
      .ok [SymName.natName] ∧
    ExprSkeleton.expressionEdges (SymName.mkSimple "e5")
      (.proj (SymName.ofList ["Foreign", "Struct"]) 0 (.strLit "x")) =
      .ok [SymName.ofList ["Foreign", "Struct"], SymName.stringName] ∧
    ExprSkeleton.expressionEdges (SymName.mkSimple "e6") (.natLit 3) =
      .ok [SymName.natName] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `extraConstNames` provenance check catches uninventoried kernel constant claimed in another module's `extraConstNames`. -/
def extraConstBadPkg : PackageAuditInput :=
  mkSingleProofPkg
    (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
      (extraConstNames := [defsBeforeName]))

theorem extraConstProvenance_rejected :
    auditAndReplayPackage defaultUnconditionalConfig extraConstBadPkg =
      .error (.extraConstProvenanceMismatch topicProofModName defsBeforeName) :=
  rfl

/-- `allowProvisionalNative = true` rejects `ofReduceNat` when placed outside `Proof.*` (e.g., in `Topic.Spec`). -/
def nonProofNativePkg : PackageAuditInput :=
  let axDecl : ConstantRecord := {
    name := SymName.ofReduceNatName
    kind := .axiomDecl
    type := .const SymName.trueName
    originModule := topicSpecModName
  }
  {
    baseEnv := standardBaseDecls
    modules := [mkAlignedModule topicSpecModName .spec [axDecl]]
  }

theorem provisionalNative_outside_proof_rejected :
    auditAndReplayPackage provisionalConfig nonProofNativePkg =
      .error (.forbiddenNativeReductionAxiom SymName.ofReduceNatName SymName.ofReduceNatName) :=
  rfl

/-- `replayMap` drift and length mismatch are independently rejected even before key comparison. -/
def lengthMismatchMod : ModuleInventory := {
  moduleName := demoModName
  role := .proof
  constNames := [validThmName, demoRenamedKey]
  constants := [validThmDecl]
  replayMap := [(validThmName, validThmDecl)]
}

def replayMapDriftMod : ModuleInventory := {
  moduleName := demoModName
  role := .proof
  constNames := [validThmName]
  constants := [validThmDecl]
  replayMap := [(demoRenamedKey, validThmDecl)]
}

theorem inventory_length_and_drift_rejected :
    validateReplayInventory lengthMismatchMod =
      .error (.inventoryLengthMismatch demoModName 2 1) ∧
    validateReplayInventory replayMapDriftMod =
      .error (.replayMapDrift demoModName) :=
  ⟨rfl, rfl⟩

/-- Duplicate `constNames` within a single module and across modules are both rejected. -/
def dupLocalMod : ModuleInventory := {
  moduleName := demoModName
  role := .proof
  constNames := [validThmName, validThmName]
  constants := [validThmDecl, validThmDecl]
  replayMap := [(validThmName, validThmDecl), (validThmName, validThmDecl)]
}

def dupCrossModPkg : PackageAuditInput := {
  baseEnv := standardBaseDecls
  modules := [
    mkAlignedModule (SymName.ofList ["Proof", "A"]) .proof
      [{ validThmDecl with originModule := SymName.ofList ["Proof", "A"] }],
    mkAlignedModule (SymName.ofList ["Proof", "B"]) .proof
      [{ validThmDecl with originModule := SymName.ofList ["Proof", "B"] }]
  ]
}

theorem duplicate_names_local_and_global_rejected :
    validateReplayInventory dupLocalMod =
      .error (.duplicateConstName demoModName demoModName) ∧
    auditAndReplayPackage defaultUnconditionalConfig dupCrossModPkg =
      .error (.duplicateConstName .anonymous .anonymous) :=
  ⟨rfl, rfl⟩

/-! ## Section 4: Pass-`B1` Regression Suite (Closure Truncation, Roles, Origins, Replay Fidelity, Lexer) -/

example := legacyClosureWalk_truncation_bypass
example := walkGraph_fuel_exhaustion_fails_closed
example := issue16675_induct_bypass
example := issue16675_induct_all_aligned_key_bypass
example := issue16675_quot_aligned_key_bypass
example := roleSpoof_labels_rejected
example := statementOrigin_laundering_rejected
example := v14_v15_flag_shortcuts_rejected
example := sourceScanner_lexer_desync_rejected
example := sourceScanner_token_glue_and_native_rejected
example := sourceScanner_ambiguous_lexing_fails_closed
example := sourceScanner_hardened_lexer_no_false_positive
example := pillar1_provisional_scoping

/--
End-to-end instantiation of the TRANSITIVE closure theorem on `validBaselinePackage`: everything
reachable from `Verify.Topic.verified` through `declarationEdges` is a `CleanDep`.
-/
theorem validBaselinePackage_verifyRoot_closure_clean :
    ∀ dep, DepReaches (packageEnv validBaselinePackage) validVerifyThmName dep →
      CleanDep validBaselinePackage (packageEnv validBaselinePackage) dep := by
  cases h : auditAndReplayPackage defaultUnconditionalConfig validBaselinePackage with
  | error e =>
    have hok := validBaselinePackage_accepted
    rw [h] at hok
    cases hok
  | ok cert =>
    exact auditAndReplayPackage_closure_sound h rfl rfl validVerifyThmName
      (Or.inr (Or.inl List.mem_cons_self))

/--
End-to-end instantiation of the SEMANTIC soundness theorem on `validBaselinePackage`: there is a
sound model of the replayed environment in which every proposition-typed constant of the replayed
and imported environments is true.
-/
theorem validBaselinePackage_semantic_sound :
    ∃ cert M',
      auditAndReplayPackage defaultUnconditionalConfig validBaselinePackage = .ok cert ∧
      EnvSound cert.replayedEnv M' ∧
      (∀ n ci, cert.importedEnv.lookup n = some ci →
        ∀ P : Prop, evalExpr M' [] ci.type = .prop P → P) := by
  cases h : auditAndReplayPackage defaultUnconditionalConfig validBaselinePackage with
  | error e =>
    have hok := validBaselinePackage_accepted
    rw [h] at hok
    cases hok
  | ok cert =>
    obtain ⟨M', hM', _, himp⟩ :=
      auditAndReplayPackage_semantic_sound h rfl rfl standardBaseEnv_sound
    exact ⟨cert, M', rfl, hM', himp⟩

/-- A definitional alias of `False` does not let an ill-typed proof through clean-env replay. -/
def aliasFalseName : SymName := SymName.ofList ["Topic", "Proofs", "MyFalse"]
def aliasFalseThmName : SymName := SymName.ofList ["Topic", "Proofs", "aliasBad"]

def aliasFalsePkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [
    { name := aliasFalseName, kind := .defnDecl, type := .sort 0,
      value? := some (.const SymName.falseName), hasValue := true,
      all := [aliasFalseName], originModule := topicProofModName },
    { name := aliasFalseThmName, kind := .thmDecl, type := .const aliasFalseName,
      value? := some (.const SymName.trueIntroName), hasValue := true,
      all := [aliasFalseThmName], originModule := topicProofModName }
  ])

theorem aliasedFalse_rejected_by_replay :
    auditAndReplayPackage defaultUnconditionalConfig aliasFalsePkg =
      .error (.kernelTypeError aliasFalseThmName "theorem proof term type mismatch") :=
  rfl

/-- Role labels are justified by module names in both directions (reserved roots accept only their own role). -/
theorem roleMatchesModuleName_table :
    roleMatchesModuleName .foundation (SymName.ofList ["Init", "Prelude"]) = true ∧
    roleMatchesModuleName .foundation topicProofModName = false ∧
    roleMatchesModuleName .proof (SymName.ofList ["Init", "Proofs"]) = false ∧
    roleMatchesModuleName .theory topicTheoryModName = true ∧
    roleMatchesModuleName .spec topicTheoryModName = false ∧
    roleMatchesModuleName .proof topicTheoryModName = false ∧
    roleMatchesModuleName .test topicTheoryModName = false ∧
    roleMatchesModuleName .defsExempt topicDefsModName = true ∧
    roleMatchesModuleName .defsExempt (SymName.ofList ["Anneal", "Defs"]) = false ∧
    roleMatchesModuleName .verify topicVerifyModName = true ∧
    roleMatchesModuleName .spec topicVerifyModName = false ∧
    roleMatchesModuleName .assumptions (SymName.ofList ["Assumptions", "Hw"]) = true ∧
    roleMatchesModuleName .assumptions topicSpecModName = false ∧
    roleMatchesModuleName .test (SymName.ofList ["Topic", "Tests"]) = true ∧
    roleMatchesModuleName .test topicProofModName = false ∧
    roleMatchesModuleName .spec (SymName.ofList ["Topic", "Tests"]) = false ∧
    roleMatchesModuleName .proof topicSpecModName = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Verify-root header checks: a non-theorem root and a root without a `VerificationResult` head are rejected. -/
def nonTheoremVerifyRootPkg : PackageAuditInput :=
  mkSingleProofPkg
    (mkAlignedModule topicProofModName .proof [cleanProofThmDecl])
    (extraMods := [
      mkAlignedModule topicVerifyModName .verify
        [{ validVerifyThmDecl with kind := .defnDecl }]
    ])
    (verifyRoots := [validVerifyThmName])

def wrongHeadVerifyRootPkg : PackageAuditInput :=
  mkSingleProofPkg
    (mkAlignedModule topicProofModName .proof [cleanProofThmDecl])
    (extraMods := [
      mkAlignedModule topicVerifyModName .verify
        [{ validVerifyThmDecl with
            type := .const SymName.trueName, value? := some (.const SymName.trueIntroName) }]
    ])
    (verifyRoots := [validVerifyThmName])

theorem verifyRoot_header_rejected :
    auditAndReplayPackage defaultUnconditionalConfig nonTheoremVerifyRootPkg =
      .error (.invalidVerifyRoot validVerifyThmName "verify root must be a theorem") ∧
    auditAndReplayPackage defaultUnconditionalConfig wrongHeadVerifyRootPkg =
      .error (.invalidVerifyRoot validVerifyThmName
        "verify root must have VerificationResult type") :=
  ⟨rfl, rfl⟩

/-- A theory dependency hidden two aliases deep (`Spec` alias of a `Defs` alias) is still found. -/
def specAliasName : SymName := SymName.ofList ["Topic", "Spec", "claimAlias2"]

def deepAliasLeakPkg : PackageAuditInput := {
  baseEnv := standardBaseDecls
  modules := [
    mkAlignedModule topicTheoryModName .theory [theoryClaimTypeDecl],
    mkAlignedModule topicDefsModName .defsExempt [defsAliasDecl],
    mkAlignedModule topicSpecModName .spec
      [{ defsAliasDecl with
          name := specAliasName, value? := some (.const defsAliasName),
          all := [specAliasName], originModule := topicSpecModName }],
    mkAlignedModule topicVerifyModName .verify
      [{ aliasLeakVerifyDecl with
          type := .app (.const SymName.verificationResultName) (.const specAliasName)
          value? := some (.app (.app (.const verificationResultMkName) (.const specAliasName))
            (.const SymName.trueIntroName)) }]
  ]
  verifyRoots := [validVerifyThmName]
}

theorem deepAlias_statementLeak_rejected :
    auditAndReplayPackage defaultUnconditionalConfig deepAliasLeakPkg =
      .error (.statementTheoryLeak validVerifyThmName theoryClaimTypeName topicTheoryModName) :=
  rfl

/-- More lexer edge cases: nested block comments, a doc-comment opener, `''` tokens, and string gaps. -/
theorem sourceScanner_more_lexer_edges :
    scanProofSource "/- a /- b -/ debug.skipKernelTC -/ theorem t : True := trivial" = .ok () ∧
    scanProofSource "/- a /- b -/ -/ set_option debug.skipKernelTC true" =
      .error (.forbiddenSourceOption topicProofModName "debug.skipKernelTC") ∧
    scanProofSource "def s := \"a\\\\\"\nset_option debug.skipKernelTC true" =
      .error (.forbiddenSourceOption topicProofModName "debug.skipKernelTC") ∧
    scanProofSource "def x' := 1 -- it's \"quoted\ntheorem t : True := trivial" = .ok () ∧
    scanProofSource "theorem t : True := by\n  first\n  | native_decide\n  | trivial" =
      .error (.forbiddenSourceOption topicProofModName "native_decide/decide +native") ∧
    scanProofSource "/- unterminated" =
      .error (.unsupportedSourceLexing topicProofModName
        "unterminated string, char literal, block comment, or escaped identifier") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.ReplayKeyAndTamperAuditProtoTests
