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
5. Pass-`A1` regressions: guillemet-in-hole & backtick raw-string lexer desyncs, `_root_.`-qualified
   native reduction tokens (unconditional even under `--provisional`), `Defs` extension hardening,
   `.test` module closure & foreign-axiom enforcement, provisional `._native.*` `@Eq Bool` type-shape
   enforcement, dependency-ordered clean-env replay (`replayCleanEnvOrdered`) & cycle rejection,
   per-root `VerifyItemStatus` isolation in mixed packages, `closureFuel` liveness proofs, structural
   validation gaps, and Lean 4.34.1 `finalizeImport` `subsumesInfo` theorem body-swap model.
6. Pass-`B2` regressions: name-only stdlib trust (`Std.*`/`Init.*`), claimed extension origins,
   `localCommandElabEntry` flag bypass, numeric-prefix token glue, foreign imports, kernel-refuted
   provisional native axioms, and `itemReports` root coverage.
7. Pass-`A2` regressions: Lean 4.34.1 numeric-literal raw-string desyncs (`0x1r"\"`, `0b1r"\"`,
   `0o7r"\"`, `1_0r"\"`, `1e+0r"\"`), positional `DecideConfig` bypasses without token `native`,
   `Trusted.*` & `Lean.*` package-module trust, `Defs` foreign `default_instance`/`scoped_instance`/
   `coe` targets & foreign `instanceEntry` decls, mathematical import acyclicity & role-direction
   stratification (`auditAndReplayPackage_imports_sound`), `private import Init`, mixed
   `provisionalNativeConditional` status preservation + completeness, `cleanNonWorkspace`
   cross-item cache poisoning (`verifyAudit` L644–670), and `.theory`/`.test` claim-root bans.
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

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.replayCleanEnvOrdered_preserves_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms replayCleanEnvOrdered_preserves_sound

/-- info: 'Anneal.ReplayKeyAndTamperAuditPrototype.replayCleanEnvOrdered_contains_decl' depends on axioms: [propext] -/
#guard_msgs in #print axioms replayCleanEnvOrdered_contains_decl

/-- info: 'Anneal.ReplayKeyAndTamperAuditPrototype.walkGraph_never_exhausts_fuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms walkGraph_never_exhausts_fuel

/-- info: 'Anneal.ReplayKeyAndTamperAuditPrototype.closureExpand_never_exhausts_fuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms closureExpand_never_exhausts_fuel

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.walkStatementOrigins_never_exhausts_fuel' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms walkStatementOrigins_never_exhausts_fuel

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.validInventory_rec_all_targets_induct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms validInventory_rec_all_targets_induct

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.auditAndReplayPackage_modules_nodup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms auditAndReplayPackage_modules_nodup

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.auditAndReplayPackage_item_status_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms auditAndReplayPackage_item_status_sound

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.auditAndReplayPackage_test_closures_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms auditAndReplayPackage_test_closures_clean

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.passA1_lexer_and_root_qualification_hardened' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms passA1_lexer_and_root_qualification_hardened

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.passA1_defsExempt_cannot_bypass_hooks_macros_reducibility_or_init_shadow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms passA1_defsExempt_cannot_bypass_hooks_macros_reducibility_or_init_shadow

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.passA1_test_module_closures_and_axioms_hardened' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms passA1_test_module_closures_and_axioms_hardened

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.passA1_provisional_native_rejects_false_type' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms passA1_provisional_native_rejects_false_type

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.passA1_dependency_ordered_replay_accepts_ooo_and_rejects_cycles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms passA1_dependency_ordered_replay_accepts_ooo_and_rejects_cycles

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.passA1_mixed_package_per_item_status_and_isolation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms passA1_mixed_package_per_item_status_and_isolation

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.passA1_structural_validation_gaps_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms passA1_structural_validation_gaps_closed

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.finalizeImport_subsumes_body_swap_bypass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms finalizeImport_subsumes_body_swap_bypass

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

/-! ## Section 5: Pass-`A1` Regression Suite (Lexer, `Defs` Hooks, `.test` Closures, Native Shape, Ordered Replay, Per-Item Status, Liveness) -/

example := passA1_lexer_and_root_qualification_hardened
example := passA1_defsExempt_cannot_bypass_hooks_macros_reducibility_or_init_shadow
example := passA1_test_module_closures_and_axioms_hardened
example := passA1_provisional_native_rejects_false_type
example := passA1_dependency_ordered_replay_accepts_ooo_and_rejects_cycles
example := passA1_mixed_package_per_item_status_and_isolation
example := passA1_structural_validation_gaps_closed
example := finalizeImport_subsumes_body_swap_bypass
example := @walkGraph_never_exhausts_fuel
example := closureExpand_never_exhausts_fuel
example := walkStatementOrigins_never_exhausts_fuel

/-- Tightened `roleMatchesModuleName`: rejects `.anonymous`, `Topic.Proofs`, and `Topic.Defs` as `.spec`. -/
theorem roleMatchesModuleName_passA1_tightened :
    roleMatchesModuleName .spec .anonymous = false ∧
    roleMatchesModuleName .spec topicProofModName = false ∧
    roleMatchesModuleName .spec topicDefsModName = false ∧
    roleMatchesModuleName .spec topicSpecModName = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `Topic.Defs` rejects foreign-target instances (`V12`), `meta initialize` (`V10`), and `export` (`V15`). -/
def defsForeignInstPkg : PackageAuditInput := {
  baseEnv := standardBaseDecls
  modules := [
    mkAlignedModule topicDefsModName .defsExempt [defsBeforeDecl]
      (extEntries := [.instanceEntry (SymName.ofList ["Topic", "Defs", "badInst"])
        SymName.natName (SymName.ofList ["Init", "Prelude"]) false])
  ]
}

def defsMetaInitPkg : PackageAuditInput := {
  baseEnv := standardBaseDecls
  modules := [
    mkAlignedModule topicDefsModName .defsExempt [defsBeforeDecl]
      (extEntries := [.metaInitHook (SymName.ofList ["Topic", "Defs", "badMetaInit"])])
  ]
}

def defsExportAliasPkg : PackageAuditInput := {
  baseEnv := standardBaseDecls
  modules := [
    mkAlignedModule topicDefsModName .defsExempt [defsBeforeDecl]
      (extEntries := [.exportAlias (SymName.ofList ["Topic", "Defs", "expNatAdd"])
        SymName.natAddName (SymName.ofList ["Init", "Prelude"])])
  ]
}

theorem defsExempt_extra_vectors_rejected :
    auditAndReplayPackage defaultUnconditionalConfig defsForeignInstPkg =
      .error (.forbiddenInstanceOrCoe topicDefsModName "imported_instance"
        (SymName.ofList ["Topic", "Defs", "badInst"])) ∧
    auditAndReplayPackage defaultUnconditionalConfig defsMetaInitPkg =
      .error (.forbiddenInitOrCodegenHook topicDefsModName "meta_initialize"
        (SymName.ofList ["Topic", "Defs", "badMetaInit"])) ∧
    auditAndReplayPackage defaultUnconditionalConfig defsExportAliasPkg =
      .error (.forbiddenShadowingOrExport topicDefsModName
        (SymName.ofList ["Topic", "Defs", "expNatAdd"]) SymName.natAddName) :=
  ⟨rfl, rfl, rfl⟩

/-- Per-item `provisionalNative` status classification when a verify root reaches a valid `Proof.*._native.*` axiom. -/
def verifyProvMod : SymName := SymName.ofList ["Verify", "ProvItem"]
def verifyProvRoot : SymName := SymName.ofList ["Verify", "ProvItem", "verified"]

def provisionalVerifyPkg : PackageAuditInput := {
  baseEnv := standardBaseDecls
  modules := [
    mkAlignedModule pillarProofMod .proof [provisionalNativeAxDecl, provisionalNativeThmDecl],
    mkAlignedModule verifyProvMod .verify [
      { name := verifyProvRoot, kind := .thmDecl,
        type := .app (.const SymName.verificationResultName) (.natLit 2),
        value? := some (.app (.app (.const verificationResultMkName) (.natLit 2))
          (.app (.lam validNativeAxiomTypeExpr (.const SymName.trueIntroName))
            (.const pillarThmName))),
        hasValue := true, all := [verifyProvRoot], originModule := verifyProvMod }
    ] (imports := [{ module := pillarProofMod }])
  ]
  verifyRoots := [verifyProvRoot]
}

theorem provisionalVerifyItem_classified_provisionalNative :
    (auditAndReplayPackage provisionalConfig provisionalVerifyPkg).map
      (fun cert => cert.itemReports.map fun r => (r.root, r.status)) =
      .ok [(verifyProvRoot, .provisionalNative [provisionalNativeAxName])] :=
  rfl

/-- Extra Pass-`A1` lexer checks: `_root_.Lean.ofReduceNat`, `_root_.Lean.reduceBool`, and `s!"{«a»}"`. -/
theorem sourceScanner_passA1_extra_edges :
    scanProofSource "def t := _root_.Lean.ofReduceNat 0 0 rfl" =
      .error (.forbiddenSourceOption topicProofModName "native_decide/decide +native") ∧
    SourceScanner.scanSourceDefenseInDepth provisionalConfig topicProofModName .proof
      "def t := _root_.Lean.reduceBool true" =
      .error (.forbiddenSourceOption topicProofModName "native_decide/decide +native") ∧
    scanProofChars ("def s := s!\"{".toList ++ ['«', 'a', '»'] ++ "}\"".toList) =
      .error (.unsupportedSourceLexing topicProofModName
        "ambiguous char literal or string-interpolation hole") :=
  ⟨rfl, rfl, rfl⟩

/-! ## Section 6: Pass-`B2` Regression Suite (Name-Only Stdlib Trust, Claimed Origins, Numeric Token Glue, Foreign Imports, Report Coverage) -/

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.stdlibName_baseTrust_bypass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms stdlibName_baseTrust_bypass

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.extEntry_claimed_origin_and_flag_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms extEntry_claimed_origin_and_flag_rejected

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.auditAndReplayPackage_itemReports_cover_roots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms auditAndReplayPackage_itemReports_cover_roots

example := stdlibName_baseTrust_bypass
example := extEntry_claimed_origin_and_flag_rejected
example := sourceScanner_numeric_prefix_glue_rejected
example := foreignImport_rejected
example := pillar1_kernel_refuted_native_axiom_rejected

/-- Coverage instantiation: the baseline certificate reports exactly its one verify root. -/
theorem validBaselinePackage_itemReports_cover :
    ∃ cert,
      auditAndReplayPackage defaultUnconditionalConfig validBaselinePackage = .ok cert ∧
      cert.itemReports.map VerifyItemReport.root = [validVerifyThmName] := by
  cases h : auditAndReplayPackage defaultUnconditionalConfig validBaselinePackage with
  | error e =>
    have hok := validBaselinePackage_accepted
    rw [h] at hok
    cases hok
  | ok cert =>
    exact ⟨cert, rfl, auditAndReplayPackage_itemReports_cover_roots h⟩

/-- A stdlib-named package module is refused whatever role it claims (`Init.*` as well as `Std.*`). -/
def initNamedPkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl])
    (extraMods := [mkAlignedModule (SymName.ofList ["Init", "Evil"]) .foundation []])

def stdNamedProofRolePkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl])
    (extraMods := [mkAlignedModule (SymName.ofList ["Std", "Proofs"]) .proof []])

theorem stdlibNamed_package_modules_rejected :
    auditAndReplayPackage defaultUnconditionalConfig initNamedPkg =
      .error (.stdlibNamedPackageModule (SymName.ofList ["Init", "Evil"])) ∧
    auditAndReplayPackage defaultUnconditionalConfig stdNamedProofRolePkg =
      .error (.stdlibNamedPackageModule (SymName.ofList ["Std", "Proofs"])) :=
  ⟨rfl, rfl⟩

/--
Segment and numeric-prefix keyword matching edges: any dot-separated segment is matched (so a
trailing-dot or qualified form cannot hide a keyword), a digit-led run ending in a keyword is
matched, and identifiers that merely CONTAIN a keyword (`native1`, `my_decide`) are not.
-/
theorem sourceScanner_segment_matching_edges :
    SourceScanner.tokenHasKeyword "native_decide".toList "native_decide.".toList = true ∧
    SourceScanner.tokenHasKeyword "native_decide".toList "Foo.native_decide.bar".toList = true ∧
    SourceScanner.tokenHasKeyword "native_decide".toList "12native_decide".toList = true ∧
    SourceScanner.tokenHasKeyword "native_decide".toList "my_native_decide".toList = false ∧
    SourceScanner.tokenHasKeyword "native".toList "native1".toList = false ∧
    scanProofSource "def native1 := 1\ntheorem t : True := by decide" = .ok () ∧
    scanProofSource "def x := 3\ntheorem t : True := trivial" = .ok () ∧
    scanProofSource "theorem t : True := by iterate 1bv_decide" =
      .error (.forbiddenSourceOption topicProofModName "native_decide/decide +native") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A reducibility override or instance attribute on a genuinely LOCAL target is still accepted. -/
def localTargetExtPkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
    (extEntries := [
      .instanceEntry (SymName.ofList ["Topic", "Proofs", "instLocal"]) cleanProofThmName
        topicProofModName false,
      .reducibilityOverride cleanProofThmName topicProofModName "irreducible"]))

theorem extEntry_local_targets_accepted :
    (auditAndReplayPackage defaultUnconditionalConfig localTargetExtPkg).isOk = true :=
  rfl

/-! ## Section 7: Pass-`A2` Regression Suite (Numeric-Raw Lexer, Positional `DecideConfig`, `Trusted.*`/`Lean.*`, `Defs` Foreign Targets, Import Acyclicity/Stratification, Mixed Status, `cleanNonWorkspace` Cache Poisoning) -/

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.auditAndReplayPackage_item_status_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms auditAndReplayPackage_item_status_complete

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.auditAndReplayPackage_imports_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms auditAndReplayPackage_imports_sound

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.passA2_numeric_raw_string_and_decide_config_hardened' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms passA2_numeric_raw_string_and_decide_config_hardened

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.trustedName_baseTrust_bypass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms trustedName_baseTrust_bypass

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.passA2_defs_and_proof_ext_foreign_targets_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms passA2_defs_and_proof_ext_foreign_targets_rejected

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.passA2_import_cycles_role_direction_and_private_init_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms passA2_import_cycles_role_direction_and_private_init_rejected

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.passA2_mixed_provisional_and_assumptions_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms passA2_mixed_provisional_and_assumptions_preserved

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.cleanNonWorkspace_cache_poisoning_bypass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms cleanNonWorkspace_cache_poisoning_bypass

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.passA2_claim_root_in_theory_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms passA2_claim_root_in_theory_rejected

example := passA2_numeric_raw_string_and_decide_config_hardened
example := trustedName_baseTrust_bypass
example := passA2_defs_and_proof_ext_foreign_targets_rejected
example := passA2_import_cycles_role_direction_and_private_init_rejected
example := passA2_mixed_provisional_and_assumptions_preserved
example := cleanNonWorkspace_cache_poisoning_bypass
example := passA2_claim_root_in_theory_rejected

/-- End-to-end instantiation of `auditAndReplayPackage_imports_sound` on `validBaselinePackage`:
every module in the baseline package is non-stdlib, non-trusted, role-stratified, and strictly acyclic. -/
theorem validBaselinePackage_imports_acyclic_and_stratified :
    ∀ inv ∈ validBaselinePackage.modules,
      ¬ SymName.isStdlibModule inv.moduleName ∧
      ¬ SymName.isTrustedModule inv.moduleName ∧
      ¬ ImportReaches validBaselinePackage inv.moduleName inv.moduleName := by
  cases h : auditAndReplayPackage defaultUnconditionalConfig validBaselinePackage with
  | error e =>
    have hok := validBaselinePackage_accepted
    rw [h] at hok; cases hok
  | ok cert =>
    intro inv hinv
    obtain ⟨h1, h2, _, h3⟩ := auditAndReplayPackage_imports_sound h inv hinv
    exact ⟨h1, h2, h3⟩

/-- 3-hop import cycle `A → B → C → A`, `.spec → .proof`, `.defsExempt → .theory`, and claim root in `.test`. -/
def triModA : SymName := SymName.ofList ["Topic", "Proofs", "TriA"]
def triModB : SymName := SymName.ofList ["Topic", "Proofs", "TriB"]
def triModC : SymName := SymName.ofList ["Topic", "Proofs", "TriC"]

def triCycleImportPkg : PackageAuditInput := {
  baseEnv := standardBaseDecls
  modules := [
    mkAlignedModule triModA .proof [] (imports := [{ module := triModB }]),
    mkAlignedModule triModB .proof [] (imports := [{ module := triModC }]),
    mkAlignedModule triModC .proof [] (imports := [{ module := triModA }])
  ]
}

def specImportsProofPkg : PackageAuditInput := {
  baseEnv := standardBaseDecls
  modules := [
    mkAlignedModule topicProofModName .proof [cleanProofThmDecl],
    mkAlignedModule topicSpecModName .spec [] (imports := [{ module := topicProofModName }])
  ]
}

def defsImportsTheoryPkg : PackageAuditInput := {
  baseEnv := standardBaseDecls
  modules := [
    mkAlignedModule topicTheoryModName .theory [theoryClaimTypeDecl],
    mkAlignedModule topicDefsModName .defsExempt [defsBeforeDecl]
      (imports := [{ module := topicTheoryModName }])
  ]
}

def testClaimRootName : SymName := SymName.ofList ["Topic", "Tests", "claimInTest"]
def testClaimRootPkg : PackageAuditInput := {
  baseEnv := standardBaseDecls
  modules := [mkAlignedModule topicTestsModName .test [{
    name := testClaimRootName, kind := .thmDecl, type := .const SymName.trueName,
    value? := some (.const SymName.trueIntroName), hasValue := true,
    all := [testClaimRootName], originModule := topicTestsModName
  }]]
  claimRoots := [testClaimRootName]
}

theorem passA2_extra_import_and_claim_regressions :
    auditAndReplayPackage defaultUnconditionalConfig triCycleImportPkg =
      .error (.importCycle triModA triModB) ∧
    auditAndReplayPackage defaultUnconditionalConfig specImportsProofPkg =
      .error (.forbiddenImportDirection topicSpecModName "spec" topicProofModName "proof") ∧
    auditAndReplayPackage defaultUnconditionalConfig defsImportsTheoryPkg =
      .error (.forbiddenImportDirection topicDefsModName "defsExempt" topicTheoryModName "theory") ∧
    auditAndReplayPackage defaultUnconditionalConfig testClaimRootPkg =
      .error (.invalidVerifyRoot testClaimRootName
        "claim root cannot reside in theory or test module") :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Extra Pass-`A2` numeric-literal lexer edges: scientific notation `1e+0r"\"` & hex+char `0x1'"'`. -/
theorem passA2_extra_lexer_edges :
    scanProofSource "def x := 1e+0r\"\\\"\nset_option debug.skipKernelTC true\n-- \"" =
      .error (.forbiddenSourceOption topicProofModName "debug.skipKernelTC") ∧
    scanProofSource "def x := 0x1'\"'\nset_option debug.skipKernelTC true\n-- \"" =
      .error (.forbiddenSourceOption topicProofModName "debug.skipKernelTC") ∧
    scanProofSource "def x := 1e-2\ndef y := 0b101\ndef z := 0o755" = .ok () :=
  ⟨rfl, rfl, rfl⟩

/-! ## Section 8: Pass-`B3` Regression Suite (Unlisted Verify Modules, `Lean.*` Imports, `bv_decide` Family, References Outside the Import Closure) -/

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.auditAndReplayPackage_verify_modules_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms auditAndReplayPackage_verify_modules_covered

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.importReachesAux_true_sound' depends on axioms: [propext]
-/
#guard_msgs in #print axioms importReachesAux_true_sound

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.importClosureCheck_exact' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms importClosureCheck_exact

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.auditAndReplayPackage_references_within_imports' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms auditAndReplayPackage_references_within_imports

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.importReaches_statementSide' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms importReaches_statementSide

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.auditAndReplayPackage_statement_side_dependencies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms auditAndReplayPackage_statement_side_dependencies

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.cleanNonWorkspace_cache_poisoning_bypass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms cleanNonWorkspace_cache_poisoning_bypass

example := unlistedVerifyModule_rejected
example := leanMetaImport_rejected
example := sourceScanner_bv_decide_family_rejected
example := reference_outside_import_closure_rejected

/-- Coverage instantiation: every `.verify` module of the baseline package has its root listed. -/
theorem validBaselinePackage_verify_modules_covered :
    ∀ inv ∈ validBaselinePackage.modules, inv.role = .verify →
      SymName.str inv.moduleName "verified" ∈ validBaselinePackage.verifyRoots := by
  cases h : auditAndReplayPackage defaultUnconditionalConfig validBaselinePackage with
  | error e =>
    have hok := validBaselinePackage_accepted
    rw [h] at hok
    cases hok
  | ok cert =>
    exact auditAndReplayPackage_verify_modules_covered h

/-- An unlisted `CrateVerify` rollup module is refused in the same way as an unlisted `Verify.*` module. -/
def crateVerifyModName : SymName := SymName.mkSimple "CrateVerify"
def crateVerifyRootName : SymName := SymName.ofList ["CrateVerify", "verified"]

def unlistedCrateVerifyPkg : PackageAuditInput :=
  mkSingleProofPkg
    (mkAlignedModule topicProofModName .proof [cleanProofThmDecl])
    (extraMods := [
      mkAlignedModule crateVerifyModName .verify
        [{ validVerifyThmDecl with
            name := crateVerifyRootName, all := [crateVerifyRootName],
            originModule := crateVerifyModName }]
        (imports := [{ module := topicProofModName }])
    ])

theorem unlistedCrateVerifyModule_rejected :
    auditAndReplayPackage defaultUnconditionalConfig unlistedCrateVerifyPkg =
      .error (.invalidVerifyRoot crateVerifyRootName
        "verify module root is not listed in verifyRoots") ∧
    (auditAndReplayPackage defaultUnconditionalConfig
      { unlistedCrateVerifyPkg with verifyRoots := [crateVerifyRootName] }).isOk = true :=
  ⟨rfl, rfl⟩

/-- `?` / `!` variant suffixes are matched as the base keyword; longer identifiers are not. -/
theorem sourceScanner_variant_suffix_edges :
    SourceScanner.tokenHasKeyword "bv_decide".toList "bv_decide?".toList = true ∧
    SourceScanner.tokenHasKeyword "native_decide".toList "native_decide!".toList = true ∧
    SourceScanner.tokenHasKeyword "decide".toList "decide?".toList = true ∧
    SourceScanner.tokenHasKeyword "bv_check".toList "1bv_check".toList = true ∧
    SourceScanner.tokenHasKeyword "decide".toList "decidable?".toList = false ∧
    SourceScanner.tokenHasKeyword "bv_decide".toList "my_bv_decide?".toList = false ∧
    scanProofSource "theorem t (b : Bool) : b = b := by cases b <;> rfl" = .ok () ∧
    scanProofSource "theorem t : True := by grind => bv_decide" =
      .error (.forbiddenSourceOption topicProofModName "native_decide/decide +native") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
The undeclared-import variant of the verify item: `Verify.Topic.verified` mentions
`Topic.Proofs.cleanLemma`, and the package is accepted only when `Verify.Topic` declares the import.
A `.theory` module mentioning a `.proof` lemma is refused whether or not it declares the edge.
-/
def verifyNoImportPkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl])
    (extraMods := [mkAlignedModule topicVerifyModName .verify [validVerifyThmDecl]])
    (verifyRoots := [validVerifyThmName])

def verifyWithImportPkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl])
    (extraMods := [mkAlignedModule topicVerifyModName .verify [validVerifyThmDecl]
      (imports := [{ module := topicProofModName }])])
    (verifyRoots := [validVerifyThmName])

def theoryMentionsProofName : SymName := SymName.ofList ["Anneal", "TheoryHelper", "mentionsProof"]
def theoryMentionsProofDecl : ConstantRecord := {
  name := theoryMentionsProofName, kind := .thmDecl, type := .const SymName.trueName,
  value? := some (.const cleanProofThmName), hasValue := true,
  all := [theoryMentionsProofName], originModule := topicTheoryModName }

def theoryMentionsProofPkg (declared : Bool) : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl])
    (extraMods := [mkAlignedModule topicTheoryModName .theory [theoryMentionsProofDecl]
      (imports := if declared then [{ module := topicProofModName }] else [])])

theorem reference_import_closure_extra_regressions :
    auditAndReplayPackage defaultUnconditionalConfig verifyNoImportPkg =
      .error (.referenceOutsideImportClosure topicVerifyModName validVerifyThmName
        cleanProofThmName topicProofModName) ∧
    (auditAndReplayPackage defaultUnconditionalConfig verifyWithImportPkg).isOk = true ∧
    auditAndReplayPackage defaultUnconditionalConfig (theoryMentionsProofPkg false) =
      .error (.referenceOutsideImportClosure topicTheoryModName theoryMentionsProofName
        cleanProofThmName topicProofModName) ∧
    auditAndReplayPackage defaultUnconditionalConfig (theoryMentionsProofPkg true) =
      .error (.forbiddenImportDirection topicTheoryModName "theory" topicProofModName "proof") :=
  ⟨rfl, rfl, rfl, rfl⟩

/--
Transitive imports are honoured: the baseline `Verify.Topic` imports only `Topic.Proofs`, which
imports `Anneal.TheoryHelper`, and the search answers exactly per `importClosureCheck_exact`.
-/
theorem baseline_import_closure_search :
    importReachesAux validBaselinePackage topicTheoryModName
      (importGraphFuel validBaselinePackage + 1) [topicProofModName] [] = true ∧
    importReachesAux validBaselinePackage topicVerifyModName
      (importGraphFuel validBaselinePackage + 1) [topicProofModName] [] = false ∧
    ¬ ImportReaches validBaselinePackage topicProofModName topicVerifyModName := by
  refine ⟨rfl, rfl, fun hreach => ?_⟩
  have hex : ∃ p ∈ [topicProofModName],
      p = topicVerifyModName ∨ ImportReaches validBaselinePackage p topicVerifyModName :=
    ⟨topicProofModName, List.mem_cons_self, Or.inr hreach⟩
  have htrue := (importClosureCheck_exact validBaselinePackage topicVerifyModName
    [topicProofModName]).mpr hex
  have hfalse : importReachesAux validBaselinePackage topicVerifyModName
      (importGraphFuel validBaselinePackage + [topicProofModName].length)
      [topicProofModName] [] = false := rfl
  rw [hfalse] at htrue
  cases htrue

/--
Dependency stratification instantiated on an accepted package: `Topic.Defs` (`.defsExempt`) of the
baseline never mentions a `.proof` / `.theory` / `.verify` / `.test` declaration.
-/
theorem validBaselinePackage_statement_side_dependencies :
    ∀ inv ∈ validBaselinePackage.modules, isStatementSideRole inv.role = true →
      ∀ ci ∈ inv.constants, ∀ edges, ConstantRecord.declarationEdges ci = .ok edges →
        ∀ dep ∈ edges, ∀ target, moduleOfConst? validBaselinePackage dep = some target →
          isStatementSideRole target.role = true := by
  cases h : auditAndReplayPackage defaultUnconditionalConfig validBaselinePackage with
  | error e =>
    have hok := validBaselinePackage_accepted
    rw [h] at hok
    cases hok
  | ok cert =>
    exact auditAndReplayPackage_statement_side_dependencies h

/-! ## Section 9: Pass-`A3` Regression Suite (Extension Import-Closure & Prefix-Collision Hijack, Duplicate Roots, Bare `Verify` & Role Uniqueness, `Lean.*` Non-Foundation, Opaque-Wrapped Provisional Refutation, `requireSources`, & `by_elab`/`run_tac`/`run_cmd`) -/

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.roleMatchesModuleName_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms roleMatchesModuleName_unique

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.auditAndReplayPackage_no_lean_modules' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms auditAndReplayPackage_no_lean_modules

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.auditAndReplayPackage_roots_nodup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms auditAndReplayPackage_roots_nodup

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.auditAndReplayPackage_sources_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms auditAndReplayPackage_sources_covered

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.auditAndReplayPackage_ext_refs_within_imports' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms auditAndReplayPackage_ext_refs_within_imports

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.auditAndReplayPackage_reserved_origins_within_imports' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms auditAndReplayPackage_reserved_origins_within_imports

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.passA3_ext_entry_import_closure_and_prefix_collision_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms passA3_ext_entry_import_closure_and_prefix_collision_rejected

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.passA3_duplicate_roots_and_bare_verify_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms passA3_duplicate_roots_and_bare_verify_rejected

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.passA3_role_uniqueness_and_lean_not_foundation' depends on axioms: [propext]
-/
#guard_msgs in #print axioms passA3_role_uniqueness_and_lean_not_foundation

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.passA3_opaque_wrapped_native_axiom_refuted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms passA3_opaque_wrapped_native_axiom_refuted

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.passA3_requireSources_and_meta_exec_scanner_hardened' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms passA3_requireSources_and_meta_exec_scanner_hardened

example := passA3_ext_entry_import_closure_and_prefix_collision_rejected
example := passA3_duplicate_roots_and_bare_verify_rejected
example := passA3_role_uniqueness_and_lean_not_foundation
example := passA3_opaque_wrapped_native_axiom_refuted
example := passA3_requireSources_and_meta_exec_scanner_hardened

/-- Instantiation on `validBaselinePackage`: roots are duplicate-free, no `Lean.*` modules exist,
and every extension entry respects local ownership and statement-side stratification. -/
theorem validBaselinePackage_passA3_guarantees :
    validBaselinePackage.verifyRoots.Nodup ∧
    validBaselinePackage.claimRoots.Nodup ∧
    (∀ inv ∈ validBaselinePackage.modules, ¬ SymName.isLeanCompilerModule inv.moduleName) ∧
    (∀ inv ∈ validBaselinePackage.modules, ∀ ext ∈ inv.extEntries,
      ∀ dep ∈ ext.referencedConstants, ∀ target, moduleOfConst? validBaselinePackage dep = some target →
        isStatementSideRole inv.role = true → isStatementSideRole target.role = true) := by
  cases h : auditAndReplayPackage defaultUnconditionalConfig validBaselinePackage with
  | error e =>
    have hok := validBaselinePackage_accepted
    rw [h] at hok
    cases hok
  | ok cert =>
    obtain ⟨hvr, hcr⟩ := auditAndReplayPackage_roots_nodup h
    refine ⟨hvr, hcr, auditAndReplayPackage_no_lean_modules h, ?_⟩
    intro inv hinv ext hext dep hdep target htarget hst
    exact ((auditAndReplayPackage_ext_refs_within_imports h inv hinv ext hext).2.1
      dep hdep target htarget).2 hst

/-- Instantiation of `auditAndReplayPackage_sources_covered` on `validBaselinePackageWithSources`. -/
theorem validBaselinePackageWithSources_all_scanned :
    ∀ inv ∈ validBaselinePackageWithSources.modules, ∃ src, inv.sourceText? = some src ∧
      SourceScanner.scanSourceDefenseInDepth requireSourcesConfig inv.moduleName inv.role src = .ok () := by
  cases h : auditAndReplayPackage requireSourcesConfig validBaselinePackageWithSources with
  | error e =>
    have hok := passA3_requireSources_and_meta_exec_scanner_hardened.2.1
    rw [h] at hok
    cases hok
  | ok cert =>
    exact auditAndReplayPackage_sources_covered h rfl

/-- Opaque lambda applied to opaque `Bool.false` is refuted by `whnfAllowOpaque` β-reduction! -/
def opaqueBoolIdName : SymName := SymName.ofList ["Proof", "Native", "opaqueBoolId"]
def opaqueBoolIdDecl : ConstantRecord := {
  name := opaqueBoolIdName, kind := .opaqueDecl,
  type := .forallE (.const SymName.boolName) (.const SymName.boolName),
  value? := some (.lam (.const SymName.boolName) (.bvar 0)), hasValue := true,
  all := [opaqueBoolIdName], originModule := pillarProofMod
}
def opaqueBetaRefutedAxName : SymName :=
  SymName.ofList ["Proof", "Native", "bad", "_native", "decide", "ax_opaque_beta"]
def opaqueBetaRefutedPkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule pillarProofMod .proof [
    opaqueFalseBoolDecl,
    opaqueBoolIdDecl,
    { name := opaqueBetaRefutedAxName, kind := .axiomDecl,
      type := .app (.app (.const SymName.eqBoolName)
        (.app (.const opaqueBoolIdName) (.const opaqueFalseBoolName)))
        (.const SymName.boolTrueName),
      originModule := pillarProofMod }
  ])

/-- Additional Pass-`A3` edges: opaque β-reduction refutation, hybrid roles, and glued/guillemet `by_elab`/`run_tac`. -/
theorem passA3_extra_edges :
    auditAndReplayPackage provisionalConfig opaqueBetaRefutedPkg =
      .error (.invalidNativeAxiomType opaqueBetaRefutedAxName opaqueBetaRefutedAxName) ∧
    roleMatchesModuleName .proof (SymName.ofList ["Tests", "Proofs"]) = false ∧
    roleMatchesModuleName .test (SymName.ofList ["Tests", "Proofs"]) = false ∧
    roleMatchesModuleName .defsExempt (SymName.ofList ["Topic", "Tests", "Defs"]) = false ∧
    roleMatchesModuleName .test (SymName.ofList ["Topic", "Tests", "Defs"]) = true ∧
    roleMatchesModuleName .proof (SymName.ofList ["Topic", "Proofs", "Defs"]) = true ∧
    roleMatchesModuleName .defsExempt (SymName.ofList ["Topic", "Proofs", "Defs"]) = false ∧
    scanProofSource "theorem t : True := by iterate 1run_tac pure ()" =
      .error (.forbiddenSourceOption topicProofModName "by_elab/run_tac/run_cmd") ∧
    scanProofSource "theorem t : True := «by_elab» return mkConst ``True.intro" =
      .error (.forbiddenSourceOption topicProofModName "by_elab/run_tac/run_cmd") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 10: Pass-`B4` Regression Suite (`run_elab`, Source Withholding Under the Default Configuration) -/

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.sourceScanner_run_elab_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms sourceScanner_run_elab_rejected

/--
info: 'Anneal.ReplayKeyAndTamperAuditPrototype.source_withholding_needs_requireSources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms source_withholding_needs_requireSources

example := sourceScanner_run_elab_rejected
example := source_withholding_needs_requireSources

/--
All five metaprogramming execution keywords are rejected in every role, including under
`--provisional` in a `.proof` module; identifiers that merely start with them are not.
-/
theorem sourceScanner_meta_exec_edges :
    SourceScanner.scanSourceDefenseInDepth provisionalConfig topicProofModName .proof
        "run_elab pure ()" =
      .error (.forbiddenSourceOption topicProofModName "by_elab/run_tac/run_cmd") ∧
    SourceScanner.scanSourceDefenseInDepth defaultUnconditionalConfig topicSpecModName .spec
        "run_cmd pure ()" =
      .error (.forbiddenSourceOption topicSpecModName "by_elab/run_tac/run_cmd") ∧
    scanProofSource "-- run_elab in a comment\ndef s := \"run_meta in a string\"" = .ok () ∧
    scanProofSource "def run_elab_count : Nat := 0" = .ok () ∧
    scanProofSource "def x := Nat.run_elab" =
      .error (.forbiddenSourceOption topicProofModName "by_elab/run_tac/run_cmd") :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end Anneal.ReplayKeyAndTamperAuditProtoTests
