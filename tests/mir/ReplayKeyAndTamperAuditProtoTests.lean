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

end Anneal.ReplayKeyAndTamperAuditProtoTests
