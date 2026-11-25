-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto

/-!
# Verification Suite for `Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto`

1. **Cross-Language Wire Contract & Disjointness (§1)**:
   Asserts literal wire tables, ranks `3..6`, `VacuityClass` mappings, round-trips,
   near-miss rejection, and disjointness from `SpecBoundaryGuardClass` (`0..2`) and
   `PropertyClassTag` (`0..11`).
2. **Pillar 1 — `lean4#16717` Forged-Inductive Replay (§2)**:
   Exercises pre-`#16717` exploit witnesses (`FakeFalse`, forged `numIndices`/`isRec`),
   all 12 malformed variant rejections, valid `Unit`/`Nat` replay acceptance, and
   `hardenedInductiveReplay_sound`.
3. **Pillar 2 — `grmf` cl/1029226310 Sharding & `--orphan-only` (§3)**:
   Exercises `shardPartitionCheck_iff_valid`, all partition failure modes, 3-hop
   cross-shard chain `M1 -> M2 -> M3 -> badAxiom`, diamond/cycle dependency graphs,
   and `shardAxiomUnion_sound`.
4. **Pillar 3 — Four Peer-Verifier Spec Guards (§4)**:
   Exercises soundness-collapse and restoration theorems for Guards 3, 4, 5, 6a, and 6b.
5. **Kernel Axiom & Hygiene Audit (§5)**:
   `#guard_msgs in #print axioms` on flagship theorems plus a compile-time `run_cmd`
   environment audit verifying every declaration in both modules is safe, total,
   `sorry`-free, and depends strictly on `{propext, Classical.choice, Quot.sound}`.
-/

namespace Anneal.Proto.InductiveReplayAndPeerSpecGuardsProtoTests

open Anneal.SpecRealizability
open Anneal.SpecBoundaryGuards
open Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto

/-! ## 1. Cross-Language Wire Contract & Disjointness -/

theorem peerGuard_wire_table_exact :
    PeerSpecGuardClass.all.map
        (fun g => (g.rank, g.guardId, g.canonicalName, g.toVacuityClass.canonicalName)) =
      [(3, "unsatisfiable_extern_ensures", "UnsatisfiableExternEnsures", "SpecViolation"),
        (4, "fndef_ghost_token_coercion", "FnDefGhostTokenCoercion", "SpecViolation"),
        (5, "external_type_drop_omission", "ExternalTypeDropOmission", "SpecViolation"),
        (6, "assumption_polarity_and_struct_sealing",
          "AssumptionPolarityAndStructSealing", "TrivialPostcondition")] :=
  PeerSpecGuardClass.wire_table

theorem peerGuard_roundtrips :
    PeerSpecGuardClass.all.all (fun g =>
      PeerSpecGuardClass.ofGuardId? g.guardId == some g &&
        PeerSpecGuardClass.ofCanonicalName? g.canonicalName == some g &&
        PeerSpecGuardClass.ofRank? g.rank == some g) = true := by
  decide

theorem peerGuard_rejects_baseline_and_out_of_range_ranks :
    [0, 1, 2, 7, 8, 99].all (fun n => (PeerSpecGuardClass.ofRank? n).isNone) = true ∧
    ["", "entry_point_requires", "fixed_width_ghost_length", "error_branch_wildcard",
      "UnsatisfiableExternEnsures", "arithmetic_overflow"].all
        (fun s => (PeerSpecGuardClass.ofGuardId? s).isNone) = true := by
  decide

theorem peerGuard_disjoint_from_baseline_guards_and_properties :
    PeerSpecGuardClass.all.all (fun p =>
      SpecBoundaryGuardClass.all.all (fun b =>
        p.rank != b.rank && p.guardId != b.guardId && p.canonicalName != b.canonicalName) &&
      PropertyClassTag.all.all (fun c => p.guardId != c.asStr)) = true := by
  decide

theorem inductiveReplayViolationCode_table_exact :
    InductiveReplayViolationCode.all.map InductiveReplayViolationCode.asStr =
      ["key_mismatch", "self_not_in_all", "duplicate_in_all", "non_induct_in_all",
        "mutual_metadata_mismatch", "duplicate_in_ctors", "non_ctor_in_ctors",
        "ctor_induct_mismatch", "ctor_cidx_mismatch",
        "dangling_ctor_not_listed_in_induct", "indices_mismatch", "is_rec_mismatch",
        "recursor_mismatch"] :=
  rfl

theorem shardAuditViolationCode_table_exact :
    ShardAuditViolationCode.all.map ShardAuditViolationCode.asStr =
      ["empty_shard_list", "empty_shard", "duplicate_module_in_shard",
        "overlapping_shards", "unregistered_module_in_shard",
        "uncovered_registered_module", "unregistered_on_disk_orphan",
        "disallowed_transitive_axiom", "missing_dependency_decl",
        "module_name_collision", "cross_shard_duplicate_conflict"] :=
  rfl

theorem peerGuardViolationCode_table_exact :
    PeerGuardViolationCode.all.map (fun c => (c.asStr, c.guardClass.guardId)) =
      [("unsatisfiable_extern_ensures", "unsatisfiable_extern_ensures"),
        ("fndef_ghost_token_coercion", "fndef_ghost_token_coercion"),
        ("external_type_drop_omission", "external_type_drop_omission"),
        ("external_type_body_with_drop", "external_type_drop_omission"),
        ("assumption_positive_polarity", "assumption_polarity_and_struct_sealing"),
        ("unsealed_invariant_struct", "assumption_polarity_and_struct_sealing")] :=
  rfl

/-! ## 2. Pillar 1 — `lean4#16717` Forged-Inductive Replay Regression Tests -/

def validUnitAndNatMap : SimConstMap :=
  [("Unit", .induct unitInductVal),
   ("Unit.unit", .ctor unitCtorVal),
   ("Unit.rec", .recInfo unitRecVal),
   ("Nat", .induct natInductVal),
   ("Nat.zero", .ctor natZeroCtorVal),
   ("Nat.succ", .ctor natSuccCtorVal),
   ("Nat.rec", .recInfo natRecVal)]

/-- Kernel environment generated by replaying `validUnitAndNatMap` (`Unit` then `Nat`). -/
def validUnitAndNatKernelEnv : SimConstMap :=
  insertKernelOutput
    (insertKernelOutput [] { inducts := [unitInductVal], ctors := [unitCtorVal], recs := [unitRecVal] })
    { inducts := [natInductVal], ctors := [natZeroCtorVal, natSuccCtorVal], recs := [natRecVal] }

theorem validUnitAndNat_passes_hardened_and_wellFormed :
    hardenedInductiveReplay demoKernelOracle validUnitAndNatMap = .ok validUnitAndNatKernelEnv ∧
      InductiveReplayWellFormed validUnitAndNatMap validUnitAndNatKernelEnv ∧
      lookupConst validUnitAndNatKernelEnv "Nat.rec" = some (.recInfo natRecVal) := by
  have hOk : hardenedInductiveReplay demoKernelOracle validUnitAndNatMap =
      .ok validUnitAndNatKernelEnv := rfl
  exact ⟨hOk, hardenedInductiveReplay_sound hOk, rfl⟩

/-- The honest map also passes the (faithful) vulnerable 4.34.1 replay: hardening adds no
    false positives on well-formed inductive blocks. -/
theorem validUnitAndNat_passes_vulnerable :
    ∃ env, vulnerableInductiveReplay demoKernelOracle validUnitAndNatMap = .ok env :=
  ⟨_, rfl⟩

theorem all_thirteen_inductive_replay_violations_exercised :
    hasReplayViolation (checkStaticInductiveIntegrity malformedKeyMismatchMap) .keyMismatch = true ∧
    hasReplayViolation (checkStaticInductiveIntegrity fakeFalseExploitMap) .selfNotInAll = true ∧
    hasReplayViolation (checkStaticInductiveIntegrity malformedDupAllMap) .duplicateInAll = true ∧
    hasReplayViolation (checkStaticInductiveIntegrity malformedNonInductInAllMap) .nonInductInAll = true ∧
    hasReplayViolation (checkStaticInductiveIntegrity malformedMutualMetaMap) .mutualMetadataMismatch = true ∧
    hasReplayViolation (checkStaticInductiveIntegrity malformedDupCtorsMap) .duplicateInCtors = true ∧
    hasReplayViolation (checkStaticInductiveIntegrity malformedNonCtorInCtorsMap) .nonCtorInCtors = true ∧
    hasReplayViolation (checkStaticInductiveIntegrity malformedCtorInductMismatchMap) .ctorInductMismatch = true ∧
    hasReplayViolation (checkStaticInductiveIntegrity malformedCtorCidxMismatchMap) .ctorCidxMismatch = true ∧
    hasReplayViolation (checkStaticInductiveIntegrity malformedDanglingCtorMap) .danglingCtorNotListedInInduct = true ∧
    hasReplayViolation (checkPostponedInductives forgedMetadataExploitMap [("Nat", .induct natInductVal)]) .indicesMismatch = true ∧
    hasReplayViolation (checkPostponedInductives forgedMetadataExploitMap [("Nat", .induct natInductVal)]) .isRecMismatch = true ∧
    hasReplayViolation (checkPostponedRecursors forgedNatRecMap forgedMetadataKernelEnv) .recursorMismatch = true :=
  ⟨checkInductive_rejects_keyMismatch,
   checkInductive_rejects_selfNotInAll,
   checkInductive_rejects_duplicateInAll,
   checkInductive_rejects_nonInductInAll,
   checkInductive_rejects_mutualMetadataMismatch,
   checkInductive_rejects_duplicateInCtors,
   checkInductive_rejects_nonCtorInCtors,
   checkInductive_rejects_ctorInductMismatch,
   checkInductive_rejects_ctorCidxMismatch,
   checkInductive_rejects_danglingCtorNotListedInInduct,
   checkInductive_rejects_indicesMismatch,
   checkInductive_rejects_isRecMismatch,
   checkInductive_rejects_recursorMismatch⟩

/-! ## 3. Pillar 2 — `grmf` cl/1029226310 Sharding Regression Tests -/

theorem valid_eight_shard_partition_accepted :
    ShardPartitionValid
      ["Trusted", "Anneal.Core", "Anneal.RustcMir", "Anneal.PureLift",
        "Anneal.ParametricCore", "Anneal.AiPcc", "Examples.Smoke", "Tests.Smoke"]
      ["Trusted", "Anneal.Core", "Anneal.RustcMir", "Anneal.PureLift",
        "Anneal.ParametricCore", "Anneal.AiPcc", "Examples.Smoke", "Tests.Smoke"]
      [["Trusted"], ["Anneal.Core"], ["Anneal.RustcMir"], ["Anneal.PureLift"],
        ["Anneal.ParametricCore"], ["Anneal.AiPcc"], ["Examples.Smoke"], ["Tests.Smoke"]] :=
  (shardPartitionCheck_iff_valid _ _ _).mp rfl

theorem shard_partition_rejects_all_seven_malformed_shapes :
    (checkShardPartition ["A"] ["A"] []).any (·.code == .emptyShardList) = true ∧
    (checkShardPartition ["A"] ["A"] [["A"], []]).any (·.code == .emptyShard) = true ∧
    (checkShardPartition ["A"] ["A"] [["A", "A"]]).any (·.code == .duplicateModuleInShard) = true ∧
    (checkShardPartition ["A", "B"] ["A", "B"] [["A", "B"], ["B"]]).any (·.code == .overlappingShards) = true ∧
    (checkShardPartition ["A"] ["A"] [["A", "Ghost"]]).any (·.code == .unregisteredModuleInShard) = true ∧
    (checkShardPartition ["A", "B"] ["A", "B"] [["A"]]).any (·.code == .uncoveredRegisteredModule) = true ∧
    (checkShardPartition ["A"] ["A", "Orphan"] [["A"]]).any (·.code == .unregisteredOnDiskOrphan) = true := by
  decide

def diamondM1Top : DeclRecord :=
  { name := "M1.top", originMod := "M1", isAxiom := false,
    isUnsafeOrPartial := false, directDeps := ["M2.left", "M2.right"] }

def diamondM2Left : DeclRecord :=
  { name := "M2.left", originMod := "M2", isAxiom := false,
    isUnsafeOrPartial := false, directDeps := ["propext"] }

def diamondM2Right : DeclRecord :=
  { name := "M2.right", originMod := "M2", isAxiom := false,
    isUnsafeOrPartial := false, directDeps := ["propext"] }

def diamondPropext : DeclRecord :=
  { name := "propext", originMod := "Init", isAxiom := true,
    isUnsafeOrPartial := false, directDeps := [] }

/-- Clean two-shard diamond repository using only `propext`. -/
def cleanDiamondEnv : RepoEnv :=
  { registeredModules := ["M1", "M2"]
    onDiskModules := ["M1", "M2"]
    permittedAxioms := ["propext"]
    decls := [diamondM1Top, diamondM2Left, diamondM2Right, diamondPropext] }

theorem cleanDiamond_reaches_propext_from_shard1 :
    ReachesAxiomFrom cleanDiamondEnv ["M1"] "propext" := by
  refine ⟨diamondM1Top, by decide, by decide, ?_, diamondPropext, by decide, rfl⟩
  exact TransDep.step (c' := "M2.left") (rec := diamondM1Top) (by decide) (by decide)
    (TransDep.step (c' := "propext") (rec := diamondM2Left) (by decide) (by decide)
      (TransDep.refl _))

theorem crossShardDuplicateConflict_reconciliation_test :
    (checkCrossShardFingerprints [["M1"], ["M2"]] crossShardConflictEntries).any
        (·.code == .crossShardDuplicateConflict) = true ∧
      MonolithicDuplicateConsistent ["M1", "M2"]
        [{ modName := "M1", declName := "evalRvalue.eq_4", fingerprint := "fp_v1" },
         { modName := "M2", declName := "evalRvalue.eq_4", fingerprint := "fp_v1" }] := by
  refine ⟨by decide, ?_⟩
  exact (crossShardFingerprintReconciliation_sound
    ((shardPartitionCheck_iff_valid ["M1", "M2"] ["M1", "M2"] [["M1"], ["M2"]]).mp rfl)).mp rfl

theorem danglingRecursor_and_iffIfte_regressions_test :
    hasReplayViolation (checkStaticInductiveIntegrity malformedDanglingRecMap) .recursorMismatch = true ∧
      checkAssumesNegativePolarity (.iff (.atom "outputEq") (.assumes "impl")) = false ∧
      checkAssumesNegativePolarity
        (.imp (.ifte (.assumes "impl") (.atom "outputEq") (.not (.atom "impl.assertionFailed")))
          (.atom "outputEq")) = false :=
  ⟨danglingRecursor_rejected_statically_and_postReplay.1,
   checkAssumesNegativePolarity_vectors.2.2.2.2.2.1,
   checkAssumesNegativePolarity_vectors.2.2.2.2.2.2⟩

/-! ## 4. Pillar 3 — Peer-Verifier Spec Guard Regression Tests -/

theorem guard3_honest_extern_transfer_test :
    let spec : ExternCallableSpec Nat Nat :=
      { fnName := "checked_inc", isTrustedExtern := true, isDiverging := false,
        pre := fun x => x < 100, post := fun x y => y = x + 1 }
    ExternEnsuresGuard spec ∧ (5 + 1 = 6) :=
  externEnsuresGuard_continuation_transfer (fun x => x + 1) (fun _ _ => rfl)
    (by decide) (fun _ _ hy => hy) rfl

theorem guard4_token_guard_test :
    FnDefGhostTokenGuard [] ∧ FnDefGhostTokenGuard [.directEntryCall true] ∧
      ¬ FnDefGhostTokenGuard [.fnDefValueBind "f"] :=
  ⟨by unfold FnDefGhostTokenGuard; decide,
   fndefGhostTokenGuard_allows_single_direct_call,
   fndefGhostTokenGuard_rejects_non_call_uses.1⟩

theorem guard5_drop_guard_preserves_zero_invariant_test :
    let t : ExternalTypeSpec :=
      { typeName := "SafeGuard", hasExternalTypeSpec := true, hasExternalBody := false,
        implementsDrop := true, fieldHasDropGlue := false, dropSpecModeled := true }
    scopeExitState t.hasDropGlue (fun _ => 0) 0 = 0 :=
  externalTypeDropGuard_preserves_scope_exit_invariant (inv := fun s => s = 0)
    rfl externalTypeDropGuard_allows_modeled_drop_without_external_body rfl (fun _ _ => rfl)

theorem guard6a_counterexample_refutes_broken_impl_fn :
    let specFn : Nat → EvalRes Nat := fun x => { assumesHold := true, assertionFailed := false, output := x }
    let implFn : Nat → EvalRes Nat := fun x => { assumesHold := true, assertionFailed := false, output := x + 1 }
    ¬ (∀ i, CorrectEquivObligation (specFn i) (implFn i)) :=
  checkCombCounterExample_refutes_equiv
    (fun x => { assumesHold := true, assertionFailed := false, output := x })
    (fun x => { assumesHold := true, assertionFailed := false, output := x + 1 })
    0 (by decide)

theorem guard6b_sealedCap_mkChecked_vectors :
    SealedCap.mkChecked 0 = none ∧
      ∃ c, SealedCap.mkChecked 7 = some c ∧ c.val = 7 ∧ 0 < c.val := by
  refine ⟨by decide, ?_⟩
  cases h : SealedCap.mkChecked 7 with
  | none =>
    have hPos : SealedCap.mkChecked 7 ≠ none := by
      unfold SealedCap.mkChecked
      simp
    exact absurd h hPos
  | some c =>
    have ⟨hv, hp⟩ := sealedCap_mkChecked_preserves_invariant h
    exact ⟨c, rfl, hv, hp⟩

/-! ## 5. Kernel Axiom & Environment Hygiene Audit -/

/-- info: 'Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.inductiveReplayWellFormed_sound' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.inductiveReplayWellFormed_sound

/-- info: 'Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.shardAxiomUnion_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.shardAxiomUnion_sound

/-- info: 'Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.shardPartitionCheck_iff_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.shardPartitionCheck_iff_valid

/-- info: 'Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.externEnsuresGuard_sound' does not depend on any axioms -/
#guard_msgs in
#print axioms Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.externEnsuresGuard_sound

/-- info: 'Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.externEnsuresGuard_vacuity_only_from_genuine_divergence' does not depend on any axioms -/
#guard_msgs in
#print axioms Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.externEnsuresGuard_vacuity_only_from_genuine_divergence

/-- info: 'Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.hardenedInductiveReplay_sound' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.hardenedInductiveReplay_sound

/-- info: 'Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.fndefGhostTokenGuard_preserves_uniqueness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.fndefGhostTokenGuard_preserves_uniqueness

/-- info: 'Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.externalTypeDropGuard_preserves_scope_exit_invariant' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.externalTypeDropGuard_preserves_scope_exit_invariant

/-- info: 'Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.checkCombCounterExample_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.checkCombCounterExample_sound

/-- info: 'Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.invariantStructSealingGuard_sound' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.invariantStructSealingGuard_sound

/-- info: 'Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.crossShardFingerprintReconciliation_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.crossShardFingerprintReconciliation_sound

/-- info: 'Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.danglingRecursor_rejected_statically_and_postReplay' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.danglingRecursor_rejected_statically_and_postReplay


/-! ## 6. B2 Regression Tests: Lossy Digests, Operational Guard 4, Semantic Guard 6a -/

/-- A concrete UInt64-truncating digest collides on `[5]` vs `[5 + 2^64]`, so hash-based
    cross-shard reconciliation accepts a conflicting duplicate. -/
def truncDigest (p : List Nat) : String :=
  if p.map (· % 18446744073709551616) = [5] then "h5" else "other"

theorem b2_truncDigest_hides_conflict :
    checkCrossShardFingerprints [["M1"], ["M2"]]
        (digestEntries truncDigest [⟨"M1", "d", [5]⟩, ⟨"M2", "d", [5 + 18446744073709551616]⟩]) = [] ∧
      ¬ ExactDuplicateConsistent ["M1", "M2"]
        [⟨"M1", "d", [5]⟩, ⟨"M2", "d", [5 + 18446744073709551616]⟩] :=
  lossyDigest_reconciliation_misses_conflict truncDigest (by decide) (by decide)

theorem b2_tokProg_guard_vectors :
    tokProgGuard (.seq .callCtor (.loop 3 .skip)) = true ∧
      TokenUniquenessHolds ((TokProg.seq .callCtor (.loop 3 .skip)).run false).1 ∧
      tokProgGuard (.loop 1 .callCtor) = false := by
  refine ⟨by decide, tokProgGuard_sound (by decide), by decide⟩

theorem b2_correctEquiv_semantically_antitone (va : String → Prop)
    (h : evalPF va (fun _ => True) correctEquivFormula) :
    ∀ vs, evalPF va vs correctEquivFormula :=
  checkAssumesNegativePolarity_sound va (by decide) h

/-- info: 'Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.checkAssumesNegativePolarity_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.checkAssumesNegativePolarity_sound

/-- info: 'Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.tokProgGuard_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.tokProgGuard_sound

/-- info: 'Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.injectiveDigest_reconciliation_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.injectiveDigest_reconciliation_exact

/-! ## 7. A2 Regression Tests: Strict Kind Compat, Bool-Neg Polarity, Operational Guard 6b -/

theorem a2_moduleSealingGuard_checked_client_test :
    let posInv : Nat → Bool := fun n => decide (0 < n)
    let safeMod : StructModule :=
      { ctorPrivate := true, derivesInhabited := false, inv := posInv,
        exports := [.checkedCtor posInv, .defaultInstance 1] }
    ∀ (e : ClientExpr) {v : Nat}, e.eval safeMod = some v → posInv v = true := by
  refine moduleSealingGuard_preserves_client_invariant ⟨rfl, rfl, ?_⟩
  intro ex hex
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hex
  rcases hex with rfl | rfl
  · intro n hn; exact hn
  · exact rfl

theorem a2_kindConfusion_and_boolNeg_regression_test :
    (strictConstCompat
      { kind := .axiomDecl, levelParams := [], typeTag := "Nat", valueOpt := none, metaTag := "" }
      { kind := .defnDecl, levelParams := [], typeTag := "Nat", valueOpt := some "0", metaTag := "" } = false) ∧
    checkAssumesNegativePolarity (.imp (.not (.assumes "impl")) (.atom "outputEq")) = false :=
  ⟨lossyCompat_accepts_axiom_vs_defn_and_forged_induct.2.1,
   boolNegAssumes_antecedent_violates_antitonicity.1⟩

/-- info: 'Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.strictConstCompat_iff_eq_nonThm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.strictConstCompat_iff_eq_nonThm

/-- info: 'Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.moduleSealingGuard_preserves_client_invariant' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.moduleSealingGuard_preserves_client_invariant

/-- info: 'Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.publicLeakOrDerivingInhabited_forges_invalid_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.publicLeakOrDerivingInhabited_forges_invalid_value

/-- B3: a module with a sound checked ctor AND an invariant-preserving method passes the
    guard, and every client term over it (including method chains) yields a valid payload. -/
theorem b3_method_preserving_module_sound :
    let posInv : Nat → Bool := fun n => decide (0 < n)
    let m : StructModule :=
      { ctorPrivate := true, derivesInhabited := false, inv := posInv,
        exports := [.checkedCtor posInv, .transform (· + 1)] }
    ∀ e : ClientExpr, ∀ v, e.eval m = some v → posInv v = true := by
  intro posInv m e v h
  refine moduleSealingGuard_preserves_client_invariant ?_ e h
  refine ⟨rfl, rfl, ?_⟩
  intro ex hex
  simp only [m, List.mem_cons, List.not_mem_nil, or_false] at hex
  rcases hex with rfl | rfl
  · exact fun _ hg => hg
  · intro n _
    exact decide_eq_true (Nat.succ_pos n)

/-- info: 'Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.moduleSealingGuard_preserves_client_invariant' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.moduleSealingGuard_preserves_client_invariant

/-! ## 8. A3 Regression Tests: Private-Helper Forwarders & Alias-Split Guard 4 -/

theorem a3_checked_privateHelper_forwarder_sound :
    let posInv : Nat → Bool := fun n => decide (0 < n)
    let safePriv : Nat → Option Nat := fun n => if posInv n then some n else none
    let m : StructModule :=
      { ctorPrivate := true, derivesInhabited := false, inv := posInv,
        privateHelpers := [safePriv],
        exports := [.callPrivateHelper 0] }
    ∀ e : ClientExpr, ∀ v, e.eval m = some v → posInv v = true := by
  intro posInv safePriv m e v h
  refine moduleSealingGuard_preserves_client_invariant ⟨rfl, rfl, ?_⟩ e h
  intro ex hex
  simp only [m, List.mem_cons, List.not_mem_nil, or_false] at hex
  rcases hex with rfl
  intro hFn hGet arg out hOut
  simp only [m, List.getElem?_cons_zero, Option.some.injEq] at hGet
  subst hGet
  simp only [safePriv] at hOut
  by_cases hp : posInv arg = true
  · simp only [hp, ↓reduceIte, Option.some.injEq] at hOut
    subst hOut
    exact hp
  · simp only [hp] at hOut
    cases hOut

/-- info: 'Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.privateHelper_leaked_by_public_forwarder_collapse' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.privateHelper_leaked_by_public_forwarder_collapse

/-- info: 'Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.canonicalSiteGuard_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.canonicalSiteGuard_sound

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let moduleName := `Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto
  let some modIdx := env.getModuleIdx? moduleName
    | throwError "module {moduleName} is not imported"
  let isCodegenUnsafeRec (n : Name) (ci : ConstantInfo) : Bool :=
    if ci.isUnsafe || !ci.isPartial then false
    else match n with
      | .str parent "_unsafe_rec" =>
        match env.find? parent with
        | some parentCi => !parentCi.isUnsafe && !parentCi.isPartial
        | none => false
      | _ => false
  let audit (n : Name) (ci : ConstantInfo) : CommandElabM Bool := do
    if isCodegenUnsafeRec n ci then
      return false
    if ci.isUnsafe then throwError "unsafe declaration: {n}"
    if ci.isPartial then throwError "partial declaration: {n}"
    match ci with
    | .axiomInfo _ => throwError "axiom declaration: {n}"
    | .opaqueInfo _ => throwError "opaque declaration: {n}"
    | .defnInfo v =>
      unless v.safety == .safe do throwError "non-safe definition: {n}"
    | _ => pure ()
    for a in ← liftCoreM <| Lean.collectAxioms n do
      unless allowed.contains a do
        throwError "{n} depends on disallowed axiom {a}"
    return ci matches .thmInfo _
  let mut moduleThms : Nat := 0
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some modIdx then
      if ← audit n ci then
        moduleThms := moduleThms + 1
  let mut testThms : Nat := 0
  for (n, ci) in env.constants.map₂.toList do
    if ← audit n ci then
      testThms := testThms + 1
  for flagship in
      [``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.PeerSpecGuardClass.guardId_injective,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.PeerSpecGuardClass.rank_ne_specBoundaryGuard,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.fakeFalse_passes_vulnerableInductiveReplay,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.fakeFalse_rejected_by_hardenedInductiveReplay,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.forgedMetadata_passes_vulnerableInductiveReplay,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.forgedMetadata_rejected_by_hardenedInductiveReplay,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.inductiveReplayWellFormed_sound,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.hardenedInductiveReplay_sound,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.shardPartitionCheck_iff_valid,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.shardAxiomUnion_sound,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.crossShardThreeHop_caught_by_shard1,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.truncatedShardAudit_misses_crossShard_badAxiom,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.readVolatile_ensures_false_collapse,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.externEnsuresGuard_sound,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.fndefCoercion_duplicates_token_collapse,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.fndefGhostTokenGuard_preserves_uniqueness,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.externalTypeDropOmission_breaks_invariant,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.externalTypeDropGuard_preserves_scope_exit_invariant,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.polarityFlip_accepts_broken_impl,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.checkCombCounterExample_sound,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.unsealedCap_allows_forged_invariant_violation,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.invariantStructSealingGuard_sound,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.fakeFalse_unitFirst_rejected_by_vulnerable_kernel,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.fakeFalseWithRec_rejected_by_vulnerable_postponedRecursors,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.forgedNatRec_rejected_by_hardened_and_vulnerable,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.lyingDiverging_bypasses_flagOnly_but_rejected_by_guard,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.externEnsuresGuard_vacuity_only_from_genuine_divergence,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.caseFoldCollision_rejected_by_checkShardPartition,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.lossyDigest_reconciliation_misses_conflict,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.uint64NatTruncation_collides,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.injectiveDigest_reconciliation_exact,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.tokProgGuard_sound,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.tokProg_valueUse_and_loop_duplicate_tokens,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.assumesOnlyNegative_monotone,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.checkAssumesNegativePolarity_sound,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.flippedConsequent_violates_antitonicity,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.uncheckedMethod_forges_invalid_value,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.danglingRecursor_rejected_statically_and_postReplay,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.shardLocalDupCheck_misses_crossShard_conflict,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.crossShardFingerprintReconciliation_sound,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.iffAndIftePolarity_accept_broken_impl,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.lossyCompat_accepts_axiom_vs_defn_and_forged_induct,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.strictConstCompat_iff_eq_nonThm,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.boolNegAssumes_antecedent_violates_antitonicity,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.publicLeakOrDerivingInhabited_forges_invalid_value,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.moduleSealingGuard_preserves_client_invariant,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.privateHelper_leaked_by_public_forwarder_collapse,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.aliasCanonicalization_catches_aliased_double_issuance,
        ``Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto.canonicalSiteGuard_sound] do
    match env.find? flagship with
    | some (.thmInfo _) =>
      unless env.getModuleIdxFor? flagship == some modIdx do
        throwError "flagship theorem {flagship} is not defined in {moduleName}"
    | _ => throwError "flagship theorem {flagship} is missing"
  unless moduleThms ≥ 60 do
    throwError "{moduleName}: only {moduleThms} kernel theorems (expected ≥ 60)"
  unless testThms ≥ 14 do
    throwError "InductiveReplayAndPeerSpecGuardsProtoTests: only {testThms} kernel theorems (expected ≥ 14)"

end Anneal.Proto.InductiveReplayAndPeerSpecGuardsProtoTests
