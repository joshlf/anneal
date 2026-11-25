-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.InductiveReplayAndPeerSpecGuards

/-!
# Tests for `Anneal.InductiveReplayAndPeerSpecGuards`

1. **Wire parity** (§1): `PeerSpecGuardClass` ranks `3..6`, identifiers, names, and
   vacuity classes pinned as literal tables against `Anneal.SpecBoundaryGuards`, plus the
   seven-guard `CombinedSpecGuardClass` bijection. The same tables are asserted by
   `anneal_spec::peer_soundness_guards`.
2. **Pillar 1** (§2): one concrete forgery per `ForgedInductiveClass`, each accepted by
   self-comparison and rejected by `InductiveReplayWellFormed` with its exact code.
3. **Pillar 2** (§3): the `2 ^ 64` collision, the `.axiomInfo` / `.defnInfo` conflation,
   and sharded-audit soundness on a concrete reconciled world.
4. **Pillar 3** (§4): Guards 3–6 collapse and restoration instances.
5. **Axiom pins** (§5): `#print axioms` on every flagship theorem.
-/

namespace Anneal.InductiveReplayAndPeerSpecGuardsTests

open Anneal.SpecRealizability (VacuityClass)
open Anneal.SpecBoundaryGuards (SpecBoundaryGuardClass)
open Anneal.InductiveReplayAndPeerSpecGuards

/-! ## 1. Wire parity -/

example : PeerSpecGuardClass.count = 4 := rfl
example : PeerSpecGuardClass.all.map PeerSpecGuardClass.rank = [3, 4, 5, 6] := rfl
example : PeerSpecGuardClass.all.map PeerSpecGuardClass.guardId =
    ["unsatisfiable_extern_ensures", "fndef_ghost_token_coercion",
      "external_type_drop_omission", "assumption_polarity_and_struct_sealing"] := rfl
example : PeerSpecGuardClass.all.map PeerSpecGuardClass.canonicalName =
    ["UnsatisfiableExternEnsures", "FnDefGhostTokenCoercion", "ExternalTypeDropOmission",
      "AssumptionPolarityAndStructSealing"] := rfl
example : PeerSpecGuardClass.all.map PeerSpecGuardClass.toVacuityClass =
    [.deadPrecondition, .specViolation, .specViolation, .survivedAllMutants] := rfl

example : PeerSpecGuardClass.ofRank? 2 = none := rfl
example : PeerSpecGuardClass.ofRank? 7 = none := rfl
example : PeerSpecGuardClass.ofRank? 0 = none := rfl
example : PeerSpecGuardClass.ofRank? 5 = some .externalTypeDropOmission := rfl
example : PeerSpecGuardClass.ofGuardId? "fndef_ghost_token_coercion" =
    some .fnDefGhostTokenCoercion := rfl
example : PeerSpecGuardClass.ofGuardId? "FnDefGhostTokenCoercion" = none := rfl
example : PeerSpecGuardClass.ofGuardId? "entry_point_requires" = none := rfl
example : PeerSpecGuardClass.ofCanonicalName? "ExternalTypeDropOmission" =
    some .externalTypeDropOmission := rfl
example : PeerSpecGuardClass.ofCanonicalName? "externaltypedropomission" = none := rfl

/-- Base ranks `0..2` and peer ranks `3..6` tile `0..6` without overlap. -/
example : SpecBoundaryGuardClass.all.map SpecBoundaryGuardClass.rank ++
    PeerSpecGuardClass.all.map PeerSpecGuardClass.rank = List.range 7 := rfl

example : CombinedSpecGuardClass.all.map CombinedSpecGuardClass.guardId =
    ["entry_point_requires", "fixed_width_ghost_length", "error_branch_wildcard",
      "unsatisfiable_extern_ensures", "fndef_ghost_token_coercion",
      "external_type_drop_omission", "assumption_polarity_and_struct_sealing"] := rfl
example : CombinedSpecGuardClass.all.map
    (fun c => c.toVacuityClass.canonicalName) =
    ["DeadPrecondition", "SpecViolation", "SurvivedAllMutants", "DeadPrecondition",
      "SpecViolation", "SpecViolation", "SurvivedAllMutants"] := rfl
example : CombinedSpecGuardClass.ofRank? 3 = some (.peer .unsatisfiableExternEnsures) := rfl
example : CombinedSpecGuardClass.ofRank? 2 = some (.base .errorBranchWildcard) := rfl
example : CombinedSpecGuardClass.ofRank? 7 = none := rfl
example : (List.range 7).map CombinedSpecGuardClass.ofRank? =
    CombinedSpecGuardClass.all.map some := rfl
example (n : Nat) (h : 7 ≤ n) : CombinedSpecGuardClass.ofRank? n = none := by
  cases hc : CombinedSpecGuardClass.ofRank? n with
  | none => rfl
  | some c =>
    have := CombinedSpecGuardClass.rank_of_ofRank? hc ▸ CombinedSpecGuardClass.rank_lt_count c
    exact absurd this (by unfold CombinedSpecGuardClass.count; omega)

example : (PeerSpecGuardVerdict.ofCheck .externalTypeDropOmission false).vacuityClass? =
    some .specViolation := rfl
example : (PeerSpecGuardVerdict.ofCheck .externalTypeDropOmission true).vacuityClass? = none := rfl

/-! ## 2. Pillar 1 — one forgery per class -/

def withInduct (I : InductMeta) : ModuleData :=
  { constNames := [1, 2, 3, 4],
    constants := [.inductInfo I, .ctorInfo fixtureCtor0, .ctorInfo fixtureCtor1,
      .recInfo fixtureRec] }

def cleanKenv : Env := pinnedReplayEnv cleanModule

example : checkInductiveReplay cleanModule cleanKenv = true := by decide
example : inductiveReplayViolations cleanModule cleanKenv = [] := by decide
example : selfComparisonCheck cleanModule = true := by decide

def fMissingName : ModuleData := { cleanModule with constNames := [1, 2, 3] }
def fKeyMismatch : ModuleData := { cleanModule with constNames := [1, 3, 2, 4] }
def fDuplicateConstName : ModuleData :=
  { constNames := [1, 2, 3, 4, 2],
    constants := cleanModule.constants ++ [.ctorInfo fixtureCtor0] }
def fCrossInductRecRule : ModuleData :=
  let otherInduct : InductMeta :=
    { fixtureInduct with name := 10, all := [10], ctors := [11] }
  let otherCtor : CtorMeta :=
    { fixtureCtor0 with name := 11, type := .const 10, induct := 10, cidx := 0 }
  let crossRec : RecMeta :=
    { fixtureRec with
        name := 12, all := [1],
        rules := [{ ctor := 11, nfields := 0, rhs := .lam (.sort 0) (.bvar 0) }] }
  { constNames := [1, 2, 3, 4, 10, 11, 12],
    constants := cleanModule.constants ++
      [.inductInfo otherInduct, .ctorInfo otherCtor, .recInfo crossRec] }
def fDupRecAll : ModuleData :=
  { constNames := [1, 2, 3, 4, 13],
    constants := cleanModule.constants ++ [.recInfo { fixtureRec with name := 13, all := [1, 1] }] }
def fOpenExpr : ModuleData :=
  { constNames := [1, 2, 3, 4],
    constants := [.inductInfo fixtureInduct, .ctorInfo { fixtureCtor0 with type := .fvar 0 },
      .ctorInfo fixtureCtor1, .recInfo fixtureRec] }
def fLooseBVar : ModuleData :=
  { constNames := [1, 2, 3, 4],
    constants := [.inductInfo fixtureInduct, .ctorInfo { fixtureCtor0 with type := .bvar 0 },
      .ctorInfo fixtureCtor1, .recInfo fixtureRec] }
def fEmptyAll : ModuleData := withInduct { fixtureInduct with all := [] }
def fDupAll : ModuleData := withInduct { fixtureInduct with all := [1, 1] }
def fNonInductAll : ModuleData := withInduct { fixtureInduct with all := [1, 2] }
def fDupCtors : ModuleData := withInduct { fixtureInduct with ctors := [2, 2, 3] }
def fNonCtorCtors : ModuleData := withInduct { fixtureInduct with ctors := [2, 3, 4] }
def fWrongParent : ModuleData :=
  { constNames := [1, 2, 3, 4],
    constants := [.inductInfo fixtureInduct, .ctorInfo { fixtureCtor0 with induct := 9 },
      .ctorInfo fixtureCtor1, .recInfo fixtureRec] }
def fWrongCidx : ModuleData :=
  { constNames := [1, 2, 3, 4],
    constants := [.inductInfo fixtureInduct, .ctorInfo fixtureCtor0,
      .ctorInfo { fixtureCtor1 with cidx := 0 }, .recInfo fixtureRec] }
def fDanglingCtor : ModuleData :=
  { constNames := [1, 2, 3, 4, 7],
    constants := cleanModule.constants ++ [.ctorInfo { fixtureCtor1 with name := 7, cidx := 2 }] }
def fDanglingRec : ModuleData :=
  { constNames := [1, 2, 3, 4, 8],
    constants := cleanModule.constants ++ [.recInfo { fixtureRec with name := 8, all := [9] }] }

/-- A two-member mutual block whose second member disagrees on `all`. -/
def mutualA : InductMeta := { fixtureInduct with all := [1, 6] }
def mutualB : InductMeta := { fixtureInduct with name := 6, all := [6, 1], ctors := [] }
def fMutual : ModuleData :=
  { constNames := [1, 2, 3, 4, 6],
    constants := [.inductInfo mutualA, .ctorInfo fixtureCtor0, .ctorInfo fixtureCtor1,
      .recInfo fixtureRec, .inductInfo mutualB] }

example : fMissingName.constants = cleanModule.constants := rfl

example : .missingConstNameEntry ∈ inductiveReplayViolations fMissingName cleanKenv := by decide
example : .keyMismatch ∈ inductiveReplayViolations fKeyMismatch cleanKenv := by decide
example : .duplicateConstName ∈ inductiveReplayViolations fDuplicateConstName cleanKenv := by decide
example : .danglingRecursor ∈ inductiveReplayViolations fCrossInductRecRule cleanKenv := by decide
example : .danglingRecursor ∈ inductiveReplayViolations fDupRecAll cleanKenv := by decide
example : ForgedInductiveClass.all.length = 19 := rfl
example : cleanModule.constNames = cleanModule.constants.map RConstInfo.name :=
  inductiveReplayWellFormed_constNames_eq cleanModule_wellFormed
example : .constantHasOpenExpr ∈ inductiveReplayViolations fOpenExpr cleanKenv := by decide
example : .constantHasOpenExpr ∈ inductiveReplayViolations fLooseBVar cleanKenv := by decide
example : .selfNotInAll ∈ inductiveReplayViolations forgedModule cleanKenv := by decide
example : .emptyAll ∈ inductiveReplayViolations fEmptyAll cleanKenv := by decide
example : .selfNotInAll ∈ inductiveReplayViolations fEmptyAll cleanKenv := by decide
example : .duplicateInAll ∈ inductiveReplayViolations fDupAll cleanKenv := by decide
example : .nonInductInAll ∈ inductiveReplayViolations fNonInductAll cleanKenv := by decide
example : .mutualMetadataMismatch ∈ inductiveReplayViolations fMutual cleanKenv := by decide
example : .duplicateInCtors ∈ inductiveReplayViolations fDupCtors cleanKenv := by decide
example : .nonCtorInCtors ∈ inductiveReplayViolations fNonCtorCtors cleanKenv := by decide
example : .ctorInductMismatch ∈ inductiveReplayViolations fWrongParent cleanKenv := by decide
example : .danglingCtorNotListedInInduct ∈ inductiveReplayViolations fWrongParent cleanKenv := by
  decide
example : .ctorCidxMismatch ∈ inductiveReplayViolations fWrongCidx cleanKenv := by decide
example : .danglingCtorNotListedInInduct ∈ inductiveReplayViolations fDanglingCtor cleanKenv := by
  decide
example : .danglingRecursor ∈ inductiveReplayViolations fDanglingRec cleanKenv := by decide

/-- Post-replay drift on the inductive, a constructor, and the recursor. -/
example : inductiveReplayViolations (withInduct { fixtureInduct with isRec := true }) cleanKenv =
    [.postReplayInductMismatch] := by decide
example : inductiveReplayViolations (withInduct { fixtureInduct with isReflexive := true })
    cleanKenv = [.postReplayInductMismatch] := by decide
example : inductiveReplayViolations (withInduct { fixtureInduct with levelParams := 1 })
    cleanKenv = [.postReplayInductMismatch] := by decide
example : inductiveReplayViolations (withInduct { fixtureInduct with type := .sort 2 })
    cleanKenv = [.postReplayInductMismatch] := by decide
example : inductiveReplayViolations
    { cleanModule with constants := [.inductInfo fixtureInduct,
        .ctorInfo { fixtureCtor0 with numFields := 1 }, .ctorInfo fixtureCtor1,
        .recInfo fixtureRec] } cleanKenv = [.postReplayCtorMismatch] := by decide
example : inductiveReplayViolations
    { cleanModule with constants := [.inductInfo fixtureInduct, .ctorInfo fixtureCtor0,
        .ctorInfo fixtureCtor1, .recInfo { fixtureRec with k := true }] } cleanKenv =
      [.recursorMismatch] := by decide
example : inductiveReplayViolations
    { cleanModule with constants := [.inductInfo fixtureInduct, .ctorInfo fixtureCtor0,
        .ctorInfo fixtureCtor1, .recInfo { fixtureRec with numMinors := 3 }] } cleanKenv =
      [.recursorMismatch] := by decide

/-- Self-comparison accepts every forgery with distinct names. -/
example : [fOpenExpr, fEmptyAll, fDupAll, fNonInductAll, fDupCtors, fNonCtorCtors, fWrongParent,
    fWrongCidx, fDanglingCtor, fDanglingRec, fMutual, forgedModule, driftedModule].all
      selfComparisonCheck = true := by decide

/-- A missing kernel entry is caught by the unconditional sweep (general theorem). -/
example : ¬ InductiveReplayWellFormed cleanModule [] :=
  postReplaySweep_rejects_unreplayed (c := .recInfo fixtureRec) (by decide) rfl rfl

/-- The general rejection theorem, instantiated with a Prop-level forgery witness. -/
example : ¬ InductiveReplayWellFormed fDupAll cleanKenv ∧
    ForgedInductiveClass.duplicateInAll.code ∈ inductiveReplayViolations fDupAll cleanKenv :=
  inductiveReplayWellFormed_rejects (cls := .duplicateInAll)
    ⟨{ fixtureInduct with all := [1, 1] }, by decide, by decide⟩

example : ¬ InductiveReplayWellFormed fWrongCidx cleanKenv :=
  (inductiveReplayWellFormed_rejects (cls := .wrongCidxCtor)
    ⟨fixtureInduct, by decide, 3, by decide, { fixtureCtor1 with cidx := 0 }, by decide,
      by decide⟩).1

example : InductiveReplayViolationCode.all.map InductiveReplayViolationCode.wireId =
    ["missing_constName_entry", "key_mismatch", "duplicate_const_name", "constant_has_open_expr",
      "self_not_in_all", "empty_all", "duplicate_in_all", "non_induct_in_all",
      "mutual_metadata_mismatch", "duplicate_in_ctors", "non_ctor_in_ctors",
      "ctor_induct_mismatch", "ctor_cidx_mismatch", "dangling_ctor_not_listed_in_induct",
      "dangling_recursor", "post_replay_induct_mismatch", "post_replay_ctor_mismatch",
      "recursor_mismatch", "kernel_constant_dropped"] := rfl

/-- A forgery that drops the recursor the kernel regenerates, or replaces it by a
    definition of the same name, is rejected by the reverse post-replay sweep. -/
def fDroppedRec : ModuleData :=
  { constNames := [1, 2, 3],
    constants := [.inductInfo fixtureInduct, .ctorInfo fixtureCtor0, .ctorInfo fixtureCtor1] }
def fReplacedRec : ModuleData :=
  { constNames := [1, 2, 3, 4],
    constants := [.inductInfo fixtureInduct, .ctorInfo fixtureCtor0, .ctorInfo fixtureCtor1,
      .defnInfo 4 1 fixtureRec.type (.lam (.sort 0) (.bvar 0))] }

example : selfComparisonCheck fDroppedRec = true ∧ selfComparisonCheck fReplacedRec = true := by
  decide
example : inductiveReplayViolations fDroppedRec cleanModule.constants = [.kernelConstantDropped] := by
  decide
example : inductiveReplayViolations fReplacedRec cleanModule.constants =
    [.kernelConstantDropped] := by decide
example : inductiveReplayViolations cleanModule cleanModule.constants = [] := by decide
example : ¬ InductiveReplayWellFormed fDroppedRec cleanModule.constants :=
  (inductiveReplayWellFormed_rejects (cls := .droppedKernelConstant)
    ⟨.recInfo fixtureRec, by decide, rfl, fun d hd => by cases hd⟩).1
example : lookup cleanModule.constants 4 = some (.recInfo fixtureRec) :=
  inductiveReplayWellFormed_kernel_exact (md := cleanModule) (kenv := cleanModule.constants)
    (by decide) (by decide) (.recInfo fixtureRec) (by decide) rfl
example : (.recInfo fixtureRec ∈ cleanModule.constants) ↔
    (.recInfo fixtureRec ∈ cleanModule.constants) :=
  inductiveReplayWellFormed_family_iff (md := cleanModule) (kenv := cleanModule.constants)
    (by decide) (by decide) rfl

/-! ## 3. Pillar 2 -/

example : (RExpr.natLit 5).hash64 = (RExpr.natLit (5 + 2 ^ 64)).hash64 := by decide
example : (RExpr.app (.const 1) (.natLit 0)).hash64 =
    (RExpr.app (.const 1) (.natLit (2 ^ 64))).hash64 := by decide
example : strictConstCompat (.defnInfo 1 0 (.const 2) (.natLit 0))
    (.defnInfo 1 0 (.const 2) (.natLit (2 ^ 64))) = false := by decide
example : naiveCompat (.opaqueInfo 1 0 (.const 2) (.const 3)) (.defnInfo 1 0 (.const 2) (.const 4)) =
    true := by decide
example : strictConstCompat (.opaqueInfo 1 0 (.const 2) (.const 3))
    (.defnInfo 1 0 (.const 2) (.const 4)) = false := by decide
example : strictConstCompat (.inductInfo fixtureInduct)
    (.inductInfo { fixtureInduct with numIndices := 1 }) = false := by decide
example : strictConstCompat (.recInfo fixtureRec) (.recInfo fixtureRec) = true := by decide

/-- A reconciled two-shard world: shard B imports module `0`, so it sees the same
    definition of `7`; module `1` declares axiom `20`, which its claim `11` uses. -/
def rClaimA : RConstInfo := .thmInfo 10 0 (.const 7) (.const 7)
def rClaimB : RConstInfo := .thmInfo 11 0 (.const 20) (.app (.const 20) (.const 7))
def rAxiom : RConstInfo := .axiomInfo 20 0 (.sort 0)

def rWorld : ModuleWorld :=
  { modules := [0, 1],
    declsOf := fun m => if m = 0 then [rClaimA, ceDefn] else if m = 1 then [rClaimB, rAxiom] else [] }

def rShardA : AuditShard := { modules := [0], env := [rClaimA, ceDefn] }
def rShardB : AuditShard := { modules := [1], env := [rClaimB, rAxiom, rClaimA, ceDefn] }

example : CrossShardReconciled [rShardA, rShardB] := by decide

theorem rWorld_sound : ShardAxiomUnionSound rWorld [rShardA, rShardB] := by
  refine shardAxiomUnion_sound ⟨by decide, by decide⟩ ?_ (by decide)
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact ⟨by decide, by decide, by decide⟩
  · exact ⟨by decide, by decide, by decide⟩

example : monoAxioms rWorld 20 ∧ ∃ s ∈ [rShardA, rShardB], shardAxioms rWorld s 20 := by
  have hMono : monoAxioms rWorld 20 :=
    ⟨rAxiom, .step (c := rClaimB) (.root (by decide) (by decide)) (by decide) (by decide), rfl, rfl⟩
  exact ⟨hMono, (rWorld_sound.axiom_union 20).mp hMono⟩

example : ¬ CrossShardReconciled ceShards := naiveReconciliation_breaks_axiom_union.2.2.2.1
example : NaiveReconciled ceShards := naiveReconciliation_breaks_axiom_union.2.2.1
example : HashReconciled hceShards ∧ ¬ CrossShardReconciled hceShards :=
  ⟨hashReconciliation_breaks_axiom_union.2.2.1, hashReconciliation_breaks_axiom_union.2.2.2.1⟩
example : monoAxioms hceWorld 17 ∧ ¬ ∃ s ∈ hceShards, shardAxioms hceWorld s 17 :=
  ⟨hashReconciliation_breaks_axiom_union.2.2.2.2.1,
    hashReconciliation_breaks_axiom_union.2.2.2.2.2⟩

/-! ## 4. Pillar 3 -/

/-! ### Guard 3 -/

def volatileRead : ExternContract Unit Nat :=
  { trust := .externSpec, requires := fun _ => True, ensures := fun _ _ => False,
    isDiverging := false }

def lyingDivergingRead : ExternContract Unit Nat := { volatileRead with isDiverging := true }

def abortStub : ExternContract Unit Empty :=
  { trust := .trusted, requires := fun _ => True, ensures := fun _ _ => False,
    isDiverging := true }

def unreachableStub : ExternContract Unit Nat :=
  { trust := .assumed, requires := fun _ => False, ensures := fun _ _ => False,
    isDiverging := false }

example : ¬ ExternalEnsuresFalseGuard volatileRead :=
  returningEnsuresFalse_rejected volatileRead (by decide) rfl () trivial (fun _ h => h)
example : ¬ ExternalEnsuresFalseGuard lyingDivergingRead := lyingDiverging_rejected _ rfl 0
example : ExternalEnsuresFalseGuard abortStub :=
  externalEnsuresFalseGuard_of_uninhabited _ (fun e => nomatch e) rfl
example : ExternalEnsuresFalseGuard unreachableStub :=
  externalEnsuresFalseGuard_of_requires_false _ (fun _ h => h) rfl
example (impl : Unit → Option Empty) : impl () = none :=
  (externalEnsuresFalseGuard_sound (externalEnsuresFalseGuard_of_uninhabited abortStub
    (fun e => nomatch e) rfl) (by decide) impl () trivial (fun _ h => h)).1
example : ¬ ContractHonest volatileRead (fun _ => some 0) := volatileRead_collapse 0

/-! ### Guard 4 -/

example : fnDefDupProg.mints = 2 := by decide
example : (TokStmt.repeatCtx .loopKw 3 .mintCall).mints = 3 := by decide
example : (TokStmt.repeatCtx .reentrantMain 2 (.seq .skip .mintCall)).mints = 2 := by decide
example : (TokStmt.repeatCtx .asyncBlock 2 .mintCall).mints = 2 := by decide
example : (TokStmt.seq .mintCall .skip).mints = 1 := by decide
example : UniqueAuthority (TokStmt.seq .mintCall .skip).mintedTokens :=
  fnDefGhostTokenGuard_unique_authority ⟨rfl, rfl, by decide⟩
example : ¬ FnDefGhostTokenGuard (.seq (.bindFnDef 0) .skip) :=
  fun h => absurd h.no_coercion (by decide)
example : ¬ FnDefGhostTokenGuard (.repeatCtx .closure 1 (.seq .skip .mintCall)) :=
  fun h => absurd h.no_repeat_mint (by decide)
example : ¬ UniqueAuthority (TokStmt.repeatCtx .forKw 2 .mintCall).mintedTokens :=
  repeatMint_soundness_collapse .forKw
example : ¬ UniqueAuthority (TokStmt.repeatCtx .genericDispatch 2 .mintCall).mintedTokens :=
  repeatMint_soundness_collapse .genericDispatch
example : (evalTok fnDefDupProg ([], 0)).2 = 2 := by decide
example : (evalTok (.seq (.callVar 0) (.bindFnDef 0)) ([], 0)).2 = 0 := by decide
example : UniqueAuthority (List.range (evalTok (.seq .mintCall .skip) ([], 0)).2) :=
  evalTok_unique_authority ⟨rfl, rfl, by decide⟩

/-! ### Guard 5 -/

def dropSpec (externalBody hasDropImpl opaqueField modelsDrop noDropGlue : Bool) :
    ExternalTypeDropSpec :=
  { externalTypeSpecification := true, externalBody := externalBody, hasDropImpl := hasDropImpl,
    opaqueForeignField := opaqueField, modelsDrop := modelsDrop, noDropGlue := noDropGlue }

example : ¬ ExternalTypeDropGuard (dropSpec true true false true false) :=
  externalBody_rejected_even_with_modelsDrop rfl rfl
example : ¬ ExternalTypeDropGuard (dropSpec true false true true false) :=
  externalBody_rejected_for_opaque_field_even_with_modelsDrop rfl rfl rfl
example : ¬ ExternalTypeDropGuard (dropSpec false false true false false) :=
  opaqueField_rejected_without_mitigation rfl rfl rfl
example : ExternalTypeDropGuard (dropSpec false true true true false) :=
  ⟨fun _ => rfl, fun _ => ⟨rfl, rfl⟩, fun _ => Or.inl rfl⟩
example : ExternalTypeDropGuard (dropSpec true false true false true) :=
  ⟨fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ => Or.inr rfl⟩
example : ¬ ResourceInv (verifierScopeExit (dropSpec true true false true false) true 1)
    (realScopeExit true 1) :=
  externalBodyDrop_soundness_collapse (s := dropSpec true true false true false)
    ⟨fun _ => Or.inl rfl, fun _ => rfl, fun h => absurd h (by decide)⟩ rfl rfl (by decide)
example : ResourceInv (verifierScopeExit (dropSpec false true true true false) true 3)
    (realScopeExit true 3) :=
  externalTypeDropGuard_preserves_inv ⟨fun _ => rfl, fun _ => ⟨rfl, rfl⟩, fun _ => Or.inl rfl⟩
    ⟨fun _ => Or.inl rfl, fun _ => rfl, fun h => absurd h (by decide)⟩ rfl

/-! ### Guard 6a -/

example : AssumptionPolarityGuard (.imp .assumesHold (.atom 0)) := by decide
example : AssumptionPolarityGuard (.imp (.and .assumesHold (.atom 1)) (.atom 0)) := by decide
example : AssumptionPolarityGuard (.not .assumesHold) := by decide
example : ¬ AssumptionPolarityGuard (.imp (.imp (.atom 1) (.not .assumesHold)) (.atom 0)) := by
  decide
example : AssumptionPolarityGuard (.imp (.imp (.atom 1) .assumesHold) (.atom 0)) := by decide
example : ¬ AssumptionPolarityGuard .assumesHold := by decide
example : ¬ AssumptionPolarityGuard (.imp (.imp .assumesHold (.atom 1)) (.atom 0)) := by decide
example : ¬ AssumptionPolarityGuard (.or (.not (.not .assumesHold)) (.atom 0)) := by decide
example : ¬ AssumptionPolarityGuard (.imp (.iff .assumesHold .tt) (.atom 0)) := by decide
example : ¬ AssumptionPolarityGuard (.imp (.ite .assumesHold .tt .ff) (.atom 0)) := by decide

/-- Inlining is bounded: nine bindings fail closed. -/
example : inlineLetAliases? (List.replicate 9 (0, .tt)) (.atom 0) = none := rfl
example : ¬ LetAssumptionPolarityGuard (List.replicate 9 (0, .tt)) (.atom 0) :=
  letAlias_depthExceeded_rejected (by decide)
example : inlineLetAliases? (List.replicate 8 (0, .tt)) (.atom 0) = some .tt := by decide
/-- A two-level alias chain is fully inlined before the polarity check. -/
example : ¬ LetAssumptionPolarityGuard [(0, .assumesHold), (1, .not (.not (.atom 0)))]
    (.and (.atom 1) (.atom 2)) := by
  rintro ⟨g, hg, hPol⟩
  simp [inlineLetAliases?, inlineLetAliases, substAtom, maxLetAliasDepth] at hg
  subst hg
  exact absurd hPol (by decide)
example : LetAssumptionPolarityGuard [(0, .assumesHold)] (.imp (.atom 0) (.atom 2)) :=
  ⟨.imp .assumesHold (.atom 2), by decide, by decide⟩

/-! ### Guard 6b -/

def evenDecl : StructDecl Nat := { inv := fun n => n % 2 = 0, ctorPrivate := true }

def evenSmart : PublicExport Nat :=
  { kind := .smartConstructor, build := fun n => some (2 * n), step := fun _ => none }

def evenAddTwo : PublicExport Nat :=
  { kind := .transform, build := fun _ => none, step := fun n => some (n + 2) }

def evenDefault : PublicExport Nat :=
  { kind := .derivingInhabited, build := fun _ => some 1, step := fun _ => none }

theorem evenGuard : StructSealingGuard evenDecl [evenSmart, evenAddTwo] := by
  refine ⟨rfl, ?_⟩
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · refine ⟨rfl, ?_, ?_⟩
    · intro r v h
      simp only [evenSmart, Option.some.injEq] at h
      subst h
      show 2 * r % 2 = 0
      omega
    · intro _ _ _ h
      cases h
  · refine ⟨rfl, ?_, ?_⟩
    · intro _ _ h
      cases h
    intro u v hu h
    simp only [evenAddTwo, Option.some.injEq] at h
    subst h
    show (u + 2) % 2 = 0
    have : u % 2 = 0 := hu
    omega

example : ClientReach (effectiveExports evenDecl [evenSmart, evenAddTwo]) [8, 6] :=
  .step evenAddTwo 6 8 (by simp [effectiveExports, evenDecl]) (by simp) rfl
    (.build evenSmart 3 6 (by simp [effectiveExports, evenDecl]) rfl .nil)

example {vs : List Nat} (h : ClientReach (effectiveExports evenDecl [evenSmart, evenAddTwo]) vs) :
    ∀ v ∈ vs, v % 2 = 0 :=
  structSealingGuard_inductive_soundness evenGuard h

example : ¬ StructSealingGuard evenDecl [evenSmart, evenDefault] :=
  leakKind_rejected (e := evenDefault) (by simp) rfl

example : ClientReach (effectiveExports evenDecl [evenDefault]) [1] ∧
    ¬ ∀ v ∈ [1], evenDecl.inv v :=
  leakyExport_soundness_collapse evenDecl [evenDefault] evenDefault (by simp) 0 1 rfl
    (by show ¬ (1 % 2 = 0); decide)

example : ClientReach (effectiveExports { evenDecl with ctorPrivate := false } []) [3] ∧
    ¬ ∀ v ∈ [3], (fun n : Nat => n % 2 = 0) v :=
  publicMk_soundness_collapse { evenDecl with ctorPrivate := false } [] rfl 3
    (by show ¬ (3 % 2 = 0); decide)

def evenBadStep : PublicExport Nat :=
  { kind := .transform, build := fun _ => none, step := fun n => some (n + 1) }

example : ClientReach (effectiveExports evenDecl [evenSmart, evenBadStep]) [7, 6] ∧
    ¬ ∀ v ∈ [7, 6], evenDecl.inv v :=
  leakyTransform_soundness_collapse evenDecl [evenSmart, evenBadStep] evenSmart evenBadStep
    (by simp) (by simp) 3 6 7 rfl rfl (by show ¬ (7 % 2 = 0); decide)

/-! ## 5. Axiom pins -/

end Anneal.InductiveReplayAndPeerSpecGuardsTests

open Anneal.InductiveReplayAndPeerSpecGuards

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.inductiveReplayWellFormed_rejects' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inductiveReplayWellFormed_rejects

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.inductiveReplayWellFormed_kernel_agreement' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inductiveReplayWellFormed_kernel_agreement

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.inductiveReplayWellFormed_kernel_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inductiveReplayWellFormed_kernel_exact

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.selfComparison_tautological' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selfComparison_tautological

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.forgedModule_gap_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forgedModule_gap_closed

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.preReplayOnly_misses_metadata_drift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms preReplayOnly_misses_metadata_drift

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.shardAxiomUnion_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shardAxiomUnion_sound

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.strictConstCompat_iff_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms strictConstCompat_iff_eq

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.naiveReconciliation_breaks_axiom_union' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms naiveReconciliation_breaks_axiom_union

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.exprHash64_collision' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms exprHash64_collision

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.externEnsuresFalse_soundness_collapse' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms externEnsuresFalse_soundness_collapse

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.externalEnsuresFalseGuard_sound' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms externalEnsuresFalseGuard_sound

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.fnDefCoercion_soundness_collapse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fnDefCoercion_soundness_collapse

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.fnDefGhostTokenGuard_unique_authority' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fnDefGhostTokenGuard_unique_authority

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.externalBodyDrop_soundness_collapse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms externalBodyDrop_soundness_collapse

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.externalTypeDropGuard_preserves_inv' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms externalTypeDropGuard_preserves_inv

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.evalPF_antitone_neg' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms evalPF_antitone_neg

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.evalPF_mono_pos' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms evalPF_mono_pos

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.evalPF_substAtom' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms evalPF_substAtom

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.assumptionsPolarityGuard_sound' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms assumptionsPolarityGuard_sound

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.letAssumptionPolarityGuard_sound' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms letAssumptionPolarityGuard_sound

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.structSealingGuard_inductive_soundness' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms structSealingGuard_inductive_soundness

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.CombinedSpecGuardClass.ofRank?_isSome_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CombinedSpecGuardClass.ofRank?_isSome_iff

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.PeerSpecGuardClass.wire_table' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms PeerSpecGuardClass.wire_table

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.inductiveReplayWellFormed_constNames_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inductiveReplayWellFormed_constNames_eq

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.hashReconciliation_breaks_axiom_union' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hashReconciliation_breaks_axiom_union

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.evalTok_unique_authority' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalTok_unique_authority

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.leakyTransform_soundness_collapse' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms leakyTransform_soundness_collapse

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.inductiveReplayWellFormed_family_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inductiveReplayWellFormed_family_iff

/-- info: 'Anneal.InductiveReplayAndPeerSpecGuards.subShardPartition_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms subShardPartition_sound
