-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Trusted
import Anneal.SpecRealizability
import Anneal.SpecBoundaryGuards

/-!
# Prototype Formalization: Forged-Inductive Replay, Sharded Audit, and Peer-Verifier Spec Guards

Isolated Track P prototype formalizing three verification-soundness pillars before
integration into `trusted/audit/`:

1. **Cross-Language Taxonomy Extension (`PeerSpecGuardClass`, ranks `3..6`)**:
   Extends `Anneal.SpecBoundaryGuards.SpecBoundaryGuardClass` (frozen ranks `0..2`)
   without duplication, adding wire-ID, canonical-name, rank-bijection, and disjointness
   proofs plus frozen violation codes for all three pillars.
2. **Pillar 1 — `lean4#16717` (`e6e25218c2ed`) Forged-Inductive Replay Integrity**:
   Models Lean 4.34.1 `Kernel.Environment.replay` (`vulnerableInductiveReplay`),
   exhibits concrete kernel-checked exploits (`FakeFalse` with `all := ["Unit"]` and
   forged `numIndices`/`isRec` metadata bypassing pre-`#16717` replay), defines the
   hardened structural + post-replay `checkPostponedInductives` checker
   (`checkInductiveReplayIntegrity` / `hardenedInductiveReplay`), proves rejection
   theorems for all 13 malformed variants (incl. postponed-recursor agreement), and proves
   `inductiveReplayWellFormed_sound`. The replay model faithfully mirrors 4.34.1's
   `remaining`-erasure order sensitivity and kernel "already declared" rejection.
3. **Pillar 2 — `grmf` cl/1029226310 `--exact-modules` Sharded Audit & `--orphan-only`**:
   Formalizes `ShardPartitionValid` and `ExactModulesShardAudit` with full cross-shard
   transitive dependency walks (`TransDep`), proves `shardPartitionCheck_iff_valid`,
   `shardAxiomUnion_sound`, a 3-shard cross-boundary chain refutation
   (`crossShardThreeHop_caught_by_shard1`), and unsoundness of naive shard-truncated
   or orphan-omitting audits.
4. **Pillar 3 — Four Peer-Verifier Spec-Boundary Soundness Guards**:
   - Guard 3 (`creusot#2388`, `unsatisfiable_extern_ensures`)
   - Guard 4 (`creusot#2389`, `fndef_ghost_token_coercion`)
   - Guard 5 (`verus#3514`, `external_type_drop_omission`)
   - Guard 6 (`Verifrag` cl/1029131309 assumption polarity + `checkCombCounterExample_sound`
     & `Samite` cl/1029680381 invariant-struct `private mk ::` sealing)

Every definition is safe, total, and pure-kernel; every theorem depends only on
`propext`, `Classical.choice`, and `Quot.sound`.
-/

namespace Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto

open Anneal.SpecRealizability
open Anneal.SpecBoundaryGuards

/-! ## 1. Cross-Language Wire Contract & Frozen Taxonomy Extension -/

/-! ### 1.1 `PeerSpecGuardClass` (Candidate Ranks `3..6`) -/

/-- The four peer-verifier specification-boundary guards extending
    `SpecBoundaryGuardClass` (ranks `0..2`) at candidate ranks `3..6`. -/
inductive PeerSpecGuardClass : Type where
  /-- Rank 3 (`creusot#2388`): non-diverging trusted extern/intrinsic spec with
      unsatisfiable `ensures` on satisfiable preconditions. -/
  | unsatisfiableExternEnsures
  /-- Rank 4 (`creusot#2389`): non-call `TyKind::FnDef` / closure / `fn()` coercion
      on a one-shot ghost-token constructor (`Tokens::new`, `#[ghost_token_ctor]`). -/
  | fndefGhostTokenCoercion
  /-- Rank 5 (`verus#3514`): `#[external_type_specification]` (or `external_body`
      combo) omitting modeled `Drop` / transitive drop glue. -/
  | externalTypeDropOmission
  /-- Rank 6 (`Verifrag` cl/1029131309 + `Samite` cl/1029680381): positive-polarity
      assumption placement in correspondence obligations and unsealed invariant-bearing
      Lean `structure` declarations lacking `private mk ::`. -/
  | assumptionPolarityAndStructSealing
  deriving DecidableEq, Repr, Inhabited

namespace PeerSpecGuardClass

/-- Canonical `snake_case` wire identifier (`guard_id`). -/
def guardId : PeerSpecGuardClass → String
  | .unsatisfiableExternEnsures => "unsatisfiable_extern_ensures"
  | .fndefGhostTokenCoercion => "fndef_ghost_token_coercion"
  | .externalTypeDropOmission => "external_type_drop_omission"
  | .assumptionPolarityAndStructSealing => "assumption_polarity_and_struct_sealing"

/-- Canonical diagnostic name (`canonical_name`). -/
def canonicalName : PeerSpecGuardClass → String
  | .unsatisfiableExternEnsures => "UnsatisfiableExternEnsures"
  | .fndefGhostTokenCoercion => "FnDefGhostTokenCoercion"
  | .externalTypeDropOmission => "ExternalTypeDropOmission"
  | .assumptionPolarityAndStructSealing => "AssumptionPolarityAndStructSealing"

/-- Mapping into Anneal's frozen 5-class `VacuityClass` taxonomy. -/
def toVacuityClass : PeerSpecGuardClass → VacuityClass
  | .unsatisfiableExternEnsures => .specViolation
  | .fndefGhostTokenCoercion => .specViolation
  | .externalTypeDropOmission => .specViolation
  | .assumptionPolarityAndStructSealing => .trivialPostcondition

/-- Candidate canonical rank (`3..6`), disjoint from `SpecBoundaryGuardClass` (`0..2`). -/
def rank : PeerSpecGuardClass → Nat
  | .unsatisfiableExternEnsures => 3
  | .fndefGhostTokenCoercion => 4
  | .externalTypeDropOmission => 5
  | .assumptionPolarityAndStructSealing => 6

/-- Inverse of `rank`; `none` for ranks `< 3` or `≥ 7`. -/
def ofRank? : Nat → Option PeerSpecGuardClass
  | 3 => some .unsatisfiableExternEnsures
  | 4 => some .fndefGhostTokenCoercion
  | 5 => some .externalTypeDropOmission
  | 6 => some .assumptionPolarityAndStructSealing
  | _ => none

/-- All four peer-verifier guards in canonical rank order `3..6`. -/
def all : List PeerSpecGuardClass :=
  [.unsatisfiableExternEnsures, .fndefGhostTokenCoercion,
    .externalTypeDropOmission, .assumptionPolarityAndStructSealing]

/-- Exact, case-sensitive parser for `guardId`. -/
def ofGuardId? (s : String) : Option PeerSpecGuardClass :=
  all.find? (fun g => g.guardId == s)

/-- Exact, case-sensitive parser for `canonicalName`. -/
def ofCanonicalName? (s : String) : Option PeerSpecGuardClass :=
  all.find? (fun g => g.canonicalName == s)

theorem ofGuardId?_guardId (g : PeerSpecGuardClass) : ofGuardId? g.guardId = some g := by
  cases g <;> rfl

theorem ofCanonicalName?_canonicalName (g : PeerSpecGuardClass) :
    ofCanonicalName? g.canonicalName = some g := by
  cases g <;> rfl

theorem guardId_injective {a b : PeerSpecGuardClass} (h : a.guardId = b.guardId) :
    a = b := by
  have hParse : ofGuardId? a.guardId = ofGuardId? b.guardId := congrArg ofGuardId? h
  rw [ofGuardId?_guardId, ofGuardId?_guardId] at hParse
  exact Option.some.inj hParse

theorem canonicalName_injective {a b : PeerSpecGuardClass}
    (h : a.canonicalName = b.canonicalName) : a = b := by
  have hParse : ofCanonicalName? a.canonicalName = ofCanonicalName? b.canonicalName :=
    congrArg ofCanonicalName? h
  rw [ofCanonicalName?_canonicalName, ofCanonicalName?_canonicalName] at hParse
  exact Option.some.inj hParse

theorem guardId_of_ofGuardId? {s : String} {g : PeerSpecGuardClass}
    (h : ofGuardId? s = some g) : g.guardId = s := by
  have hFound := List.find?_some h
  exact eq_of_beq hFound

theorem canonicalName_of_ofCanonicalName? {s : String} {g : PeerSpecGuardClass}
    (h : ofCanonicalName? s = some g) : g.canonicalName = s := by
  have hFound := List.find?_some h
  exact eq_of_beq hFound

theorem ofGuardId?_eq_some_iff {s : String} {g : PeerSpecGuardClass} :
    ofGuardId? s = some g ↔ g.guardId = s :=
  ⟨guardId_of_ofGuardId?, fun h => h ▸ ofGuardId?_guardId g⟩

theorem ofCanonicalName?_eq_some_iff {s : String} {g : PeerSpecGuardClass} :
    ofCanonicalName? s = some g ↔ g.canonicalName = s :=
  ⟨canonicalName_of_ofCanonicalName?, fun h => h ▸ ofCanonicalName?_canonicalName g⟩

theorem rank_bounds (g : PeerSpecGuardClass) : 3 ≤ g.rank ∧ g.rank < 7 := by
  cases g <;> decide

theorem ofRank?_rank (g : PeerSpecGuardClass) : ofRank? g.rank = some g := by
  cases g <;> rfl

theorem rank_injective {a b : PeerSpecGuardClass} (h : a.rank = b.rank) : a = b := by
  have hParse : ofRank? a.rank = ofRank? b.rank := congrArg ofRank? h
  rw [ofRank?_rank, ofRank?_rank] at hParse
  exact Option.some.inj hParse

theorem ofRank?_eq_none_of_lt_three {n : Nat} (h : n < 3) : ofRank? n = none := by
  match n, h with
  | 0, _ | 1, _ | 2, _ => rfl

theorem ofRank?_eq_none_of_ge_seven {n : Nat} (h : 7 ≤ n) : ofRank? n = none := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  rfl

theorem rank_of_ofRank? {n : Nat} {g : PeerSpecGuardClass} (h : ofRank? n = some g) :
    g.rank = n := by
  by_cases hLo : n < 3
  · rw [ofRank?_eq_none_of_lt_three hLo] at h; cases h
  · by_cases hHi : 7 ≤ n
    · rw [ofRank?_eq_none_of_ge_seven hHi] at h; cases h
    · have hMid : n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
      rcases hMid with rfl | rfl | rfl | rfl <;> (cases h; rfl)

theorem mem_all (g : PeerSpecGuardClass) : g ∈ all := by
  cases g <;> decide

theorem all_length : all.length = 4 := rfl

theorem all_nodup : all.Nodup := by decide

theorem all_map_rank : all.map rank = [3, 4, 5, 6] := by decide

/-- Disjointness from baseline `SpecBoundaryGuardClass` (`0..2`) on ranks. -/
theorem rank_ne_specBoundaryGuard (p : PeerSpecGuardClass) (b : SpecBoundaryGuardClass) :
    p.rank ≠ b.rank := by
  have hp := p.rank_bounds.1
  have hb := b.rank_lt_three
  omega

/-- Disjointness from baseline `SpecBoundaryGuardClass` on `guardId`. -/
theorem guardId_ne_specBoundaryGuard (p : PeerSpecGuardClass) (b : SpecBoundaryGuardClass) :
    p.guardId ≠ b.guardId := by
  cases p <;> cases b <;> decide

/-- Disjointness from baseline `SpecBoundaryGuardClass` on `canonicalName`. -/
theorem canonicalName_ne_specBoundaryGuard (p : PeerSpecGuardClass)
    (b : SpecBoundaryGuardClass) : p.canonicalName ≠ b.canonicalName := by
  cases p <;> cases b <;> decide

/-- Disjointness from `PropertyClassTag` wire identifiers. -/
theorem guardId_ne_propertyClass (p : PeerSpecGuardClass) (c : PropertyClassTag) :
    p.guardId ≠ c.asStr := by
  cases p <;> cases c <;> decide

/-- Guard wire identifiers and canonical diagnostic names never collide. -/
theorem guardId_ne_canonicalName (a b : PeerSpecGuardClass) :
    a.guardId ≠ b.canonicalName := by
  cases a <;> cases b <;> decide

/-- Every mapped vacuity class lies in the frozen 5-class `VacuityClass` taxonomy. -/
theorem toVacuityClass_mem_all (g : PeerSpecGuardClass) :
    g.toVacuityClass ∈ VacuityClass.all :=
  VacuityClass.mem_all g.toVacuityClass

/-- Frozen `(rank, guard_id, canonical_name, vacuity_class)` wire table matching Python. -/
theorem wire_table :
    all.map (fun g => (g.rank, g.guardId, g.canonicalName, g.toVacuityClass.canonicalName)) =
      [(3, "unsatisfiable_extern_ensures", "UnsatisfiableExternEnsures", "SpecViolation"),
        (4, "fndef_ghost_token_coercion", "FnDefGhostTokenCoercion", "SpecViolation"),
        (5, "external_type_drop_omission", "ExternalTypeDropOmission", "SpecViolation"),
        (6, "assumption_polarity_and_struct_sealing",
          "AssumptionPolarityAndStructSealing", "TrivialPostcondition")] :=
  rfl

end PeerSpecGuardClass

/-! ### 1.2 Frozen Violation Codes Across All Three Pillars -/

/-- All 13 forged-inductive replay violation codes (`lean4#16717` + postponed-recursor
    agreement, which Lean 4.34.1 `checkPostponedRecursors` already enforces and which the
    hardened checker must therefore never weaken). -/
inductive InductiveReplayViolationCode : Type where
  | keyMismatch
  | selfNotInAll
  | duplicateInAll
  | nonInductInAll
  | mutualMetadataMismatch
  | duplicateInCtors
  | nonCtorInCtors
  | ctorInductMismatch
  | ctorCidxMismatch
  | danglingCtorNotListedInInduct
  | indicesMismatch
  | isRecMismatch
  | recursorMismatch
  deriving DecidableEq, Repr, Inhabited

namespace InductiveReplayViolationCode

def asStr : InductiveReplayViolationCode → String
  | .keyMismatch => "key_mismatch"
  | .selfNotInAll => "self_not_in_all"
  | .duplicateInAll => "duplicate_in_all"
  | .nonInductInAll => "non_induct_in_all"
  | .mutualMetadataMismatch => "mutual_metadata_mismatch"
  | .duplicateInCtors => "duplicate_in_ctors"
  | .nonCtorInCtors => "non_ctor_in_ctors"
  | .ctorInductMismatch => "ctor_induct_mismatch"
  | .ctorCidxMismatch => "ctor_cidx_mismatch"
  | .danglingCtorNotListedInInduct => "dangling_ctor_not_listed_in_induct"
  | .indicesMismatch => "indices_mismatch"
  | .isRecMismatch => "is_rec_mismatch"
  | .recursorMismatch => "recursor_mismatch"

def all : List InductiveReplayViolationCode :=
  [.keyMismatch, .selfNotInAll, .duplicateInAll, .nonInductInAll,
    .mutualMetadataMismatch, .duplicateInCtors, .nonCtorInCtors,
    .ctorInductMismatch, .ctorCidxMismatch, .danglingCtorNotListedInInduct,
    .indicesMismatch, .isRecMismatch, .recursorMismatch]

def ofStr? (s : String) : Option InductiveReplayViolationCode :=
  all.find? (fun c => c.asStr == s)

theorem ofStr?_asStr (c : InductiveReplayViolationCode) : ofStr? c.asStr = some c := by
  cases c <;> rfl

theorem asStr_injective {a b : InductiveReplayViolationCode} (h : a.asStr = b.asStr) :
    a = b := by
  have hP := congrArg ofStr? h
  rw [ofStr?_asStr, ofStr?_asStr] at hP
  exact Option.some.inj hP

theorem all_length : all.length = 13 := rfl

theorem all_nodup : all.Nodup := by decide

end InductiveReplayViolationCode

/-- All 10 sharded-audit and orphan-gate violation codes (`grmf` cl/1029226310), including
    case-folding module-name collisions that alias one `.lean`/`.olean` path on
    case-insensitive filesystems. -/
inductive ShardAuditViolationCode : Type where
  | emptyShardList
  | emptyShard
  | duplicateModuleInShard
  | overlappingShards
  | unregisteredModuleInShard
  | uncoveredRegisteredModule
  | unregisteredOnDiskOrphan
  | disallowedTransitiveAxiom
  | missingDependencyDecl
  | moduleNameCollision
  | crossShardDuplicateConflict
  deriving DecidableEq, Repr, Inhabited

namespace ShardAuditViolationCode

def asStr : ShardAuditViolationCode → String
  | .emptyShardList => "empty_shard_list"
  | .emptyShard => "empty_shard"
  | .duplicateModuleInShard => "duplicate_module_in_shard"
  | .overlappingShards => "overlapping_shards"
  | .unregisteredModuleInShard => "unregistered_module_in_shard"
  | .uncoveredRegisteredModule => "uncovered_registered_module"
  | .unregisteredOnDiskOrphan => "unregistered_on_disk_orphan"
  | .disallowedTransitiveAxiom => "disallowed_transitive_axiom"
  | .missingDependencyDecl => "missing_dependency_decl"
  | .moduleNameCollision => "module_name_collision"
  | .crossShardDuplicateConflict => "cross_shard_duplicate_conflict"

def all : List ShardAuditViolationCode :=
  [.emptyShardList, .emptyShard, .duplicateModuleInShard, .overlappingShards,
    .unregisteredModuleInShard, .uncoveredRegisteredModule,
    .unregisteredOnDiskOrphan, .disallowedTransitiveAxiom, .missingDependencyDecl,
    .moduleNameCollision, .crossShardDuplicateConflict]

def ofStr? (s : String) : Option ShardAuditViolationCode :=
  all.find? (fun c => c.asStr == s)

theorem ofStr?_asStr (c : ShardAuditViolationCode) : ofStr? c.asStr = some c := by
  cases c <;> rfl

theorem asStr_injective {a b : ShardAuditViolationCode} (h : a.asStr = b.asStr) :
    a = b := by
  have hP := congrArg ofStr? h
  rw [ofStr?_asStr, ofStr?_asStr] at hP
  exact Option.some.inj hP

theorem all_length : all.length = 11 := rfl

end ShardAuditViolationCode

/-- Frozen violation codes emitted by the four peer-verifier spec guards. -/
inductive PeerGuardViolationCode : Type where
  | unsatisfiableExternEnsures
  | fndefGhostTokenCoercion
  | externalTypeDropOmission
  | externalTypeBodyWithDrop
  | assumptionPositivePolarity
  | unsealedInvariantStruct
  deriving DecidableEq, Repr, Inhabited

namespace PeerGuardViolationCode

def asStr : PeerGuardViolationCode → String
  | .unsatisfiableExternEnsures => "unsatisfiable_extern_ensures"
  | .fndefGhostTokenCoercion => "fndef_ghost_token_coercion"
  | .externalTypeDropOmission => "external_type_drop_omission"
  | .externalTypeBodyWithDrop => "external_type_body_with_drop"
  | .assumptionPositivePolarity => "assumption_positive_polarity"
  | .unsealedInvariantStruct => "unsealed_invariant_struct"

def guardClass : PeerGuardViolationCode → PeerSpecGuardClass
  | .unsatisfiableExternEnsures => .unsatisfiableExternEnsures
  | .fndefGhostTokenCoercion => .fndefGhostTokenCoercion
  | .externalTypeDropOmission => .externalTypeDropOmission
  | .externalTypeBodyWithDrop => .externalTypeDropOmission
  | .assumptionPositivePolarity => .assumptionPolarityAndStructSealing
  | .unsealedInvariantStruct => .assumptionPolarityAndStructSealing

def all : List PeerGuardViolationCode :=
  [.unsatisfiableExternEnsures, .fndefGhostTokenCoercion,
    .externalTypeDropOmission, .externalTypeBodyWithDrop,
    .assumptionPositivePolarity, .unsealedInvariantStruct]

def ofStr? (s : String) : Option PeerGuardViolationCode :=
  all.find? (fun c => c.asStr == s)

theorem ofStr?_asStr (c : PeerGuardViolationCode) : ofStr? c.asStr = some c := by
  cases c <;> rfl

theorem asStr_injective {a b : PeerGuardViolationCode} (h : a.asStr = b.asStr) :
    a = b := by
  have hP := congrArg ofStr? h
  rw [ofStr?_asStr, ofStr?_asStr] at hP
  exact Option.some.inj hP

theorem all_length : all.length = 6 := rfl

end PeerGuardViolationCode

/-! ## 2. Pillar 1 — `lean4#16717` (`e6e25218c2ed`) Forged-Inductive Replay Integrity -/

/-- Pure-kernel model of `Lean.InductiveVal` metadata stored in a `.olean` `ConstantInfo`. -/
structure SimInductVal : Type where
  name : String
  levelParams : List String
  typeTag : String
  numParams : Nat
  numIndices : Nat
  all : List String
  ctors : List String
  isRec : Bool
  isReflexive : Bool
  isUnsafe : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Pure-kernel model of `Lean.ConstructorVal` metadata stored in a `.olean` `ConstantInfo`. -/
structure SimCtorVal : Type where
  name : String
  levelParams : List String
  typeTag : String
  induct : String
  cidx : Nat
  numParams : Nat
  numFields : Nat
  isUnsafe : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Pure-kernel model of `Lean.RecursorVal` metadata (every field compared by Lean 4.34.1
    `checkPostponedRecursors` via `RecursorVal` `BEq`). -/
structure SimRecVal : Type where
  name : String
  levelParams : List String
  typeTag : String
  all : List String
  numParams : Nat
  numIndices : Nat
  numMotives : Nat
  numMinors : Nat
  ruleCtors : List String
  k : Bool
  isUnsafe : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Pure-kernel model of `Lean.ConstantInfo`. -/
inductive SimConstInfo : Type where
  | induct (v : SimInductVal)
  | ctor (v : SimCtorVal)
  | recInfo (v : SimRecVal)
  | defn (name : String) (typeTag : String)
  | thm (name : String) (typeTag : String)
  deriving DecidableEq, Repr, Inhabited

/-- Stored declaration name inside a `SimConstInfo`. -/
def SimConstInfo.constName : SimConstInfo → String
  | .induct v => v.name
  | .ctor v => v.name
  | .recInfo v => v.name
  | .defn n _ => n
  | .thm n _ => n

/-- Association-list constant map modeling `Std.HashMap Name ConstantInfo`. -/
abbrev SimConstMap := List (String × SimConstInfo)

/-- Lookup a constant by map key. -/
def lookupConst (m : SimConstMap) (k : String) : Option SimConstInfo :=
  (m.find? (fun p => p.1 == k)).map Prod.snd

theorem lookupConst_eq_some_mem {m : SimConstMap} {k : String} {ci : SimConstInfo}
    (h : lookupConst m k = some ci) : (k, ci) ∈ m := by
  unfold lookupConst at h
  cases hF : m.find? (fun p => p.1 == k) with
  | none => rw [hF] at h; cases h
  | some p =>
    rw [hF] at h
    cases h
    have hMem := List.mem_of_find?_eq_some hF
    have hEq : p.1 = k := eq_of_beq (by simpa using List.find?_some hF)
    cases p
    simp only at hEq
    subst hEq
    exact hMem

/-- Request sent to `Declaration.inductDecl` during replay. -/
structure KernelInductDeclReq : Type where
  levelParams : List String
  numParams : Nat
  types : List (String × String × List (String × String))
  deriving DecidableEq, Repr

/-- Result produced by the kernel when accepting an inductive declaration block:
    the canonical `SimInductVal`s and `SimCtorVal`s generated by the kernel. -/
structure KernelInductOutput : Type where
  inducts : List SimInductVal
  ctors : List SimCtorVal
  recs : List SimRecVal
  deriving DecidableEq, Repr

/-- Abstract kernel oracle modeling `Kernel.Environment.addDeclCore` for inductive blocks. -/
abbrev KernelInductOracle := KernelInductDeclReq → Option KernelInductOutput

/-- Check whether a list of strings has no duplicate entries (computable). -/
def hasNoDupStrings : List String → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && hasNoDupStrings xs

theorem hasNoDupStrings_eq_true_iff (xs : List String) :
    hasNoDupStrings xs = true ↔ xs.Nodup := by
  induction xs with
  | nil => simp [hasNoDupStrings]
  | cons x xs ih =>
    simp [hasNoDupStrings, ih, List.nodup_cons]

/-- Structural violation record emitted by `checkInductiveReplayIntegrity`. -/
structure InductiveReplayViolation : Type where
  code : InductiveReplayViolationCode
  subject : String
  detail : String
  deriving DecidableEq, Repr

/-- Check constructor list entries of an inductive against `newConstants`. -/
def checkCtorList (m : SimConstMap) (ind : SimInductVal) :
    Nat → List String → List InductiveReplayViolation
  | _, [] => []
  | idx, c :: rest =>
    let here :=
      match lookupConst m c with
      | some (.ctor cVal) =>
        let vInduct :=
          if cVal.induct != ind.name || cVal.numParams != ind.numParams ||
              cVal.levelParams != ind.levelParams then
            [{ code := .ctorInductMismatch, subject := ind.name, detail := c }]
          else []
        let vCidx :=
          if cVal.cidx != idx then
            [{ code := .ctorCidxMismatch, subject := ind.name, detail := c }]
          else []
        vInduct ++ vCidx
      | _ =>
        [{ code := .nonCtorInCtors, subject := ind.name, detail := c }]
    here ++ checkCtorList m ind (idx + 1) rest

/-- Check mutual-block `all` entries of an inductive against `newConstants`. -/
def checkAllList (m : SimConstMap) (ind : SimInductVal) :
    List String → List InductiveReplayViolation
  | [] => []
  | n :: rest =>
    let here :=
      match lookupConst m n with
      | some (.induct peer) =>
        if peer.all != ind.all || peer.levelParams != ind.levelParams ||
            peer.numParams != ind.numParams || peer.isReflexive != ind.isReflexive ||
            peer.isRec != ind.isRec then
          [{ code := .mutualMetadataMismatch, subject := ind.name, detail := n }]
        else []
      | _ =>
        [{ code := .nonInductInAll, subject := ind.name, detail := n }]
    here ++ checkAllList m ind rest

/-- Static pre-replay structural integrity checks over all entries in `newConstants`
    (closing the pre-`lean4#16717` blind spots on `info.all`, `info.ctors`, keys,
    mutual metadata, and dangling `.ctorInfo`s). -/
def checkStaticInductiveIntegrity (m : SimConstMap) : List InductiveReplayViolation :=
  let dupKeyViol :=
    if hasNoDupStrings (m.map Prod.fst) then []
    else [{ code := .keyMismatch, subject := "<map>", detail := "duplicate_key" }]
  let entryViols := m.flatMap fun (k, ci) =>
    let vKey :=
      if ci.constName != k then
        [{ code := .keyMismatch, subject := k, detail := ci.constName }]
      else []
    let vBody :=
      match ci with
      | .induct ind =>
        let vSelf :=
          if !ind.all.contains ind.name then
            [{ code := .selfNotInAll, subject := ind.name, detail := "missing_self" }]
          else []
        let vDupAll :=
          if !hasNoDupStrings ind.all then
            [{ code := .duplicateInAll, subject := ind.name, detail := "duplicate_all" }]
          else []
        let vAllEntries := checkAllList m ind ind.all
        let vDupCtors :=
          if !hasNoDupStrings ind.ctors then
            [{ code := .duplicateInCtors, subject := ind.name, detail := "duplicate_ctors" }]
          else []
        let vCtorEntries := checkCtorList m ind 0 ind.ctors
        vSelf ++ vDupAll ++ vAllEntries ++ vDupCtors ++ vCtorEntries
      | .ctor cVal =>
        match lookupConst m cVal.induct with
        | some (.induct parent) =>
          if parent.ctors.contains cVal.name then []
          else [{ code := .danglingCtorNotListedInInduct, subject := cVal.name, detail := cVal.induct }]
        | _ =>
          [{ code := .danglingCtorNotListedInInduct, subject := cVal.name, detail := cVal.induct }]
      | .recInfo rVal =>
        let vEmpty :=
          if rVal.all.isEmpty then
            [{ code := .recursorMismatch, subject := rVal.name, detail := "empty_rec_all" }]
          else []
        let vPeers := rVal.all.flatMap fun n =>
          match lookupConst m n with
          | some (.induct parent) =>
            if parent.all != rVal.all || parent.numParams != rVal.numParams then
              [{ code := .recursorMismatch, subject := rVal.name, detail := n }]
            else []
          | _ =>
            [{ code := .recursorMismatch, subject := rVal.name, detail := n }]
        vEmpty ++ vPeers
      | _ => []
    vKey ++ vBody
  dupKeyViol ++ entryViols

/-- Post-replay `checkPostponedInductives` (`lean4#16717` fix): compares every `.induct`
    entry in `newConstants` field-for-field against the kernel-generated `SimInductVal`
    stored in `kernelEnv`. -/
def checkPostponedInductives (m : SimConstMap) (kernelEnv : SimConstMap) :
    List InductiveReplayViolation :=
  m.flatMap fun (_, ci) =>
    match ci with
    | .induct info =>
      match lookupConst kernelEnv info.name with
      | some (.induct kInfo) =>
        let vIdx :=
          if kInfo.numIndices != info.numIndices then
            [{ code := .indicesMismatch, subject := info.name, detail := "numIndices" }]
          else []
        let vRec :=
          if kInfo.isRec != info.isRec then
            [{ code := .isRecMismatch, subject := info.name, detail := "isRec" }]
          else []
        let vMeta :=
          if kInfo.name != info.name || kInfo.levelParams != info.levelParams ||
              kInfo.typeTag != info.typeTag || kInfo.numParams != info.numParams ||
              kInfo.all != info.all || kInfo.ctors != info.ctors ||
              kInfo.isReflexive != info.isReflexive || kInfo.isUnsafe != info.isUnsafe then
            [{ code := .mutualMetadataMismatch, subject := info.name, detail := "post_replay_diff" }]
          else []
        vIdx ++ vRec ++ vMeta
      | _ =>
        [{ code := .selfNotInAll, subject := info.name, detail := "not_replayed_in_kernel" }]
    | _ => []

/-- Post-replay `checkPostponedConstructors`: compares every `.ctor` entry in
    `newConstants` against the kernel-generated `SimCtorVal` in `kernelEnv`. -/
def checkPostponedConstructors (m : SimConstMap) (kernelEnv : SimConstMap) :
    List InductiveReplayViolation :=
  m.flatMap fun (_, ci) =>
    match ci with
    | .ctor cInfo =>
      match lookupConst kernelEnv cInfo.name with
      | some (.ctor kCtor) =>
        if kCtor == cInfo then []
        else if kCtor.cidx != cInfo.cidx then
          [{ code := .ctorCidxMismatch, subject := cInfo.name, detail := "post_replay_cidx" }]
        else
          [{ code := .ctorInductMismatch, subject := cInfo.name, detail := "post_replay_ctor_diff" }]
      | _ =>
        [{ code := .danglingCtorNotListedInInduct, subject := cInfo.name, detail := "ctor_not_in_kernel" }]
    | _ => []

/-- Post-replay `checkPostponedRecursors` (already present in Lean 4.34.1 `Replay.lean`):
    compares every `.recInfo` entry in `newConstants` field-for-field (`RecursorVal` `BEq`)
    against the kernel-generated `SimRecVal` in `kernelEnv`. -/
def checkPostponedRecursors (m : SimConstMap) (kernelEnv : SimConstMap) :
    List InductiveReplayViolation :=
  m.flatMap fun (_, ci) =>
    match ci with
    | .recInfo rInfo =>
      match lookupConst kernelEnv rInfo.name with
      | some (.recInfo kRec) =>
        if kRec == rInfo then []
        else [{ code := .recursorMismatch, subject := rInfo.name, detail := "post_replay_rec_diff" }]
      | _ =>
        [{ code := .recursorMismatch, subject := rInfo.name, detail := "rec_not_in_kernel" }]
    | _ => []

/-- Full `lean4#16717` integrity checker combining static pre-replay checks and
    post-replay postponed-inductive + postponed-constructor + postponed-recursor checks. -/
def checkInductiveReplayIntegrity (m : SimConstMap) (kernelEnv : SimConstMap) :
    List InductiveReplayViolation :=
  checkStaticInductiveIntegrity m ++
    checkPostponedInductives m kernelEnv ++
    checkPostponedConstructors m kernelEnv ++
    checkPostponedRecursors m kernelEnv

/-! ### 2.1 Pre-`#16717` Vulnerable Replay Model & Concrete Exploit Witnesses -/

/-- Insert a constant into a `SimConstMap` (shadowing or appending if absent). -/
def insertConst (env : SimConstMap) (k : String) (ci : SimConstInfo) : SimConstMap :=
  (k, ci) :: env.filter (fun p => p.1 != k)

/-- Build the `KernelInductDeclReq` that Lean 4.34.1 `Replay.lean` constructs when
    replaying `.inductInfo info`: it iterates ONLY over `info.all` (trusting `info.all`
    blindly without checking `info.name ∈ info.all`!). A missing/non-inductive `all`
    member or non-constructor `ctors` member models the `newConstants[n]!` /
    `inductiveVal!` panic as a replay error. -/
def buildReplayInductReq (m : SimConstMap) (info : SimInductVal) : Option KernelInductDeclReq := do
  let types ← info.all.mapM fun n => do
    match lookupConst m n with
    | some (.induct peer) =>
      let ctors ← peer.ctors.mapM fun c => do
        match lookupConst m c with
        | some (.ctor cVal) => some (cVal.name, cVal.typeTag)
        | _ => none
      some (peer.name, peer.typeTag, ctors)
    | _ => none
  some { levelParams := info.levelParams, numParams := info.numParams, types := types }

/-- Replay state mirroring Lean 4.34.1 `Replay.State` (`remaining` + kernel `env`).
    `pending` is subsumed because dependency pre-replay is abstracted away: a name is
    processed exactly when it is still in `remaining` at the moment it is visited. -/
structure ReplayState : Type where
  remaining : List String
  env : SimConstMap
  deriving Repr

/-- Insert every kernel-generated inductive, constructor, and recursor into `env`. -/
def insertKernelOutput (env : SimConstMap) (out : KernelInductOutput) : SimConstMap :=
  let env1 := out.inducts.foldl (fun e iv => insertConst e iv.name (.induct iv)) env
  let env2 := out.ctors.foldl (fun e cv => insertConst e cv.name (.ctor cv)) env1
  out.recs.foldl (fun e rv => insertConst e rv.name (.recInfo rv)) env2

/-- Faithful model of Lean 4.34.1 `Replay.lean` `replayConstant` (lines 74-141):
    - `isTodo k`: skip `k` unless it is still in `remaining`; otherwise erase it.
    - `.inductInfo info`: erase EVERY `n ∈ info.all` from `remaining` (so peers are never
      revisited), build the `inductDecl` from `info.all` ONLY (never `info.name`!), and
      send it to the kernel, which rejects any already-declared type name
      (`addDeclCore` "already declared").
    - `.ctorInfo` / `.recInfo`: postponed (checked at the end).
    - `.defnInfo` / `.thmInfo`: abstracted as accepted by the kernel.
    There is **no** `checkPostponedInductives`. -/
def replayLoop (oracle : KernelInductOracle) (m : SimConstMap) :
    List String → ReplayState → Except String ReplayState
  | [], st => .ok st
  | k :: rest, st =>
    if !st.remaining.contains k then
      replayLoop oracle m rest st
    else
      let st := { st with remaining := st.remaining.filter (· != k) }
      match lookupConst m k with
      | none => replayLoop oracle m rest st
      | some (.induct info) =>
        let st := { st with remaining := st.remaining.filter (fun n => !info.all.contains n) }
        match buildReplayInductReq m info with
        | none => .error s!"malformed induct req for {k}"
        | some req =>
          if req.types.any (fun t => (lookupConst st.env t.1).isSome) then
            .error s!"kernel: already declared while replaying {k}"
          else
            match oracle req with
            | none => .error s!"kernel rejected induct req for {k}"
            | some out =>
              replayLoop oracle m rest { st with env := insertKernelOutput st.env out }
      | some (.ctor _) => replayLoop oracle m rest st
      | some (.recInfo _) => replayLoop oracle m rest st
      | some (.defn n t) =>
        replayLoop oracle m rest { st with env := insertConst st.env n (.defn n t) }
      | some (.thm n t) =>
        replayLoop oracle m rest { st with env := insertConst st.env n (.thm n t) }

/-- Run `replayLoop` over `keys` (iteration order of Lean's `NameSet`) starting from
    `remaining := keys` and kernel environment `env`. -/
def vulnerableReplayStep (oracle : KernelInductOracle) (m : SimConstMap)
    (keys : List String) (env : SimConstMap) : Except String SimConstMap :=
  (replayLoop oracle m keys { remaining := keys, env := env }).map ReplayState.env

/-- Pre-`#16717` vulnerable replay (Lean 4.34.1): replays constants, then checks
    postponed constructors AND postponed recursors, but has no static `info.all` /
    `info.ctors` integrity checks and no `checkPostponedInductives`. -/
def vulnerableInductiveReplay (oracle : KernelInductOracle) (m : SimConstMap) :
    Except String SimConstMap := do
  let env ← vulnerableReplayStep oracle m (m.map Prod.fst) []
  if !(checkPostponedConstructors m env).isEmpty then
    .error "postponed constructor mismatch"
  else if !(checkPostponedRecursors m env).isEmpty then
    .error "postponed recursor mismatch"
  else
    .ok env

/-- Post-`#16717` hardened replay: enforces static structural checks BEFORE replay,
    runs kernel replay, and enforces `checkPostponedInductives`,
    `checkPostponedConstructors`, AND `checkPostponedRecursors` afterward. -/
def hardenedInductiveReplay (oracle : KernelInductOracle) (m : SimConstMap) :
    Except (List InductiveReplayViolation) SimConstMap :=
  let staticViols := checkStaticInductiveIntegrity m
  if !staticViols.isEmpty then
    .error staticViols
  else
    match vulnerableReplayStep oracle m (m.map Prod.fst) [] with
    | .error msg =>
      .error [{ code := .mutualMetadataMismatch, subject := "<kernel>", detail := msg }]
    | .ok env =>
      let postViols := checkPostponedInductives m env ++ checkPostponedConstructors m env ++
        checkPostponedRecursors m env
      if postViols.isEmpty then .ok env
      else .error postViols

/-! ### 2.2 Concrete Kernel Oracle and Exploit Witnesses -/

/-- Canonical `Unit` inductive value generated by the kernel. -/
def unitInductVal : SimInductVal :=
  { name := "Unit", levelParams := [], typeTag := "Type", numParams := 0,
    numIndices := 0, all := ["Unit"], ctors := ["Unit.unit"],
    isRec := false, isReflexive := false }

/-- Canonical `Unit.unit` constructor value generated by the kernel. -/
def unitCtorVal : SimCtorVal :=
  { name := "Unit.unit", levelParams := [], typeTag := "Unit",
    induct := "Unit", cidx := 0, numParams := 0, numFields := 0 }

/-- Canonical `Unit.rec` recursor generated by the kernel. -/
def unitRecVal : SimRecVal :=
  { name := "Unit.rec", levelParams := ["u"], typeTag := "Unit.rec.type", all := ["Unit"],
    numParams := 0, numIndices := 0, numMotives := 1, numMinors := 1,
    ruleCtors := ["Unit.unit"], k := true }

/-- Canonical `Nat` recursive inductive value generated by the kernel. -/
def natInductVal : SimInductVal :=
  { name := "Nat", levelParams := [], typeTag := "Type", numParams := 0,
    numIndices := 0, all := ["Nat"], ctors := ["Nat.zero", "Nat.succ"],
    isRec := true, isReflexive := false }

def natZeroCtorVal : SimCtorVal :=
  { name := "Nat.zero", levelParams := [], typeTag := "Nat",
    induct := "Nat", cidx := 0, numParams := 0, numFields := 0 }

def natSuccCtorVal : SimCtorVal :=
  { name := "Nat.succ", levelParams := [], typeTag := "Nat -> Nat",
    induct := "Nat", cidx := 1, numParams := 0, numFields := 1 }

/-- Canonical `Nat.rec` recursor generated by the kernel. -/
def natRecVal : SimRecVal :=
  { name := "Nat.rec", levelParams := ["u"], typeTag := "Nat.rec.type", all := ["Nat"],
    numParams := 0, numIndices := 0, numMotives := 1, numMinors := 2,
    ruleCtors := ["Nat.zero", "Nat.succ"], k := false }

/-- Concrete demo kernel oracle accepting canonical `Unit` and `Nat` declarations and
    generating their inductive, constructor, and recursor values. -/
def demoKernelOracle : KernelInductOracle
  | { levelParams := [], numParams := 0, types := [("Unit", "Type", [("Unit.unit", "Unit")])] } =>
    some { inducts := [unitInductVal], ctors := [unitCtorVal], recs := [unitRecVal] }
  | { levelParams := [], numParams := 0,
      types := [("Nat", "Type", [("Nat.zero", "Nat"), ("Nat.succ", "Nat -> Nat")])] } =>
    some { inducts := [natInductVal]
           ctors := [natZeroCtorVal, natSuccCtorVal]
           recs := [natRecVal] }
  | _ => none

/-- **Pre-`#16717` Exploit #1 (`selfNotInAll`)**: `FakeFalse : Prop` has `ctors := []`
    and `all := ["Unit"]`, omitting itself from `all`. -/
def fakeFalseInductVal : SimInductVal :=
  { name := "FakeFalse", levelParams := [], typeTag := "Prop", numParams := 0,
    numIndices := 0, all := ["Unit"], ctors := [],
    isRec := false, isReflexive := false }

/-- Exploit map whose `NameSet` iteration order visits `FakeFalse` BEFORE `Unit`
    (attackers choose names so `Name.quickCmp` orders them this way). Replaying
    `FakeFalse` erases `Unit` from `remaining` and sends ONLY `Unit` to the kernel. -/
def fakeFalseExploitMap : SimConstMap :=
  [("FakeFalse", .induct fakeFalseInductVal),
   ("Unit", .induct unitInductVal),
   ("Unit.unit", .ctor unitCtorVal)]

/-- **Exploit Witness 1**: `fakeFalseExploitMap` PASSES pre-`#16717`
    `vulnerableInductiveReplay` (faithful `remaining`-erasure model), yet `"FakeFalse"`
    is NEVER added to or checked by the kernel environment! -/
theorem fakeFalse_passes_vulnerableInductiveReplay :
    ∃ env, vulnerableInductiveReplay demoKernelOracle fakeFalseExploitMap = .ok env ∧
      lookupConst env "FakeFalse" = none ∧
      lookupConst env "Unit" = some (.induct unitInductVal) ∧
      lookupConst fakeFalseExploitMap "FakeFalse" = some (.induct fakeFalseInductVal) :=
  ⟨_, rfl, rfl, rfl, rfl⟩

/-- **Model Fidelity (order sensitivity)**: if `Unit` is visited BEFORE `FakeFalse`, the
    real kernel rejects the second `inductDecl [Unit]` as "already declared", so the
    exploit only works when `FakeFalse` precedes its `all` targets. A model that silently
    skips already-replayed `all` blocks would overstate the attack surface. -/
def fakeFalseUnitFirstMap : SimConstMap :=
  [("Unit", .induct unitInductVal),
   ("Unit.unit", .ctor unitCtorVal),
   ("FakeFalse", .induct fakeFalseInductVal)]

theorem fakeFalse_unitFirst_rejected_by_vulnerable_kernel :
    ∃ msg, vulnerableInductiveReplay demoKernelOracle fakeFalseUnitFirstMap = .error msg :=
  ⟨_, rfl⟩

/-- **Model Fidelity (postponed recursors)**: Lean 4.34.1 already runs
    `checkPostponedRecursors`, so an attacker who also ships the eliminator
    `FakeFalse.rec` (needed to derive `False` from `FakeFalse`) is rejected even by the
    VULNERABLE replay: the kernel never generated `FakeFalse.rec`. -/
def fakeFalseRecVal : SimRecVal :=
  { name := "FakeFalse.rec", levelParams := [], typeTag := "FakeFalse.rec.type",
    all := ["FakeFalse"], numParams := 0, numIndices := 0, numMotives := 1, numMinors := 0,
    ruleCtors := [], k := false }

def fakeFalseWithRecExploitMap : SimConstMap :=
  fakeFalseExploitMap ++ [("FakeFalse.rec", .recInfo fakeFalseRecVal)]

theorem fakeFalseWithRec_rejected_by_vulnerable_postponedRecursors :
    vulnerableInductiveReplay demoKernelOracle fakeFalseWithRecExploitMap =
      .error "postponed recursor mismatch" :=
  rfl

/-- **Fix Witness 1**: `hardenedInductiveReplay` REJECTS `fakeFalseExploitMap` with
    `selfNotInAll`! -/
theorem fakeFalse_rejected_by_hardenedInductiveReplay :
    ∃ vs, hardenedInductiveReplay demoKernelOracle fakeFalseExploitMap = .error vs ∧
      vs.any (fun v => v.code == .selfNotInAll && v.subject == "FakeFalse") = true :=
  ⟨checkStaticInductiveIntegrity fakeFalseExploitMap, rfl, by decide⟩

/-- **Pre-`#16717` Exploit #2 (`indicesMismatch` & `isRecMismatch`)**: `Nat` stored in
    `newConstants` lies about `numIndices := 1` and `isRec := false`, while `all`,
    `ctors`, AND the shipped `Nat.rec` all match `demoKernelOracle` exactly (so neither
    `checkPostponedConstructors` nor `checkPostponedRecursors` notices). -/
def forgedNatMetadataVal : SimInductVal :=
  { natInductVal with numIndices := 1, isRec := false }

def forgedMetadataExploitMap : SimConstMap :=
  [("Nat", .induct forgedNatMetadataVal),
   ("Nat.zero", .ctor natZeroCtorVal),
   ("Nat.succ", .ctor natSuccCtorVal),
   ("Nat.rec", .recInfo natRecVal)]

/-- Kernel environment produced by replaying `forgedMetadataExploitMap`. -/
def forgedMetadataKernelEnv : SimConstMap :=
  insertKernelOutput []
    { inducts := [natInductVal], ctors := [natZeroCtorVal, natSuccCtorVal], recs := [natRecVal] }

/-- **Exploit Witness 2**: `forgedMetadataExploitMap` PASSES pre-`#16717`
    `vulnerableInductiveReplay` because `checkPostponedInductives` does not exist! -/
theorem forgedMetadata_passes_vulnerableInductiveReplay :
    vulnerableInductiveReplay demoKernelOracle forgedMetadataExploitMap = .ok forgedMetadataKernelEnv ∧
      lookupConst forgedMetadataKernelEnv "Nat" = some (.induct natInductVal) ∧
      natInductVal.numIndices ≠ forgedNatMetadataVal.numIndices ∧
      natInductVal.isRec ≠ forgedNatMetadataVal.isRec :=
  ⟨rfl, rfl, by decide, by decide⟩

/-- **Fix Witness 2**: `hardenedInductiveReplay` REJECTS `forgedMetadataExploitMap`
    reporting BOTH `indicesMismatch` and `isRecMismatch`! -/
theorem forgedMetadata_rejected_by_hardenedInductiveReplay :
    ∃ vs, hardenedInductiveReplay demoKernelOracle forgedMetadataExploitMap = .error vs ∧
      vs.any (fun v => v.code == .indicesMismatch && v.subject == "Nat") = true ∧
      vs.any (fun v => v.code == .isRecMismatch && v.subject == "Nat") = true :=
  ⟨_, rfl, by decide, by decide⟩

/-- **Recursor Forgery**: a shipped `Nat.rec` lying about `k` (structural-eta /
    K-like reduction flag) is rejected by the hardened checker with `recursorMismatch`
    (and, faithfully, also by Lean 4.34.1's `checkPostponedRecursors`). -/
def forgedNatRecMap : SimConstMap :=
  [("Nat", .induct natInductVal),
   ("Nat.zero", .ctor natZeroCtorVal),
   ("Nat.succ", .ctor natSuccCtorVal),
   ("Nat.rec", .recInfo { natRecVal with k := true })]

theorem forgedNatRec_rejected_by_hardened_and_vulnerable :
    (∃ vs, hardenedInductiveReplay demoKernelOracle forgedNatRecMap = .error vs ∧
      vs.any (fun v => v.code == .recursorMismatch && v.subject == "Nat.rec") = true) ∧
    vulnerableInductiveReplay demoKernelOracle forgedNatRecMap =
      .error "postponed recursor mismatch" :=
  ⟨⟨_, rfl, by decide⟩, rfl⟩

/-! ### 2.3 Rejection Theorems for All 13 Malformed Variants -/

/-- Helper checking whether a violation list contains a given violation code. -/
def hasReplayViolation (vs : List InductiveReplayViolation)
    (c : InductiveReplayViolationCode) : Bool :=
  vs.any (fun v => v.code == c)

/-- Malformed fixtures covering every remaining `InductiveReplayViolationCode`. -/
def malformedKeyMismatchMap : SimConstMap :=
  [("WrongKey", .induct unitInductVal), ("Unit.unit", .ctor unitCtorVal)]

def malformedDupAllMap : SimConstMap :=
  [("Unit", .induct { unitInductVal with all := ["Unit", "Unit"] }),
   ("Unit.unit", .ctor unitCtorVal)]

def malformedNonInductInAllMap : SimConstMap :=
  [("Unit", .induct { unitInductVal with all := ["Unit", "NotAnInduct"] }),
   ("NotAnInduct", .defn "NotAnInduct" "Type"),
   ("Unit.unit", .ctor unitCtorVal)]

def malformedMutualMetaMap : SimConstMap :=
  let indA : SimInductVal :=
    { name := "MutA", levelParams := ["u"], typeTag := "Type", numParams := 1,
      numIndices := 0, all := ["MutA", "MutB"], ctors := [], isRec := false, isReflexive := false }
  let indB : SimInductVal :=
    { name := "MutB", levelParams := ["u"], typeTag := "Type", numParams := 2,
      numIndices := 0, all := ["MutA", "MutB"], ctors := [], isRec := false, isReflexive := false }
  [("MutA", .induct indA), ("MutB", .induct indB)]

def malformedDupCtorsMap : SimConstMap :=
  [("Unit", .induct { unitInductVal with ctors := ["Unit.unit", "Unit.unit"] }),
   ("Unit.unit", .ctor unitCtorVal)]

def malformedNonCtorInCtorsMap : SimConstMap :=
  [("Unit", .induct { unitInductVal with ctors := ["FakeCtor"] }),
   ("FakeCtor", .defn "FakeCtor" "Unit")]

def malformedCtorInductMismatchMap : SimConstMap :=
  [("Unit", .induct unitInductVal),
   ("Unit.unit", .ctor { unitCtorVal with induct := "OtherInd" })]

def malformedCtorCidxMismatchMap : SimConstMap :=
  [("Unit", .induct unitInductVal),
   ("Unit.unit", .ctor { unitCtorVal with cidx := 5 })]

def malformedDanglingCtorMap : SimConstMap :=
  [("Unit", .induct unitInductVal),
   ("Unit.unit", .ctor unitCtorVal),
   ("Unit.ghost", .ctor { unitCtorVal with name := "Unit.ghost", cidx := 1 })]

theorem checkInductive_rejects_keyMismatch :
    hasReplayViolation (checkStaticInductiveIntegrity malformedKeyMismatchMap) .keyMismatch = true := by
  decide

theorem checkInductive_rejects_selfNotInAll :
    hasReplayViolation (checkStaticInductiveIntegrity fakeFalseExploitMap) .selfNotInAll = true := by
  decide

theorem checkInductive_rejects_duplicateInAll :
    hasReplayViolation (checkStaticInductiveIntegrity malformedDupAllMap) .duplicateInAll = true := by
  decide

theorem checkInductive_rejects_nonInductInAll :
    hasReplayViolation (checkStaticInductiveIntegrity malformedNonInductInAllMap) .nonInductInAll = true := by
  decide

theorem checkInductive_rejects_mutualMetadataMismatch :
    hasReplayViolation (checkStaticInductiveIntegrity malformedMutualMetaMap) .mutualMetadataMismatch = true := by
  decide

theorem checkInductive_rejects_duplicateInCtors :
    hasReplayViolation (checkStaticInductiveIntegrity malformedDupCtorsMap) .duplicateInCtors = true := by
  decide

theorem checkInductive_rejects_nonCtorInCtors :
    hasReplayViolation (checkStaticInductiveIntegrity malformedNonCtorInCtorsMap) .nonCtorInCtors = true := by
  decide

theorem checkInductive_rejects_ctorInductMismatch :
    hasReplayViolation (checkStaticInductiveIntegrity malformedCtorInductMismatchMap) .ctorInductMismatch = true := by
  decide

theorem checkInductive_rejects_ctorCidxMismatch :
    hasReplayViolation (checkStaticInductiveIntegrity malformedCtorCidxMismatchMap) .ctorCidxMismatch = true := by
  decide

theorem checkInductive_rejects_danglingCtorNotListedInInduct :
    hasReplayViolation (checkStaticInductiveIntegrity malformedDanglingCtorMap) .danglingCtorNotListedInInduct = true := by
  decide

theorem checkInductive_rejects_indicesMismatch :
    hasReplayViolation
      (checkPostponedInductives forgedMetadataExploitMap [("Nat", .induct natInductVal)])
      .indicesMismatch = true := by
  decide

theorem checkInductive_rejects_isRecMismatch :
    hasReplayViolation
      (checkPostponedInductives forgedMetadataExploitMap [("Nat", .induct natInductVal)])
      .isRecMismatch = true := by
  decide

theorem checkInductive_rejects_recursorMismatch :
    hasReplayViolation
      (checkPostponedRecursors forgedNatRecMap forgedMetadataKernelEnv)
      .recursorMismatch = true := by
  decide

/-- **Dangling / non-parent recursor rejection (A1)**: a forged `.recInfo` whose `all`
    references a non-existent inductive is rejected statically BEFORE replay as well as
    post-replay by `checkPostponedRecursors`. -/
def malformedDanglingRecMap : SimConstMap :=
  [("Unit", .induct unitInductVal),
   ("Unit.unit", .ctor unitCtorVal),
   ("Unit.rec", .recInfo unitRecVal),
   ("Ghost.rec_1", .recInfo
     { name := "Ghost.rec_1", levelParams := ["u"], typeTag := "Ghost.rec.type",
       all := ["Ghost"], numParams := 0, numIndices := 0, numMotives := 1,
       numMinors := 0, ruleCtors := [], k := false })]

theorem danglingRecursor_rejected_statically_and_postReplay :
    hasReplayViolation (checkStaticInductiveIntegrity malformedDanglingRecMap) .recursorMismatch = true ∧
    hasReplayViolation
      (checkPostponedRecursors malformedDanglingRecMap
        (insertKernelOutput [] { inducts := [unitInductVal], ctors := [unitCtorVal], recs := [unitRecVal] }))
      .recursorMismatch = true := by
  decide

/-! ### 2.4 Semantic `InductiveReplayWellFormed` & Soundness Theorem -/

/-- Relational well-formedness invariant established by hardened `lean4#16717` replay:
    1. Every entry `(k, ci)` has unique key `k = ci.constName`.
    2. Every inductive `ind` in `m` lists itself in `ind.all` (`ind.all.Nodup`), every
       member of `ind.all` is an inductive in `m` with identical mutual metadata,
       `ind.ctors.Nodup`, and every `i`-th constructor `c` is a `.ctor` in `m` with
       `cVal.induct = ind.name`, matching params/levels, and `cVal.cidx = i`.
    3. Every `.ctor` in `m` has its parent inductive in `m` listing it in `parent.ctors`
       (zero dangling constructors).
    4. Every `.induct`, `.ctor`, and `.recInfo` in `m` exists in the kernel-replayed
       `kernelEnv` with identical field-for-field metadata. -/
structure InductiveReplayWellFormed (m kernelEnv : SimConstMap) : Prop where
  keys_nodup : (m.map Prod.fst).Nodup
  key_matches_name : ∀ k ci, (k, ci) ∈ m → ci.constName = k
  induct_self_in_all : ∀ k ind, (k, .induct ind) ∈ m → ind.name ∈ ind.all
  induct_all_nodup : ∀ k ind, (k, .induct ind) ∈ m → ind.all.Nodup
  induct_all_peers : ∀ k ind n, (k, .induct ind) ∈ m → n ∈ ind.all →
    ∃ peer, lookupConst m n = some (.induct peer) ∧
      peer.all = ind.all ∧ peer.levelParams = ind.levelParams ∧
      peer.numParams = ind.numParams ∧ peer.isReflexive = ind.isReflexive ∧
      peer.isRec = ind.isRec
  induct_ctors_nodup : ∀ k ind, (k, .induct ind) ∈ m → ind.ctors.Nodup
  induct_ctors_valid : ∀ k ind i c, (k, .induct ind) ∈ m → ind.ctors[i]? = some c →
    ∃ cVal, lookupConst m c = some (.ctor cVal) ∧
      cVal.induct = ind.name ∧ cVal.numParams = ind.numParams ∧
      cVal.levelParams = ind.levelParams ∧ cVal.cidx = i
  ctor_listed_in_parent : ∀ k cVal, (k, .ctor cVal) ∈ m →
    ∃ parent, lookupConst m cVal.induct = some (.induct parent) ∧ cVal.name ∈ parent.ctors
  induct_matches_kernel : ∀ k ind, (k, .induct ind) ∈ m →
    lookupConst kernelEnv ind.name = some (.induct ind)
  ctor_matches_kernel : ∀ k cVal, (k, .ctor cVal) ∈ m →
    lookupConst kernelEnv cVal.name = some (.ctor cVal)
  rec_all_valid : ∀ k rVal, (k, .recInfo rVal) ∈ m →
    rVal.all ≠ [] ∧
    ∀ n ∈ rVal.all, ∃ parent, lookupConst m n = some (.induct parent) ∧
      parent.all = rVal.all ∧ parent.numParams = rVal.numParams
  rec_matches_kernel : ∀ k rVal, (k, .recInfo rVal) ∈ m →
    lookupConst kernelEnv rVal.name = some (.recInfo rVal)

private theorem checkAllList_nil_imp {m : SimConstMap} {ind : SimInductVal}
    {ns : List String} (h : checkAllList m ind ns = []) :
    ∀ n ∈ ns, ∃ peer, lookupConst m n = some (.induct peer) ∧
      peer.all = ind.all ∧ peer.levelParams = ind.levelParams ∧
      peer.numParams = ind.numParams ∧ peer.isReflexive = ind.isReflexive ∧
      peer.isRec = ind.isRec := by
  induction ns with
  | nil => intro n hn; cases hn
  | cons n rest ih =>
    unfold checkAllList at h
    rw [List.append_eq_nil_iff] at h
    obtain ⟨hHere, hRest⟩ := h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hxRest
    · cases hL : lookupConst m x with
      | none => rw [hL] at hHere; cases hHere
      | some ci =>
        cases ci with
        | induct peer =>
          rw [hL] at hHere
          by_cases hDiff : (peer.all != ind.all || peer.levelParams != ind.levelParams ||
              peer.numParams != ind.numParams || peer.isReflexive != ind.isReflexive ||
              peer.isRec != ind.isRec) = true
          · simp only [hDiff, ↓reduceIte] at hHere; cases hHere
          · simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hDiff
            exact ⟨peer, rfl, hDiff.1.1.1.1, hDiff.1.1.1.2, hDiff.1.1.2, hDiff.1.2, hDiff.2⟩
        | ctor _ | recInfo _ | defn _ _ | thm _ _ => rw [hL] at hHere; cases hHere
    · exact ih hRest x hxRest

private theorem checkCtorList_nil_imp {m : SimConstMap} {ind : SimInductVal}
    {cs : List String} {base : Nat} (h : checkCtorList m ind base cs = []) :
    ∀ offset c, cs[offset]? = some c →
      ∃ cVal, lookupConst m c = some (.ctor cVal) ∧
        cVal.induct = ind.name ∧ cVal.numParams = ind.numParams ∧
        cVal.levelParams = ind.levelParams ∧ cVal.cidx = base + offset := by
  induction cs generalizing base with
  | nil => intro offset c hGet; simp at hGet
  | cons c0 rest ih =>
    unfold checkCtorList at h
    rw [List.append_eq_nil_iff] at h
    obtain ⟨hHere, hRest⟩ := h
    intro offset c hGet
    cases offset with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hGet
      subst hGet
      cases hL : lookupConst m c0 with
      | none => rw [hL] at hHere; cases hHere
      | some ci =>
        cases ci with
        | ctor cVal =>
          rw [hL] at hHere
          rw [List.append_eq_nil_iff] at hHere
          obtain ⟨hInd, hCidx⟩ := hHere
          have hIndEq : cVal.induct = ind.name ∧ cVal.numParams = ind.numParams ∧
              cVal.levelParams = ind.levelParams := by
            by_cases hB : (cVal.induct != ind.name || cVal.numParams != ind.numParams ||
                cVal.levelParams != ind.levelParams) = true
            · simp only [hB, ↓reduceIte] at hInd; cases hInd
            · simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hB
              exact ⟨hB.1.1, hB.1.2, hB.2⟩
          have hIdxEq : cVal.cidx = base := by
            by_cases hC : (cVal.cidx != base) = true
            · simp only [hC, ↓reduceIte] at hCidx; cases hCidx
            · simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hC; exact hC
          exact ⟨cVal, rfl, hIndEq.1, hIndEq.2.1, hIndEq.2.2, by omega⟩
        | induct _ | recInfo _ | defn _ _ | thm _ _ => rw [hL] at hHere; cases hHere
    | succ k =>
      simp only [List.getElem?_cons_succ] at hGet
      obtain ⟨cVal, hL, h1, h2, h3, h4⟩ := ih hRest k c hGet
      exact ⟨cVal, hL, h1, h2, h3, by omega⟩

private theorem checkPostponedInductives_nil_imp {m kernelEnv : SimConstMap}
    (h : checkPostponedInductives m kernelEnv = []) :
    ∀ k ind, (k, .induct ind) ∈ m → lookupConst kernelEnv ind.name = some (.induct ind) := by
  intro k ind hMem
  unfold checkPostponedInductives at h
  have hItem := (List.flatMap_eq_nil_iff.mp h) (k, .induct ind) hMem
  simp only at hItem
  cases hL : lookupConst kernelEnv ind.name with
  | none => rw [hL] at hItem; cases hItem
  | some ci =>
    cases ci with
    | induct kInfo =>
      rw [hL] at hItem
      rw [List.append_eq_nil_iff, List.append_eq_nil_iff] at hItem
      obtain ⟨⟨hIdx, hRec⟩, hMeta⟩ := hItem
      have h1 : kInfo.numIndices = ind.numIndices := by
        by_cases hb : (kInfo.numIndices != ind.numIndices) = true
        · simp only [hb, ↓reduceIte] at hIdx; cases hIdx
        · simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hb; exact hb
      have h2 : kInfo.isRec = ind.isRec := by
        by_cases hb : (kInfo.isRec != ind.isRec) = true
        · simp only [hb, ↓reduceIte] at hRec; cases hRec
        · simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hb; exact hb
      have h3 : kInfo.name = ind.name ∧ kInfo.levelParams = ind.levelParams ∧
          kInfo.typeTag = ind.typeTag ∧ kInfo.numParams = ind.numParams ∧
          kInfo.all = ind.all ∧ kInfo.ctors = ind.ctors ∧
          kInfo.isReflexive = ind.isReflexive ∧ kInfo.isUnsafe = ind.isUnsafe := by
        by_cases hb : (kInfo.name != ind.name || kInfo.levelParams != ind.levelParams ||
            kInfo.typeTag != ind.typeTag || kInfo.numParams != ind.numParams ||
            kInfo.all != ind.all || kInfo.ctors != ind.ctors ||
            kInfo.isReflexive != ind.isReflexive || kInfo.isUnsafe != ind.isUnsafe) = true
        · simp only [hb, ↓reduceIte] at hMeta; cases hMeta
        · simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hb
          exact ⟨hb.1.1.1.1.1.1.1, hb.1.1.1.1.1.1.2, hb.1.1.1.1.1.2, hb.1.1.1.1.2,
            hb.1.1.1.2, hb.1.1.2, hb.1.2, hb.2⟩
      have hEq : kInfo = ind := by
        cases kInfo; cases ind
        simp only at h1 h2 h3
        rcases h3 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        subst h1; subst h2; rfl
      rw [← hEq]
    | ctor _ | recInfo _ | defn _ _ | thm _ _ => rw [hL] at hItem; cases hItem

private theorem checkPostponedConstructors_nil_imp {m kernelEnv : SimConstMap}
    (h : checkPostponedConstructors m kernelEnv = []) :
    ∀ k cVal, (k, .ctor cVal) ∈ m → lookupConst kernelEnv cVal.name = some (.ctor cVal) := by
  intro k cVal hMem
  unfold checkPostponedConstructors at h
  have hItem := (List.flatMap_eq_nil_iff.mp h) (k, .ctor cVal) hMem
  simp only at hItem
  cases hL : lookupConst kernelEnv cVal.name with
  | none => rw [hL] at hItem; cases hItem
  | some ci =>
    cases ci with
    | ctor kCtor =>
      rw [hL] at hItem
      by_cases hEq : (kCtor == cVal) = true
      · rw [eq_of_beq hEq]
      · simp [hEq] at hItem
        split at hItem <;> cases hItem
    | induct _ | recInfo _ | defn _ _ | thm _ _ => rw [hL] at hItem; cases hItem

private theorem checkPostponedRecursors_nil_imp {m kernelEnv : SimConstMap}
    (h : checkPostponedRecursors m kernelEnv = []) :
    ∀ k rVal, (k, .recInfo rVal) ∈ m → lookupConst kernelEnv rVal.name = some (.recInfo rVal) := by
  intro k rVal hMem
  unfold checkPostponedRecursors at h
  have hItem := (List.flatMap_eq_nil_iff.mp h) (k, .recInfo rVal) hMem
  simp only at hItem
  cases hL : lookupConst kernelEnv rVal.name with
  | none => rw [hL] at hItem; cases hItem
  | some ci =>
    cases ci with
    | recInfo kRec =>
      rw [hL] at hItem
      by_cases hEq : (kRec == rVal) = true
      · rw [eq_of_beq hEq]
      · simp [hEq] at hItem
    | induct _ | ctor _ | defn _ _ | thm _ _ => rw [hL] at hItem; cases hItem

/-- **Flagship Soundness Theorem (`inductiveReplayWellFormed_sound`)**:
    Whenever `checkInductiveReplayIntegrity m kernelEnv = []` (and in particular
    whenever `hardenedInductiveReplay oracle m = .ok kernelEnv`), every structural
    invariant and exact kernel-agreement invariant in `InductiveReplayWellFormed m kernelEnv`
    holds. No inductive can be silently skipped (`FakeFalse`), no constructor can dangle,
    and no metadata field (`numIndices`, `isRec`, `all`, `ctors`, etc.) can differ from
    the kernel's generated declaration. -/
theorem inductiveReplayWellFormed_sound {m kernelEnv : SimConstMap}
    (hCheck : checkInductiveReplayIntegrity m kernelEnv = []) :
    InductiveReplayWellFormed m kernelEnv := by
  unfold checkInductiveReplayIntegrity at hCheck
  rw [List.append_eq_nil_iff, List.append_eq_nil_iff, List.append_eq_nil_iff] at hCheck
  obtain ⟨⟨⟨hStatic, hPostInd⟩, hPostCtor⟩, hPostRec⟩ := hCheck
  unfold checkStaticInductiveIntegrity at hStatic
  rw [List.append_eq_nil_iff] at hStatic
  obtain ⟨hDupKeys, hEntries⟩ := hStatic
  have hNodupKeys : (m.map Prod.fst).Nodup := by
    by_cases hk : hasNoDupStrings (m.map Prod.fst) = true
    · exact (hasNoDupStrings_eq_true_iff _).mp hk
    · simp [hk] at hDupKeys
  have hEntryNil : ∀ p ∈ m,
      (if p.2.constName != p.1 then ([{ code := .keyMismatch, subject := p.1, detail := p.2.constName }] : List InductiveReplayViolation) else []) = [] ∧
      (match p.2 with
      | .induct ind =>
        (if !ind.all.contains ind.name then [{ code := .selfNotInAll, subject := ind.name, detail := "missing_self" }] else []) ++
        (if !hasNoDupStrings ind.all then [{ code := .duplicateInAll, subject := ind.name, detail := "duplicate_all" }] else []) ++
        checkAllList m ind ind.all ++
        (if !hasNoDupStrings ind.ctors then [{ code := .duplicateInCtors, subject := ind.name, detail := "duplicate_ctors" }] else []) ++
        checkCtorList m ind 0 ind.ctors
      | .ctor cVal =>
        match lookupConst m cVal.induct with
        | some (.induct parent) =>
          if parent.ctors.contains cVal.name then []
          else [{ code := .danglingCtorNotListedInInduct, subject := cVal.name, detail := cVal.induct }]
        | _ =>
          [{ code := .danglingCtorNotListedInInduct, subject := cVal.name, detail := cVal.induct }]
      | .recInfo rVal =>
        let vEmpty :=
          if rVal.all.isEmpty then
            [{ code := .recursorMismatch, subject := rVal.name, detail := "empty_rec_all" }]
          else []
        let vPeers := rVal.all.flatMap fun n =>
          match lookupConst m n with
          | some (.induct parent) =>
            if parent.all != rVal.all || parent.numParams != rVal.numParams then
              [{ code := .recursorMismatch, subject := rVal.name, detail := n }]
            else []
          | _ =>
            [{ code := .recursorMismatch, subject := rVal.name, detail := n }]
        vEmpty ++ vPeers
      | _ => []) = [] := by
    intro p hp
    have hP := (List.flatMap_eq_nil_iff.mp hEntries) p hp
    exact List.append_eq_nil_iff.mp hP
  refine
    { keys_nodup := hNodupKeys
      key_matches_name := fun k ci hMem => by
        have hK := (hEntryNil (k, ci) hMem).1
        by_cases hb : (ci.constName != k) = true
        · simp only [hb, ↓reduceIte] at hK; cases hK
        · simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hb; exact hb
      induct_self_in_all := fun k ind hMem => by
        have hB := (hEntryNil (k, .induct ind) hMem).2
        simp only [List.append_eq_nil_iff] at hB
        have hS := hB.1.1.1.1
        by_cases hb : (!ind.all.contains ind.name) = true
        · simp only [hb, ↓reduceIte] at hS; cases hS
        · simp only [Bool.not_eq_true', Bool.eq_false_iff, List.contains_iff_mem, Decidable.not_not] at hb
          exact hb
      induct_all_nodup := fun k ind hMem => by
        have hB := (hEntryNil (k, .induct ind) hMem).2
        simp only [List.append_eq_nil_iff] at hB
        have hD := hB.1.1.1.2
        by_cases hb : (!hasNoDupStrings ind.all) = true
        · simp only [hb, ↓reduceIte] at hD; cases hD
        · simp only [Bool.not_eq_true', Bool.eq_false_iff, Decidable.not_not] at hb
          exact (hasNoDupStrings_eq_true_iff _).mp hb
      induct_all_peers := fun k ind n hMem hn => by
        have hB := (hEntryNil (k, .induct ind) hMem).2
        simp only [List.append_eq_nil_iff] at hB
        exact checkAllList_nil_imp hB.1.1.2 n hn
      induct_ctors_nodup := fun k ind hMem => by
        have hB := (hEntryNil (k, .induct ind) hMem).2
        simp only [List.append_eq_nil_iff] at hB
        have hD := hB.1.2
        by_cases hb : (!hasNoDupStrings ind.ctors) = true
        · simp only [hb, ↓reduceIte] at hD; cases hD
        · simp only [Bool.not_eq_true', Bool.eq_false_iff, Decidable.not_not] at hb
          exact (hasNoDupStrings_eq_true_iff _).mp hb
      induct_ctors_valid := fun k ind i c hMem hGet => by
        have hB := (hEntryNil (k, .induct ind) hMem).2
        simp only [List.append_eq_nil_iff] at hB
        have hRes := checkCtorList_nil_imp hB.2 i c hGet
        simpa using hRes
      ctor_listed_in_parent := fun k cVal hMem => by
        have hB := (hEntryNil (k, .ctor cVal) hMem).2
        simp only at hB
        cases hL : lookupConst m cVal.induct with
        | none => rw [hL] at hB; cases hB
        | some ci =>
          cases ci with
          | induct parent =>
            rw [hL] at hB
            simp at hB
            exact ⟨parent, rfl, hB⟩
          | ctor _ | recInfo _ | defn _ _ | thm _ _ => rw [hL] at hB; cases hB
      induct_matches_kernel := checkPostponedInductives_nil_imp hPostInd
      ctor_matches_kernel := checkPostponedConstructors_nil_imp hPostCtor
      rec_all_valid := fun k rVal hMem => by
        have hB := (hEntryNil (k, .recInfo rVal) hMem).2
        simp only [List.append_eq_nil_iff] at hB
        obtain ⟨hEmpty, hPeers⟩ := hB
        refine ⟨?_, ?_⟩
        · intro hNil; rw [hNil] at hEmpty; cases hEmpty
        · intro n hn
          have hP := (List.flatMap_eq_nil_iff.mp hPeers) n hn
          cases hL : lookupConst m n with
          | none => rw [hL] at hP; cases hP
          | some ci =>
            cases ci with
            | induct parent =>
              rw [hL] at hP
              by_cases hd : (parent.all != rVal.all || parent.numParams != rVal.numParams) = true
              · simp only [hd, ↓reduceIte] at hP; cases hP
              · simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hd
                exact ⟨parent, rfl, hd.1, hd.2⟩
            | ctor _ | recInfo _ | defn _ _ | thm _ _ => rw [hL] at hP; cases hP
      rec_matches_kernel := checkPostponedRecursors_nil_imp hPostRec }

/-- Corollary: a successful `hardenedInductiveReplay` guarantees `InductiveReplayWellFormed`. -/
theorem hardenedInductiveReplay_sound {oracle : KernelInductOracle} {m env : SimConstMap}
    (hOk : hardenedInductiveReplay oracle m = .ok env) :
    InductiveReplayWellFormed m env := by
  unfold hardenedInductiveReplay at hOk
  cases hStatic : checkStaticInductiveIntegrity m with
  | cons v vs =>
    simp [hStatic] at hOk
  | nil =>
    simp only [hStatic, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
    cases hStep : vulnerableReplayStep oracle m (m.map Prod.fst) [] with
    | error msg => rw [hStep] at hOk; cases hOk
    | ok env' =>
      rw [hStep] at hOk
      dsimp only at hOk
      cases hPost : (checkPostponedInductives m env' ++ checkPostponedConstructors m env' ++
          checkPostponedRecursors m env').isEmpty with
      | false => rw [hPost] at hOk; cases hOk
      | true =>
        rw [hPost] at hOk
        simp only [↓reduceIte, Except.ok.injEq] at hOk
        subst hOk
        have hPostNil : checkPostponedInductives m env' ++ checkPostponedConstructors m env' ++
            checkPostponedRecursors m env' = [] :=
          List.isEmpty_iff.mp hPost
        rw [List.append_eq_nil_iff, List.append_eq_nil_iff] at hPostNil
        apply inductiveReplayWellFormed_sound
        simp [checkInductiveReplayIntegrity, hStatic, hPostNil.1.1, hPostNil.1.2, hPostNil.2]

/-! ## 3. Pillar 2 — `grmf` cl/1029226310 `--exact-modules` Sharded Audit & `--orphan-only` -/

/-- A declaration record in a compiled Lean repository graph. -/
structure DeclRecord : Type where
  name : String
  originMod : String
  isAxiom : Bool
  isUnsafeOrPartial : Bool
  directDeps : List String
  deriving DecidableEq, Repr, Inhabited

/-- Repository model for monolithic vs. `--exact-modules` sharded audit. -/
structure RepoEnv : Type where
  registeredModules : List String
  onDiskModules : List String
  decls : List DeclRecord
  permittedAxioms : List String
  deriving DecidableEq, Repr

/-- Lookup a declaration by name in `env.decls`. -/
def RepoEnv.lookup (env : RepoEnv) (c : String) : Option DeclRecord :=
  env.decls.find? (fun r => r.name == c)

/-- Full transitive constant-dependency graph across arbitrary module/import boundaries
    (handling chains, diamonds, and cycles cleanly). -/
inductive TransDep (env : RepoEnv) : String → String → Prop where
  | refl (c : String) : TransDep env c c
  | step {c c' d : String} {rec : DeclRecord}
      (hLookup : env.lookup c = some rec)
      (hEdge : c' ∈ rec.directDeps)
      (hRest : TransDep env c' d) :
      TransDep env c d

/-- Transitivity of `TransDep`. -/
theorem TransDep.trans {env : RepoEnv} {a b c : String}
    (h1 : TransDep env a b) (h2 : TransDep env b c) : TransDep env a c := by
  induction h1 with
  | refl => exact h2
  | step hL hE _ ih => exact TransDep.step hL hE (ih h2)

/-- An axiom `a` is transitively reached from a module set `mods` in `env`. -/
def ReachesAxiomFrom (env : RepoEnv) (mods : List String) (a : String) : Prop :=
  ∃ r ∈ env.decls, r.originMod ∈ mods ∧
    TransDep env r.name a ∧
    ∃ ra, env.lookup a = some ra ∧ ra.isAxiom = true

/-- Monolithic audit safety over the full repository:
    1. Every on-disk `.lean` module is registered (zero orphans).
    2. Every declaration owned by a registered module is safe/total and every
       transitively reachable constant exists, is safe/total, and (if an axiom)
       belongs to `env.permittedAxioms`. -/
structure MonolithicAuditSafe (env : RepoEnv) : Prop where
  no_orphans : ∀ m ∈ env.onDiskModules, m ∈ env.registeredModules
  decls_safe : ∀ r ∈ env.decls, r.originMod ∈ env.registeredModules →
    r.isUnsafeOrPartial = false ∧
    ∀ d, TransDep env r.name d →
      ∃ dr, env.lookup d = some dr ∧
        dr.isUnsafeOrPartial = false ∧
        (dr.isAxiom = true → d ∈ env.permittedAxioms)

/-- Case-folding key of a module name (`Anneal.Foo` and `anneal.foo` collide on
    case-insensitive filesystems such as default macOS APFS). -/
def caseFoldKey (s : String) : List Char :=
  s.toList.map Char.toLower

/-- Exact-partition + zero-orphan + zero-case-fold-collision completeness predicate
    (`--orphan-only` gate). -/
structure ShardPartitionValid (registered onDisk : List String)
    (shards : List (List String)) : Prop where
  nonempty_shards : shards ≠ []
  each_nonempty : ∀ s ∈ shards, s ≠ []
  each_nodup : ∀ s ∈ shards, s.Nodup
  pairwise_disjoint : ∀ i j (hi : i < shards.length) (hj : j < shards.length),
    i ≠ j → ∀ m, m ∈ shards[i] → m ∉ shards[j]
  subset_registered : ∀ s ∈ shards, ∀ m ∈ s, m ∈ registered
  covers_registered : ∀ m ∈ registered, ∃ s ∈ shards, m ∈ s
  no_on_disk_orphans : ∀ m ∈ onDisk, m ∈ registered
  no_case_fold_collisions : ∀ a ∈ registered ++ onDisk, ∀ b ∈ registered ++ onDisk,
    caseFoldKey a = caseFoldKey b → a = b

/-- Violation record produced by `checkShardPartition`. -/
structure ShardAuditViolation : Type where
  code : ShardAuditViolationCode
  subject : String
  deriving DecidableEq, Repr

/-- Check pairwise disjointness of shards starting at index `i`. -/
def checkPairwiseDisjoint : List (List String) → List ShardAuditViolation
  | [] => []
  | s :: rest =>
    let overlaps := s.flatMap fun m =>
      if rest.any (fun other => other.contains m) then
        [{ code := .overlappingShards, subject := m }]
      else []
    overlaps ++ checkPairwiseDisjoint rest

/-- Computable `--orphan-only` + exact shard-partition gate matching Python 1-for-1. -/
def checkShardPartition (registered onDisk : List String)
    (shards : List (List String)) : List ShardAuditViolation :=
  let vEmptyList :=
    if shards.isEmpty then [{ code := .emptyShardList, subject := "<shards>" }] else []
  let vPerShard := shards.flatMap fun s =>
    let vEmpty := if s.isEmpty then [{ code := .emptyShard, subject := "<shard>" }] else []
    let vDup := if !hasNoDupStrings s then [{ code := .duplicateModuleInShard, subject := "<shard>" }] else []
    let vUnreg := s.flatMap fun m =>
      if !registered.contains m then [{ code := .unregisteredModuleInShard, subject := m }] else []
    vEmpty ++ vDup ++ vUnreg
  let vDisjoint := checkPairwiseDisjoint shards
  let covered := shards.flatten
  let vUncovered := registered.flatMap fun m =>
    if !covered.contains m then [{ code := .uncoveredRegisteredModule, subject := m }] else []
  let vOrphans := onDisk.flatMap fun m =>
    if !registered.contains m then [{ code := .unregisteredOnDiskOrphan, subject := m }] else []
  let univ := registered ++ onDisk
  let vCollide := univ.flatMap fun a => univ.flatMap fun b =>
    if a != b && caseFoldKey a == caseFoldKey b then
      [{ code := .moduleNameCollision, subject := a }]
    else []
  vEmptyList ++ vPerShard ++ vDisjoint ++ vUncovered ++ vOrphans ++ vCollide

private theorem checkPairwiseDisjoint_nil_iff (shards : List (List String)) :
    checkPairwiseDisjoint shards = [] ↔
      ∀ i j (hi : i < shards.length) (hj : j < shards.length),
        i ≠ j → ∀ m, m ∈ shards[i] → m ∉ shards[j] := by
  induction shards with
  | nil =>
    constructor
    · intro _ i _ hi; cases hi
    · intro _; rfl
  | cons s rest ih =>
    unfold checkPairwiseDisjoint
    rw [List.append_eq_nil_iff, ih]
    constructor
    · rintro ⟨hOver, hRest⟩ i j hi hj hne m hmi hmj
      cases i with
      | zero =>
        cases j with
        | zero => exact hne rfl
        | succ j' =>
          simp only [List.getElem_cons_zero] at hmi
          simp only [List.getElem_cons_succ] at hmj
          have hItem := (List.flatMap_eq_nil_iff.mp hOver) m hmi
          have hAny : rest.any (fun other => other.contains m) = true := by
            rw [List.any_eq_true]
            exact ⟨rest[j']'(Nat.lt_of_succ_lt_succ hj), List.getElem_mem _, List.contains_iff_mem.mpr hmj⟩
          simp only [hAny, ↓reduceIte] at hItem
          cases hItem
      | succ i' =>
        cases j with
        | zero =>
          simp only [List.getElem_cons_succ] at hmi
          simp only [List.getElem_cons_zero] at hmj
          have hItem := (List.flatMap_eq_nil_iff.mp hOver) m hmj
          have hAny : rest.any (fun other => other.contains m) = true := by
            rw [List.any_eq_true]
            exact ⟨rest[i']'(Nat.lt_of_succ_lt_succ hi), List.getElem_mem _, List.contains_iff_mem.mpr hmi⟩
          simp only [hAny, ↓reduceIte] at hItem
          cases hItem
        | succ j' =>
          simp only [List.getElem_cons_succ] at hmi hmj
          have hne' : i' ≠ j' := fun hEq => hne (congrArg Nat.succ hEq)
          exact hRest i' j' (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) hne' m hmi hmj
    · intro hAll
      refine ⟨?_, ?_⟩
      · rw [List.flatMap_eq_nil_iff]
        intro m hm
        simp
        intro other hOtherMem
        obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem hOtherMem
        exact hAll 0 (j' + 1) (Nat.zero_lt_succ _) (Nat.succ_lt_succ hj')
          (Nat.zero_ne_add_one j') m hm
      · intro i' j' hi' hj' hne' m hmi hmj
        exact hAll (i' + 1) (j' + 1) (Nat.succ_lt_succ hi') (Nat.succ_lt_succ hj')
          (fun hEq => hne' (Nat.succ.inj hEq)) m hmi hmj

/-- **Completeness & Soundness Equivalence (`shardPartitionCheck_iff_valid`)**:
    `checkShardPartition registered onDisk shards = []` if and only if
    `ShardPartitionValid registered onDisk shards`. -/
theorem shardPartitionCheck_iff_valid (registered onDisk : List String)
    (shards : List (List String)) :
    checkShardPartition registered onDisk shards = [] ↔
      ShardPartitionValid registered onDisk shards := by
  unfold checkShardPartition
  simp only [List.append_eq_nil_iff, checkPairwiseDisjoint_nil_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨hEmptyList, hPerShard⟩, hDisj⟩, hUncov⟩, hOrph⟩, hColl⟩
    have hNonEmpty : shards ≠ [] := by
      intro hNil; subst hNil; cases hEmptyList
    have hEach : ∀ s ∈ shards, s ≠ [] ∧ s.Nodup ∧ ∀ m ∈ s, m ∈ registered := by
      intro s hs
      have hS := (List.flatMap_eq_nil_iff.mp hPerShard) s hs
      simp only [List.append_eq_nil_iff] at hS
      obtain ⟨⟨hSEmpty, hSDup⟩, hSUnreg⟩ := hS
      refine ⟨?_, ?_, ?_⟩
      · intro hNil; subst hNil; cases hSEmpty
      · simp at hSDup
        exact (hasNoDupStrings_eq_true_iff s).mp hSDup
      · intro m hm
        have hM := (List.flatMap_eq_nil_iff.mp hSUnreg) m hm
        simp at hM
        exact hM
    refine
      { nonempty_shards := hNonEmpty
        each_nonempty := fun s hs => (hEach s hs).1
        each_nodup := fun s hs => (hEach s hs).2.1
        pairwise_disjoint := hDisj
        subset_registered := fun s hs => (hEach s hs).2.2
        covers_registered := fun m hm => by
          have hM := (List.flatMap_eq_nil_iff.mp hUncov) m hm
          simp at hM
          exact hM
        no_on_disk_orphans := fun m hm => by
          have hM := (List.flatMap_eq_nil_iff.mp hOrph) m hm
          simp at hM
          exact hM
        no_case_fold_collisions := fun a ha b hb hKey => by
          have hA := (List.flatMap_eq_nil_iff.mp hColl) a ha
          have hB := (List.flatMap_eq_nil_iff.mp hA) b hb
          by_cases hNe : a = b
          · exact hNe
          · have hT : (a != b && caseFoldKey a == caseFoldKey b) = true := by
              simp [hNe, hKey]
            simp only [hT, ↓reduceIte] at hB
            cases hB }
  · intro hV
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, hV.pairwise_disjoint⟩, ?_⟩, ?_⟩, ?_⟩
    · cases hSh : shards with
      | nil => exact absurd hSh hV.nonempty_shards
      | cons _ _ => rfl
    · rw [List.flatMap_eq_nil_iff]
      intro s hs
      simp only [List.append_eq_nil_iff]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · cases hS : s with
        | nil => exact absurd hS (hV.each_nonempty s hs)
        | cons _ _ => rfl
      · have hNd : hasNoDupStrings s = true := (hasNoDupStrings_eq_true_iff s).mpr (hV.each_nodup s hs)
        simp only [hNd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      · rw [List.flatMap_eq_nil_iff]
        intro m hm
        have hIn : registered.contains m = true := List.contains_iff_mem.mpr (hV.subset_registered s hs m hm)
        simp only [hIn, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · rw [List.flatMap_eq_nil_iff]
      intro m hm
      obtain ⟨s, hs, hms⟩ := hV.covers_registered m hm
      have hIn : shards.flatten.contains m = true :=
        List.contains_iff_mem.mpr (List.mem_flatten.mpr ⟨s, hs, hms⟩)
      simp only [hIn, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · rw [List.flatMap_eq_nil_iff]
      intro m hm
      have hIn : registered.contains m = true :=
        List.contains_iff_mem.mpr (hV.no_on_disk_orphans m hm)
      simp only [hIn, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · rw [List.flatMap_eq_nil_iff]
      intro a ha
      rw [List.flatMap_eq_nil_iff]
      intro b hb
      have hC : (a != b && caseFoldKey a == caseFoldKey b) = false := by
        cases hEq : (caseFoldKey a == caseFoldKey b) with
        | false => simp
        | true =>
          have hab := hV.no_case_fold_collisions a ha b hb (eq_of_beq hEq)
          simp [hab]
      simp only [hC, Bool.false_eq_true, ↓reduceIte]

/-- `--exact-modules` shard audit: checks direct declarations owned by `m ∈ shard`,
    walking the FULL transitive constant graph `TransDep env` across all imports
    (never truncating at shard boundaries!). -/
def ExactModulesShardAudit (env : RepoEnv) (shard : List String) : Prop :=
  ∀ r ∈ env.decls, r.originMod ∈ shard →
    r.isUnsafeOrPartial = false ∧
    ∀ d, TransDep env r.name d →
      ∃ dr, env.lookup d = some dr ∧
        dr.isUnsafeOrPartial = false ∧
        (dr.isAxiom = true → d ∈ env.permittedAxioms)

/-- **Flagship Sharding Soundness Theorem (`shardAxiomUnion_sound`)**:
    If `--orphan-only` validates `ShardPartitionValid` and every `--exact-modules`
    shard passes `ExactModulesShardAudit`, then:
    1. `MonolithicAuditSafe env` holds globally (zero orphans, zero unsafe/partial,
       all transitively reached axioms `⊆ env.permittedAxioms`), AND
    2. The union of axioms transitively reached across shards equals the monolithic
       reached-axiom set, and every reached axiom lies in `env.permittedAxioms`. -/
theorem shardAxiomUnion_sound {env : RepoEnv} {shards : List (List String)}
    (hPart : ShardPartitionValid env.registeredModules env.onDiskModules shards)
    (hShards : ∀ s ∈ shards, ExactModulesShardAudit env s) :
    MonolithicAuditSafe env ∧
      (∀ a, ReachesAxiomFrom env env.registeredModules a ↔
        ∃ s ∈ shards, ReachesAxiomFrom env s a) ∧
      (∀ s ∈ shards, ∀ a, ReachesAxiomFrom env s a → a ∈ env.permittedAxioms) := by
  have hMono : MonolithicAuditSafe env :=
    { no_orphans := hPart.no_on_disk_orphans
      decls_safe := fun r hr hModReg => by
        obtain ⟨s, hs, hModS⟩ := hPart.covers_registered r.originMod hModReg
        exact hShards s hs r hr hModS }
  refine ⟨hMono, ?_, ?_⟩
  · intro a
    constructor
    · rintro ⟨r, hr, hModReg, hDep, ra, hL, hAx⟩
      obtain ⟨s, hs, hModS⟩ := hPart.covers_registered r.originMod hModReg
      exact ⟨s, hs, r, hr, hModS, hDep, ra, hL, hAx⟩
    · rintro ⟨s, hs, r, hr, hModS, hDep, ra, hL, hAx⟩
      exact ⟨r, hr, hPart.subset_registered s hs r.originMod hModS, hDep, ra, hL, hAx⟩
  · intro s hs a ⟨r, hr, hModS, hDep, ra, hL, hAx⟩
    obtain ⟨_, hWalk⟩ := hShards s hs r hr hModS
    obtain ⟨dr, hLdr, _, hPerm⟩ := hWalk a hDep
    rw [hL] at hLdr
    cases hLdr
    exact hPerm hAx

/-! ### 3.1 Multi-Hop Cross-Shard Chain & Naive Truncated-Shard Counterexamples -/

/-- Concrete 3-shard declarations forming `M1 ∈ S1 -> M2 ∈ S2 -> M3 ∈ S3 -> badAxiom`. -/
def m1EntryDecl : DeclRecord :=
  { name := "M1.entry", originMod := "M1", isAxiom := false,
    isUnsafeOrPartial := false, directDeps := ["M2.mid"] }

def m2MidDecl : DeclRecord :=
  { name := "M2.mid", originMod := "M2", isAxiom := false,
    isUnsafeOrPartial := false, directDeps := ["M3.leaf"] }

def m3LeafDecl : DeclRecord :=
  { name := "M3.leaf", originMod := "M3", isAxiom := false,
    isUnsafeOrPartial := false, directDeps := ["M3.badAxiom"] }

def m3BadAxiomDecl : DeclRecord :=
  { name := "M3.badAxiom", originMod := "M3", isAxiom := true,
    isUnsafeOrPartial := false, directDeps := [] }

/-- Concrete 3-shard repository with cross-shard chain
    `M1 ∈ S1 -> M2 ∈ S2 -> M3 ∈ S3 -> badAxiom` (where `badAxiom ∉ permittedAxioms`). -/
def threeShardCrossChainEnv : RepoEnv :=
  { registeredModules := ["M1", "M2", "M3"]
    onDiskModules := ["M1", "M2", "M3"]
    permittedAxioms := ["propext", "Classical.choice", "Quot.sound"]
    decls := [m1EntryDecl, m2MidDecl, m3LeafDecl, m3BadAxiomDecl] }

/-- Shard `["M1"]`'s full transitive walk catches `M3.badAxiom` three hops away
    across shards `S1 -> S2 -> S3`! -/
theorem crossShardThreeHop_caught_by_shard1 :
    ¬ ExactModulesShardAudit threeShardCrossChainEnv ["M1"] := by
  intro hAudit
  have hEntryMem : m1EntryDecl ∈ threeShardCrossChainEnv.decls := by decide
  have hWalk := (hAudit _ hEntryMem (by decide)).2
  have hChain : TransDep threeShardCrossChainEnv "M1.entry" "M3.badAxiom" :=
    TransDep.step (c' := "M2.mid") (rec := m1EntryDecl) (by decide) (by decide)
      (TransDep.step (c' := "M3.leaf") (rec := m2MidDecl) (by decide) (by decide)
        (TransDep.step (c' := "M3.badAxiom") (rec := m3LeafDecl) (by decide) (by decide)
          (TransDep.refl _)))
  obtain ⟨dr, hL, _, hPerm⟩ := hWalk "M3.badAxiom" hChain
  have hExp : threeShardCrossChainEnv.lookup "M3.badAxiom" = some m3BadAxiomDecl := by decide
  rw [hExp] at hL
  have hEq : dr = m3BadAxiomDecl := Option.some.inj hL.symm
  subst hEq
  have hInPerm := hPerm rfl
  revert hInPerm
  decide

/-- Naive shard-truncated audit that stops walking edges outside `shard`. -/
def NaiveTruncatedShardAudit (env : RepoEnv) (shard : List String) : Prop :=
  ∀ r ∈ env.decls, r.originMod ∈ shard →
    r.isUnsafeOrPartial = false ∧
    ∀ d ∈ r.directDeps,
      ∀ dr, env.lookup d = some dr → dr.originMod ∈ shard →
        dr.isUnsafeOrPartial = false ∧ (dr.isAxiom = true → d ∈ env.permittedAxioms)

/-- **Why full transitive walks matter**: naive shard-truncated audit PASSES on `S1 = ["M1"]`
    even though `M1.entry` transitively depends on `M3.badAxiom`! -/
theorem truncatedShardAudit_misses_crossShard_badAxiom :
    NaiveTruncatedShardAudit threeShardCrossChainEnv ["M1"] ∧
      ¬ ExactModulesShardAudit threeShardCrossChainEnv ["M1"] := by
  refine ⟨?_, crossShardThreeHop_caught_by_shard1⟩
  intro r hr hMod
  simp only [List.mem_singleton] at hMod
  simp only [threeShardCrossChainEnv, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · refine ⟨rfl, ?_⟩
    intro d hd dr hL hInS
    simp only [m1EntryDecl, List.mem_singleton] at hd
    subst hd
    have hExp : threeShardCrossChainEnv.lookup "M2.mid" = some m2MidDecl := by decide
    rw [hExp] at hL
    have hEq : dr = m2MidDecl := Option.some.inj hL.symm
    subst hEq
    exact absurd hInS (by decide)
  · exact absurd hMod (by decide)
  · exact absurd hMod (by decide)
  · exact absurd hMod (by decide)

/-- **Case-fold collision**: `Anneal.Foo` and `Anneal.foo` alias one file on
    case-insensitive filesystems, so a shard plan listing both would audit one `.olean`
    twice (or silently shadow the other); `checkShardPartition` rejects it. -/
theorem caseFoldCollision_rejected_by_checkShardPartition :
    (checkShardPartition ["Anneal.Foo", "Anneal.foo"] ["Anneal.Foo", "Anneal.foo"]
        [["Anneal.Foo"], ["Anneal.foo"]]).any
      (fun v => v.code == .moduleNameCollision && v.subject == "Anneal.Foo") = true := by
  decide

/-- **Why `--orphan-only` matters**: omitting an unregistered on-disk orphan module
    causes `checkShardPartition` to emit `unregisteredOnDiskOrphan`. -/
theorem orphanModule_rejected_by_checkShardPartition :
    (checkShardPartition ["M1"] ["M1", "OrphanBad"] [["M1"]]).any
      (fun v => v.code == .unregisteredOnDiskOrphan && v.subject == "OrphanBad") = true := by
  decide

/-! ### 3.2 Cross-Shard Duplicate Consistency & Fingerprint Reconciliation (A1)

When lazily-realized reserved declarations (such as `.eq_k` equation lemmas) or forged
duplicates appear in two different modules belonging to *distinct* shards, shard-local
checks alone cannot observe the conflict. Exporting each shard's per-declaration canonical
fingerprint table and reconciling across shards restores exact monolithic completeness. -/

/-- A module-tagged declaration fingerprint entry exported by an audited `.olean` shard. -/
structure ModDeclFingerprint : Type where
  modName : String
  declName : String
  fingerprint : String
  deriving DecidableEq, Repr, Inhabited

/-- Monolithic duplicate consistency: any two entries from registered modules sharing
    `declName` must agree on `fingerprint`. -/
def MonolithicDuplicateConsistent (registered : List String)
    (entries : List ModDeclFingerprint) : Prop :=
  ∀ e₁ ∈ entries, ∀ e₂ ∈ entries,
    e₁.modName ∈ registered → e₂.modName ∈ registered →
    e₁.declName = e₂.declName → e₁.fingerprint = e₂.fingerprint

/-- Shard-local duplicate consistency: checks agreement only among entries whose modules
    reside inside the *same* shard. -/
def ShardLocalDuplicateConsistent (shard : List String)
    (entries : List ModDeclFingerprint) : Prop :=
  ∀ e₁ ∈ entries, ∀ e₂ ∈ entries,
    e₁.modName ∈ shard → e₂.modName ∈ shard →
    e₁.declName = e₂.declName → e₁.fingerprint = e₂.fingerprint

/-- Cross-shard fingerprint reconciliation table: checks agreement across EVERY pair of
    exported shard tables `(s₁, s₂)` in `shards`. -/
def CrossShardFingerprintReconciled (shards : List (List String))
    (entries : List ModDeclFingerprint) : Prop :=
  ∀ s₁ ∈ shards, ∀ s₂ ∈ shards, ∀ e₁ ∈ entries, ∀ e₂ ∈ entries,
    e₁.modName ∈ s₁ → e₂.modName ∈ s₂ →
    e₁.declName = e₂.declName → e₁.fingerprint = e₂.fingerprint

/-- Computable cross-shard fingerprint reconciliation check returning
    `crossShardDuplicateConflict` for every conflicting declaration across shards. -/
def checkCrossShardFingerprints (shards : List (List String))
    (entries : List ModDeclFingerprint) : List ShardAuditViolation :=
  let covered := shards.flatten
  let active := entries.filter (fun e => covered.contains e.modName)
  active.flatMap fun e₁ =>
    if active.any (fun e₂ => e₂.declName == e₁.declName && e₂.fingerprint != e₁.fingerprint) then
      [{ code := .crossShardDuplicateConflict, subject := e₁.declName }]
    else []

/-- **Sharding Completeness Hole Witness (closes B1 Open Issue 2)**:
    Two shards `["M1"]` and `["M2"]` both pass `ShardLocalDuplicateConsistent` even when
    `M1` and `M2` disagree on `evalRvalue.eq_4`'s fingerprint — violating
    `MonolithicDuplicateConsistent`. `checkCrossShardFingerprints` catches the conflict! -/
def crossShardConflictEntries : List ModDeclFingerprint :=
  [{ modName := "M1", declName := "evalRvalue.eq_4", fingerprint := "fp_v1" },
   { modName := "M2", declName := "evalRvalue.eq_4", fingerprint := "fp_v2" }]

theorem shardLocalDupCheck_misses_crossShard_conflict :
    ShardLocalDuplicateConsistent ["M1"] crossShardConflictEntries ∧
    ShardLocalDuplicateConsistent ["M2"] crossShardConflictEntries ∧
    ¬ MonolithicDuplicateConsistent ["M1", "M2"] crossShardConflictEntries ∧
    (checkCrossShardFingerprints [["M1"], ["M2"]] crossShardConflictEntries).any
      (fun v => v.code == .crossShardDuplicateConflict && v.subject == "evalRvalue.eq_4") = true := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro e₁ h₁ e₂ h₂ hm₁ hm₂ _
    simp only [crossShardConflictEntries, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
    rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
    · rfl
    · exact absurd hm₂ (by decide)
    · exact absurd hm₁ (by decide)
    · exact absurd hm₁ (by decide)
  · intro e₁ h₁ e₂ h₂ hm₁ hm₂ _
    simp only [crossShardConflictEntries, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
    rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
    · exact absurd hm₁ (by decide)
    · exact absurd hm₁ (by decide)
    · exact absurd hm₂ (by decide)
    · rfl
  · intro hMono
    have hEq := hMono
      { modName := "M1", declName := "evalRvalue.eq_4", fingerprint := "fp_v1" } (by decide)
      { modName := "M2", declName := "evalRvalue.eq_4", fingerprint := "fp_v2" } (by decide)
      (by decide) (by decide) rfl
    exact absurd hEq (by decide)

/-- **Cross-Shard Fingerprint Reconciliation Soundness & Completeness**:
    Under `ShardPartitionValid`, `checkCrossShardFingerprints shards entries = []` holds
    if and only if `MonolithicDuplicateConsistent registered entries` holds globally. -/
theorem crossShardFingerprintReconciliation_sound
    {registered onDisk : List String} {shards : List (List String)}
    {entries : List ModDeclFingerprint}
    (hPart : ShardPartitionValid registered onDisk shards) :
    checkCrossShardFingerprints shards entries = [] ↔
      MonolithicDuplicateConsistent registered entries := by
  have hCovIff : ∀ m, shards.flatten.contains m = true ↔ m ∈ registered := by
    intro m
    rw [List.contains_iff_mem, List.mem_flatten]
    constructor
    · rintro ⟨s, hs, hms⟩
      exact hPart.subset_registered s hs m hms
    · intro hm
      exact hPart.covers_registered m hm
  unfold checkCrossShardFingerprints MonolithicDuplicateConsistent
  constructor
  · intro hNil e₁ h₁ e₂ h₂ hm₁ hm₂ hName
    have hAct₁ : e₁ ∈ entries.filter (fun e => shards.flatten.contains e.modName) :=
      List.mem_filter.mpr ⟨h₁, (hCovIff e₁.modName).mpr hm₁⟩
    have hAct₂ : e₂ ∈ entries.filter (fun e => shards.flatten.contains e.modName) :=
      List.mem_filter.mpr ⟨h₂, (hCovIff e₂.modName).mpr hm₂⟩
    have hItem := (List.flatMap_eq_nil_iff.mp hNil) e₁ hAct₁
    by_cases hFp : e₁.fingerprint = e₂.fingerprint
    · exact hFp
    · have hAny : (entries.filter (fun e => shards.flatten.contains e.modName)).any
          (fun e => e.declName == e₁.declName && e.fingerprint != e₁.fingerprint) = true := by
        rw [List.any_eq_true]
        refine ⟨e₂, hAct₂, ?_⟩
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
        exact ⟨hName.symm, fun h => hFp h.symm⟩
      simp only [hAny, ↓reduceIte] at hItem
      cases hItem
  · intro hMono
    rw [List.flatMap_eq_nil_iff]
    intro e₁ hAct₁
    have ⟨h₁, hC₁⟩ := List.mem_filter.mp hAct₁
    have hm₁ := (hCovIff e₁.modName).mp hC₁
    by_cases hAny : (entries.filter (fun e => shards.flatten.contains e.modName)).any
        (fun e => e.declName == e₁.declName && e.fingerprint != e₁.fingerprint) = true
    · rw [List.any_eq_true] at hAny
      obtain ⟨e₂, hAct₂, hCond⟩ := hAny
      have ⟨h₂, hC₂⟩ := List.mem_filter.mp hAct₂
      have hm₂ := (hCovIff e₂.modName).mp hC₂
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hCond
      exact absurd (hMono e₂ h₂ e₁ h₁ hm₂ hm₁ hCond.1) hCond.2
    · rw [Bool.not_eq_true] at hAny
      simp only [hAny, Bool.false_eq_true, ↓reduceIte]

/-! ### 3.3 Lossy Digests Break Cross-Shard Reconciliation (B2)

`checkCrossShardFingerprints` is exact ONLY when the exported fingerprint is an injective
encoding of the compared `ConstantInfo` payload. A non-injective digest (e.g. Lean 4.34.1
`Expr.hash`, whose `Nat` literal hash truncates to `UInt64`, so `5` and `5 + 2^64` collide)
lets two shards ship conflicting duplicates that a monolithic load rejects. -/

/-- Module-tagged declaration with its exact (abstractly serialized) payload. -/
structure ModDeclPayload : Type where
  modName : String
  declName : String
  payload : List Nat
  deriving DecidableEq, Repr, Inhabited

/-- Exact monolithic duplicate consistency over payloads (what loading compares). -/
def ExactDuplicateConsistent (registered : List String)
    (entries : List ModDeclPayload) : Prop :=
  ∀ e₁ ∈ entries, ∀ e₂ ∈ entries,
    e₁.modName ∈ registered → e₂.modName ∈ registered →
    e₁.declName = e₂.declName → e₁.payload = e₂.payload

/-- Export each payload through a digest function. -/
def digestEntries (digest : List Nat → String) (entries : List ModDeclPayload) :
    List ModDeclFingerprint :=
  entries.map fun e => { modName := e.modName, declName := e.declName, fingerprint := digest e.payload }

/-- **Lossy-digest unsoundness**: ANY digest collision between distinct payloads yields a
    two-shard repository that cross-shard reconciliation accepts but monolithic exact
    duplicate consistency rejects. -/
theorem lossyDigest_reconciliation_misses_conflict (digest : List Nat → String)
    {p q : List Nat} (hne : p ≠ q) (hcol : digest p = digest q) :
    checkCrossShardFingerprints [["M1"], ["M2"]]
        (digestEntries digest [⟨"M1", "d", p⟩, ⟨"M2", "d", q⟩]) = [] ∧
      ¬ ExactDuplicateConsistent ["M1", "M2"] [⟨"M1", "d", p⟩, ⟨"M2", "d", q⟩] := by
  refine ⟨?_, ?_⟩
  · simp [checkCrossShardFingerprints, digestEntries, hcol]
  · intro h
    exact hne (h ⟨"M1", "d", p⟩ (by simp) ⟨"M2", "d", q⟩ (by simp) (by simp) (by simp) rfl)

/-- The `UInt64` truncation underlying Lean's `Nat` literal hash collides on `5` vs
    `5 + 2^64`. -/
theorem uint64NatTruncation_collides :
    (5 : Nat) % 18446744073709551616 = (5 + 18446744073709551616) % 18446744073709551616 ∧
      (5 : Nat) ≠ 5 + 18446744073709551616 := by
  decide

/-- **Exact reconciliation soundness**: with an INJECTIVE digest (exact structural
    comparison), cross-shard reconciliation coincides with monolithic exact duplicate
    consistency under a valid partition. -/
theorem injectiveDigest_reconciliation_exact {registered onDisk : List String}
    {shards : List (List String)} {entries : List ModDeclPayload}
    (digest : List Nat → String) (hInj : ∀ p q, digest p = digest q → p = q)
    (hPart : ShardPartitionValid registered onDisk shards) :
    checkCrossShardFingerprints shards (digestEntries digest entries) = [] ↔
      ExactDuplicateConsistent registered entries := by
  rw [crossShardFingerprintReconciliation_sound hPart]
  unfold MonolithicDuplicateConsistent ExactDuplicateConsistent digestEntries
  constructor
  · intro h e₁ h₁ e₂ h₂ hm₁ hm₂ hn
    exact hInj _ _ (h _ (List.mem_map.mpr ⟨e₁, h₁, rfl⟩) _ (List.mem_map.mpr ⟨e₂, h₂, rfl⟩)
      hm₁ hm₂ hn)
  · intro h f₁ hf₁ f₂ hf₂ hm₁ hm₂ hn
    obtain ⟨e₁, h₁, rfl⟩ := List.mem_map.mp hf₁
    obtain ⟨e₂, h₂, rfl⟩ := List.mem_map.mp hf₂
    simp only at hm₁ hm₂ hn ⊢
    rw [h e₁ h₁ e₂ h₂ hm₁ hm₂ hn]

/-- Constant constructor tags mirroring Lean's `ConstantInfo` constructors. -/
inductive ConstKindTag : Type where
  | axiomDecl
  | defnDecl
  | thmDecl
  | opaqueDecl
  | quotDecl
  | inductDecl
  | ctorDecl
  | recDecl
  deriving DecidableEq, Repr, Inhabited

/-- Typed constant record modeling `ConstantInfo` fields compared during duplicate reconciliation. -/
structure TypedConstRecord : Type where
  kind : ConstKindTag
  levelParams : List String
  typeTag : String
  valueOpt : Option String
  metaTag : String
  isSafe : Bool := true
  deriving DecidableEq, Repr, Inhabited

/-- Pre-A2 lossy compatibility predicate: short-circuits on `valueOpt == none` and fails to
    discriminate `ConstantInfo` constructors or inductive/ctor/recursor metadata. -/
def lossyValueOptCompat (a b : TypedConstRecord) : Bool :=
  a.levelParams == b.levelParams &&
    match a.kind, b.kind with
    | .thmDecl, .thmDecl => a.typeTag == b.typeTag
    | _, _ =>
      a.typeTag == b.typeTag &&
        (a.valueOpt == b.valueOpt || a.valueOpt.isNone || b.valueOpt.isNone)

/-- Hardened A2 exact structural compatibility predicate: discriminates every `ConstantInfo`
    constructor, rejects kind confusion (`axiom` vs `defn`), and requires full metadata and
    safety parity across duplicates. -/
def strictConstCompat (a b : TypedConstRecord) : Bool :=
  a.levelParams == b.levelParams &&
    match a.kind, b.kind with
    | .thmDecl, .thmDecl => a.typeTag == b.typeTag
    | ka, kb =>
      ka == kb && a.typeTag == b.typeTag && a.valueOpt == b.valueOpt &&
        a.metaTag == b.metaTag && a.isSafe == b.isSafe

/-- **Kind-Confusion & Metadata-Bypass Witness (A2)**: `lossyValueOptCompat` falsely accepts
    both an `axiom` masquerading as a `defn` of the same type AND two `inductDecl` duplicates
    with different `numIndices`/`isRec` metadata, whereas `strictConstCompat` rejects both! -/
theorem lossyCompat_accepts_axiom_vs_defn_and_forged_induct :
    let axRec : TypedConstRecord :=
      { kind := .axiomDecl, levelParams := [], typeTag := "Nat", valueOpt := none, metaTag := "" }
    let defRec : TypedConstRecord :=
      { kind := .defnDecl, levelParams := [], typeTag := "Nat", valueOpt := some "0", metaTag := "" }
    let indGood : TypedConstRecord :=
      { kind := .inductDecl, levelParams := [], typeTag := "Type", valueOpt := none,
        metaTag := "numIndices=0,isRec=false" }
    let indBad : TypedConstRecord :=
      { kind := .inductDecl, levelParams := [], typeTag := "Type", valueOpt := none,
        metaTag := "numIndices=1,isRec=true" }
    lossyValueOptCompat axRec defRec = true ∧
      strictConstCompat axRec defRec = false ∧
      lossyValueOptCompat indGood indBad = true ∧
      strictConstCompat indGood indBad = false := by
  decide

/-- For all non-theorem constants, `strictConstCompat` holds if and only if the two records
    are structurally identical. -/
theorem strictConstCompat_iff_eq_nonThm {a b : TypedConstRecord}
    (ha : a.kind ≠ .thmDecl) :
    strictConstCompat a b = true ↔ a = b := by
  cases a with
  | mk ka la ta va ma sa =>
    cases b with
    | mk kb lb tb vb mb sb =>
      simp only at ha
      cases ka <;> cases kb <;> simp_all [strictConstCompat] <;>
        exact fun _ =>
          ⟨fun ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩,
            fun ⟨h1, h2, h3, h4⟩ => ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩⟩

/-! ## 4. Pillar 3 — Four Peer-Verifier Spec-Boundary Soundness Guards -/

/-! ### 4.1 Guard 3 — Unsatisfiable Extern `ensures` (`creusot#2388`, rank `3`) -/

/-- Specification model of an external/intrinsic callable (`#[external_spec]` / `extern`). -/
structure ExternCallableSpec (X Y : Type) : Type where
  fnName : String
  isTrustedExtern : Bool
  isDiverging : Bool
  pre : X → Prop
  post : X → Y → Prop

/-- Caller continuation verification under a trusted extern contract:
    given `pre x`, the verifier assumes `post x y` when proving continuation `Q y`. -/
def ExternContinuationVerified {X Y : Type} (spec : ExternCallableSpec X Y)
    (x : X) (Q : Y → Prop) : Prop :=
  spec.pre x → ∀ y, spec.post x y → Q y

/-- Concrete `creusot#2388` fixture: non-diverging `core::ptr::read_volatile` carrying
    satisfiable precondition (`True`) and unsatisfiable `ensures(false)`. -/
def readVolatileBrokenSpec : ExternCallableSpec Nat Nat :=
  { fnName := "core::ptr::read_volatile"
    isTrustedExtern := true
    isDiverging := false
    pre := fun _ => True
    post := fun _ _ => False }

/-- **Soundness Collapse (`creusot#2388`)**: an unsatisfiable `ensures(false)` on a
    non-diverging extern lets a caller vacuously verify `Q := fun _ => False` for EVERY
    input, even though the real `read_volatile` returns concrete value `42` violating `Q`! -/
theorem readVolatile_ensures_false_collapse :
    (∀ x, ExternContinuationVerified readVolatileBrokenSpec x (fun _ => False)) ∧
      ∃ (x actualRet : Nat), readVolatileBrokenSpec.pre x ∧
        ¬ readVolatileBrokenSpec.post x actualRet := by
  refine ⟨fun _ _ _ hFalse => hFalse, 0, 42, trivial, fun h => h⟩

/-- General collapse: any non-diverging extern with satisfiable `pre` and pointwise-false
    `post` proves EVERY continuation property `Q` vacuously. -/
theorem unsatisfiableExternEnsures_derives_arbitrary_post {X Y : Type}
    (spec : ExternCallableSpec X Y) {x : X}
    (hUnsat : ∀ y, ¬ spec.post x y) :
    ∀ Q : Y → Prop, ExternContinuationVerified spec x Q :=
  fun _ _ y hPost => False.elim (hUnsat y hPost)

/-- Legacy (A0) flag-only formulation of Guard 3: trusts the self-declared
    `isDiverging` metadata bit. Retained ONLY to exhibit the bypass below. -/
def FlagOnlyExternEnsuresGuard {X Y : Type} (spec : ExternCallableSpec X Y) : Prop :=
  spec.isTrustedExtern = true → spec.isDiverging = false →
    ∀ x, spec.pre x → ∃ y, spec.post x y

/-- Guard 3 (`creusot#2388`): for every trusted extern,
    1. a declared-diverging spec must GENUINELY diverge: its return type `Y` is empty
       (`-> !`), so the `isDiverging` bit cannot be forged on an inhabited return type; and
    2. every non-diverging spec must admit at least one satisfying output `y` for every
       input `x` satisfying `pre x`.
    Genuinely diverging (`-> !`) functions and `requires(false)` (`unreachable_unchecked`)
    remain cleanly permitted. -/
def ExternEnsuresGuard {X Y : Type} (spec : ExternCallableSpec X Y) : Prop :=
  spec.isTrustedExtern = true →
    (spec.isDiverging = true → (Y → False)) ∧
    ∀ x, spec.pre x → spec.isDiverging = false → ∃ y, spec.post x y

/-- **Diverging Distinction**: genuinely diverging `-> !` functions (`abort`, `exit`,
    return type `PEmpty`) satisfy `ExternEnsuresGuard` vacuously without needing a return
    witness, and no execution can reach a return value. -/
def abortDivergingSpec : ExternCallableSpec Nat PEmpty :=
  { fnName := "core::intrinsics::abort"
    isTrustedExtern := true
    isDiverging := true
    pre := fun _ => True
    post := fun _ _ => False }

theorem divergingExtern_admissible :
    ExternEnsuresGuard abortDivergingSpec ∧ (PEmpty → False) :=
  ⟨fun _ => ⟨fun _ y => PEmpty.elim y, fun _ _ hNd => absurd hNd (by decide)⟩,
    fun y => PEmpty.elim y⟩

/-- **`unreachable_unchecked` Distinction**: explicit `requires(false)` satisfies
    `ExternEnsuresGuard` because no verified caller can discharge `pre x`. -/
def unreachableUncheckedSpec : ExternCallableSpec Nat Nat :=
  { fnName := "core::hint::unreachable_unchecked"
    isTrustedExtern := true
    isDiverging := false
    pre := fun _ => False
    post := fun _ _ => False }

theorem unreachableUnchecked_requires_false_admissible :
    ExternEnsuresGuard unreachableUncheckedSpec :=
  fun _ => ⟨fun hDiv => absurd hDiv (by decide), fun _ hPre _ => False.elim hPre⟩

/-- **Guard 3 Rejection**: `readVolatileBrokenSpec` fails `ExternEnsuresGuard`. -/
theorem externEnsuresGuard_rejects_readVolatileBrokenSpec :
    ¬ ExternEnsuresGuard readVolatileBrokenSpec := by
  intro hG
  obtain ⟨_, hFalse⟩ := (hG rfl).2 0 trivial rfl
  exact hFalse

/-- **Forged-Divergence Bypass (B1 regression)**: a trusted extern that falsely declares
    `isDiverging := true` while returning an INHABITED type (`Nat`) with `ensures(false)`
    passes the flag-only guard and still collapses every continuation to `False`, but is
    rejected by `ExternEnsuresGuard` because `Nat` is inhabited. -/
def lyingDivergingSpec : ExternCallableSpec Nat Nat :=
  { fnName := "core::ptr::read_volatile"
    isTrustedExtern := true
    isDiverging := true
    pre := fun _ => True
    post := fun _ _ => False }

theorem lyingDiverging_bypasses_flagOnly_but_rejected_by_guard :
    FlagOnlyExternEnsuresGuard lyingDivergingSpec ∧
      (∀ x, ExternContinuationVerified lyingDivergingSpec x (fun _ => False)) ∧
      ¬ ExternEnsuresGuard lyingDivergingSpec := by
  refine ⟨fun _ hNd => absurd hNd (by decide), fun _ _ _ hF => hF, ?_⟩
  intro hG
  exact (hG rfl).1 rfl 0

/-- **Guard 3 Soundness Restoration**: under `ExternEnsuresGuard`, a non-diverging
    trusted extern with satisfiable `pre` can NEVER derive `False` in its continuation,
    and any honest implementation `implFn` satisfying `spec.post x (implFn x)` transfers
    every verified continuation `Q` to the real return value `implFn x`. -/
theorem externEnsuresGuard_sound {X Y : Type} {spec : ExternCallableSpec X Y}
    (hTrusted : spec.isTrustedExtern = true)
    (hNonDiv : spec.isDiverging = false)
    (hGuard : ExternEnsuresGuard spec)
    (hPreSat : PreconditionSatisfiable spec.pre) :
    ¬ (∀ x, ExternContinuationVerified spec x (fun _ => False)) := by
  intro hBad
  obtain ⟨x, hx⟩ := hPreSat
  obtain ⟨y, hy⟩ := (hGuard hTrusted).2 x hx hNonDiv
  exact hBad x hx y hy

/-- **Guard 3 General Soundness**: under `ExternEnsuresGuard`, a trusted extern can make a
    satisfiable-precondition continuation vacuous ONLY when its return type is genuinely
    empty (true `-> !` divergence): every `pre`-satisfying input either admits a
    post-state witness or no return value can exist at all. -/
theorem externEnsuresGuard_vacuity_only_from_genuine_divergence {X Y : Type}
    {spec : ExternCallableSpec X Y}
    (hTrusted : spec.isTrustedExtern = true)
    (hGuard : ExternEnsuresGuard spec) :
    ∀ x, spec.pre x → (∃ y, spec.post x y) ∨ (Y → False) := by
  intro x hx
  cases hDiv : spec.isDiverging with
  | true => exact Or.inr ((hGuard hTrusted).1 hDiv)
  | false => exact Or.inl ((hGuard hTrusted).2 x hx hDiv)

/-- Continuation transfer for an honest returning extern implementation. -/
theorem externEnsuresGuard_continuation_transfer {X Y : Type}
    {spec : ExternCallableSpec X Y} (implFn : X → Y)
    (hHonest : ∀ x, spec.pre x → spec.post x (implFn x))
    {x : X} {Q : Y → Prop}
    (hPre : spec.pre x)
    (hCont : ExternContinuationVerified spec x Q)
    (hNonDiv : spec.isDiverging = false) :
    ExternEnsuresGuard spec ∧ Q (implFn x) :=
  ⟨fun _ => ⟨fun hDiv => absurd (hDiv.symm.trans hNonDiv) (by decide),
      fun x' hx' _ => ⟨implFn x', hHonest x' hx'⟩⟩,
    hCont hPre (implFn x) (hHonest x hPre)⟩

/-! ### 4.2 Guard 4 — `FnDef` Ghost-Token Coercion Ban (`creusot#2389`, rank `4`) -/

/-- How a Rust program references a one-shot ghost-token constructor
    (`Tokens::new` / `#[ghost_token_ctor]`). -/
inductive GhostTokenCtorUse : Type where
  /-- Direct call `Tokens::new()` in the single-entry authority (`main`). -/
  | directEntryCall (inSingleEntry : Bool)
  /-- Value binding `let f = Tokens::new` (Copy `TyKind::FnDef` value!). -/
  | fnDefValueBind (binding : String)
  /-- Coercion `let f : fn() -> Tokens = Tokens::new` or `as fn() -> Tokens`. -/
  | fnPtrCoercion
  /-- Closure capturing/wrapping the one-shot ctor `|| Tokens::new()`. -/
  | closureCapture
  /-- Passing constructor as a higher-order argument `call_twice(Tokens::new)`. -/
  | higherOrderArg (callee : String)
  deriving DecidableEq, Repr, Inhabited

/-- Worst-case invocation multiplicity achievable at runtime by a `GhostTokenCtorUse`
    because `TyKind::FnDef` and `fn()` pointers are `Copy` and reusable arbitrarily. -/
def GhostTokenCtorUse.maxRuntimeCalls : GhostTokenCtorUse → Nat
  | .directEntryCall true => 1
  | .directEntryCall false => 2
  | .fnDefValueBind _ => 2
  | .fnPtrCoercion => 2
  | .closureCapture => 2
  | .higherOrderArg _ => 2

/-- Sum of worst-case token issuances across all uses of a one-shot constructor. -/
def totalMaxTokenIssuances (uses : List GhostTokenCtorUse) : Nat :=
  uses.foldl (fun acc u => acc + u.maxRuntimeCalls) 0

/-- Linear/affine uniqueness invariant of a `NonAtomicInvariant` token authority:
    at most one unique token may ever be issued for the namespace (`issued ≤ 1`). -/
def TokenUniquenessHolds (issued : Nat) : Prop :=
  issued ≤ 1

/-- Exclusivity lemma: issuing two unique tokens for the same namespace violates
    `TokenUniquenessHolds` (`2 ≤ 1` is uninhabited). -/
theorem duplicateToken_violates_uniqueness {n : Nat} (h : 2 ≤ n) :
    ¬ TokenUniquenessHolds n := by
  unfold TokenUniquenessHolds
  omega

/-- **Soundness Collapse (`creusot#2389`)**: coercing `Tokens::new` via `fnDefValueBind`
    (`let f = Tokens::new; (f(), f())`) or `higherOrderArg` (`call_twice(Tokens::new)`)
    yields `totalMaxTokenIssuances = 2`, directly violating `TokenUniquenessHolds`! -/
theorem fndefCoercion_duplicates_token_collapse :
    ¬ TokenUniquenessHolds (totalMaxTokenIssuances [.fnDefValueBind "f"]) ∧
    ¬ TokenUniquenessHolds (totalMaxTokenIssuances [.fnPtrCoercion]) ∧
    ¬ TokenUniquenessHolds (totalMaxTokenIssuances [.closureCapture]) ∧
    ¬ TokenUniquenessHolds (totalMaxTokenIssuances [.higherOrderArg "call_twice"]) := by
  unfold TokenUniquenessHolds totalMaxTokenIssuances GhostTokenCtorUse.maxRuntimeCalls
  decide

/-- Guard 4 (`creusot#2389`): bans every non-call `FnDef`/coercion/closure/higher-order
    use and permits at most one single-entry direct call `Tokens::new()`. -/
def isDirectSingleEntryUse : GhostTokenCtorUse → Bool
  | .directEntryCall true => true
  | _ => false

def checkFnDefGhostTokenGuard (uses : List GhostTokenCtorUse) : Bool :=
  uses.all isDirectSingleEntryUse && (uses.length ≤ 1)

def FnDefGhostTokenGuard (uses : List GhostTokenCtorUse) : Prop :=
  checkFnDefGhostTokenGuard uses = true

/-- Direct single-entry call `Tokens::new()` is permitted. -/
theorem fndefGhostTokenGuard_allows_single_direct_call :
    FnDefGhostTokenGuard [.directEntryCall true] := by
  unfold FnDefGhostTokenGuard
  decide

/-- Every non-call coercion/binding/closure/higher-order use is rejected by Guard 4. -/
theorem fndefGhostTokenGuard_rejects_non_call_uses :
    ¬ FnDefGhostTokenGuard [.fnDefValueBind "f"] ∧
    ¬ FnDefGhostTokenGuard [.fnPtrCoercion] ∧
    ¬ FnDefGhostTokenGuard [.closureCapture] ∧
    ¬ FnDefGhostTokenGuard [.higherOrderArg "call_twice"] ∧
    ¬ FnDefGhostTokenGuard [.directEntryCall false] ∧
    ¬ FnDefGhostTokenGuard [.directEntryCall true, .directEntryCall true] := by
  unfold FnDefGhostTokenGuard
  decide

/-- **Guard 4 Soundness Restoration**: whenever `FnDefGhostTokenGuard uses` holds,
    `TokenUniquenessHolds (totalMaxTokenIssuances uses)` is guaranteed (`≤ 1` token). -/
theorem fndefGhostTokenGuard_preserves_uniqueness {uses : List GhostTokenCtorUse}
    (hGuard : FnDefGhostTokenGuard uses) :
    TokenUniquenessHolds (totalMaxTokenIssuances uses) := by
  unfold FnDefGhostTokenGuard checkFnDefGhostTokenGuard at hGuard
  rw [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hGuard
  obtain ⟨hAll, hLen⟩ := hGuard
  cases uses with
  | nil =>
    unfold TokenUniquenessHolds totalMaxTokenIssuances
    decide
  | cons u rest =>
    cases rest with
    | nil =>
      have hU := hAll u (List.mem_cons_self ..)
      cases u with
      | directEntryCall b =>
        cases b with
        | true =>
          unfold TokenUniquenessHolds totalMaxTokenIssuances GhostTokenCtorUse.maxRuntimeCalls
          decide
        | false => cases hU
      | fnDefValueBind _ | fnPtrCoercion | closureCapture | higherOrderArg _ => cases hU
    | cons _ _ =>
      simp only [List.length_cons] at hLen
      omega

/-! #### 4.2.1 Operational Ghost-Token Program Model (B2)

The table `GhostTokenCtorUse.maxRuntimeCalls` above is a stipulated multiplicity. The
model below derives issuance counts from an operational semantics: a bound `FnDef` value
(`let f = Tokens::new`) is `Copy` and can be invoked arbitrarily often, and loops repeat
their body. -/

/-- Tiny program language over one one-shot ghost-token constructor. -/
inductive TokProg : Type where
  | skip
  /-- Direct call `Tokens::new()`. -/
  | callCtor
  /-- `let f = Tokens::new` / `fn()` coercion / closure capture (binds a reusable value). -/
  | bindCtorValue
  /-- `f()` on the bound constructor value. -/
  | invokeBound
  | seq (a b : TokProg)
  /-- Body executed exactly `n` times. -/
  | loop (n : Nat) (body : TokProg)
  deriving DecidableEq, Repr, Inhabited

/-- Iterate a state transformer `n` times, summing issuance counts. -/
def iterRun (f : Bool → Nat × Bool) : Nat → Bool → Nat × Bool
  | 0, b => (0, b)
  | k + 1, b =>
    let r₁ := f b
    let r₂ := iterRun f k r₁.2
    (r₁.1 + r₂.1, r₂.2)

/-- Operational semantics: `(tokens issued, ctor value bound?)`. -/
def TokProg.run : TokProg → Bool → Nat × Bool
  | .skip, b => (0, b)
  | .callCtor, b => (1, b)
  | .bindCtorValue, _ => (0, true)
  | .invokeBound, b => (if b then 1 else 0, b)
  | .seq p q, b =>
    let r₁ := p.run b
    let r₂ := q.run r₁.2
    (r₁.1 + r₂.1, r₂.2)
  | .loop n body, b => iterRun body.run n b

/-- Number of syntactic direct call sites. -/
def TokProg.callSites : TokProg → Nat
  | .callCtor => 1
  | .seq p q => p.callSites + q.callSites
  | .loop _ body => body.callSites
  | _ => 0

/-- Whether any non-call `FnDef` value use (bind / invoke) occurs. -/
def TokProg.hasValueUse : TokProg → Bool
  | .bindCtorValue => true
  | .invokeBound => true
  | .seq p q => p.hasValueUse || q.hasValueUse
  | .loop _ body => body.hasValueUse
  | _ => false

/-- Whether a direct call site sits under a loop. -/
def TokProg.callUnderLoop : TokProg → Bool
  | .seq p q => p.callUnderLoop || q.callUnderLoop
  | .loop _ body => body.callSites != 0
  | _ => false

/-- Executable Guard 4 over programs (mirrors the Python single-entry authority check). -/
def tokProgGuard (p : TokProg) : Bool :=
  !p.hasValueUse && !p.callUnderLoop && p.callSites ≤ 1

private theorem iterRun_zero {f : Bool → Nat × Bool} (hf : ∀ b, f b = (0, b)) :
    ∀ n b, iterRun f n b = (0, b) := by
  intro n
  induction n with
  | zero => intro b; rfl
  | succ k ih => intro b; simp [iterRun, hf, ih]

private theorem TokProg.callUnderLoop_of_noCalls :
    ∀ p : TokProg, p.callSites = 0 → p.callUnderLoop = false := by
  intro p
  induction p with
  | seq a c iha ihc =>
    intro h
    simp only [TokProg.callSites] at h
    simp only [TokProg.callUnderLoop, Bool.or_eq_false_iff]
    exact ⟨iha (by omega), ihc (by omega)⟩
  | loop n body _ =>
    intro h
    simp only [TokProg.callSites] at h
    simp [TokProg.callUnderLoop, h]
  | _ => intro _; rfl

private theorem TokProg.run_noValue_bound {p : TokProg}
    (hV : p.hasValueUse = false) (hL : p.callUnderLoop = false) :
    ∀ b, (p.run b).1 ≤ p.callSites ∧ (p.run b).2 = b := by
  induction p with
  | skip => intro b; simp [TokProg.run, TokProg.callSites]
  | callCtor => intro b; simp [TokProg.run, TokProg.callSites]
  | bindCtorValue => simp [TokProg.hasValueUse] at hV
  | invokeBound => simp [TokProg.hasValueUse] at hV
  | seq a c iha ihc =>
    simp only [TokProg.hasValueUse, Bool.or_eq_false_iff] at hV
    simp only [TokProg.callUnderLoop, Bool.or_eq_false_iff] at hL
    intro b
    obtain ⟨ha1, ha2⟩ := iha hV.1 hL.1 b
    obtain ⟨hc1, hc2⟩ := ihc hV.2 hL.2 (a.run b).2
    simp only [TokProg.run, TokProg.callSites]
    exact ⟨by omega, by rw [hc2, ha2]⟩
  | loop n body ih =>
    simp only [TokProg.hasValueUse] at hV
    simp only [TokProg.callUnderLoop, bne_eq_false_iff_eq] at hL
    have hBody : ∀ b, body.run b = (0, b) := by
      intro b
      obtain ⟨h1, h2⟩ := ih hV (TokProg.callUnderLoop_of_noCalls body hL) b
      have h0 : (body.run b).1 = 0 := by omega
      exact Prod.ext h0 h2
    intro b
    simp [TokProg.run, iterRun_zero hBody, TokProg.callSites]

/-- **Operational Guard 4 Soundness**: every program accepted by `tokProgGuard` issues at
    most ONE token, for every loop bound. -/
theorem tokProgGuard_sound {p : TokProg} (hG : tokProgGuard p = true) :
    TokenUniquenessHolds (p.run false).1 := by
  unfold tokProgGuard at hG
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hG
  obtain ⟨⟨hV, hL⟩, hC⟩ := hG
  have := (TokProg.run_noValue_bound hV hL false).1
  unfold TokenUniquenessHolds
  omega

/-- **Operational Collapse**: `let f = Tokens::new; f(); f()` and a direct call in a
    2-iteration loop both issue TWO tokens, and both are rejected by `tokProgGuard`. -/
theorem tokProg_valueUse_and_loop_duplicate_tokens :
    (TokProg.seq .bindCtorValue (.seq .invokeBound .invokeBound)).run false = (2, true) ∧
    (TokProg.loop 2 .callCtor).run false = (2, false) ∧
    tokProgGuard (.seq .bindCtorValue (.seq .invokeBound .invokeBound)) = false ∧
    tokProgGuard (.loop 2 .callCtor) = false ∧
    tokProgGuard (.seq .callCtor .callCtor) = false ∧
    tokProgGuard (.seq .skip (.loop 5 .skip)) = true ∧
    tokProgGuard .callCtor = true := by
  decide

/-! ### 4.3 Guard 5 — External-Type `Drop` Omission (`verus#3514`, rank `5`) -/

/-- Specification metadata for an external Rust type declaration. -/
structure ExternalTypeSpec : Type where
  typeName : String
  hasExternalTypeSpec : Bool
  hasExternalBody : Bool
  implementsDrop : Bool
  fieldHasDropGlue : Bool
  dropSpecModeled : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Whether the underlying Rust type runs implicit destructor code at scope exit. -/
def ExternalTypeSpec.hasDropGlue (t : ExternalTypeSpec) : Bool :=
  t.implementsDrop || t.fieldHasDropGlue

/-- Concrete scope-exit execution semantics with and without modeled drop glue. -/
def scopeExitState (hasDrop : Bool) (dropEffect : Nat → Nat) (s : Nat) : Nat :=
  if hasDrop then dropEffect s else s

/-- **Soundness Collapse (`verus#3514`)**: a `#[external_type_specification]` type whose
    underlying Rust type has `Drop` (or transitive drop glue) mutating state `0 ↦ 1`
    causes an unguarded verifier (which omits `dropEffect` at scope exit) to certify
    `Inv 0` (`s = 0`), while real Rust execution ends in state `1` violating `Inv`! -/
theorem externalTypeDropOmission_breaks_invariant :
    let inv : Nat → Prop := fun s => s = 0
    let dropEffect : Nat → Nat := fun s => s + 1
    let verifierModeledExit := scopeExitState false dropEffect 0
    let rustRealExit := scopeExitState true dropEffect 0
    inv verifierModeledExit ∧ ¬ inv rustRealExit :=
  ⟨rfl, by decide⟩

/-- Guard 5 (`verus#3514`):
    1. Rejects combining `external_type_specification` with `external_body` whenever
       `hasDropGlue = true`.
    2. Rejects any `external_type_specification` with `hasDropGlue = true` unless
       `dropSpecModeled = true`. -/
def checkExternalTypeDropGuard (t : ExternalTypeSpec) : Option PeerGuardViolationCode :=
  if t.hasExternalTypeSpec && t.hasDropGlue then
    if t.hasExternalBody then some .externalTypeBodyWithDrop
    else if !t.dropSpecModeled then some .externalTypeDropOmission
    else none
  else none

def ExternalTypeDropGuard (t : ExternalTypeSpec) : Prop :=
  checkExternalTypeDropGuard t = none

theorem externalTypeDropGuard_rejects_unmodeled_drop :
    checkExternalTypeDropGuard
      { typeName := "DropGuard", hasExternalTypeSpec := true, hasExternalBody := false,
        implementsDrop := true, fieldHasDropGlue := false, dropSpecModeled := false } =
      some .externalTypeDropOmission :=
  rfl

theorem externalTypeDropGuard_rejects_transitive_drop_glue :
    checkExternalTypeDropGuard
      { typeName := "WrapperWithVec", hasExternalTypeSpec := true, hasExternalBody := false,
        implementsDrop := false, fieldHasDropGlue := true, dropSpecModeled := false } =
      some .externalTypeDropOmission :=
  rfl

theorem externalTypeDropGuard_rejects_external_body_with_drop :
    checkExternalTypeDropGuard
      { typeName := "OpaqueDropBox", hasExternalTypeSpec := true, hasExternalBody := true,
        implementsDrop := true, fieldHasDropGlue := false, dropSpecModeled := true } =
      some .externalTypeBodyWithDrop :=
  rfl

theorem externalTypeDropGuard_allows_copy_no_drop_type :
    ExternalTypeDropGuard
      { typeName := "PlainPair", hasExternalTypeSpec := true, hasExternalBody := false,
        implementsDrop := false, fieldHasDropGlue := false, dropSpecModeled := false } :=
  rfl

theorem externalTypeDropGuard_allows_modeled_drop_without_external_body :
    ExternalTypeDropGuard
      { typeName := "ModeledGuard", hasExternalTypeSpec := true, hasExternalBody := false,
        implementsDrop := true, fieldHasDropGlue := false, dropSpecModeled := true } :=
  rfl

/-- **Guard 5 Soundness Restoration**: when `ExternalTypeDropGuard t` holds and the
    verifier checks the drop obligation whenever `t.dropSpecModeled = true`, the real
    Rust scope-exit state `scopeExitState t.hasDropGlue dropEffect s` preserves `Inv`. -/
theorem externalTypeDropGuard_preserves_scope_exit_invariant
    {t : ExternalTypeSpec} {inv : Nat → Prop} {dropEffect : Nat → Nat} {s : Nat}
    (hSpec : t.hasExternalTypeSpec = true)
    (hGuard : ExternalTypeDropGuard t)
    (hPreExit : inv s)
    (hDropVerified : t.dropSpecModeled = true → inv s → inv (dropEffect s)) :
    inv (scopeExitState t.hasDropGlue dropEffect s) := by
  unfold ExternalTypeDropGuard checkExternalTypeDropGuard at hGuard
  cases hGlue : t.hasDropGlue with
  | false =>
    simpa [scopeExitState, hGlue] using hPreExit
  | true =>
    simp only [hSpec, hGlue, Bool.and_self, ↓reduceIte] at hGuard
    cases hBody : t.hasExternalBody with
    | true => rw [hBody] at hGuard; cases hGuard
    | false =>
      rw [hBody] at hGuard
      simp only [Bool.false_eq_true, ↓reduceIte] at hGuard
      cases hMod : t.dropSpecModeled with
      | false => rw [hMod] at hGuard; cases hGuard
      | true =>
        simpa [scopeExitState, hGlue] using hDropVerified hMod hPreExit

/-! ### 4.4 Guard 6 — Assumption Polarity (`Verifrag` cl/1029131309) & Struct Sealing (`Samite` cl/1029680381) -/

/-! #### 4.4.1 Part 6a: Assumption Polarity & Constructive Counterexample Soundness -/

/-- Evaluation result of a specification or implementation model on an input. -/
structure EvalRes (Val : Type) : Type where
  assumesHold : Bool
  assertionFailed : Bool
  output : Val
  deriving DecidableEq, Repr, Inhabited

/-- Canonical negative-polarity equivalence/correspondence obligation:
    implementation and specification assumptions sit in **negative** (antecedent)
    polarity (`specRes.assumesHold ∧ implRes.assumesHold ∧ ¬specRes.assertionFailed → ...`). -/
def CorrectEquivObligation {Val : Type} (specRes implRes : EvalRes Val) : Prop :=
  (specRes.assumesHold = true ∧ implRes.assumesHold = true ∧ specRes.assertionFailed = false) →
    (implRes.assertionFailed = false ∧ implRes.output = specRes.output)

/-- Polarity in a propositional formula (`pos` = consequent/conclusion, `neg` = antecedent/hypothesis). -/
inductive Polarity : Type where
  | pos
  | neg
  deriving DecidableEq, Repr, Inhabited

def Polarity.flip : Polarity → Polarity
  | .pos => .neg
  | .neg => .pos

/-- Propositional formula AST distinguishing assumption atoms from ordinary obligation atoms,
    including biconditionals (`iff`) and conditionals (`ifte`) where both polarities occur. -/
inductive PropFormula : Type where
  | atom (tag : String)
  | assumes (tag : String)
  | not (p : PropFormula)
  | and (p q : PropFormula)
  | or (p q : PropFormula)
  | imp (p q : PropFormula)
  | iff (p q : PropFormula)
  | ifte (c t e : PropFormula)
  deriving DecidableEq, Repr, Inhabited

/-- Recursive polarity checker verifying that every `assumes` occurrence appears
    strictly in negative polarity (`pol = .neg`). Both `iff` operands and the condition
    of `ifte` (`(c → t) ∧ (¬c → e)`) sit in BOTH positive and negative polarity! -/
def assumesOnlyNegative : Polarity → PropFormula → Bool
  | _, .atom _ => true
  | .neg, .assumes _ => true
  | .pos, .assumes _ => false
  | pol, .not p => assumesOnlyNegative pol.flip p
  | pol, .and p q => assumesOnlyNegative pol p && assumesOnlyNegative pol q
  | pol, .or p q => assumesOnlyNegative pol p && assumesOnlyNegative pol q
  | pol, .imp p q => assumesOnlyNegative pol.flip p && assumesOnlyNegative pol q
  | _, .iff p q =>
    assumesOnlyNegative .pos p && assumesOnlyNegative .neg p &&
      assumesOnlyNegative .pos q && assumesOnlyNegative .neg q
  | pol, .ifte c t e =>
    assumesOnlyNegative .pos c && assumesOnlyNegative .neg c &&
      assumesOnlyNegative pol t && assumesOnlyNegative pol e

/-- Top-level Guard 6a polarity check starting at positive root polarity. -/
def checkAssumesNegativePolarity (f : PropFormula) : Bool :=
  assumesOnlyNegative .pos f

/-- Semantic interpretation of equivalence formulas over `(specRes, implRes)`. -/
def evalEquivFormula {Val : Type} (specRes implRes : EvalRes Val) : PropFormula → Prop
  | .atom "spec.assertionFailed" => specRes.assertionFailed = true
  | .atom "impl.assertionFailed" => implRes.assertionFailed = true
  | .atom "outputEq" => implRes.output = specRes.output
  | .atom _ => False
  | .assumes "spec" => specRes.assumesHold = true
  | .assumes "impl" => implRes.assumesHold = true
  | .assumes _ => False
  | .not p => ¬ evalEquivFormula specRes implRes p
  | .and p q => evalEquivFormula specRes implRes p ∧ evalEquivFormula specRes implRes q
  | .or p q => evalEquivFormula specRes implRes p ∨ evalEquivFormula specRes implRes q
  | .imp p q => evalEquivFormula specRes implRes p → evalEquivFormula specRes implRes q
  | .iff p q => evalEquivFormula specRes implRes p ↔ evalEquivFormula specRes implRes q
  | .ifte c t e =>
    (evalEquivFormula specRes implRes c → evalEquivFormula specRes implRes t) ∧
      (¬ evalEquivFormula specRes implRes c → evalEquivFormula specRes implRes e)

/-- Canonical negative-polarity formula AST. -/
def correctEquivFormula : PropFormula :=
  .imp
    (.and (.and (.assumes "spec") (.assumes "impl")) (.not (.atom "spec.assertionFailed")))
    (.and (.not (.atom "impl.assertionFailed")) (.atom "outputEq"))

/-- Flipped-consequent formula putting assumptions in positive conclusion polarity. -/
def flippedConsequentFormula : PropFormula :=
  .imp
    (.and (.not (.atom "impl.assertionFailed")) (.atom "outputEq"))
    (.and (.assumes "spec") (.assumes "impl"))

/-- Disjunctive positive-polarity formula putting `impl.assumesHold` in a positive disjunct. -/
def positiveDisjunctFormula : PropFormula :=
  .imp
    (.and (.assumes "spec") (.not (.atom "spec.assertionFailed")))
    (.or (.assumes "impl") (.and (.not (.atom "impl.assertionFailed")) (.atom "outputEq")))

/-- Nested-implication trap `((assumes → P) → Q)` where double negation puts `assumes`
    back into POSITIVE polarity! -/
def nestedImpPositiveAssumesFormula : PropFormula :=
  .imp
    (.imp (.assumes "impl") (.atom "outputEq"))
    (.not (.atom "impl.assertionFailed"))

/-- Bridge theorem: `correctEquivFormula` evaluates identically to `CorrectEquivObligation`. -/
theorem evalEquivFormula_correct_iff {Val : Type} (specRes implRes : EvalRes Val) :
    evalEquivFormula specRes implRes correctEquivFormula ↔
      CorrectEquivObligation specRes implRes := by
  unfold correctEquivFormula evalEquivFormula CorrectEquivObligation
  constructor
  · intro h ⟨hS, hI, hNotF⟩
    have hSpecNe : ¬ (specRes.assertionFailed = true) := by simp [hNotF]
    obtain ⟨hImplNe, hOut⟩ := h ⟨⟨hS, hI⟩, hSpecNe⟩
    refine ⟨?_, hOut⟩
    cases hF : implRes.assertionFailed with
    | false => rfl
    | true => exact absurd hF hImplNe
  · intro h ⟨⟨hS, hI⟩, hSpecNe⟩
    have hNotF : specRes.assertionFailed = false := by
      cases hF : specRes.assertionFailed with
      | false => rfl
      | true => exact absurd hF hSpecNe
    obtain ⟨hImplF, hOut⟩ := h ⟨hS, hI, hNotF⟩
    exact ⟨by simp [evalEquivFormula, hImplF], hOut⟩

/-- Polarity checker accepts `correctEquivFormula` and rejects all positive-polarity bugs
    (flipped consequent, positive disjunct, double negation, nested implication, `iff`,
    and conditional `if assumes then ... else ...` even inside an antecedent!). -/
theorem checkAssumesNegativePolarity_vectors :
    checkAssumesNegativePolarity correctEquivFormula = true ∧
    checkAssumesNegativePolarity flippedConsequentFormula = false ∧
    checkAssumesNegativePolarity positiveDisjunctFormula = false ∧
    checkAssumesNegativePolarity nestedImpPositiveAssumesFormula = false ∧
    checkAssumesNegativePolarity (.not (.not (.assumes "impl"))) = false ∧
    checkAssumesNegativePolarity (.iff (.atom "outputEq") (.assumes "impl")) = false ∧
    checkAssumesNegativePolarity
      (.imp (.ifte (.assumes "impl") (.atom "outputEq") (.not (.atom "impl.assertionFailed")))
        (.atom "outputEq")) = false := by
  decide

/-- **Biconditional & Conditional Polarity Collapse (A1)**: both `outputEq ↔ implAssumes`
    and `if implAssumes then outputEq else ¬implFailed` accept a broken implementation that
    crashes with `assertionFailed = true` while `output = spec.output`, refuting
    `CorrectEquivObligation`! -/
theorem iffAndIftePolarity_accept_broken_impl :
    let specRes : EvalRes Nat := { assumesHold := true, assertionFailed := false, output := 42 }
    let implRes : EvalRes Nat := { assumesHold := true, assertionFailed := true, output := 42 }
    evalEquivFormula specRes implRes (.iff (.atom "outputEq") (.assumes "impl")) ∧
      evalEquivFormula specRes implRes
        (.ifte (.assumes "impl") (.atom "outputEq") (.not (.atom "impl.assertionFailed"))) ∧
      ¬ CorrectEquivObligation specRes implRes := by
  refine ⟨⟨fun _ => rfl, fun _ => rfl⟩, ⟨fun _ => rfl, fun hNot => absurd rfl hNot⟩, ?_⟩
  intro h
  have hBad := (h ⟨rfl, rfl, rfl⟩).1
  cases hBad

/-- **Soundness Collapse 6a (Polarity Flip)**: both `flippedConsequentFormula` and
    `positiveDisjunctFormula` vacuously accept a broken implementation that fails
    an assertion and returns wrong output `99 ≠ 42`, refuting `CorrectEquivObligation`! -/
theorem polarityFlip_accepts_broken_impl :
    let specRes : EvalRes Nat := { assumesHold := true, assertionFailed := false, output := 42 }
    let implRes : EvalRes Nat := { assumesHold := true, assertionFailed := true, output := 99 }
    evalEquivFormula specRes implRes flippedConsequentFormula ∧
      evalEquivFormula specRes implRes positiveDisjunctFormula ∧
      ¬ CorrectEquivObligation specRes implRes := by
  refine ⟨?_, ?_, ?_⟩
  · intro _; exact ⟨rfl, rfl⟩
  · intro _; exact Or.inl rfl
  · intro h
    have hBad := (h ⟨rfl, rfl, rfl⟩).1
    cases hBad

/-- Computable combinational counterexample checker (`Verifrag` cl/1029131309 analogue):
    checks `specRes.assumesHold ∧ implRes.assumesHold ∧ ¬specRes.assertionFailed ∧
    (implRes.assertionFailed ∨ implRes.output ≠ specRes.output)`. -/
def checkCombCounterExample {Val : Type} [DecidableEq Val]
    (specRes implRes : EvalRes Val) : Bool :=
  specRes.assumesHold && implRes.assumesHold && (!specRes.assertionFailed) &&
    (implRes.assertionFailed || (implRes.output != specRes.output))

/-- **Constructive Counterexample Soundness & Completeness (`checkCombCounterExample_sound`)**:
    `checkCombCounterExample specRes implRes = true` if and only if
    `¬ CorrectEquivObligation specRes implRes`. -/
theorem checkCombCounterExample_sound {Val : Type} [DecidableEq Val]
    (specRes implRes : EvalRes Val) :
    checkCombCounterExample specRes implRes = true ↔
      ¬ CorrectEquivObligation specRes implRes := by
  unfold checkCombCounterExample CorrectEquivObligation
  cases hSA : specRes.assumesHold <;>
  cases hIA : implRes.assumesHold <;>
  cases hSF : specRes.assertionFailed <;>
  cases hIF : implRes.assertionFailed <;>
  by_cases hOut : implRes.output = specRes.output <;>
  simp [hOut]

/-- Lifting `checkCombCounterExample_sound` to refute universal equivalence over an
    input domain `Input` from a single constructive counterexample witness `cex`. -/
theorem checkCombCounterExample_refutes_equiv {Input Val : Type} [DecidableEq Val]
    (specFn implFn : Input → EvalRes Val) (cex : Input)
    (hCex : checkCombCounterExample (specFn cex) (implFn cex) = true) :
    ¬ (∀ i, CorrectEquivObligation (specFn i) (implFn i)) := by
  intro hAll
  exact (checkCombCounterExample_sound (specFn cex) (implFn cex)).mp hCex (hAll cex)

/-! #### 4.4.1b Semantic Soundness of the Polarity Check (B2)

`checkAssumesNegativePolarity` was previously justified only by test vectors. The theorem
below gives its semantic meaning: if every `assumes` atom is in negative polarity, the
obligation is ANTITONE in the assumption valuation, so it is hardest exactly when all
assumptions hold. An implementation therefore can never discharge it by *making* its
assumptions hold (the `Verifrag` positive-polarity bug). -/

/-- Valuation semantics: `va` interprets obligation atoms, `vs` interprets assumptions. -/
def evalPF (va vs : String → Prop) : PropFormula → Prop
  | .atom t => va t
  | .assumes t => vs t
  | .not p => ¬ evalPF va vs p
  | .and p q => evalPF va vs p ∧ evalPF va vs q
  | .or p q => evalPF va vs p ∨ evalPF va vs q
  | .imp p q => evalPF va vs p → evalPF va vs q
  | .iff p q => (evalPF va vs p ↔ evalPF va vs q)
  | .ifte c t e => (evalPF va vs c → evalPF va vs t) ∧ (¬ evalPF va vs c → evalPF va vs e)

/-- Polarity monotonicity: positive-root formulas are antitone and negative-root formulas
    are monotone in the assumption valuation. -/
theorem assumesOnlyNegative_monotone (va : String → Prop) {vs₁ vs₂ : String → Prop}
    (hle : ∀ t, vs₁ t → vs₂ t) :
    ∀ (f : PropFormula) (pol : Polarity), assumesOnlyNegative pol f = true →
      (pol = .pos → evalPF va vs₂ f → evalPF va vs₁ f) ∧
      (pol = .neg → evalPF va vs₁ f → evalPF va vs₂ f) := by
  intro f
  induction f with
  | atom t => intro pol _; exact ⟨fun _ h => h, fun _ h => h⟩
  | assumes t =>
    intro pol h
    cases pol with
    | pos => simp [assumesOnlyNegative] at h
    | neg => exact ⟨(fun hp => nomatch hp), fun _ h₁ => hle t h₁⟩
  | not p ih =>
    intro pol h
    cases pol with
    | pos =>
      have hp := (ih .neg (by simpa [assumesOnlyNegative, Polarity.flip] using h)).2 rfl
      exact ⟨fun _ hn h₁ => hn (hp h₁), (fun hc => nomatch hc)⟩
    | neg =>
      have hp := (ih .pos (by simpa [assumesOnlyNegative, Polarity.flip] using h)).1 rfl
      exact ⟨(fun hc => nomatch hc), fun _ hn h₂ => hn (hp h₂)⟩
  | and p q ihp ihq =>
    intro pol h
    simp only [assumesOnlyNegative, Bool.and_eq_true] at h
    have hp := ihp pol h.1
    have hq := ihq pol h.2
    exact ⟨fun e ⟨a, b⟩ => ⟨hp.1 e a, hq.1 e b⟩, fun e ⟨a, b⟩ => ⟨hp.2 e a, hq.2 e b⟩⟩
  | or p q ihp ihq =>
    intro pol h
    simp only [assumesOnlyNegative, Bool.and_eq_true] at h
    have hp := ihp pol h.1
    have hq := ihq pol h.2
    exact ⟨fun e hor => hor.elim (fun a => Or.inl (hp.1 e a)) (fun b => Or.inr (hq.1 e b)),
      fun e hor => hor.elim (fun a => Or.inl (hp.2 e a)) (fun b => Or.inr (hq.2 e b))⟩
  | imp p q ihp ihq =>
    intro pol h
    cases pol with
    | pos =>
      simp only [assumesOnlyNegative, Polarity.flip, Bool.and_eq_true] at h
      have hp := (ihp .neg h.1).2 rfl
      have hq := (ihq .pos h.2).1 rfl
      exact ⟨fun _ himp a => hq (himp (hp a)), (fun hc => nomatch hc)⟩
    | neg =>
      simp only [assumesOnlyNegative, Polarity.flip, Bool.and_eq_true] at h
      have hp := (ihp .pos h.1).1 rfl
      have hq := (ihq .neg h.2).2 rfl
      exact ⟨(fun hc => nomatch hc), fun _ himp a => hq (himp (hp a))⟩
  | iff p q ihp ihq =>
    intro pol h
    simp only [assumesOnlyNegative, Bool.and_eq_true] at h
    have hp₁ := (ihp .pos h.1.1.1).1 rfl
    have hp₂ := (ihp .neg h.1.1.2).2 rfl
    have hq₁ := (ihq .pos h.1.2).1 rfl
    have hq₂ := (ihq .neg h.2).2 rfl
    have hP : evalPF va vs₁ p ↔ evalPF va vs₂ p := ⟨hp₂, hp₁⟩
    have hQ : evalPF va vs₁ q ↔ evalPF va vs₂ q := ⟨hq₂, hq₁⟩
    exact ⟨fun _ hi => hP.trans (hi.trans hQ.symm), fun _ hi => hP.symm.trans (hi.trans hQ)⟩
  | ifte c t e ihc iht ihe =>
    intro pol h
    simp only [assumesOnlyNegative, Bool.and_eq_true] at h
    have hc₁ := (ihc .pos h.1.1.1).1 rfl
    have hc₂ := (ihc .neg h.1.1.2).2 rfl
    have ht := iht pol h.1.2
    have he := ihe pol h.2
    exact ⟨fun hpol ⟨h1, h2⟩ =>
        ⟨fun c₁ => ht.1 hpol (h1 (hc₂ c₁)), fun nc₁ => he.1 hpol (h2 (fun c₂ => nc₁ (hc₁ c₂)))⟩,
      fun hpol ⟨h1, h2⟩ =>
        ⟨fun c₂ => ht.2 hpol (h1 (hc₁ c₂)), fun nc₂ => he.2 hpol (h2 (fun c₁ => nc₂ (hc₂ c₁)))⟩⟩

/-- **Guard 6a Semantic Soundness**: if `checkAssumesNegativePolarity f = true`, then
    proving `f` under all-assumptions-hold proves `f` under EVERY assumption valuation —
    the obligation can never become easier by establishing assumptions. -/
theorem checkAssumesNegativePolarity_sound (va : String → Prop) {f : PropFormula}
    (h : checkAssumesNegativePolarity f = true)
    (hAll : evalPF va (fun _ => True) f) :
    ∀ vs, evalPF va vs f :=
  fun _ => (assumesOnlyNegative_monotone va (fun _ _ => trivial) f .pos h).1 rfl hAll

/-- **Guard 6a Semantic Collapse**: the flipped-consequent formula holds when every
    assumption holds, yet fails when assumptions fail: positive polarity lets
    "establishing the assumptions" discharge the obligation. -/
theorem flippedConsequent_violates_antitonicity :
    let va : String → Prop := fun t => t = "outputEq"
    evalPF va (fun _ => True) flippedConsequentFormula ∧
      ¬ evalPF va (fun _ => False) flippedConsequentFormula := by
  refine ⟨fun _ => ⟨trivial, trivial⟩, ?_⟩
  intro h
  have hAnt : ¬ ("impl.assertionFailed" = "outputEq") ∧ ("outputEq" = "outputEq") :=
    ⟨by decide, rfl⟩
  exact (h hAnt).1

/-- **Boolean-Negated Assumption Antecedent Collapse (A2)**: writing `(impl.assumesHold = false) → outputEq`
    (i.e. `(¬ assumes) → outputEq`) places `assumes` in POSITIVE polarity: `checkAssumesNegativePolarity`
    rejects it, and semantically it holds vacuously when `assumes` is `True` even if `outputEq` is `False`! -/
theorem boolNegAssumes_antecedent_violates_antitonicity :
    let f : PropFormula := .imp (.not (.assumes "impl")) (.atom "outputEq")
    let va : String → Prop := fun _ => False
    checkAssumesNegativePolarity f = false ∧
      evalPF va (fun _ => True) f ∧
      ¬ evalPF va (fun _ => False) f := by
  refine ⟨by decide, fun hNot => absurd trivial hNot, ?_⟩
  intro h
  exact h (fun hFalse => hFalse)

/-! #### 4.4.2 Part 6b: Invariant-Struct `private mk ::` Sealing (`Samite` cl/1029680381) -/

/-- Unsealed capability structure (public default `mk` allows forging arbitrary invalid values). -/
structure UnsealedCap : Type where
  val : Nat
  deriving DecidableEq, Repr

/-- Sealed invariant-bearing capability structure using Lean 4's `private mk ::` constructor
    so external callers can only construct values via the checked smart constructor. -/
-- @sealed_invariant
structure SealedCap : Type where
  private mk ::
  val : Nat
  inv : 0 < val
  deriving DecidableEq

/-- Smart constructor for `SealedCap` enforcing `0 < val`. -/
def SealedCap.mkChecked (n : Nat) : Option SealedCap :=
  if h : 0 < n then some (SealedCap.mk n h) else none

/-- **Soundness Collapse 6b (Unsealed Struct)**: without sealing, any caller can invoke
    `UnsealedCap.mk 0` directly and violate the intended positivity invariant `0 < c.val`. -/
theorem unsealedCap_allows_forged_invariant_violation :
    ∃ c : UnsealedCap, ¬ (0 < c.val) :=
  ⟨UnsealedCap.mk 0, by decide⟩

/-- Every `SealedCap` constructed via `SealedCap.mkChecked` carries exact `c.val = n`
    and genuinely satisfies `0 < c.val`. -/
theorem sealedCap_mkChecked_preserves_invariant {n : Nat} {c : SealedCap}
    (h : SealedCap.mkChecked n = some c) : c.val = n ∧ 0 < c.val := by
  unfold SealedCap.mkChecked at h
  by_cases hPos : 0 < n
  · simp only [hPos, ↓reduceDIte, Option.some.injEq] at h
    subst h
    exact ⟨rfl, hPos⟩
  · simp only [hPos, ↓reduceDIte] at h
    cases h

/-- Parsed summary of a Lean `structure` declaration for Samite sealing checks. -/
structure StructSealingDescriptor : Type where
  name : String
  isInvariantBearing : Bool
  hasPrivateMkCtor : Bool
  hasPrivateMkField : Bool := false
  hasSealedSibling : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Guard 6b (`Samite` cl/1029680381): strictly scoped per target structure so neither
    a decoy field `private mk : Nat` nor a sealed sibling structure can mask an unsealed
    invariant-bearing struct. -/
def checkInvariantStructSealing (decls : List StructSealingDescriptor) : Bool :=
  decls.all fun d => (!d.isInvariantBearing) || d.hasPrivateMkCtor

def InvariantStructSealingGuard (decls : List StructSealingDescriptor) : Prop :=
  checkInvariantStructSealing decls = true

/-- Decoy field `private mk : Nat` does NOT satisfy `InvariantStructSealingGuard`. -/
theorem decoyPrivateMkField_rejected_by_sealingGuard :
    ¬ InvariantStructSealingGuard
      [{ name := "UnsealedWithField", isInvariantBearing := true,
         hasPrivateMkCtor := false, hasPrivateMkField := true, hasSealedSibling := false }] := by
  unfold InvariantStructSealingGuard checkInvariantStructSealing
  decide

/-- A sealed sibling structure in the same file does NOT mask an unsealed target struct. -/
theorem sealedSibling_does_not_mask_unsealed_target :
    ¬ InvariantStructSealingGuard
      [{ name := "SealedSibling", isInvariantBearing := true,
         hasPrivateMkCtor := true, hasSealedSibling := true },
       { name := "UnsealedTarget", isInvariantBearing := true,
         hasPrivateMkCtor := false, hasSealedSibling := true }] := by
  unfold InvariantStructSealingGuard checkInvariantStructSealing
  decide

/-- **Guard 6b Soundness Restoration**: `InvariantStructSealingGuard decls` guarantees
    that EVERY invariant-bearing structure in `decls` has `hasPrivateMkCtor = true`. -/
theorem invariantStructSealingGuard_sound {decls : List StructSealingDescriptor}
    (hGuard : InvariantStructSealingGuard decls) :
    ∀ d ∈ decls, d.isInvariantBearing = true → d.hasPrivateMkCtor = true := by
  unfold InvariantStructSealingGuard checkInvariantStructSealing at hGuard
  rw [List.all_eq_true] at hGuard
  intro d hd hInv
  have hD := hGuard d hd
  simp only [hInv, Bool.not_true, Bool.false_or] at hD
  exact hD

/-! #### 4.4.2b Operational Module-Boundary Sealing Model (A2)

Closing B2's open issue: `private mk ::` alone is insufficient if the same file either
attaches `deriving Inhabited` (synthesizing a public `default` constructor) OR exports a
public unchecked wrapper `def V.mk' (v : Nat) : V := ⟨v⟩`. The operational model below
evaluates arbitrary external client terms against a `StructModule` and proves by structural
induction that `ModuleSealingGuard` preserves the struct invariant on EVERY client-producible
value. -/

/-- Classification of a same-file public export that can construct a sealed struct. -/
inductive PublicExportKind : Type where
  /-- Smart constructor checking a boolean guard `g` before invoking private `mk`. -/
  | checkedCtor (guard : Nat → Bool)
  /-- Unchecked public wrapper (e.g., `def V.mk' (v : Nat) : V := ⟨v⟩`). -/
  | uncheckedLeak
  /-- Public `Inhabited` / `OfNat` constant instance yielding a fixed payload `d`. -/
  | defaultInstance (defaultVal : Nat)

/-- Module-boundary specification for an invariant-bearing Lean `structure`. -/
structure StructModule : Type where
  ctorPrivate : Bool
  derivesInhabited : Bool
  inv : Nat → Bool
  exports : List PublicExportKind

/-- External client expression language over a `StructModule`. -/
inductive ClientExpr : Type where
  /-- Direct constructor invocation `S.mk n` (succeeds iff constructor is public). -/
  | directMk (n : Nat)
  /-- Derived `default` invocation (succeeds iff `deriving Inhabited` was emitted). -/
  | callDefault
  /-- Invocation of same-file public export `#idx` with payload `arg`. -/
  | callExport (idx : Nat) (arg : Nat)
  /-- Client-side branching between two struct-producing expressions. -/
  | choose (cond : Bool) (lhs rhs : ClientExpr)
  deriving DecidableEq, Repr, Inhabited

/-- Operational semantics: evaluates a client expression against module `m`, returning
    `some v` if the module boundary permits producing a struct carrying payload `v`. -/
def ClientExpr.eval (m : StructModule) : ClientExpr → Option Nat
  | .directMk n => if !m.ctorPrivate then some n else none
  | .callDefault => if m.derivesInhabited then some 0 else none
  | .callExport idx arg =>
    match m.exports[idx]? with
    | some (.checkedCtor g) => if g arg then some arg else none
    | some .uncheckedLeak => some arg
    | some (.defaultInstance d) => some d
    | none => none
  | .choose cond lhs rhs => if cond then lhs.eval m else rhs.eval m

/-- Soundness obligation for a same-file public constructor export. -/
def ExportPreservesInv (inv : Nat → Bool) : PublicExportKind → Prop
  | .checkedCtor g => ∀ n, g n = true → inv n = true
  | .uncheckedLeak => False
  | .defaultInstance d => inv d = true

/-- **Module-Boundary Sealing Guard (A2)**: requires `private mk ::`, forbids `deriving Inhabited`,
    and requires every same-file public export to establish the struct invariant `m.inv`. -/
def ModuleSealingGuard (m : StructModule) : Prop :=
  m.ctorPrivate = true ∧
    m.derivesInhabited = false ∧
    ∀ ex ∈ m.exports, ExportPreservesInv m.inv ex

/-- **Operational Leak Collapse (A2)**: even when `private mk ::` is enabled (`ctorPrivate = true`),
    EITHER `deriving Inhabited` OR a same-file public wrapper `def V.mk' v := ⟨v⟩` allows an
    external client to construct `v = 0` violating `0 < v`, and BOTH are rejected by
    `ModuleSealingGuard`! -/
theorem publicLeakOrDerivingInhabited_forges_invalid_value :
    let posInv : Nat → Bool := fun n => decide (0 < n)
    let modWithDeriving : StructModule :=
      { ctorPrivate := true, derivesInhabited := true, inv := posInv, exports := [] }
    let modWithLeak : StructModule :=
      { ctorPrivate := true, derivesInhabited := false, inv := posInv,
        exports := [.uncheckedLeak] }
    ClientExpr.callDefault.eval modWithDeriving = some 0 ∧
      posInv 0 = false ∧
      ¬ ModuleSealingGuard modWithDeriving ∧
      (ClientExpr.callExport 0 0).eval modWithLeak = some 0 ∧
      ¬ ModuleSealingGuard modWithLeak := by
  refine ⟨rfl, rfl, ?_, rfl, ?_⟩
  · intro h
    cases h.2.1
  · intro h
    exact h.2.2 .uncheckedLeak (by simp)

/-- **Operational Guard 6b Soundness (A2)**: under `ModuleSealingGuard m`, EVERY value
    constructible by ANY external `ClientExpr` genuinely satisfies `m.inv v = true`! -/
theorem moduleSealingGuard_preserves_client_invariant {m : StructModule}
    (hGuard : ModuleSealingGuard m) :
    ∀ (e : ClientExpr) {v : Nat}, e.eval m = some v → m.inv v = true := by
  intro e
  induction e with
  | directMk n =>
    intro v hEval
    simp only [ClientExpr.eval, hGuard.1, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hEval
    cases hEval
  | callDefault =>
    intro v hEval
    simp only [ClientExpr.eval, hGuard.2.1, Bool.false_eq_true, ↓reduceIte] at hEval
    cases hEval
  | callExport idx arg =>
    intro v hEval
    simp only [ClientExpr.eval] at hEval
    cases hGet : m.exports[idx]? with
    | none =>
      rw [hGet] at hEval
      cases hEval
    | some ex =>
      rw [hGet] at hEval
      have hMem : ex ∈ m.exports := List.mem_of_getElem? hGet
      have hEx := hGuard.2.2 ex hMem
      cases ex with
      | checkedCtor g =>
        by_cases hg : g arg = true
        · simp only [hg, ↓reduceIte, Option.some.injEq] at hEval
          subst hEval
          exact hEx arg hg
        · simp only [hg] at hEval
          cases hEval
      | uncheckedLeak =>
        exact False.elim hEx
      | defaultInstance d =>
        simp only [Option.some.injEq] at hEval
        subst hEval
        exact hEx
  | choose cond lhs rhs ihL ihR =>
    intro v hEval
    cases cond with
    | true => exact ihL (by simpa [ClientExpr.eval] using hEval)
    | false => exact ihR (by simpa [ClientExpr.eval] using hEval)

/-- Combined Guard 6 (`Verifrag` cl/1029131309 + `Samite` cl/1029680381). -/
def AssumptionPolarityAndStructSealingGuard
    (f : PropFormula) (decls : List StructSealingDescriptor) : Prop :=
  checkAssumesNegativePolarity f = true ∧ InvariantStructSealingGuard decls

theorem assumptionPolarityAndStructSealingGuard_sound
    {f : PropFormula} {decls : List StructSealingDescriptor}
    (hG : AssumptionPolarityAndStructSealingGuard f decls) :
    checkAssumesNegativePolarity f = true ∧
      (∀ d ∈ decls, d.isInvariantBearing = true → d.hasPrivateMkCtor = true) :=
  ⟨hG.1, invariantStructSealingGuard_sound hG.2⟩

end Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto
