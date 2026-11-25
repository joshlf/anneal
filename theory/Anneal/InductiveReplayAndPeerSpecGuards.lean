-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.SpecBoundaryGuards

/-!
# Inductive-Metadata Replay, Sharded Audit Reconciliation, and Peer Spec Guards

This module is a pure, kernel-checked model of three trusted-boundary hardening
pillars. Every definition is a safe kernel definition and every theorem depends only
on `propext`, `Classical.choice`, and `Quot.sound`.

1. **Pillar 1 — inductive-metadata replay** (`lean4#16717`). Kernel replay of an
   imported module re-checks constructors and recursors, but on the pinned toolchain
   it never re-checks stored `.inductInfo` metadata, and it erases every member of
   `info.all` from its work list without checking `info.name ∈ info.all`. A binary
   `.olean` forgery can therefore smuggle inductive metadata the kernel never saw.
   `selfComparison_tautological` proves that comparing stored entries against the
   environment built from those same entries accepts every module with distinct
   names, whatever its metadata. `InductiveReplayWellFormed` combines pre-replay
   structural invariants with post-replay agreement against the kernel-generated
   environment; `inductiveReplayWellFormed_rejects` proves it rejects every
   `ForgedInductiveClass`, with the exact diagnostic code.
2. **Pillar 2 — sharded audit reconciliation** (`grmf`). A module partition audited
   shard by shard agrees with the monolithic audit exactly when the partition is
   orphan-free, every shard environment is closed under its references, and
   cross-shard duplicate constants are reconciled by the exact structural
   `strictConstCompat` (`shardAxiomUnion_sound`). A 64-bit expression fingerprint
   collides on literals differing by `2 ^ 64` (`exprHash64_collision`), and a naive
   `value? = none` comparison conflates `.axiomInfo` with `.defnInfo`
   (`naiveCompat_conflates_axiom_defn`); the latter provably breaks axiom-union
   parity (`naiveReconciliation_breaks_axiom_union`).
3. **Pillar 3 — four peer-verifier spec-boundary guards**, frozen as
   `PeerSpecGuardClass` ranks `3..6` extending `SpecBoundaryGuardClass` ranks
   `0..2`, each with a soundness-collapse counterexample and a restoration theorem:
   unsatisfiable extern `ensures` (`creusot#2388`), `FnDef` ghost-token coercion
   (`creusot#2389`), external-type `Drop` omission (`verus#3514`), and assumption
   polarity plus structure sealing (`Verifrag`, `Samite`).
-/

namespace Anneal.InductiveReplayAndPeerSpecGuards

open Anneal.SpecRealizability (VacuityClass)
open Anneal.SpecBoundaryGuards (SpecBoundaryGuardClass)

/-! ## 1. Frozen `PeerSpecGuardClass` Taxonomy (Ranks `3..6`) -/

/-- The four peer-verifier specification-boundary guards, in rank order `3..6`,
    mirroring `anneal_spec::peer_soundness_guards::PeerSpecGuardClass`. They extend,
    and never duplicate, `SpecBoundaryGuardClass` (ranks `0..2`). -/
inductive PeerSpecGuardClass : Type where
  /-- `creusot#2388`: an assumed contract with an unsatisfiable `ensures` on a
      function that can return. -/
  | unsatisfiableExternEnsures
  /-- `creusot#2389`: a ghost-token constructor coerced to a first-class `FnDef`
      value or minted from a repeating context. -/
  | fnDefGhostTokenCoercion
  /-- `verus#3514`: an external type specification omits an active `Drop` effect. -/
  | externalTypeDropOmission
  /-- `Verifrag` + `Samite`: an assumption atom in non-antecedent polarity, or an
      invariant-bearing structure with an unsealed constructor. -/
  | assumptionPolarityAndStructSealing
  deriving DecidableEq, Repr, Inhabited

namespace PeerSpecGuardClass

/-- Number of peer guards (`PeerSpecGuardClass::COUNT`). -/
def count : Nat := 4

/-- Canonical `snake_case` wire identifier (`guard_id`). -/
def guardId : PeerSpecGuardClass → String
  | .unsatisfiableExternEnsures => "unsatisfiable_extern_ensures"
  | .fnDefGhostTokenCoercion => "fndef_ghost_token_coercion"
  | .externalTypeDropOmission => "external_type_drop_omission"
  | .assumptionPolarityAndStructSealing => "assumption_polarity_and_struct_sealing"

/-- Canonical diagnostic name (`canonical_name`). -/
def canonicalName : PeerSpecGuardClass → String
  | .unsatisfiableExternEnsures => "UnsatisfiableExternEnsures"
  | .fnDefGhostTokenCoercion => "FnDefGhostTokenCoercion"
  | .externalTypeDropOmission => "ExternalTypeDropOmission"
  | .assumptionPolarityAndStructSealing => "AssumptionPolarityAndStructSealing"

/-- The frozen vacuity class a violation is reported under (`to_vacuity_class`). -/
def toVacuityClass : PeerSpecGuardClass → VacuityClass
  | .unsatisfiableExternEnsures => .deadPrecondition
  | .fnDefGhostTokenCoercion => .specViolation
  | .externalTypeDropOmission => .specViolation
  | .assumptionPolarityAndStructSealing => .survivedAllMutants

/-- Canonical rank, continuing `SpecBoundaryGuardClass.rank` (`3..6`). -/
def rank : PeerSpecGuardClass → Nat
  | .unsatisfiableExternEnsures => 3
  | .fnDefGhostTokenCoercion => 4
  | .externalTypeDropOmission => 5
  | .assumptionPolarityAndStructSealing => 6

/-- Inverse of `rank`; `none` outside `3..6`. -/
def ofRank? : Nat → Option PeerSpecGuardClass
  | 3 => some .unsatisfiableExternEnsures
  | 4 => some .fnDefGhostTokenCoercion
  | 5 => some .externalTypeDropOmission
  | 6 => some .assumptionPolarityAndStructSealing
  | _ => none

/-- All four peer guards in rank order (`PeerSpecGuardClass::ALL`). -/
def all : List PeerSpecGuardClass :=
  [.unsatisfiableExternEnsures, .fnDefGhostTokenCoercion, .externalTypeDropOmission,
    .assumptionPolarityAndStructSealing]

/-- Parse a wire identifier; exact and case-sensitive. -/
def ofGuardId? (s : String) : Option PeerSpecGuardClass :=
  all.find? (fun g => g.guardId == s)

/-- Parse a canonical diagnostic name; exact and case-sensitive. -/
def ofCanonicalName? (s : String) : Option PeerSpecGuardClass :=
  all.find? (fun g => g.canonicalName == s)

theorem all_length : all.length = count := rfl

theorem mem_all (g : PeerSpecGuardClass) : g ∈ all := by
  cases g <;> decide

theorem all_nodup : all.Nodup := by decide

theorem all_map_rank : all.map rank = [3, 4, 5, 6] := rfl

theorem ofRank?_rank (g : PeerSpecGuardClass) : ofRank? g.rank = some g := by
  cases g <;> rfl

theorem rank_of_ofRank? {n : Nat} {g : PeerSpecGuardClass} (h : ofRank? n = some g) :
    g.rank = n := by
  match n, h with
  | 3, h => cases h; rfl
  | 4, h => cases h; rfl
  | 5, h => cases h; rfl
  | 6, h => cases h; rfl
  | n + 7, h => cases h

theorem ofRank?_eq_some_iff {n : Nat} {g : PeerSpecGuardClass} :
    ofRank? n = some g ↔ g.rank = n :=
  ⟨rank_of_ofRank?, fun h => h ▸ ofRank?_rank g⟩

theorem rank_injective {a b : PeerSpecGuardClass} (h : a.rank = b.rank) : a = b := by
  have hParse : ofRank? a.rank = ofRank? b.rank := congrArg ofRank? h
  rw [ofRank?_rank, ofRank?_rank] at hParse
  exact Option.some.inj hParse

theorem rank_bounds (g : PeerSpecGuardClass) : 3 ≤ g.rank ∧ g.rank < 3 + count := by
  cases g <;> decide

theorem ofRank?_isSome_iff (n : Nat) : (ofRank? n).isSome = true ↔ 3 ≤ n ∧ n < 3 + count := by
  match n with
  | 0 | 1 | 2 => decide
  | 3 | 4 | 5 | 6 => decide
  | n + 7 => simp [ofRank?, count]

theorem ofGuardId?_guardId (g : PeerSpecGuardClass) : ofGuardId? g.guardId = some g := by
  cases g <;> rfl

theorem ofCanonicalName?_canonicalName (g : PeerSpecGuardClass) :
    ofCanonicalName? g.canonicalName = some g := by
  cases g <;> rfl

theorem guardId_injective {a b : PeerSpecGuardClass} (h : a.guardId = b.guardId) : a = b := by
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

/-- No peer wire identifier coincides with a base `SpecBoundaryGuardClass` identifier. -/
theorem guardId_ne_base (p : PeerSpecGuardClass) (b : SpecBoundaryGuardClass) :
    p.guardId ≠ b.guardId := by
  cases p <;> cases b <;> decide

/-- No peer diagnostic name coincides with a base diagnostic name. -/
theorem canonicalName_ne_base (p : PeerSpecGuardClass) (b : SpecBoundaryGuardClass) :
    p.canonicalName ≠ b.canonicalName := by
  cases p <;> cases b <;> decide

/-- Peer ranks never collide with base ranks. -/
theorem rank_ne_base (p : PeerSpecGuardClass) (b : SpecBoundaryGuardClass) :
    p.rank ≠ b.rank := by
  cases p <;> cases b <;> decide

/-- Wire identifiers and diagnostic names are disjoint namespaces. -/
theorem guardId_ne_canonicalName (a b : PeerSpecGuardClass) :
    a.guardId ≠ b.canonicalName := by
  cases a <;> cases b <;> decide

/-- The frozen `(rank, guard_id, canonical_name, vacuity_class)` wire table. -/
theorem wire_table :
    all.map (fun g => (g.rank, g.guardId, g.canonicalName, g.toVacuityClass.canonicalName)) =
      [(3, "unsatisfiable_extern_ensures", "UnsatisfiableExternEnsures", "DeadPrecondition"),
        (4, "fndef_ghost_token_coercion", "FnDefGhostTokenCoercion", "SpecViolation"),
        (5, "external_type_drop_omission", "ExternalTypeDropOmission", "SpecViolation"),
        (6, "assumption_polarity_and_struct_sealing", "AssumptionPolarityAndStructSealing",
          "SurvivedAllMutants")] :=
  rfl

end PeerSpecGuardClass

/-- The combined seven-guard taxonomy: base ranks `0..2` followed by peer ranks `3..6`
    (`anneal_spec::peer_soundness_guards::CombinedSpecGuardClass`). -/
inductive CombinedSpecGuardClass : Type where
  | base (g : SpecBoundaryGuardClass)
  | peer (g : PeerSpecGuardClass)
  deriving DecidableEq, Repr

namespace CombinedSpecGuardClass

/-- Number of combined guards. -/
def count : Nat := 7

def rank : CombinedSpecGuardClass → Nat
  | .base g => g.rank
  | .peer g => g.rank

def guardId : CombinedSpecGuardClass → String
  | .base g => g.guardId
  | .peer g => g.guardId

def canonicalName : CombinedSpecGuardClass → String
  | .base g => g.canonicalName
  | .peer g => g.canonicalName

def toVacuityClass : CombinedSpecGuardClass → VacuityClass
  | .base g => g.toVacuityClass
  | .peer g => g.toVacuityClass

/-- Inverse of `rank`: base ranks first, then peer ranks; `none` for `n ≥ 7`. -/
def ofRank? (n : Nat) : Option CombinedSpecGuardClass :=
  match SpecBoundaryGuardClass.ofRank? n with
  | some g => some (.base g)
  | none => (PeerSpecGuardClass.ofRank? n).map .peer

def all : List CombinedSpecGuardClass :=
  SpecBoundaryGuardClass.all.map .base ++ PeerSpecGuardClass.all.map .peer

def ofGuardId? (s : String) : Option CombinedSpecGuardClass :=
  all.find? (fun g => g.guardId == s)

theorem all_length : all.length = count := rfl

theorem all_map_rank : all.map rank = List.range count := by decide

theorem all_nodup : all.Nodup := by decide

theorem mem_all (c : CombinedSpecGuardClass) : c ∈ all := by
  cases c with
  | base g => cases g <;> decide
  | peer g => cases g <;> decide

theorem ofRank?_rank (c : CombinedSpecGuardClass) : ofRank? c.rank = some c := by
  cases c with
  | base g => cases g <;> rfl
  | peer g => cases g <;> rfl

theorem rank_lt_count (c : CombinedSpecGuardClass) : c.rank < count := by
  cases c with
  | base g => cases g <;> decide
  | peer g => cases g <;> decide

theorem rank_injective {a b : CombinedSpecGuardClass} (h : a.rank = b.rank) : a = b := by
  have hParse : ofRank? a.rank = ofRank? b.rank := congrArg ofRank? h
  rw [ofRank?_rank, ofRank?_rank] at hParse
  exact Option.some.inj hParse

theorem rank_of_ofRank? {n : Nat} {c : CombinedSpecGuardClass} (h : ofRank? n = some c) :
    c.rank = n := by
  match n, h with
  | 0, h => cases h; rfl
  | 1, h => cases h; rfl
  | 2, h => cases h; rfl
  | 3, h => cases h; rfl
  | 4, h => cases h; rfl
  | 5, h => cases h; rfl
  | 6, h => cases h; rfl
  | n + 7, h => cases h

/-- `rank` is a bijection from the seven guards onto `0..6`. -/
theorem ofRank?_isSome_iff (n : Nat) : (ofRank? n).isSome = true ↔ n < count := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
    exact rank_of_ofRank? hc ▸ rank_lt_count c
  · intro h
    match n, h with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => rfl

theorem ofGuardId?_guardId (c : CombinedSpecGuardClass) : ofGuardId? c.guardId = some c := by
  cases c with
  | base g => cases g <;> rfl
  | peer g => cases g <;> rfl

theorem guardId_injective {a b : CombinedSpecGuardClass} (h : a.guardId = b.guardId) :
    a = b := by
  have hParse : ofGuardId? a.guardId = ofGuardId? b.guardId := congrArg ofGuardId? h
  rw [ofGuardId?_guardId, ofGuardId?_guardId] at hParse
  exact Option.some.inj hParse

end CombinedSpecGuardClass

/-- A peer-guard verdict (`PeerSpecGuardVerdict`). -/
inductive PeerSpecGuardVerdict : Type where
  | pass (g : PeerSpecGuardClass)
  | violation (g : PeerSpecGuardClass)
  deriving DecidableEq, Repr

namespace PeerSpecGuardVerdict

def guard : PeerSpecGuardVerdict → PeerSpecGuardClass
  | .pass g => g
  | .violation g => g

def isPass : PeerSpecGuardVerdict → Bool
  | .pass _ => true
  | .violation _ => false

/-- The vacuity class a verdict reports; `none` exactly for a passing verdict. -/
def vacuityClass? : PeerSpecGuardVerdict → Option VacuityClass
  | .pass _ => none
  | .violation g => some g.toVacuityClass

/-- Build a verdict from a Boolean guard check. -/
def ofCheck (g : PeerSpecGuardClass) (ok : Bool) : PeerSpecGuardVerdict :=
  if ok then .pass g else .violation g

theorem vacuityClass?_eq_none_iff (v : PeerSpecGuardVerdict) :
    v.vacuityClass? = none ↔ v.isPass = true := by
  cases v <;> simp [vacuityClass?, isPass]

theorem ofCheck_guard (g : PeerSpecGuardClass) (ok : Bool) : (ofCheck g ok).guard = g := by
  cases ok <;> rfl

theorem ofCheck_isPass (g : PeerSpecGuardClass) (ok : Bool) : (ofCheck g ok).isPass = ok := by
  cases ok <;> rfl

theorem ofCheck_false_vacuityClass (g : PeerSpecGuardClass) :
    (ofCheck g false).vacuityClass? = some g.toVacuityClass := rfl

end PeerSpecGuardVerdict

/-! ## 2. Pillar 1 — Inductive-Metadata Replay (`lean4#16717`) -/

/-- Constant names are modeled as natural-number keys. -/
abbrev ConstName := Nat

/-- Kernel expressions, with free and meta variables and a literal form. -/
inductive RExpr : Type where
  | bvar (idx : Nat)
  | fvar (id : Nat)
  | mvar (id : Nat)
  | sort (level : Nat)
  | const (name : ConstName)
  | app (fn arg : RExpr)
  | lam (ty body : RExpr)
  | forallE (ty body : RExpr)
  | natLit (val : Nat)
  deriving DecidableEq, Repr, Inhabited

namespace RExpr

/-- No free or meta variable, and every bound variable is below binder depth `d`. -/
def closedAt : Nat → RExpr → Bool
  | d, .bvar i => decide (i < d)
  | _, .fvar _ => false
  | _, .mvar _ => false
  | _, .sort _ => true
  | _, .const _ => true
  | d, .app f a => closedAt d f && closedAt d a
  | d, .lam t b => closedAt d t && closedAt (d + 1) b
  | d, .forallE t b => closedAt d t && closedAt (d + 1) b
  | _, .natLit _ => true

/-- A stored expression is closed (`¬ hasFVar ∧ ¬ hasMVar ∧ ¬ hasLooseBVars`). -/
def isClosed (e : RExpr) : Bool := closedAt 0 e

/-- Constants referenced by an expression. -/
def consts : RExpr → List ConstName
  | .const n => [n]
  | .app f a => consts f ++ consts a
  | .lam t b => consts t ++ consts b
  | .forallE t b => consts t ++ consts b
  | _ => []

/-- A 64-bit structural fingerprint in the style of `Expr.hash`: literals are reduced
    modulo `2 ^ 64`, so it is not injective. -/
def hash64 : RExpr → Nat
  | .bvar i => (i * 3 + 1) % 2 ^ 64
  | .fvar i => (i * 5 + 2) % 2 ^ 64
  | .mvar i => (i * 7 + 3) % 2 ^ 64
  | .sort l => (l * 11 + 4) % 2 ^ 64
  | .const n => (n * 13 + 5) % 2 ^ 64
  | .app f a => (hash64 f * 17 + hash64 a + 6) % 2 ^ 64
  | .lam t b => (hash64 t * 19 + hash64 b + 7) % 2 ^ 64
  | .forallE t b => (hash64 t * 23 + hash64 b + 8) % 2 ^ 64
  | .natLit v => (v * 31 + 9) % 2 ^ 64

end RExpr

/-- Stored `.inductInfo` metadata. -/
structure InductMeta where
  name : ConstName
  levelParams : Nat
  type : RExpr
  numParams : Nat
  numIndices : Nat
  all : List ConstName
  ctors : List ConstName
  numNested : Nat
  isRec : Bool
  isReflexive : Bool
  isUnsafe : Bool
  deriving DecidableEq, Repr

/-- Stored `.ctorInfo` metadata. -/
structure CtorMeta where
  name : ConstName
  levelParams : Nat
  type : RExpr
  induct : ConstName
  cidx : Nat
  numParams : Nat
  numFields : Nat
  isUnsafe : Bool
  deriving DecidableEq, Repr

/-- A recursor computation rule. -/
structure RecRule where
  ctor : ConstName
  nfields : Nat
  rhs : RExpr
  deriving DecidableEq, Repr

/-- Stored `.recInfo` metadata (covers every `rec`, `rec_1`, ..., `rec_k`). -/
structure RecMeta where
  name : ConstName
  levelParams : Nat
  type : RExpr
  all : List ConstName
  numParams : Nat
  numIndices : Nat
  numMotives : Nat
  numMinors : Nat
  rules : List RecRule
  k : Bool
  isUnsafe : Bool
  deriving DecidableEq, Repr

/-- Stored constant information, one constructor per `ConstantInfo` kind. -/
inductive RConstInfo : Type where
  | axiomInfo (name : ConstName) (levelParams : Nat) (type : RExpr)
  | defnInfo (name : ConstName) (levelParams : Nat) (type value : RExpr)
  | thmInfo (name : ConstName) (levelParams : Nat) (type value : RExpr)
  | opaqueInfo (name : ConstName) (levelParams : Nat) (type value : RExpr)
  | quotInfo (name : ConstName) (levelParams : Nat) (type : RExpr)
  | inductInfo (val : InductMeta)
  | ctorInfo (val : CtorMeta)
  | recInfo (val : RecMeta)
  deriving DecidableEq, Repr

namespace RConstInfo

def name : RConstInfo → ConstName
  | .axiomInfo n _ _ => n
  | .defnInfo n _ _ _ => n
  | .thmInfo n _ _ _ => n
  | .opaqueInfo n _ _ _ => n
  | .quotInfo n _ _ => n
  | .inductInfo v => v.name
  | .ctorInfo v => v.name
  | .recInfo v => v.name

def type : RConstInfo → RExpr
  | .axiomInfo _ _ t => t
  | .defnInfo _ _ t _ => t
  | .thmInfo _ _ t _ => t
  | .opaqueInfo _ _ t _ => t
  | .quotInfo _ _ t => t
  | .inductInfo v => v.type
  | .ctorInfo v => v.type
  | .recInfo v => v.type

/-- `ConstantInfo.value?` with its default `allowOpaque := false`: only definitions and
    theorems expose a value. -/
def value? : RConstInfo → Option RExpr
  | .defnInfo _ _ _ v => some v
  | .thmInfo _ _ _ v => some v
  | _ => none

/-- Every stored expression: type, value, and recursor-rule right-hand sides. -/
def exprs : RConstInfo → List RExpr
  | .axiomInfo _ _ t => [t]
  | .defnInfo _ _ t v => [t, v]
  | .thmInfo _ _ t v => [t, v]
  | .opaqueInfo _ _ t v => [t, v]
  | .quotInfo _ _ t => [t]
  | .inductInfo v => [v.type]
  | .ctorInfo v => [v.type]
  | .recInfo v => v.type :: v.rules.map RecRule.rhs

/-- Every constant a declaration references, including mutual and constructor metadata. -/
def refs : RConstInfo → List ConstName
  | .inductInfo v => v.type.consts ++ v.all ++ v.ctors
  | .ctorInfo v => v.type.consts ++ [v.induct]
  | .recInfo v =>
    (v.type :: v.rules.map RecRule.rhs).flatMap RExpr.consts ++ v.all ++ v.rules.map RecRule.ctor
  | c => c.exprs.flatMap RExpr.consts

def isAxiom : RConstInfo → Bool
  | .axiomInfo .. => true
  | _ => false

/-- Audit roots: theorems (claims). -/
def isClaim : RConstInfo → Bool
  | .thmInfo .. => true
  | _ => false

def isInductFamily : RConstInfo → Bool
  | .inductInfo _ | .ctorInfo _ | .recInfo _ => true
  | _ => false

end RConstInfo

/-- An environment is a list of constants. -/
abbrev Env := List RConstInfo

/-- Name lookup (first match). -/
def lookup (env : Env) (n : ConstName) : Option RConstInfo :=
  env.find? (fun c => c.name == n)

/-- `.olean` module data: the `constNames` table and the stored `constants` array. -/
structure ModuleData where
  constNames : List ConstName
  constants : List RConstInfo
  deriving DecidableEq, Repr

/-- Position of `n` in a list. -/
def posOf (n : ConstName) : List ConstName → Option Nat
  | [] => none
  | m :: ms => if m = n then some 0 else (posOf n ms).map (· + 1)

def isInductIn (env : Env) (n : ConstName) : Bool :=
  match lookup env n with
  | some (.inductInfo _) => true
  | _ => false

def isCtorIn (env : Env) (n : ConstName) : Bool :=
  match lookup env n with
  | some (.ctorInfo _) => true
  | _ => false

/-- Mutual-block members share `all`, parameters, universe parameters and safety. -/
def mutualAgrees (env : Env) (I : InductMeta) (n : ConstName) : Bool :=
  match lookup env n with
  | some (.inductInfo J) =>
    J.all == I.all && J.numParams == I.numParams && J.levelParams == I.levelParams &&
      J.isUnsafe == I.isUnsafe
  | _ => true

def ctorParentAgrees (env : Env) (I : InductMeta) (c : ConstName) : Bool :=
  match lookup env c with
  | some (.ctorInfo C) => C.induct == I.name && C.numParams == I.numParams
  | _ => true

def ctorCidxAgrees (env : Env) (I : InductMeta) (c : ConstName) : Bool :=
  match lookup env c with
  | some (.ctorInfo C) => posOf c I.ctors == some C.cidx
  | _ => true

def ctorListedInParent (env : Env) (C : CtorMeta) : Bool :=
  match lookup env C.induct with
  | some (.inductInfo I) => decide (C.name ∈ I.ctors)
  | _ => false

def recRuleAnchored (env : Env) (all : List ConstName) (r : RecRule) : Bool :=
  match lookup env r.ctor with
  | some (.ctorInfo C) => decide (C.induct ∈ all)
  | _ => false

def recAnchored (env : Env) (R : RecMeta) : Bool :=
  !R.all.isEmpty && decide R.all.Nodup && R.all.all (isInductIn env) &&
    R.rules.all (recRuleAnchored env R.all)

/-- Check `p` on every stored `.inductInfo`. -/
def forallInduct (env : Env) (p : InductMeta → Bool) : Bool :=
  env.all (fun c => match c with
    | .inductInfo I => p I
    | _ => true)

/-- Check `p` on every stored `.ctorInfo`. -/
def forallCtor (env : Env) (p : CtorMeta → Bool) : Bool :=
  env.all (fun c => match c with
    | .ctorInfo C => p C
    | _ => true)

/-- Check `p` on every stored `.recInfo`. -/
def forallRec (env : Env) (p : RecMeta → Bool) : Bool :=
  env.all (fun c => match c with
    | .recInfo R => p R
    | _ => true)

theorem forallInduct_eq_true {env : Env} {p : InductMeta → Bool} :
    forallInduct env p = true ↔ ∀ I, .inductInfo I ∈ env → p I = true := by
  unfold forallInduct
  rw [List.all_eq_true]
  constructor
  · intro h I hI
    exact h _ hI
  · intro h c hc
    cases c <;> first | rfl | exact h _ hc

theorem forallCtor_eq_true {env : Env} {p : CtorMeta → Bool} :
    forallCtor env p = true ↔ ∀ C, .ctorInfo C ∈ env → p C = true := by
  unfold forallCtor
  rw [List.all_eq_true]
  constructor
  · intro h C hC
    exact h _ hC
  · intro h c hc
    cases c <;> first | rfl | exact h _ hc

theorem forallRec_eq_true {env : Env} {p : RecMeta → Bool} :
    forallRec env p = true ↔ ∀ R, .recInfo R ∈ env → p R = true := by
  unfold forallRec
  rw [List.all_eq_true]
  constructor
  · intro h R hR
    exact h _ hR
  · intro h c hc
    cases c <;> first | rfl | exact h _ hc

/-- The exact diagnostic codes of the inductive-metadata replay verifier. -/
inductive InductiveReplayViolationCode : Type where
  | missingConstNameEntry
  | keyMismatch
  | duplicateConstName
  | constantHasOpenExpr
  | selfNotInAll
  | emptyAll
  | duplicateInAll
  | nonInductInAll
  | mutualMetadataMismatch
  | duplicateInCtors
  | nonCtorInCtors
  | ctorInductMismatch
  | ctorCidxMismatch
  | danglingCtorNotListedInInduct
  | danglingRecursor
  | postReplayInductMismatch
  | postReplayCtorMismatch
  | recursorMismatch
  deriving DecidableEq, Repr, Inhabited

namespace InductiveReplayViolationCode

def wireId : InductiveReplayViolationCode → String
  | .missingConstNameEntry => "missing_constName_entry"
  | .keyMismatch => "key_mismatch"
  | .duplicateConstName => "duplicate_const_name"
  | .constantHasOpenExpr => "constant_has_open_expr"
  | .selfNotInAll => "self_not_in_all"
  | .emptyAll => "empty_all"
  | .duplicateInAll => "duplicate_in_all"
  | .nonInductInAll => "non_induct_in_all"
  | .mutualMetadataMismatch => "mutual_metadata_mismatch"
  | .duplicateInCtors => "duplicate_in_ctors"
  | .nonCtorInCtors => "non_ctor_in_ctors"
  | .ctorInductMismatch => "ctor_induct_mismatch"
  | .ctorCidxMismatch => "ctor_cidx_mismatch"
  | .danglingCtorNotListedInInduct => "dangling_ctor_not_listed_in_induct"
  | .danglingRecursor => "dangling_recursor"
  | .postReplayInductMismatch => "post_replay_induct_mismatch"
  | .postReplayCtorMismatch => "post_replay_ctor_mismatch"
  | .recursorMismatch => "recursor_mismatch"

def all : List InductiveReplayViolationCode :=
  [.missingConstNameEntry, .keyMismatch, .duplicateConstName, .constantHasOpenExpr,
    .selfNotInAll, .emptyAll, .duplicateInAll, .nonInductInAll, .mutualMetadataMismatch,
    .duplicateInCtors, .nonCtorInCtors, .ctorInductMismatch, .ctorCidxMismatch,
    .danglingCtorNotListedInInduct, .danglingRecursor, .postReplayInductMismatch,
    .postReplayCtorMismatch, .recursorMismatch]

/-- Codes checked against the kernel-generated environment after replay. -/
def isPostReplay : InductiveReplayViolationCode → Bool
  | .postReplayInductMismatch | .postReplayCtorMismatch | .recursorMismatch => true
  | _ => false

theorem mem_all (c : InductiveReplayViolationCode) : c ∈ all := by
  cases c <;> decide

theorem all_length : all.length = 18 := rfl

theorem all_nodup : all.Nodup := by decide

theorem wireId_injective {a b : InductiveReplayViolationCode} (h : a.wireId = b.wireId) :
    a = b := by
  cases a <;> cases b <;> first | rfl | (exact absurd h (by decide))

end InductiveReplayViolationCode

open InductiveReplayViolationCode in
/-- The Boolean check behind each diagnostic code, over the stored module data `md` and
    the kernel-generated post-replay environment `kenv`. -/
def codeCheck : InductiveReplayViolationCode → ModuleData → Env → Bool
  | .missingConstNameEntry, md, _ => md.constNames.length == md.constants.length
  | .keyMismatch, md, _ => (md.constNames.zip md.constants).all (fun p => p.1 == p.2.name)
  | .duplicateConstName, md, _ => decide (md.constants.map RConstInfo.name).Nodup
  | .constantHasOpenExpr, md, _ => md.constants.all (fun c => c.exprs.all RExpr.isClosed)
  | .selfNotInAll, md, _ => forallInduct md.constants (fun I => decide (I.name ∈ I.all))
  | .emptyAll, md, _ => forallInduct md.constants (fun I => !I.all.isEmpty)
  | .duplicateInAll, md, _ => forallInduct md.constants (fun I => decide I.all.Nodup)
  | .nonInductInAll, md, _ =>
    forallInduct md.constants (fun I => I.all.all (isInductIn md.constants))
  | .mutualMetadataMismatch, md, _ =>
    forallInduct md.constants (fun I => I.all.all (mutualAgrees md.constants I))
  | .duplicateInCtors, md, _ => forallInduct md.constants (fun I => decide I.ctors.Nodup)
  | .nonCtorInCtors, md, _ =>
    forallInduct md.constants (fun I => I.ctors.all (isCtorIn md.constants))
  | .ctorInductMismatch, md, _ =>
    forallInduct md.constants (fun I => I.ctors.all (ctorParentAgrees md.constants I))
  | .ctorCidxMismatch, md, _ =>
    forallInduct md.constants (fun I => I.ctors.all (ctorCidxAgrees md.constants I))
  | .danglingCtorNotListedInInduct, md, _ =>
    forallCtor md.constants (ctorListedInParent md.constants)
  | .danglingRecursor, md, _ => forallRec md.constants (recAnchored md.constants)
  | .postReplayInductMismatch, md, kenv =>
    forallInduct md.constants (fun I => lookup kenv I.name == some (.inductInfo I))
  | .postReplayCtorMismatch, md, kenv =>
    forallCtor md.constants (fun C => lookup kenv C.name == some (.ctorInfo C))
  | .recursorMismatch, md, kenv =>
    forallRec md.constants (fun R => lookup kenv R.name == some (.recInfo R))

/-- Pre-replay structural invariants plus post-replay agreement of every stored
    inductive, constructor, and recursor with the kernel-generated environment. -/
def InductiveReplayWellFormed (md : ModuleData) (kenv : Env) : Prop :=
  ∀ code, codeCheck code md kenv = true

/-- The pre-replay half alone (codes not consulting the kernel environment). -/
def PreReplayInvariants (md : ModuleData) : Prop :=
  ∀ code, code.isPostReplay = false → codeCheck code md [] = true

/-- Every failing diagnostic code, in canonical order. -/
def inductiveReplayViolations (md : ModuleData) (kenv : Env) :
    List InductiveReplayViolationCode :=
  InductiveReplayViolationCode.all.filter (fun c => !codeCheck c md kenv)

/-- Executable verifier. -/
def checkInductiveReplay (md : ModuleData) (kenv : Env) : Bool :=
  InductiveReplayViolationCode.all.all (fun c => codeCheck c md kenv)

theorem checkInductiveReplay_iff (md : ModuleData) (kenv : Env) :
    checkInductiveReplay md kenv = true ↔ InductiveReplayWellFormed md kenv := by
  unfold checkInductiveReplay InductiveReplayWellFormed
  rw [List.all_eq_true]
  exact ⟨fun h c => h c (InductiveReplayViolationCode.mem_all c), fun h c _ => h c⟩

instance (md : ModuleData) (kenv : Env) : Decidable (InductiveReplayWellFormed md kenv) :=
  decidable_of_iff _ (checkInductiveReplay_iff md kenv)

theorem mem_inductiveReplayViolations {md : ModuleData} {kenv : Env}
    {c : InductiveReplayViolationCode} :
    c ∈ inductiveReplayViolations md kenv ↔ codeCheck c md kenv = false := by
  unfold inductiveReplayViolations
  rw [List.mem_filter]
  simp [InductiveReplayViolationCode.mem_all]

theorem inductiveReplayViolations_eq_nil_iff (md : ModuleData) (kenv : Env) :
    inductiveReplayViolations md kenv = [] ↔ InductiveReplayWellFormed md kenv := by
  rw [List.eq_nil_iff_forall_not_mem]
  constructor
  · intro h c
    have hc := h c
    rw [mem_inductiveReplayViolations] at hc
    cases hEq : codeCheck c md kenv
    · exact absurd hEq hc
    · rfl
  · intro h c hc
    rw [mem_inductiveReplayViolations, h c] at hc
    cases hc

/-- Well-formedness implies the pre-replay invariants. -/
theorem preReplayInvariants_of_wellFormed {md : ModuleData} {kenv : Env}
    (h : InductiveReplayWellFormed md kenv) : PreReplayInvariants md := by
  intro code hPre
  have hc := h code
  cases code <;> first
    | exact absurd hPre (by decide)
    | (simp only [codeCheck] at hc ⊢; exact hc)

/-- Restoration: a well-formed module's inductive family agrees exactly with the
    kernel-generated environment, constant by constant. -/
theorem inductiveReplayWellFormed_kernel_agreement {md : ModuleData} {kenv : Env}
    (h : InductiveReplayWellFormed md kenv) :
    ∀ c ∈ md.constants, c.isInductFamily = true → lookup kenv c.name = some c := by
  intro c hc hFam
  cases c with
  | inductInfo I =>
    have := forallInduct_eq_true.mp (h .postReplayInductMismatch) I hc
    exact eq_of_beq this
  | ctorInfo C =>
    have := forallCtor_eq_true.mp (h .postReplayCtorMismatch) C hc
    exact eq_of_beq this
  | recInfo R =>
    have := forallRec_eq_true.mp (h .recursorMismatch) R hc
    exact eq_of_beq this
  | _ => cases hFam

/-- Restoration: a well-formed module's stored inductives are self-anchored in their
    mutual block, with distinct members and distinct constructors. -/
theorem inductiveReplayWellFormed_block_anchored {md : ModuleData} {kenv : Env}
    (h : InductiveReplayWellFormed md kenv) :
    ∀ I, .inductInfo I ∈ md.constants → I.name ∈ I.all ∧ I.all.Nodup ∧ I.ctors.Nodup := by
  intro I hI
  refine ⟨?_, ?_, ?_⟩
  · exact of_decide_eq_true (forallInduct_eq_true.mp (h .selfNotInAll) I hI)
  · exact of_decide_eq_true (forallInduct_eq_true.mp (h .duplicateInAll) I hI)
  · exact of_decide_eq_true (forallInduct_eq_true.mp (h .duplicateInCtors) I hI)

theorem list_eq_map_of_zip_all :
    ∀ (ns : List ConstName) (cs : List RConstInfo),
      ns.length = cs.length →
      (ns.zip cs).all (fun p => p.1 == p.2.name) = true →
      ns = cs.map RConstInfo.name
  | [], [], _, _ => rfl
  | _ :: _, [], hLen, _ => by cases hLen
  | [], _ :: _, hLen, _ => by cases hLen
  | n :: ns, c :: cs, hLen, hAll => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hAll
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hLen
    rw [hAll.1, list_eq_map_of_zip_all ns cs hLen hAll.2]
    rfl

/-- Restoration: a well-formed module's `constNames` table is exact (no missing entries
    and no key/constant name drift). -/
theorem inductiveReplayWellFormed_constNames_eq {md : ModuleData} {kenv : Env}
    (h : InductiveReplayWellFormed md kenv) :
    md.constNames = md.constants.map RConstInfo.name :=
  list_eq_map_of_zip_all md.constNames md.constants
    (eq_of_beq (h .missingConstNameEntry)) (h .keyMismatch)

/-! ### 2.1 Pre-replay self-comparison is tautological -/

/-- The tautological check: compare each stored entry against the environment built from
    the very same stored entries. -/
def selfComparisonCheck (md : ModuleData) : Bool :=
  md.constants.all (fun c => lookup md.constants c.name == some c)

theorem lookup_self_of_nodup :
    ∀ (env : Env), (env.map RConstInfo.name).Nodup → ∀ c ∈ env, lookup env c.name = some c
  | [], _, c, hc => absurd hc (List.not_mem_nil)
  | d :: ds, hNd, c, hc => by
    rw [List.map_cons, List.nodup_cons] at hNd
    unfold lookup
    rw [List.find?_cons]
    rcases List.mem_cons.mp hc with hEq | hTail
    · subst hEq
      simp
    · have hNe : d.name ≠ c.name := by
        intro hN
        exact hNd.1 (hN ▸ List.mem_map_of_mem hTail)
      have hBeq : (d.name == c.name) = false := by simpa using hNe
      rw [hBeq]
      exact lookup_self_of_nodup ds hNd.2 c hTail

/-- **Self-comparison is tautological.** It accepts every module whose constant names
    are distinct, whatever metadata the module stores, so it cannot detect a binary
    `.olean` forgery of inductive metadata. -/
theorem selfComparison_tautological (md : ModuleData)
    (hNodup : (md.constants.map RConstInfo.name).Nodup) : selfComparisonCheck md = true := by
  unfold selfComparisonCheck
  rw [List.all_eq_true]
  intro c hc
  rw [lookup_self_of_nodup md.constants hNodup c hc]
  exact beq_self_eq_true _

/-! ### 2.2 The pinned replay loop and its `remaining`-erasure gap -/

/-- The pinned toolchain's replay loop over stored inductives: an inductive already
    erased is skipped; otherwise the kernel regenerates the block named by its `all`
    field (`gen`), and every member of `all` is erased, without checking that the
    inductive itself is a member. -/
def replayInductiveBlocks (gen : List InductMeta → Env) (stored : Env) :
    List InductMeta → List ConstName → Env
  | [], _ => []
  | I :: rest, erased =>
    if I.name ∈ erased then replayInductiveBlocks gen stored rest erased
    else
      let block := I.all.filterMap (fun n => match lookup stored n with
        | some (.inductInfo J) => some J
        | _ => none)
      gen block ++ replayInductiveBlocks gen stored rest (I.all ++ erased)

/-- Stored inductives of a module, in order. -/
def storedInducts (env : Env) : List InductMeta :=
  env.filterMap (fun c => match c with
    | .inductInfo I => some I
    | _ => none)

/-- A faithful kernel block generator: each block member is regenerated with its
    constructors and recursors exactly as stored. -/
def faithfulGen (stored : Env) (block : List InductMeta) : Env :=
  block.flatMap (fun J => .inductInfo J ::
    stored.filter (fun c => match c with
      | .ctorInfo C => C.induct == J.name
      | .recInfo R => R.all.head? == some J.name
      | _ => false))

/-- Kernel-generated environment of a module under the pinned replay loop. -/
def pinnedReplayEnv (md : ModuleData) : Env :=
  replayInductiveBlocks (faithfulGen md.constants) md.constants (storedInducts md.constants) []

/-! ### 2.3 Every forged-inductive class is rejected with its exact code -/

/-- The forged-inductive classes a binary `.olean` forgery can exhibit (in bijection with
    `InductiveReplayViolationCode`). -/
inductive ForgedInductiveClass : Type where
  | missingConstNameEntry
  | keyMismatch
  | duplicateConstName
  | openExpression
  | selfNotInAll
  | emptyAll
  | duplicateInAll
  | nonInductInAll
  | mutualMetadataMismatch
  | duplicateInCtors
  | nonCtorInCtors
  | wrongParentCtor
  | wrongCidxCtor
  | danglingCtorInfo
  | danglingRecInfo
  | postReplayInductDrift
  | postReplayCtorDrift
  | postReplayRecDrift
  deriving DecidableEq, Repr

/-- The diagnostic code each forgery class is reported under. -/
def ForgedInductiveClass.code : ForgedInductiveClass → InductiveReplayViolationCode
  | .missingConstNameEntry => .missingConstNameEntry
  | .keyMismatch => .keyMismatch
  | .duplicateConstName => .duplicateConstName
  | .openExpression => .constantHasOpenExpr
  | .selfNotInAll => .selfNotInAll
  | .emptyAll => .emptyAll
  | .duplicateInAll => .duplicateInAll
  | .nonInductInAll => .nonInductInAll
  | .mutualMetadataMismatch => .mutualMetadataMismatch
  | .duplicateInCtors => .duplicateInCtors
  | .nonCtorInCtors => .nonCtorInCtors
  | .wrongParentCtor => .ctorInductMismatch
  | .wrongCidxCtor => .ctorCidxMismatch
  | .danglingCtorInfo => .danglingCtorNotListedInInduct
  | .danglingRecInfo => .danglingRecursor
  | .postReplayInductDrift => .postReplayInductMismatch
  | .postReplayCtorDrift => .postReplayCtorMismatch
  | .postReplayRecDrift => .recursorMismatch

def ForgedInductiveClass.all : List ForgedInductiveClass :=
  [.missingConstNameEntry, .keyMismatch, .duplicateConstName, .openExpression,
    .selfNotInAll, .emptyAll, .duplicateInAll, .nonInductInAll, .mutualMetadataMismatch,
    .duplicateInCtors, .nonCtorInCtors, .wrongParentCtor, .wrongCidxCtor,
    .danglingCtorInfo, .danglingRecInfo, .postReplayInductDrift, .postReplayCtorDrift,
    .postReplayRecDrift]

theorem ForgedInductiveClass.all_map_code :
    ForgedInductiveClass.all.map ForgedInductiveClass.code = InductiveReplayViolationCode.all :=
  rfl

theorem ForgedInductiveClass.code_injective {a b : ForgedInductiveClass}
    (h : a.code = b.code) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

/-- Semantic (Prop-level) description of each forgery class. -/
def Exhibits : ForgedInductiveClass → ModuleData → Env → Prop
  | .missingConstNameEntry, md, _ => md.constNames.length ≠ md.constants.length
  | .keyMismatch, md, _ => ∃ p ∈ md.constNames.zip md.constants, p.1 ≠ p.2.name
  | .duplicateConstName, md, _ => ¬ (md.constants.map RConstInfo.name).Nodup
  | .openExpression, md, _ => ∃ c ∈ md.constants, ∃ e ∈ c.exprs, e.isClosed = false
  | .selfNotInAll, md, _ => ∃ I, .inductInfo I ∈ md.constants ∧ I.name ∉ I.all
  | .emptyAll, md, _ => ∃ I, .inductInfo I ∈ md.constants ∧ I.all = []
  | .duplicateInAll, md, _ => ∃ I, .inductInfo I ∈ md.constants ∧ ¬ I.all.Nodup
  | .nonInductInAll, md, _ =>
    ∃ I, .inductInfo I ∈ md.constants ∧
      ∃ n ∈ I.all, ∀ J, lookup md.constants n ≠ some (.inductInfo J)
  | .mutualMetadataMismatch, md, _ =>
    ∃ I, .inductInfo I ∈ md.constants ∧ ∃ n ∈ I.all, ∃ J,
      lookup md.constants n = some (.inductInfo J) ∧
      (J.all ≠ I.all ∨ J.numParams ≠ I.numParams ∨ J.levelParams ≠ I.levelParams ∨
        J.isUnsafe ≠ I.isUnsafe)
  | .duplicateInCtors, md, _ => ∃ I, .inductInfo I ∈ md.constants ∧ ¬ I.ctors.Nodup
  | .nonCtorInCtors, md, _ =>
    ∃ I, .inductInfo I ∈ md.constants ∧
      ∃ c ∈ I.ctors, ∀ C, lookup md.constants c ≠ some (.ctorInfo C)
  | .wrongParentCtor, md, _ =>
    ∃ I, .inductInfo I ∈ md.constants ∧ ∃ c ∈ I.ctors, ∃ C,
      lookup md.constants c = some (.ctorInfo C) ∧
      (C.induct ≠ I.name ∨ C.numParams ≠ I.numParams)
  | .wrongCidxCtor, md, _ =>
    ∃ I, .inductInfo I ∈ md.constants ∧ ∃ c ∈ I.ctors, ∃ C,
      lookup md.constants c = some (.ctorInfo C) ∧ posOf c I.ctors ≠ some C.cidx
  | .danglingCtorInfo, md, _ =>
    ∃ C, .ctorInfo C ∈ md.constants ∧
      ∀ I, lookup md.constants C.induct = some (.inductInfo I) → C.name ∉ I.ctors
  | .danglingRecInfo, md, _ =>
    ∃ R, .recInfo R ∈ md.constants ∧
      (R.all = [] ∨ ¬ R.all.Nodup ∨
        (∃ n ∈ R.all, ∀ I, lookup md.constants n ≠ some (.inductInfo I)) ∨
        ∃ r ∈ R.rules, ∀ C, lookup md.constants r.ctor = some (.ctorInfo C) → C.induct ∉ R.all)
  | .postReplayInductDrift, md, kenv =>
    ∃ I, .inductInfo I ∈ md.constants ∧ lookup kenv I.name ≠ some (.inductInfo I)
  | .postReplayCtorDrift, md, kenv =>
    ∃ C, .ctorInfo C ∈ md.constants ∧ lookup kenv C.name ≠ some (.ctorInfo C)
  | .postReplayRecDrift, md, kenv =>
    ∃ R, .recInfo R ∈ md.constants ∧ lookup kenv R.name ≠ some (.recInfo R)

theorem isInductIn_eq_false {env : Env} {n : ConstName}
    (h : ∀ J, lookup env n ≠ some (.inductInfo J)) : isInductIn env n = false := by
  unfold isInductIn
  split
  · rename_i J hJ
    exact absurd hJ (h J)
  · rfl

theorem isCtorIn_eq_false {env : Env} {n : ConstName}
    (h : ∀ C, lookup env n ≠ some (.ctorInfo C)) : isCtorIn env n = false := by
  unfold isCtorIn
  split
  · rename_i C hC
    exact absurd hC (h C)
  · rfl

/-- Boolean-level helper: a failing element falsifies `List.all`. -/
theorem all_eq_false_of_mem {α : Type} {l : List α} {p : α → Bool} {a : α}
    (ha : a ∈ l) (hp : p a = false) : l.all p = false := by
  cases hAll : l.all p
  · rfl
  · rw [List.all_eq_true] at hAll
    rw [hAll a ha] at hp
    cases hp

theorem forallInduct_eq_false {env : Env} {p : InductMeta → Bool} {I : InductMeta}
    (hI : .inductInfo I ∈ env) (hp : p I = false) : forallInduct env p = false :=
  all_eq_false_of_mem hI hp

theorem forallCtor_eq_false {env : Env} {p : CtorMeta → Bool} {C : CtorMeta}
    (hC : .ctorInfo C ∈ env) (hp : p C = false) : forallCtor env p = false :=
  all_eq_false_of_mem hC hp

theorem forallRec_eq_false {env : Env} {p : RecMeta → Bool} {R : RecMeta}
    (hR : .recInfo R ∈ env) (hp : p R = false) : forallRec env p = false :=
  all_eq_false_of_mem hR hp

theorem beq_some_eq_false {a b : Option RConstInfo} (h : a ≠ b) : (a == b) = false := by
  simpa using h

/-- Each forgery class falsifies exactly its own diagnostic check. -/
theorem codeCheck_eq_false_of_exhibits {md : ModuleData} {kenv : Env}
    {cls : ForgedInductiveClass} (h : Exhibits cls md kenv) :
    codeCheck cls.code md kenv = false := by
  cases cls with
  | missingConstNameEntry =>
    simpa [ForgedInductiveClass.code, codeCheck, Exhibits] using h
  | keyMismatch =>
    obtain ⟨p, hp, hNe⟩ := h
    exact all_eq_false_of_mem hp (by simpa using hNe)
  | duplicateConstName =>
    exact decide_eq_false h
  | openExpression =>
    obtain ⟨c, hc, e, he, hOpen⟩ := h
    exact all_eq_false_of_mem hc (all_eq_false_of_mem he hOpen)
  | selfNotInAll =>
    obtain ⟨I, hI, hNot⟩ := h
    exact forallInduct_eq_false hI (decide_eq_false hNot)
  | emptyAll =>
    obtain ⟨I, hI, hNil⟩ := h
    exact forallInduct_eq_false hI (by simp [hNil])
  | duplicateInAll =>
    obtain ⟨I, hI, hDup⟩ := h
    exact forallInduct_eq_false hI (decide_eq_false hDup)
  | nonInductInAll =>
    obtain ⟨I, hI, n, hn, hNone⟩ := h
    exact forallInduct_eq_false hI (all_eq_false_of_mem hn (isInductIn_eq_false hNone))
  | mutualMetadataMismatch =>
    obtain ⟨I, hI, n, hn, J, hJ, hDiff⟩ := h
    refine forallInduct_eq_false hI (all_eq_false_of_mem hn ?_)
    unfold mutualAgrees
    rw [hJ]
    simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    rcases hDiff with h1 | h2 | h3 | h4
    · exact Or.inl (Or.inl (Or.inl h1))
    · exact Or.inl (Or.inl (Or.inr h2))
    · exact Or.inl (Or.inr h3)
    · exact Or.inr h4
  | duplicateInCtors =>
    obtain ⟨I, hI, hDup⟩ := h
    exact forallInduct_eq_false hI (decide_eq_false hDup)
  | nonCtorInCtors =>
    obtain ⟨I, hI, c, hc, hNone⟩ := h
    exact forallInduct_eq_false hI (all_eq_false_of_mem hc (isCtorIn_eq_false hNone))
  | wrongParentCtor =>
    obtain ⟨I, hI, c, hc, C, hC, hDiff⟩ := h
    refine forallInduct_eq_false hI (all_eq_false_of_mem hc ?_)
    unfold ctorParentAgrees
    rw [hC]
    simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    exact hDiff
  | wrongCidxCtor =>
    obtain ⟨I, hI, c, hc, C, hC, hDiff⟩ := h
    refine forallInduct_eq_false hI (all_eq_false_of_mem hc ?_)
    unfold ctorCidxAgrees
    rw [hC]
    simpa using hDiff
  | danglingCtorInfo =>
    obtain ⟨C, hC, hNot⟩ := h
    refine forallCtor_eq_false hC ?_
    unfold ctorListedInParent
    split
    · rename_i I hI
      exact decide_eq_false (hNot I hI)
    · rfl
  | danglingRecInfo =>
    obtain ⟨R, hR, hBad⟩ := h
    refine forallRec_eq_false hR ?_
    unfold recAnchored
    rcases hBad with hNil | hDup | ⟨n, hn, hNone⟩ | ⟨r, hr, hBadRule⟩
    · simp [hNil]
    · simp [decide_eq_false hDup]
    · rw [all_eq_false_of_mem hn (isInductIn_eq_false hNone)]
      simp
    · have hRule : recRuleAnchored md.constants R.all r = false := by
        unfold recRuleAnchored
        split
        · rename_i C hC
          exact decide_eq_false (hBadRule C hC)
        · rfl
      rw [all_eq_false_of_mem hr hRule]
      simp
  | postReplayInductDrift =>
    obtain ⟨I, hI, hNe⟩ := h
    exact forallInduct_eq_false hI (beq_some_eq_false hNe)
  | postReplayCtorDrift =>
    obtain ⟨C, hC, hNe⟩ := h
    exact forallCtor_eq_false hC (beq_some_eq_false hNe)
  | postReplayRecDrift =>
    obtain ⟨R, hR, hNe⟩ := h
    exact forallRec_eq_false hR (beq_some_eq_false hNe)

/-- **`InductiveReplayWellFormed` rejects every forged-inductive class**, and reports
    the class's exact diagnostic code. -/
theorem inductiveReplayWellFormed_rejects {md : ModuleData} {kenv : Env}
    {cls : ForgedInductiveClass} (h : Exhibits cls md kenv) :
    ¬ InductiveReplayWellFormed md kenv ∧ cls.code ∈ inductiveReplayViolations md kenv := by
  have hFalse := codeCheck_eq_false_of_exhibits h
  refine ⟨fun hWF => ?_, mem_inductiveReplayViolations.mpr hFalse⟩
  rw [hWF cls.code] at hFalse
  cases hFalse

/-- An inductive-family constant the kernel never regenerated is rejected by the
    unconditional post-replay sweep. -/
theorem postReplaySweep_rejects_unreplayed {md : ModuleData} {kenv : Env} {c : RConstInfo}
    (hc : c ∈ md.constants) (hFam : c.isInductFamily = true) (hMissing : lookup kenv c.name = none) :
    ¬ InductiveReplayWellFormed md kenv := by
  intro hWF
  have := inductiveReplayWellFormed_kernel_agreement hWF c hc hFam
  rw [hMissing] at this
  cases this

/-! ### 2.4 Concrete fixtures: a clean block and a `lean4#16717` forgery -/

/-- A two-constructor inductive `B` (name `1`) with constructors `2`, `3` and recursor `4`. -/
def fixtureInduct : InductMeta :=
  { name := 1, levelParams := 0, type := .sort 1, numParams := 0, numIndices := 0,
    all := [1], ctors := [2, 3], numNested := 0, isRec := false, isReflexive := false,
    isUnsafe := false }

def fixtureCtor0 : CtorMeta :=
  { name := 2, levelParams := 0, type := .const 1, induct := 1, cidx := 0, numParams := 0,
    numFields := 0, isUnsafe := false }

def fixtureCtor1 : CtorMeta :=
  { name := 3, levelParams := 0, type := .const 1, induct := 1, cidx := 1, numParams := 0,
    numFields := 0, isUnsafe := false }

def fixtureRec : RecMeta :=
  { name := 4, levelParams := 1, type := .forallE (.sort 0) (.bvar 0), all := [1],
    numParams := 0, numIndices := 0, numMotives := 1, numMinors := 2,
    rules := [{ ctor := 2, nfields := 0, rhs := .lam (.sort 0) (.bvar 0) },
      { ctor := 3, nfields := 0, rhs := .lam (.sort 0) (.bvar 0) }],
    k := false, isUnsafe := false }

def cleanModule : ModuleData :=
  { constNames := [1, 2, 3, 4],
    constants := [.inductInfo fixtureInduct, .ctorInfo fixtureCtor0, .ctorInfo fixtureCtor1,
      .recInfo fixtureRec] }

/-- The clean module passes the verifier against its pinned-replay kernel environment. -/
theorem cleanModule_wellFormed : InductiveReplayWellFormed cleanModule (pinnedReplayEnv cleanModule) := by
  decide

/-- A forged inductive `F` (name `5`) whose `all` field names only `B`: the pinned loop
    regenerates `B`'s block on its behalf, erases `B`, and never sends `F` itself. -/
def forgedSelfNotInAll : InductMeta :=
  { name := 5, levelParams := 0, type := .sort 1, numParams := 0, numIndices := 0,
    all := [1], ctors := [], numNested := 0, isRec := false, isReflexive := false,
    isUnsafe := false }

def forgedModule : ModuleData :=
  { constNames := [5, 1, 2, 3, 4],
    constants := .inductInfo forgedSelfNotInAll :: cleanModule.constants }

/-- **The `lean4#16717` gap, end to end.** The forged module passes self-comparison,
    the pinned replay loop never regenerates `F`, and the verifier rejects it under both
    `self_not_in_all` and `post_replay_induct_mismatch`. -/
theorem forgedModule_gap_closed :
    selfComparisonCheck forgedModule = true ∧ lookup (pinnedReplayEnv forgedModule) 5 = none ∧
      ¬ InductiveReplayWellFormed forgedModule (pinnedReplayEnv forgedModule) ∧
      inductiveReplayViolations forgedModule (pinnedReplayEnv forgedModule) =
        [.selfNotInAll, .postReplayInductMismatch] := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- A metadata-drift forgery that passes every pre-replay structural invariant: the
    stored `numIndices` of `B` is `1`, while the kernel regenerates `0`. -/
def driftedInduct : InductMeta := { fixtureInduct with numIndices := 1 }

def driftedModule : ModuleData :=
  { constNames := [1, 2, 3, 4],
    constants := [.inductInfo driftedInduct, .ctorInfo fixtureCtor0, .ctorInfo fixtureCtor1,
      .recInfo fixtureRec] }

/-- **Pre-replay validation alone is insufficient**: the drifted module satisfies every
    pre-replay invariant and passes self-comparison, yet disagrees with the clean kernel
    output and is rejected only by post-replay agreement. -/
theorem preReplayOnly_misses_metadata_drift :
    PreReplayInvariants driftedModule ∧ selfComparisonCheck driftedModule = true ∧
      inductiveReplayViolations driftedModule (pinnedReplayEnv cleanModule) =
        [.postReplayInductMismatch] := by
  refine ⟨?_, by decide, by decide⟩
  intro code hPre
  cases code <;> first | decide | exact absurd hPre (by decide)

/-! ## 3. Pillar 2 — Sharded Audit and Cross-Shard Reconciliation (`grmf`) -/

/-- Module identifiers. -/
abbrev ModName := Nat

/-- A downstream world: its modules and the constants each module declares. -/
structure ModuleWorld where
  modules : List ModName
  declsOf : ModName → List RConstInfo

namespace ModuleWorld

/-- The monolithic environment: every declaration of every module. -/
def monoEnv (W : ModuleWorld) : Env := W.modules.flatMap W.declsOf

/-- Monolithic audit roots: every claim. -/
def roots (W : ModuleWorld) : List RConstInfo := W.monoEnv.filter RConstInfo.isClaim

theorem mem_monoEnv {W : ModuleWorld} {d : RConstInfo} :
    d ∈ W.monoEnv ↔ ∃ m ∈ W.modules, d ∈ W.declsOf m := by
  unfold monoEnv
  rw [List.mem_flatMap]

end ModuleWorld

/-- One audit shard: its owned modules and its local environment (owned modules plus
    their transitive imports). -/
structure AuditShard where
  modules : List ModName
  env : Env

/-- Audit roots of a shard: the claims of its owned modules. -/
def AuditShard.roots (W : ModuleWorld) (s : AuditShard) : List RConstInfo :=
  (s.modules.flatMap W.declsOf).filter RConstInfo.isClaim

/-- Transitive dependency reachability from `roots` within `env`. -/
inductive Reach (env : Env) (roots : List RConstInfo) : RConstInfo → Prop where
  | root {c : RConstInfo} : c ∈ roots → c ∈ env → Reach env roots c
  | step {c d : RConstInfo} : Reach env roots c → d.name ∈ c.refs → d ∈ env → Reach env roots d

theorem Reach.mem_env {env : Env} {roots : List RConstInfo} {c : RConstInfo}
    (h : Reach env roots c) : c ∈ env := by
  cases h with
  | root _ hc => exact hc
  | step _ _ hd => exact hd

theorem Reach.false_of_nil_roots {env : Env} {c : RConstInfo} (h : Reach env [] c) : False := by
  induction h with
  | root hc _ => exact absurd hc List.not_mem_nil
  | step _ _ _ ih => exact ih

/-- Axioms in the transitive closure of an audit. -/
def AxiomOf (env : Env) (roots : List RConstInfo) (a : ConstName) : Prop :=
  ∃ d, Reach env roots d ∧ d.isAxiom = true ∧ d.name = a

def monoAxioms (W : ModuleWorld) (a : ConstName) : Prop := AxiomOf W.monoEnv W.roots a

def shardAxioms (W : ModuleWorld) (s : AuditShard) (a : ConstName) : Prop :=
  AxiomOf s.env (s.roots W) a

/-- Partition completeness: every module is owned by some shard, and shards own only
    world modules. -/
def OrphanFreePartition (W : ModuleWorld) (shards : List AuditShard) : Prop :=
  (∀ m ∈ W.modules, ∃ s ∈ shards, m ∈ s.modules) ∧
    (∀ s ∈ shards, ∀ m ∈ s.modules, m ∈ W.modules)

/-- Shard-local transitive closure: a shard environment contains its owned modules,
    draws only from the world, and resolves every reference the world can resolve. -/
def ShardLocalClosure (W : ModuleWorld) (s : AuditShard) : Prop :=
  (∀ m ∈ s.modules, ∀ d ∈ W.declsOf m, d ∈ s.env) ∧
    (∀ d ∈ s.env, d ∈ W.monoEnv) ∧
    (∀ c ∈ s.env, ∀ d ∈ W.monoEnv, d.name ∈ c.refs → ∃ d' ∈ s.env, d'.name = d.name)

/-- Exact structural compatibility of two constants: identical constructor tag and
    identical fields, including every inductive, constructor, and recursor field. -/
def strictConstCompat : RConstInfo → RConstInfo → Bool
  | .axiomInfo n l t, .axiomInfo n' l' t' => n == n' && l == l' && t == t'
  | .defnInfo n l t v, .defnInfo n' l' t' v' => n == n' && l == l' && t == t' && v == v'
  | .thmInfo n l t v, .thmInfo n' l' t' v' => n == n' && l == l' && t == t' && v == v'
  | .opaqueInfo n l t v, .opaqueInfo n' l' t' v' => n == n' && l == l' && t == t' && v == v'
  | .quotInfo n l t, .quotInfo n' l' t' => n == n' && l == l' && t == t'
  | .inductInfo I, .inductInfo I' => I == I'
  | .ctorInfo C, .ctorInfo C' => C == C'
  | .recInfo R, .recInfo R' => R == R'
  | _, _ => false

theorem strictConstCompat_iff_eq (a b : RConstInfo) : strictConstCompat a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [strictConstCompat, and_assoc]

/-- Fingerprint compatibility: names, `hash64` of the type, and `hash64` of the value. -/
def hashCompat (a b : RConstInfo) : Bool :=
  a.name == b.name && a.type.hash64 == b.type.hash64 &&
    a.value?.map RExpr.hash64 == b.value?.map RExpr.hash64

/-- Naive compatibility: names and types agree, and values agree whenever both exist,
    treating `value? = none` as compatible with anything. -/
def naiveCompat (a b : RConstInfo) : Bool :=
  a.name == b.name && a.type == b.type &&
    (a.value?.isNone || b.value?.isNone || a.value? == b.value?)

/-- **`Expr.hash` collision**: literals differing by `2 ^ 64` share a fingerprint. -/
theorem exprHash64_collision :
    (RExpr.natLit 3).hash64 = (RExpr.natLit (3 + 2 ^ 64)).hash64 ∧
      RExpr.natLit 3 ≠ RExpr.natLit (3 + 2 ^ 64) := by
  refine ⟨by decide, by decide⟩

/-- Fingerprint compatibility accepts two definitions with different values. -/
theorem hashCompat_accepts_distinct_values :
    hashCompat (.defnInfo 7 0 (.const 1) (.natLit 3))
        (.defnInfo 7 0 (.const 1) (.natLit (3 + 2 ^ 64))) = true ∧
      strictConstCompat (.defnInfo 7 0 (.const 1) (.natLit 3))
        (.defnInfo 7 0 (.const 1) (.natLit (3 + 2 ^ 64))) = false := by
  refine ⟨by decide, by decide⟩

/-- **`value? = none` conflation**: naive compatibility accepts an axiom against a
    definition of the same name and type. -/
theorem naiveCompat_conflates_axiom_defn :
    naiveCompat (.axiomInfo 7 0 (.const 1)) (.defnInfo 7 0 (.const 1) (.const 2)) = true ∧
      strictConstCompat (.axiomInfo 7 0 (.const 1)) (.defnInfo 7 0 (.const 1) (.const 2)) =
        false := by
  refine ⟨by decide, by decide⟩

/-- Cross-shard reconciliation: any two constants of the same name drawn from any two
    shard environments are strictly compatible. -/
def CrossShardReconciled (shards : List AuditShard) : Prop :=
  ∀ s₁ ∈ shards, ∀ s₂ ∈ shards, ∀ d₁ ∈ s₁.env, ∀ d₂ ∈ s₂.env,
    d₁.name = d₂.name → strictConstCompat d₁ d₂ = true

instance (shards : List AuditShard) : Decidable (CrossShardReconciled shards) :=
  inferInstanceAs (Decidable (∀ s₁ ∈ shards, ∀ s₂ ∈ shards, ∀ d₁ ∈ s₁.env, ∀ d₂ ∈ s₂.env,
    d₁.name = d₂.name → strictConstCompat d₁ d₂ = true))

/-- A monolithic duplicate-constant conflict on name `n`. -/
def MonoConflict (W : ModuleWorld) (n : ConstName) : Prop :=
  ∃ d₁ ∈ W.monoEnv, ∃ d₂ ∈ W.monoEnv, d₁.name = n ∧ d₂.name = n ∧ strictConstCompat d₁ d₂ = false

/-- A conflict reported by the sharded audit plus its cross-shard reconciler. -/
def ShardedConflict (shards : List AuditShard) (n : ConstName) : Prop :=
  ∃ s₁ ∈ shards, ∃ s₂ ∈ shards, ∃ d₁ ∈ s₁.env, ∃ d₂ ∈ s₂.env,
    d₁.name = n ∧ d₂.name = n ∧ strictConstCompat d₁ d₂ = false

/-- A conflict visible to an independent shard on its own (no reconciliation). -/
def ShardLocalConflict (shards : List AuditShard) (n : ConstName) : Prop :=
  ∃ s ∈ shards, ∃ d₁ ∈ s.env, ∃ d₂ ∈ s.env,
    d₁.name = n ∧ d₂.name = n ∧ strictConstCompat d₁ d₂ = false

theorem crossShardReconciled_iff_no_conflict (shards : List AuditShard) :
    CrossShardReconciled shards ↔ ∀ n, ¬ ShardedConflict shards n := by
  constructor
  · rintro h n ⟨s₁, hs₁, s₂, hs₂, d₁, hd₁, d₂, hd₂, hn₁, hn₂, hc⟩
    rw [h s₁ hs₁ s₂ hs₂ d₁ hd₁ d₂ hd₂ (hn₁.trans hn₂.symm)] at hc
    cases hc
  · intro h s₁ hs₁ s₂ hs₂ d₁ hd₁ d₂ hd₂ hn
    cases hc : strictConstCompat d₁ d₂
    · exact absurd ⟨s₁, hs₁, s₂, hs₂, d₁, hd₁, d₂, hd₂, rfl, hn.symm, hc⟩ (h d₁.name)
    · rfl

/-- Every world declaration lies in some shard environment. -/
theorem mem_some_shard_env {W : ModuleWorld} {shards : List AuditShard}
    (hP : OrphanFreePartition W shards) (hC : ∀ s ∈ shards, ShardLocalClosure W s)
    {d : RConstInfo} (hd : d ∈ W.monoEnv) : ∃ s ∈ shards, d ∈ s.env := by
  obtain ⟨m, hm, hdm⟩ := ModuleWorld.mem_monoEnv.mp hd
  obtain ⟨s, hs, hms⟩ := hP.1 m hm
  exact ⟨s, hs, (hC s hs).1 m hms d hdm⟩

/-- **Violation parity**: orphan-free sharding with cross-shard reconciliation reports
    exactly the monolithic duplicate-constant conflicts. -/
theorem violation_parity {W : ModuleWorld} {shards : List AuditShard}
    (hP : OrphanFreePartition W shards) (hC : ∀ s ∈ shards, ShardLocalClosure W s)
    (n : ConstName) : MonoConflict W n ↔ ShardedConflict shards n := by
  constructor
  · rintro ⟨d₁, hd₁, d₂, hd₂, hn₁, hn₂, hc⟩
    obtain ⟨s₁, hs₁, h₁⟩ := mem_some_shard_env hP hC hd₁
    obtain ⟨s₂, hs₂, h₂⟩ := mem_some_shard_env hP hC hd₂
    exact ⟨s₁, hs₁, s₂, hs₂, d₁, h₁, d₂, h₂, hn₁, hn₂, hc⟩
  · rintro ⟨s₁, hs₁, s₂, hs₂, d₁, hd₁, d₂, hd₂, hn₁, hn₂, hc⟩
    exact ⟨d₁, (hC s₁ hs₁).2.1 d₁ hd₁, d₂, (hC s₂ hs₂).2.1 d₂ hd₂, hn₁, hn₂, hc⟩

theorem shardReach_mono {W : ModuleWorld} {s : AuditShard} (hsW : ∀ m ∈ s.modules, m ∈ W.modules)
    (hC : ShardLocalClosure W s) {d : RConstInfo} (h : Reach s.env (s.roots W) d) :
    Reach W.monoEnv W.roots d := by
  induction h with
  | root hc _ =>
    unfold AuditShard.roots at hc
    rw [List.mem_filter, List.mem_flatMap] at hc
    obtain ⟨⟨m, hm, hcm⟩, hClaim⟩ := hc
    have hMono : _ ∈ W.monoEnv := ModuleWorld.mem_monoEnv.mpr ⟨m, hsW m hm, hcm⟩
    exact .root (List.mem_filter.mpr ⟨hMono, hClaim⟩) hMono
  | step _ hRef hd ih => exact .step ih hRef (hC.2.1 _ hd)

theorem monoReach_shard {W : ModuleWorld} {shards : List AuditShard}
    (hP : OrphanFreePartition W shards) (hC : ∀ s ∈ shards, ShardLocalClosure W s)
    (hR : CrossShardReconciled shards) {d : RConstInfo} (h : Reach W.monoEnv W.roots d) :
    ∃ s ∈ shards, Reach s.env (s.roots W) d := by
  induction h with
  | @root c hc _ =>
    unfold ModuleWorld.roots at hc
    rw [List.mem_filter] at hc
    obtain ⟨hMono, hClaim⟩ := hc
    obtain ⟨m, hm, hcm⟩ := ModuleWorld.mem_monoEnv.mp hMono
    obtain ⟨s, hs, hms⟩ := hP.1 m hm
    have hRoot : c ∈ s.roots W :=
      List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨m, hms, hcm⟩, hClaim⟩
    exact ⟨s, hs, .root hRoot ((hC s hs).1 m hms c hcm)⟩
  | @step c d' _ hRef hd ih =>
    obtain ⟨s, hs, hReach⟩ := ih
    obtain ⟨d'', hd'', hName⟩ := (hC s hs).2.2 c hReach.mem_env d' hd hRef
    obtain ⟨s₂, hs₂, hd₂⟩ := mem_some_shard_env hP hC hd
    have hEq : d'' = d' :=
      (strictConstCompat_iff_eq _ _).mp (hR s hs s₂ hs₂ d'' hd'' d' hd₂ hName)
    subst hEq
    exact ⟨s, hs, .step hReach (hName ▸ hRef) hd''⟩

/-- Sharded-audit soundness: exact axiom-union equality with the monolithic audit and
    exact violation parity. -/
structure ShardAxiomUnionSound (W : ModuleWorld) (shards : List AuditShard) : Prop where
  axiom_union : ∀ a, monoAxioms W a ↔ ∃ s ∈ shards, shardAxioms W s a
  violation_parity : ∀ n, MonoConflict W n ↔ ShardedConflict shards n

/-- **Sharded audit soundness.** An orphan-free partition into shard-locally closed
    shards, reconciled across shards by `strictConstCompat`, has exactly the monolithic
    transitive axiom union and exactly the monolithic violations. -/
theorem shardAxiomUnion_sound {W : ModuleWorld} {shards : List AuditShard}
    (hP : OrphanFreePartition W shards) (hC : ∀ s ∈ shards, ShardLocalClosure W s)
    (hR : CrossShardReconciled shards) : ShardAxiomUnionSound W shards := by
  refine ⟨fun a => ⟨?_, ?_⟩, violation_parity hP hC⟩
  · rintro ⟨d, hReach, hAx, hName⟩
    obtain ⟨s, hs, hS⟩ := monoReach_shard hP hC hR hReach
    exact ⟨s, hs, d, hS, hAx, hName⟩
  · rintro ⟨s, hs, d, hReach, hAx, hName⟩
    exact ⟨d, shardReach_mono (hP.2 s hs) (hC s hs) hReach, hAx, hName⟩

/-- Whenever the sharded audit reports no conflict, axiom unions agree exactly; and the
    sharded audit reports a conflict exactly when the monolithic audit does. -/
theorem shardedAudit_exact {W : ModuleWorld} {shards : List AuditShard}
    (hP : OrphanFreePartition W shards) (hC : ∀ s ∈ shards, ShardLocalClosure W s) :
    (∀ n, MonoConflict W n ↔ ShardedConflict shards n) ∧
      ((∀ n, ¬ ShardedConflict shards n) →
        ∀ a, monoAxioms W a ↔ ∃ s ∈ shards, shardAxioms W s a) :=
  ⟨violation_parity hP hC, fun hNo =>
    (shardAxiomUnion_sound hP hC ((crossShardReconciled_iff_no_conflict shards).mpr hNo)).axiom_union⟩

/-! ### 3.1 Counterexamples: naive reconciliation, orphans, and independent shards -/

/-- Claim `t` (name `10`) refers to `n` (name `7`). Module `0` defines `n` as a
    definition; module `1` declares `n` as an axiom. -/
def ceClaim : RConstInfo := .thmInfo 10 0 (.const 7) (.const 7)
def ceDefn : RConstInfo := .defnInfo 7 0 (.const 1) (.const 2)
def ceAxiom : RConstInfo := .axiomInfo 7 0 (.const 1)

def ceWorld : ModuleWorld :=
  { modules := [0, 1],
    declsOf := fun m => if m = 0 then [ceClaim, ceDefn] else if m = 1 then [ceAxiom] else [] }

def ceShardA : AuditShard := { modules := [0], env := [ceClaim, ceDefn] }
def ceShardB : AuditShard := { modules := [1], env := [ceAxiom] }
def ceShards : List AuditShard := [ceShardA, ceShardB]

/-- Naive reconciliation: same-name constants across shards are `naiveCompat`. -/
def NaiveReconciled (shards : List AuditShard) : Prop :=
  ∀ s₁ ∈ shards, ∀ s₂ ∈ shards, ∀ d₁ ∈ s₁.env, ∀ d₂ ∈ s₂.env,
    d₁.name = d₂.name → naiveCompat d₁ d₂ = true

instance (shards : List AuditShard) : Decidable (NaiveReconciled shards) :=
  inferInstanceAs (Decidable (∀ s₁ ∈ shards, ∀ s₂ ∈ shards, ∀ d₁ ∈ s₁.env, ∀ d₂ ∈ s₂.env,
    d₁.name = d₂.name → naiveCompat d₁ d₂ = true))

theorem ceWorld_monoAxiom : monoAxioms ceWorld 7 := by
  refine ⟨ceAxiom, ?_, rfl, rfl⟩
  have hClaim : Reach ceWorld.monoEnv ceWorld.roots ceClaim := .root (by decide) (by decide)
  exact .step hClaim (by decide) (by decide)

theorem ceShards_no_shardAxiom : ¬ ∃ s ∈ ceShards, shardAxioms ceWorld s 7 := by
  rintro ⟨s, hs, d, hReach, hAx, _⟩
  simp only [ceShards, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · have hd := hReach.mem_env
    simp only [ceShardA, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> exact absurd hAx (by decide)
  · have hNil : AuditShard.roots ceWorld ceShardB = [] := by decide
    rw [hNil] at hReach
    exact hReach.false_of_nil_roots

/-- **Naive reconciliation breaks axiom-union parity.** The partition is orphan-free,
    both shards are locally closed, and naive reconciliation passes, yet the monolithic
    audit reaches axiom `7` while no shard does. -/
theorem naiveReconciliation_breaks_axiom_union :
    OrphanFreePartition ceWorld ceShards ∧ (∀ s ∈ ceShards, ShardLocalClosure ceWorld s) ∧
      NaiveReconciled ceShards ∧ ¬ CrossShardReconciled ceShards ∧
      monoAxioms ceWorld 7 ∧ ¬ ∃ s ∈ ceShards, shardAxioms ceWorld s 7 := by
  refine ⟨⟨by decide, by decide⟩, ?_, by decide, ?_, ceWorld_monoAxiom, ceShards_no_shardAxiom⟩
  · intro s hs
    simp only [ceShards, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨by decide, by decide, by decide⟩
    · exact ⟨by decide, by decide, by decide⟩
  · intro h
    have := h ceShardA (by simp [ceShards]) ceShardB (by simp [ceShards]) ceDefn (by decide)
      ceAxiom (by decide) rfl
    cases this

/-- **Independent shards miss cross-shard conflicts**: the monolithic audit reports the
    axiom/definition conflict on `7`, no shard sees it alone, and the reconciler does. -/
theorem independentShards_miss_conflict :
    MonoConflict ceWorld 7 ∧ ¬ ShardLocalConflict ceShards 7 ∧ ShardedConflict ceShards 7 := by
  refine ⟨⟨ceDefn, by decide, ceAxiom, by decide, rfl, rfl, by decide⟩, ?_,
    ⟨ceShardA, by simp [ceShards], ceShardB, by simp [ceShards], ceDefn, by decide, ceAxiom,
      by decide, rfl, rfl, by decide⟩⟩
  rintro ⟨s, hs, d₁, hd₁, d₂, hd₂, hn₁, hn₂, hc⟩
  simp only [ceShards, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · simp only [ceShardA, List.mem_cons, List.not_mem_nil, or_false] at hd₁ hd₂
    rcases hd₁ with rfl | rfl <;> rcases hd₂ with rfl | rfl <;>
      first | exact absurd hn₁ (by decide) | exact absurd hn₂ (by decide) |
        exact absurd hc (by decide)
  · simp only [ceShardB, List.mem_cons, List.not_mem_nil, or_false] at hd₁ hd₂
    subst hd₁
    subst hd₂
    cases hc

/-- **Orphan modules break axiom-union parity**: a module owned by no shard hides its
    claim's axiom from the sharded audit. -/
theorem orphanModule_breaks_axiom_union :
    let W : ModuleWorld := { modules := [0], declsOf := fun _ => [ceClaim, ceAxiom] }
    ¬ OrphanFreePartition W [] ∧ monoAxioms W 7 ∧ ¬ ∃ s ∈ ([] : List AuditShard), shardAxioms W s 7 := by
  intro W
  refine ⟨fun h => ?_, ?_, fun ⟨_, hs, _⟩ => absurd hs List.not_mem_nil⟩
  · obtain ⟨_, hs, _⟩ := h.1 0 (by decide)
    exact absurd hs List.not_mem_nil
  · refine ⟨ceAxiom, ?_, rfl, rfl⟩
    have hClaim : Reach W.monoEnv W.roots ceClaim := .root (by decide) (by decide)
    exact .step hClaim (by decide) (by decide)

/-- Fingerprint reconciliation: same-name constants across shards are `hashCompat`. -/
def HashReconciled (shards : List AuditShard) : Prop :=
  ∀ s₁ ∈ shards, ∀ s₂ ∈ shards, ∀ d₁ ∈ s₁.env, ∀ d₂ ∈ s₂.env,
    d₁.name = d₂.name → hashCompat d₁ d₂ = true

instance (shards : List AuditShard) : Decidable (HashReconciled shards) :=
  inferInstanceAs (Decidable (∀ s₁ ∈ shards, ∀ s₂ ∈ shards, ∀ d₁ ∈ s₁.env, ∀ d₂ ∈ s₂.env,
    d₁.name = d₂.name → hashCompat d₁ d₂ = true))

/-- Two definitions with colliding `hash64` values (`7 * 31 + 9 = 226 = 17 * 13 + 5`):
    `hcePureDefn` is axiom-free while `hceAxiomDefn` references axiom `17`. -/
def hcePureDefn : RConstInfo := .defnInfo 7 0 (.const 1) (.natLit 7)
def hceAxiomDefn : RConstInfo := .defnInfo 7 0 (.const 1) (.const 17)
def hceHiddenAxiom : RConstInfo := .axiomInfo 17 0 (.sort 0)

def hceWorld : ModuleWorld :=
  { modules := [0, 1],
    declsOf := fun m =>
      if m = 0 then [ceClaim, hcePureDefn]
      else if m = 1 then [hceAxiomDefn, hceHiddenAxiom]
      else [] }

def hceShardA : AuditShard := { modules := [0], env := [ceClaim, hcePureDefn] }
def hceShardB : AuditShard := { modules := [1], env := [hceAxiomDefn, hceHiddenAxiom] }
def hceShards : List AuditShard := [hceShardA, hceShardB]

theorem hceWorld_monoAxiom : monoAxioms hceWorld 17 := by
  refine ⟨hceHiddenAxiom, ?_, rfl, rfl⟩
  have hClaim : Reach hceWorld.monoEnv hceWorld.roots ceClaim := .root (by decide) (by decide)
  have hDefn : Reach hceWorld.monoEnv hceWorld.roots hceAxiomDefn :=
    .step hClaim (by decide) (by decide)
  exact .step hDefn (by decide) (by decide)

theorem hceShards_no_shardAxiom : ¬ ∃ s ∈ hceShards, shardAxioms hceWorld s 17 := by
  rintro ⟨s, hs, d, hReach, hAx, _⟩
  simp only [hceShards, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · have hd := hReach.mem_env
    simp only [hceShardA, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> exact absurd hAx (by decide)
  · have hNil : AuditShard.roots hceWorld hceShardB = [] := by decide
    rw [hNil] at hReach
    exact hReach.false_of_nil_roots

/-- **Hash-based reconciliation breaks axiom-union parity.** Two `.defnInfo` entries of
    the same name collide under `hash64` (`natLit 7` vs `const 17`); `HashReconciled`
    accepts them, yet the monolithic audit reaches axiom `17` while no shard does. -/
theorem hashReconciliation_breaks_axiom_union :
    OrphanFreePartition hceWorld hceShards ∧ (∀ s ∈ hceShards, ShardLocalClosure hceWorld s) ∧
      HashReconciled hceShards ∧ ¬ CrossShardReconciled hceShards ∧
      monoAxioms hceWorld 17 ∧ ¬ ∃ s ∈ hceShards, shardAxioms hceWorld s 17 := by
  refine ⟨⟨by decide, by decide⟩, ?_, by decide, ?_, hceWorld_monoAxiom, hceShards_no_shardAxiom⟩
  · intro s hs
    simp only [hceShards, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨by decide, by decide, by decide⟩
    · exact ⟨by decide, by decide, by decide⟩
  · intro h
    have := h hceShardA (by simp [hceShards]) hceShardB (by simp [hceShards]) hcePureDefn
      (by decide) hceAxiomDefn (by decide) rfl
    cases this

/-! ## 4. Pillar 3 — Peer-Verifier Spec-Boundary Guards -/

/-! ### 4.1 Guard 3 — unsatisfiable extern `ensures` (`creusot#2388`) -/

/-- How a contract enters the verifier's trusted base. -/
inductive ContractTrust : Type where
  | verified
  | externSpec
  | externalSpec
  | trusted
  | assumed
  | externalBody
  deriving DecidableEq, Repr

/-- A function contract with a declared divergence flag. -/
structure ExternContract (Arg Ret : Type) where
  trust : ContractTrust
  requires : Arg → Prop
  ensures : Arg → Ret → Prop
  isDiverging : Bool

/-- The verifier's call rule for an assumed contract and implementation `impl`
    (`none` = diverges): every value a reachable call returns satisfies `ensures`. -/
def ContractHonest {Arg Ret : Type} (c : ExternContract Arg Ret) (impl : Arg → Option Ret) :
    Prop :=
  ∀ a r, c.requires a → impl a = some r → c.ensures a r

/-- **Collapse (`creusot#2388`)**: an assumed contract whose `ensures` is unsatisfiable
    at a reachable input derives `False` against any implementation that returns there. -/
theorem externEnsuresFalse_soundness_collapse {Arg Ret : Type} (c : ExternContract Arg Ret)
    (impl : Arg → Option Ret) (a : Arg) (r : Ret) (hReach : c.requires a)
    (hUnsat : ∀ r', ¬ c.ensures a r') (hRet : impl a = some r)
    (hRule : ContractHonest c impl) : False :=
  hUnsat r (hRule a r hReach hRet)

/-- Concrete instance: a volatile-read stub `Unit → Nat` with `ensures(false)`. Every
    returning implementation refutes the trusted call rule. -/
theorem volatileRead_collapse :
    let c : ExternContract Unit Nat :=
      { trust := .externSpec, requires := fun _ => True, ensures := fun _ _ => False,
        isDiverging := false }
    ∀ r : Nat, ¬ ContractHonest c (fun _ => some r) := by
  intro c r hRule
  exact hRule () r trivial rfl

/-- `ExternalEnsuresFalseGuard`: a divergence claim requires an uninhabited return
    type, and an assumed contract with an unsatisfiable `ensures` at a reachable input
    must be a genuine divergence claim. -/
structure ExternalEnsuresFalseGuard {Arg Ret : Type} (c : ExternContract Arg Ret) : Prop where
  diverging_uninhabited : c.isDiverging = true → Ret → False
  unsat_ensures_diverges : c.trust ≠ .verified →
    ∀ a, c.requires a → (∀ r, ¬ c.ensures a r) → c.isDiverging = true

/-- **Restoration**: under the guard, no implementation can return at an input where
    the assumed `ensures` is unsatisfiable, so the verifier's `False` after the call is
    never reached, and the trusted call rule holds for every implementation there. -/
theorem externalEnsuresFalseGuard_sound {Arg Ret : Type} {c : ExternContract Arg Ret}
    (hG : ExternalEnsuresFalseGuard c) (hTrust : c.trust ≠ .verified) (impl : Arg → Option Ret)
    (a : Arg) (hReach : c.requires a) (hUnsat : ∀ r, ¬ c.ensures a r) :
    impl a = none ∧ ∀ r, impl a = some r → c.ensures a r := by
  have hDiv := hG.unsat_ensures_diverges hTrust a hReach hUnsat
  have hNone : impl a = none := by
    cases hImpl : impl a with
    | none => rfl
    | some r => exact (hG.diverging_uninhabited hDiv r).elim
  refine ⟨hNone, fun r hr => ?_⟩
  rw [hNone] at hr
  cases hr

/-- The guard admits a genuinely uninhabited (`!` / `Empty`) diverging contract. -/
theorem externalEnsuresFalseGuard_of_uninhabited {Arg Ret : Type} (c : ExternContract Arg Ret)
    (hEmpty : Ret → False) (hDiv : c.isDiverging = true) : ExternalEnsuresFalseGuard c :=
  ⟨fun _ => hEmpty, fun _ _ _ _ => hDiv⟩

/-- The guard admits an unconditional `requires(false)` mitigation (no reachable input). -/
theorem externalEnsuresFalseGuard_of_requires_false {Arg Ret : Type} (c : ExternContract Arg Ret)
    (hNoReach : ∀ a, ¬ c.requires a) (hDiv : c.isDiverging = false) :
    ExternalEnsuresFalseGuard c :=
  ⟨fun h => absurd (hDiv ▸ h) (by decide), fun _ a ha _ => absurd ha (hNoReach a)⟩

/-- A lying divergence claim on an inhabited return type is rejected. -/
theorem lyingDiverging_rejected {Arg Ret : Type} (c : ExternContract Arg Ret)
    (hDiv : c.isDiverging = true) (r : Ret) : ¬ ExternalEnsuresFalseGuard c :=
  fun hG => hG.diverging_uninhabited hDiv r

/-- A returning extern contract with `ensures(false)` at a reachable input is rejected. -/
theorem returningEnsuresFalse_rejected {Arg Ret : Type} (c : ExternContract Arg Ret)
    (hTrust : c.trust ≠ .verified) (hDiv : c.isDiverging = false) (a : Arg)
    (hReach : c.requires a) (hUnsat : ∀ r, ¬ c.ensures a r) : ¬ ExternalEnsuresFalseGuard c := by
  intro hG
  have := hG.unsat_ensures_diverges hTrust a hReach hUnsat
  rw [hDiv] at this
  cases this

/-! ### 4.2 Guard 4 — `FnDef` ghost-token coercion (`creusot#2389`) -/

/-- Contexts whose body may run more than once. -/
inductive RepeatKind : Type where
  | loopKw
  | whileKw
  | forKw
  | closure
  | asyncBlock
  | reentrantMain
  deriving DecidableEq, Repr

/-- `TokProg`: a linear ghost-token program. -/
inductive TokStmt : Type where
  | skip
  /-- A direct `Tokens::new()` call. -/
  | mintCall
  /-- `let x = Tokens::new;`: a non-call `FnDef` value coercion. -/
  | bindFnDef (x : Nat)
  /-- `x()`: a call through a variable. -/
  | callVar (x : Nat)
  | seq (a b : TokStmt)
  /-- A body that runs `iterations` times (loop, closure, async block, re-entrant main). -/
  | repeatCtx (kind : RepeatKind) (iterations : Nat) (body : TokStmt)
  deriving DecidableEq, Repr

namespace TokStmt

def boundFnDefs : TokStmt → List Nat
  | .bindFnDef x => [x]
  | .seq a b => boundFnDefs a ++ boundFnDefs b
  | .repeatCtx _ _ b => boundFnDefs b
  | _ => []

/-- Number of tokens minted when the variables in `fns` hold the constructor. -/
def mintsWith (fns : List Nat) : TokStmt → Nat
  | .skip => 0
  | .mintCall => 1
  | .bindFnDef _ => 0
  | .callVar x => if x ∈ fns then 1 else 0
  | .seq a b => mintsWith fns a + mintsWith fns b
  | .repeatCtx _ n b => n * mintsWith fns b

/-- Number of tokens a program mints. -/
def mints (p : TokStmt) : Nat := mintsWith p.boundFnDefs p

/-- Fresh token identifiers minted by a program. -/
def mintedTokens (p : TokStmt) : List Nat := List.range p.mints

/-- No `FnDef` value coercion and no call through a variable. -/
def noFnDefCoercion : TokStmt → Bool
  | .bindFnDef _ => false
  | .callVar _ => false
  | .seq a b => noFnDefCoercion a && noFnDefCoercion b
  | .repeatCtx _ _ b => noFnDefCoercion b
  | _ => true

/-- Syntactic constructor call sites. -/
def mintSites : TokStmt → Nat
  | .mintCall => 1
  | .callVar _ => 1
  | .seq a b => mintSites a + mintSites b
  | .repeatCtx _ _ b => mintSites b
  | _ => 0

/-- No constructor call site inside a repeating context. -/
def mintFreeRepeats : TokStmt → Bool
  | .seq a b => mintFreeRepeats a && mintFreeRepeats b
  | .repeatCtx _ _ b => mintSites b == 0 && mintFreeRepeats b
  | _ => true

end TokStmt

/-- The verifier's linear-token assumption: every minted token is the unique authority. -/
def UniqueAuthority (toks : List Nat) : Prop := ∀ t ∈ toks, ∀ t' ∈ toks, t = t'

/-- Two minted tokens contradict unique authority. -/
theorem not_uniqueAuthority_of_two_le {p : TokStmt} (h : 2 ≤ p.mints) :
    ¬ UniqueAuthority p.mintedTokens := by
  intro hU
  have h0 : 0 ∈ p.mintedTokens := List.mem_range.mpr (by omega)
  have h1 : 1 ∈ p.mintedTokens := List.mem_range.mpr (by omega)
  exact absurd (hU 0 h0 1 h1) (by decide)

/-- `let mk = Tokens::new; (mk(), mk())`. -/
def fnDefDupProg : TokStmt := .seq (.bindFnDef 0) (.seq (.callVar 0) (.callVar 0))

/-- **Collapse (`creusot#2389`)**: coercing the constructor to a `FnDef` value mints two
    unique-authority tokens, deriving `False`. -/
theorem fnDefCoercion_soundness_collapse (hU : UniqueAuthority fnDefDupProg.mintedTokens) : False :=
  not_uniqueAuthority_of_two_le (by decide) hU

/-- Minting inside a loop or a re-entered `main` also collapses. -/
theorem repeatMint_soundness_collapse (k : RepeatKind) :
    ¬ UniqueAuthority (TokStmt.repeatCtx k 2 .mintCall).mintedTokens :=
  not_uniqueAuthority_of_two_le (by cases k <;> decide)

/-- `FnDefGhostTokenGuard`: no non-call `FnDef` coercion, no call site in a repeating
    context, and at most one direct call site. -/
structure FnDefGhostTokenGuard (p : TokStmt) : Prop where
  no_coercion : p.noFnDefCoercion = true
  no_repeat_mint : p.mintFreeRepeats = true
  single_site : p.mintSites ≤ 1

theorem mintsWith_le_mintSites (fns : List Nat) :
    ∀ p : TokStmt, p.noFnDefCoercion = true → p.mintFreeRepeats = true →
      p.mintsWith fns ≤ p.mintSites
  | .skip, _, _ => Nat.le_refl _
  | .mintCall, _, _ => Nat.le_refl _
  | .bindFnDef _, h, _ => by cases h
  | .callVar _, h, _ => by cases h
  | .seq a b, hNo, hRep => by
    simp only [TokStmt.noFnDefCoercion, Bool.and_eq_true] at hNo
    simp only [TokStmt.mintFreeRepeats, Bool.and_eq_true] at hRep
    have ha := mintsWith_le_mintSites fns a hNo.1 hRep.1
    have hb := mintsWith_le_mintSites fns b hNo.2 hRep.2
    simp only [TokStmt.mintsWith, TokStmt.mintSites]
    omega
  | .repeatCtx _ n b, hNo, hRep => by
    simp only [TokStmt.noFnDefCoercion] at hNo
    simp only [TokStmt.mintFreeRepeats, Bool.and_eq_true, beq_iff_eq] at hRep
    have hb := mintsWith_le_mintSites fns b hNo hRep.2
    have hZero : b.mintsWith fns = 0 := by omega
    simp only [TokStmt.mintsWith, hZero, Nat.mul_zero]
    exact Nat.zero_le _

/-- **Restoration**: the guard preserves linear token uniqueness. -/
theorem fnDefGhostTokenGuard_unique_authority {p : TokStmt} (h : FnDefGhostTokenGuard p) :
    UniqueAuthority p.mintedTokens := by
  have hLe : p.mints ≤ 1 :=
    Nat.le_trans (mintsWith_le_mintSites _ p h.no_coercion h.no_repeat_mint) h.single_site
  intro t ht t' ht'
  have := List.mem_range.mp ht
  have := List.mem_range.mp ht'
  omega

/-- Flow-sensitive stateful execution of `TokStmt`: threads bound `FnDef` variables and
    the minted-token count in execution order. -/
def evalTokLoop (step : List Nat × Nat → List Nat × Nat) : Nat → List Nat × Nat → List Nat × Nat
  | 0, st => st
  | n + 1, st => evalTokLoop step n (step st)

def evalTok : TokStmt → List Nat × Nat → List Nat × Nat
  | .skip, st => st
  | .mintCall, (fns, c) => (fns, c + 1)
  | .bindFnDef x, (fns, c) => (x :: fns, c)
  | .callVar x, (fns, c) => (fns, if x ∈ fns then c + 1 else c)
  | .seq a b, st => evalTok b (evalTok a st)
  | .repeatCtx _ n b, st => evalTokLoop (evalTok b) n st

theorem evalTokLoop_snd_eq {step : List Nat × Nat → List Nat × Nat}
    (hStep : ∀ st, (step st).2 = st.2) :
    ∀ n st, (evalTokLoop step n st).2 = st.2
  | 0, _ => rfl
  | n + 1, st => by
    simp only [evalTokLoop]
    rw [evalTokLoop_snd_eq hStep n (step st), hStep st]

theorem evalTokLoop_snd_ge {step : List Nat × Nat → List Nat × Nat}
    (hStep : ∀ st, st.2 ≤ (step st).2) :
    ∀ n st, st.2 ≤ (evalTokLoop step n st).2
  | 0, _ => Nat.le_refl _
  | n + 1, st => Nat.le_trans (hStep st) (evalTokLoop_snd_ge hStep n (step st))

theorem evalTok_snd_ge : ∀ (p : TokStmt) (st : List Nat × Nat), st.2 ≤ (evalTok p st).2
  | .skip, _ => Nat.le_refl _
  | .mintCall, _ => Nat.le_succ _
  | .bindFnDef _, _ => Nat.le_refl _
  | .callVar x, (fns, c) => by
    simp only [evalTok]
    split <;> omega
  | .seq a b, st => Nat.le_trans (evalTok_snd_ge a st) (evalTok_snd_ge b (evalTok a st))
  | .repeatCtx _ n b, st => evalTokLoop_snd_ge (evalTok_snd_ge b) n st

theorem evalTok_snd_le_mintSites :
    ∀ (p : TokStmt) (st : List Nat × Nat),
      p.noFnDefCoercion = true → p.mintFreeRepeats = true →
      (evalTok p st).2 ≤ st.2 + p.mintSites
  | .skip, _, _, _ => Nat.le_refl _
  | .mintCall, _, _, _ => Nat.le_refl _
  | .bindFnDef _, _, h, _ => by cases h
  | .callVar _, _, h, _ => by cases h
  | .seq a b, st, hNo, hRep => by
    simp only [TokStmt.noFnDefCoercion, Bool.and_eq_true] at hNo
    simp only [TokStmt.mintFreeRepeats, Bool.and_eq_true] at hRep
    have ha := evalTok_snd_le_mintSites a st hNo.1 hRep.1
    have hb := evalTok_snd_le_mintSites b (evalTok a st) hNo.2 hRep.2
    simp only [evalTok, TokStmt.mintSites]
    omega
  | .repeatCtx _ n b, st, hNo, hRep => by
    simp only [TokStmt.noFnDefCoercion] at hNo
    simp only [TokStmt.mintFreeRepeats, Bool.and_eq_true, beq_iff_eq] at hRep
    have hStep : ∀ s, (evalTok b s).2 = s.2 := by
      intro s
      have hLe := evalTok_snd_le_mintSites b s hNo hRep.2
      have hGe := evalTok_snd_ge b s
      omega
    simp only [evalTok, TokStmt.mintSites, hRep.1, Nat.add_zero]
    rw [evalTokLoop_snd_eq hStep n st]
    exact Nat.le_refl _

/-- **Flow-sensitive restoration**: under `FnDefGhostTokenGuard`, stateful execution
    from an empty environment preserves linear token uniqueness. -/
theorem evalTok_unique_authority {p : TokStmt} (h : FnDefGhostTokenGuard p) :
    UniqueAuthority (List.range (evalTok p ([], 0)).2) := by
  have hLe := evalTok_snd_le_mintSites p ([], 0) h.no_coercion h.no_repeat_mint
  have hOne : (evalTok p ([], 0)).2 ≤ 1 := by
    have := h.single_site
    omega
  intro t ht t' ht'
  have := List.mem_range.mp ht
  have := List.mem_range.mp ht'
  omega

/-- The guard admits the single direct call and rejects each bypass. -/
theorem fnDefGhostTokenGuard_verdicts :
    FnDefGhostTokenGuard .mintCall ∧ ¬ FnDefGhostTokenGuard fnDefDupProg ∧
      (∀ k, ¬ FnDefGhostTokenGuard (.repeatCtx k 1 .mintCall)) ∧
      ¬ FnDefGhostTokenGuard (.seq .mintCall .mintCall) := by
  refine ⟨⟨rfl, rfl, by decide⟩, fun h => absurd h.no_coercion (by decide), ?_,
    fun h => absurd h.single_site (by decide)⟩
  intro k h
  exact absurd h.no_repeat_mint (by cases k <;> decide)

/-! ### 4.3 Guard 5 — external-type `Drop` omission (`verus#3514`) -/

/-- The declared shape of an `external_type_specification`. -/
structure ExternalTypeDropSpec where
  externalTypeSpecification : Bool
  externalBody : Bool
  hasDropImpl : Bool
  opaqueForeignField : Bool
  modelsDrop : Bool
  noDropGlue : Bool
  deriving DecidableEq, Repr

/-- A `Drop` effect may exist. -/
def ExternalTypeDropSpec.dropMayExist (s : ExternalTypeDropSpec) : Bool :=
  s.hasDropImpl || (s.opaqueForeignField && !s.noDropGlue)

/-- Facts relating the declarations to the real type's `Drop` behaviour `actualDrop`:
    drop glue comes only from a `Drop` impl or a field, a `Drop` impl always runs, and a
    `no_drop_glue` declaration is trusted. -/
structure DropTruth (s : ExternalTypeDropSpec) (actualDrop : Bool) : Prop where
  drop_source : actualDrop = true → s.hasDropImpl = true ∨ s.opaqueForeignField = true
  impl_runs : s.hasDropImpl = true → actualDrop = true
  no_glue_trusted : s.noDropGlue = true → actualDrop = false

/-- Releasing one live resource handle. -/
def dropEffect (live : Nat) : Nat := live - 1

/-- Real scope exit. -/
def realScopeExit (actualDrop : Bool) (live : Nat) : Nat :=
  if actualDrop then dropEffect live else live

/-- The verifier's scope exit: an `external_body` type is opaque (its drop is omitted);
    otherwise a `models_drop` specification reproduces the drop and an unmodeled one
    omits it. -/
def verifierScopeExit (s : ExternalTypeDropSpec) (actualDrop : Bool) (live : Nat) : Nat :=
  if s.externalBody then live else if s.modelsDrop then realScopeExit actualDrop live else live

/-- The ghost resource invariant: the verifier's view equals reality. -/
def ResourceInv (ghost real : Nat) : Prop := ghost = real

/-- `ExternalTypeDropGuard`. -/
structure ExternalTypeDropGuard (s : ExternalTypeDropSpec) : Prop where
  no_external_body : s.dropMayExist = true → s.externalBody = false
  drop_impl_modeled : s.hasDropImpl = true → s.modelsDrop = true ∧ s.noDropGlue = false
  opaque_field_covered : s.opaqueForeignField = true → s.modelsDrop = true ∨ s.noDropGlue = true

/-- **Restoration**: under the guard, the ghost invariant survives scope exit. -/
theorem externalTypeDropGuard_preserves_inv {s : ExternalTypeDropSpec} {actualDrop : Bool}
    (hG : ExternalTypeDropGuard s) (hT : DropTruth s actualDrop) {ghost real : Nat}
    (hInv : ResourceInv ghost real) :
    ResourceInv (verifierScopeExit s actualDrop ghost) (realScopeExit actualDrop real) := by
  unfold ResourceInv at hInv ⊢
  subst hInv
  have hNoDrop : (s.hasDropImpl = false ∧ (s.opaqueForeignField = true → s.noDropGlue = true)) →
      actualDrop = false := by
    rintro ⟨hImpl, hOpaque⟩
    cases hA : actualDrop
    · rfl
    · rcases hT.drop_source hA with h | h
      · rw [hImpl] at h
        cases h
      · exact absurd (hT.no_glue_trusted (hOpaque h)) (by rw [hA]; decide)
  unfold verifierScopeExit
  cases hBody : s.externalBody
  · cases hModels : s.modelsDrop
    · have hImpl : s.hasDropImpl = false := by
        cases h : s.hasDropImpl
        · rfl
        · rw [(hG.drop_impl_modeled h).1] at hModels
          cases hModels
      have hOpaque : s.opaqueForeignField = true → s.noDropGlue = true := by
        intro h
        rcases hG.opaque_field_covered h with h' | h'
        · rw [h'] at hModels
          cases hModels
        · exact h'
      rw [hNoDrop ⟨hImpl, hOpaque⟩]
      rfl
    · rfl
  · have hMay : s.dropMayExist = false := by
      cases h : s.dropMayExist
      · rfl
      · rw [hG.no_external_body h] at hBody
        cases hBody
    unfold ExternalTypeDropSpec.dropMayExist at hMay
    simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, Bool.not_eq_false'] at hMay
    have hOpaque : s.opaqueForeignField = true → s.noDropGlue = true := by
      intro h
      rcases hMay.2 with h' | h'
      · rw [h] at h'
        cases h'
      · exact h'
    rw [hNoDrop ⟨hMay.1, hOpaque⟩]
    rfl

/-- **Collapse (`verus#3514`)**: `external_body` over a type with an active `Drop`
    omits the drop and breaks the resource invariant at scope exit. -/
theorem externalBodyDrop_soundness_collapse {s : ExternalTypeDropSpec} {actualDrop : Bool}
    (hT : DropTruth s actualDrop) (hBody : s.externalBody = true) (hImpl : s.hasDropImpl = true)
    {live : Nat} (hLive : 0 < live) :
    ¬ ResourceInv (verifierScopeExit s actualDrop live) (realScopeExit actualDrop live) := by
  unfold ResourceInv verifierScopeExit realScopeExit dropEffect
  rw [hBody, hT.impl_runs hImpl]
  simp only [ite_true]
  omega

/-- **Collapse**: an unmodeled opaque foreign field with real drop glue breaks the
    invariant even without `external_body`. -/
theorem unmodeledOpaqueDrop_soundness_collapse {s : ExternalTypeDropSpec}
    (hBody : s.externalBody = false) (hModels : s.modelsDrop = false) {live : Nat}
    (hLive : 0 < live) :
    ¬ ResourceInv (verifierScopeExit s true live) (realScopeExit true live) := by
  unfold ResourceInv verifierScopeExit realScopeExit dropEffect
  rw [hBody, hModels]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  omega

/-- `external_body` is rejected whenever a `Drop` impl exists, even with `models_drop`. -/
theorem externalBody_rejected_even_with_modelsDrop {s : ExternalTypeDropSpec}
    (hBody : s.externalBody = true) (hImpl : s.hasDropImpl = true) : ¬ ExternalTypeDropGuard s := by
  intro hG
  have := hG.no_external_body (by simp [ExternalTypeDropSpec.dropMayExist, hImpl])
  rw [hBody] at this
  cases this

/-- `external_body` is also rejected on an opaque foreign field without `no_drop_glue`,
    even when `models_drop` is claimed. -/
theorem externalBody_rejected_for_opaque_field_even_with_modelsDrop {s : ExternalTypeDropSpec}
    (hBody : s.externalBody = true) (hOpaque : s.opaqueForeignField = true)
    (hGlue : s.noDropGlue = false) : ¬ ExternalTypeDropGuard s := by
  intro hG
  have := hG.no_external_body (by simp [ExternalTypeDropSpec.dropMayExist, hOpaque, hGlue])
  rw [hBody] at this
  cases this

/-- An opaque foreign field without `models_drop` or `no_drop_glue` is rejected. -/
theorem opaqueField_rejected_without_mitigation {s : ExternalTypeDropSpec}
    (hOpaque : s.opaqueForeignField = true) (hModels : s.modelsDrop = false)
    (hGlue : s.noDropGlue = false) : ¬ ExternalTypeDropGuard s := by
  intro hG
  rcases hG.opaque_field_covered hOpaque with h | h
  · rw [hModels] at h
    cases h
  · rw [hGlue] at h
    cases h

/-! ### 4.4 Guard 6a — assumption polarity (`Verifrag`) -/

/-- Propositional formula AST over atoms and the assumption atom `assumesHold`. -/
inductive PropFormula : Type where
  | atom (x : Nat)
  | assumesHold
  | tt
  | ff
  | not (p : PropFormula)
  | and (p q : PropFormula)
  | or (p q : PropFormula)
  | imp (p q : PropFormula)
  | iff (p q : PropFormula)
  | ite (c t e : PropFormula)
  /-- A Boolean leaf (`decide`, `==`, a call): its polarity is not tracked. -/
  | boolLeaf (p : PropFormula)
  deriving DecidableEq, Repr

/-- Semantics under an atom valuation `ρ` and assumption truth value `A`. -/
def evalPF (ρ : Nat → Prop) (A : Prop) : PropFormula → Prop
  | .atom x => ρ x
  | .assumesHold => A
  | .tt => True
  | .ff => False
  | .not p => ¬ evalPF ρ A p
  | .and p q => evalPF ρ A p ∧ evalPF ρ A q
  | .or p q => evalPF ρ A p ∨ evalPF ρ A q
  | .imp p q => evalPF ρ A p → evalPF ρ A q
  | .iff p q => (evalPF ρ A p ↔ evalPF ρ A q)
  | .ite c t e => (evalPF ρ A c ∧ evalPF ρ A t) ∨ (¬ evalPF ρ A c ∧ evalPF ρ A e)
  | .boolLeaf p => evalPF ρ A p

/-- Absolute polarity. -/
inductive Polarity : Type where
  | pos
  | neg
  deriving DecidableEq, Repr

def Polarity.flip : Polarity → Polarity
  | .pos => .neg
  | .neg => .pos

/-- The monotonicity relation a polarity induces. -/
def Polarity.Rel : Polarity → Prop → Prop → Prop
  | .pos, P, Q => P → Q
  | .neg, P, Q => Q → P

/-- `occursAt τ σ f`: in `f`, sitting at absolute polarity `σ`, the assumption atom
    occurs at absolute polarity `τ`. `iff`, `if` conditions, and Boolean leaves count
    as both polarities (fail-closed). -/
def occursAt (τ : Polarity) : Polarity → PropFormula → Bool
  | σ, .assumesHold => decide (σ = τ)
  | _, .atom _ => false
  | _, .tt => false
  | _, .ff => false
  | σ, .not p => occursAt τ σ.flip p
  | σ, .and p q => occursAt τ σ p || occursAt τ σ q
  | σ, .or p q => occursAt τ σ p || occursAt τ σ q
  | σ, .imp p q => occursAt τ σ.flip p || occursAt τ σ q
  | σ, .iff p q => occursAt τ σ p || occursAt τ σ.flip p || occursAt τ σ q || occursAt τ σ.flip q
  | σ, .ite c t e => occursAt τ σ c || occursAt τ σ.flip c || occursAt τ σ t || occursAt τ σ e
  | σ, .boolLeaf p => occursAt τ σ p || occursAt τ σ.flip p

theorem Polarity.flip_flip (σ : Polarity) : σ.flip.flip = σ := by cases σ <;> rfl

theorem occursAt_flip (τ σ : Polarity) (f : PropFormula) :
    occursAt τ.flip σ.flip f = occursAt τ σ f := by
  induction f generalizing σ with
  | assumesHold => cases τ <;> cases σ <;> rfl
  | atom _ => rfl
  | tt => rfl
  | ff => rfl
  | not p ih => simp only [occursAt]; exact ih σ.flip
  | and p q ihp ihq => simp only [occursAt, ihp, ihq]
  | or p q ihp ihq => simp only [occursAt, ihp, ihq]
  | imp p q ihp ihq => simp only [occursAt, ihp, ihq]
  | iff p q ihp ihq => simp only [occursAt, ihp, ihq]
  | ite c t e ihc iht ihe => simp only [occursAt, ihc, iht, ihe]
  | boolLeaf p ih => simp only [occursAt, ih]

/-- A formula with no occurrence of the assumption atom is independent of it. -/
theorem evalPF_indep (ρ : Nat → Prop) (A A' : Prop) :
    ∀ (f : PropFormula) (σ : Polarity), occursAt .pos σ f = false → occursAt .neg σ f = false →
      (evalPF ρ A f ↔ evalPF ρ A' f)
  | .assumesHold, σ, h₁, h₂ => by cases σ <;> simp [occursAt] at h₁ h₂
  | .atom _, _, _, _ => Iff.rfl
  | .tt, _, _, _ => Iff.rfl
  | .ff, _, _, _ => Iff.rfl
  | .not p, σ, h₁, h₂ => by
    simp only [occursAt] at h₁ h₂
    simp only [evalPF]
    rw [evalPF_indep ρ A A' p σ.flip h₁ h₂]
  | .and p q, σ, h₁, h₂ => by
    simp only [occursAt, Bool.or_eq_false_iff] at h₁ h₂
    simp only [evalPF]
    rw [evalPF_indep ρ A A' p σ h₁.1 h₂.1, evalPF_indep ρ A A' q σ h₁.2 h₂.2]
  | .or p q, σ, h₁, h₂ => by
    simp only [occursAt, Bool.or_eq_false_iff] at h₁ h₂
    simp only [evalPF]
    rw [evalPF_indep ρ A A' p σ h₁.1 h₂.1, evalPF_indep ρ A A' q σ h₁.2 h₂.2]
  | .imp p q, σ, h₁, h₂ => by
    simp only [occursAt, Bool.or_eq_false_iff] at h₁ h₂
    simp only [evalPF]
    rw [evalPF_indep ρ A A' p σ.flip h₁.1 h₂.1, evalPF_indep ρ A A' q σ h₁.2 h₂.2]
  | .iff p q, σ, h₁, h₂ => by
    simp only [occursAt, Bool.or_eq_false_iff] at h₁ h₂
    simp only [evalPF]
    rw [evalPF_indep ρ A A' p σ h₁.1.1.1 h₂.1.1.1, evalPF_indep ρ A A' q σ h₁.1.2 h₂.1.2]
  | .ite c t e, σ, h₁, h₂ => by
    simp only [occursAt, Bool.or_eq_false_iff] at h₁ h₂
    simp only [evalPF]
    rw [evalPF_indep ρ A A' c σ h₁.1.1.1 h₂.1.1.1, evalPF_indep ρ A A' t σ h₁.1.2 h₂.1.2,
      evalPF_indep ρ A A' e σ h₁.2 h₂.2]
  | .boolLeaf p, σ, h₁, h₂ => by
    simp only [occursAt, Bool.or_eq_false_iff] at h₁ h₂
    simp only [evalPF]
    exact evalPF_indep ρ A A' p σ h₁.1 h₂.1

/-- Polarity soundness: a formula at absolute polarity `σ` with no negative occurrence
    of the assumption atom is `σ`-monotone in the assumption. -/
theorem evalPF_polarity (ρ : Nat → Prop) {A A' : Prop} (hAA : A → A') :
    ∀ (f : PropFormula) (σ : Polarity), occursAt .neg σ f = false →
      σ.Rel (evalPF ρ A f) (evalPF ρ A' f)
  | .assumesHold, σ, h => by
    cases σ
    · exact hAA
    · simp [occursAt] at h
  | .atom _, σ, _ => by cases σ <;> exact id
  | .tt, σ, _ => by cases σ <;> exact id
  | .ff, σ, _ => by cases σ <;> exact id
  | .not p, σ, h => by
    simp only [occursAt] at h
    have ih := evalPF_polarity ρ hAA p σ.flip h
    cases σ <;> simp only [Polarity.flip, Polarity.Rel, evalPF] at ih ⊢ <;>
      exact fun hn hp => hn (ih hp)
  | .and p q, σ, h => by
    simp only [occursAt, Bool.or_eq_false_iff] at h
    have ihp := evalPF_polarity ρ hAA p σ h.1
    have ihq := evalPF_polarity ρ hAA q σ h.2
    cases σ <;> simp only [Polarity.Rel, evalPF] at ihp ihq ⊢ <;>
      exact fun hpq => ⟨ihp hpq.1, ihq hpq.2⟩
  | .or p q, σ, h => by
    simp only [occursAt, Bool.or_eq_false_iff] at h
    have ihp := evalPF_polarity ρ hAA p σ h.1
    have ihq := evalPF_polarity ρ hAA q σ h.2
    cases σ <;> simp only [Polarity.Rel, evalPF] at ihp ihq ⊢ <;>
      exact fun hpq => hpq.elim (fun hp => Or.inl (ihp hp)) (fun hq => Or.inr (ihq hq))
  | .imp p q, σ, h => by
    simp only [occursAt, Bool.or_eq_false_iff] at h
    have ihp := evalPF_polarity ρ hAA p σ.flip h.1
    have ihq := evalPF_polarity ρ hAA q σ h.2
    cases σ <;> simp only [Polarity.flip, Polarity.Rel, evalPF] at ihp ihq ⊢ <;>
      exact fun hpq hp => ihq (hpq (ihp hp))
  | .iff p q, σ, h => by
    simp only [occursAt, Bool.or_eq_false_iff] at h
    have hp₂ : occursAt .pos σ p = false := by
      rw [← occursAt_flip]; exact h.1.1.2
    have hq₂ : occursAt .pos σ q = false := by
      rw [← occursAt_flip]; exact h.2
    have ip := evalPF_indep ρ A A' p σ hp₂ h.1.1.1
    have iq := evalPF_indep ρ A A' q σ hq₂ h.1.2
    cases σ <;> simp only [Polarity.Rel, evalPF] <;> rw [ip, iq] <;> exact id
  | .ite c t e, σ, h => by
    simp only [occursAt, Bool.or_eq_false_iff] at h
    have hc₂ : occursAt .pos σ c = false := by
      rw [← occursAt_flip]; exact h.1.1.2
    have ic := evalPF_indep ρ A A' c σ hc₂ h.1.1.1
    have iht := evalPF_polarity ρ hAA t σ h.1.2
    have ihe := evalPF_polarity ρ hAA e σ h.2
    cases σ <;> simp only [Polarity.Rel, evalPF] at iht ihe ⊢ <;> rw [ic] <;>
      exact fun hx => hx.elim (fun h' => Or.inl ⟨h'.1, iht h'.2⟩)
        (fun h' => Or.inr ⟨h'.1, ihe h'.2⟩)
  | .boolLeaf p, σ, h => by
    simp only [occursAt, Bool.or_eq_false_iff] at h
    have hp₂ : occursAt .pos σ p = false := by
      rw [← occursAt_flip]; exact h.2
    have ip := evalPF_indep ρ A A' p σ hp₂ h.1
    cases σ <;> simp only [Polarity.Rel, evalPF] <;> rw [ip] <;> exact id

/-- Monotonicity: with only positive occurrences, `evalPF` is monotone in `A`. -/
theorem evalPF_mono_pos (ρ : Nat → Prop) {A A' : Prop} (f : PropFormula)
    (hNoNeg : occursAt .neg .pos f = false) (hAA : A → A') : evalPF ρ A f → evalPF ρ A' f :=
  evalPF_polarity ρ hAA f .pos hNoNeg

/-- Antitonicity: with only negative occurrences, `evalPF` is antitone in `A`. -/
theorem evalPF_antitone_neg (ρ : Nat → Prop) {A A' : Prop} (f : PropFormula)
    (hNoPos : occursAt .pos .pos f = false) (hAA : A → A') : evalPF ρ A' f → evalPF ρ A f := by
  have h : occursAt .neg .neg f = false := by
    rw [← occursAt_flip]
    exact hNoPos
  exact evalPF_polarity ρ hAA f .neg h

/-- `AssumptionPolarityGuard`: the assumption atom occurs only in strictly negative
    (antecedent) polarity, never in `iff`, `if` conditions, or Boolean leaves. -/
def AssumptionPolarityGuard (f : PropFormula) : Prop := occursAt .pos .pos f = false

instance (f : PropFormula) : Decidable (AssumptionPolarityGuard f) :=
  inferInstanceAs (Decidable (occursAt .pos .pos f = false))

/-- **Restoration**: a formula verified with its assumptions holding delivers a genuine
    conditional guarantee whatever the assumptions' real truth value. -/
theorem assumptionsPolarityGuard_sound {f : PropFormula} (hG : AssumptionPolarityGuard f)
    (ρ : Nat → Prop) (hVerified : evalPF ρ True f) (A : Prop) : evalPF ρ A f :=
  evalPF_antitone_neg ρ f hG (fun _ => trivial) hVerified

/-- The guarded antecedent form `assumesHold → C` is a genuine obligation on `C`. -/
theorem guardedAntecedent_genuine (ρ : Nat → Prop) :
    AssumptionPolarityGuard (.imp .assumesHold (.atom 0)) ∧
      (evalPF ρ True (.imp .assumesHold (.atom 0)) ↔ ρ 0) := by
  refine ⟨by decide, ⟨fun h => h trivial, fun h _ => h⟩⟩

/-- A placement verified with assumptions true but failing when they are false. -/
def PolarityCollapse (f : PropFormula) : Prop :=
  ∃ ρ : Nat → Prop, evalPF ρ True f ∧ ¬ evalPF ρ False f

/-- **Collapse** in postcondition position: `ensures C ∧ assumesHold`. -/
theorem positiveAssumption_collapse :
    ¬ AssumptionPolarityGuard (.and (.atom 0) .assumesHold) ∧
      PolarityCollapse (.and (.atom 0) .assumesHold) :=
  ⟨by decide, ⟨fun _ => True, ⟨trivial, trivial⟩, fun h => h.2⟩⟩

/-- **Collapse** in `iff` position. -/
theorem iffAssumption_collapse :
    ¬ AssumptionPolarityGuard (.iff .assumesHold (.atom 0)) ∧
      PolarityCollapse (.iff .assumesHold (.atom 0)) :=
  ⟨by decide, ⟨fun _ => True, ⟨fun _ => trivial, fun _ => trivial⟩, fun h => h.2 trivial⟩⟩

/-- **Collapse** in negated-antecedent position: `¬ assumesHold → C` is vacuous when
    verified with assumptions true. -/
theorem negatedAntecedent_collapse :
    ¬ AssumptionPolarityGuard (.imp (.not .assumesHold) (.atom 0)) ∧
      PolarityCollapse (.imp (.not .assumesHold) (.atom 0)) :=
  ⟨by decide, ⟨fun _ => False, fun hn => absurd trivial hn, fun h => h id⟩⟩

/-- **Collapse** in `if`-condition position. -/
theorem ifConditionAssumption_collapse :
    ¬ AssumptionPolarityGuard (.ite .assumesHold .tt (.atom 0)) ∧
      PolarityCollapse (.ite .assumesHold .tt (.atom 0)) :=
  ⟨by decide, ⟨fun _ => False, Or.inl ⟨trivial, trivial⟩,
    fun h => h.elim (fun h' => h'.1) (fun h' => h'.2)⟩⟩

/-- An unclean Boolean leaf is rejected even in antecedent position (fail-closed). -/
theorem boolLeafAssumption_rejected :
    ¬ AssumptionPolarityGuard (.imp (.boolLeaf .assumesHold) (.atom 0)) ∧
      PolarityCollapse (.boolLeaf .assumesHold) :=
  ⟨by decide, ⟨fun _ => True, trivial, id⟩⟩

/-! #### Let-alias inlining -/

/-- Substitute `v` for atom `x`. -/
def substAtom (x : Nat) (v : PropFormula) : PropFormula → PropFormula
  | .atom y => if y = x then v else .atom y
  | .assumesHold => .assumesHold
  | .tt => .tt
  | .ff => .ff
  | .not p => .not (substAtom x v p)
  | .and p q => .and (substAtom x v p) (substAtom x v q)
  | .or p q => .or (substAtom x v p) (substAtom x v q)
  | .imp p q => .imp (substAtom x v p) (substAtom x v q)
  | .iff p q => .iff (substAtom x v p) (substAtom x v q)
  | .ite c t e => .ite (substAtom x v c) (substAtom x v t) (substAtom x v e)
  | .boolLeaf p => .boolLeaf (substAtom x v p)

/-- Valuation update. -/
def updateVal (ρ : Nat → Prop) (x : Nat) (P : Prop) : Nat → Prop :=
  fun y => if y = x then P else ρ y

theorem evalPF_substAtom (ρ : Nat → Prop) (A : Prop) (x : Nat) (v : PropFormula) :
    ∀ f : PropFormula,
      (evalPF ρ A (substAtom x v f) ↔ evalPF (updateVal ρ x (evalPF ρ A v)) A f)
  | .atom y => by
    by_cases h : y = x
    · simp [substAtom, evalPF, updateVal, h]
    · simp [substAtom, evalPF, updateVal, h]
  | .assumesHold => Iff.rfl
  | .tt => Iff.rfl
  | .ff => Iff.rfl
  | .not p => by
    simp only [substAtom, evalPF]
    rw [evalPF_substAtom ρ A x v p]
  | .and p q => by
    simp only [substAtom, evalPF]
    rw [evalPF_substAtom ρ A x v p, evalPF_substAtom ρ A x v q]
  | .or p q => by
    simp only [substAtom, evalPF]
    rw [evalPF_substAtom ρ A x v p, evalPF_substAtom ρ A x v q]
  | .imp p q => by
    simp only [substAtom, evalPF]
    rw [evalPF_substAtom ρ A x v p, evalPF_substAtom ρ A x v q]
  | .iff p q => by
    simp only [substAtom, evalPF]
    rw [evalPF_substAtom ρ A x v p, evalPF_substAtom ρ A x v q]
  | .ite c t e => by
    simp only [substAtom, evalPF]
    rw [evalPF_substAtom ρ A x v c, evalPF_substAtom ρ A x v t, evalPF_substAtom ρ A x v e]
  | .boolLeaf p => by
    simp only [substAtom, evalPF]
    exact evalPF_substAtom ρ A x v p

/-- Maximum `let`-alias inlining depth; deeper chains fail closed. -/
def maxLetAliasDepth : Nat := 8

/-- Inline `let x₁ := v₁; ...; let xₖ := vₖ; f` (later values may mention earlier names). -/
def inlineLetAliases : List (Nat × PropFormula) → PropFormula → PropFormula
  | [], f => f
  | (x, v) :: bs, f => substAtom x v (inlineLetAliases bs f)

/-- Bounded inlining: `none` beyond `maxLetAliasDepth` bindings. -/
def inlineLetAliases? (bs : List (Nat × PropFormula)) (f : PropFormula) : Option PropFormula :=
  if bs.length ≤ maxLetAliasDepth then some (inlineLetAliases bs f) else none

/-- Semantics of a `let`-prefixed formula. -/
def evalLet (ρ : Nat → Prop) (A : Prop) : List (Nat × PropFormula) → PropFormula → Prop
  | [], f => evalPF ρ A f
  | (x, v) :: bs, f => evalLet (updateVal ρ x (evalPF ρ A v)) A bs f

theorem evalPF_inlineLetAliases (A : Prop) :
    ∀ (bs : List (Nat × PropFormula)) (ρ : Nat → Prop) (f : PropFormula),
      (evalPF ρ A (inlineLetAliases bs f) ↔ evalLet ρ A bs f)
  | [], _, _ => Iff.rfl
  | (x, v) :: bs, ρ, f => by
    simp only [inlineLetAliases, evalLet]
    rw [evalPF_substAtom]
    exact evalPF_inlineLetAliases A bs _ f

/-- The polarity guard applied after bounded `let`-alias inlining. -/
def LetAssumptionPolarityGuard (bs : List (Nat × PropFormula)) (f : PropFormula) : Prop :=
  ∃ g, inlineLetAliases? bs f = some g ∧ AssumptionPolarityGuard g

/-- **Restoration through `let` aliases.** -/
theorem letAssumptionPolarityGuard_sound {bs : List (Nat × PropFormula)} {f : PropFormula}
    (hG : LetAssumptionPolarityGuard bs f) (ρ : Nat → Prop) (hVerified : evalLet ρ True bs f)
    (A : Prop) : evalLet ρ A bs f := by
  obtain ⟨g, hg, hPol⟩ := hG
  unfold inlineLetAliases? at hg
  split at hg
  · cases hg
    rw [← evalPF_inlineLetAliases] at hVerified ⊢
    exact assumptionsPolarityGuard_sound hPol ρ hVerified A
  · cases hg

/-- **Fail-closed depth bound**: any `let`-alias chain exceeding `maxLetAliasDepth`
    is rejected regardless of its body. -/
theorem letAlias_depthExceeded_rejected {bs : List (Nat × PropFormula)} {f : PropFormula}
    (hDeep : maxLetAliasDepth < bs.length) : ¬ LetAssumptionPolarityGuard bs f := by
  rintro ⟨g, hg, _⟩
  unfold inlineLetAliases? at hg
  have hNotLe : ¬ bs.length ≤ maxLetAliasDepth := by omega
  simp [hNotLe] at hg

/-- **An alias hides a positive assumption**: `let h := assumesHold; h` passes the guard
    on its body alone, is rejected after inlining, and collapses. -/
theorem letAlias_hides_positive_assumption :
    AssumptionPolarityGuard (.atom 0) ∧ ¬ LetAssumptionPolarityGuard [(0, .assumesHold)] (.atom 0) ∧
      ∃ ρ, evalLet ρ True [(0, .assumesHold)] (.atom 0) ∧ ¬ evalLet ρ False [(0, .assumesHold)] (.atom 0) := by
  refine ⟨by decide, ?_, ⟨fun _ => False, ?_, ?_⟩⟩
  · rintro ⟨g, hg, hPol⟩
    have : g = .assumesHold := by
      simp [inlineLetAliases?, inlineLetAliases, substAtom, maxLetAliasDepth] at hg
      exact hg.symm
    subst this
    exact absurd hPol (by decide)
  · simp [evalLet, evalPF, updateVal]
  · simp [evalLet, evalPF, updateVal]

/-! ### 4.5 Guard 6b — structure constructor sealing (`Samite`) -/

/-- How a public export reaches an invariant-bearing structure. -/
inductive PublicExportKind : Type where
  | directMk
  | derivingInhabited
  | abbrevAlias
  | carrierWrap
  | privateForwarder
  | unqualifiedMk
  | openRenaming
  | smartConstructor
  | transform
  deriving DecidableEq, Repr

/-- Only verified smart constructors and invariant-preserving transforms are sealed. -/
def PublicExportKind.isSealedKind : PublicExportKind → Bool
  | .smartConstructor | .transform => true
  | _ => false

/-- A public export: constructor-like (`build`, from client-supplied fields) and
    method-like (`step`, from an existing value). -/
structure PublicExport (V : Type) where
  kind : PublicExportKind
  build : V → Option V
  step : V → Option V

/-- An invariant-bearing structure declaration. -/
structure StructDecl (V : Type) where
  inv : V → Prop
  ctorPrivate : Bool

/-- The raw constructor, exported when `mk` is not `private`. -/
def rawMkExport (V : Type) : PublicExport V :=
  { kind := .directMk, build := some, step := fun _ => none }

/-- Everything an external client can call. -/
def effectiveExports {V : Type} (d : StructDecl V) (exps : List (PublicExport V)) :
    List (PublicExport V) :=
  if d.ctorPrivate then exps else rawMkExport V :: exps

/-- Values reachable by an arbitrary external client trace. -/
inductive ClientReach {V : Type} (exps : List (PublicExport V)) : List V → Prop where
  | nil : ClientReach exps []
  | build {vs : List V} (e : PublicExport V) (r v : V) :
      e ∈ exps → e.build r = some v → ClientReach exps vs → ClientReach exps (v :: vs)
  | step {vs : List V} (e : PublicExport V) (u v : V) :
      e ∈ exps → u ∈ vs → e.step u = some v → ClientReach exps vs → ClientReach exps (v :: vs)

/-- A sealed export establishes or preserves the invariant. -/
def ExportSealed {V : Type} (inv : V → Prop) (e : PublicExport V) : Prop :=
  e.kind.isSealedKind = true ∧ (∀ r v, e.build r = some v → inv v) ∧
    (∀ u v, inv u → e.step u = some v → inv v)

/-- `StructSealingGuard`: `private mk ::` and only sealed exports. -/
structure StructSealingGuard {V : Type} (d : StructDecl V) (exps : List (PublicExport V)) :
    Prop where
  ctor_private : d.ctorPrivate = true
  exports_sealed : ∀ e ∈ exps, ExportSealed d.inv e

/-- **Restoration**: by induction over arbitrary client traces, every value reachable
    outside the defining boundary satisfies the invariant. -/
theorem structSealingGuard_inductive_soundness {V : Type} {d : StructDecl V}
    {exps : List (PublicExport V)} (hG : StructSealingGuard d exps) {vs : List V}
    (hr : ClientReach (effectiveExports d exps) vs) : ∀ v ∈ vs, d.inv v := by
  have hEff : effectiveExports d exps = exps := by
    simp [effectiveExports, hG.ctor_private]
  rw [hEff] at hr
  induction hr with
  | nil => intro v hv; exact absurd hv List.not_mem_nil
  | build e r v he hb _ ih =>
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact (hG.exports_sealed e he).2.1 r w hb
    · exact ih w hw
  | step e u v he hu hs _ ih =>
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact (hG.exports_sealed e he).2.2 u w (ih u hu) hs
    · exact ih w hw

/-- **Collapse**: a public raw constructor lets a client reach any violating value. -/
theorem publicMk_soundness_collapse {V : Type} (d : StructDecl V) (exps : List (PublicExport V))
    (hPub : d.ctorPrivate = false) (bad : V) (hBad : ¬ d.inv bad) :
    ClientReach (effectiveExports d exps) [bad] ∧ ¬ ∀ v ∈ [bad], d.inv v := by
  refine ⟨?_, fun h => hBad (h bad (List.mem_singleton.mpr rfl))⟩
  have hMem : rawMkExport V ∈ effectiveExports d exps := by
    simp [effectiveExports, hPub]
  exact .build (rawMkExport V) bad bad hMem rfl .nil

/-- **Collapse**: any leaking export (`deriving Inhabited`, alias, carrier, forwarder,
    unqualified `mk`, `open ... renaming`) producing a violating value breaks the
    invariant. -/
theorem leakyExport_soundness_collapse {V : Type} (d : StructDecl V) (exps : List (PublicExport V))
    (e : PublicExport V) (he : e ∈ exps) (r bad : V) (hb : e.build r = some bad)
    (hBad : ¬ d.inv bad) :
    ClientReach (effectiveExports d exps) [bad] ∧ ¬ ∀ v ∈ [bad], d.inv v := by
  refine ⟨?_, fun h => hBad (h bad (List.mem_singleton.mpr rfl))⟩
  have hMem : e ∈ effectiveExports d exps := by
    unfold effectiveExports
    split
    · exact he
    · exact List.mem_cons_of_mem _ he
  exact .build e r bad hMem hb .nil

/-- **Collapse**: a non-invariant-preserving transform export breaks the invariant even
    when all constructors start from valid values. -/
theorem leakyTransform_soundness_collapse {V : Type} (d : StructDecl V)
    (exps : List (PublicExport V)) (eBuild eStep : PublicExport V)
    (heBuild : eBuild ∈ exps) (heStep : eStep ∈ exps) (r good bad : V)
    (hb : eBuild.build r = some good) (hs : eStep.step good = some bad)
    (hBad : ¬ d.inv bad) :
    ClientReach (effectiveExports d exps) [bad, good] ∧ ¬ ∀ v ∈ [bad, good], d.inv v := by
  have memEff : ∀ e ∈ exps, e ∈ effectiveExports d exps := by
    intro e he
    unfold effectiveExports
    split
    · exact he
    · exact List.mem_cons_of_mem _ he
  refine ⟨?_, fun h => hBad (h bad (List.mem_cons_self ..))⟩
  exact .step eStep good bad (memEff eStep heStep) (List.mem_singleton.mpr rfl) hs
    (.build eBuild r good (memEff eBuild heBuild) hb .nil)

/-- Every leaking export kind is rejected by the guard. -/
theorem leakKind_rejected {V : Type} {d : StructDecl V} {exps : List (PublicExport V)}
    {e : PublicExport V} (he : e ∈ exps) (hKind : e.kind.isSealedKind = false) :
    ¬ StructSealingGuard d exps := by
  intro hG
  have := (hG.exports_sealed e he).1
  rw [hKind] at this
  cases this

theorem leakKinds_unsealed :
    [PublicExportKind.directMk, .derivingInhabited, .abbrevAlias, .carrierWrap,
      .privateForwarder, .unqualifiedMk, .openRenaming].all (fun k => !k.isSealedKind) = true :=
  rfl

end Anneal.InductiveReplayAndPeerSpecGuards
