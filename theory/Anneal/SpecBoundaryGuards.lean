-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Trusted
import Anneal.SpecRealizability

/-!
# Specification-Boundary Soundness Guards and the Frozen Taxonomy Contract

A kernel-checked `VerificationResult` with no proof gap and only standard axioms can
still certify nothing when the *specification boundary* is wrong. This module
formalizes three external specification-boundary guards, and freezes the
cross-language taxonomy contract shared with the Rust tooling
(`anneal_spec::spec_check` and `cargo_anneal::property_registry`).

1. **Frozen taxonomy contract** (`PropertyClassTag`, `SpecBoundaryGuardClass`): the
   12 canonical MIR property classes and the 3 spec-boundary guards, with their wire
   identifiers, ranks, and bijection proofs.
2. **Guard 1 — entry-point `requires` ban** (`verus#3606`, wire id
   `entry_point_requires`): a binary entry point (`main`, `#![no_main]` `_start`,
   `#[entry]`) has no verified Rust caller, so nothing discharges its precondition.
   `EntryRequiresSoundnessCollapse` exhibits a verified, non-vacuous, dichotomous
   claim whose closed program still faults with undefined behavior;
   `claimClosedProgramSafe_of_guard` proves that `EntryPointRequiresGuard` restores
   closed-program safety over every ABI-admissible initial state.
3. **Guard 2 — fixed-width ghost length** (`Slate` soundness bug 121, wire id
   `fixed_width_ghost_length`): a ghost collection length typed at a fixed machine
   width wraps at `2 ^ w`, and the standard inductive collection axioms then derive
   `False` (`false_of_fixedWidth_ghost_length_strict_mono`,
   `false_of_fixedWidth_ghost_length_zero_empty`). Unbounded `Nat` / `Int` lengths
   have a model (`ghostLengthTypeGuard_iff_nonempty_model`).
4. **Guard 3 — error-branch `True` wildcard** (`awsm2`, wire id
   `error_branch_wildcard`): a postcondition `| .err _ => True | .ub => True` passes
   `PostconditionDichotomy` on the strength of its `ok` arm alone while accepting
   every error escape and every fault (`errorWildcardPost_postconditionDichotomy`,
   `errorWildcardPost_constErr_survives`). `ErrorBranchGuardedPost` is the positive
   obligation that kills those mutants.

Every definition is a safe kernel definition and every theorem depends only on
`propext`, `Classical.choice`, and `Quot.sound`.
-/

namespace Anneal.SpecBoundaryGuards

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.SpecRealizability

universe u v w

/-! ## 1. Frozen Cross-Language Taxonomy Contract -/

/-! ### 1.1 The 12 Canonical MIR Property Classes -/

/-- The 12 canonical MIR verification property classes in rank order `0..11`,
    mirroring `cargo_anneal::property_registry::PropertyClass` constructor for
    constructor. -/
inductive PropertyClassTag : Type where
  | arithmeticOverflow
  | shiftBounds
  | divRemUb
  | pointerDereference
  | sliceArrayBounds
  | discriminantValidity
  | callContract
  | loopTermination
  | switchExhaustiveness
  | memoryCopyOverlap
  | uninitRead
  | unsupportedFallback
  deriving DecidableEq, Repr, Inhabited

namespace PropertyClassTag

/-- Canonical `snake_case` wire identifier (`PropertyClass::as_str`). -/
def asStr : PropertyClassTag → String
  | .arithmeticOverflow => "arithmetic_overflow"
  | .shiftBounds => "shift_bounds"
  | .divRemUb => "div_rem_ub"
  | .pointerDereference => "pointer_deref"
  | .sliceArrayBounds => "slice_array_bounds"
  | .discriminantValidity => "discriminant_validity"
  | .callContract => "call_contract"
  | .loopTermination => "loop_termination"
  | .switchExhaustiveness => "switch_exhaustiveness"
  | .memoryCopyOverlap => "memory_copy_overlap"
  | .uninitRead => "uninit_read"
  | .unsupportedFallback => "unsupported_fallback"

/-- Rust enum variant name of the class (`PropertyClass::<Variant>`). -/
def variantName : PropertyClassTag → String
  | .arithmeticOverflow => "ArithmeticOverflow"
  | .shiftBounds => "ShiftBounds"
  | .divRemUb => "DivRemUb"
  | .pointerDereference => "PointerDereference"
  | .sliceArrayBounds => "SliceArrayBounds"
  | .discriminantValidity => "DiscriminantValidity"
  | .callContract => "CallContract"
  | .loopTermination => "LoopTermination"
  | .switchExhaustiveness => "SwitchExhaustiveness"
  | .memoryCopyOverlap => "MemoryCopyOverlap"
  | .uninitRead => "UninitRead"
  | .unsupportedFallback => "UnsupportedFallback"

/-- 0-based canonical rank (`PropertyClass::rank`). -/
def rank : PropertyClassTag → Nat
  | .arithmeticOverflow => 0
  | .shiftBounds => 1
  | .divRemUb => 2
  | .pointerDereference => 3
  | .sliceArrayBounds => 4
  | .discriminantValidity => 5
  | .callContract => 6
  | .loopTermination => 7
  | .switchExhaustiveness => 8
  | .memoryCopyOverlap => 9
  | .uninitRead => 10
  | .unsupportedFallback => 11

/-- Inverse of `rank` (`PropertyClass::from_rank`); `none` for every rank `≥ 12`. -/
def ofRank? : Nat → Option PropertyClassTag
  | 0 => some .arithmeticOverflow
  | 1 => some .shiftBounds
  | 2 => some .divRemUb
  | 3 => some .pointerDereference
  | 4 => some .sliceArrayBounds
  | 5 => some .discriminantValidity
  | 6 => some .callContract
  | 7 => some .loopTermination
  | 8 => some .switchExhaustiveness
  | 9 => some .memoryCopyOverlap
  | 10 => some .uninitRead
  | 11 => some .unsupportedFallback
  | _ => none

/-- Whether a contract or registry waiver may ever cover the class
    (`PropertyClass::is_waivable`). Only `unsupportedFallback` is non-waivable. -/
def isWaivable : PropertyClassTag → Bool
  | .unsupportedFallback => false
  | _ => true

/-- All 12 classes in canonical rank order (`PropertyClass::ALL`). -/
def all : List PropertyClassTag :=
  [.arithmeticOverflow, .shiftBounds, .divRemUb, .pointerDereference, .sliceArrayBounds,
    .discriminantValidity, .callContract, .loopTermination, .switchExhaustiveness,
    .memoryCopyOverlap, .uninitRead, .unsupportedFallback]

/-- Parse a wire identifier (`PropertyClass::from_str`); exact and case-sensitive. -/
def ofStr? (s : String) : Option PropertyClassTag :=
  all.find? (fun c => c.asStr == s)

/-- Parse a Rust variant name; exact and case-sensitive. -/
def ofVariantName? (s : String) : Option PropertyClassTag :=
  all.find? (fun c => c.variantName == s)

theorem ofStr?_asStr (c : PropertyClassTag) : ofStr? c.asStr = some c := by
  cases c <;> rfl

theorem ofVariantName?_variantName (c : PropertyClassTag) :
    ofVariantName? c.variantName = some c := by
  cases c <;> rfl

/-- The wire identifiers of distinct classes are distinct. -/
theorem asStr_injective {a b : PropertyClassTag} (h : a.asStr = b.asStr) : a = b := by
  have hParse : ofStr? a.asStr = ofStr? b.asStr := congrArg ofStr? h
  rw [ofStr?_asStr, ofStr?_asStr] at hParse
  exact Option.some.inj hParse

theorem variantName_injective {a b : PropertyClassTag}
    (h : a.variantName = b.variantName) : a = b := by
  have hParse : ofVariantName? a.variantName = ofVariantName? b.variantName :=
    congrArg ofVariantName? h
  rw [ofVariantName?_variantName, ofVariantName?_variantName] at hParse
  exact Option.some.inj hParse

/-- A successful parse returns the class carrying exactly that identifier. -/
theorem asStr_of_ofStr? {s : String} {c : PropertyClassTag} (h : ofStr? s = some c) :
    c.asStr = s := by
  have hFound := List.find?_some h
  exact eq_of_beq hFound

theorem ofStr?_eq_some_iff {s : String} {c : PropertyClassTag} :
    ofStr? s = some c ↔ c.asStr = s :=
  ⟨asStr_of_ofStr?, fun h => h ▸ ofStr?_asStr c⟩

theorem rank_lt_twelve (c : PropertyClassTag) : c.rank < 12 := by
  cases c <;> decide

theorem ofRank?_rank (c : PropertyClassTag) : ofRank? c.rank = some c := by
  cases c <;> rfl

theorem rank_injective {a b : PropertyClassTag} (h : a.rank = b.rank) : a = b := by
  have hParse : ofRank? a.rank = ofRank? b.rank := congrArg ofRank? h
  rw [ofRank?_rank, ofRank?_rank] at hParse
  exact Option.some.inj hParse

/-- `ofRank?` rejects every rank outside `0..11`. -/
theorem ofRank?_eq_none_of_ge {n : Nat} (h : 12 ≤ n) : ofRank? n = none := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 12 := ⟨n - 12, by omega⟩
  rfl

/-- A successful `ofRank?` returns the class of exactly that rank. -/
theorem rank_of_ofRank? {n : Nat} {c : PropertyClassTag} (h : ofRank? n = some c) :
    c.rank = n := by
  by_cases hn : 12 ≤ n
  · rw [ofRank?_eq_none_of_ge hn] at h
    cases h
  · have hLt : n < 12 := by omega
    match n, hLt, h with
    | 0, _, h | 1, _, h | 2, _, h | 3, _, h | 4, _, h | 5, _, h
    | 6, _, h | 7, _, h | 8, _, h | 9, _, h | 10, _, h | 11, _, h =>
      cases h
      rfl

theorem mem_all (c : PropertyClassTag) : c ∈ all := by
  cases c <;> decide

theorem all_length : all.length = 12 := rfl

theorem all_nodup : all.Nodup := by decide

/-- `all` lists the classes in strictly increasing rank order `0, 1, …, 11`. -/
theorem all_map_rank : all.map rank = List.range 12 := by decide

theorem isWaivable_eq_false_iff (c : PropertyClassTag) :
    c.isWaivable = false ↔ c = .unsupportedFallback := by
  cases c <;> decide

/-- Exactly 11 of the 12 classes are waivable. -/
theorem all_filter_isWaivable_length : (all.filter isWaivable).length = 11 := by decide

end PropertyClassTag

/-! ### 1.2 The 3 Spec-Boundary Guards -/

/-- The 3 specification-boundary guards in rank order `0..2`, mirroring
    `anneal_spec::spec_check::SpecBoundaryGuardClass` and
    `cargo_anneal::property_registry::SpecBoundaryGuardId`. -/
inductive SpecBoundaryGuardClass : Type where
  /-- `verus#3606`: a binary entry point carries a non-trivial `requires`. -/
  | entryPointPrecondition
  /-- `Slate` soundness bug 121: a ghost collection length has a fixed machine width. -/
  | fixedWidthGhostLength
  /-- `awsm2`: a postcondition accepts every error, `ub`, or `unsupported` outcome. -/
  | errorBranchWildcard
  deriving DecidableEq, Repr, Inhabited

namespace SpecBoundaryGuardClass

/-- Canonical `snake_case` guard identifier (`guard_id` / `SpecBoundaryGuardId::as_str`). -/
def guardId : SpecBoundaryGuardClass → String
  | .entryPointPrecondition => "entry_point_requires"
  | .fixedWidthGhostLength => "fixed_width_ghost_length"
  | .errorBranchWildcard => "error_branch_wildcard"

/-- Canonical diagnostic name (`canonical_name`). -/
def canonicalName : SpecBoundaryGuardClass → String
  | .entryPointPrecondition => "EntryPointPrecondition"
  | .fixedWidthGhostLength => "FixedWidthGhostLength"
  | .errorBranchWildcard => "ErrorBranchWildcard"

/-- The frozen 5-class vacuity class a violation of the guard is reported under
    (`to_vacuity_class`). -/
def toVacuityClass : SpecBoundaryGuardClass → VacuityClass
  | .entryPointPrecondition => .deadPrecondition
  | .fixedWidthGhostLength => .specViolation
  | .errorBranchWildcard => .survivedAllMutants

/-- 0-based canonical rank. -/
def rank : SpecBoundaryGuardClass → Nat
  | .entryPointPrecondition => 0
  | .fixedWidthGhostLength => 1
  | .errorBranchWildcard => 2

/-- Inverse of `rank`; `none` for every rank `≥ 3`. -/
def ofRank? : Nat → Option SpecBoundaryGuardClass
  | 0 => some .entryPointPrecondition
  | 1 => some .fixedWidthGhostLength
  | 2 => some .errorBranchWildcard
  | _ => none

/-- All 3 guards in canonical rank order (`SpecBoundaryGuardClass::ALL`). -/
def all : List SpecBoundaryGuardClass :=
  [.entryPointPrecondition, .fixedWidthGhostLength, .errorBranchWildcard]

/-- Parse a guard identifier; exact and case-sensitive. -/
def ofGuardId? (s : String) : Option SpecBoundaryGuardClass :=
  all.find? (fun g => g.guardId == s)

/-- Parse a canonical diagnostic name; exact and case-sensitive. -/
def ofCanonicalName? (s : String) : Option SpecBoundaryGuardClass :=
  all.find? (fun g => g.canonicalName == s)

theorem ofGuardId?_guardId (g : SpecBoundaryGuardClass) : ofGuardId? g.guardId = some g := by
  cases g <;> rfl

theorem ofCanonicalName?_canonicalName (g : SpecBoundaryGuardClass) :
    ofCanonicalName? g.canonicalName = some g := by
  cases g <;> rfl

theorem guardId_injective {a b : SpecBoundaryGuardClass} (h : a.guardId = b.guardId) :
    a = b := by
  have hParse : ofGuardId? a.guardId = ofGuardId? b.guardId := congrArg ofGuardId? h
  rw [ofGuardId?_guardId, ofGuardId?_guardId] at hParse
  exact Option.some.inj hParse

theorem canonicalName_injective {a b : SpecBoundaryGuardClass}
    (h : a.canonicalName = b.canonicalName) : a = b := by
  have hParse : ofCanonicalName? a.canonicalName = ofCanonicalName? b.canonicalName :=
    congrArg ofCanonicalName? h
  rw [ofCanonicalName?_canonicalName, ofCanonicalName?_canonicalName] at hParse
  exact Option.some.inj hParse

theorem guardId_of_ofGuardId? {s : String} {g : SpecBoundaryGuardClass}
    (h : ofGuardId? s = some g) : g.guardId = s := by
  have hFound := List.find?_some h
  exact eq_of_beq hFound

theorem canonicalName_of_ofCanonicalName? {s : String} {g : SpecBoundaryGuardClass}
    (h : ofCanonicalName? s = some g) : g.canonicalName = s := by
  have hFound := List.find?_some h
  exact eq_of_beq hFound

theorem ofGuardId?_eq_some_iff {s : String} {g : SpecBoundaryGuardClass} :
    ofGuardId? s = some g ↔ g.guardId = s :=
  ⟨guardId_of_ofGuardId?, fun h => h ▸ ofGuardId?_guardId g⟩

theorem ofCanonicalName?_eq_some_iff {s : String} {g : SpecBoundaryGuardClass} :
    ofCanonicalName? s = some g ↔ g.canonicalName = s :=
  ⟨canonicalName_of_ofCanonicalName?, fun h => h ▸ ofCanonicalName?_canonicalName g⟩

theorem rank_lt_three (g : SpecBoundaryGuardClass) : g.rank < 3 := by
  cases g <;> decide

theorem ofRank?_rank (g : SpecBoundaryGuardClass) : ofRank? g.rank = some g := by
  cases g <;> rfl

theorem rank_injective {a b : SpecBoundaryGuardClass} (h : a.rank = b.rank) : a = b := by
  have hParse : ofRank? a.rank = ofRank? b.rank := congrArg ofRank? h
  rw [ofRank?_rank, ofRank?_rank] at hParse
  exact Option.some.inj hParse

theorem mem_all (g : SpecBoundaryGuardClass) : g ∈ all := by
  cases g <;> decide

theorem all_length : all.length = 3 := rfl

theorem all_nodup : all.Nodup := by decide

theorem all_map_rank : all.map rank = List.range 3 := by decide

/-- Distinct guards report under distinct vacuity classes. -/
theorem toVacuityClass_injective {a b : SpecBoundaryGuardClass}
    (h : a.toVacuityClass = b.toVacuityClass) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

/-- No guard identifier coincides with a guard diagnostic name, so the two wire
    namespaces cannot be confused. -/
theorem guardId_ne_canonicalName (a b : SpecBoundaryGuardClass) :
    a.guardId ≠ b.canonicalName := by
  cases a <;> cases b <;> decide

/-- The frozen `(guard_id, canonical_name, vacuity_class)` wire table. -/
theorem wire_table :
    all.map (fun g => (g.guardId, g.canonicalName, g.toVacuityClass.canonicalName)) =
      [("entry_point_requires", "EntryPointPrecondition", "DeadPrecondition"),
        ("fixed_width_ghost_length", "FixedWidthGhostLength", "SpecViolation"),
        ("error_branch_wildcard", "ErrorBranchWildcard", "SurvivedAllMutants")] :=
  rfl

end SpecBoundaryGuardClass

/-! ## 2. One-Step Interaction-Tree Reasoning

Inversion lemmas for `Reaches`, `TauStar`, `FaultNow`, `TreeSafe`, and `ReachesRet` along
a single observed `ITreeF` layer. They let a concrete, finite MIR execution be
replayed inside the kernel without any proof calculus beyond `Trusted`. -/

section StepLemmas

variable {E : Effect.{u}} {R : Type u}

/-- A tree observed at `.ret` has no silent successor other than itself. -/
theorem tauStar_eq_of_observe_ret {t t' : ITree E R} {r : R}
    (h : t.observe = .ret r) (hs : TauStar t t') : t' = t := by
  cases hs with
  | refl => rfl
  | step hObs _ => rw [h] at hObs; cases hObs

theorem not_faultNow_of_observe_ret [FaultEffect E] {t : ITree E R} {r : R}
    (h : t.observe = .ret r) : ¬ FaultNow t := by
  rintro ⟨t', i, k, hs, hObs, _⟩
  have hEq := tauStar_eq_of_observe_ret h hs
  subst hEq
  rw [h] at hObs
  cases hObs

theorem faultNow_of_observe_tau [FaultEffect E] {t t' : ITree E R}
    (h : t.observe = .tau t') (hf : FaultNow t) : FaultNow t' := by
  obtain ⟨u, i, k, hs, hObs, hFault⟩ := hf
  cases hs with
  | refl => rw [h] at hObs; cases hObs
  | step hObs' hs' =>
    rw [h] at hObs'
    cases hObs'
    exact ⟨u, i, k, hs', hObs, hFault⟩

theorem faultNow_of_observe_fault [FaultEffect E] {t : ITree E R} {i : E.I}
    {k : E.O i → ITree E R} (h : t.observe = .vis i k) (hFault : FaultEffect.isFault i) :
    FaultNow t :=
  ⟨t, i, k, TauStar.refl t, h, hFault⟩

theorem reaches_of_observe_ret [FaultEffect E] {t u : ITree E R} {r : R}
    {tr : List (Event E)} (h : t.observe = .ret r) (hr : Reaches t tr u) :
    tr = [] ∧ u = t := by
  cases hr with
  | refl => exact ⟨rfl, rfl⟩
  | tau hObs _ => rw [h] at hObs; cases hObs
  | vis hObs _ _ _ => rw [h] at hObs; cases hObs

theorem reaches_of_observe_tau [FaultEffect E] {t t' u : ITree E R}
    {tr : List (Event E)} (h : t.observe = .tau t') (hr : Reaches t tr u) :
    (tr = [] ∧ u = t) ∨ Reaches t' tr u := by
  cases hr with
  | refl => exact Or.inl ⟨rfl, rfl⟩
  | tau hObs hr' =>
    rw [h] at hObs
    cases hObs
    exact Or.inr hr'
  | vis hObs _ _ _ => rw [h] at hObs; cases hObs

/-- A tree that returns immediately is safe. -/
theorem treeSafe_of_observe_ret [FaultEffect E] {t : ITree E R} {r : R}
    (h : t.observe = .ret r) : TreeSafe t := by
  intro tr u hr
  obtain ⟨-, rfl⟩ := reaches_of_observe_ret h hr
  exact not_faultNow_of_observe_ret h

/-- Safety propagates backwards across a silent step. -/
theorem treeSafe_of_observe_tau [FaultEffect E] {t t' : ITree E R}
    (h : t.observe = .tau t') (hSafe : TreeSafe t') : TreeSafe t := by
  intro tr u hr
  rcases reaches_of_observe_tau h hr with ⟨-, rfl⟩ | hr'
  · exact fun hf => hSafe [] t' (Reaches.refl t') (faultNow_of_observe_tau h hf)
  · exact hSafe tr u hr'

/-- A tree that can fault now is not safe. -/
theorem not_treeSafe_of_faultNow [FaultEffect E] {t : ITree E R} (hf : FaultNow t) :
    ¬ TreeSafe t :=
  fun hSafe => hSafe [] t (Reaches.refl t) hf

theorem reachesRet_of_observe_ret [FaultEffect E] {t : ITree E R} {r r' : R}
    {tr : List (Event E)} (h : t.observe = .ret r) (hr : ReachesRet t tr r') :
    tr = [] ∧ r' = r := by
  obtain ⟨u, hReach, hObs⟩ := hr
  obtain ⟨rfl, rfl⟩ := reaches_of_observe_ret h hReach
  rw [h] at hObs
  cases hObs
  exact ⟨rfl, rfl⟩

theorem reachesRet_of_observe_tau [FaultEffect E] {t t' : ITree E R} {r : R}
    {tr : List (Event E)} (h : t.observe = .tau t') (hr : ReachesRet t tr r) :
    ReachesRet t' tr r := by
  obtain ⟨u, hReach, hObs⟩ := hr
  rcases reaches_of_observe_tau h hReach with ⟨-, rfl⟩ | hr'
  · rw [h] at hObs
    cases hObs
  · exact ⟨u, hr', hObs⟩

/-- A tree observed at `.ret` does not silently diverge. -/
theorem not_diverges_of_observe_ret {t : ITree E R} {r : R}
    (h : t.observe = .ret r) : ¬ Diverges t := by
  intro hd
  rw [Diverges.eq_def, h] at hd
  exact hd

/-- Silent divergence steps across `.tau`. -/
theorem diverges_of_observe_tau {t t' : ITree E R}
    (h : t.observe = .tau t') (hd : Diverges t) : Diverges t' := by
  rw [Diverges.eq_def, h] at hd
  exact hd

/-- A tree observed at `.ret` is reactively productive. -/
theorem productive_of_observe_ret [FaultEffect E] {t : ITree E R} {r : R}
    (h : t.observe = .ret r) : Productive t := by
  intro tr u hr
  obtain ⟨-, hEq⟩ := reaches_of_observe_ret h hr
  subst hEq
  refine ⟨u, TauStar.refl u, fun w hTau => ?_⟩
  rw [h] at hTau
  cases hTau

/-- Productivity propagates backwards across a silent step. -/
theorem productive_of_observe_tau [FaultEffect E] {t t' : ITree E R}
    (h : t.observe = .tau t') (hProd : Productive t') : Productive t := by
  intro tr u hr
  rcases reaches_of_observe_tau h hr with ⟨-, rfl⟩ | hr'
  · obtain ⟨u', hs, hNonTau⟩ := hProd [] t' (Reaches.refl t')
    exact ⟨u', TauStar.step h hs, hNonTau⟩
  · exact hProd tr u hr'

/-- A tree observed at `.ret` cannot diverge. -/
theorem not_mayDiverge_of_observe_ret [FaultEffect E] {t : ITree E R} {r : R}
    (h : t.observe = .ret r) : ¬ MayDiverge t := by
  rintro ⟨tr, u, hr, hd⟩
  obtain ⟨-, rfl⟩ := reaches_of_observe_ret h hr
  exact not_diverges_of_observe_ret h hd

/-- Non-divergence propagates backwards across a silent step. -/
theorem not_mayDiverge_of_observe_tau [FaultEffect E] {t t' : ITree E R}
    (h : t.observe = .tau t') (hNoDiv : ¬ MayDiverge t') : ¬ MayDiverge t := by
  rintro ⟨tr, u, hr, hd⟩
  rcases reaches_of_observe_tau h hr with ⟨-, rfl⟩ | hr'
  · exact hNoDiv ⟨[], t', Reaches.refl t', diverges_of_observe_tau h hd⟩
  · exact hNoDiv ⟨tr, u, hr', hd⟩

end StepLemmas

/-! ### MIR Coalgebra Unfolding -/

/-- A silent coalgebra step is a `.tau` layer of the unfolded tree. -/
theorem cofix_observe_of_step_tau {body : CapturedMir} {st st' : MirExecState}
    (h : stepMirState body st = .tau st') :
    (ITree.cofix (stepMirState body) st).observe =
      .tau (ITree.cofix (stepMirState body) st') := by
  rw [ITree.observe_cofix, h]
  rfl

/-- A returning coalgebra step is a `.ret` layer of the unfolded tree. -/
theorem cofix_observe_of_step_ret {body : CapturedMir} {st : MirExecState}
    {out : MirOutcome} (h : stepMirState body st = .ret out) :
    (ITree.cofix (stepMirState body) st).observe = .ret out := by
  rw [ITree.observe_cofix, h]
  rfl

/-- A faulting coalgebra step is a fault `.vis` layer of the unfolded tree. -/
theorem cofix_observe_of_step_fail {body : CapturedMir} {st : MirExecState}
    {kind : FailureKind} (h : stepMirState body st = MirStepNode.fail kind) :
    ∃ k, (ITree.cofix (stepMirState body) st).observe =
      .vis (Sum.inl (FailReq.fail kind)) k := by
  refine ⟨fun o => ITree.cofix (stepMirState body) (PEmpty.elim o), ?_⟩
  rw [ITree.observe_cofix, h]
  rfl

/-- `t` raises the operational fault `kind` after finitely many silent steps. -/
def FaultsWith (t : ITree MirEffect MirOutcome) (kind : FailureKind) : Prop :=
  ∃ (t' : ITree MirEffect MirOutcome)
    (k : MirEffect.O (Sum.inl (FailReq.fail kind)) → ITree MirEffect MirOutcome),
    TauStar t t' ∧ t'.observe = .vis (Sum.inl (FailReq.fail kind)) k

theorem FaultsWith.faultNow {t : ITree MirEffect MirOutcome} {kind : FailureKind}
    (h : FaultsWith t kind) : FaultNow t := by
  obtain ⟨t', k, hs, hObs⟩ := h
  exact ⟨t', _, k, hs, hObs, trivial⟩

/-- A tree that raises any operational fault is not `TreeSafe`. -/
theorem FaultsWith.not_treeSafe {t : ITree MirEffect MirOutcome} {kind : FailureKind}
    (h : FaultsWith t kind) : ¬ TreeSafe t :=
  not_treeSafe_of_faultNow h.faultNow

/-- A MIR execution whose first coalgebra step faults raises that fault. -/
theorem faultsWith_of_step_fail {body : CapturedMir} {s : MachineState}
    {kind : FailureKind}
    (h : stepMirState body (.running s) = MirStepNode.fail kind) :
    FaultsWith (mirTree body s) kind := by
  obtain ⟨k, hObs⟩ := cofix_observe_of_step_fail h
  exact ⟨mirTree body s, k, TauStar.refl _, hObs⟩

/-! ## 3. Guard 1 — Entry-Point `requires` Ban (`verus#3606`)

A precondition is an obligation on the *caller*. Every ordinary function is called
from verified Rust code, so a `VerificationResult` for the caller discharges it. A
binary entry point is called by the operating system, the C runtime, or a reset
vector: nothing checks its `requires`. A verified claim `{pre} main {post}` then only
certifies the executions the loader happens to start inside `pre`, and the closed
program is unverified on every other ABI-admissible initial state. -/

/-! ### 3.1 Entry-Point Classification -/

/-- How an item becomes a binary entry point. -/
inductive EntryPointKind : Type where
  /-- Rust `fn main` of a binary crate, called by the `std` runtime (`lang_start`). -/
  | rustMain
  /-- `#![no_main]` entry symbol (`_start`, `__start`, or an exported C `main`). -/
  | noMainStart
  /-- Item marked by an entry attribute (`#[entry]`, `#[main]`, `#[start]`). -/
  | customEntryAttr
  deriving DecidableEq, Repr, Inhabited

/-- Wire identifier of an `EntryPointKind` (`EntryPointKind::as_str`). -/
def EntryPointKind.asStr : EntryPointKind → String
  | .rustMain => "main"
  | .noMainStart => "no_main_start"
  | .customEntryAttr => "entry_attribute"

theorem EntryPointKind.asStr_injective {a b : EntryPointKind} (h : a.asStr = b.asStr) :
    a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- Scanner state for splitting a path at `::`: whether the previous character was
    an unpaired `:`, the current segment (reversed), and the completed segments
    (reversed). -/
structure PathSplitState : Type where
  /-- The previous character was a `:` not yet paired into a `::` separator. -/
  pendingColon : Bool
  /-- Characters of the current segment, most recent first. -/
  cur : List Char
  /-- Completed segments, most recent first. -/
  acc : List (List Char)

/-- Consume one character: the second `:` of a pair closes the current segment, and
    an unpaired `:` is an ordinary segment character. -/
def PathSplitState.step (st : PathSplitState) (ch : Char) : PathSplitState :=
  if ch == ':' then
    if st.pendingColon then
      { pendingColon := false, cur := [], acc := st.cur.reverse :: st.acc }
    else
      { st with pendingColon := true }
  else if st.pendingColon then
    { pendingColon := false, cur := ch :: ':' :: st.cur, acc := st.acc }
  else
    { st with cur := ch :: st.cur }

/-- Close the final segment, keeping a trailing unpaired `:`. -/
def PathSplitState.finish (st : PathSplitState) : List (List Char) :=
  ((if st.pendingColon then ':' :: st.cur else st.cur).reverse :: st.acc).reverse

/-- The `::`-separated segments of a definition path (`"a::b"` ↦ `["a", "b"]`),
    splitting at the leftmost non-overlapping `::` occurrences exactly as Rust's
    `str::split("::")` does. -/
def pathSegments (path : String) : List String :=
  (path.toList.foldl PathSplitState.step
    { pendingColon := false, cur := [], acc := [] }).finish.map String.ofList

/-- Whether `seg` is a valid crate-root segment name: non-empty, starting with an
    ASCII letter or `_`, and containing only ASCII alphanumerics, `_`, or `-`.
    This rejects rustc impl/trait pseudo-segments such as `<MyType as Trait>`,
    `<impl Foo>`, `{{impl}}`, and empty or whitespace-bearing segments. -/
def isValidCrateSegment (seg : String) : Bool :=
  match seg.toList with
  | [] => false
  | first :: rest =>
    (first.isAlpha || first == '_') &&
      rest.all (fun ch => ch.isAlphanum || ch == '_' || ch == '-')

/-- Normalize `pathSegments` by stripping a single leading root `::` (`::main`
    ↦ `["main"]`, `::my_crate::main` ↦ `["my_crate", "main"]`). Double root
    separators (`::::main`) leave an empty crate segment that
    `isValidCrateSegment` rejects. -/
def normalizeEntryPathSegments (defPath : String) : List String :=
  match pathSegments defPath with
  | "" :: rest => rest
  | segs => segs

/-- Link-level names under which a loader or C runtime transfers control to a
    binary: `main`, `_start`, and `__start`. -/
def isEntryLeafSymbol (leaf : String) : Bool :=
  leaf == "main" || leaf == "_start" || leaf == "__start"

/-- Name-only entry-point test: `main`, `::main`, `<crate>::main`,
    `::<crate>::main`, `_start`, `<crate>::_start`, `__start`,
    `<crate>::__start`. Matching is on whole path segments with a validated crate
    segment, so `domain`, `maintain`, `main_loop`, `<crate>::Type::main`,
    `<MyType as Trait>::main`, `{{impl}}::main`, and `:::main` are all rejected.
    This over-approximates `classifyEntryPoint` when no attribute information is
    available. -/
def isBinaryEntrySymbol (defPath : String) : Bool :=
  match normalizeEntryPathSegments defPath with
  | [leaf] => isEntryLeafSymbol leaf
  | [crateSeg, leaf] => isValidCrateSegment crateSeg && isEntryLeafSymbol leaf
  | _ => false

/-- Facts about an item that decide whether it is a binary entry point
    (`anneal_spec::spec_check::EntryPointDescriptor`). -/
structure EntryPointDescriptor : Type where
  /-- Crate-qualified definition path, e.g. `"my_crate::main"`. -/
  defPath : String
  /-- The crate is compiled with `#![no_main]`. -/
  crateNoMain : Bool := false
  /-- The item carries an entry attribute (`#[entry]`, `#[main]`, `#[start]`). -/
  hasEntryAttr : Bool := false
  /-- Exported link symbol when the item is `#[no_mangle]` or `#[export_name = ..]`. -/
  linkSymbol : Option String := none
  /-- The item is an associated function or method (`Type::main`). -/
  isAssocFn : Bool := false
  deriving DecidableEq, Repr

/-- Classify a crate-root item by its leaf name: `main` is always an entry point
    (the `std` runtime's under a default crate, the C runtime's under `#![no_main]`),
    and `_start` / `__start` are entry points under `#![no_main]`. -/
def classifyEntryLeaf (leaf : String) (crateNoMain : Bool) : Option EntryPointKind :=
  if leaf == "main" then
    some (if crateNoMain then .noMainStart else .rustMain)
  else if crateNoMain && (leaf == "_start" || leaf == "__start") then
    some .noMainStart
  else
    none

/-- Classify an item by its definition path alone: only crate-root items
    (`leaf`, `::leaf`, `<crate>::leaf`, `::<crate>::leaf` with a valid crate
    segment) can be entry points. -/
def classifyEntryPath (defPath : String) (crateNoMain : Bool) : Option EntryPointKind :=
  match normalizeEntryPathSegments defPath with
  | [leaf] => classifyEntryLeaf leaf crateNoMain
  | [crateSeg, leaf] =>
    if isValidCrateSegment crateSeg then classifyEntryLeaf leaf crateNoMain else none
  | _ => none

/-- Classify an item as a binary entry point
    (`anneal_spec::spec_check::classify_entry_point`):

    1. an associated function is never an entry point;
    2. an entry attribute makes the item a `customEntryAttr` entry point;
    3. an exported link symbol `main`, `_start`, or `__start` is a `noMainStart`
       entry point;
    4. otherwise the crate-root items `main` (always) and `_start` / `__start`
       (under `#![no_main]`) are entry points. -/
def classifyEntryPoint (d : EntryPointDescriptor) : Option EntryPointKind :=
  if d.isAssocFn then
    none
  else if d.hasEntryAttr then
    some .customEntryAttr
  else
    match d.linkSymbol with
    | some sym =>
      if isEntryLeafSymbol sym then some .noMainStart
      else classifyEntryPath d.defPath d.crateNoMain
    | none => classifyEntryPath d.defPath d.crateNoMain

/-- An associated function is never classified as an entry point. -/
theorem classifyEntryPoint_assocFn {d : EntryPointDescriptor} (h : d.isAssocFn = true) :
    classifyEntryPoint d = none := by
  simp [classifyEntryPoint, h]

/-- Whatever leaf `classifyEntryLeaf` accepts is an entry link symbol. -/
theorem isEntryLeafSymbol_of_classifyEntryLeaf {leaf : String} {crateNoMain : Bool}
    {kind : EntryPointKind} (h : classifyEntryLeaf leaf crateNoMain = some kind) :
    isEntryLeafSymbol leaf = true := by
  unfold isEntryLeafSymbol
  unfold classifyEntryLeaf at h
  by_cases hMain : (leaf == "main") = true
  · simp [hMain]
  · by_cases hStart : (crateNoMain && (leaf == "_start" || leaf == "__start")) = true
    · simp only [Bool.and_eq_true, Bool.or_eq_true] at hStart
      rcases hStart.2 with hS | hS <;> simp [hS]
    · simp [hMain, hStart] at h

/-- Path-based classification is sound for the name-only test: whatever
    `classifyEntryPath` accepts, `isBinaryEntrySymbol` accepts. -/
theorem isBinaryEntrySymbol_of_classifyEntryPath {defPath : String} {crateNoMain : Bool}
    {kind : EntryPointKind} (h : classifyEntryPath defPath crateNoMain = some kind) :
    isBinaryEntrySymbol defPath = true := by
  unfold classifyEntryPath at h
  unfold isBinaryEntrySymbol
  generalize normalizeEntryPathSegments defPath = segs at h
  match segs, h with
  | [], h => cases h
  | [_], h => exact isEntryLeafSymbol_of_classifyEntryLeaf h
  | [crateSeg, leaf], h =>
    by_cases hCrate : isValidCrateSegment crateSeg = true
    · simp only [hCrate, ↓reduceIte] at h
      simp only [hCrate, Bool.true_and]
      exact isEntryLeafSymbol_of_classifyEntryLeaf h
    · simp [hCrate] at h
  | _ :: _ :: _ :: _, h => cases h

/-! ### 3.2 Closed-Program Safety and the Guard -/

/-- Closed-program safety: the program runs without operational fault from *every*
    initial state the loader ABI may supply, not merely from those a `requires`
    clause selects. -/
def ClosedProgramSafe {Init : Type} (admissible : Init → Prop)
    (run : Init → ITree MirEffect MirOutcome) : Prop :=
  ∀ init, admissible init → TreeSafe (run init)

/-- The entry-point `requires` guard: the precondition holds on every ABI-admissible
    initial state, so no caller is needed to establish it. -/
def EntryPointRequiresGuard {Init : Type} (admissible pre : Init → Prop) : Prop :=
  ∀ init, admissible init → pre init

/-- A `requires` clause is non-universal when the loader may start the program in a
    state the clause excludes. -/
def EntryRequiresNonUniversal {Init : Type} (admissible pre : Init → Prop) : Prop :=
  ∃ init, admissible init ∧ ¬ pre init

/-- The guard fails exactly when the `requires` clause is non-universal. -/
theorem not_entryPointRequiresGuard_iff {Init : Type} {admissible pre : Init → Prop} :
    ¬ EntryPointRequiresGuard admissible pre ↔ EntryRequiresNonUniversal admissible pre := by
  constructor
  · intro hNot
    apply Classical.byContradiction
    intro hNone
    exact hNot fun init hAdm =>
      Classical.byContradiction fun hPre => hNone ⟨init, hAdm, hPre⟩
  · rintro ⟨init, hAdm, hPre⟩ hGuard
    exact hPre (hGuard init hAdm)

/-- Effective precondition of an entry point: the ABI admissibility predicate,
    conjoined with the authored `requires` clause when one is present. -/
def effectiveEntryPre {Init : Type} (hasExplicitRequires : Bool)
    (admissible explicit : Init → Prop) : Init → Prop :=
  if hasExplicitRequires then fun init => admissible init ∧ explicit init else admissible

/-- The guard holds when the precondition *is* the ABI admissibility predicate. -/
theorem entryPointRequiresGuard_refl {Init : Type} (admissible : Init → Prop) :
    EntryPointRequiresGuard admissible admissible :=
  fun _ hAdm => hAdm

/-- An entry point without an authored `requires` clause passes the guard. -/
theorem entryPointRequiresGuard_of_no_explicit_requires {Init : Type}
    (admissible explicit : Init → Prop) :
    EntryPointRequiresGuard admissible (effectiveEntryPre false admissible explicit) :=
  fun _ hAdm => hAdm

/-- An authored `requires` clause passes the guard exactly when the ABI already
    implies it, i.e. when it is trivial on the admissible states. -/
theorem entryPointRequiresGuard_explicit_iff {Init : Type}
    (admissible explicit : Init → Prop) :
    EntryPointRequiresGuard admissible (effectiveEntryPre true admissible explicit) ↔
      ∀ init, admissible init → explicit init :=
  ⟨fun h init hAdm => (h init hAdm).2, fun h init hAdm => ⟨hAdm, h init hAdm⟩⟩

/-- Strengthening the ABI assumption or weakening the precondition preserves the guard. -/
theorem EntryPointRequiresGuard.mono {Init : Type} {adm adm' pre pre' : Init → Prop}
    (h : EntryPointRequiresGuard adm pre) (hAdm : ∀ init, adm' init → adm init)
    (hPre : ∀ init, pre init → pre' init) : EntryPointRequiresGuard adm' pre' :=
  fun init hInit => hPre init (h init (hAdm init hInit))

/-! ### 3.3 Specialization to `Trusted.VerificationResult` Claims -/

/-- Closed-program safety of a stateless `Claim` over the argument ABI `admissible`. -/
def ClaimClosedProgramSafe (admissible : List Value → Prop) (c : Claim) : Prop :=
  ClosedProgramSafe admissible (fun args => mirCallTreeWithCallees c.body args c.callees)

/-- Closed-program functional correctness of a stateless `Claim`: every normal return
    from an ABI-admissible initial state satisfies the postcondition. -/
def ClaimClosedProgramCorrect (admissible : List Value → Prop) (c : Claim) : Prop :=
  ∀ args, admissible args → ∀ tr retVal mem',
    ReachesRet (mirCallTreeWithCallees c.body args c.callees) tr (.normal (retVal, mem')) →
      c.post args retVal

/-- The entry-point `requires` guard on a stateless `Claim`. -/
def ClaimEntryRequiresGuard (admissible : List Value → Prop) (c : Claim) : Prop :=
  EntryPointRequiresGuard admissible c.pre

/-- A verified `Claim` is safe on every input satisfying its precondition. -/
theorem treeSafe_of_verificationResult {c : Claim} (h : VerificationResult c)
    {args : List Value} (hPre : c.pre args) :
    TreeSafe (mirCallTreeWithCallees c.body args c.callees) :=
  (h.proof args hPre).1

/-- A verified `Claim` satisfies its postcondition on every normal return from an
    input satisfying its precondition. -/
theorem post_of_verificationResult {c : Claim} (h : VerificationResult c)
    {args : List Value} (hPre : c.pre args) {tr : List (Event MirEffect)}
    {retVal : Value} {mem' : Memory}
    (hRet : ReachesRet (mirCallTreeWithCallees c.body args c.callees) tr
      (.normal (retVal, mem'))) :
    c.post args retVal := by
  obtain ⟨hSafe, hVal⟩ := h.proof args hPre
  exact hVal (tr, .normal (retVal, mem')) hRet hPre retVal mem' rfl

/-- **Positive soundness (stateless).** The guard plus a `VerificationResult` gives
    closed-program safety on every ABI-admissible initial state. -/
theorem claimClosedProgramSafe_of_guard {admissible : List Value → Prop} {c : Claim}
    (hGuard : ClaimEntryRequiresGuard admissible c) (h : VerificationResult c) :
    ClaimClosedProgramSafe admissible c :=
  fun args hAdm => treeSafe_of_verificationResult h (hGuard args hAdm)

/-- **Positive soundness (stateless, functional).** The guard plus a
    `VerificationResult` gives the postcondition on every ABI-admissible run. -/
theorem claimClosedProgramCorrect_of_guard {admissible : List Value → Prop} {c : Claim}
    (hGuard : ClaimEntryRequiresGuard admissible c) (h : VerificationResult c) :
    ClaimClosedProgramCorrect admissible c :=
  fun args hAdm _ _ _ hRet => post_of_verificationResult h (hGuard args hAdm) hRet

/-- An entry point whose precondition is exactly the ABI admissibility predicate
    (no authored `requires`) is closed-program safe once verified. -/
theorem claimClosedProgramSafe_of_pre_eq_abi {admissible : List Value → Prop} {c : Claim}
    (hPre : c.pre = admissible) (h : VerificationResult c) :
    ClaimClosedProgramSafe admissible c :=
  claimClosedProgramSafe_of_guard (hPre ▸ entryPointRequiresGuard_refl c.pre) h

/-- Closed-program safety of a `StatefulClaim` over the `(args, memory)` ABI. -/
def StatefulClaimClosedProgramSafe (admissible : List Value → Memory → Prop)
    (c : StatefulClaim) : Prop :=
  ClosedProgramSafe (fun p : List Value × Memory => admissible p.1 p.2)
    (fun p => mirStatefulTreeWithCallees c.body p.1 p.2 c.callees)

/-- Closed-program functional correctness of a `StatefulClaim`. -/
def StatefulClaimClosedProgramCorrect (admissible : List Value → Memory → Prop)
    (c : StatefulClaim) : Prop :=
  ∀ args mem, admissible args mem → ∀ tr retVal mem',
    ReachesRet (mirStatefulTreeWithCallees c.body args mem c.callees) tr
        (.normal (retVal, mem')) →
      c.post args mem retVal mem'

/-- The entry-point `requires` guard on a `StatefulClaim`. -/
def StatefulClaimEntryRequiresGuard (admissible : List Value → Memory → Prop)
    (c : StatefulClaim) : Prop :=
  EntryPointRequiresGuard (fun p : List Value × Memory => admissible p.1 p.2)
    (fun p => c.pre p.1 p.2)

/-- **Positive soundness (stateful).** -/
theorem statefulClaimClosedProgramSafe_of_guard
    {admissible : List Value → Memory → Prop} {c : StatefulClaim}
    (hGuard : StatefulClaimEntryRequiresGuard admissible c)
    (h : StatefulVerificationResult c) :
    StatefulClaimClosedProgramSafe admissible c :=
  fun p hAdm => (h.proof p.1 p.2 (hGuard p hAdm)).1

/-- **Positive soundness (stateful, functional).** -/
theorem statefulClaimClosedProgramCorrect_of_guard
    {admissible : List Value → Memory → Prop} {c : StatefulClaim}
    (hGuard : StatefulClaimEntryRequiresGuard admissible c)
    (h : StatefulVerificationResult c) :
    StatefulClaimClosedProgramCorrect admissible c := by
  intro args mem hAdm tr retVal mem' hRet
  have hPre : c.pre args mem := hGuard (args, mem) hAdm
  obtain ⟨hSafe, hVal⟩ := h.proof args mem hPre
  exact hVal (tr, .normal (retVal, mem')) hRet hPre retVal mem' rfl

/-- Closed-program total correctness of a `TotalClaim`: from every ABI-admissible
    initial state the program is safe, productive, non-diverging, and returns only
    normally with the postcondition. -/
def TotalClaimClosedProgramTotal (admissible : List Value → Memory → Prop)
    (c : TotalClaim) : Prop :=
  ∀ args mem, admissible args mem →
    TreeSafe (mirStatefulTreeWithCallees c.body args mem c.callees) ∧
    Productive (mirStatefulTreeWithCallees c.body args mem c.callees) ∧
    ¬ MayDiverge (mirStatefulTreeWithCallees c.body args mem c.callees) ∧
    ∀ tr out,
      ReachesRet (mirStatefulTreeWithCallees c.body args mem c.callees) tr out →
        ∃ retVal mem', out = .normal (retVal, mem') ∧ c.post args mem retVal mem'

/-- The entry-point `requires` guard on a `TotalClaim`. -/
def TotalClaimEntryRequiresGuard (admissible : List Value → Memory → Prop)
    (c : TotalClaim) : Prop :=
  EntryPointRequiresGuard (fun p : List Value × Memory => admissible p.1 p.2)
    (fun p => c.pre p.1 p.2)

/-- **Positive soundness (total correctness).** -/
theorem totalClaimClosedProgramTotal_of_guard
    {admissible : List Value → Memory → Prop} {c : TotalClaim}
    (hGuard : TotalClaimEntryRequiresGuard admissible c)
    (h : TotalVerificationResult c) :
    TotalClaimClosedProgramTotal admissible c :=
  fun args mem hAdm => h.proof args mem (hGuard (args, mem) hAdm)

/-- Total closed-program correctness implies closed-program safety. -/
theorem TotalClaimClosedProgramTotal.closedProgramSafe
    {admissible : List Value → Memory → Prop} {c : TotalClaim}
    (h : TotalClaimClosedProgramTotal admissible c) :
    ClosedProgramSafe (fun p : List Value × Memory => admissible p.1 p.2)
      (fun p => mirStatefulTreeWithCallees c.body p.1 p.2 c.callees) :=
  fun p hAdm => (h p.1 p.2 hAdm).1

/-! ### 3.4 The Soundness Collapse -/

/-- **`verus#3606` collapse witness.** Every gate a specification is normally held to
    passes — the item is a binary entry point, its precondition is satisfiable
    (`NonVacuousPre`), its contract is dichotomous (`ClaimDichotomy`), and the claim
    is verified (`VerificationResult`) — and yet the loader may start the program in
    an ABI-admissible state outside `pre` on which it raises undefined behavior. -/
structure EntryRequiresSoundnessCollapse (admissible : List Value → Prop) (c : Claim) :
    Prop where
  /-- The verified item is a binary entry point. -/
  entrySymbol : isBinaryEntrySymbol c.body.defPath = true
  /-- `DeadPrecondition` does not fire: the precondition is satisfiable. -/
  nonVacuous : NonVacuousPre c.pre
  /-- `PostconditionDichotomy` holds: the contract is not vacuous. -/
  dichotomy : ClaimDichotomy c
  /-- The claim carries a kernel-checked certificate. -/
  verified : VerificationResult c
  /-- Some ABI-admissible initial state violates `pre` and raises `.ub`. -/
  escapes : ∃ args, admissible args ∧ ¬ c.pre args ∧
    FaultsWith (mirCallTreeWithCallees c.body args c.callees) .ub

/-- A collapse witness refutes the entry-point `requires` guard. -/
theorem EntryRequiresSoundnessCollapse.nonUniversal {admissible : List Value → Prop}
    {c : Claim} (h : EntryRequiresSoundnessCollapse admissible c) :
    EntryRequiresNonUniversal admissible c.pre :=
  let ⟨args, hAdm, hPre, _⟩ := h.escapes
  ⟨args, hAdm, hPre⟩

theorem EntryRequiresSoundnessCollapse.not_guard {admissible : List Value → Prop}
    {c : Claim} (h : EntryRequiresSoundnessCollapse admissible c) :
    ¬ ClaimEntryRequiresGuard admissible c :=
  not_entryPointRequiresGuard_iff.mpr h.nonUniversal

/-- A collapse witness refutes closed-program safety: the verified program has
    undefined behavior. -/
theorem EntryRequiresSoundnessCollapse.not_closedProgramSafe
    {admissible : List Value → Prop} {c : Claim}
    (h : EntryRequiresSoundnessCollapse admissible c) :
    ¬ ClaimClosedProgramSafe admissible c := by
  intro hSafe
  obtain ⟨args, hAdm, -, hFault⟩ := h.escapes
  exact hFault.not_treeSafe (hSafe args hAdm)

/-- **Stateful `verus#3606` collapse witness**: the `StatefulClaim` counterpart of
    `EntryRequiresSoundnessCollapse`. -/
structure StatefulEntryRequiresSoundnessCollapse
    (admissible : List Value → Memory → Prop) (c : StatefulClaim) : Prop where
  /-- The verified item is a binary entry point. -/
  entrySymbol : isBinaryEntrySymbol c.body.defPath = true
  /-- The stateful precondition is satisfiable. -/
  nonVacuous : NonVacuousStatefulPre c.pre
  /-- The stateful contract is dichotomous. -/
  dichotomy : StatefulClaimDichotomy c
  /-- The claim carries a kernel-checked certificate. -/
  verified : StatefulVerificationResult c
  /-- Some ABI-admissible initial `(args, memory)` violates `pre` and raises `.ub`. -/
  escapes : ∃ args mem, admissible args mem ∧ ¬ c.pre args mem ∧
    FaultsWith (mirStatefulTreeWithCallees c.body args mem c.callees) .ub

theorem StatefulEntryRequiresSoundnessCollapse.not_guard
    {admissible : List Value → Memory → Prop} {c : StatefulClaim}
    (h : StatefulEntryRequiresSoundnessCollapse admissible c) :
    ¬ StatefulClaimEntryRequiresGuard admissible c := by
  intro hGuard
  obtain ⟨args, mem, hAdm, hPre, -⟩ := h.escapes
  exact hPre (hGuard (args, mem) hAdm)

theorem StatefulEntryRequiresSoundnessCollapse.not_closedProgramSafe
    {admissible : List Value → Memory → Prop} {c : StatefulClaim}
    (h : StatefulEntryRequiresSoundnessCollapse admissible c) :
    ¬ StatefulClaimClosedProgramSafe admissible c := by
  intro hSafe
  obtain ⟨args, mem, hAdm, -, hFault⟩ := h.escapes
  exact hFault.not_treeSafe (hSafe (args, mem) hAdm)

/-- **Total-correctness `verus#3606` collapse witness**: even a kernel-checked
    `TotalVerificationResult` (UB-free, productive, non-diverging, panic-free) on
    a binary entry point collapses when its `requires` is non-universal. -/
structure TotalEntryRequiresSoundnessCollapse
    (admissible : List Value → Memory → Prop) (c : TotalClaim) : Prop where
  /-- The verified item is a binary entry point. -/
  entrySymbol : isBinaryEntrySymbol c.body.defPath = true
  /-- The stateful precondition is satisfiable. -/
  nonVacuous : NonVacuousStatefulPre c.pre
  /-- The total contract is dichotomous. -/
  dichotomy : TotalClaimDichotomy c
  /-- The claim carries a kernel-checked total-correctness certificate. -/
  verified : TotalVerificationResult c
  /-- Some ABI-admissible initial `(args, memory)` violates `pre` and raises `.ub`. -/
  escapes : ∃ args mem, admissible args mem ∧ ¬ c.pre args mem ∧
    FaultsWith (mirStatefulTreeWithCallees c.body args mem c.callees) .ub

theorem TotalEntryRequiresSoundnessCollapse.not_guard
    {admissible : List Value → Memory → Prop} {c : TotalClaim}
    (h : TotalEntryRequiresSoundnessCollapse admissible c) :
    ¬ TotalClaimEntryRequiresGuard admissible c := by
  intro hGuard
  obtain ⟨args, mem, hAdm, hPre, -⟩ := h.escapes
  exact hPre (hGuard (args, mem) hAdm)

theorem TotalEntryRequiresSoundnessCollapse.not_closedProgramTotal
    {admissible : List Value → Memory → Prop} {c : TotalClaim}
    (h : TotalEntryRequiresSoundnessCollapse admissible c) :
    ¬ TotalClaimClosedProgramTotal admissible c := by
  intro hTotal
  obtain ⟨args, mem, hAdm, -, hFault⟩ := h.escapes
  exact hFault.not_treeSafe (hTotal.closedProgramSafe (args, mem) hAdm)

/-! ### 3.5 A Concrete Collapse in `Trusted.Rustc.V2026_06_01.MirSemantics`

The entry point `extern "C" fn main(argc: u8) -> u8 { 1 / argc }` with
`requires argc == 1`. An `execve` with an empty argument vector starts it with
`argc == 0`, which is ABI-admissible and divides by zero. -/

/-- A MIR execution that takes one silent step and then returns `out` is safe and
    returns exactly `out`. -/
theorem mirTree_safe_of_step_tau_ret {body : CapturedMir} {s s' : MachineState}
    {out : MirOutcome}
    (h₀ : stepMirState body (.running s) = .tau (.running s'))
    (h₁ : stepMirState body (.running s') = .ret out) :
    TreeSafe (mirTree body s) ∧
      ∀ tr out', ReachesRet (mirTree body s) tr out' → out' = out := by
  have hObs₀ := cofix_observe_of_step_tau h₀
  have hObs₁ := cofix_observe_of_step_ret h₁
  refine ⟨treeSafe_of_observe_tau hObs₀ (treeSafe_of_observe_ret hObs₁), ?_⟩
  intro tr out' hRet
  exact (reachesRet_of_observe_ret hObs₁ (reachesRet_of_observe_tau hObs₀ hRet)).2

/-- A MIR execution that takes one silent step and then returns `out` is safe,
    reactively productive, non-diverging, and returns exactly `out`. -/
theorem mirTree_total_of_step_tau_ret {body : CapturedMir} {s s' : MachineState}
    {out : MirOutcome}
    (h₀ : stepMirState body (.running s) = .tau (.running s'))
    (h₁ : stepMirState body (.running s') = .ret out) :
    TreeSafe (mirTree body s) ∧
      Productive (mirTree body s) ∧
      ¬ MayDiverge (mirTree body s) ∧
      ∀ tr out', ReachesRet (mirTree body s) tr out' → out' = out := by
  have hObs₀ := cofix_observe_of_step_tau h₀
  have hObs₁ := cofix_observe_of_step_ret h₁
  obtain ⟨hSafe, hRet⟩ := mirTree_safe_of_step_tau_ret h₀ h₁
  exact ⟨hSafe,
    productive_of_observe_tau hObs₀ (productive_of_observe_ret hObs₁),
    not_mayDiverge_of_observe_tau hObs₀ (not_mayDiverge_of_observe_ret hObs₁),
    hRet⟩

namespace EntryDemo

/-- The MIR type `u8`. -/
def u8Ty : Ty := { kind := .uint .u8, layoutIdx := 0 }

/-- The constant operand `const n_u8`. -/
def u8Const (n : Nat) : Operand :=
  .constant { ty := u8Ty, val := .scalar (.int { bits := n, sizeBytes := 1 }) }

/-- One-byte scalar return layout. -/
def demoLayout : TypeLayout := {
  size := { bytes := 1 }
  align := { bytes := 1 }
  backendRepr := .memory
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

/-- `extern "C"`-style ABI record of the demo entry points. -/
def demoFnAbi : FnAbi := {
  args := []
  ret := { layout := demoLayout, mode := .direct }
  conv := .rust
  canUnwind := true
}

/-- The projection-free place `_idx`. -/
def localPlace (idx : Nat) : Place := { local_ := idx, projection := [] }

/-- A single-block body `bb0: _0 = <rvalue>; return` over `(_0 : u8, _1 : u8)`. -/
def singleAssignBody (defPath : DefPath) (rvalue : Rvalue) : CapturedMir := {
  defPath := defPath
  argCount := 1
  localDecls :=
    [ { mutability := .mut, ty := u8Ty, debugName := none },
      { mutability := .not, ty := u8Ty, debugName := none } ]
  basicBlocks :=
    [ { statements :=
          [ { kind := .assign (localPlace 0) rvalue, span := "SpecBoundaryGuards.lean" } ]
        terminator := { kind := .return_, span := "SpecBoundaryGuards.lean" }
        isCleanup := false } ]
  role := .subject
  phase := .runtimePostCleanup
  fnAbi := demoFnAbi
  layouts := emptyLayoutTable
  allocations := []
}

/-- `fn <entry>(argc: u8) -> u8 { 1 / argc }` in runtime MIR:
    `bb0: _0 = Div(const 1_u8, copy _1); return`. The zero-divisor check of
    surface Rust is a separate `Assert` terminator, so `Div` by zero is undefined
    behavior at this level. -/
def divEntryBody (defPath : DefPath) : CapturedMir :=
  singleAssignBody defPath (.binaryOp .div (u8Const 1) (.copy (localPlace 1)))

/-- `fn <entry>(argc: u8) -> u8 { argc }` in runtime MIR:
    `bb0: _0 = copy _1; return`. -/
def echoEntryBody (defPath : DefPath) : CapturedMir :=
  singleAssignBody defPath (.use (.copy (localPlace 1)))

/-- The argument vector `[argc]` for `argc = n`. -/
def u8Arg (n : Nat) : List Value := [.scalar { bits := n, sizeBytes := 1 }]

/-- Loader ABI of the demo entry points: exactly one `u8` argument, of any value.
    Nothing about the ABI excludes `argc == 0`. -/
def u8EntryAbi (args : List Value) : Prop := ∃ n, n < 256 ∧ args = u8Arg n

/-- Machine state after `bb0[0]` wrote `ret` to `_0` with argument `argc`. -/
def afterAssign (ret argc : Nat) : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 1
        locals :=
          [ .init (.scalar { bits := ret, sizeBytes := 1 }),
            .init (.scalar { bits := argc, sizeBytes := 1 }) ] }
    memory := {} }

/-- With `argc == 0` the very first step is `Div` by zero: `.ub`. -/
theorem divEntry_step_zero (defPath : DefPath) :
    stepMirState (divEntryBody defPath)
        (.running (initMachineStateWithCallees (divEntryBody defPath) (u8Arg 0) [])) =
      MirStepNode.fail .ub :=
  rfl

/-- With `argc == 1` the first step computes `1 / 1 = 1`. -/
theorem divEntry_step_one (defPath : DefPath) :
    stepMirState (divEntryBody defPath)
        (.running (initMachineStateWithCallees (divEntryBody defPath) (u8Arg 1) [])) =
      .tau (.running (afterAssign 1 1)) :=
  rfl

/-- The `return` terminator yields `_0`. -/
theorem divEntry_step_return (defPath : DefPath) :
    stepMirState (divEntryBody defPath) (.running (afterAssign 1 1)) =
      .ret (.normal (.scalar { bits := 1, sizeBytes := 1 }, {})) :=
  rfl

/-- **Concrete undefined behavior**: started with `argc == 0`, the division entry
    point raises `.ub` in `MirSemantics`. -/
theorem divEntry_faults_on_zero (defPath : DefPath) :
    FaultsWith (mirCallTreeWithCallees (divEntryBody defPath) (u8Arg 0) []) .ub :=
  faultsWith_of_step_fail (divEntry_step_zero defPath)

/-- The division entry point is not `TreeSafe` on `argc == 0`. -/
theorem divEntry_not_treeSafe_on_zero (defPath : DefPath) :
    ¬ TreeSafe (mirCallTreeWithCallees (divEntryBody defPath) (u8Arg 0) []) :=
  (divEntry_faults_on_zero defPath).not_treeSafe

/-- The verified claim `{argc == 1} <entry> {ret == 1}`. -/
def divEntryClaim (defPath : DefPath) : Claim where
  body := divEntryBody defPath
  pre := fun args => args = u8Arg 1
  post := fun _ ret => ret = .scalar { bits := 1, sizeBytes := 1 }

/-- `DeadPrecondition` does not fire on `divEntryClaim`. -/
theorem divEntryClaim_nonVacuousPre (defPath : DefPath) :
    NonVacuousPre (divEntryClaim defPath).pre :=
  ⟨u8Arg 1, rfl⟩

/-- `divEntryClaim` is dichotomous: it accepts `1` and rejects `()`. -/
theorem divEntryClaim_dichotomy (defPath : DefPath) :
    ClaimDichotomy (divEntryClaim defPath) :=
  ⟨u8Arg 1, rfl, ⟨.scalar { bits := 1, sizeBytes := 1 }, rfl⟩,
    ⟨.unit, fun h => Value.noConfusion h⟩⟩

/-- `divEntryClaim` is verified: under `argc == 1` the body is safe and returns `1`. -/
theorem divEntryClaim_verified (defPath : DefPath) :
    VerificationResult (divEntryClaim defPath) := by
  refine ⟨fun args hPre => ?_⟩
  have hArgs : args = u8Arg 1 := hPre
  subst hArgs
  obtain ⟨hSafe, hRet⟩ :=
    mirTree_safe_of_step_tau_ret (divEntry_step_one defPath) (divEntry_step_return defPath)
  refine ⟨hSafe, ?_⟩
  intro out hReach _ retVal mem' hOut
  have hEq := hRet out.1 out.2 hReach
  rw [hEq] at hOut
  cases hOut
  rfl

/-- **Negative soundness-collapse theorem.** For every binary entry symbol
    `defPath`, `divEntryClaim defPath` passes `NonVacuousPre`, `ClaimDichotomy`, and
    `VerificationResult`, while the ABI-admissible start `argc == 0` lies outside
    its `requires` and raises `.ub`. -/
theorem divEntryClaim_collapse (defPath : DefPath)
    (hEntry : isBinaryEntrySymbol defPath = true) :
    EntryRequiresSoundnessCollapse u8EntryAbi (divEntryClaim defPath) where
  entrySymbol := hEntry
  nonVacuous := divEntryClaim_nonVacuousPre defPath
  dichotomy := divEntryClaim_dichotomy defPath
  verified := divEntryClaim_verified defPath
  escapes := by
    refine ⟨u8Arg 0, ⟨0, by decide, rfl⟩, ?_, divEntry_faults_on_zero defPath⟩
    intro hPre
    have hArgs : u8Arg 0 = u8Arg 1 := hPre
    cases hArgs

/-- The collapse on a Rust `main`. -/
theorem main_requires_collapse :
    EntryRequiresSoundnessCollapse u8EntryAbi (divEntryClaim "entry_demo::main") :=
  divEntryClaim_collapse _ (by decide)

/-- The collapse on a `#![no_main]` `_start`. -/
theorem start_requires_collapse :
    EntryRequiresSoundnessCollapse u8EntryAbi (divEntryClaim "_start") :=
  divEntryClaim_collapse _ (by decide)

/-- Verification, precondition satisfiability, and postcondition dichotomy together
    do **not** imply closed-program safety of an entry point. -/
theorem verified_nonVacuous_dichotomy_not_closedProgramSafe :
    ¬ ∀ (admissible : List Value → Prop) (c : Claim),
        isBinaryEntrySymbol c.body.defPath = true → NonVacuousPre c.pre →
          ClaimDichotomy c → VerificationResult c → ClaimClosedProgramSafe admissible c :=
  fun hAll =>
    main_requires_collapse.not_closedProgramSafe
      (hAll u8EntryAbi _ main_requires_collapse.entrySymbol main_requires_collapse.nonVacuous
        main_requires_collapse.dichotomy main_requires_collapse.verified)

/-- The claim `{u8EntryAbi} <entry> {args == [ret]}` of the echo entry point: its
    precondition is the ABI itself, i.e. it has no authored `requires`. -/
def echoEntryClaim (defPath : DefPath) : Claim where
  body := echoEntryBody defPath
  pre := u8EntryAbi
  post := fun args ret => args = [ret]

theorem echoEntry_step_assign (defPath : DefPath) (n : Nat) :
    stepMirState (echoEntryBody defPath)
        (.running (initMachineStateWithCallees (echoEntryBody defPath) (u8Arg n) [])) =
      .tau (.running (afterAssign n n)) :=
  rfl

theorem echoEntry_step_return (defPath : DefPath) (n : Nat) :
    stepMirState (echoEntryBody defPath) (.running (afterAssign n n)) =
      .ret (.normal (.scalar { bits := n, sizeBytes := 1 }, {})) :=
  rfl

/-- The echo entry point is verified on the whole ABI. -/
theorem echoEntryClaim_verified (defPath : DefPath) :
    VerificationResult (echoEntryClaim defPath) := by
  refine ⟨fun args hPre => ?_⟩
  obtain ⟨n, -, rfl⟩ : u8EntryAbi args := hPre
  obtain ⟨hSafe, hRet⟩ :=
    mirTree_safe_of_step_tau_ret (echoEntry_step_assign defPath n)
      (echoEntry_step_return defPath n)
  refine ⟨hSafe, ?_⟩
  intro out hReach _ retVal mem' hOut
  have hEq := hRet out.1 out.2 hReach
  rw [hEq] at hOut
  cases hOut
  rfl

/-- **Positive instance.** The echo entry point passes the guard and is therefore
    closed-program safe on every ABI-admissible start, `argc == 0` included. -/
theorem echoEntry_closedProgramSafe (defPath : DefPath) :
    ClaimClosedProgramSafe u8EntryAbi (echoEntryClaim defPath) :=
  claimClosedProgramSafe_of_pre_eq_abi rfl (echoEntryClaim_verified defPath)

/-- The echo entry point passes the guard; the division entry point does not. -/
theorem echoEntry_guard (defPath : DefPath) :
    ClaimEntryRequiresGuard u8EntryAbi (echoEntryClaim defPath) :=
  entryPointRequiresGuard_refl u8EntryAbi

/-- Loader ABI of the stateful demo: one `u8` argument and the empty initial memory. -/
def u8StatefulEntryAbi (args : List Value) (mem : Memory) : Prop :=
  u8EntryAbi args ∧ mem = emptyMemory

/-- The verified stateful claim `{argc == 1 ∧ mem == ∅} <entry> {ret == 1 ∧ mem' == ∅}`. -/
def divEntryStatefulClaim (defPath : DefPath) : StatefulClaim where
  body := divEntryBody defPath
  pre := fun args mem => args = u8Arg 1 ∧ mem = emptyMemory
  post := fun _ _ ret mem' => ret = .scalar { bits := 1, sizeBytes := 1 } ∧ mem' = emptyMemory

theorem divEntry_stateful_step_zero (defPath : DefPath) :
    stepMirState (divEntryBody defPath)
        (.running (initMachineStateWithMemoryAndCallees (divEntryBody defPath) (u8Arg 0)
          emptyMemory [])) =
      MirStepNode.fail .ub :=
  rfl

theorem divEntry_stateful_step_one (defPath : DefPath) :
    stepMirState (divEntryBody defPath)
        (.running (initMachineStateWithMemoryAndCallees (divEntryBody defPath) (u8Arg 1)
          emptyMemory [])) =
      .tau (.running (afterAssign 1 1)) :=
  rfl

/-- `divEntryStatefulClaim` is verified. -/
theorem divEntryStatefulClaim_verified (defPath : DefPath) :
    StatefulVerificationResult (divEntryStatefulClaim defPath) := by
  refine ⟨fun args mem hPre => ?_⟩
  obtain ⟨hArgs, hMem⟩ : args = u8Arg 1 ∧ mem = emptyMemory := hPre
  subst hArgs hMem
  obtain ⟨hSafe, hRet⟩ :=
    mirTree_safe_of_step_tau_ret (divEntry_stateful_step_one defPath)
      (divEntry_step_return defPath)
  refine ⟨hSafe, ?_⟩
  intro out hReach _ retVal mem' hOut
  have hEq := hRet out.1 out.2 hReach
  rw [hEq] at hOut
  cases hOut
  exact ⟨rfl, rfl⟩

/-- **Negative soundness-collapse theorem (stateful).** -/
theorem divEntryStatefulClaim_collapse (defPath : DefPath)
    (hEntry : isBinaryEntrySymbol defPath = true) :
    StatefulEntryRequiresSoundnessCollapse u8StatefulEntryAbi
      (divEntryStatefulClaim defPath) where
  entrySymbol := hEntry
  nonVacuous := ⟨u8Arg 1, emptyMemory, rfl, rfl⟩
  dichotomy :=
    ⟨(u8Arg 1, emptyMemory), ⟨rfl, rfl⟩,
      ⟨(.scalar { bits := 1, sizeBytes := 1 }, emptyMemory), ⟨rfl, rfl⟩⟩,
      ⟨(.unit, emptyMemory), fun h => Value.noConfusion h.1⟩⟩
  verified := divEntryStatefulClaim_verified defPath
  escapes := by
    refine ⟨u8Arg 0, emptyMemory, ⟨⟨0, by decide, rfl⟩, rfl⟩, ?_,
      faultsWith_of_step_fail (divEntry_stateful_step_zero defPath)⟩
    intro hPre
    have hArgs : u8Arg 0 = u8Arg 1 := hPre.1
    cases hArgs

/-- The stateful collapse on a `#![no_main]` `_start`. -/
theorem start_requires_stateful_collapse :
    StatefulEntryRequiresSoundnessCollapse u8StatefulEntryAbi
      (divEntryStatefulClaim "_start") :=
  divEntryStatefulClaim_collapse _ (by decide)

/-- The verified total-correctness claim
    `{argc == 1 ∧ mem == ∅} <entry> {ret == 1 ∧ mem' == ∅}`. -/
def divEntryTotalClaim (defPath : DefPath) : TotalClaim where
  body := divEntryBody defPath
  pre := fun args mem => args = u8Arg 1 ∧ mem = emptyMemory
  post := fun _ _ ret mem' => ret = .scalar { bits := 1, sizeBytes := 1 } ∧ mem' = emptyMemory

/-- `divEntryTotalClaim` carries a kernel-checked `TotalVerificationResult`. -/
theorem divEntryTotalClaim_verified (defPath : DefPath) :
    TotalVerificationResult (divEntryTotalClaim defPath) := by
  refine ⟨fun args mem hPre => ?_⟩
  obtain ⟨hArgs, hMem⟩ : args = u8Arg 1 ∧ mem = emptyMemory := hPre
  subst hArgs hMem
  obtain ⟨hSafe, hProd, hNoDiv, hRet⟩ :=
    mirTree_total_of_step_tau_ret (divEntry_stateful_step_one defPath)
      (divEntry_step_return defPath)
  refine ⟨hSafe, hProd, hNoDiv, ?_⟩
  intro tr out hReach
  have hEq := hRet tr out hReach
  exact ⟨.scalar { bits := 1, sizeBytes := 1 }, emptyMemory, hEq, rfl, rfl⟩

/-- **Negative soundness-collapse theorem (total correctness).** -/
theorem divEntryTotalClaim_collapse (defPath : DefPath)
    (hEntry : isBinaryEntrySymbol defPath = true) :
    TotalEntryRequiresSoundnessCollapse u8StatefulEntryAbi
      (divEntryTotalClaim defPath) where
  entrySymbol := hEntry
  nonVacuous := ⟨u8Arg 1, emptyMemory, rfl, rfl⟩
  dichotomy :=
    ⟨(u8Arg 1, emptyMemory), ⟨rfl, rfl⟩,
      ⟨(.scalar { bits := 1, sizeBytes := 1 }, emptyMemory), ⟨rfl, rfl⟩⟩,
      ⟨(.unit, emptyMemory), fun h => Value.noConfusion h.1⟩⟩
  verified := divEntryTotalClaim_verified defPath
  escapes := by
    refine ⟨u8Arg 0, emptyMemory, ⟨⟨0, by decide, rfl⟩, rfl⟩, ?_,
      faultsWith_of_step_fail (divEntry_stateful_step_zero defPath)⟩
    intro hPre
    have hArgs : u8Arg 0 = u8Arg 1 := hPre.1
    cases hArgs

/-- The total-correctness collapse on `main`. -/
theorem main_requires_total_collapse :
    TotalEntryRequiresSoundnessCollapse u8StatefulEntryAbi
      (divEntryTotalClaim "entry_demo::main") :=
  divEntryTotalClaim_collapse _ (by decide)

/-- The total-correctness collapse on `#![no_main]` `_start`. -/
theorem start_requires_total_collapse :
    TotalEntryRequiresSoundnessCollapse u8StatefulEntryAbi
      (divEntryTotalClaim "_start") :=
  divEntryTotalClaim_collapse _ (by decide)

/-- Even `TotalVerificationResult`, precondition satisfiability, and dichotomy do
    not imply closed-program total correctness of an entry point without the guard. -/
theorem totalVerified_nonVacuous_dichotomy_not_closedProgramTotal :
    ¬ ∀ (admissible : List Value → Memory → Prop) (c : TotalClaim),
        isBinaryEntrySymbol c.body.defPath = true → NonVacuousStatefulPre c.pre →
          TotalClaimDichotomy c → TotalVerificationResult c →
            TotalClaimClosedProgramTotal admissible c :=
  fun hAll =>
    main_requires_total_collapse.not_closedProgramTotal
      (hAll u8StatefulEntryAbi _ main_requires_total_collapse.entrySymbol
        main_requires_total_collapse.nonVacuous main_requires_total_collapse.dichotomy
        main_requires_total_collapse.verified)

end EntryDemo

/-! ## 4. Guard 2 — Fixed-Width Ghost Length (`Slate` Soundness Bug 121)

A ghost `List` / `Set` / `Map` / `Seq` is a mathematical object: it may have any
natural number of elements. Typing its length or cardinality as `u64` / `usize`
(`UInt64` / `USize`) makes the length wrap at `2 ^ 64`, so a collection with
`2 ^ 64` elements reports length `0`. The standard inductive collection axioms
("length zero means empty", "appending strictly increases the length") are then
inconsistent, and a fully kernel-checked proof may derive `False`. -/

/-! ### 4.1 Ghost Integer Widths and the Guard -/

/-- The integer type a ghost length or cardinality is stated at. -/
inductive GhostIntWidth : Type where
  /-- Fixed-width unsigned machine integer of `bits` bits (`u64`, `UInt64`, `BitVec n`). -/
  | fixedUnsigned (bits : Nat)
  /-- Fixed-width signed machine integer of `bits` bits (`i64`, `Int64`). -/
  | fixedSigned (bits : Nat)
  /-- Unbounded natural number (`Nat`). -/
  | unboundedNat
  /-- Unbounded integer (`Int`). -/
  | unboundedInt
  deriving DecidableEq, Repr, Inhabited

namespace GhostIntWidth

/-- Whether the width is an unbounded mathematical integer type. -/
def isUnbounded : GhostIntWidth → Bool
  | .fixedUnsigned _ => false
  | .fixedSigned _ => false
  | .unboundedNat => true
  | .unboundedInt => true

/-- The non-negative mathematical values a length of this width can denote. -/
def Represents : GhostIntWidth → Nat → Prop
  | .fixedUnsigned bits, n => n < 2 ^ bits
  | .fixedSigned bits, n => n < 2 ^ (bits - 1)
  | .unboundedNat, _ => True
  | .unboundedInt, _ => True

/-- Number of distinct non-negative values of the width, `none` when unbounded. -/
def capacity? : GhostIntWidth → Option Nat
  | .fixedUnsigned bits => some (2 ^ bits)
  | .fixedSigned bits => some (2 ^ (bits - 1))
  | .unboundedNat => none
  | .unboundedInt => none

/-- Width denoted by a spelled Lean or Rust integer type name. Pointer-sized types
    are modeled at 64 bits, the widest pointer width Rust supports; a narrower
    target wraps sooner. `BitVec n` is `fixedUnsigned n`. -/
def ofTypeName? : String → Option GhostIntWidth
  | "Nat" => some .unboundedNat
  | "Int" => some .unboundedInt
  | "UInt8" => some (.fixedUnsigned 8)
  | "UInt16" => some (.fixedUnsigned 16)
  | "UInt32" => some (.fixedUnsigned 32)
  | "UInt64" => some (.fixedUnsigned 64)
  | "USize" => some (.fixedUnsigned 64)
  | "Int8" => some (.fixedSigned 8)
  | "Int16" => some (.fixedSigned 16)
  | "Int32" => some (.fixedSigned 32)
  | "Int64" => some (.fixedSigned 64)
  | "ISize" => some (.fixedSigned 64)
  | "u8" => some (.fixedUnsigned 8)
  | "u16" => some (.fixedUnsigned 16)
  | "u32" => some (.fixedUnsigned 32)
  | "u64" => some (.fixedUnsigned 64)
  | "u128" => some (.fixedUnsigned 128)
  | "usize" => some (.fixedUnsigned 64)
  | "i8" => some (.fixedSigned 8)
  | "i16" => some (.fixedSigned 16)
  | "i32" => some (.fixedSigned 32)
  | "i64" => some (.fixedSigned 64)
  | "i128" => some (.fixedSigned 128)
  | "isize" => some (.fixedSigned 64)
  | _ => none

end GhostIntWidth

/-- The ghost length type guard: a ghost collection length or cardinality must be
    stated at an unbounded type (`Nat` or `Int`). -/
def GhostLengthTypeGuard (w : GhostIntWidth) : Prop :=
  w.isUnbounded = true

instance : DecidablePred GhostLengthTypeGuard :=
  fun w => inferInstanceAs (Decidable (w.isUnbounded = true))

theorem ghostLengthTypeGuard_iff (w : GhostIntWidth) :
    GhostLengthTypeGuard w ↔ w = .unboundedNat ∨ w = .unboundedInt := by
  cases w <;> simp [GhostLengthTypeGuard, GhostIntWidth.isUnbounded]

theorem ghostLengthTypeGuard_unboundedNat : GhostLengthTypeGuard .unboundedNat := rfl

theorem ghostLengthTypeGuard_unboundedInt : GhostLengthTypeGuard .unboundedInt := rfl

/-- Every fixed-width unsigned type is rejected. -/
theorem not_ghostLengthTypeGuard_fixedUnsigned (bits : Nat) :
    ¬ GhostLengthTypeGuard (.fixedUnsigned bits) :=
  fun h => Bool.noConfusion h

/-- Every fixed-width signed type is rejected. -/
theorem not_ghostLengthTypeGuard_fixedSigned (bits : Nat) :
    ¬ GhostLengthTypeGuard (.fixedSigned bits) :=
  fun h => Bool.noConfusion h

/-- The guard accepts exactly the widths without a finite capacity. -/
theorem ghostLengthTypeGuard_iff_capacity_none (w : GhostIntWidth) :
    GhostLengthTypeGuard w ↔ w.capacity? = none := by
  cases w <;> simp [GhostLengthTypeGuard, GhostIntWidth.isUnbounded, GhostIntWidth.capacity?]

/-- A representable value lies strictly below the finite capacity. -/
theorem GhostIntWidth.lt_capacity_of_represents {w : GhostIntWidth} {cap n : Nat}
    (hCap : w.capacity? = some cap) (hRep : w.Represents n) : n < cap := by
  cases w with
  | fixedUnsigned bits => cases hCap; exact hRep
  | fixedSigned bits => cases hCap; exact hRep
  | unboundedNat => cases hCap
  | unboundedInt => cases hCap

/-- Fixed-width integer type names the ghost-length scanners flag
    (`cargo_anneal::property_registry::FIXED_WIDTH_GHOST_INT_TYPE_NAMES`). -/
def fixedWidthGhostTypeNames : List String :=
  ["UInt8", "UInt16", "UInt32", "UInt64", "USize", "Int8", "Int16", "Int32", "Int64", "ISize",
    "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize"]

/-- Unbounded integer type names the ghost-length scanners accept. -/
def unboundedGhostTypeNames : List String := ["Nat", "Int"]

/-- Guard verdict on a spelled type name: `some true` accepts, `some false` rejects,
    and `none` means the name is not a recognized integer type. -/
def ghostLengthTypeNameVerdict? (name : String) : Option Bool :=
  (GhostIntWidth.ofTypeName? name).map GhostIntWidth.isUnbounded

/-- Every flagged fixed-width type name is recognized and rejected. -/
theorem fixedWidthGhostTypeNames_rejected :
    fixedWidthGhostTypeNames.all (fun name => ghostLengthTypeNameVerdict? name == some false) =
      true := by
  decide

/-- Both unbounded type names are recognized and accepted. -/
theorem unboundedGhostTypeNames_accepted :
    unboundedGhostTypeNames.all (fun name => ghostLengthTypeNameVerdict? name == some true) =
      true := by
  decide

/-! ### 4.2 The `2 ^ 64` Wraparound -/

/-- A ghost length stored in a `u64`: the cardinality `n` truncated to 64 bits. -/
def u64GhostLen (n : Nat) : UInt64 := UInt64.ofNat n

/-- The `u64` ghost length of a list. -/
def u64ListGhostLen {α : Type u} (xs : List α) : UInt64 := u64GhostLen xs.length

theorem two_pow_64_eq : (2 : Nat) ^ 64 = 18446744073709551616 := by decide

theorem two_pow_64_pos : 0 < (2 : Nat) ^ 64 := by decide

/-- **The wraparound.** At cardinality `2 ^ 64` the `u64` ghost length is `0`, even
    though `2 ^ 64 > 0`. -/
theorem u64GhostLen_two_pow_64 : u64GhostLen (2 ^ 64) = 0 := by decide

/-- The largest representable cardinality does not wrap. -/
theorem u64GhostLen_two_pow_64_sub_one :
    (u64GhostLen (2 ^ 64 - 1)).toNat = 2 ^ 64 - 1 := by decide

/-- The `u64` ghost length is the cardinality modulo `2 ^ 64`. -/
theorem u64GhostLen_toNat (n : Nat) : (u64GhostLen n).toNat = n % 2 ^ 64 := by
  simp [u64GhostLen]

/-- A list of `2 ^ 64` elements has `u64` ghost length `0`. -/
theorem u64ListGhostLen_replicate_two_pow_64 {α : Type u} (x : α) :
    u64ListGhostLen (List.replicate (2 ^ 64) x) = 0 := by
  unfold u64ListGhostLen
  rw [List.length_replicate]
  exact u64GhostLen_two_pow_64

/-- A list of `2 ^ 64` elements is not empty. -/
theorem replicate_two_pow_64_ne_nil {α : Type u} (x : α) :
    List.replicate (2 ^ 64) x ≠ [] := by
  intro h
  have hLen : (List.replicate (2 ^ 64) x).length = ([] : List α).length := congrArg List.length h
  rw [List.length_replicate] at hLen
  have hZero : (2 : Nat) ^ 64 = 0 := hLen
  exact absurd hZero (by decide)

/-- **`False` from the `u64` list length.** The axiom "a list of length zero is
    empty", stated for the `u64` ghost length, is inconsistent. -/
theorem false_of_u64_list_len_zero_imp_nil {α : Type u} (x : α)
    (hAxiom : ∀ xs : List α, u64ListGhostLen xs = 0 → xs = []) : False :=
  replicate_two_pow_64_ne_nil x (hAxiom _ (u64ListGhostLen_replicate_two_pow_64 x))

/-- A ghost length stored in a target pointer-sized `USize`. -/
def usizeGhostLen (n : Nat) : USize := USize.ofNat n

/-- The `USize` ghost length of a list. -/
def usizeListGhostLen {α : Type u} (xs : List α) : USize := usizeGhostLen xs.length

/-- **`USize` wraparound at every target pointer width.** `USize.ofNat USize.size = 0`,
    whether the platform is 32-bit or 64-bit. -/
theorem usizeGhostLen_wraps : usizeGhostLen USize.size = 0 := by
  apply USize.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  simp [usizeGhostLen, USize.size]

theorem usize_size_pos : 0 < USize.size := by
  rw [USize.size]
  exact Nat.two_pow_pos _

/-- A list of `USize.size` elements has `USize` ghost length `0`. -/
theorem usizeListGhostLen_replicate_size {α : Type u} (x : α) :
    usizeListGhostLen (List.replicate USize.size x) = 0 := by
  unfold usizeListGhostLen
  rw [List.length_replicate]
  exact usizeGhostLen_wraps

/-- A list of `USize.size` elements is not empty. -/
theorem replicate_usize_size_ne_nil {α : Type u} (x : α) :
    List.replicate USize.size x ≠ [] := by
  intro h
  have hLen : (List.replicate USize.size x).length = ([] : List α).length :=
    congrArg List.length h
  rw [List.length_replicate] at hLen
  exact Nat.ne_of_gt usize_size_pos hLen

/-- **`False` from the `USize` list length** at every target pointer width. -/
theorem false_of_usize_list_len_zero_imp_nil {α : Type u} (x : α)
    (hAxiom : ∀ xs : List α, usizeListGhostLen xs = 0 → xs = []) : False :=
  replicate_usize_size_ne_nil x (hAxiom _ (usizeListGhostLen_replicate_size x))

/-- A ghost length stored in a `BitVec w`. -/
def bitVecGhostLen (w n : Nat) : BitVec w := BitVec.ofNat w n

/-- The `BitVec w` ghost length of a list. -/
def bitVecListGhostLen (w : Nat) {α : Type u} (xs : List α) : BitVec w :=
  bitVecGhostLen w xs.length

/-- **`BitVec w` wraparound at every width `w`.** -/
theorem bitVecGhostLen_two_pow (w : Nat) : bitVecGhostLen w (2 ^ w) = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [bitVecGhostLen]

/-- Concrete `BitVec 64` wraparound at `2 ^ 64`. -/
theorem bitVec64GhostLen_two_pow_64 : bitVecGhostLen 64 (2 ^ 64) = 0 :=
  bitVecGhostLen_two_pow 64

/-- **`False` from a `BitVec w` ghost list length** at every width `w`. -/
theorem false_of_bitVec_list_len_zero_imp_nil (w : Nat) {α : Type u} (x : α)
    (hAxiom : ∀ xs : List α, bitVecListGhostLen w xs = 0 → xs = []) : False := by
  have hNil : List.replicate (2 ^ w) x = [] := hAxiom _ (by
    unfold bitVecListGhostLen
    rw [List.length_replicate]
    exact bitVecGhostLen_two_pow w)
  have hLen : (List.replicate (2 ^ w) x).length = ([] : List α).length :=
    congrArg List.length hNil
  rw [List.length_replicate] at hLen
  exact Nat.ne_of_gt (Nat.two_pow_pos w) hLen

/-! ### 4.3 `False` from Fixed-Width Ghost Collection Axioms -/

/-- `n`-fold application of `snoc` to `c`. -/
def iterSnoc {Coll : Type u} (snoc : Coll → Coll) (n : Nat) (c : Coll) : Coll :=
  Nat.repeat snoc n c

theorem iterSnoc_zero {Coll : Type u} (snoc : Coll → Coll) (c : Coll) :
    iterSnoc snoc 0 c = c := rfl

theorem iterSnoc_succ {Coll : Type u} (snoc : Coll → Coll) (n : Nat) (c : Coll) :
    iterSnoc snoc (n + 1) c = snoc (iterSnoc snoc n c) := rfl

theorem iterSnoc_of_pos {Coll : Type u} (snoc : Coll → Coll) {n : Nat} (hn : 0 < n)
    (c : Coll) : iterSnoc snoc n c = snoc (iterSnoc snoc (n - 1) c) := by
  cases n with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ k => rfl

/-- Base axioms of a ghost collection whose length has the fixed width `w`: the
    length takes values in `Fin (2 ^ w)`, is `0` on the empty collection, and
    advances by one modulo `2 ^ w` on every `snoc`. These axioms alone are
    consistent (`fixedWidthGhostCollectionAxioms_nonempty`). -/
structure FixedWidthGhostCollectionAxioms (Coll : Type u) (w : Nat) where
  /-- The empty collection. -/
  empty : Coll
  /-- Append one element. -/
  snoc : Coll → Coll
  /-- Emptiness predicate. -/
  IsEmpty : Coll → Prop
  /-- Fixed-width length. -/
  len : Coll → Fin (2 ^ w)
  /-- The empty collection has length `0`. -/
  len_empty : (len empty).val = 0
  /-- `snoc` advances the length by one, modulo `2 ^ w`. -/
  len_snoc : ∀ c, (len (snoc c)).val = ((len c).val + 1) % 2 ^ w

namespace FixedWidthGhostCollectionAxioms

variable {Coll : Type u} {w : Nat}

/-- Standard inductive axiom pair: a collection of length zero is empty, and a
    collection built by `snoc` is not. -/
def ZeroLenIsEmpty (A : FixedWidthGhostCollectionAxioms Coll w) : Prop :=
  (∀ c, (A.len c).val = 0 → A.IsEmpty c) ∧ ∀ c, ¬ A.IsEmpty (A.snoc c)

/-- Standard inductive axiom: `snoc` strictly increases the length. -/
def LenStrictMono (A : FixedWidthGhostCollectionAxioms Coll w) : Prop :=
  ∀ c, A.len c < A.len (A.snoc c)

/-- The length after `n` appends is `n` modulo `2 ^ w`. -/
theorem len_iterSnoc (A : FixedWidthGhostCollectionAxioms Coll w) (n : Nat) :
    (A.len (iterSnoc A.snoc n A.empty)).val = n % 2 ^ w := by
  induction n with
  | zero =>
    show (A.len A.empty).val = 0 % 2 ^ w
    rw [A.len_empty, Nat.zero_mod]
  | succ n ih =>
    show (A.len (A.snoc (iterSnoc A.snoc n A.empty))).val = (n + 1) % 2 ^ w
    rw [A.len_snoc, ih, Nat.mod_add_mod]

/-- After `2 ^ w` appends the length has wrapped back to `0`. -/
theorem len_wraps (A : FixedWidthGhostCollectionAxioms Coll w) :
    (A.len (iterSnoc A.snoc (2 ^ w) A.empty)).val = 0 := by
  rw [A.len_iterSnoc, Nat.mod_self]

/-- Under strict monotonicity the length after `n` appends is at least `n`. -/
theorem le_len_iterSnoc_of_strictMono (A : FixedWidthGhostCollectionAxioms Coll w)
    (h : A.LenStrictMono) (n : Nat) : n ≤ (A.len (iterSnoc A.snoc n A.empty)).val := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have hStep : (A.len (iterSnoc A.snoc n A.empty)).val <
        (A.len (A.snoc (iterSnoc A.snoc n A.empty))).val := h _
    exact Nat.lt_of_le_of_lt ih hStep

end FixedWidthGhostCollectionAxioms

/-- **`False` from "zero length means empty".** A fixed-width ghost length together
    with the standard emptiness axioms is inconsistent: after `2 ^ w` appends the
    length is `0`, so the collection is "empty", yet it was built by `snoc`. -/
theorem false_of_fixedWidth_ghost_length_zero_empty {Coll : Type u} {w : Nat}
    (A : FixedWidthGhostCollectionAxioms Coll w) (h : A.ZeroLenIsEmpty) : False := by
  have hEmpty : A.IsEmpty (iterSnoc A.snoc (2 ^ w) A.empty) := h.1 _ A.len_wraps
  rw [iterSnoc_of_pos A.snoc (Nat.two_pow_pos w)] at hEmpty
  exact h.2 _ hEmpty

/-- **`False` from strict monotonicity.** A fixed-width ghost length cannot strictly
    increase on every `snoc`: after `2 ^ w` appends it would be at least `2 ^ w`. -/
theorem false_of_fixedWidth_ghost_length_strict_mono {Coll : Type u} {w : Nat}
    (A : FixedWidthGhostCollectionAxioms Coll w) (h : A.LenStrictMono) : False :=
  absurd (A.len (iterSnoc A.snoc (2 ^ w) A.empty)).isLt
    (Nat.not_lt.mpr (A.le_len_iterSnoc_of_strictMono h (2 ^ w)))

/-- The `u64` / `usize` instance of `false_of_fixedWidth_ghost_length_zero_empty`. -/
theorem false_of_u64_ghost_length_zero_empty {Coll : Type u}
    (A : FixedWidthGhostCollectionAxioms Coll 64) (h : A.ZeroLenIsEmpty) : False :=
  false_of_fixedWidth_ghost_length_zero_empty A h

/-- The `u64` / `usize` instance of `false_of_fixedWidth_ghost_length_strict_mono`. -/
theorem false_of_u64_ghost_length_strict_mono {Coll : Type u}
    (A : FixedWidthGhostCollectionAxioms Coll 64) (h : A.LenStrictMono) : False :=
  false_of_fixedWidth_ghost_length_strict_mono A h

/-- The modular counter model of the base axioms: collections are element counts. -/
def modCounterAxioms (w : Nat) : FixedWidthGhostCollectionAxioms Nat w where
  empty := 0
  snoc := Nat.succ
  IsEmpty := fun n => n = 0
  len := fun n => ⟨n % 2 ^ w, Nat.mod_lt n (Nat.two_pow_pos w)⟩
  len_empty := Nat.zero_mod _
  len_snoc := fun n => (Nat.mod_add_mod n (2 ^ w) 1).symm

/-- The base axioms are consistent at every width: the inconsistency is caused by
    adding the inductive axioms, not by the base axioms themselves. -/
theorem fixedWidthGhostCollectionAxioms_nonempty (w : Nat) :
    Nonempty (FixedWidthGhostCollectionAxioms Nat w) :=
  ⟨modCounterAxioms w⟩

/-- The modular counter model satisfies neither inductive axiom. -/
theorem modCounterAxioms_not_zeroLenIsEmpty (w : Nat) :
    ¬ (modCounterAxioms w).ZeroLenIsEmpty :=
  false_of_fixedWidth_ghost_length_zero_empty _

theorem modCounterAxioms_not_lenStrictMono (w : Nat) :
    ¬ (modCounterAxioms w).LenStrictMono :=
  false_of_fixedWidth_ghost_length_strict_mono _

/-! ### 4.4 Unbounded `Nat` / `Int` Ghost Lengths Are Sound -/

/-- The full inductive axiom set of a ghost collection with an unbounded `Nat`
    length. Unlike the fixed-width set it has a model. -/
structure UnboundedGhostCollectionAxioms (Coll : Type u) where
  /-- The empty collection. -/
  empty : Coll
  /-- Append one element. -/
  snoc : Coll → Coll
  /-- Emptiness predicate. -/
  IsEmpty : Coll → Prop
  /-- Unbounded length. -/
  len : Coll → Nat
  /-- The empty collection has length `0`. -/
  len_empty : len empty = 0
  /-- `snoc` advances the length by exactly one. -/
  len_snoc : ∀ c, len (snoc c) = len c + 1
  /-- `snoc` strictly increases the length. -/
  len_strict_mono : ∀ c, len c < len (snoc c)
  /-- Length zero characterizes emptiness. -/
  len_zero_iff_isEmpty : ∀ c, len c = 0 ↔ IsEmpty c
  /-- A collection built by `snoc` is not empty. -/
  not_isEmpty_snoc : ∀ c, ¬ IsEmpty (snoc c)

/-- The `Nat` ghost length of a list. -/
def natGhostLen {α : Type u} (xs : List α) : Nat := xs.length

/-- The `Int` ghost length of a list. -/
def intGhostLen {α : Type u} (xs : List α) : Int := Int.ofNat xs.length

theorem natGhostLen_nil {α : Type u} : natGhostLen ([] : List α) = 0 := rfl

theorem natGhostLen_cons {α : Type u} (x : α) (xs : List α) :
    natGhostLen (x :: xs) = natGhostLen xs + 1 := rfl

theorem natGhostLen_lt_cons {α : Type u} (x : α) (xs : List α) :
    natGhostLen xs < natGhostLen (x :: xs) := Nat.lt_succ_self _

theorem natGhostLen_eq_zero_iff {α : Type u} (xs : List α) :
    natGhostLen xs = 0 ↔ xs = [] := by
  cases xs with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons x xs => exact ⟨fun h => absurd h (Nat.succ_ne_zero _), fun h => nomatch h⟩

/-- **Immunity to the wraparound.** The `Nat` ghost length of a list of `2 ^ 64`
    elements is `2 ^ 64`. -/
theorem natGhostLen_replicate_two_pow_64 {α : Type u} (x : α) :
    natGhostLen (List.replicate (2 ^ 64) x) = 2 ^ 64 :=
  List.length_replicate

theorem natGhostLen_replicate_two_pow_64_ne_zero {α : Type u} (x : α) :
    natGhostLen (List.replicate (2 ^ 64) x) ≠ 0 := by
  rw [natGhostLen_replicate_two_pow_64]
  decide

/-- The brief's literal statement: the unit list of `2 ^ 64` elements has length
    `2 ^ 64`, which is not `0`. -/
theorem length_replicate_two_pow_64_unit :
    (List.replicate (2 ^ 64) ()).length = 2 ^ 64 ∧ (List.replicate (2 ^ 64) ()).length ≠ 0 :=
  ⟨natGhostLen_replicate_two_pow_64 (), natGhostLen_replicate_two_pow_64_ne_zero ()⟩

theorem intGhostLen_nil {α : Type u} : intGhostLen ([] : List α) = 0 := rfl

theorem intGhostLen_cons {α : Type u} (x : α) (xs : List α) :
    intGhostLen (x :: xs) = intGhostLen xs + 1 := rfl

theorem intGhostLen_nonneg {α : Type u} (xs : List α) : 0 ≤ intGhostLen xs :=
  Int.natCast_nonneg _

theorem intGhostLen_lt_cons {α : Type u} (x : α) (xs : List α) :
    intGhostLen xs < intGhostLen (x :: xs) := by
  rw [intGhostLen_cons]
  omega

theorem intGhostLen_eq_zero_iff {α : Type u} (xs : List α) :
    intGhostLen xs = 0 ↔ xs = [] := by
  cases xs with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons x xs =>
    refine ⟨fun h => ?_, fun h => nomatch h⟩
    have hNonneg := intGhostLen_nonneg xs
    rw [intGhostLen_cons] at h
    omega

theorem intGhostLen_replicate_two_pow_64 {α : Type u} (x : α) :
    intGhostLen (List.replicate (2 ^ 64) x) = 2 ^ 64 := by
  unfold intGhostLen
  rw [List.length_replicate]
  rfl

theorem intGhostLen_replicate_two_pow_64_ne_zero {α : Type u} (x : α) :
    intGhostLen (List.replicate (2 ^ 64) x) ≠ 0 := by
  rw [intGhostLen_replicate_two_pow_64]
  decide

/-- The list model of the unbounded axioms: `snoc` prepends `x`. -/
def listGhostLengthAxioms {α : Type u} (x : α) : UnboundedGhostCollectionAxioms (List α) where
  empty := []
  snoc := fun xs => x :: xs
  IsEmpty := fun xs => xs = []
  len := natGhostLen
  len_empty := natGhostLen_nil
  len_snoc := natGhostLen_cons x
  len_strict_mono := natGhostLen_lt_cons x
  len_zero_iff_isEmpty := natGhostLen_eq_zero_iff
  not_isEmpty_snoc := fun _ h => nomatch h

/-- **Model consistency.** The unbounded inductive axioms are satisfiable. -/
theorem unboundedGhostCollectionAxioms_nonempty :
    Nonempty (UnboundedGhostCollectionAxioms (List Unit)) :=
  ⟨listGhostLengthAxioms ()⟩

/-- Under the unbounded axioms the length after `n` appends is exactly `n`: no
    number of appends ever wraps. -/
theorem UnboundedGhostCollectionAxioms.len_iterSnoc {Coll : Type u}
    (A : UnboundedGhostCollectionAxioms Coll) (n : Nat) :
    A.len (iterSnoc A.snoc n A.empty) = n := by
  induction n with
  | zero => exact A.len_empty
  | succ n ih =>
    show A.len (A.snoc (iterSnoc A.snoc n A.empty)) = n + 1
    rw [A.len_snoc, ih]

/-- The full inductive axiom set of a ghost collection with an unbounded `Int`
    length (`0 ≤ len c`). -/
structure UnboundedIntGhostCollectionAxioms (Coll : Type u) where
  /-- The empty collection. -/
  empty : Coll
  /-- Append one element. -/
  snoc : Coll → Coll
  /-- Emptiness predicate. -/
  IsEmpty : Coll → Prop
  /-- Unbounded signed length. -/
  len : Coll → Int
  /-- Ghost lengths are always non-negative. -/
  len_nonneg : ∀ c, 0 ≤ len c
  /-- The empty collection has length `0`. -/
  len_empty : len empty = 0
  /-- `snoc` advances the length by exactly one. -/
  len_snoc : ∀ c, len (snoc c) = len c + 1
  /-- `snoc` strictly increases the length. -/
  len_strict_mono : ∀ c, len c < len (snoc c)
  /-- Length zero characterizes emptiness. -/
  len_zero_iff_isEmpty : ∀ c, len c = 0 ↔ IsEmpty c
  /-- A collection built by `snoc` is not empty. -/
  not_isEmpty_snoc : ∀ c, ¬ IsEmpty (snoc c)

/-- The list model of the unbounded `Int` axioms. -/
def listIntGhostLengthAxioms {α : Type u} (x : α) :
    UnboundedIntGhostCollectionAxioms (List α) where
  empty := []
  snoc := fun xs => x :: xs
  IsEmpty := fun xs => xs = []
  len := intGhostLen
  len_nonneg := intGhostLen_nonneg
  len_empty := intGhostLen_nil
  len_snoc := intGhostLen_cons x
  len_strict_mono := intGhostLen_lt_cons x
  len_zero_iff_isEmpty := intGhostLen_eq_zero_iff
  not_isEmpty_snoc := fun _ h => nomatch h

/-- **Model consistency (`Int`).** The unbounded `Int` inductive axioms are satisfiable. -/
theorem unboundedIntGhostCollectionAxioms_nonempty :
    Nonempty (UnboundedIntGhostCollectionAxioms (List Unit)) :=
  ⟨listIntGhostLengthAxioms ()⟩

/-- Under the unbounded `Int` axioms the length after `n` appends is `Int.ofNat n`. -/
theorem UnboundedIntGhostCollectionAxioms.len_iterSnoc {Coll : Type u}
    (A : UnboundedIntGhostCollectionAxioms Coll) (n : Nat) :
    A.len (iterSnoc A.snoc n A.empty) = Int.ofNat n := by
  induction n with
  | zero => exact A.len_empty
  | succ n ih =>
    show A.len (A.snoc (iterSnoc A.snoc n A.empty)) = Int.ofNat (n + 1)
    rw [A.len_snoc, ih]
    rfl

/-! ### 4.5 The Guard Is Exactly Right -/

/-- A model of the strict-monotonicity axiom whose length denotes only values
    representable at width `w`. -/
structure InductiveGhostLengthModel (w : GhostIntWidth) : Type 1 where
  /-- Carrier of ghost collections. -/
  Coll : Type
  /-- The empty collection. -/
  empty : Coll
  /-- Append one element. -/
  snoc : Coll → Coll
  /-- Mathematical value denoted by the `w`-typed length. -/
  len : Coll → Nat
  /-- Every length is representable at width `w`. -/
  len_represents : ∀ c, w.Represents (len c)
  /-- `snoc` strictly increases the length. -/
  len_strict_mono : ∀ c, len c < len (snoc c)

/-- In any such model the length after `n` appends is at least `n`. -/
theorem InductiveGhostLengthModel.le_len_iterSnoc {w : GhostIntWidth}
    (M : InductiveGhostLengthModel w) (n : Nat) :
    n ≤ M.len (iterSnoc M.snoc n M.empty) := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => exact Nat.lt_of_le_of_lt ih (M.len_strict_mono _)

/-- The unbounded model: collections are element counts. -/
def natCounterModel (w : GhostIntWidth) (h : GhostLengthTypeGuard w) :
    InductiveGhostLengthModel w where
  Coll := Nat
  empty := 0
  snoc := Nat.succ
  len := id
  len_represents := fun n => by
    cases w with
    | fixedUnsigned bits => exact Bool.noConfusion h
    | fixedSigned bits => exact Bool.noConfusion h
    | unboundedNat => exact True.intro
    | unboundedInt => exact True.intro
  len_strict_mono := Nat.lt_succ_self

/-- **Soundness and completeness of the guard.** `GhostLengthTypeGuard w` holds
    exactly when the inductive length axiom has a model at width `w`: every
    fixed-width type is inconsistent with it, and both unbounded types are
    consistent with it. -/
theorem ghostLengthTypeGuard_iff_nonempty_model (w : GhostIntWidth) :
    GhostLengthTypeGuard w ↔ Nonempty (InductiveGhostLengthModel w) := by
  constructor
  · exact fun h => ⟨natCounterModel w h⟩
  · rintro ⟨M⟩
    cases hCap : w.capacity? with
    | none => exact (ghostLengthTypeGuard_iff_capacity_none w).mpr hCap
    | some cap =>
      have hLt := GhostIntWidth.lt_capacity_of_represents hCap
        (M.len_represents (iterSnoc M.snoc cap M.empty))
      exact absurd hLt (Nat.not_lt.mpr (M.le_len_iterSnoc cap))

/-- No fixed-width unsigned ghost length admits the inductive length axiom. -/
theorem isEmpty_model_of_fixedUnsigned (bits : Nat) :
    ¬ Nonempty (InductiveGhostLengthModel (.fixedUnsigned bits)) :=
  fun h => not_ghostLengthTypeGuard_fixedUnsigned bits
    ((ghostLengthTypeGuard_iff_nonempty_model _).mpr h)

/-- No fixed-width signed ghost length admits the inductive length axiom. -/
theorem isEmpty_model_of_fixedSigned (bits : Nat) :
    ¬ Nonempty (InductiveGhostLengthModel (.fixedSigned bits)) :=
  fun h => not_ghostLengthTypeGuard_fixedSigned bits
    ((ghostLengthTypeGuard_iff_nonempty_model _).mpr h)

/-! ## 5. Guard 3 — Error-Branch `True` Wildcard (`awsm2`)

`PostconditionDichotomy` asks for one accepted and one rejected output. A
postcondition `| Ok v => v = f x | Err _ => True` supplies both from its `Ok` arm
and so passes, while saying nothing at all about failure: an implementation that
always returns `Err`, returns the wrong error, or runs into undefined behavior
satisfies it on every input. -/

/-! ### 5.1 Fallible Outcomes -/

/-- The four-branch outcome of a fallible computation: success, a domain error, an
    undefined-behavior fault, or an unsupported-construct fault. -/
inductive FallibleOutcome (α : Type u) (ε : Type v) : Type (max u v) where
  /-- Successful completion with value `v` (`Ok(v)`). -/
  | ok (v : α)
  /-- Domain error with payload `e` (`Err(e)`). -/
  | err (e : ε)
  /-- Undefined behavior. -/
  | ub
  /-- Unsupported, fail-closed construct. -/
  | unsupported

namespace FallibleOutcome

variable {α : Type u} {ε : Type v}

/-- Embed a pure `Except ε α` result. -/
def ofExcept : Except ε α → FallibleOutcome α ε
  | .ok v => .ok v
  | .error e => .err e

/-- The `ok` payload, and `none` on every other branch. -/
def okValue? : FallibleOutcome α ε → Option α
  | .ok v => some v
  | .err _ => none
  | .ub => none
  | .unsupported => none

/-- Whether the outcome is an operational fault (`ub` or `unsupported`). -/
def isFault : FallibleOutcome α ε → Bool
  | .ok _ => false
  | .err _ => false
  | .ub => true
  | .unsupported => true

/-- Classify an operational `FailureKind`: `.ub` is `ub`, and both fail-closed kinds
    (`.unsupported`, `.outOfFuel`) are `unsupported`. -/
def ofFailureKind : FailureKind → FallibleOutcome α ε
  | .ub => .ub
  | .unsupported => .unsupported
  | .outOfFuel => .unsupported

theorem isFault_ofFailureKind (kind : FailureKind) :
    (ofFailureKind kind : FallibleOutcome α ε).isFault = true := by
  cases kind <;> rfl

theorem isFault_ofExcept (r : Except ε α) : (ofExcept r).isFault = false := by
  cases r <;> rfl

end FallibleOutcome

/-- The candidate implementation `impl` is accepted by the contract `(pre, post)` on
    every valid input. When `impl` is wrong, it is a *surviving mutant*. -/
def MutantSurvives {X : Type u} {Y : Type v} (pre : X → Prop) (post : X → Y → Prop)
    (impl : X → Y) : Prop :=
  ∀ x, pre x → post x (impl x)

/-- Dichotomy restricted to the error fibre: some valid input has one accepted and
    one rejected *error payload*. -/
def ErrorFibreDichotomy {X : Type u} {α : Type v} {ε : Type w} (pre : X → Prop)
    (post : X → FallibleOutcome α ε → Prop) : Prop :=
  DichotomyModuloObservation (fun (_ : X) (_ : ε) => ()) pre (fun x e => post x (.err e))

theorem errorFibreDichotomy_iff {X : Type u} {α : Type v} {ε : Type w} {pre : X → Prop}
    {post : X → FallibleOutcome α ε → Prop} :
    ErrorFibreDichotomy pre post ↔
      ∃ x, pre x ∧ ∃ eOk eBad, post x (.err eOk) ∧ ¬ post x (.err eBad) :=
  ⟨fun ⟨x, hx, eOk, eBad, _, hOk, hBad⟩ => ⟨x, hx, eOk, eBad, hOk, hBad⟩,
    fun ⟨x, hx, eOk, eBad, hOk, hBad⟩ => ⟨x, hx, eOk, eBad, rfl, hOk, hBad⟩⟩

/-! ### 5.2 The Wildcard Postcondition Is Vacuous on Failure -/

/-- The `awsm2` wildcard postcondition: the `ok` value is pinned to `specFn x`, and
    every error, `ub`, and `unsupported` outcome is accepted. -/
def errorWildcardPost {X : Type u} {α : Type v} {ε : Type w} (specFn : X → α) (x : X) :
    FallibleOutcome α ε → Prop
  | .ok v => v = specFn x
  | .err _ => True
  | .ub => True
  | .unsupported => True

/-- The pure `Except` form `| .ok v => v = specFn x | .error _ => True`. -/
def exceptErrorWildcardPost {X : Type u} {α : Type v} {ε : Type w} (specFn : X → α)
    (x : X) : Except ε α → Prop
  | .ok v => v = specFn x
  | .error _ => True

section WildcardVacuity

variable {X : Type u} {α : Type v} {ε : Type w} {pre : X → Prop}

theorem exceptErrorWildcardPost_iff (specFn : X → α) (x : X) (r : Except ε α) :
    exceptErrorWildcardPost specFn x r ↔
      errorWildcardPost specFn x (FallibleOutcome.ofExcept r) := by
  cases r <;> exact Iff.rfl

/-- **The wildcard passes `PostconditionDichotomy`.** With two distinct values of `α`
    and a satisfiable precondition, the `ok` arm alone supplies an accepted and a
    rejected output. -/
theorem errorWildcardPost_postconditionDichotomy (specFn : X → α)
    (hTwo : ∃ a₁ a₂ : α, a₁ ≠ a₂) (hPre : PreconditionSatisfiable pre) :
    PostconditionDichotomy pre (errorWildcardPost (ε := ε) specFn) := by
  obtain ⟨x, hx⟩ := hPre
  obtain ⟨a₁, a₂, hNe⟩ := hTwo
  refine ⟨x, hx, ⟨.ok (specFn x), rfl⟩, ?_⟩
  by_cases h : a₁ = specFn x
  · exact ⟨.ok a₂, fun h₂ : a₂ = specFn x => hNe (h.trans h₂.symm)⟩
  · exact ⟨.ok a₁, h⟩

/-- **Constant-error escape.** The mutant that always fails with `e` satisfies the
    wildcard postcondition on every valid input. -/
theorem errorWildcardPost_constErr_survives (specFn : X → α) (e : ε) :
    MutantSurvives pre (errorWildcardPost specFn) (fun _ => .err e) :=
  fun _ _ => True.intro

/-- **Constant-UB escape.** The mutant that always has undefined behavior satisfies
    the wildcard postcondition on every valid input. -/
theorem errorWildcardPost_constUb_survives (specFn : X → α) :
    MutantSurvives pre (errorWildcardPost (ε := ε) specFn) (fun _ => .ub) :=
  fun _ _ => True.intro

/-- The mutant that always hits an unsupported construct survives as well. -/
theorem errorWildcardPost_constUnsupported_survives (specFn : X → α) :
    MutantSurvives pre (errorWildcardPost (ε := ε) specFn) (fun _ => .unsupported) :=
  fun _ _ => True.intro

/-- The wildcard postcondition cannot tell two error payloads apart. -/
theorem errorWildcardPost_err_indistinguishable (specFn : X → α) (x : X) (e₁ e₂ : ε) :
    errorWildcardPost specFn x (.err e₁ : FallibleOutcome α ε) ↔
      errorWildcardPost specFn x (.err e₂ : FallibleOutcome α ε) :=
  Iff.rfl

/-- **Error-fibre dichotomy fails.** No valid input has a rejected error payload. -/
theorem errorWildcardPost_not_errorFibreDichotomy (specFn : X → α) :
    ¬ ErrorFibreDichotomy pre (errorWildcardPost (ε := ε) specFn) := by
  rintro ⟨_, _, _, _, _, _, hBad⟩
  exact hBad True.intro

/-- The wildcard postcondition is blind to everything but the `ok` payload: it has
    no dichotomy between two outcomes with the same `okValue?`. -/
theorem errorWildcardPost_not_dichotomyModuloOkValue (specFn : X → α) :
    ¬ DichotomyModuloObservation
        (fun (_ : X) (out : FallibleOutcome α ε) => out.okValue?) pre
        (errorWildcardPost specFn) := by
  rintro ⟨x, _, yOk, yBad, hObs, hOk, hBad⟩
  cases yBad with
  | ok v =>
    cases yOk with
    | ok v' =>
      have hEq : v' = v := Option.some.inj hObs
      subst hEq
      exact hBad hOk
    | err e => cases hObs
    | ub => cases hObs
    | unsupported => cases hObs
  | err e => exact hBad True.intro
  | ub => exact hBad True.intro
  | unsupported => exact hBad True.intro

/-- **The `awsm2` hole in one statement.** The wildcard postcondition passes
    `PostconditionDichotomy`, yet the constant-error, constant-UB, and
    constant-unsupported mutants all survive and the error fibre has no dichotomy. -/
theorem errorWildcardPost_vacuous_on_failure (specFn : X → α)
    (hTwo : ∃ a₁ a₂ : α, a₁ ≠ a₂) (hPre : PreconditionSatisfiable pre) (e : ε) :
    PostconditionDichotomy pre (errorWildcardPost (ε := ε) specFn) ∧
      MutantSurvives pre (errorWildcardPost specFn) (fun _ => .err e) ∧
      MutantSurvives pre (errorWildcardPost (ε := ε) specFn) (fun _ => .ub) ∧
      MutantSurvives pre (errorWildcardPost (ε := ε) specFn) (fun _ => .unsupported) ∧
      ¬ ErrorFibreDichotomy pre (errorWildcardPost (ε := ε) specFn) :=
  ⟨errorWildcardPost_postconditionDichotomy specFn hTwo hPre,
    errorWildcardPost_constErr_survives specFn e,
    errorWildcardPost_constUb_survives specFn,
    errorWildcardPost_constUnsupported_survives specFn,
    errorWildcardPost_not_errorFibreDichotomy specFn⟩

/-- The pure `Except` wildcard also passes `PostconditionDichotomy`. -/
theorem exceptErrorWildcardPost_postconditionDichotomy (specFn : X → α)
    (hTwo : ∃ a₁ a₂ : α, a₁ ≠ a₂) (hPre : PreconditionSatisfiable pre) :
    PostconditionDichotomy pre (exceptErrorWildcardPost (ε := ε) specFn) := by
  obtain ⟨x, hx⟩ := hPre
  obtain ⟨a₁, a₂, hNe⟩ := hTwo
  refine ⟨x, hx, ⟨.ok (specFn x), rfl⟩, ?_⟩
  by_cases h : a₁ = specFn x
  · exact ⟨.ok a₂, fun h₂ : a₂ = specFn x => hNe (h.trans h₂.symm)⟩
  · exact ⟨.ok a₁, h⟩

/-- The constant-`error` mutant survives the pure `Except` wildcard. -/
theorem exceptErrorWildcardPost_constError_survives (specFn : X → α) (e : ε) :
    MutantSurvives pre (exceptErrorWildcardPost specFn) (fun _ => .error e) :=
  fun _ _ => True.intro

/-- The pure `Except` wildcard rejects no `error` payload on any input. -/
theorem exceptErrorWildcardPost_not_errorDichotomy (specFn : X → α) :
    ¬ ∃ x, pre x ∧ ∃ e₁ e₂ : ε,
        exceptErrorWildcardPost specFn x (.error e₁) ∧
          ¬ exceptErrorWildcardPost specFn x (.error e₂) := by
  rintro ⟨_, _, _, _, _, hBad⟩
  exact hBad True.intro

end WildcardVacuity

/-! ### 5.3 Specialization to `Trusted.Rustc.V2026_06_01.MirSemantics` -/

/-- Result type of scalar evaluation in `MirSemantics` (`evalScalarBinOp`):
    `ok`, `ub`, or `unsupported`. -/
abbrev ScalarEvalResult : Type := RvalueEvalResult

/-- View a scalar evaluation result as a `FallibleOutcome` with no error branch. -/
def FallibleOutcome.ofScalarEvalResult : ScalarEvalResult → FallibleOutcome Value Empty
  | .ok val _ _ => .ok val
  | .ub => .ub
  | .unsupported => .unsupported

/-- A wildcard correspondence predicate on scalar evaluation: the value is pinned on
    success, and `| .ub => True | .unsupported => True`. -/
def scalarWildcardCorr (expected : Value) : ScalarEvalResult → Prop
  | .ok val _ _ => val = expected
  | .ub => True
  | .unsupported => True

/-- The guarded correspondence predicate: `ub` and `unsupported` are rejected. -/
def scalarGuardedCorr (expected : Value) : ScalarEvalResult → Prop
  | .ok val _ _ => val = expected
  | .ub => False
  | .unsupported => False

theorem scalarWildcardCorr_iff (expected : Value) (r : ScalarEvalResult) :
    scalarWildcardCorr expected r ↔
      errorWildcardPost (fun _ : Unit => expected) () (FallibleOutcome.ofScalarEvalResult r) := by
  cases r <;> exact Iff.rfl

/-- `1_u8 / 0_u8` is undefined behavior in `MirSemantics`. -/
theorem evalScalarBinOp_div_zero_ub :
    evalScalarBinOp .div { bits := 1, sizeBytes := 1 } { bits := 0, sizeBytes := 1 } [] = .ub :=
  rfl

/-- `1_u8 / 1_u8` evaluates to `1_u8`. -/
theorem evalScalarBinOp_div_one_ok :
    evalScalarBinOp .div { bits := 1, sizeBytes := 1 } { bits := 1, sizeBytes := 1 } [] =
      .ok (.scalar { bits := 1, sizeBytes := 1 }) [] {} :=
  rfl

/-- **Concrete `MirSemantics` counterexample.** Whatever value the specification
    expects, the wildcard correspondence predicate accepts division by zero. -/
theorem scalarWildcardCorr_accepts_div_by_zero (expected : Value) :
    scalarWildcardCorr expected
      (evalScalarBinOp .div { bits := 1, sizeBytes := 1 } { bits := 0, sizeBytes := 1 } []) := by
  rw [evalScalarBinOp_div_zero_ub]
  exact True.intro

/-- The guarded correspondence predicate rejects division by zero. -/
theorem scalarGuardedCorr_rejects_div_by_zero (expected : Value) :
    ¬ scalarGuardedCorr expected
      (evalScalarBinOp .div { bits := 1, sizeBytes := 1 } { bits := 0, sizeBytes := 1 } []) := by
  rw [evalScalarBinOp_div_zero_ub]
  exact fun h => h

/-- The guarded correspondence predicate still accepts the correct quotient. -/
theorem scalarGuardedCorr_accepts_div_one :
    scalarGuardedCorr (.scalar { bits := 1, sizeBytes := 1 })
      (evalScalarBinOp .div { bits := 1, sizeBytes := 1 } { bits := 1, sizeBytes := 1 } []) := by
  rw [evalScalarBinOp_div_one_ok]
  exact rfl

/-- The guarded correspondence predicate implies UB-freedom of the evaluation. -/
theorem scalarGuardedCorr_ne_ub {expected : Value} {r : ScalarEvalResult}
    (h : scalarGuardedCorr expected r) : r ≠ .ub ∧ r ≠ .unsupported := by
  cases r with
  | ok val locals mem => exact ⟨fun hEq => (nomatch hEq), fun hEq => (nomatch hEq)⟩
  | ub => exact False.elim h
  | unsupported => exact False.elim h

/-- Defined halting outcomes other than a normal return. -/
inductive HaltError : Type where
  /-- Unwinding panic. -/
  | panic
  /-- Immediate abort. -/
  | abort
  deriving DecidableEq, Repr, Inhabited

/-- View a terminal `MirOutcome` as a `FallibleOutcome`. -/
def FallibleOutcome.ofMirOutcome : MirOutcome → FallibleOutcome MirReturn HaltError
  | .normal ret => .ok ret
  | .panic => .err .panic
  | .abort => .err .abort

/-- Classify one `MirStepNode`: a return is `ok` / `err`, an operational fault is
    `ub` / `unsupported`, and a node that keeps running has no outcome yet. -/
def classifyMirStepNode : MirStepNode → Option (FallibleOutcome MirReturn HaltError)
  | .ret out => some (FallibleOutcome.ofMirOutcome out)
  | .tau _ => none
  | .vis (.inl (.fail kind)) _ => some (FallibleOutcome.ofFailureKind kind)
  | .vis (.inr _) _ => none

theorem classifyMirStepNode_fail (kind : FailureKind) :
    classifyMirStepNode (MirStepNode.fail kind) = some (FallibleOutcome.ofFailureKind kind) :=
  rfl

theorem classifyMirStepNode_unsupported :
    classifyMirStepNode MirStepNode.unsupported = some .unsupported :=
  rfl

/-- **Concrete `MirStepNode` counterexample.** The first step of the division entry
    point on `argc == 0` is classified `ub`, and the wildcard postcondition accepts
    it for every expected return. -/
theorem errorWildcardPost_accepts_divEntry_ub (defPath : DefPath) (expected : MirReturn) :
    ∃ out,
      classifyMirStepNode
          (stepMirState (EntryDemo.divEntryBody defPath)
            (.running (initMachineStateWithCallees (EntryDemo.divEntryBody defPath)
              (EntryDemo.u8Arg 0) []))) = some out ∧
        out = .ub ∧ errorWildcardPost (fun _ : Unit => expected) () out := by
  refine ⟨.ub, ?_, rfl, True.intro⟩
  rw [EntryDemo.divEntry_step_zero]
  rfl

/-! ### 5.4 The Guarded Postcondition -/

/-- The error-branch guard on a postcondition over `FallibleOutcome`. `expectsOk`
    selects the valid inputs on which the computation must succeed; on the remaining
    valid inputs it must fail with a determined error payload. -/
structure ErrorBranchGuardedPost {X : Type u} {α : Type v} {ε : Type w}
    (pre expectsOk : X → Prop) (post : X → FallibleOutcome α ε → Prop) : Prop where
  /-- Every valid input has an accepted outcome. -/
  realizable : ∀ x, pre x → ∃ out, post x out
  /-- Undefined behavior is never accepted. -/
  rejects_ub : ∀ x, pre x → ¬ post x .ub
  /-- An unsupported-construct fault is never accepted. -/
  rejects_unsupported : ∀ x, pre x → ¬ post x .unsupported
  /-- On an expected-`ok` input every error is rejected. -/
  ok_rejects_err : ∀ x, pre x → expectsOk x → ∀ e, ¬ post x (.err e)
  /-- On an expected-`err` input every success is rejected. -/
  err_rejects_ok : ∀ x, pre x → ¬ expectsOk x → ∀ v, ¬ post x (.ok v)
  /-- On an expected-`err` input the accepted error payload is unique. -/
  err_payload_unique : ∀ x, pre x → ¬ expectsOk x → ∀ e₁ e₂,
    post x (.err e₁) → post x (.err e₂) → e₁ = e₂

namespace ErrorBranchGuardedPost

variable {X : Type u} {α : Type v} {ε : Type w} {pre expectsOk : X → Prop}
  {post : X → FallibleOutcome α ε → Prop}

/-- On an expected-`ok` input some success is accepted. -/
theorem exists_ok_accepted (h : ErrorBranchGuardedPost pre expectsOk post) {x : X}
    (hx : pre x) (hOk : expectsOk x) : ∃ v, post x (.ok v) := by
  obtain ⟨out, hOut⟩ := h.realizable x hx
  cases out with
  | ok v => exact ⟨v, hOut⟩
  | err e => exact absurd hOut (h.ok_rejects_err x hx hOk e)
  | ub => exact absurd hOut (h.rejects_ub x hx)
  | unsupported => exact absurd hOut (h.rejects_unsupported x hx)

/-- On an expected-`err` input some error is accepted. -/
theorem exists_err_accepted (h : ErrorBranchGuardedPost pre expectsOk post) {x : X}
    (hx : pre x) (hErr : ¬ expectsOk x) : ∃ e, post x (.err e) := by
  obtain ⟨out, hOut⟩ := h.realizable x hx
  cases out with
  | ok v => exact absurd hOut (h.err_rejects_ok x hx hErr v)
  | err e => exact ⟨e, hOut⟩
  | ub => exact absurd hOut (h.rejects_ub x hx)
  | unsupported => exact absurd hOut (h.rejects_unsupported x hx)

/-- **Kills constant-`Err` mutants.** If some valid input must succeed, no
    always-failing implementation is accepted. -/
theorem kills_constErr (h : ErrorBranchGuardedPost pre expectsOk post)
    (hOk : ∃ x, pre x ∧ expectsOk x) (e : ε) :
    ¬ MutantSurvives pre post (fun _ => .err e) := by
  intro hSurvives
  obtain ⟨x, hx, hExp⟩ := hOk
  exact h.ok_rejects_err x hx hExp e (hSurvives x hx)

/-- **Kills wrong-payload mutants.** On an expected-`err` input, once `Err(e)` is
    accepted every other payload `e'` is rejected. -/
theorem kills_wrong_err_payload (h : ErrorBranchGuardedPost pre expectsOk post) {x : X}
    (hx : pre x) (hErr : ¬ expectsOk x) {e e' : ε} (hAccept : post x (.err e))
    (hNe : e' ≠ e) : ¬ post x (.err e') :=
  fun hAccept' => hNe (h.err_payload_unique x hx hErr e' e hAccept' hAccept)

/-- **Kills the constant-UB mutant.** -/
theorem kills_constUb (h : ErrorBranchGuardedPost pre expectsOk post)
    (hPre : PreconditionSatisfiable pre) : ¬ MutantSurvives pre post (fun _ => .ub) := by
  intro hSurvives
  obtain ⟨x, hx⟩ := hPre
  exact h.rejects_ub x hx (hSurvives x hx)

/-- **Kills the constant-unsupported mutant.** -/
theorem kills_constUnsupported (h : ErrorBranchGuardedPost pre expectsOk post)
    (hPre : PreconditionSatisfiable pre) :
    ¬ MutantSurvives pre post (fun _ => .unsupported) := by
  intro hSurvives
  obtain ⟨x, hx⟩ := hPre
  exact h.rejects_unsupported x hx (hSurvives x hx)

/-- **UB-freedom.** Any implementation accepted by a guarded postcondition never
    faults on a valid input. -/
theorem fault_free (h : ErrorBranchGuardedPost pre expectsOk post)
    {impl : X → FallibleOutcome α ε} (hImpl : MutantSurvives pre post impl) {x : X}
    (hx : pre x) : (impl x).isFault = false := by
  have hAccept := hImpl x hx
  cases hOut : impl x with
  | ok v => rfl
  | err e => rfl
  | ub => rw [hOut] at hAccept; exact absurd hAccept (h.rejects_ub x hx)
  | unsupported => rw [hOut] at hAccept; exact absurd hAccept (h.rejects_unsupported x hx)

/-- A guarded postcondition is dichotomous as soon as its precondition is satisfiable. -/
theorem postconditionDichotomy (h : ErrorBranchGuardedPost pre expectsOk post)
    (hPre : PreconditionSatisfiable pre) : PostconditionDichotomy pre post := by
  obtain ⟨x, hx⟩ := hPre
  exact ⟨x, hx, h.realizable x hx, ⟨.ub, h.rejects_ub x hx⟩⟩

/-- **Error-payload dichotomy.** With a valid expected-`err` input and two distinct
    error payloads, the error fibre itself has an accepted and a rejected payload. -/
theorem errorFibreDichotomy (h : ErrorBranchGuardedPost pre expectsOk post)
    (hErr : ∃ x, pre x ∧ ¬ expectsOk x) (hTwo : ∃ e₁ e₂ : ε, e₁ ≠ e₂) :
    ErrorFibreDichotomy pre post := by
  obtain ⟨x, hx, hExp⟩ := hErr
  obtain ⟨e, hAccept⟩ := h.exists_err_accepted hx hExp
  obtain ⟨e₁, e₂, hNe⟩ := hTwo
  refine errorFibreDichotomy_iff.mpr ⟨x, hx, e, ?_⟩
  by_cases hEq : e₁ = e
  · exact ⟨e₂, hAccept, h.kills_wrong_err_payload hx hExp hAccept (fun h₂ => hNe (hEq.trans h₂.symm))⟩
  · exact ⟨e₁, hAccept, h.kills_wrong_err_payload hx hExp hAccept hEq⟩

end ErrorBranchGuardedPost

/-- **The wildcard fails the guard.** `errorWildcardPost` is never an
    `ErrorBranchGuardedPost` over a satisfiable precondition. -/
theorem not_errorBranchGuardedPost_errorWildcardPost {X : Type u} {α : Type v} {ε : Type w}
    {pre expectsOk : X → Prop} (specFn : X → α) (hPre : PreconditionSatisfiable pre) :
    ¬ ErrorBranchGuardedPost pre expectsOk (errorWildcardPost (ε := ε) specFn) :=
  fun h => h.kills_constUb hPre (errorWildcardPost_constUb_survives specFn)

/-- The repaired postcondition: the value is pinned on expected-`ok` inputs, the
    error payload is pinned on expected-`err` inputs, and faults are rejected. -/
def errorGuardedPost {X : Type u} {α : Type v} {ε : Type w} (expectsOk : X → Prop)
    (specFn : X → α) (errFn : X → ε) (x : X) : FallibleOutcome α ε → Prop
  | .ok v => expectsOk x ∧ v = specFn x
  | .err e => ¬ expectsOk x ∧ e = errFn x
  | .ub => False
  | .unsupported => False

/-- The repaired postcondition satisfies the guard over every precondition. -/
theorem errorGuardedPost_guarded {X : Type u} {α : Type v} {ε : Type w}
    (pre expectsOk : X → Prop) (specFn : X → α) (errFn : X → ε) :
    ErrorBranchGuardedPost pre expectsOk (errorGuardedPost expectsOk specFn errFn) where
  realizable := fun x _ => by
    by_cases hOk : expectsOk x
    · exact ⟨.ok (specFn x), hOk, rfl⟩
    · exact ⟨.err (errFn x), hOk, rfl⟩
  rejects_ub := fun _ _ h => h
  rejects_unsupported := fun _ _ h => h
  ok_rejects_err := fun _ _ hOk _ h => h.1 hOk
  err_rejects_ok := fun _ _ hErr _ h => hErr h.1
  err_payload_unique := fun _ _ _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm

/-- The pure `Except ε α` counterpart of `ErrorBranchGuardedPost`. -/
structure ErrorBranchGuardedExceptPost {X : Type u} {α : Type v} {ε : Type w}
    (pre expectsOk : X → Prop) (post : X → Except ε α → Prop) : Prop where
  /-- Every valid input has an accepted `Except` outcome. -/
  realizable : ∀ x, pre x → ∃ out, post x out
  /-- On an expected-`ok` input every `error` is rejected. -/
  ok_rejects_error : ∀ x, pre x → expectsOk x → ∀ e, ¬ post x (.error e)
  /-- On an expected-`error` input every `ok` is rejected. -/
  error_rejects_ok : ∀ x, pre x → ¬ expectsOk x → ∀ v, ¬ post x (.ok v)
  /-- On an expected-`error` input the accepted error payload is unique. -/
  error_payload_unique : ∀ x, pre x → ¬ expectsOk x → ∀ e₁ e₂,
    post x (.error e₁) → post x (.error e₂) → e₁ = e₂

namespace ErrorBranchGuardedExceptPost

variable {X : Type u} {α : Type v} {ε : Type w} {pre expectsOk : X → Prop}
  {post : X → Except ε α → Prop}

/-- On an expected-`error` input some error payload is accepted. -/
theorem exists_error_accepted (h : ErrorBranchGuardedExceptPost pre expectsOk post) {x : X}
    (hx : pre x) (hErr : ¬ expectsOk x) : ∃ e, post x (.error e) := by
  obtain ⟨out, hOut⟩ := h.realizable x hx
  cases out with
  | ok v => exact absurd hOut (h.error_rejects_ok x hx hErr v)
  | error e => exact ⟨e, hOut⟩

/-- Kills every constant-`.error` escape mutant whenever some input must succeed. -/
theorem kills_constError (h : ErrorBranchGuardedExceptPost pre expectsOk post)
    (hOk : ∃ x, pre x ∧ expectsOk x) (e : ε) :
    ¬ MutantSurvives pre post (fun _ => .error e) := by
  intro hSurvives
  obtain ⟨x, hx, hExp⟩ := hOk
  exact h.ok_rejects_error x hx hExp e (hSurvives x hx)

/-- Kills wrong error payloads on expected-`error` inputs. -/
theorem kills_wrong_error_payload (h : ErrorBranchGuardedExceptPost pre expectsOk post) {x : X}
    (hx : pre x) (hErr : ¬ expectsOk x) {e e' : ε} (hAccept : post x (.error e))
    (hNe : e' ≠ e) : ¬ post x (.error e') :=
  fun hAccept' => hNe (h.error_payload_unique x hx hErr e' e hAccept' hAccept)

/-- Achieves error-fibre dichotomy on `Except ε α`. -/
theorem errorDichotomy (h : ErrorBranchGuardedExceptPost pre expectsOk post)
    (hErr : ∃ x, pre x ∧ ¬ expectsOk x) (hTwo : ∃ e₁ e₂ : ε, e₁ ≠ e₂) :
    ∃ x, pre x ∧ ∃ eOk eBad : ε, post x (.error eOk) ∧ ¬ post x (.error eBad) := by
  obtain ⟨x, hx, hExp⟩ := hErr
  obtain ⟨e, hAccept⟩ := h.exists_error_accepted hx hExp
  obtain ⟨e₁, e₂, hNe⟩ := hTwo
  refine ⟨x, hx, e, ?_⟩
  by_cases hEq : e₁ = e
  · exact ⟨e₂, hAccept, h.kills_wrong_error_payload hx hExp hAccept
      (fun h₂ => hNe (hEq.trans h₂.symm))⟩
  · exact ⟨e₁, hAccept, h.kills_wrong_error_payload hx hExp hAccept hEq⟩

end ErrorBranchGuardedExceptPost

/-- The pure `Except` wildcard fails `ErrorBranchGuardedExceptPost` whenever some
    valid input must succeed. -/
theorem not_errorBranchGuardedExceptPost_exceptErrorWildcardPost
    {X : Type u} {α : Type v} {ε : Type w} {pre expectsOk : X → Prop}
    (specFn : X → α) (hOk : ∃ x, pre x ∧ expectsOk x) (e : ε) :
    ¬ ErrorBranchGuardedExceptPost pre expectsOk (exceptErrorWildcardPost (ε := ε) specFn) :=
  fun h => h.kills_constError hOk e (exceptErrorWildcardPost_constError_survives specFn e)

/-- The repaired pure `Except` postcondition. -/
def exceptGuardedPost {X : Type u} {α : Type v} {ε : Type w} (expectsOk : X → Prop)
    (specFn : X → α) (errFn : X → ε) (x : X) : Except ε α → Prop
  | .ok v => expectsOk x ∧ v = specFn x
  | .error e => ¬ expectsOk x ∧ e = errFn x

/-- The repaired pure `Except` postcondition satisfies `ErrorBranchGuardedExceptPost`. -/
theorem exceptGuardedPost_guarded {X : Type u} {α : Type v} {ε : Type w}
    (pre expectsOk : X → Prop) (specFn : X → α) (errFn : X → ε) :
    ErrorBranchGuardedExceptPost pre expectsOk (exceptGuardedPost expectsOk specFn errFn) where
  realizable := fun x _ => by
    by_cases hOk : expectsOk x
    · exact ⟨.ok (specFn x), hOk, rfl⟩
    · exact ⟨.error (errFn x), hOk, rfl⟩
  ok_rejects_error := fun _ _ hOk _ h => h.1 hOk
  error_rejects_ok := fun _ _ hErr _ h => hErr h.1
  error_payload_unique := fun _ _ _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm

end Anneal.SpecBoundaryGuards
