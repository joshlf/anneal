/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Trusted
import Anneal.Memory
import Anneal.BitValidity
import Std.Data.TreeMap.Raw

/-!
# Keyed `UInt64` `ExtTreeMap0` Allocation Maps, `#[rustc_no_writable]` & Static-Access Retags, and Array `Sized` / Auto-Trait VTable / Null-VTable Validity

Complete, kernel-checked, `Classical.choice`-free theory covering:

- **Part 1 (`proofs-rs/lean-miri#73`)**: Constructive `TransCmp`/`LawfulEqCmp`
  on `Nat`, `UInt64`, and full-width `MiriAllocId` (`NonZeroU64`); balanced
  AA-tree `RawAATree` and quotient-extensional `ExtTreeMap0`; `KeyedAllocTable`,
  `KeyedAllocWorld`, `LinearAllocWorld`, total bidirectional refinement
  `AllocWorldRel`, `RaceDetectorMode`, `DeallocActor.ofVClock`, mode-aware
  `allocateMachine`/`deallocateMachine`, and exact Miri deallocation failure
  ordering.
- **Part 2 (`AeneasVerif/charon#1619`, `charon#1620`, `minirust#295`)**:
  `FnEntryRetagPolicy`, exact mirror of upstream `Miri.TreeBorrows.RetagPolicy.create`,
  operational bridge to `Trusted.Rustc.V2026_06_01.MirSemantics`, bottom-up
  `ancestorPathNodes` source-order borrow-tree traversal, hypothesis-free
  success-path equivalence across two-pass / flat-upstream / source-order
  models, `.frozen` preservation under `rustcNoWritable`, and syntactic
  `isSyntacticFreeze` static allocation mutability separating preserved `#1620`
  static-temporary retags from pre-`#1620` raw address-of erasure.
- **Part 3 (`lean-miri#79`, `#75`, `#82`)**: `O(1)` syntactic `Sized` fast-path
  with custom-DST `unsizedMetadataTail` / `unsizedDynTailTrait?`,
  `getAllocInfo`-backed `validateSafeThinRef` with provenance-agnostic null
  rejection and access-before-alignment ordering, canonical principal-less
  auto-trait `VTableKey` + `VTableWorldWF` / `SaltedVTableWorldWF` round-trip
  soundness + auto-trait-ignoring `vtableMatchesExpectedSpec` + upcast
  preservation, wide-`dyn` vtable-before-data UB precedence, unified
  `validateRawPtrFull`, and deferred recursive `childSession` (`mayDangle = true`)
  pointee byte visitor (`validateWideDynSafePtrWithBytes`).

## Upstream Correspondence Map (pinned `lean-miri/vendor/Miri`)

| Definition in this module | Upstream source |
| :--- | :--- |
| `reserveAllocId` | `Miri.Memory.MemoryState.reserveAllocId` (`AllocMap::reserve`, `fetch_add`) |
| `registerReservedGlobal` | `Miri.Memory.MemoryState.registerReservedGlobal` (`validateReservedGlobal`) |
| `isAllocLive`, `getAllocInfo`, `getLiveAllocSizeAndAlign`, `findAllocBytes?` | same-named `Miri.Memory.MemoryState` queries + global byte storage |
| `deallocateWith` | `Miri.Memory.MemoryState.deallocatePtrWith` (`Memory::deallocate_ptr`) |
| `machineDeallocHook` | `Miri.Interpreter.AllocationMachine.before` (`MachineHooks.memoryRaceAccess`, then Tree Borrows) |
| `detachRaceClock`, `deallocateMachine` | `Miri.Interpreter.AllocationMachine.deallocate` |
| `MiriRetagPolicyMirror.create` | `Miri.TreeBorrows.RetagPolicy.create` (`NewPermission::new`) |
| `stepNodeOnRangeRead` / `stepNodeOnRangeWrite` | `Miri.TreeBorrows.performAccess` + `Tree.LocationState.performAccess` (incl. `accessed`) |
| `execFnEntryMutRetagSourceOrder` / `execFnEntryMutRetagPrunedSourceOrder` | `Miri.TreeBorrows.RetagPipeline` (`accessTreeForReborrow`) over `TraversalTree.traverse` + `NormalTreeState.performAccess` (`SkipSelfAndChildren`) |
| `KeyedAllocWorld.checkPtrAccess` | `Miri.Memory.checkAndDerefPtr` via `ValidityMachine.checkPointerAccessResult` |
| `validateSafeThinRef`, `validateWideDynSafePtr` | `Miri.Interpreter.ValidityVisitor.checkSafe` |
| `validateVTableHalf`, `vtableMatchesExpectedSpec` | `Miri.Interpreter.VTable.getPtrVTableTypeRead`, `checkForTypeRead` |
| `visitConcreteValue`, `validateWideDynSafePtrWithBytes` | `Miri.Interpreter.ValidityVisitor.visit`, `validatePlace … recursive` |

Honest scope: Miri's `extra_fn_ptr_map` / va-list tables, export-ID tables, and wildcard provenance are
not modeled; the machine hook has no memory side effects beyond the race-clock detach; borrow-tree nodes
carry one coarse byte range (no per-byte lazy permissions, no `SkipSelfAndChildren` subtree pruning);
pointers are 8 bytes (wide nested pointers are validated on their data word); and global allocations
are metadata-only (no byte payload).
-/

namespace Anneal.ExtTreeMapAllocAndNoWritable

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.Memory

/-! ## Part 1: Constructive Ordering, `MiriAllocId`, `RawAATree`, `ExtTreeMap0`, and `KeyedAllocWorld` -/

/-! ### 1.1 Constructive `TransCmp` / `LawfulEqCmp` and Full-Width `MiriAllocId` -/

/-- Constructive `OrientedCmp` on `Nat` (`0` axioms). -/
instance (priority := 2000) instOrientedCmpNatConstructive :
    Std.OrientedCmp (compare : Nat → Nat → Ordering) where
  eq_swap {a b} := by
    change compareOfLessAndEq a b = (compareOfLessAndEq b a).swap
    unfold compareOfLessAndEq
    by_cases h1 : a < b
    · have h2 : ¬ (b < a) := by omega
      have h3 : ¬ (b = a) := by omega
      simp [h1, h2, h3]
    · by_cases h2 : a = b
      · subst h2; simp
      · have h3 : b < a := by omega
        simp [h1, h2, h3]

/-- Constructive `TransCmp` on `Nat` (`0` axioms, avoiding Lean `v4.34.1`'s `Classical.choice` default). -/
instance (priority := 2000) instTransCmpNatConstructive :
    Std.TransCmp (compare : Nat → Nat → Ordering) where
  isLE_trans {a b c} h1 h2 := by
    change (compareOfLessAndEq a b).isLE = true at h1
    change (compareOfLessAndEq b c).isLE = true at h2
    change (compareOfLessAndEq a c).isLE = true
    unfold compareOfLessAndEq at h1 h2 ⊢
    split at h1
    · split at h2
      · have h3 : a < c := by omega
        simp [h3]
      · split at h2
        · have h3 : a < c := by omega
          simp [h3]
        · cases h2
    · split at h1
      · split at h2
        · have h3 : a < c := by omega
          simp [h3]
        · split at h2
          · have h4 : a = c := by omega
            simp [h4]
          · cases h2
      · cases h1

/-- Constructive `ReflCmp` on `Nat` (`0` axioms). -/
instance (priority := 2000) instReflCmpNatConstructive :
    Std.ReflCmp (compare : Nat → Nat → Ordering) where
  compare_self {a} := by
    change compareOfLessAndEq a a = .eq
    simp [compareOfLessAndEq]

/-- Constructive `LawfulEqCmp` on `Nat` (`0` axioms). -/
instance (priority := 2000) instLawfulEqCmpNatConstructive :
    Std.LawfulEqCmp (compare : Nat → Nat → Ordering) where
  eq_of_compare {a b} h := by
    change compareOfLessAndEq a b = .eq at h
    unfold compareOfLessAndEq at h
    split at h
    · cases h
    · split at h
      · assumption
      · cases h

/-- Constructive `OrientedCmp` on `UInt64` (`0` axioms). -/
instance (priority := 2000) instOrientedCmpUInt64Constructive :
    Std.OrientedCmp (compare : UInt64 → UInt64 → Ordering) where
  eq_swap {a b} := by
    change compareOfLessAndEq a b = (compareOfLessAndEq b a).swap
    unfold compareOfLessAndEq
    by_cases h1 : a < b
    · have h1n : a.toNat < b.toNat := h1
      have h2 : ¬ (b < a) := fun h => by
        have : b.toNat < a.toNat := h
        omega
      have h3 : ¬ (b = a) := fun h => by subst h; omega
      simp [h1, h2, h3]
    · by_cases h2 : a = b
      · subst h2; simp
      · have h1n : ¬ (a.toNat < b.toNat) := h1
        have h2n : a.toNat ≠ b.toNat := fun h => h2 (UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))
        have h3 : b < a := show b.toNat < a.toNat by omega
        simp [h1, h2, h3]

/-- Constructive `TransCmp` on `UInt64` (`0` axioms). -/
instance (priority := 2000) instTransCmpUInt64Constructive :
    Std.TransCmp (compare : UInt64 → UInt64 → Ordering) where
  isLE_trans {a b c} h1 h2 := by
    change (compareOfLessAndEq a b).isLE = true at h1
    change (compareOfLessAndEq b c).isLE = true at h2
    change (compareOfLessAndEq a c).isLE = true
    unfold compareOfLessAndEq at h1 h2 ⊢
    split at h1
    · rename_i hab
      have habn : a.toNat < b.toNat := hab
      split at h2
      · rename_i hbc
        have hbcn : b.toNat < c.toNat := hbc
        have hac : a < c := show a.toNat < c.toNat by omega
        simp [hac]
      · split at h2
        · rename_i hbc
          subst hbc
          simp [hab]
        · cases h2
    · split at h1
      · rename_i hab
        subst hab
        exact h2
      · cases h1

/-- Constructive `ReflCmp` on `UInt64` (`0` axioms). -/
instance (priority := 2000) instReflCmpUInt64Constructive :
    Std.ReflCmp (compare : UInt64 → UInt64 → Ordering) where
  compare_self {a} := by
    change compareOfLessAndEq a a = .eq
    have h : ¬ (a < a) := fun h => by
      have : a.toNat < a.toNat := h
      omega
    simp [compareOfLessAndEq, h]

/-- Constructive `LawfulEqCmp` on `UInt64` (`0` axioms). -/
instance (priority := 2000) instLawfulEqCmpUInt64Constructive :
    Std.LawfulEqCmp (compare : UInt64 → UInt64 → Ordering) where
  eq_of_compare {a b} h := by
    change compareOfLessAndEq a b = .eq at h
    unfold compareOfLessAndEq at h
    split at h
    · cases h
    · split at h
      · assumption
      · cases h

/-- Full-width non-zero `UInt64` allocation identifier mirroring `Miri.Memory.AllocId` (`NonZeroU64`). -/
structure MiriAllocId where
  value : UInt64
  nonzero : value ≠ 0
  deriving DecidableEq, Repr

namespace MiriAllocId

@[ext]
theorem ext {a b : MiriAllocId} (h : a.value = b.value) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

/-- Construct a `MiriAllocId` from a raw `UInt64`, rejecting the reserved `0` sentinel. -/
def ofUInt64 (v : UInt64) : Option MiriAllocId :=
  if h : v ≠ 0 then some ⟨v, h⟩ else none

theorem ofUInt64_zero : ofUInt64 0 = none := by
  simp [ofUInt64]

theorem ofUInt64_eq_some_iff {v : UInt64} {id : MiriAllocId} :
    ofUInt64 v = some id ↔ id.value = v := by
  unfold ofUInt64
  split
  · constructor
    · intro h; injection h with h; subst h; rfl
    · intro h; congr 1; exact ext h.symm
  · rename_i h
    constructor
    · intro hnone; cases hnone
    · intro hv; exact False.elim (h (hv ▸ id.nonzero))

/-- Smallest valid runtime allocation identifier (`1`). -/
def one : MiriAllocId := ⟨1, by decide⟩

/-- Second-largest valid `UInt64` allocation identifier (`2^64 - 2`). -/
def maxMinusOne : MiriAllocId := ⟨UInt64.ofNat (2^64 - 2), by decide⟩

/-- Largest valid `UInt64` allocation identifier (`2^64 - 1`). -/
def maxValue : MiriAllocId := ⟨UInt64.ofNat (2^64 - 1), by decide⟩

/-- Inject `MiriAllocId` into `Trusted.Rustc.V2026_06_01.MirAst.AllocId` (`Nat`). -/
def toTrustedAllocId (id : MiriAllocId) : Trusted.Rustc.V2026_06_01.MirAst.AllocId :=
  id.value.toNat

theorem toTrustedAllocId_pos (id : MiriAllocId) : 0 < id.toTrustedAllocId := by
  unfold toTrustedAllocId
  by_cases h : id.value.toNat = 0
  · exfalso
    apply id.nonzero
    exact UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)
  · exact Nat.pos_of_ne_zero h

theorem toTrustedAllocId_injective : Function.Injective toTrustedAllocId := by
  intro a b h
  apply ext
  exact UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

end MiriAllocId

instance : Ord MiriAllocId where
  compare a b := compare a.value.toNat b.value.toNat

instance : Inhabited MiriAllocId where
  default := MiriAllocId.one

instance : Std.OrientedCmp (compare : MiriAllocId → MiriAllocId → Ordering) where
  eq_swap {a b} := Std.OrientedCmp.eq_swap (cmp := (compare : Nat → Nat → Ordering)) (a := a.value.toNat) (b := b.value.toNat)

instance : Std.TransCmp (compare : MiriAllocId → MiriAllocId → Ordering) where
  isLE_trans {_a _b _c} h1 h2 :=
    Std.TransCmp.isLE_trans (cmp := (compare : Nat → Nat → Ordering)) h1 h2

instance : Std.ReflCmp (compare : MiriAllocId → MiriAllocId → Ordering) where
  compare_self {a} := Std.ReflCmp.compare_self (cmp := (compare : Nat → Nat → Ordering)) (a := a.value.toNat)

instance : Std.LawfulEqCmp (compare : MiriAllocId → MiriAllocId → Ordering) where
  eq_of_compare {a b} h := by
    have hn : a.value.toNat = b.value.toNat :=
      Std.LawfulEqCmp.eq_of_compare (cmp := (compare : Nat → Nat → Ordering)) h
    exact MiriAllocId.toTrustedAllocId_injective hn

/-! ### 1.2 Constructive Ordered-List Specification, Balanced `RawAATree`, and Quotient `ExtTreeMap0` -/

section OrderedListSpec

variable {α : Type u} {β : Type v} (cmp : α → α → Ordering)

/-- Strict key-order invariant on an association list. -/
def StrictlySorted (xs : List (α × β)) : Prop :=
  List.Pairwise (fun x y => cmp x.1 y.1 = .lt) xs

/-- Sorted-list lookup stopping early once `cmp k k' = .lt`. -/
def lookupSorted (k : α) : List (α × β) → Option β
  | [] => none
  | (k', v) :: rest =>
    match cmp k k' with
    | .lt => none
    | .eq => some v
    | .gt => lookupSorted k rest

/-- Sorted-list insert replacing any equal key in place. -/
def insertSorted (k : α) (v : β) : List (α × β) → List (α × β)
  | [] => [(k, v)]
  | (k', v') :: rest =>
    match cmp k k' with
    | .lt => (k, v) :: (k', v') :: rest
    | .eq => (k, v) :: rest
    | .gt => (k', v') :: insertSorted k v rest

/-- Sorted-list erase removing any equal key. -/
def eraseSorted (k : α) : List (α × β) → List (α × β)
  | [] => []
  | (k', v') :: rest =>
    match cmp k k' with
    | .lt => (k', v') :: rest
    | .eq => rest
    | .gt => (k', v') :: eraseSorted k rest

/-- Constructive ordering helper lemmas from `Std.TransCmp` and `Std.LawfulEqCmp`. -/
theorem cmp_gt_iff_lt [Std.TransCmp cmp] {a b : α} :
    cmp a b = .gt ↔ cmp b a = .lt := by
  have h := Std.OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := b)
  cases hba : cmp b a <;> rw [hba] at h <;> simp [h]

theorem cmp_lt_trans [Std.TransCmp cmp] {a b c : α}
    (hab : cmp a b = .lt) (hbc : cmp b c = .lt) : cmp a c = .lt := by
  have h1 : (cmp a b).isLE = true := by simp [hab]
  have h2 : (cmp b c).isLE = true := by simp [hbc]
  have hle : (cmp a c).isLE = true := Std.TransCmp.isLE_trans h1 h2
  cases hac : cmp a c with
  | lt => rfl
  | gt => simp [hac] at hle
  | eq =>
    have hca : cmp c a = .eq := by
      have hsw := Std.OrientedCmp.eq_swap (cmp := cmp) (a := c) (b := a)
      rw [hac] at hsw; exact hsw
    have hba : (cmp b a).isLE = true :=
      Std.TransCmp.isLE_trans h2 (by simp [hca])
    have hba_gt : cmp b a = .gt := (cmp_gt_iff_lt cmp).2 hab
    simp [hba_gt] at hba

theorem cmp_lt_of_eq_of_lt [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] {a b c : α}
    (hab : cmp a b = .eq) (hbc : cmp b c = .lt) : cmp a c = .lt := by
  have heq : a = b := Std.LawfulEqCmp.eq_of_compare hab
  subst heq; exact hbc

theorem cmp_lt_of_lt_of_eq [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] {a b c : α}
    (hab : cmp a b = .lt) (hbc : cmp b c = .eq) : cmp a c = .lt := by
  have heq : b = c := Std.LawfulEqCmp.eq_of_compare hbc
  subst heq; exact hab

theorem lookupSorted_eq_none_of_forall_lt [Std.TransCmp cmp]
    {k : α} {xs : List (α × β)} (h : ∀ p ∈ xs, cmp k p.1 = .lt) :
    lookupSorted cmp k xs = none := by
  cases xs with
  | nil => rfl
  | cons p rest =>
    have hp : cmp k p.1 = .lt := h p (List.mem_cons_self ..)
    simp [lookupSorted, hp]

theorem lookupSorted_append [Std.TransCmp cmp]
    {k k' : α} {v' : β} {l r : List (α × β)}
    (hl : ∀ p ∈ l, cmp p.1 k' = .lt)
    (_hr : ∀ p ∈ r, cmp k' p.1 = .lt) :
    lookupSorted cmp k (l ++ (k', v') :: r) =
      match cmp k k' with
      | .lt => lookupSorted cmp k l
      | .eq => some v'
      | .gt => lookupSorted cmp k r := by
  induction l with
  | nil =>
    rfl
  | cons p rest ih =>
    have hpk' : cmp p.1 k' = .lt := hl p (List.mem_cons_self ..)
    have hl' : ∀ q ∈ rest, cmp q.1 k' = .lt := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    simp only [List.cons_append, lookupSorted]
    cases hkp : cmp k p.1 with
    | lt =>
      have hkk' : cmp k k' = .lt := cmp_lt_trans cmp hkp hpk'
      simp [hkk']
    | eq =>
      have hkp_le : (cmp k p.1).isLE = true := by simp [hkp]
      have hpk_le : (cmp p.1 k).isLE = true := by
        have hsw := Std.OrientedCmp.eq_swap (cmp := cmp) (a := p.1) (b := k)
        rw [hkp] at hsw; simp [hsw]
      have hkk'_le : (cmp k k').isLE = true :=
        Std.TransCmp.isLE_trans hkp_le (by simp [hpk'])
      have hkk' : cmp k k' = .lt := by
        cases h : cmp k k' with
        | lt => rfl
        | gt => simp [h] at hkk'_le
        | eq =>
          have hk'k : cmp k' k = .eq := by
            have hsw := Std.OrientedCmp.eq_swap (cmp := cmp) (a := k') (b := k)
            rw [h] at hsw; exact hsw
          have hk'p : (cmp k' p.1).isLE = true :=
            Std.TransCmp.isLE_trans (by simp [hk'k]) hkp_le
          have hk'p_gt : cmp k' p.1 = .gt := (cmp_gt_iff_lt cmp).2 hpk'
          simp [hk'p_gt] at hk'p
      simp [hkk']
    | gt =>
      exact ih hl'

theorem insertSorted_append [Std.TransCmp cmp]
    {k k' : α} {v v' : β} {l r : List (α × β)}
    (hl : ∀ p ∈ l, cmp p.1 k' = .lt) :
    insertSorted cmp k v (l ++ (k', v') :: r) =
      match cmp k k' with
      | .lt => insertSorted cmp k v l ++ (k', v') :: r
      | .eq => l ++ (k, v) :: r
      | .gt => l ++ (k', v') :: insertSorted cmp k v r := by
  induction l with
  | nil =>
    simp only [List.nil_append, insertSorted]
    cases hkk' : cmp k k' <;> rfl
  | cons p rest ih =>
    have hpk' : cmp p.1 k' = .lt := hl p (List.mem_cons_self ..)
    have hl' : ∀ q ∈ rest, cmp q.1 k' = .lt := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    simp only [List.cons_append, insertSorted]
    cases hkp : cmp k p.1 with
    | lt =>
      have hkk' : cmp k k' = .lt := cmp_lt_trans cmp hkp hpk'
      simp [hkk']
    | eq =>
      have hkp_le : (cmp k p.1).isLE = true := by simp [hkp]
      have hkk'_le : (cmp k k').isLE = true :=
        Std.TransCmp.isLE_trans hkp_le (by simp [hpk'])
      have hkk' : cmp k k' = .lt := by
        cases h : cmp k k' with
        | lt => rfl
        | gt => simp [h] at hkk'_le
        | eq =>
          have hk'k : cmp k' k = .eq := by
            have hsw := Std.OrientedCmp.eq_swap (cmp := cmp) (a := k') (b := k)
            rw [h] at hsw; exact hsw
          have hk'p : (cmp k' p.1).isLE = true :=
            Std.TransCmp.isLE_trans (by simp [hk'k]) hkp_le
          have hk'p_gt : cmp k' p.1 = .gt := (cmp_gt_iff_lt cmp).2 hpk'
          simp [hk'p_gt] at hk'p
      simp [hkk']
    | gt =>
      rw [ih hl']
      cases cmp k k' <;> rfl

theorem eraseSorted_append [Std.TransCmp cmp]
    {k k' : α} {v' : β} {l r : List (α × β)}
    (hl : ∀ p ∈ l, cmp p.1 k' = .lt) :
    eraseSorted cmp k (l ++ (k', v') :: r) =
      match cmp k k' with
      | .lt => eraseSorted cmp k l ++ (k', v') :: r
      | .eq => l ++ r
      | .gt => l ++ (k', v') :: eraseSorted cmp k r := by
  induction l with
  | nil =>
    rfl
  | cons p rest ih =>
    have hpk' : cmp p.1 k' = .lt := hl p (List.mem_cons_self ..)
    have hl' : ∀ q ∈ rest, cmp q.1 k' = .lt := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    simp only [List.cons_append, eraseSorted]
    cases hkp : cmp k p.1 with
    | lt =>
      have hkk' : cmp k k' = .lt := cmp_lt_trans cmp hkp hpk'
      simp [hkk']
    | eq =>
      have hkp_le : (cmp k p.1).isLE = true := by simp [hkp]
      have hkk'_le : (cmp k k').isLE = true :=
        Std.TransCmp.isLE_trans hkp_le (by simp [hpk'])
      have hkk' : cmp k k' = .lt := by
        cases h : cmp k k' with
        | lt => rfl
        | gt => simp [h] at hkk'_le
        | eq =>
          have hk'k : cmp k' k = .eq := by
            have hsw := Std.OrientedCmp.eq_swap (cmp := cmp) (a := k') (b := k)
            rw [h] at hsw; exact hsw
          have hk'p : (cmp k' p.1).isLE = true :=
            Std.TransCmp.isLE_trans (by simp [hk'k]) hkp_le
          have hk'p_gt : cmp k' p.1 = .gt := (cmp_gt_iff_lt cmp).2 hpk'
          simp [hk'p_gt] at hk'p
      simp [hkk']
    | gt =>
      rw [ih hl']
      cases cmp k k' <;> rfl

theorem mem_insertSorted_imp [Std.TransCmp cmp] {k : α} {v : β} {xs : List (α × β)} {p : α × β}
    (hp : p ∈ insertSorted cmp k v xs) :
    p = (k, v) ∨ p ∈ xs := by
  induction xs with
  | nil =>
    simp [insertSorted] at hp
    exact Or.inl hp
  | cons q rest ih =>
    simp only [insertSorted] at hp
    cases h : cmp k q.1 with
    | lt =>
      rw [h] at hp
      cases hp with
      | head => exact Or.inl rfl
      | tail _ h' => exact Or.inr h'
    | eq =>
      rw [h] at hp
      cases hp with
      | head => exact Or.inl rfl
      | tail _ h' => exact Or.inr (List.mem_cons_of_mem _ h')
    | gt =>
      rw [h] at hp
      cases hp with
      | head => exact Or.inr (List.mem_cons_self ..)
      | tail _ h' =>
        cases ih h' with
        | inl heq => exact Or.inl heq
        | inr hmem => exact Or.inr (List.mem_cons_of_mem _ hmem)

theorem strictlySorted_insertSorted [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    {k : α} {v : β} {xs : List (α × β)} (hxs : StrictlySorted cmp xs) :
    StrictlySorted cmp (insertSorted cmp k v xs) := by
  induction xs with
  | nil => exact List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil
  | cons q rest ih =>
    cases hxs with
    | cons hq hrest =>
      simp only [insertSorted]
      cases h : cmp k q.1 with
      | lt =>
        refine List.Pairwise.cons ?_ (List.Pairwise.cons hq hrest)
        intro p hp
        cases hp with
        | head => exact h
        | tail _ hp' => exact cmp_lt_trans cmp h (hq p hp')
      | eq =>
        refine List.Pairwise.cons ?_ hrest
        intro p hp
        exact cmp_lt_of_eq_of_lt cmp h (hq p hp)
      | gt =>
        refine List.Pairwise.cons ?_ (ih hrest)
        intro p hp
        cases mem_insertSorted_imp cmp hp with
        | inl heq =>
          subst heq
          exact (cmp_gt_iff_lt cmp).1 h
        | inr hmem => exact hq p hmem

theorem mem_eraseSorted_imp {k : α} {xs : List (α × β)} {p : α × β}
    (hp : p ∈ eraseSorted cmp k xs) : p ∈ xs := by
  induction xs with
  | nil => cases hp
  | cons q rest ih =>
    simp only [eraseSorted] at hp
    cases h : cmp k q.1 with
    | lt => rw [h] at hp; exact hp
    | eq => rw [h] at hp; exact List.mem_cons_of_mem _ hp
    | gt =>
      rw [h] at hp
      cases hp with
      | head => exact List.mem_cons_self ..
      | tail _ h' => exact List.mem_cons_of_mem _ (ih h')

theorem strictlySorted_eraseSorted {k : α} {xs : List (α × β)}
    (hxs : StrictlySorted cmp xs) :
    StrictlySorted cmp (eraseSorted cmp k xs) := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons q rest ih =>
    cases hxs with
    | cons hq hrest =>
      simp only [eraseSorted]
      cases cmp k q.1 with
      | lt => exact List.Pairwise.cons hq hrest
      | eq => exact hrest
      | gt =>
        refine List.Pairwise.cons ?_ (ih hrest)
        intro p hp
        exact hq p (mem_eraseSorted_imp cmp hp)

theorem lookupSorted_insertSorted [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    {k k' : α} {v : β} {xs : List (α × β)} (hxs : StrictlySorted cmp xs) :
    lookupSorted cmp k' (insertSorted cmp k v xs) =
      if cmp k' k == .eq then some v else lookupSorted cmp k' xs := by
  induction xs with
  | nil =>
    simp only [insertSorted, lookupSorted]
    cases h : cmp k' k <;> rfl
  | cons q rest ih =>
    cases hxs with
    | cons hq hrest =>
      simp only [insertSorted]
      cases hkq : cmp k q.1 with
      | lt =>
        simp only [lookupSorted]
        cases hk'k : cmp k' k with
        | lt =>
          have hk'q : cmp k' q.1 = .lt := cmp_lt_trans cmp hk'k hkq
          simp [hk'q]
        | eq =>
          simp
        | gt =>
          simp
      | eq =>
        have heq : k = q.1 := Std.LawfulEqCmp.eq_of_compare hkq
        subst heq
        simp only [lookupSorted]
        cases cmp k' q.1 <;> simp
      | gt =>
        have hqk : cmp q.1 k = .lt := (cmp_gt_iff_lt cmp).1 hkq
        simp only [lookupSorted]
        cases hk'q : cmp k' q.1 with
        | lt =>
          have hk'k : cmp k' k = .lt := cmp_lt_trans cmp hk'q hqk
          simp [hk'k]
        | eq =>
          have hk'k : cmp k' k = .lt := cmp_lt_of_eq_of_lt cmp hk'q hqk
          simp [hk'k]
        | gt =>
          exact ih hrest

theorem lookupSorted_eraseSorted [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    {k k' : α} {xs : List (α × β)} (hxs : StrictlySorted cmp xs) :
    lookupSorted cmp k' (eraseSorted cmp k xs) =
      if cmp k' k == .eq then none else lookupSorted cmp k' xs := by
  induction xs with
  | nil =>
    simp only [eraseSorted, lookupSorted]
    cases cmp k' k <;> rfl
  | cons q rest ih =>
    cases hxs with
    | cons hq hrest =>
      simp only [eraseSorted]
      cases hkq : cmp k q.1 with
      | lt =>
        simp only [lookupSorted]
        cases hk'q : cmp k' q.1 with
        | lt =>
          cases cmp k' k <;> rfl
        | eq =>
          have hkk' : cmp k k' = .lt := cmp_lt_of_lt_of_eq cmp hkq (by
            have hsw := Std.OrientedCmp.eq_swap (cmp := cmp) (a := q.1) (b := k')
            rw [hk'q] at hsw; exact hsw)
          have hk'k : cmp k' k = .gt := (cmp_gt_iff_lt cmp).2 hkk'
          simp [hk'k]
        | gt =>
          have hqk' : cmp q.1 k' = .lt := (cmp_gt_iff_lt cmp).1 hk'q
          have hkk' : cmp k k' = .lt := cmp_lt_trans cmp hkq hqk'
          have hk'k : cmp k' k = .gt := (cmp_gt_iff_lt cmp).2 hkk'
          simp [hk'k]
      | eq =>
        have heq : k = q.1 := Std.LawfulEqCmp.eq_of_compare hkq
        subst heq
        simp only [lookupSorted]
        cases hk'k : cmp k' q.1 with
        | lt =>
          have hnone : lookupSorted cmp k' rest = none :=
            lookupSorted_eq_none_of_forall_lt cmp (fun p hp => cmp_lt_trans cmp hk'k (hq p hp))
          simp [hnone]
        | eq =>
          have hnone : lookupSorted cmp k' rest = none :=
            lookupSorted_eq_none_of_forall_lt cmp (fun p hp => cmp_lt_of_eq_of_lt cmp hk'k (hq p hp))
          simp [hnone]
        | gt =>
          simp
      | gt =>
        have hqk : cmp q.1 k = .lt := (cmp_gt_iff_lt cmp).1 hkq
        simp only [lookupSorted]
        cases hk'q : cmp k' q.1 with
        | lt =>
          have hk'k : cmp k' k = .lt := cmp_lt_trans cmp hk'q hqk
          simp [hk'k]
        | eq =>
          have hk'k : cmp k' k = .lt := cmp_lt_of_eq_of_lt cmp hk'q hqk
          simp [hk'k]
        | gt =>
          exact ih hrest

/-- Extensionality for strictly sorted association lists: pointwise equal `lookupSorted` implies equality. -/
theorem strictlySorted_eq_of_lookupSorted_eq [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    {xs ys : List (α × β)} (hxs : StrictlySorted cmp xs) (hys : StrictlySorted cmp ys)
    (heq : ∀ k, lookupSorted cmp k xs = lookupSorted cmp k ys) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y rest =>
      have h := heq y.1
      simp [lookupSorted, Std.ReflCmp.compare_self] at h
  | cons x xs ih =>
    cases ys with
    | nil =>
      have h := heq x.1
      simp [lookupSorted, Std.ReflCmp.compare_self] at h
    | cons y ys =>
      cases hxs with
      | cons hx hxs' =>
        cases hys with
        | cons hy hys' =>
          cases hxy : cmp x.1 y.1 with
          | lt =>
            have h := heq x.1
            simp [lookupSorted, Std.ReflCmp.compare_self, hxy] at h
          | gt =>
            have hyx : cmp y.1 x.1 = .lt := (cmp_gt_iff_lt cmp).1 hxy
            have h := heq y.1
            simp [lookupSorted, Std.ReflCmp.compare_self, hyx] at h
          | eq =>
            have hkx : x.1 = y.1 := Std.LawfulEqCmp.eq_of_compare hxy
            have hv : x.2 = y.2 := by
              have h := heq x.1
              simp [lookupSorted, Std.ReflCmp.compare_self, hxy] at h
              exact h
            have hxy_pair : x = y := Prod.ext hkx hv
            subst hxy_pair
            congr 1
            apply ih hxs' hys'
            intro k
            cases hkx' : cmp k x.1 with
            | lt =>
              rw [lookupSorted_eq_none_of_forall_lt cmp (fun p hp => cmp_lt_trans cmp hkx' (hx p hp))]
              rw [lookupSorted_eq_none_of_forall_lt cmp (fun p hp => cmp_lt_trans cmp hkx' (hy p hp))]
            | eq =>
              rw [lookupSorted_eq_none_of_forall_lt cmp (fun p hp => cmp_lt_of_eq_of_lt cmp hkx' (hx p hp))]
              rw [lookupSorted_eq_none_of_forall_lt cmp (fun p hp => cmp_lt_of_eq_of_lt cmp hkx' (hy p hp))]
            | gt =>
              have h := heq k
              simp only [lookupSorted, hkx'] at h
              exact h

/-- Linear scan (`List.find?` using `cmp`) agrees with `lookupSorted` on strictly sorted lists. -/
theorem linearFind?_eq_lookupSorted [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    {k : α} {xs : List (α × β)} (hxs : StrictlySorted cmp xs) :
    (xs.find? (fun p => cmp k p.1 == .eq)).map Prod.snd = lookupSorted cmp k xs := by
  induction xs with
  | nil => rfl
  | cons p rest ih =>
    cases hxs with
    | cons hp hrest =>
      simp only [List.find?, lookupSorted]
      cases hkp : cmp k p.1 with
      | lt =>
        simp only [show (Ordering.lt == Ordering.eq) = false from rfl]
        rw [ih hrest]
        exact lookupSorted_eq_none_of_forall_lt cmp (fun q hq => cmp_lt_trans cmp hkp (hp q hq))
      | eq =>
        simp
      | gt =>
        simp only [show (Ordering.gt == Ordering.eq) = false from rfl]
        exact ih hrest

end OrderedListSpec

/-- Balanced AA-tree representation backing `ExtTreeMap0` (`0 Classical.choice`). -/
inductive RawAATree (α : Type u) (β : Type v) where
  | nil : RawAATree α β
  | node (lvl : Nat) (k : α) (v : β) (l r : RawAATree α β) : RawAATree α β

namespace RawAATree

variable {α : Type u} {β : Type v}

def level : RawAATree α β → Nat
  | .nil => 0
  | .node lvl _ _ _ _ => lvl

def toList : RawAATree α β → List (α × β)
  | .nil => []
  | .node _ k v l r => l.toList ++ (k, v) :: r.toList

def size : RawAATree α β → Nat
  | .nil => 0
  | .node _ _ _ l r => l.size + 1 + r.size

theorem size_eq_length_toList (t : RawAATree α β) : t.size = t.toList.length := by
  induction t with
  | nil => rfl
  | node _ _ _ l r ihl ihr =>
    simp [size, toList, ihl, ihr]
    omega

/-- AA-tree `skew` right-rotation eliminating a left horizontal link. -/
def skew : RawAATree α β → RawAATree α β
  | .node lvl k v (.node llvl lk lv ll lr) r =>
    if llvl == lvl then
      .node llvl lk lv ll (.node lvl k v lr r)
    else
      .node lvl k v (.node llvl lk lv ll lr) r
  | t => t

theorem toList_skew (t : RawAATree α β) : (skew t).toList = t.toList := by
  cases t with
  | nil => rfl
  | node lvl k v l r =>
    cases l with
    | nil => rfl
    | node llvl lk lv ll lr =>
      simp only [skew]
      split
      · simp [toList, List.append_assoc]
      · rfl

/-- AA-tree `split` left-rotation eliminating two consecutive right horizontal links. -/
def split : RawAATree α β → RawAATree α β
  | .node lvl k v l (.node rlvl rk rv rl (.node rrlvl rrk rrv rrl rrr)) =>
    if lvl == rrlvl then
      .node (rlvl + 1) rk rv (.node lvl k v l rl) (.node rrlvl rrk rrv rrl rrr)
    else
      .node lvl k v l (.node rlvl rk rv rl (.node rrlvl rrk rrv rrl rrr))
  | t => t

theorem toList_split (t : RawAATree α β) : (split t).toList = t.toList := by
  cases t with
  | nil => rfl
  | node lvl k v l r =>
    cases r with
    | nil => rfl
    | node rlvl rk rv rl rr =>
      cases rr with
      | nil => rfl
      | node rrlvl rrk rrv rrl rrr =>
        simp only [split]
        split
        · simp [toList, List.append_assoc]
        · rfl

/-- AA-tree `decreaseLevel` restoring level invariants after deletion. -/
def decreaseLevel : RawAATree α β → RawAATree α β
  | .node lvl k v l r =>
    let shouldBe := Nat.min l.level r.level + 1
    if shouldBe < lvl then
      let r' :=
        match r with
        | .node rlvl rk rv rl rr =>
          if shouldBe < rlvl then .node shouldBe rk rv rl rr else r
        | .nil => .nil
      .node shouldBe k v l r'
    else
      .node lvl k v l r
  | .nil => .nil

theorem toList_decreaseLevel (t : RawAATree α β) : (decreaseLevel t).toList = t.toList := by
  cases t with
  | nil => rfl
  | node lvl k v l r =>
    simp only [decreaseLevel]
    split
    · cases r with
      | nil => rfl
      | node rlvl rk rv rl rr =>
        simp only
        split <;> rfl
    · rfl

/-- Post-deletion AA-tree rebalancing sequence. -/
def rebalanceAfterErase (t : RawAATree α β) : RawAATree α β :=
  let t1 := skew (decreaseLevel t)
  let t2 :=
    match t1 with
    | .node lvl k v l r =>
      let r1 := skew r
      let r2 :=
        match r1 with
        | .node rlvl rk rv rl rr => .node rlvl rk rv rl (skew rr)
        | .nil => .nil
      .node lvl k v l r2
    | .nil => .nil
  let t3 := split t2
  match t3 with
  | .node lvl k v l r => .node lvl k v l (split r)
  | .nil => .nil

theorem toList_rebalanceAfterErase (t : RawAATree α β) :
    (rebalanceAfterErase t).toList = t.toList := by
  unfold rebalanceAfterErase
  have h1 : (skew (decreaseLevel t)).toList = t.toList := by
    rw [toList_skew, toList_decreaseLevel]
  have h2 :
      (match skew (decreaseLevel t) with
       | RawAATree.node lvl k v l r =>
         let r1 := skew r
         let r2 :=
           match r1 with
           | RawAATree.node rlvl rk rv rl rr => RawAATree.node rlvl rk rv rl (skew rr)
           | RawAATree.nil => RawAATree.nil
         RawAATree.node lvl k v l r2
       | RawAATree.nil => RawAATree.nil).toList = (skew (decreaseLevel t)).toList := by
    cases h : skew (decreaseLevel t) with
    | nil => rfl
    | node lvl k v l r =>
      simp only
      have hr : (skew r).toList = r.toList := toList_skew r
      cases hr1 : skew r with
      | nil => simp [toList, ← hr, hr1]
      | node rlvl rk rv rl rr =>
        simp [toList, toList_skew, ← hr, hr1]
  have h3 : ∀ u : RawAATree α β,
      (match split u with
       | RawAATree.node lvl k v l r => RawAATree.node lvl k v l (split r)
       | RawAATree.nil => RawAATree.nil).toList = u.toList := by
    intro u
    have hs := toList_split u
    cases hu : split u with
    | nil => rw [← hs, hu]
    | node lvl k v l r =>
      simp only [toList, toList_split]
      rw [← hs, hu]; rfl
  rw [h3, h2, h1]

/-- Extract the minimum entry from a non-empty `RawAATree`. -/
def popMin : RawAATree α β → Option (α × β × RawAATree α β)
  | .nil => none
  | .node _ k v .nil r => some (k, v, r)
  | .node lvl k v l r =>
    match popMin l with
    | none => some (k, v, r)
    | some (mk, mv, l') => some (mk, mv, rebalanceAfterErase (.node lvl k v l' r))

theorem popMin_node_isSome (lvl : Nat) (k : α) (v : β) (l r : RawAATree α β) :
    (popMin (.node lvl k v l r)).isSome = true := by
  cases l with
  | nil => rfl
  | node llvl lk lv ll lr =>
    simp only [popMin]
    cases popMin (.node llvl lk lv ll lr) <;> rfl

theorem toList_popMin (t : RawAATree α β) {mk : α} {mv : β} {t' : RawAATree α β}
    (h : popMin t = some (mk, mv, t')) :
    t.toList = (mk, mv) :: t'.toList := by
  induction t generalizing mk mv t' with
  | nil => cases h
  | node lvl k v l r ihl _ =>
    cases l with
    | nil =>
      simp [popMin] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      simp [toList]
    | node llvl lk lv ll lr =>
      simp only [popMin] at h
      cases hp : popMin (.node llvl lk lv ll lr) with
      | none =>
        have hsome := popMin_node_isSome llvl lk lv ll lr
        rw [hp] at hsome; cases hsome
      | some res =>
        rcases res with ⟨mk', mv', l'⟩
        rw [hp] at h
        injection h with h
        rcases Prod.mk.inj h with ⟨rfl, hrest⟩
        rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
        have hl := ihl hp
        rw [toList_rebalanceAfterErase]
        change (RawAATree.node llvl lk lv ll lr).toList ++ (k, v) :: r.toList =
          (mk', mv') :: (l'.toList ++ (k, v) :: r.toList)
        rw [hl]; rfl

/-- Constructive BST invariant: the in-order traversal is strictly sorted under `cmp`. -/
def BST (cmp : α → α → Ordering) (t : RawAATree α β) : Prop :=
  StrictlySorted cmp t.toList

theorem bst_node_parts {cmp : α → α → Ordering} {lvl : Nat} {k : α} {v : β}
    {l r : RawAATree α β} (h : BST cmp (.node lvl k v l r)) :
    BST cmp l ∧ BST cmp r ∧
    (∀ p ∈ l.toList, cmp p.1 k = .lt) ∧
    (∀ p ∈ r.toList, cmp k p.1 = .lt) := by
  unfold BST StrictlySorted at h
  simp only [toList] at h
  rw [List.pairwise_append] at h
  rcases h with ⟨hl, hkr, hcross⟩
  cases hkr with
  | cons hk hr =>
    refine ⟨hl, hr, ?_, hk⟩
    intro p hp
    exact hcross p hp (k, v) (List.mem_cons_self ..)

/-- Lookup in a `RawAATree`. -/
def get? (cmp : α → α → Ordering) (k : α) : RawAATree α β → Option β
  | .nil => none
  | .node _ k' v' l r =>
    match cmp k k' with
    | .lt => get? cmp k l
    | .eq => some v'
    | .gt => get? cmp k r

/-- Balanced insertion in a `RawAATree`. -/
def insert (cmp : α → α → Ordering) (k : α) (v : β) : RawAATree α β → RawAATree α β
  | .nil => .node 1 k v .nil .nil
  | .node lvl k' v' l r =>
    match cmp k k' with
    | .lt => split (skew (.node lvl k' v' (insert cmp k v l) r))
    | .eq => .node lvl k v l r
    | .gt => split (skew (.node lvl k' v' l (insert cmp k v r)))

/-- Balanced erasure in a `RawAATree`. -/
def erase (cmp : α → α → Ordering) (k : α) : RawAATree α β → RawAATree α β
  | .nil => .nil
  | .node lvl k' v' l r =>
    match cmp k k' with
    | .lt => rebalanceAfterErase (.node lvl k' v' (erase cmp k l) r)
    | .gt => rebalanceAfterErase (.node lvl k' v' l (erase cmp k r))
    | .eq =>
      match l, r with
      | .nil, r => r
      | l, .nil => l
      | l, r =>
        match popMin r with
        | none => l
        | some (sk, sv, r') => rebalanceAfterErase (.node lvl sk sv l r')

theorem get?_eq_lookupSorted {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (k : α) {t : RawAATree α β} (ht : BST cmp t) :
    t.get? cmp k = lookupSorted cmp k t.toList := by
  induction t with
  | nil => rfl
  | node lvl k' v' l r ihl ihr =>
    rcases bst_node_parts ht with ⟨hl, hr, hlt, hgt⟩
    simp only [get?, toList]
    rw [lookupSorted_append cmp hlt hgt]
    cases cmp k k' with
    | lt => exact ihl hl
    | eq => rfl
    | gt => exact ihr hr

theorem toList_insert {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (k : α) (v : β) {t : RawAATree α β} (ht : BST cmp t) :
    (t.insert cmp k v).toList = insertSorted cmp k v t.toList := by
  induction t with
  | nil => rfl
  | node lvl k' v' l r ihl ihr =>
    rcases bst_node_parts ht with ⟨hl, hr, hlt, _⟩
    simp only [insert, toList]
    rw [insertSorted_append cmp hlt]
    cases hkk' : cmp k k' with
    | lt =>
      rw [toList_split, toList_skew]
      simp [toList, ihl hl]
    | eq =>
      simp [toList]
    | gt =>
      rw [toList_split, toList_skew]
      simp [toList, ihr hr]

theorem bst_insert {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (k : α) (v : β) {t : RawAATree α β} (ht : BST cmp t) :
    BST cmp (t.insert cmp k v) := by
  unfold BST
  rw [toList_insert k v ht]
  exact strictlySorted_insertSorted cmp ht

theorem toList_erase {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (k : α) {t : RawAATree α β} (ht : BST cmp t) :
    (t.erase cmp k).toList = eraseSorted cmp k t.toList := by
  induction t with
  | nil => rfl
  | node lvl k' v' l r ihl ihr =>
    rcases bst_node_parts ht with ⟨hl, hr, hlt, _⟩
    simp only [erase, toList]
    rw [eraseSorted_append cmp hlt]
    cases hkk' : cmp k k' with
    | lt =>
      rw [toList_rebalanceAfterErase]
      simp [toList, ihl hl]
    | gt =>
      rw [toList_rebalanceAfterErase]
      simp [toList, ihr hr]
    | eq =>
      cases l with
      | nil =>
        simp [toList]
      | node llvl lk lv ll lr =>
        cases r with
        | nil =>
          simp [toList]
        | node rlvl rk rv rl rr =>
          simp only
          cases hp : popMin (.node rlvl rk rv rl rr) with
          | none =>
            have hsome := popMin_node_isSome rlvl rk rv rl rr
            rw [hp] at hsome; cases hsome
          | some res =>
            rcases res with ⟨sk, sv, r'⟩
            rw [toList_rebalanceAfterErase]
            have hrlist := toList_popMin (.node rlvl rk rv rl rr) hp
            change (RawAATree.node llvl lk lv ll lr).toList ++ (sk, sv) :: r'.toList =
              (RawAATree.node llvl lk lv ll lr).toList ++ (RawAATree.node rlvl rk rv rl rr).toList
            rw [hrlist]

theorem bst_erase {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (k : α) {t : RawAATree α β} (ht : BST cmp t) :
    BST cmp (t.erase cmp k) := by
  unfold BST
  rw [toList_erase k ht]
  exact strictlySorted_eraseSorted cmp ht

end RawAATree

/-- Well-formed AA-tree carrier for `ExtTreeMap0`. -/
structure WFNode (α : Type u) (β : Type v) (cmp : α → α → Ordering) where
  tree : RawAATree α β
  bst : RawAATree.BST cmp tree

/-- Equivalence relation equating BST-valid AA-trees with identical sorted `toList`. -/
def ExtTreeMap0Rel (cmp : α → α → Ordering) (a b : WFNode α β cmp) : Prop :=
  a.tree.toList = b.tree.toList

/-- Constructive quotient-extensional balanced tree map (`{propext, Quot.sound}` only, `0 Classical.choice`). -/
structure ExtTreeMap0 (α : Type u) (β : Type v) (cmp : α → α → Ordering) : Type (max u v) where
  rep : Quot (@ExtTreeMap0Rel α β cmp)

namespace ExtTreeMap0

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering}

/-- Empty map. -/
def empty : ExtTreeMap0 α β cmp :=
  ⟨Quot.mk _ ⟨.nil, List.Pairwise.nil⟩⟩

instance : EmptyCollection (ExtTreeMap0 α β cmp) := ⟨empty⟩

instance : Inhabited (ExtTreeMap0 α β cmp) := ⟨empty⟩

theorem empty_eq_emptyc : (empty : ExtTreeMap0 α β cmp) = ∅ := rfl

/-- Sorted association-list view. -/
def toList (m : ExtTreeMap0 α β cmp) : List (α × β) :=
  Quot.lift (fun (n : WFNode α β cmp) => n.tree.toList) (fun _ _ h => h) m.rep

theorem toList_strictlySorted (m : ExtTreeMap0 α β cmp) : StrictlySorted cmp m.toList := by
  rcases m with ⟨q⟩
  induction q using Quot.ind with
  | _ n => exact n.bst

/-- Number of entries in the map. -/
def size (m : ExtTreeMap0 α β cmp) : Nat :=
  Quot.lift (fun (n : WFNode α β cmp) => n.tree.size)
    (fun a b h => by
      rw [RawAATree.size_eq_length_toList, RawAATree.size_eq_length_toList, h])
    m.rep

theorem size_empty : (empty : ExtTreeMap0 α β cmp).size = 0 := rfl

theorem size_eq_length_toList (m : ExtTreeMap0 α β cmp) : m.size = m.toList.length := by
  rcases m with ⟨q⟩
  induction q using Quot.ind with
  | _ n => exact RawAATree.size_eq_length_toList n.tree

/-- Lookup by key. -/
def get? [Std.TransCmp cmp] (m : ExtTreeMap0 α β cmp) (k : α) : Option β :=
  Quot.lift (fun (n : WFNode α β cmp) => n.tree.get? cmp k)
    (fun a b h => by
      rw [RawAATree.get?_eq_lookupSorted k a.bst, RawAATree.get?_eq_lookupSorted k b.bst, h])
    m.rep

instance [Std.TransCmp cmp] : GetElem? (ExtTreeMap0 α β cmp) α β (fun m k => (m.get? k).isSome) where
  getElem m k h := (m.get? k).get h
  getElem? m k := m.get? k

theorem getElem?_eq_get? [Std.TransCmp cmp] (m : ExtTreeMap0 α β cmp) (k : α) :
    m[k]? = m.get? k := rfl

theorem get?_eq_lookupSorted_toList [Std.TransCmp cmp] (m : ExtTreeMap0 α β cmp) (k : α) :
    m.get? k = lookupSorted cmp k m.toList := by
  rcases m with ⟨q⟩
  induction q using Quot.ind with
  | _ n => exact RawAATree.get?_eq_lookupSorted k n.bst

theorem get?_empty [Std.TransCmp cmp] (k : α) :
    (empty : ExtTreeMap0 α β cmp).get? k = none := rfl

/-- Boolean membership query. -/
def contains [Std.TransCmp cmp] (m : ExtTreeMap0 α β cmp) (k : α) : Bool :=
  (m.get? k).isSome

theorem contains_eq_isSome_get? [Std.TransCmp cmp] (m : ExtTreeMap0 α β cmp) (k : α) :
    m.contains k = (m.get? k).isSome := rfl

/-- Insert or replace `(k, v)`. -/
def insert [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (m : ExtTreeMap0 α β cmp) (k : α) (v : β) : ExtTreeMap0 α β cmp :=
  ⟨Quot.lift
    (fun (n : WFNode α β cmp) => Quot.mk _ ⟨n.tree.insert cmp k v, RawAATree.bst_insert k v n.bst⟩)
    (fun a b h => Quot.sound (by
      change (a.tree.insert cmp k v).toList = (b.tree.insert cmp k v).toList
      rw [RawAATree.toList_insert k v a.bst, RawAATree.toList_insert k v b.bst, h]))
    m.rep⟩

/-- Erase `k` if present. -/
def erase [Std.TransCmp cmp]
    (m : ExtTreeMap0 α β cmp) (k : α) : ExtTreeMap0 α β cmp :=
  ⟨Quot.lift
    (fun (n : WFNode α β cmp) => Quot.mk _ ⟨n.tree.erase cmp k, RawAATree.bst_erase k n.bst⟩)
    (fun a b h => Quot.sound (by
      change (a.tree.erase cmp k).toList = (b.tree.erase cmp k).toList
      rw [RawAATree.toList_erase k a.bst, RawAATree.toList_erase k b.bst, h]))
    m.rep⟩

/-- Build an `ExtTreeMap0` from an association list (later entries overwrite earlier ones). -/
def ofList [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] (xs : List (α × β)) : ExtTreeMap0 α β cmp :=
  xs.foldl (fun acc p => acc.insert p.1 p.2) empty

theorem toList_insert [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (m : ExtTreeMap0 α β cmp) (k : α) (v : β) :
    (m.insert k v).toList = insertSorted cmp k v m.toList := by
  rcases m with ⟨q⟩
  induction q using Quot.ind with
  | _ n => exact RawAATree.toList_insert k v n.bst

theorem toList_erase [Std.TransCmp cmp]
    (m : ExtTreeMap0 α β cmp) (k : α) :
    (m.erase k).toList = eraseSorted cmp k m.toList := by
  rcases m with ⟨q⟩
  induction q using Quot.ind with
  | _ n => exact RawAATree.toList_erase k n.bst

theorem get?_insert [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (m : ExtTreeMap0 α β cmp) (k k' : α) (v : β) :
    (m.insert k v).get? k' = if cmp k' k == .eq then some v else m.get? k' := by
  rw [get?_eq_lookupSorted_toList, toList_insert,
    lookupSorted_insertSorted cmp (toList_strictlySorted m),
    ← get?_eq_lookupSorted_toList]

theorem get?_insert_self [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (m : ExtTreeMap0 α β cmp) (k : α) (v : β) :
    (m.insert k v).get? k = some v := by
  rw [get?_insert, Std.ReflCmp.compare_self (cmp := cmp)]; rfl

theorem get?_insert_ne [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (m : ExtTreeMap0 α β cmp) {k k' : α} (v : β) (hne : k' ≠ k) :
    (m.insert k v).get? k' = m.get? k' := by
  rw [get?_insert]
  cases h : cmp k' k with
  | eq => exact False.elim (hne (Std.LawfulEqCmp.eq_of_compare h))
  | lt => rfl
  | gt => rfl

theorem get?_erase [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (m : ExtTreeMap0 α β cmp) (k k' : α) :
    (m.erase k).get? k' = if cmp k' k == .eq then none else m.get? k' := by
  rw [get?_eq_lookupSorted_toList, toList_erase,
    lookupSorted_eraseSorted cmp (toList_strictlySorted m),
    ← get?_eq_lookupSorted_toList]

theorem get?_erase_self [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (m : ExtTreeMap0 α β cmp) (k : α) :
    (m.erase k).get? k = none := by
  rw [get?_erase, Std.ReflCmp.compare_self (cmp := cmp)]; rfl

theorem get?_erase_ne [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (m : ExtTreeMap0 α β cmp) {k k' : α} (hne : k' ≠ k) :
    (m.erase k).get? k' = m.get? k' := by
  rw [get?_erase]
  cases h : cmp k' k with
  | eq => exact False.elim (hne (Std.LawfulEqCmp.eq_of_compare h))
  | lt => rfl
  | gt => rfl

theorem toList_inj {m₁ m₂ : ExtTreeMap0 α β cmp} (h : m₁.toList = m₂.toList) : m₁ = m₂ := by
  rcases m₁ with ⟨q₁⟩
  rcases m₂ with ⟨q₂⟩
  congr 1
  induction q₁ using Quot.ind with
  | _ a =>
    induction q₂ using Quot.ind with
    | _ b => exact Quot.sound h

/-- Propositional extensionality for `ExtTreeMap0` via `get?` (`{propext, Quot.sound}` only). -/
@[ext]
theorem ext_get? [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    {m₁ m₂ : ExtTreeMap0 α β cmp} (h : ∀ k, m₁.get? k = m₂.get? k) : m₁ = m₂ := by
  apply toList_inj
  apply strictlySorted_eq_of_lookupSorted_eq cmp (toList_strictlySorted m₁) (toList_strictlySorted m₂)
  intro k
  rw [← get?_eq_lookupSorted_toList, ← get?_eq_lookupSorted_toList]
  exact h k

/-- Propositional extensionality for `ExtTreeMap0` via `getElem?` (`m[k]?`). -/
theorem ext_getElem? [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    {m₁ m₂ : ExtTreeMap0 α β cmp} (h : ∀ (k : α), m₁[k]? = m₂[k]?) : m₁ = m₂ :=
  ext_get? h

theorem insert_insert_same [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (m : ExtTreeMap0 α β cmp) (k : α) (v₁ v₂ : β) :
    (m.insert k v₁).insert k v₂ = m.insert k v₂ := by
  apply ext_get?
  intro k'
  rw [get?_insert, get?_insert, get?_insert]
  cases cmp k' k <;> rfl

theorem erase_insert_self_of_none [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (m : ExtTreeMap0 α β cmp) (k : α) (v : β) (hnone : m.get? k = none) :
    (m.insert k v).erase k = m := by
  apply ext_get?
  intro k'
  rw [get?_erase, get?_insert]
  cases h : cmp k' k with
  | eq =>
    have heq : k' = k := Std.LawfulEqCmp.eq_of_compare h
    subst heq; exact hnone.symm
  | lt => rfl
  | gt => rfl

/-- Linear scan over `m.toList` equals `m.get?`. -/
theorem linearFind?_toList [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (m : ExtTreeMap0 α β cmp) (k : α) :
    (m.toList.find? (fun p => cmp k p.1 == .eq)).map Prod.snd = m.get? k := by
  rw [linearFind?_eq_lookupSorted cmp (toList_strictlySorted m), ← get?_eq_lookupSorted_toList]

/-- Pointwise agreement predicate between `ExtTreeMap0` and `Std.TreeMap.Raw` (`WF`-free). -/
def AgreesWithStdRaw [Std.TransCmp cmp]
    (m : ExtTreeMap0 α β cmp) (raw : Std.TreeMap.Raw α β cmp) : Prop :=
  ∀ k, m.get? k = raw.get? k

theorem agreesWithStdRaw_empty [Std.TransCmp cmp] :
    AgreesWithStdRaw (empty : ExtTreeMap0 α β cmp) (Std.TreeMap.Raw.empty : Std.TreeMap.Raw α β cmp) := by
  intro k; rfl

/-- Concrete map operation trace for operational cross-checking against `Std.TreeMap.Raw`. -/
inductive MapTraceOp (α : Type u) (β : Type v) where
  | insert (k : α) (v : β)
  | erase (k : α)
  deriving DecidableEq, Repr

/-- Execute a `MapTraceOp` trace on `ExtTreeMap0`. -/
def execMapTraceExt0 [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (ops : List (MapTraceOp α β)) (init : ExtTreeMap0 α β cmp := empty) : ExtTreeMap0 α β cmp :=
  ops.foldl (fun acc op =>
    match op with
    | .insert k v => acc.insert k v
    | .erase k => acc.erase k) init

/-- Execute a `MapTraceOp` trace on `Std.TreeMap.Raw` (`0` axioms). -/
def execMapTraceStdRaw
    (ops : List (MapTraceOp α β))
    (init : Std.TreeMap.Raw α β cmp := Std.TreeMap.Raw.empty) : Std.TreeMap.Raw α β cmp :=
  ops.foldl (fun acc op =>
    match op with
    | .insert k v => acc.insert k v
    | .erase k => acc.erase k) init

theorem execMapTraceExt0_snoc_insert [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (ops : List (MapTraceOp α β)) (init : ExtTreeMap0 α β cmp) (k k' : α) (v : β) :
    (execMapTraceExt0 (ops ++ [.insert k v]) init).get? k' =
      if cmp k' k == .eq then some v else (execMapTraceExt0 ops init).get? k' := by
  simp only [execMapTraceExt0, List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact get?_insert _ k k' v

end ExtTreeMap0

/-! ### 1.3 `KeyedAllocTable`, `KeyedAllocWorld`, `LinearAllocWorld`, `AllocWorldRel`, and Miri Deallocation -/

/-- Allocation memory kind mirroring `Miri.Memory.MemoryKind`. -/
inductive AllocMemKind where
  | stack
  | callerLocation
  | heap
  | global
  deriving DecidableEq, Repr, Inhabited

/-- Allocation mutability mirroring `Miri.ABI.Mutability` / `MirAst.Mutability`. -/
inductive AllocMutability where
  | not
  | mut
  deriving DecidableEq, Repr, Inhabited

/-- Global allocation kind mirroring `Miri.Memory.GlobalAllocationKind`. -/
inductive GlobalAllocKind where
  | function
  | vtable
  | typeId
  | static
  | memory
  deriving DecidableEq, Repr, Inhabited

/-- Single abstract memory byte carrying optional allocation provenance (shared by Parts 1 and 3C). -/
inductive MemByte where
  | uninit
  | init (val : UInt8) (prov : Option MiriAllocId := none)
  deriving DecidableEq, Repr, Inhabited

/-- Metadata and byte payload for a live local allocation. -/
structure LiveAllocEntry where
  sizeBytes : UInt64
  alignPow2 : UInt8
  kind : AllocMemKind
  mutability : AllocMutability
  bytes : List MemByte := []
  deriving DecidableEq, Repr, Inhabited

/-- Tombstone record retained for a deallocated allocation. -/
structure DeadAllocEntry where
  sizeBytes : UInt64
  alignPow2 : UInt8
  deriving DecidableEq, Repr, Inhabited

/-- Metadata and optional payload bytes for a compiler/runtime global allocation. Only `.static` and
`.memory` globals expose dereferenceable `.liveData` bytes; `.function` / `.vtable` / `.typeId`
globals leave `bytes := []`. -/
structure GlobalAllocEntry where
  kind : GlobalAllocKind
  sizeBytes : UInt64
  alignPow2 : UInt8
  mutability : AllocMutability := .not
  bytes : List MemByte := []
  deriving DecidableEq, Repr, Inhabited

/-- Allocation classification returned by `getAllocInfo`, mirroring `Miri.Memory.AllocationKind`
(`rustc_const_eval::interpret::AllocKind`). Miri's `extra_fn_ptr_map` and va-list tables are not
modeled, so `.function` arises only from `GlobalAllocKind.function` globals. -/
inductive AllocInfoKind where
  | liveData
  | function
  | vtable
  | typeId
  | dead
  deriving DecidableEq, Repr, Inhabited

/-- Unified allocation info returned by `getAllocInfo` (`Miri.Memory.AllocationInfo`). -/
structure AllocInfo where
  sizeBytes : UInt64
  alignPow2 : UInt8
  kind : AllocInfoKind
  mutability : AllocMutability
  deriving DecidableEq, Repr

/-- Kind-specific `(size, align, kind, mutability)` reported by `get_alloc_info` for a compiler global
(`Miri.Memory.MemoryState.getAllocInfo`): functions and type-ids are `0`-byte align-`1` immutable,
vtables are `0`-byte with their recorded alignment, and only `.static` / `.memory` globals expose
dereferenceable `.liveData` bytes. -/
def GlobalAllocEntry.toAllocInfo (g : GlobalAllocEntry) : AllocInfo :=
  match g.kind with
  | .function => ⟨0, 0, .function, .not⟩
  | .vtable => ⟨0, g.alignPow2, .vtable, .not⟩
  | .typeId => ⟨0, 0, .typeId, .not⟩
  | .static => ⟨g.sizeBytes, g.alignPow2, .liveData, g.mutability⟩
  | .memory => ⟨g.sizeBytes, g.alignPow2, .liveData, g.mutability⟩

/-- Failure modes of `getLiveAllocSizeAndAlign` (`Miri.Memory.LiveAllocationInfoError`). -/
inductive LiveAllocInfoErr where
  | unavailable (allocId : MiriAllocId)
  | useAfterFree (allocId : MiriAllocId)
  deriving DecidableEq, Repr

/-- Per-allocation vector-clock summary tracking writer, primary reader, and additional concurrent readers. -/
structure RaceClockEntry where
  writerThread : UInt32
  writeTimestamp : UInt64
  readerThread : UInt32
  readTimestamp : UInt64
  extraReaders : List (UInt32 × UInt64) := []
  deriving DecidableEq, Repr, Inhabited

/-- Race detector configuration mirroring `Miri.Interpreter.RaceMode` + `race_detecting`. -/
inductive RaceDetectorMode where
  | unconfigured
  | configured (raceDetecting : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- Thread actor performing deallocation, with per-thread vector clock view. -/
structure DeallocActor where
  threadId : UInt32
  observedTimestamp : UInt64
  perThreadView : List (UInt32 × UInt64) := []
  deriving DecidableEq, Repr, Inhabited

namespace DeallocActor

/-- Thread `actor.threadId`'s observed timestamp for thread `tid`. -/
def viewFor (actor : DeallocActor) (tid : UInt32) : UInt64 :=
  match actor.perThreadView.find? (fun p => p.1 == tid) with
  | some (_, ts) => ts
  | none => actor.observedTimestamp

/-- Construct a `DeallocActor` from an explicit vector clock where unlisted threads default to `0`,
matching `Miri.Concurrency.VClock.index` (`VectorClock.lean:221-223`). -/
def ofVClock (threadId : UInt32) (vclock : List (UInt32 × UInt64)) : DeallocActor :=
  { threadId := threadId, observedTimestamp := 0, perThreadView := vclock }

theorem ofVClock_viewFor_unlisted_eq_zero (threadId tid : UInt32)
    (vclock : List (UInt32 × UInt64))
    (hunlisted : vclock.find? (fun p => p.1 == tid) = none) :
    (ofVClock threadId vclock).viewFor tid = 0 := by
  simp [ofVClock, viewFor, hunlisted]

end DeallocActor

/-- Data-race check for deallocation by `actor` against an allocation's `RaceClockEntry`. -/
def hasDeallocDataRace (actor : DeallocActor) (clk : RaceClockEntry) : Bool :=
  let writerRace :=
    clk.writerThread != actor.threadId &&
    clk.writeTimestamp != 0 &&
    actor.viewFor clk.writerThread < clk.writeTimestamp
  let primaryReaderRace :=
    clk.readerThread != actor.threadId &&
    clk.readTimestamp != 0 &&
    actor.viewFor clk.readerThread < clk.readTimestamp
  let extraReaderRace :=
    clk.extraReaders.any fun (rt, rts) =>
      rt != actor.threadId && rts != 0 && actor.viewFor rt < rts
  writerRace || primaryReaderRace || extraReaderRace

/-- Explicit Tree Borrows / machine hook verdict for deallocation. -/
inductive DeallocHookSpec where
  | ok
  | protectedDealloc
  | missingRaceClock
  | customFailure (reason : String)
  deriving DecidableEq, Repr, Inhabited

def DeallocHookSpec.run : DeallocHookSpec → Except String Unit
  | .ok => .ok ()
  | .protectedDealloc => .error "TreeBorrowsProtectedDealloc"
  | .missingRaceClock => .error "MissingVectorClockExtra"
  | .customFailure reason => .error reason

/-- Verdict of Miri's machine `before_memory_deallocation` hook on the detached allocation
(`Miri.Interpreter.AllocationMachine.before`): the data-race stage
(`MachineHooks.memoryRaceAccess … (some .Deallocate)`) runs first — a no-op when the detector is
`unconfigured`, reporting a missing vector clock BEFORE the `raceDetecting` gate, and never racing on
`0`-byte ranges — followed by the Tree Borrows / machine verdict `tb`. -/
def machineDeallocHook (mode : RaceDetectorMode) (actor : DeallocActor) (tb : DeallocHookSpec)
    (clk? : Option RaceClockEntry) (sizeBytes : UInt64) : Except String Unit :=
  match mode with
  | .unconfigured => tb.run
  | .configured raceDetecting =>
    match clk? with
    | none => .error "MissingVectorClockExtra"
    | some clk =>
      if raceDetecting && sizeBytes != 0 && hasDeallocDataRace actor clk then .error "DataRace"
      else tb.run

/-- Requested-layout check of `deallocate_ptr` (`old_size_and_align`): returns the requested
`(size, align)` iff a layout was requested and it differs from the detached allocation's layout. -/
def deallocLayoutMismatch? (entry : LiveAllocEntry) (expectedLayout : Option (UInt64 × UInt8)) :
    Option (UInt64 × UInt8) :=
  match expectedLayout with
  | some (reqSize, reqAlign) =>
    if reqSize != entry.sizeBytes || reqAlign != entry.alignPow2 then some (reqSize, reqAlign)
    else none
  | none => none

/-- Allocation-ID reservation errors. -/
inductive AllocIdErr where
  | exhausted
  | alreadyIssued (allocId : MiriAllocId)
  deriving DecidableEq, Repr

/-- Global-registration failures mirroring `Miri.Memory.MemoryMetadataError`
(`validateReservedGlobal`). -/
inductive GlobalRegErr where
  | duplicateRuntimeId (allocId : MiriAllocId)
  | globalIdAlreadyPresent (allocId : MiriAllocId)
  deriving DecidableEq, Repr

/-- Pointer passed to `deallocate` / `deallocateMachine`. -/
inductive DeallocPtr where
  | dangling (address : UInt64)
  | provenanced (allocId : MiriAllocId) (offset : UInt64)
  deriving DecidableEq, Repr

/-- Exact Miri deallocation lifecycle error categories. -/
inductive DeallocErr where
  | danglingPointer (address : UInt64)
  | nonzeroOffset (allocId : MiriAllocId) (offset : UInt64)
  | globalErr (allocId : MiriAllocId) (kind : GlobalAllocKind)
  | useAfterFree (allocId : MiriAllocId)
  | immutableAllocation (allocId : MiriAllocId)
  | memoryKindMismatch (allocId : MiriAllocId)
  | layoutMismatch (allocId : MiriAllocId)
      (actualSize requestedSize : UInt64) (actualAlign requestedAlign : UInt8)
  | hookFailure (reason : String)
  | duplicateDeadAllocation (allocId : MiriAllocId)
  deriving DecidableEq, Repr

/-- Outcome of `deallocate` / `deallocateMachine`, preserving the detached owner on post-removal errors. -/
structure DeallocResult (W : Type) where
  world : W
  detached : Option (MiriAllocId × LiveAllocEntry)
  outcome : Except DeallocErr Unit
  deriving Repr

/-- Keyed `ExtTreeMap0` tables for live, dead, and race-clock allocation state (`lean-miri#73`). -/
structure KeyedAllocTable where
  live : ExtTreeMap0 MiriAllocId LiveAllocEntry compare := ExtTreeMap0.empty
  dead : ExtTreeMap0 MiriAllocId DeadAllocEntry compare := ExtTreeMap0.empty
  race : ExtTreeMap0 MiriAllocId RaceClockEntry compare := ExtTreeMap0.empty

namespace KeyedAllocTable

def empty : KeyedAllocTable := {}

@[ext]
theorem ext {t₁ t₂ : KeyedAllocTable}
    (hl : ∀ id, t₁.live.get? id = t₂.live.get? id)
    (hd : ∀ id, t₁.dead.get? id = t₂.dead.get? id)
    (hr : ∀ id, t₁.race.get? id = t₂.race.get? id) : t₁ = t₂ := by
  cases t₁; cases t₂
  congr 1
  · exact ExtTreeMap0.ext_get? hl
  · exact ExtTreeMap0.ext_get? hd
  · exact ExtTreeMap0.ext_get? hr

end KeyedAllocTable

/-- Keyed allocation world backed by `ExtTreeMap0` (`lean-miri#73`). -/
structure KeyedAllocWorld where
  nextAllocId : UInt64 := 1
  idSupplyExhausted : Bool := false
  issued : ExtTreeMap0 MiriAllocId Unit compare := ExtTreeMap0.empty
  globals : ExtTreeMap0 MiriAllocId GlobalAllocEntry compare := ExtTreeMap0.empty
  table : KeyedAllocTable := {}

/-- Linear-list allocation world modeling pre-PR-#73 Miri allocation tables. -/
structure LinearAllocWorld where
  nextAllocId : UInt64 := 1
  idSupplyExhausted : Bool := false
  issued : List MiriAllocId := []
  globals : List (MiriAllocId × GlobalAllocEntry) := []
  live : List (MiriAllocId × LiveAllocEntry) := []
  dead : List (MiriAllocId × DeadAllocEntry) := []
  race : List (MiriAllocId × RaceClockEntry) := []
  deriving DecidableEq, Repr

/-- First-match linear lookup by `MiriAllocId`. -/
def linearFind? {α : Type} (xs : List (MiriAllocId × α)) (id : MiriAllocId) : Option α :=
  (xs.find? (fun p => p.1 == id)).map Prod.snd

/-- Build an `ExtTreeMap0` from an association list using right-fold so first occurrences win
(preserving `linearFind?` even on lists with shadowed duplicate keys). -/
def ofLinearRows {α : Type} (xs : List (MiriAllocId × α)) : ExtTreeMap0 MiriAllocId α compare :=
  xs.foldr (fun p acc => acc.insert p.1 p.2) ExtTreeMap0.empty

theorem get?_ofLinearRows {α : Type} (xs : List (MiriAllocId × α)) (id : MiriAllocId) :
    (ofLinearRows xs).get? id = linearFind? xs id := by
  induction xs with
  | nil => rfl
  | cons p rest ih =>
    simp only [ofLinearRows, List.foldr_cons, linearFind?, List.find?]
    by_cases h : p.1 = id
    · subst h
      rw [ExtTreeMap0.get?_insert_self]
      simp
    · have hne : id ≠ p.1 := fun he => h he.symm
      rw [ExtTreeMap0.get?_insert_ne _ _ hne]
      have hbeq : (p.1 == id) = false := beq_false_of_ne h
      simp only [hbeq]
      exact ih

/-- Build an issued-ID `ExtTreeMap0` from a list of `MiriAllocId`s. -/
def ofLinearIssued (xs : List MiriAllocId) : ExtTreeMap0 MiriAllocId Unit compare :=
  xs.foldr (fun id acc => acc.insert id ()) ExtTreeMap0.empty

theorem isSome_get?_ofLinearIssued (xs : List MiriAllocId) (id : MiriAllocId) :
    ((ofLinearIssued xs).get? id).isSome = xs.any (fun x => x == id) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [ofLinearIssued, List.foldr_cons, List.any_cons]
    by_cases h : x = id
    · subst h
      rw [ExtTreeMap0.get?_insert_self]
      simp
    · have hne : id ≠ x := fun he => h he.symm
      rw [ExtTreeMap0.get?_insert_ne _ _ hne]
      have hbeq : (x == id) = false := beq_false_of_ne h
      simp only [hbeq, Bool.false_or]
      exact ih

theorem linearFind?_filter_append_single {α : Type} (xs : List (MiriAllocId × α))
    (id k : MiriAllocId) (v : α) :
    linearFind? (xs.filter (fun p => p.1 != id) ++ [(id, v)]) k =
      if k == id then some v else linearFind? xs k := by
  induction xs with
  | nil =>
    simp only [List.filter_nil, List.nil_append, linearFind?, List.find?]
    by_cases h : k = id
    · subst h; simp
    · have h1 : (id == k) = false := beq_false_of_ne (fun he => h he.symm)
      have h2 : (k == id) = false := beq_false_of_ne h
      simp [h1, h2]
  | cons p rest ih =>
    by_cases hpid : p.1 = id
    · subst hpid
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      rw [ih]
      by_cases hk : k = p.1
      · subst hk; simp
      · have h1 : (k == p.1) = false := beq_false_of_ne hk
        have h2 : (p.1 == k) = false := beq_false_of_ne (fun he => hk he.symm)
        simp [linearFind?, List.find?, h1, h2]
    · have hpbne : (p.1 != id) = true := bne_iff_ne.2 hpid
      simp only [List.filter_cons, hpbne, ↓reduceIte, List.cons_append]
      by_cases hpk : p.1 = k
      · subst hpk
        have hkid : (p.1 == id) = false := beq_false_of_ne hpid
        simp [linearFind?, List.find?, hkid]
      · have h1 : (p.1 == k) = false := beq_false_of_ne hpk
        simp only [linearFind?, List.find?, h1]
        exact ih

theorem linearFind?_filter_ne {α : Type} (xs : List (MiriAllocId × α))
    (id k : MiriAllocId) :
    linearFind? (xs.filter (fun p => p.1 != id)) k =
      if k == id then none else linearFind? xs k := by
  induction xs with
  | nil =>
    simp only [List.filter_nil, linearFind?, List.find?]
    cases k == id <;> rfl
  | cons p rest ih =>
    by_cases hpid : p.1 = id
    · subst hpid
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      rw [ih]
      by_cases hk : k = p.1
      · subst hk; simp
      · have h1 : (k == p.1) = false := beq_false_of_ne hk
        have h2 : (p.1 == k) = false := beq_false_of_ne (fun he => hk he.symm)
        simp [linearFind?, List.find?, h1, h2]
    · have hpbne : (p.1 != id) = true := bne_iff_ne.2 hpid
      simp only [List.filter_cons, hpbne, ↓reduceIte]
      by_cases hpk : p.1 = k
      · subst hpk
        have hkid : (p.1 == id) = false := beq_false_of_ne hpid
        simp [linearFind?, List.find?, hkid]
      · have h1 : (p.1 == k) = false := beq_false_of_ne hpk
        simp only [linearFind?, List.find?, h1]
        exact ih

namespace KeyedAllocWorld

def empty : KeyedAllocWorld := {}

def hasIssued (w : KeyedAllocWorld) (id : MiriAllocId) : Bool :=
  w.issued.contains id

def findGlobal? (w : KeyedAllocWorld) (id : MiriAllocId) : Option GlobalAllocEntry :=
  w.globals.get? id

def findLive? (w : KeyedAllocWorld) (id : MiriAllocId) : Option LiveAllocEntry :=
  w.table.live.get? id

def findDead? (w : KeyedAllocWorld) (id : MiriAllocId) : Option DeadAllocEntry :=
  w.table.dead.get? id

def findRace? (w : KeyedAllocWorld) (id : MiriAllocId) : Option RaceClockEntry :=
  w.table.race.get? id

/-- Keyed worlds with equal scalar fields and pointwise map lookups are propositionally equal. -/
@[ext]
theorem ext {w₁ w₂ : KeyedAllocWorld}
    (hnext : w₁.nextAllocId = w₂.nextAllocId)
    (hexh : w₁.idSupplyExhausted = w₂.idSupplyExhausted)
    (hiss : ∀ id, w₁.hasIssued id = w₂.hasIssued id)
    (hglob : ∀ id, w₁.findGlobal? id = w₂.findGlobal? id)
    (hlive : ∀ id, w₁.findLive? id = w₂.findLive? id)
    (hdead : ∀ id, w₁.findDead? id = w₂.findDead? id)
    (hrace : ∀ id, w₁.findRace? id = w₂.findRace? id) :
    w₁ = w₂ := by
  cases w₁ with | mk n1 e1 i1 g1 t1 =>
  cases w₂ with | mk n2 e2 i2 g2 t2 =>
  simp only at hnext hexh
  subst hnext; subst hexh
  congr 1
  · apply ExtTreeMap0.ext_get?
    intro id
    have h := hiss id
    simp only [hasIssued, ExtTreeMap0.contains_eq_isSome_get?] at h
    cases h1 : i1.get? id with
    | none =>
      cases h2 : i2.get? id with
      | none => rfl
      | some u => simp [h1, h2] at h
    | some u =>
      cases u
      cases h2 : i2.get? id with
      | none => simp [h1, h2] at h
      | some u' => cases u'; rfl
  · exact ExtTreeMap0.ext_get? hglob
  · exact KeyedAllocTable.ext hlive hdead hrace

def containsId (w : KeyedAllocWorld) (id : MiriAllocId) : Bool :=
  (w.findLive? id).isSome || (w.findDead? id).isSome || (w.findGlobal? id).isSome

/-- `is_alloc_live` (`Miri.Memory.MemoryState.isAllocLive`): live local allocations AND compiler
globals (function / vtable / type-id / static / memory) are live; only tombstoned or never-registered
IDs are not. -/
def isAllocLive (w : KeyedAllocWorld) (id : MiriAllocId) : Bool :=
  (w.findLive? id).isSome || (w.findGlobal? id).isSome

/-- `get_alloc_info` (`Miri.Memory.MemoryState.getAllocInfo`) precedence: live local bytes, compiler
globals (kind-specific size/align), then dead-allocation (tombstone) metadata; `none` only for IDs
with no metadata at all. -/
def getAllocInfo (w : KeyedAllocWorld) (id : MiriAllocId) : Option AllocInfo :=
  match w.findLive? id with
  | some e => some ⟨e.sizeBytes, e.alignPow2, .liveData, e.mutability⟩
  | none =>
    match w.findGlobal? id with
    | some g => some g.toAllocInfo
    | none =>
      match w.findDead? id with
      | some d => some ⟨d.sizeBytes, d.alignPow2, .dead, .not⟩
      | none => none

/-- `get_live_alloc_size_and_align` (`Miri.Memory.MemoryState.getLiveAllocSizeAndAlign`): reports
size/align for live locals AND globals, distinguishing a tombstoned allocation (`.useAfterFree`)
from absent metadata (`.unavailable`). -/
def getLiveAllocSizeAndAlign (w : KeyedAllocWorld) (id : MiriAllocId) :
    Except LiveAllocInfoErr (UInt64 × UInt8) :=
  match w.getAllocInfo id with
  | none => .error (.unavailable id)
  | some info =>
    if info.kind == .dead then .error (.useAfterFree id)
    else .ok (info.sizeBytes, info.alignPow2)

/-- Dereferenceable allocation byte storage (`live` local bytes take precedence, else `.static` /
`.memory` global payload bytes; `.function` / `.vtable` / `.typeId` globals and dead/absent IDs
return `none`). -/
def findAllocBytes? (w : KeyedAllocWorld) (id : MiriAllocId) : Option (List MemByte) :=
  match w.findLive? id with
  | some e => some e.bytes
  | none =>
    match w.findGlobal? id with
    | some g =>
      match g.kind with
      | .static | .memory => some g.bytes
      | .function | .vtable | .typeId => none
    | none => none

def insertLive (w : KeyedAllocWorld) (id : MiriAllocId) (entry : LiveAllocEntry) : KeyedAllocWorld :=
  { w with table := { w.table with live := w.table.live.insert id entry } }

def removeLive (w : KeyedAllocWorld) (id : MiriAllocId) : KeyedAllocWorld × Option LiveAllocEntry :=
  match w.findLive? id with
  | none => (w, none)
  | some e => ({ w with table := { w.table with live := w.table.live.erase id } }, some e)

def insertDead (w : KeyedAllocWorld) (id : MiriAllocId) (entry : DeadAllocEntry) : KeyedAllocWorld :=
  { w with table := { w.table with dead := w.table.dead.insert id entry } }

def setRace (w : KeyedAllocWorld) (id : MiriAllocId) (clk : RaceClockEntry) : KeyedAllocWorld :=
  { w with table := { w.table with race := w.table.race.insert id clk } }

def removeRace (w : KeyedAllocWorld) (id : MiriAllocId) : KeyedAllocWorld :=
  { w with table := { w.table with race := w.table.race.erase id } }

def registerGlobal (w : KeyedAllocWorld) (id : MiriAllocId) (entry : GlobalAllocEntry) : KeyedAllocWorld :=
  { w with
    issued := w.issued.insert id ()
    globals := w.globals.insert id entry }

/-- Validated registration of a compiler global under an ALREADY-RESERVED ID
(`Miri.Memory.MemoryState.registerReservedGlobal` / `validateReservedGlobal`): rejects an ID that already
names a global (`.duplicateRuntimeId`), that is live or tombstoned, or that was never issued
(`.globalIdAlreadyPresent`); validation precedes every table update, so a failure returns the exact
input world. Unlike the unvalidated `registerGlobal`, success never touches `issued`. -/
def registerReservedGlobal (w : KeyedAllocWorld) (id : MiriAllocId) (entry : GlobalAllocEntry) :
    KeyedAllocWorld × Except GlobalRegErr Unit :=
  if (w.findGlobal? id).isSome then (w, .error (.duplicateRuntimeId id))
  else if (w.findLive? id).isSome || (w.findDead? id).isSome || !w.hasIssued id then
    (w, .error (.globalIdAlreadyPresent id))
  else ({ w with globals := w.globals.insert id entry }, .ok ())

def updateLiveBytes (w : KeyedAllocWorld) (id : MiriAllocId) (bytes : List MemByte) : KeyedAllocWorld :=
  match w.findLive? id with
  | none => w
  | some e => w.insertLive id { e with bytes := bytes }

/-- `AllocMap::reserve` (`Miri.Memory.MemoryState.reserveAllocId`, `AtomicU64::fetch_add`): the cursor
advances on EVERY non-exhausted attempt — including the `alreadyIssued` collision path and the
zero-sentinel path — and `idSupplyExhausted` latches only when a reservation *observes* the wrapped
`0` sentinel (never eagerly on the successful reservation of `2^64 - 1`). -/
def reserveAllocId (w : KeyedAllocWorld) : KeyedAllocWorld × Except AllocIdErr MiriAllocId :=
  if w.idSupplyExhausted then
    (w, .error .exhausted)
  else
    match MiriAllocId.ofUInt64 w.nextAllocId with
    | none =>
      ({ w with nextAllocId := w.nextAllocId + 1, idSupplyExhausted := true }, .error .exhausted)
    | some id =>
      if w.hasIssued id || w.containsId id then
        ({ w with nextAllocId := w.nextAllocId + 1 }, .error (.alreadyIssued id))
      else
        ({ w with
          nextAllocId := w.nextAllocId + 1
          issued := w.issued.insert id () }, .ok id)

def allocate (w : KeyedAllocWorld) (entry : LiveAllocEntry) :
    KeyedAllocWorld × Except AllocIdErr MiriAllocId :=
  let (w1, res) := w.reserveAllocId
  match res with
  | .error e => (w1, .error e)
  | .ok id => (w1.insertLive id entry, .ok id)

/-- Mode-aware machine allocation: seeds `RaceClockEntry` iff `mode` is `.configured _`. -/
def allocateMachine (w : KeyedAllocWorld) (entry : LiveAllocEntry)
    (mode : RaceDetectorMode) (creatorThread : UInt32) (timestamp : UInt64) :
    KeyedAllocWorld × Except AllocIdErr MiriAllocId :=
  let (w1, res) := w.allocate entry
  match res with
  | .error e => (w1, .error e)
  | .ok id =>
    match mode with
    | .unconfigured => (w1, .ok id)
    | .configured _ =>
      let initClk : RaceClockEntry :=
        { writerThread := creatorThread
          writeTimestamp := timestamp
          readerThread := creatorThread
          readTimestamp := 0
          extraReaders := [] }
      (w1.setRace id initClk, .ok id)

/-- Core `Memory::deallocate_ptr` (`Miri.Memory.MemoryState.deallocatePtrWith`) with exact failure
ordering and detached-state retention, parameterized by the machine `before_memory_deallocation`
hook. The hook observes the world AFTER the live entry was detached (`removeLive`); a hook failure
retains that detached world without tombstoning. -/
def deallocateWith (w : KeyedAllocWorld) (ptr : DeallocPtr)
    (expectedLayout : Option (UInt64 × UInt8)) (expectedKind : AllocMemKind)
    (hook : KeyedAllocWorld → MiriAllocId → LiveAllocEntry → Except String Unit) :
    DeallocResult KeyedAllocWorld :=
  match ptr with
  | .dangling addr => ⟨w, none, .error (.danglingPointer addr)⟩
  | .provenanced id off =>
    if off != 0 then
      ⟨w, none, .error (.nonzeroOffset id off)⟩
    else
      match (w.removeLive id).2 with
      | none =>
        match w.findGlobal? id with
        | some g => ⟨w, none, .error (.globalErr id g.kind)⟩
        | none => ⟨w, none, .error (.useAfterFree id)⟩
      | some entry =>
        if entry.mutability == .not then
          ⟨(w.removeLive id).1, some (id, entry), .error (.immutableAllocation id)⟩
        else if entry.kind != expectedKind then
          ⟨(w.removeLive id).1, some (id, entry), .error (.memoryKindMismatch id)⟩
        else
          match deallocLayoutMismatch? entry expectedLayout with
          | some (reqSize, reqAlign) =>
            ⟨(w.removeLive id).1, some (id, entry),
              .error (.layoutMismatch id entry.sizeBytes reqSize entry.alignPow2 reqAlign)⟩
          | none =>
            match hook (w.removeLive id).1 id entry with
            | .error msg => ⟨(w.removeLive id).1, some (id, entry), .error (.hookFailure msg)⟩
            | .ok () =>
              if ((w.removeLive id).1.findDead? id).isSome then
                ⟨(w.removeLive id).1.insertDead id ⟨entry.sizeBytes, entry.alignPow2⟩,
                  some (id, entry), .error (.duplicateDeadAllocation id)⟩
              else
                ⟨(w.removeLive id).1.insertDead id ⟨entry.sizeBytes, entry.alignPow2⟩,
                  some (id, entry), .ok ()⟩

/-- Core Miri deallocation (`deallocateWith` under a state-independent hook verdict `tb`). -/
def deallocate (w : KeyedAllocWorld) (ptr : DeallocPtr)
    (expectedLayout : Option (UInt64 × UInt8)) (expectedKind : AllocMemKind)
    (tb : DeallocHookSpec := .ok) : DeallocResult KeyedAllocWorld :=
  w.deallocateWith ptr expectedLayout expectedKind (fun _ _ _ => tb.run)

/-- Machine-level detach cleanup (`Miri.Interpreter.AllocationMachine.deallocate`): whenever the live
entry was detached — on success AND on every post-removal failure — the allocation's race clock
leaves the machine together with the detached allocation. -/
def detachRaceClock (res : DeallocResult KeyedAllocWorld) : DeallocResult KeyedAllocWorld :=
  match res.detached with
  | some (id, _) => { res with world := res.world.removeRace id }
  | none => res

/-- Mode-aware machine deallocation (`Miri.Interpreter.AllocationMachine.deallocate`): runs
`deallocateWith` under `machineDeallocHook`, which reads the allocation's vector clock from the
live-detached world (i.e. BEFORE any race-clock cleanup), then applies `detachRaceClock`. -/
def deallocateMachine (w : KeyedAllocWorld) (ptr : DeallocPtr)
    (expectedLayout : Option (UInt64 × UInt8)) (expectedKind : AllocMemKind)
    (mode : RaceDetectorMode) (actor : DeallocActor)
    (tb : DeallocHookSpec := .ok) : DeallocResult KeyedAllocWorld :=
  detachRaceClock (w.deallocateWith ptr expectedLayout expectedKind
    (fun wDetached id entry =>
      machineDeallocHook mode actor tb (wDetached.findRace? id) entry.sizeBytes))

/-- Canonical keyed conversion from any `LinearAllocWorld` (preserving first-match shadowing). -/
def ofLinear (lw : LinearAllocWorld) : KeyedAllocWorld where
  nextAllocId := lw.nextAllocId
  idSupplyExhausted := lw.idSupplyExhausted
  issued := ofLinearIssued lw.issued
  globals := ofLinearRows lw.globals
  table :=
    { live := ofLinearRows lw.live
      dead := ofLinearRows lw.dead
      race := ofLinearRows lw.race }

end KeyedAllocWorld

namespace LinearAllocWorld

def empty : LinearAllocWorld := {}

def hasIssued (lw : LinearAllocWorld) (id : MiriAllocId) : Bool :=
  lw.issued.any (fun x => x == id)

def findGlobal? (lw : LinearAllocWorld) (id : MiriAllocId) : Option GlobalAllocEntry :=
  linearFind? lw.globals id

def findLive? (lw : LinearAllocWorld) (id : MiriAllocId) : Option LiveAllocEntry :=
  linearFind? lw.live id

def findDead? (lw : LinearAllocWorld) (id : MiriAllocId) : Option DeadAllocEntry :=
  linearFind? lw.dead id

def findRace? (lw : LinearAllocWorld) (id : MiriAllocId) : Option RaceClockEntry :=
  linearFind? lw.race id

def containsId (lw : LinearAllocWorld) (id : MiriAllocId) : Bool :=
  (lw.findLive? id).isSome || (lw.findDead? id).isSome || (lw.findGlobal? id).isSome

/-- `is_alloc_live` (`Miri.Memory.MemoryState.isAllocLive`): live local allocations AND compiler
globals (function / vtable / type-id / static / memory) are live; only tombstoned or never-registered
IDs are not. -/
def isAllocLive (lw : LinearAllocWorld) (id : MiriAllocId) : Bool :=
  (lw.findLive? id).isSome || (lw.findGlobal? id).isSome

/-- `get_alloc_info` (`Miri.Memory.MemoryState.getAllocInfo`) precedence: live local bytes, compiler
globals (kind-specific size/align), then dead-allocation (tombstone) metadata; `none` only for IDs
with no metadata at all. -/
def getAllocInfo (lw : LinearAllocWorld) (id : MiriAllocId) : Option AllocInfo :=
  match lw.findLive? id with
  | some e => some ⟨e.sizeBytes, e.alignPow2, .liveData, e.mutability⟩
  | none =>
    match lw.findGlobal? id with
    | some g => some g.toAllocInfo
    | none =>
      match lw.findDead? id with
      | some d => some ⟨d.sizeBytes, d.alignPow2, .dead, .not⟩
      | none => none

/-- `get_live_alloc_size_and_align` (`Miri.Memory.MemoryState.getLiveAllocSizeAndAlign`): reports
size/align for live locals AND globals, distinguishing a tombstoned allocation (`.useAfterFree`)
from absent metadata (`.unavailable`). -/
def getLiveAllocSizeAndAlign (lw : LinearAllocWorld) (id : MiriAllocId) :
    Except LiveAllocInfoErr (UInt64 × UInt8) :=
  match lw.getAllocInfo id with
  | none => .error (.unavailable id)
  | some info =>
    if info.kind == .dead then .error (.useAfterFree id)
    else .ok (info.sizeBytes, info.alignPow2)

/-- Dereferenceable allocation byte storage (`live` local bytes take precedence, else `.static` /
`.memory` global payload bytes; `.function` / `.vtable` / `.typeId` globals and dead/absent IDs
return `none`). -/
def findAllocBytes? (lw : LinearAllocWorld) (id : MiriAllocId) : Option (List MemByte) :=
  match lw.findLive? id with
  | some e => some e.bytes
  | none =>
    match lw.findGlobal? id with
    | some g =>
      match g.kind with
      | .static | .memory => some g.bytes
      | .function | .vtable | .typeId => none
    | none => none

def insertLive (lw : LinearAllocWorld) (id : MiriAllocId) (entry : LiveAllocEntry) : LinearAllocWorld :=
  { lw with live := lw.live.filter (fun p => p.1 != id) ++ [(id, entry)] }

def removeLive (lw : LinearAllocWorld) (id : MiriAllocId) : LinearAllocWorld × Option LiveAllocEntry :=
  match lw.findLive? id with
  | none => (lw, none)
  | some e => ({ lw with live := lw.live.filter (fun p => p.1 != id) }, some e)

def insertDead (lw : LinearAllocWorld) (id : MiriAllocId) (entry : DeadAllocEntry) : LinearAllocWorld :=
  { lw with dead := lw.dead.filter (fun p => p.1 != id) ++ [(id, entry)] }

def setRace (lw : LinearAllocWorld) (id : MiriAllocId) (clk : RaceClockEntry) : LinearAllocWorld :=
  { lw with race := lw.race.filter (fun p => p.1 != id) ++ [(id, clk)] }

def removeRace (lw : LinearAllocWorld) (id : MiriAllocId) : LinearAllocWorld :=
  { lw with race := lw.race.filter (fun p => p.1 != id) }

def registerGlobal (lw : LinearAllocWorld) (id : MiriAllocId) (entry : GlobalAllocEntry) : LinearAllocWorld :=
  { lw with
    issued := id :: lw.issued
    globals := lw.globals.filter (fun p => p.1 != id) ++ [(id, entry)] }

/-- Validated registration of a compiler global under an ALREADY-RESERVED ID
(`Miri.Memory.MemoryState.registerReservedGlobal` / `validateReservedGlobal`); see
`KeyedAllocWorld.registerReservedGlobal`. -/
def registerReservedGlobal (lw : LinearAllocWorld) (id : MiriAllocId) (entry : GlobalAllocEntry) :
    LinearAllocWorld × Except GlobalRegErr Unit :=
  if (lw.findGlobal? id).isSome then (lw, .error (.duplicateRuntimeId id))
  else if (lw.findLive? id).isSome || (lw.findDead? id).isSome || !lw.hasIssued id then
    (lw, .error (.globalIdAlreadyPresent id))
  else ({ lw with globals := lw.globals.filter (fun p => p.1 != id) ++ [(id, entry)] }, .ok ())

def updateLiveBytes (lw : LinearAllocWorld) (id : MiriAllocId) (bytes : List MemByte) : LinearAllocWorld :=
  match lw.findLive? id with
  | none => lw
  | some e => lw.insertLive id { e with bytes := bytes }

/-- `AllocMap::reserve` (`Miri.Memory.MemoryState.reserveAllocId`, `AtomicU64::fetch_add`): the cursor
advances on EVERY non-exhausted attempt — including the `alreadyIssued` collision path and the
zero-sentinel path — and `idSupplyExhausted` latches only when a reservation *observes* the wrapped
`0` sentinel (never eagerly on the successful reservation of `2^64 - 1`). -/
def reserveAllocId (lw : LinearAllocWorld) : LinearAllocWorld × Except AllocIdErr MiriAllocId :=
  if lw.idSupplyExhausted then
    (lw, .error .exhausted)
  else
    match MiriAllocId.ofUInt64 lw.nextAllocId with
    | none =>
      ({ lw with nextAllocId := lw.nextAllocId + 1, idSupplyExhausted := true }, .error .exhausted)
    | some id =>
      if lw.hasIssued id || lw.containsId id then
        ({ lw with nextAllocId := lw.nextAllocId + 1 }, .error (.alreadyIssued id))
      else
        ({ lw with
          nextAllocId := lw.nextAllocId + 1
          issued := id :: lw.issued }, .ok id)

def allocate (lw : LinearAllocWorld) (entry : LiveAllocEntry) :
    LinearAllocWorld × Except AllocIdErr MiriAllocId :=
  let (lw1, res) := lw.reserveAllocId
  match res with
  | .error e => (lw1, .error e)
  | .ok id => (lw1.insertLive id entry, .ok id)

/-- Mode-aware machine allocation: seeds `RaceClockEntry` iff `mode` is `.configured _`. -/
def allocateMachine (lw : LinearAllocWorld) (entry : LiveAllocEntry)
    (mode : RaceDetectorMode) (creatorThread : UInt32) (timestamp : UInt64) :
    LinearAllocWorld × Except AllocIdErr MiriAllocId :=
  let (lw1, res) := lw.allocate entry
  match res with
  | .error e => (lw1, .error e)
  | .ok id =>
    match mode with
    | .unconfigured => (lw1, .ok id)
    | .configured _ =>
      let initClk : RaceClockEntry :=
        { writerThread := creatorThread
          writeTimestamp := timestamp
          readerThread := creatorThread
          readTimestamp := 0
          extraReaders := [] }
      (lw1.setRace id initClk, .ok id)

/-- Core `Memory::deallocate_ptr` (`Miri.Memory.MemoryState.deallocatePtrWith`) with exact failure
ordering and detached-state retention, parameterized by the machine `before_memory_deallocation`
hook. The hook observes the world AFTER the live entry was detached (`removeLive`); a hook failure
retains that detached world without tombstoning. -/
def deallocateWith (lw : LinearAllocWorld) (ptr : DeallocPtr)
    (expectedLayout : Option (UInt64 × UInt8)) (expectedKind : AllocMemKind)
    (hook : LinearAllocWorld → MiriAllocId → LiveAllocEntry → Except String Unit) :
    DeallocResult LinearAllocWorld :=
  match ptr with
  | .dangling addr => ⟨lw, none, .error (.danglingPointer addr)⟩
  | .provenanced id off =>
    if off != 0 then
      ⟨lw, none, .error (.nonzeroOffset id off)⟩
    else
      match (lw.removeLive id).2 with
      | none =>
        match lw.findGlobal? id with
        | some g => ⟨lw, none, .error (.globalErr id g.kind)⟩
        | none => ⟨lw, none, .error (.useAfterFree id)⟩
      | some entry =>
        if entry.mutability == .not then
          ⟨(lw.removeLive id).1, some (id, entry), .error (.immutableAllocation id)⟩
        else if entry.kind != expectedKind then
          ⟨(lw.removeLive id).1, some (id, entry), .error (.memoryKindMismatch id)⟩
        else
          match deallocLayoutMismatch? entry expectedLayout with
          | some (reqSize, reqAlign) =>
            ⟨(lw.removeLive id).1, some (id, entry),
              .error (.layoutMismatch id entry.sizeBytes reqSize entry.alignPow2 reqAlign)⟩
          | none =>
            match hook (lw.removeLive id).1 id entry with
            | .error msg => ⟨(lw.removeLive id).1, some (id, entry), .error (.hookFailure msg)⟩
            | .ok () =>
              if ((lw.removeLive id).1.findDead? id).isSome then
                ⟨(lw.removeLive id).1.insertDead id ⟨entry.sizeBytes, entry.alignPow2⟩,
                  some (id, entry), .error (.duplicateDeadAllocation id)⟩
              else
                ⟨(lw.removeLive id).1.insertDead id ⟨entry.sizeBytes, entry.alignPow2⟩,
                  some (id, entry), .ok ()⟩

/-- Core Miri deallocation (`deallocateWith` under a state-independent hook verdict `tb`). -/
def deallocate (lw : LinearAllocWorld) (ptr : DeallocPtr)
    (expectedLayout : Option (UInt64 × UInt8)) (expectedKind : AllocMemKind)
    (tb : DeallocHookSpec := .ok) : DeallocResult LinearAllocWorld :=
  lw.deallocateWith ptr expectedLayout expectedKind (fun _ _ _ => tb.run)

/-- Machine-level detach cleanup (`Miri.Interpreter.AllocationMachine.deallocate`): whenever the live
entry was detached — on success AND on every post-removal failure — the allocation's race clock
leaves the machine together with the detached allocation. -/
def detachRaceClock (res : DeallocResult LinearAllocWorld) : DeallocResult LinearAllocWorld :=
  match res.detached with
  | some (id, _) => { res with world := res.world.removeRace id }
  | none => res

/-- Mode-aware machine deallocation (`Miri.Interpreter.AllocationMachine.deallocate`): runs
`deallocateWith` under `machineDeallocHook`, which reads the allocation's vector clock from the
live-detached world (i.e. BEFORE any race-clock cleanup), then applies `detachRaceClock`. -/
def deallocateMachine (lw : LinearAllocWorld) (ptr : DeallocPtr)
    (expectedLayout : Option (UInt64 × UInt8)) (expectedKind : AllocMemKind)
    (mode : RaceDetectorMode) (actor : DeallocActor)
    (tb : DeallocHookSpec := .ok) : DeallocResult LinearAllocWorld :=
  detachRaceClock (lw.deallocateWith ptr expectedLayout expectedKind
    (fun wDetached id entry =>
      machineDeallocHook mode actor tb (wDetached.findRace? id) entry.sizeBytes))

/-- Materialize a canonical sorted `LinearAllocWorld` from any `KeyedAllocWorld`. -/
def ofKeyed (kw : KeyedAllocWorld) : LinearAllocWorld where
  nextAllocId := kw.nextAllocId
  idSupplyExhausted := kw.idSupplyExhausted
  issued := kw.issued.toList.map Prod.fst
  globals := kw.globals.toList
  live := kw.table.live.toList
  dead := kw.table.dead.toList
  race := kw.table.race.toList

end LinearAllocWorld

/-- Bidirectional refinement relation between linear-list and keyed `ExtTreeMap0` allocation worlds. -/
structure AllocWorldRel (lw : LinearAllocWorld) (kw : KeyedAllocWorld) : Prop where
  nextAllocId_eq : lw.nextAllocId = kw.nextAllocId
  idSupplyExhausted_eq : lw.idSupplyExhausted = kw.idSupplyExhausted
  issued_rel : ∀ id, lw.hasIssued id = kw.hasIssued id
  globals_rel : ∀ id, lw.findGlobal? id = kw.findGlobal? id
  live_rel : ∀ id, lw.findLive? id = kw.findLive? id
  dead_rel : ∀ id, lw.findDead? id = kw.findDead? id
  race_rel : ∀ id, lw.findRace? id = kw.findRace? id

theorem allocWorldRel_empty : AllocWorldRel LinearAllocWorld.empty KeyedAllocWorld.empty :=
  ⟨rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem allocWorldRel_ofLinear (lw : LinearAllocWorld) :
    AllocWorldRel lw (KeyedAllocWorld.ofLinear lw) where
  nextAllocId_eq := rfl
  idSupplyExhausted_eq := rfl
  issued_rel id := by
    simp only [KeyedAllocWorld.ofLinear, KeyedAllocWorld.hasIssued,
      ExtTreeMap0.contains_eq_isSome_get?, isSome_get?_ofLinearIssued, LinearAllocWorld.hasIssued]
  globals_rel id := (get?_ofLinearRows lw.globals id).symm
  live_rel id := (get?_ofLinearRows lw.live id).symm
  dead_rel id := (get?_ofLinearRows lw.dead id).symm
  race_rel id := (get?_ofLinearRows lw.race id).symm

private theorem cmp_miriAllocId_eq_iff (a b : MiriAllocId) :
    (compare a b == .eq) = (b == a) := by
  cases h : compare a b with
  | eq =>
    have heq : a = b := Std.LawfulEqCmp.eq_of_compare h
    subst heq; simp
  | lt =>
    have hne : b ≠ a := fun heq => by subst heq; rw [Std.ReflCmp.compare_self (cmp := compare)] at h; cases h
    simp [beq_false_of_ne hne]
  | gt =>
    have hne : b ≠ a := fun heq => by subst heq; rw [Std.ReflCmp.compare_self (cmp := compare)] at h; cases h
    simp [beq_false_of_ne hne]

private theorem linearFind?_extTreeMap0_toList {α : Type}
    (m : ExtTreeMap0 MiriAllocId α compare) (id : MiriAllocId) :
    linearFind? m.toList id = m.get? id := by
  unfold linearFind?
  have hfun : (fun p : MiriAllocId × α => p.1 == id) = (fun p : MiriAllocId × α => compare id p.1 == .eq) := by
    funext p; exact (cmp_miriAllocId_eq_iff id p.1).symm
  rw [hfun]
  exact ExtTreeMap0.linearFind?_toList m id

private theorem any_map_fst_toList (m : ExtTreeMap0 MiriAllocId Unit compare) (id : MiriAllocId) :
    (m.toList.map Prod.fst).any (fun x => x == id) = m.contains id := by
  rw [ExtTreeMap0.contains_eq_isSome_get?, ← linearFind?_extTreeMap0_toList]
  unfold linearFind?
  induction m.toList with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.map_cons, List.any_cons, List.find?]
    cases h : p.1 == id <;> simp [ih]

theorem allocWorldRel_ofKeyed (kw : KeyedAllocWorld) :
    AllocWorldRel (LinearAllocWorld.ofKeyed kw) kw where
  nextAllocId_eq := rfl
  idSupplyExhausted_eq := rfl
  issued_rel id := by
    simp only [LinearAllocWorld.ofKeyed, LinearAllocWorld.hasIssued, KeyedAllocWorld.hasIssued]
    exact any_map_fst_toList kw.issued id
  globals_rel id := linearFind?_extTreeMap0_toList kw.globals id
  live_rel id := linearFind?_extTreeMap0_toList kw.table.live id
  dead_rel id := linearFind?_extTreeMap0_toList kw.table.dead id
  race_rel id := linearFind?_extTreeMap0_toList kw.table.race id

theorem allocWorldRel_iff_eq_ofLinear (lw : LinearAllocWorld) (kw : KeyedAllocWorld) :
    AllocWorldRel lw kw ↔ kw = KeyedAllocWorld.ofLinear lw := by
  constructor
  · intro h
    have h0 := allocWorldRel_ofLinear lw
    apply KeyedAllocWorld.ext
    · rw [← h.nextAllocId_eq, h0.nextAllocId_eq]
    · rw [← h.idSupplyExhausted_eq, h0.idSupplyExhausted_eq]
    · intro id; rw [← h.issued_rel id, h0.issued_rel id]
    · intro id; rw [← h.globals_rel id, h0.globals_rel id]
    · intro id; rw [← h.live_rel id, h0.live_rel id]
    · intro id; rw [← h.dead_rel id, h0.dead_rel id]
    · intro id; rw [← h.race_rel id, h0.race_rel id]
  · intro h; subst h; exact allocWorldRel_ofLinear lw

theorem allocWorldRel_keyed_unique {lw : LinearAllocWorld} {kw₁ kw₂ : KeyedAllocWorld}
    (h1 : AllocWorldRel lw kw₁) (h2 : AllocWorldRel lw kw₂) : kw₁ = kw₂ := by
  rw [(allocWorldRel_iff_eq_ofLinear lw kw₁).1 h1, (allocWorldRel_iff_eq_ofLinear lw kw₂).1 h2]

/-! #### Query & Mutation Simulation under `AllocWorldRel` -/

theorem allocWorldRel_containsId {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (h : AllocWorldRel lw kw) (id : MiriAllocId) :
    lw.containsId id = kw.containsId id := by
  simp [LinearAllocWorld.containsId, KeyedAllocWorld.containsId,
    h.live_rel id, h.dead_rel id, h.globals_rel id]

theorem allocWorldRel_isAllocLive {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (h : AllocWorldRel lw kw) (id : MiriAllocId) :
    lw.isAllocLive id = kw.isAllocLive id := by
  simp [LinearAllocWorld.isAllocLive, KeyedAllocWorld.isAllocLive, h.live_rel id, h.globals_rel id]

theorem allocWorldRel_getAllocInfo {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (h : AllocWorldRel lw kw) (id : MiriAllocId) :
    lw.getAllocInfo id = kw.getAllocInfo id := by
  simp [LinearAllocWorld.getAllocInfo, KeyedAllocWorld.getAllocInfo,
    h.live_rel id, h.globals_rel id, h.dead_rel id]

theorem allocWorldRel_getLiveAllocSizeAndAlign {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (h : AllocWorldRel lw kw) (id : MiriAllocId) :
    lw.getLiveAllocSizeAndAlign id = kw.getLiveAllocSizeAndAlign id := by
  simp [LinearAllocWorld.getLiveAllocSizeAndAlign, KeyedAllocWorld.getLiveAllocSizeAndAlign,
    allocWorldRel_getAllocInfo h id]

theorem allocWorldRel_findAllocBytes? {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (h : AllocWorldRel lw kw) (id : MiriAllocId) :
    lw.findAllocBytes? id = kw.findAllocBytes? id := by
  simp [LinearAllocWorld.findAllocBytes?, KeyedAllocWorld.findAllocBytes?,
    h.live_rel id, h.globals_rel id]

theorem allocWorldRel_insertLive {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (h : AllocWorldRel lw kw) (id : MiriAllocId) (entry : LiveAllocEntry) :
    AllocWorldRel (lw.insertLive id entry) (kw.insertLive id entry) where
  nextAllocId_eq := h.nextAllocId_eq
  idSupplyExhausted_eq := h.idSupplyExhausted_eq
  issued_rel := h.issued_rel
  globals_rel := h.globals_rel
  live_rel k := by
    simp only [LinearAllocWorld.insertLive, LinearAllocWorld.findLive?,
      KeyedAllocWorld.insertLive, KeyedAllocWorld.findLive?]
    rw [linearFind?_filter_append_single, ExtTreeMap0.get?_insert, cmp_miriAllocId_eq_iff]
    by_cases hk : k = id
    · subst hk; simp
    · have h1 : (k == id) = false := beq_false_of_ne hk
      have h2 : (id == k) = false := beq_false_of_ne (fun he => hk he.symm)
      simp only [h1, h2]
      exact h.live_rel k
  dead_rel := h.dead_rel
  race_rel := h.race_rel

theorem allocWorldRel_removeLive {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (h : AllocWorldRel lw kw) (id : MiriAllocId) :
    AllocWorldRel (lw.removeLive id).1 (kw.removeLive id).1 ∧
    (lw.removeLive id).2 = (kw.removeLive id).2 := by
  unfold LinearAllocWorld.removeLive KeyedAllocWorld.removeLive
  rw [h.live_rel id]
  cases kw.findLive? id with
  | none => exact ⟨h, rfl⟩
  | some e =>
    refine ⟨?_, rfl⟩
    exact
      { nextAllocId_eq := h.nextAllocId_eq
        idSupplyExhausted_eq := h.idSupplyExhausted_eq
        issued_rel := h.issued_rel
        globals_rel := h.globals_rel
        live_rel := fun k => by
          simp only [LinearAllocWorld.findLive?, KeyedAllocWorld.findLive?]
          rw [linearFind?_filter_ne, ExtTreeMap0.get?_erase, cmp_miriAllocId_eq_iff]
          by_cases hk : k = id
          · subst hk; simp
          · have h1 : (k == id) = false := beq_false_of_ne hk
            have h2 : (id == k) = false := beq_false_of_ne (fun he => hk he.symm)
            simp only [h1, h2]
            exact h.live_rel k
        dead_rel := h.dead_rel
        race_rel := h.race_rel }

theorem allocWorldRel_insertDead {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (h : AllocWorldRel lw kw) (id : MiriAllocId) (entry : DeadAllocEntry) :
    AllocWorldRel (lw.insertDead id entry) (kw.insertDead id entry) where
  nextAllocId_eq := h.nextAllocId_eq
  idSupplyExhausted_eq := h.idSupplyExhausted_eq
  issued_rel := h.issued_rel
  globals_rel := h.globals_rel
  live_rel := h.live_rel
  dead_rel k := by
    simp only [LinearAllocWorld.insertDead, LinearAllocWorld.findDead?,
      KeyedAllocWorld.insertDead, KeyedAllocWorld.findDead?]
    rw [linearFind?_filter_append_single, ExtTreeMap0.get?_insert, cmp_miriAllocId_eq_iff]
    by_cases hk : k = id
    · subst hk; simp
    · have h1 : (k == id) = false := beq_false_of_ne hk
      have h2 : (id == k) = false := beq_false_of_ne (fun he => hk he.symm)
      simp only [h1, h2]
      exact h.dead_rel k
  race_rel := h.race_rel

theorem allocWorldRel_setRace {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (h : AllocWorldRel lw kw) (id : MiriAllocId) (clk : RaceClockEntry) :
    AllocWorldRel (lw.setRace id clk) (kw.setRace id clk) where
  nextAllocId_eq := h.nextAllocId_eq
  idSupplyExhausted_eq := h.idSupplyExhausted_eq
  issued_rel := h.issued_rel
  globals_rel := h.globals_rel
  live_rel := h.live_rel
  dead_rel := h.dead_rel
  race_rel k := by
    simp only [LinearAllocWorld.setRace, LinearAllocWorld.findRace?,
      KeyedAllocWorld.setRace, KeyedAllocWorld.findRace?]
    rw [linearFind?_filter_append_single, ExtTreeMap0.get?_insert, cmp_miriAllocId_eq_iff]
    by_cases hk : k = id
    · subst hk; simp
    · have h1 : (k == id) = false := beq_false_of_ne hk
      have h2 : (id == k) = false := beq_false_of_ne (fun he => hk he.symm)
      simp only [h1, h2]
      exact h.race_rel k

theorem allocWorldRel_removeRace {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (h : AllocWorldRel lw kw) (id : MiriAllocId) :
    AllocWorldRel (lw.removeRace id) (kw.removeRace id) where
  nextAllocId_eq := h.nextAllocId_eq
  idSupplyExhausted_eq := h.idSupplyExhausted_eq
  issued_rel := h.issued_rel
  globals_rel := h.globals_rel
  live_rel := h.live_rel
  dead_rel := h.dead_rel
  race_rel k := by
    simp only [LinearAllocWorld.removeRace, LinearAllocWorld.findRace?,
      KeyedAllocWorld.removeRace, KeyedAllocWorld.findRace?]
    rw [linearFind?_filter_ne, ExtTreeMap0.get?_erase, cmp_miriAllocId_eq_iff]
    by_cases hk : k = id
    · subst hk; simp
    · have h1 : (k == id) = false := beq_false_of_ne hk
      have h2 : (id == k) = false := beq_false_of_ne (fun he => hk he.symm)
      simp only [h1, h2]
      exact h.race_rel k

theorem allocWorldRel_registerGlobal {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (h : AllocWorldRel lw kw) (id : MiriAllocId) (entry : GlobalAllocEntry) :
    AllocWorldRel (lw.registerGlobal id entry) (kw.registerGlobal id entry) where
  nextAllocId_eq := h.nextAllocId_eq
  idSupplyExhausted_eq := h.idSupplyExhausted_eq
  issued_rel k := by
    simp only [LinearAllocWorld.registerGlobal, LinearAllocWorld.hasIssued, List.any_cons,
      KeyedAllocWorld.registerGlobal, KeyedAllocWorld.hasIssued, ExtTreeMap0.contains_eq_isSome_get?]
    rw [ExtTreeMap0.get?_insert, cmp_miriAllocId_eq_iff]
    by_cases hk : k = id
    · subst hk; simp
    · have h1 : (id == k) = false := beq_false_of_ne (fun he => hk he.symm)
      simp only [h1, Bool.false_or]
      exact h.issued_rel k
  globals_rel k := by
    simp only [LinearAllocWorld.registerGlobal, LinearAllocWorld.findGlobal?,
      KeyedAllocWorld.registerGlobal, KeyedAllocWorld.findGlobal?]
    rw [linearFind?_filter_append_single, ExtTreeMap0.get?_insert, cmp_miriAllocId_eq_iff]
    by_cases hk : k = id
    · subst hk; simp
    · have h1 : (k == id) = false := beq_false_of_ne hk
      have h2 : (id == k) = false := beq_false_of_ne (fun he => hk he.symm)
      simp only [h1, h2]
      exact h.globals_rel k
  live_rel := h.live_rel
  dead_rel := h.dead_rel
  race_rel := h.race_rel

theorem allocWorldRel_registerReservedGlobal {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (h : AllocWorldRel lw kw) (id : MiriAllocId) (entry : GlobalAllocEntry) :
    AllocWorldRel (lw.registerReservedGlobal id entry).1 (kw.registerReservedGlobal id entry).1 ∧
    (lw.registerReservedGlobal id entry).2 = (kw.registerReservedGlobal id entry).2 := by
  unfold LinearAllocWorld.registerReservedGlobal KeyedAllocWorld.registerReservedGlobal
  rw [h.globals_rel id, h.live_rel id, h.dead_rel id, h.issued_rel id]
  cases (kw.findGlobal? id).isSome with
  | true => exact ⟨h, rfl⟩
  | false =>
    cases ((kw.findLive? id).isSome || (kw.findDead? id).isSome || !kw.hasIssued id) with
    | true => exact ⟨h, rfl⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, trivial⟩
      exact
        { nextAllocId_eq := h.nextAllocId_eq
          idSupplyExhausted_eq := h.idSupplyExhausted_eq
          issued_rel := h.issued_rel
          globals_rel := fun k => by
            simp only [LinearAllocWorld.findGlobal?, KeyedAllocWorld.findGlobal?]
            rw [linearFind?_filter_append_single, ExtTreeMap0.get?_insert, cmp_miriAllocId_eq_iff]
            by_cases hk : k = id
            · subst hk; simp
            · have h1 : (k == id) = false := beq_false_of_ne hk
              have h2 : (id == k) = false := beq_false_of_ne (fun he => hk he.symm)
              simp only [h1, h2]
              exact h.globals_rel k
          live_rel := h.live_rel
          dead_rel := h.dead_rel
          race_rel := h.race_rel }

theorem allocWorldRel_updateLiveBytes {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (h : AllocWorldRel lw kw) (id : MiriAllocId) (bytes : List MemByte) :
    AllocWorldRel (lw.updateLiveBytes id bytes) (kw.updateLiveBytes id bytes) := by
  unfold LinearAllocWorld.updateLiveBytes KeyedAllocWorld.updateLiveBytes
  rw [h.live_rel id]
  cases kw.findLive? id with
  | none => exact h
  | some e => exact allocWorldRel_insertLive h id { e with bytes := bytes }

theorem allocWorldRel_reserveAllocId {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (h : AllocWorldRel lw kw) :
    AllocWorldRel lw.reserveAllocId.1 kw.reserveAllocId.1 ∧
    lw.reserveAllocId.2 = kw.reserveAllocId.2 := by
  unfold LinearAllocWorld.reserveAllocId KeyedAllocWorld.reserveAllocId
  rw [h.idSupplyExhausted_eq, h.nextAllocId_eq]
  cases hexh : kw.idSupplyExhausted with
  | true => simp [h]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases MiriAllocId.ofUInt64 kw.nextAllocId with
    | none =>
      refine ⟨⟨rfl, rfl, h.issued_rel, h.globals_rel, h.live_rel, h.dead_rel, h.race_rel⟩, rfl⟩
    | some id =>
      simp only [h.issued_rel id, allocWorldRel_containsId h id]
      cases hcon : kw.hasIssued id || kw.containsId id with
      | true =>
        simp only [↓reduceIte]
        exact ⟨⟨rfl, rfl, h.issued_rel, h.globals_rel, h.live_rel, h.dead_rel, h.race_rel⟩, trivial⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine ⟨?_, trivial⟩
        exact
          { nextAllocId_eq := rfl
            idSupplyExhausted_eq := rfl
            issued_rel := fun k => by
              simp only [LinearAllocWorld.hasIssued, List.any_cons,
                KeyedAllocWorld.hasIssued, ExtTreeMap0.contains_eq_isSome_get?]
              rw [ExtTreeMap0.get?_insert, cmp_miriAllocId_eq_iff]
              by_cases hk : k = id
              · subst hk; simp
              · have h1 : (id == k) = false := beq_false_of_ne (fun he => hk he.symm)
                simp only [h1, Bool.false_or]
                exact h.issued_rel k
            globals_rel := h.globals_rel
            live_rel := h.live_rel
            dead_rel := h.dead_rel
            race_rel := h.race_rel }

theorem allocWorldRel_allocate {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (h : AllocWorldRel lw kw) (entry : LiveAllocEntry) :
    AllocWorldRel (lw.allocate entry).1 (kw.allocate entry).1 ∧
    (lw.allocate entry).2 = (kw.allocate entry).2 := by
  unfold LinearAllocWorld.allocate KeyedAllocWorld.allocate
  rcases allocWorldRel_reserveAllocId h with ⟨hrel, hres⟩
  cases hlr : lw.reserveAllocId with
  | mk lw1 lres =>
    cases hkr : kw.reserveAllocId with
    | mk kw1 kres =>
      rw [hlr, hkr] at hrel hres
      simp only at hrel hres
      rw [hres]
      cases kres with
      | error e => exact ⟨hrel, rfl⟩
      | ok id => exact ⟨allocWorldRel_insertLive hrel id entry, rfl⟩

theorem allocWorldRel_allocateMachine {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (h : AllocWorldRel lw kw) (entry : LiveAllocEntry)
    (mode : RaceDetectorMode) (creatorThread : UInt32) (timestamp : UInt64) :
    AllocWorldRel (lw.allocateMachine entry mode creatorThread timestamp).1
      (kw.allocateMachine entry mode creatorThread timestamp).1 ∧
    (lw.allocateMachine entry mode creatorThread timestamp).2 =
      (kw.allocateMachine entry mode creatorThread timestamp).2 := by
  unfold LinearAllocWorld.allocateMachine KeyedAllocWorld.allocateMachine
  rcases allocWorldRel_allocate h entry with ⟨hrel, hres⟩
  cases hla : lw.allocate entry with
  | mk lw1 lres =>
    cases hka : kw.allocate entry with
    | mk kw1 kres =>
      rw [hla, hka] at hrel hres
      simp only at hrel hres
      rw [hres]
      cases kres with
      | error e => exact ⟨hrel, rfl⟩
      | ok id =>
        cases mode with
        | unconfigured => exact ⟨hrel, rfl⟩
        | configured _ => exact ⟨allocWorldRel_setRace hrel id _, rfl⟩

/-- Refinement of the hook-parameterized core deallocation: linear and keyed worlds stay related
whenever the two machine hooks agree on related (live-detached) worlds. -/
theorem allocWorldRel_deallocateWith {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (h : AllocWorldRel lw kw) (ptr : DeallocPtr)
    (expectedLayout : Option (UInt64 × UInt8)) (expectedKind : AllocMemKind)
    (lhook : LinearAllocWorld → MiriAllocId → LiveAllocEntry → Except String Unit)
    (khook : KeyedAllocWorld → MiriAllocId → LiveAllocEntry → Except String Unit)
    (hhook : ∀ lw' kw', AllocWorldRel lw' kw' → ∀ id entry, lhook lw' id entry = khook kw' id entry) :
    AllocWorldRel (lw.deallocateWith ptr expectedLayout expectedKind lhook).world
      (kw.deallocateWith ptr expectedLayout expectedKind khook).world ∧
    (lw.deallocateWith ptr expectedLayout expectedKind lhook).detached =
      (kw.deallocateWith ptr expectedLayout expectedKind khook).detached ∧
    (lw.deallocateWith ptr expectedLayout expectedKind lhook).outcome =
      (kw.deallocateWith ptr expectedLayout expectedKind khook).outcome := by
  unfold LinearAllocWorld.deallocateWith KeyedAllocWorld.deallocateWith
  cases ptr with
  | dangling addr => exact ⟨h, rfl, rfl⟩
  | provenanced id off =>
    cases h_off : (off != 0) with
    | true => simp [h_off, h]
    | false =>
      simp only [h_off, Bool.false_eq_true, ↓reduceIte]
      rcases allocWorldRel_removeLive h id with ⟨hrem, hentry⟩
      rw [hentry]
      cases (kw.removeLive id).2 with
      | none =>
        rw [h.globals_rel id]
        cases kw.findGlobal? id <;> exact ⟨h, rfl, rfl⟩
      | some entry =>
        cases hmut : (entry.mutability == .not) with
        | true => simp [hmut, hrem]
        | false =>
          cases hkind : (entry.kind != expectedKind) with
          | true => simp [hmut, hkind, hrem]
          | false =>
            simp only [hmut, hkind, Bool.false_eq_true, ↓reduceIte]
            cases deallocLayoutMismatch? entry expectedLayout with
            | some lay => exact ⟨hrem, rfl, rfl⟩
            | none =>
              simp only [hhook _ _ hrem id entry]
              cases khook (kw.removeLive id).1 id entry with
              | error msg => exact ⟨hrem, rfl, rfl⟩
              | ok u =>
                simp only [hrem.dead_rel id]
                split <;> exact ⟨allocWorldRel_insertDead hrem id _, rfl, rfl⟩

theorem allocWorldRel_deallocate {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (h : AllocWorldRel lw kw) (ptr : DeallocPtr)
    (expectedLayout : Option (UInt64 × UInt8)) (expectedKind : AllocMemKind)
    (tb : DeallocHookSpec := .ok) :
    AllocWorldRel (lw.deallocate ptr expectedLayout expectedKind tb).world
      (kw.deallocate ptr expectedLayout expectedKind tb).world ∧
    (lw.deallocate ptr expectedLayout expectedKind tb).detached =
      (kw.deallocate ptr expectedLayout expectedKind tb).detached ∧
    (lw.deallocate ptr expectedLayout expectedKind tb).outcome =
      (kw.deallocate ptr expectedLayout expectedKind tb).outcome :=
  allocWorldRel_deallocateWith h ptr expectedLayout expectedKind _ _ (fun _ _ _ _ _ => rfl)

/-- The machine-level detach cleanup preserves the refinement. -/
theorem allocWorldRel_detachRaceClock
    {lr : DeallocResult LinearAllocWorld} {kr : DeallocResult KeyedAllocWorld}
    (hw : AllocWorldRel lr.world kr.world) (hd : lr.detached = kr.detached)
    (ho : lr.outcome = kr.outcome) :
    AllocWorldRel (LinearAllocWorld.detachRaceClock lr).world
      (KeyedAllocWorld.detachRaceClock kr).world ∧
    (LinearAllocWorld.detachRaceClock lr).detached = (KeyedAllocWorld.detachRaceClock kr).detached ∧
    (LinearAllocWorld.detachRaceClock lr).outcome = (KeyedAllocWorld.detachRaceClock kr).outcome := by
  unfold LinearAllocWorld.detachRaceClock KeyedAllocWorld.detachRaceClock
  rw [hd]
  cases hdet : kr.detached with
  | none => exact ⟨hw, hd, ho⟩
  | some p => exact ⟨allocWorldRel_removeRace hw p.1, rfl, ho⟩

theorem allocWorldRel_deallocateMachine {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (h : AllocWorldRel lw kw) (ptr : DeallocPtr)
    (expectedLayout : Option (UInt64 × UInt8)) (expectedKind : AllocMemKind)
    (mode : RaceDetectorMode) (actor : DeallocActor)
    (tb : DeallocHookSpec := .ok) :
    AllocWorldRel (lw.deallocateMachine ptr expectedLayout expectedKind mode actor tb).world
      (kw.deallocateMachine ptr expectedLayout expectedKind mode actor tb).world ∧
    (lw.deallocateMachine ptr expectedLayout expectedKind mode actor tb).detached =
      (kw.deallocateMachine ptr expectedLayout expectedKind mode actor tb).detached ∧
    (lw.deallocateMachine ptr expectedLayout expectedKind mode actor tb).outcome =
      (kw.deallocateMachine ptr expectedLayout expectedKind mode actor tb).outcome := by
  have hcore := allocWorldRel_deallocateWith h ptr expectedLayout expectedKind
    (fun lwD id entry => machineDeallocHook mode actor tb (lwD.findRace? id) entry.sizeBytes)
    (fun kwD id entry => machineDeallocHook mode actor tb (kwD.findRace? id) entry.sizeBytes)
    (fun lw' kw' hrel id entry => by rw [hrel.race_rel id])
  exact allocWorldRel_detachRaceClock hcore.1 hcore.2.1 hcore.2.2

/-! #### Exact Miri Allocation Supply, Deallocation Failure Ordering, and Race-Detector Theorems -/

/-- Inversion of a successful reservation: the supply was not exhausted, the cursor decoded to the
returned ID, that ID was fresh, and the post-state only advances the cursor and records the ID
(the exhaustion flag is NOT latched, even when the cursor wraps to `0`). -/
theorem keyedReserveAllocId_ok_inv {w w' : KeyedAllocWorld} {id : MiriAllocId}
    (h : w.reserveAllocId = (w', .ok id)) :
    w.idSupplyExhausted = false ∧
    MiriAllocId.ofUInt64 w.nextAllocId = some id ∧
    w.hasIssued id = false ∧ w.containsId id = false ∧
    w' = { w with nextAllocId := w.nextAllocId + 1, issued := w.issued.insert id () } := by
  unfold KeyedAllocWorld.reserveAllocId at h
  split at h
  · simp at h
  · rename_i hexh
    split at h
    · simp at h
    · rename_i id' hof
      split at h
      · simp at h
      · rename_i hcon
        injection h with hw hres
        injection hres with hid
        subst hid
        have hcon' : (w.hasIssued id' || w.containsId id') = false := by simpa using hcon
        rw [Bool.or_eq_false_iff] at hcon'
        exact ⟨by simpa using hexh, hof, hcon'.1, hcon'.2, hw.symm⟩

theorem keyedReserveAllocId_of_highWater (w : KeyedAllocWorld) (id : MiriAllocId)
    (hnotExh : w.idSupplyExhausted = false)
    (hnext : MiriAllocId.ofUInt64 w.nextAllocId = some id)
    (hfresh : w.hasIssued id = false) (hnotIn : w.containsId id = false) :
    let (w', res) := w.reserveAllocId
    res = .ok id ∧ w'.nextAllocId = w.nextAllocId + 1 ∧
    w'.idSupplyExhausted = false ∧ w'.hasIssued id = true := by
  simp only [KeyedAllocWorld.reserveAllocId, hnotExh, hnext, hfresh, hnotIn, Bool.or_self,
    Bool.false_eq_true, ↓reduceIte]
  simp [KeyedAllocWorld.hasIssued, ExtTreeMap0.contains_eq_isSome_get?,
    ExtTreeMap0.get?_insert_self]

/-- `AllocMap::reserve` is a `fetch_add`: a collision with an already-issued / already-present ID
still consumes the cursor value, so a retry probes the NEXT ID instead of colliding forever. -/
theorem keyedReserveAllocId_alreadyIssued_advances_cursor (w : KeyedAllocWorld) (id : MiriAllocId)
    (hnotExh : w.idSupplyExhausted = false)
    (hnext : MiriAllocId.ofUInt64 w.nextAllocId = some id)
    (hcollide : (w.hasIssued id || w.containsId id) = true) :
    w.reserveAllocId =
      ({ w with nextAllocId := w.nextAllocId + 1 }, .error (.alreadyIssued id)) := by
  simp [KeyedAllocWorld.reserveAllocId, hnotExh, hnext, hcollide]

/-- Wrap-around exhaustion exactly as upstream: reserving `2^64 - 1` succeeds and wraps the cursor to
`0` WITHOUT latching `idSupplyExhausted`; the next reservation observes the `0` sentinel, fails with
`.exhausted`, advances the cursor to `1`, and latches the flag; every later reservation fails without
changing the state (sticky). -/
theorem keyedReserveAllocId_wrapAround_latches_exhausted (w : KeyedAllocWorld)
    (hnotExh : w.idSupplyExhausted = false)
    (hmax : w.nextAllocId = MiriAllocId.maxValue.value)
    (hfresh : w.hasIssued MiriAllocId.maxValue = false)
    (hnotIn : w.containsId MiriAllocId.maxValue = false) :
    let (w1, res1) := w.reserveAllocId
    let (w2, res2) := w1.reserveAllocId
    let (w3, res3) := w2.reserveAllocId
    res1 = .ok MiriAllocId.maxValue ∧
    w1.nextAllocId = 0 ∧ w1.idSupplyExhausted = false ∧
    res2 = .error .exhausted ∧
    w2.nextAllocId = 1 ∧ w2.idSupplyExhausted = true ∧
    res3 = .error .exhausted ∧ w3 = w2 := by
  have hof : MiriAllocId.ofUInt64 MiriAllocId.maxValue.value = some MiriAllocId.maxValue :=
    (MiriAllocId.ofUInt64_eq_some_iff).2 rfl
  have hwrap : MiriAllocId.maxValue.value + 1 = 0 := by decide
  simp [KeyedAllocWorld.reserveAllocId, hnotExh, hmax, hof, hfresh, hnotIn, hwrap,
    MiriAllocId.ofUInt64_zero]

/-- Reserve-then-register (the only order upstream performs, e.g. vtable / function interning): right
after a successful reservation the validated `registerReservedGlobal` succeeds and coincides with the
unvalidated `registerGlobal` (re-recording the already-issued ID is the identity by extensionality). -/
theorem keyedRegisterReservedGlobal_after_reserve {w w1 : KeyedAllocWorld} {id : MiriAllocId}
    (entry : GlobalAllocEntry) (hres : w.reserveAllocId = (w1, .ok id)) :
    w1.registerReservedGlobal id entry = (w1.registerGlobal id entry, .ok ()) := by
  rcases keyedReserveAllocId_ok_inv hres with ⟨_, _, _, hnotIn, hw1⟩
  have hparts : w.findLive? id = none ∧ w.findDead? id = none ∧ w.findGlobal? id = none := by
    simp only [KeyedAllocWorld.containsId, Bool.or_eq_false_iff, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none] at hnotIn
    exact ⟨hnotIn.1.1, hnotIn.1.2, hnotIn.2⟩
  have hissued : w1.hasIssued id = true := by
    rw [hw1]
    simp [KeyedAllocWorld.hasIssued, ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.get?_insert_self]
  have hg : w1.findGlobal? id = none := by rw [hw1]; exact hparts.2.2
  have hl : w1.findLive? id = none := by rw [hw1]; exact hparts.1
  have hd : w1.findDead? id = none := by rw [hw1]; exact hparts.2.1
  unfold KeyedAllocWorld.registerReservedGlobal
  simp only [hg, hl, hd, hissued, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Bool.or_self,
    Bool.not_true]
  refine congrArg (fun x => (x, (Except.ok () : Except GlobalRegErr Unit))) ?_
  refine KeyedAllocWorld.ext rfl rfl (fun k => ?_) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl)
  simp only [KeyedAllocWorld.registerGlobal, KeyedAllocWorld.hasIssued,
    ExtTreeMap0.contains_eq_isSome_get?]
  rw [ExtTreeMap0.get?_insert]
  split
  · rename_i hk
    have hkEq : k = id := Std.LawfulEqCmp.eq_of_compare (eq_of_beq hk)
    subst hkEq
    simpa [KeyedAllocWorld.hasIssued, ExtTreeMap0.contains_eq_isSome_get?] using hissued
  · rfl

/-- Validation order and state retention of `registerReservedGlobal`: an ID already naming a global is
`.duplicateRuntimeId`; a live, tombstoned, or never-issued ID is `.globalIdAlreadyPresent`; every
rejection returns the exact input world. -/
theorem keyedRegisterReservedGlobal_rejections (w : KeyedAllocWorld) (id : MiriAllocId)
    (entry : GlobalAllocEntry) :
    ((w.findGlobal? id).isSome = true →
      w.registerReservedGlobal id entry = (w, .error (.duplicateRuntimeId id))) ∧
    ((w.findGlobal? id).isSome = false →
      ((w.findLive? id).isSome = true ∨ (w.findDead? id).isSome = true ∨ w.hasIssued id = false) →
      w.registerReservedGlobal id entry = (w, .error (.globalIdAlreadyPresent id))) := by
  refine ⟨fun hg => ?_, fun hg hbad => ?_⟩
  · simp [KeyedAllocWorld.registerReservedGlobal, hg]
  · have hcond : ((w.findLive? id).isSome || (w.findDead? id).isSome || !w.hasIssued id) = true := by
      rcases hbad with hb | hb | hb <;> simp [hb]
    simp only [KeyedAllocWorld.registerReservedGlobal, hg, Bool.false_eq_true, ↓reduceIte, hcond]

/-- `is_alloc_live` treats compiler globals as live (they can never be deallocated). -/
theorem keyedIsAllocLive_of_global (w : KeyedAllocWorld) (id : MiriAllocId) (g : GlobalAllocEntry)
    (hglobal : w.findGlobal? id = some g) : w.isAllocLive id = true := by
  simp [KeyedAllocWorld.isAllocLive, hglobal]

/-- `get_alloc_info` precedence on a tombstoned allocation: the dead metadata is reported with kind
`.dead` (never `none`), and `get_live_alloc_size_and_align` classifies it as `.useAfterFree`, while an
ID with no metadata at all is `.unavailable`. -/
theorem keyedGetAllocInfo_dead_and_unavailable (w : KeyedAllocWorld) (id : MiriAllocId)
    (hnotLive : w.findLive? id = none) (hnotGlobal : w.findGlobal? id = none) :
    (∀ d, w.findDead? id = some d →
      w.getAllocInfo id = some ⟨d.sizeBytes, d.alignPow2, .dead, .not⟩ ∧
      w.getLiveAllocSizeAndAlign id = .error (.useAfterFree id) ∧
      w.isAllocLive id = false) ∧
    (w.findDead? id = none →
      w.getAllocInfo id = none ∧
      w.getLiveAllocSizeAndAlign id = .error (.unavailable id)) := by
  refine ⟨fun d hd => ?_, fun hd => ?_⟩
  · simp [KeyedAllocWorld.getAllocInfo, KeyedAllocWorld.getLiveAllocSizeAndAlign,
      KeyedAllocWorld.isAllocLive, hnotLive, hnotGlobal, hd]
  · simp [KeyedAllocWorld.getAllocInfo, KeyedAllocWorld.getLiveAllocSizeAndAlign,
      hnotLive, hnotGlobal, hd]

/-- `get_alloc_info` on compiler globals: functions, vtables, and type-ids expose `0` dereferenceable
bytes, whereas `.static` / `.memory` globals are `.liveData` with their recorded size, alignment, and
mutability (also reported by `get_live_alloc_size_and_align`). -/
theorem keyedGetAllocInfo_global_kinds (w : KeyedAllocWorld) (id : MiriAllocId) (g : GlobalAllocEntry)
    (hnotLive : w.findLive? id = none) (hglobal : w.findGlobal? id = some g) :
    w.getAllocInfo id = some g.toAllocInfo ∧
    (g.kind = .function ∨ g.kind = .vtable ∨ g.kind = .typeId → g.toAllocInfo.sizeBytes = 0 ∧
      g.toAllocInfo.kind ≠ .liveData) ∧
    (g.kind = .static ∨ g.kind = .memory →
      g.toAllocInfo = ⟨g.sizeBytes, g.alignPow2, .liveData, g.mutability⟩ ∧
      w.getLiveAllocSizeAndAlign id = .ok (g.sizeBytes, g.alignPow2)) := by
  have hinfo : w.getAllocInfo id = some g.toAllocInfo := by
    simp [KeyedAllocWorld.getAllocInfo, hnotLive, hglobal]
  refine ⟨hinfo, fun hk => ?_, fun hk => ?_⟩
  · rcases hk with hk | hk | hk <;> simp [GlobalAllocEntry.toAllocInfo, hk]
  · rcases hk with hk | hk <;>
      simp [KeyedAllocWorld.getLiveAllocSizeAndAlign, hinfo, GlobalAllocEntry.toAllocInfo, hk]

/-- Precedence of `findAllocBytes?`: live local bytes shadow globals; uncached `.static` / `.memory`
globals expose their stored `g.bytes`; `.function` / `.vtable` / `.typeId` globals expose `none`. -/
theorem keyedFindAllocBytes?_precedence (w : KeyedAllocWorld) (id : MiriAllocId) :
    (∀ e, w.findLive? id = some e → w.findAllocBytes? id = some e.bytes) ∧
    (w.findLive? id = none → ∀ g, w.findGlobal? id = some g →
      ((g.kind = .static ∨ g.kind = .memory) → w.findAllocBytes? id = some g.bytes) ∧
      ((g.kind = .function ∨ g.kind = .vtable ∨ g.kind = .typeId) → w.findAllocBytes? id = none)) := by
  refine ⟨fun e he => by simp [KeyedAllocWorld.findAllocBytes?, he], fun hnl g hg => ⟨fun hk => ?_, fun hk => ?_⟩⟩
  · rcases hk with hk | hk <;> simp [KeyedAllocWorld.findAllocBytes?, hnl, hg, hk]
  · rcases hk with hk | hk | hk <;> simp [KeyedAllocWorld.findAllocBytes?, hnl, hg, hk]

theorem keyedDeallocate_nonzeroOffset_preserves_live (w : KeyedAllocWorld)
    (id : MiriAllocId) (off : UInt64) (hoff : off ≠ 0)
    (expectedLayout : Option (UInt64 × UInt8)) (expectedKind : AllocMemKind)
    (tb : DeallocHookSpec := .ok) :
    w.deallocate (.provenanced id off) expectedLayout expectedKind tb =
      ⟨w, none, .error (.nonzeroOffset id off)⟩ := by
  have hbne : (off != 0) = true := bne_iff_ne.2 hoff
  simp [KeyedAllocWorld.deallocate, KeyedAllocWorld.deallocateWith, hbne]

theorem keyedDeallocate_absent_reports_useAfterFree (w : KeyedAllocWorld)
    (id : MiriAllocId)
    (hnotLive : w.findLive? id = none)
    (hnotGlobal : w.findGlobal? id = none)
    (expectedLayout : Option (UInt64 × UInt8)) (expectedKind : AllocMemKind)
    (tb : DeallocHookSpec := .ok) :
    w.deallocate (.provenanced id 0) expectedLayout expectedKind tb =
      ⟨w, none, .error (.useAfterFree id)⟩ := by
  simp [KeyedAllocWorld.deallocate, KeyedAllocWorld.deallocateWith, KeyedAllocWorld.removeLive,
    hnotLive, hnotGlobal]

theorem keyedDeallocate_doubleFree_precedes_layout_and_kind (w : KeyedAllocWorld)
    (id : MiriAllocId) (deadEntry : DeadAllocEntry)
    (hnotLive : w.findLive? id = none)
    (hnotGlobal : w.findGlobal? id = none)
    (_hdead : w.findDead? id = some deadEntry)
    (expectedLayout : Option (UInt64 × UInt8)) (expectedKind : AllocMemKind)
    (tb : DeallocHookSpec := .ok) :
    w.deallocate (.provenanced id 0) expectedLayout expectedKind tb =
      ⟨w, none, .error (.useAfterFree id)⟩ :=
  keyedDeallocate_absent_reports_useAfterFree w id hnotLive hnotGlobal expectedLayout expectedKind tb

theorem keyedDeallocate_global_reports_globalErr (w : KeyedAllocWorld)
    (id : MiriAllocId) (g : GlobalAllocEntry)
    (hnotLive : w.findLive? id = none)
    (hglobal : w.findGlobal? id = some g)
    (expectedLayout : Option (UInt64 × UInt8)) (expectedKind : AllocMemKind)
    (tb : DeallocHookSpec := .ok) :
    w.deallocate (.provenanced id 0) expectedLayout expectedKind tb =
      ⟨w, none, .error (.globalErr id g.kind)⟩ := by
  simp [KeyedAllocWorld.deallocate, KeyedAllocWorld.deallocateWith, KeyedAllocWorld.removeLive,
    hnotLive, hglobal]

theorem keyedDeallocate_postRemovalFailure_retains_detached_state (w : KeyedAllocWorld)
    (id : MiriAllocId) (entry : LiveAllocEntry)
    (expectedLayout : Option (UInt64 × UInt8)) (expectedKind : AllocMemKind)
    (tb : DeallocHookSpec)
    (hlive : w.findLive? id = some entry)
    (hmut : entry.mutability = .mut)
    (hkindNe : entry.kind ≠ expectedKind) :
    let res := w.deallocate (.provenanced id 0) expectedLayout expectedKind tb
    res.outcome = .error (.memoryKindMismatch id) ∧
    res.detached = some (id, entry) ∧
    res.world.findLive? id = none ∧
    res.world.findDead? id = w.findDead? id := by
  have hmutF : (entry.mutability == .not) = false := by rw [hmut]; rfl
  have hkindT : (entry.kind != expectedKind) = true := bne_iff_ne.2 hkindNe
  simp only [KeyedAllocWorld.findLive?] at hlive
  simp [KeyedAllocWorld.deallocate, KeyedAllocWorld.deallocateWith, KeyedAllocWorld.removeLive,
    KeyedAllocWorld.findLive?, KeyedAllocWorld.findDead?, hlive, hmutF, hkindT,
    ExtTreeMap0.get?_erase_self]

/-- A failing machine hook retains the live-detached world WITHOUT recording a tombstone. -/
theorem keyedDeallocate_hookFailure_retains_detached_state_without_tombstone (w : KeyedAllocWorld)
    (id : MiriAllocId) (entry : LiveAllocEntry) (tb : DeallocHookSpec) (msg : String)
    (hlive : w.findLive? id = some entry)
    (hmut : entry.mutability = .mut)
    (hhook : tb.run = .error msg) :
    let res := w.deallocate (.provenanced id 0) none entry.kind tb
    res.outcome = .error (.hookFailure msg) ∧
    res.detached = some (id, entry) ∧
    res.world.findLive? id = none ∧
    res.world.findDead? id = w.findDead? id := by
  have hmutF : (entry.mutability == .not) = false := by rw [hmut]; rfl
  simp only [KeyedAllocWorld.findLive?] at hlive
  simp [KeyedAllocWorld.deallocate, KeyedAllocWorld.deallocateWith, KeyedAllocWorld.removeLive,
    KeyedAllocWorld.findLive?, KeyedAllocWorld.findDead?, hlive, hmutF, hhook,
    deallocLayoutMismatch?, ExtTreeMap0.get?_erase_self]

theorem keyedDeallocate_duplicateDead_replaces_before_error (w : KeyedAllocWorld)
    (id : MiriAllocId) (entry : LiveAllocEntry) (oldDead : DeadAllocEntry)
    (hlive : w.findLive? id = some entry)
    (hdead : w.findDead? id = some oldDead)
    (hmut : entry.mutability = .mut) :
    let res := w.deallocate (.provenanced id 0) none entry.kind .ok
    res.outcome = .error (.duplicateDeadAllocation id) ∧
    res.detached = some (id, entry) ∧
    res.world.findLive? id = none ∧
    res.world.findDead? id = some ⟨entry.sizeBytes, entry.alignPow2⟩ := by
  have hmutF : (entry.mutability == .not) = false := by rw [hmut]; rfl
  simp only [KeyedAllocWorld.findLive?] at hlive
  simp only [KeyedAllocWorld.findDead?] at hdead
  simp [KeyedAllocWorld.deallocate, KeyedAllocWorld.deallocateWith, KeyedAllocWorld.removeLive,
    hlive, hmutF, DeallocHookSpec.run, KeyedAllocWorld.findDead?, hdead, deallocLayoutMismatch?,
    KeyedAllocWorld.insertDead, KeyedAllocWorld.findLive?,
    ExtTreeMap0.get?_erase_self, ExtTreeMap0.get?_insert_self]

/-- The core `deallocateWith` never touches race clocks; only the machine-level `detachRaceClock`
wrapper does. -/
theorem keyedDeallocateWith_preserves_raceClocks (w : KeyedAllocWorld) (ptr : DeallocPtr)
    (expectedLayout : Option (UInt64 × UInt8)) (expectedKind : AllocMemKind)
    (hook : KeyedAllocWorld → MiriAllocId → LiveAllocEntry → Except String Unit) (k : MiriAllocId) :
    (w.deallocateWith ptr expectedLayout expectedKind hook).world.findRace? k = w.findRace? k := by
  have hrem : ∀ id, (w.removeLive id).1.findRace? k = w.findRace? k := by
    intro id
    unfold KeyedAllocWorld.removeLive
    cases w.findLive? id <;> rfl
  unfold KeyedAllocWorld.deallocateWith
  cases ptr with
  | dangling addr => rfl
  | provenanced id off =>
    dsimp only
    repeat' split
    all_goals first | rfl | exact hrem id

/-- The detached owner reported by `deallocateWith` is always the allocation named by the pointer. -/
theorem keyedDeallocateWith_detached_id (w : KeyedAllocWorld) (ptr : DeallocPtr)
    (expectedLayout : Option (UInt64 × UInt8)) (expectedKind : AllocMemKind)
    (hook : KeyedAllocWorld → MiriAllocId → LiveAllocEntry → Except String Unit)
    (id : MiriAllocId) (entry : LiveAllocEntry)
    (hdet : (w.deallocateWith ptr expectedLayout expectedKind hook).detached = some (id, entry)) :
    ptr = .provenanced id 0 ∧ w.findLive? id = some entry := by
  unfold KeyedAllocWorld.deallocateWith at hdet
  cases ptr with
  | dangling addr => cases hdet
  | provenanced id' off =>
    dsimp only at hdet
    cases hoff : (off != 0) with
    | true => rw [hoff] at hdet; cases hdet
    | false =>
      have hoff0 : off = 0 := by
        cases hdec : decide (off = 0) with
        | true => exact of_decide_eq_true hdec
        | false =>
          have hne : off ≠ 0 := of_decide_eq_false hdec
          rw [bne_iff_ne.2 hne] at hoff; cases hoff
      have hremEq : (w.removeLive id').2 = w.findLive? id' := by
        unfold KeyedAllocWorld.removeLive
        cases w.findLive? id' <;> rfl
      rw [hoff] at hdet
      simp only [Bool.false_eq_true, ↓reduceIte] at hdet
      rw [hremEq] at hdet
      cases hl : w.findLive? id' with
      | none =>
        rw [hl] at hdet
        dsimp only at hdet
        split at hdet <;> cases hdet
      | some e =>
        rw [hl] at hdet
        dsimp only at hdet
        have hpair : some (id', e) = some (id, entry) := by
          repeat' split at hdet
          all_goals exact hdet
        injection hpair with hpair
        injection hpair with h1 h2
        subst h1; subst h2; subst hoff0
        exact ⟨rfl, hl⟩

/-- Universal detached-state retention of the core deallocation: whenever the pointer names a live
allocation at offset `0`, `deallocateWith` detaches it and removes it from `live` — on success and on
EVERY post-removal failure (immutability, kind, layout, machine hook, duplicate tombstone), for every
requested layout, kind, and hook. -/
theorem keyedDeallocateWith_live_always_detaches (w : KeyedAllocWorld) (id : MiriAllocId)
    (entry : LiveAllocEntry)
    (expectedLayout : Option (UInt64 × UInt8)) (expectedKind : AllocMemKind)
    (hook : KeyedAllocWorld → MiriAllocId → LiveAllocEntry → Except String Unit)
    (hlive : w.findLive? id = some entry) :
    (w.deallocateWith (.provenanced id 0) expectedLayout expectedKind hook).detached =
      some (id, entry) ∧
    (w.deallocateWith (.provenanced id 0) expectedLayout expectedKind hook).world.findLive? id =
      none := by
  have hrem2 : (w.removeLive id).2 = some entry := by
    unfold KeyedAllocWorld.removeLive; rw [hlive]
  have hrem1 : (w.removeLive id).1.findLive? id = none := by
    unfold KeyedAllocWorld.removeLive; rw [hlive]
    simp [KeyedAllocWorld.findLive?, ExtTreeMap0.get?_erase_self]
  unfold KeyedAllocWorld.deallocateWith
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hrem2]
  repeat' split
  all_goals first | exact ⟨rfl, hrem1⟩ | exact ⟨rfl, by simpa [KeyedAllocWorld.insertDead, KeyedAllocWorld.findLive?] using hrem1⟩

/-- Dropping an absent race clock is the identity (by keyed-world extensionality). -/
theorem keyedRemoveRace_eq_self_of_noClock (w : KeyedAllocWorld) (id : MiriAllocId)
    (hnoClk : w.findRace? id = none) : w.removeRace id = w := by
  refine KeyedAllocWorld.ext rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_
  intro k
  simp only [KeyedAllocWorld.removeRace, KeyedAllocWorld.findRace?]
  rw [ExtTreeMap0.get?_erase]
  split
  · rename_i hk
    have hkEq : k = id := Std.LawfulEqCmp.eq_of_compare (eq_of_beq hk)
    subst hkEq
    exact hnoClk.symm
  · rfl

/-- The detach cleanup only edits race clocks: outcome, detached owner, and every non-race lookup of
the result world are unchanged. -/
theorem keyedDetachRaceClock_preserves_outcome_detached_and_tables
    (res : DeallocResult KeyedAllocWorld) (k : MiriAllocId) :
    (KeyedAllocWorld.detachRaceClock res).outcome = res.outcome ∧
    (KeyedAllocWorld.detachRaceClock res).detached = res.detached ∧
    (KeyedAllocWorld.detachRaceClock res).world.findLive? k = res.world.findLive? k ∧
    (KeyedAllocWorld.detachRaceClock res).world.findDead? k = res.world.findDead? k ∧
    (KeyedAllocWorld.detachRaceClock res).world.findGlobal? k = res.world.findGlobal? k := by
  unfold KeyedAllocWorld.detachRaceClock
  cases hd : res.detached with
  | none => exact ⟨rfl, hd, rfl, rfl, rfl⟩
  | some p => exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Upstream detach cleanup (`AllocationMachine.deallocate`): whenever machine deallocation detached
the live entry — on success AND on every post-removal failure, in every `RaceDetectorMode` — the
allocation's race clock has left the machine. -/
theorem keyedDeallocateMachine_detached_drops_raceClock (w : KeyedAllocWorld) (ptr : DeallocPtr)
    (expectedLayout : Option (UInt64 × UInt8)) (expectedKind : AllocMemKind)
    (mode : RaceDetectorMode) (actor : DeallocActor) (tb : DeallocHookSpec)
    (id : MiriAllocId) (entry : LiveAllocEntry)
    (hdet : (w.deallocateMachine ptr expectedLayout expectedKind mode actor tb).detached =
      some (id, entry)) :
    (w.deallocateMachine ptr expectedLayout expectedKind mode actor tb).world.findRace? id = none ∧
    ptr = .provenanced id 0 ∧ w.findLive? id = some entry := by
  unfold KeyedAllocWorld.deallocateMachine KeyedAllocWorld.detachRaceClock at hdet ⊢
  generalize hres : w.deallocateWith ptr expectedLayout expectedKind
    (fun wDetached id entry =>
      machineDeallocHook mode actor tb (wDetached.findRace? id) entry.sizeBytes) = res at hdet ⊢
  cases hd : res.detached with
  | none =>
    rw [hd] at hdet
    dsimp only at hdet
    rw [hd] at hdet
    cases hdet
  | some p =>
    rw [hd] at hdet
    dsimp only at hdet
    injection hdet with hp
    subst hp
    refine ⟨?_, ?_⟩
    · simp [KeyedAllocWorld.removeRace, KeyedAllocWorld.findRace?, ExtTreeMap0.get?_erase_self]
    · have := keyedDeallocateWith_detached_id w ptr expectedLayout expectedKind _ id entry
        (by rw [hres]; exact hd)
      exact this

/-- Universal machine-level detached-state retention (`AllocationMachine.deallocate`): deallocating a
live allocation at offset `0` ALWAYS detaches the live entry together with its race clock — whatever the
`RaceDetectorMode`, requested layout / kind, actor clocks, and Tree Borrows verdict, and whatever the
outcome (success, `DataRace`, missing clock, hook failure, layout / kind / mutability mismatch). -/
theorem keyedDeallocateMachine_live_always_detaches_entry_and_clock (w : KeyedAllocWorld)
    (id : MiriAllocId) (entry : LiveAllocEntry)
    (expectedLayout : Option (UInt64 × UInt8)) (expectedKind : AllocMemKind)
    (mode : RaceDetectorMode) (actor : DeallocActor) (tb : DeallocHookSpec)
    (hlive : w.findLive? id = some entry) :
    let res := w.deallocateMachine (.provenanced id 0) expectedLayout expectedKind mode actor tb
    res.detached = some (id, entry) ∧ res.world.findLive? id = none ∧
    res.world.findRace? id = none := by
  have hcore := keyedDeallocateWith_live_always_detaches w id entry expectedLayout expectedKind
    (fun wDetached id entry =>
      machineDeallocHook mode actor tb (wDetached.findRace? id) entry.sizeBytes) hlive
  have hproj := keyedDetachRaceClock_preserves_outcome_detached_and_tables
    (w.deallocateWith (.provenanced id 0) expectedLayout expectedKind
      (fun wDetached id entry =>
        machineDeallocHook mode actor tb (wDetached.findRace? id) entry.sizeBytes)) id
  have hdet : (w.deallocateMachine (.provenanced id 0) expectedLayout expectedKind mode actor tb).detached =
      some (id, entry) := hproj.2.1.trans hcore.1
  exact ⟨hdet, hproj.2.2.1.trans hcore.2,
    (keyedDeallocateMachine_detached_drops_raceClock w (.provenanced id 0) expectedLayout
      expectedKind mode actor tb id entry hdet).1⟩

/-- With the race detector `unconfigured`, machine deallocation is core deallocation followed by the
(unconditional) detach cleanup of the allocation's race clock. -/
theorem keyedDeallocateMachine_unconfigured_eq_detachRaceClock (w : KeyedAllocWorld)
    (ptr : DeallocPtr) (expectedLayout : Option (UInt64 × UInt8))
    (expectedKind : AllocMemKind) (actor : DeallocActor) (tb : DeallocHookSpec := .ok) :
    w.deallocateMachine ptr expectedLayout expectedKind .unconfigured actor tb =
      KeyedAllocWorld.detachRaceClock (w.deallocate ptr expectedLayout expectedKind tb) := rfl

/-- With the race detector `unconfigured` and no stale clock recorded for the pointed-to allocation
(the invariant maintained by `allocateMachine … .unconfigured`), machine deallocation coincides with
core deallocation. -/
theorem keyedDeallocateMachine_unconfigured_eq_deallocate (w : KeyedAllocWorld)
    (ptr : DeallocPtr) (expectedLayout : Option (UInt64 × UInt8))
    (expectedKind : AllocMemKind) (actor : DeallocActor) (tb : DeallocHookSpec := .ok)
    (hnoClk : ∀ id off, ptr = .provenanced id off → w.findRace? id = none) :
    w.deallocateMachine ptr expectedLayout expectedKind .unconfigured actor tb =
      w.deallocate ptr expectedLayout expectedKind tb := by
  rw [keyedDeallocateMachine_unconfigured_eq_detachRaceClock w ptr expectedLayout expectedKind actor tb]
  unfold KeyedAllocWorld.detachRaceClock KeyedAllocWorld.deallocate
  have hid := keyedDeallocateWith_detached_id w ptr expectedLayout expectedKind (fun _ _ _ => tb.run)
  have hrace := keyedDeallocateWith_preserves_raceClocks w ptr expectedLayout expectedKind
    (fun _ _ _ => tb.run)
  generalize w.deallocateWith ptr expectedLayout expectedKind (fun _ _ _ => tb.run) = res
    at hid hrace ⊢
  rcases res with ⟨resWorld, resDetached, resOutcome⟩
  cases resDetached with
  | none => rfl
  | some p =>
    rcases p with ⟨id, entry⟩
    dsimp only
    have hptr := (hid id entry rfl).1
    have hno : resWorld.findRace? id = none := by
      rw [hrace id]; exact hnoClk id 0 hptr
    rw [keyedRemoveRace_eq_self_of_noClock _ id hno]

theorem keyedDeallocateMachine_missingClock_invalid (w : KeyedAllocWorld)
    (id : MiriAllocId) (entry : LiveAllocEntry) (raceDetecting : Bool)
    (actor : DeallocActor) (tb : DeallocHookSpec := .ok)
    (hlive : w.findLive? id = some entry)
    (hmut : entry.mutability = .mut)
    (hnoClk : w.findRace? id = none) :
    let res := w.deallocateMachine (.provenanced id 0) none entry.kind (.configured raceDetecting) actor tb
    res.outcome = .error (.hookFailure "MissingVectorClockExtra") ∧
    res.detached = some (id, entry) ∧
    res.world.findLive? id = none := by
  have hmutF : (entry.mutability == .not) = false := by rw [hmut]; rfl
  simp only [KeyedAllocWorld.findLive?] at hlive
  simp only [KeyedAllocWorld.findRace?] at hnoClk
  simp [KeyedAllocWorld.deallocateMachine, KeyedAllocWorld.deallocateWith,
    KeyedAllocWorld.detachRaceClock, machineDeallocHook, deallocLayoutMismatch?,
    KeyedAllocWorld.removeLive, KeyedAllocWorld.removeRace, hlive, hmutF,
    KeyedAllocWorld.findRace?, hnoClk, KeyedAllocWorld.findLive?, ExtTreeMap0.get?_erase_self]

/-- A configured-but-not-detecting race detector (`race_detecting = false`, e.g. single-threaded
execution) skips the clock comparison: whenever the allocation's clock is present, machine
deallocation is core deallocation followed by the detach cleanup. -/
theorem keyedDeallocateMachine_notDetecting_eq_deallocate (w : KeyedAllocWorld)
    (id : MiriAllocId) (off : UInt64) (clk : RaceClockEntry)
    (expectedLayout : Option (UInt64 × UInt8)) (expectedKind : AllocMemKind)
    (actor : DeallocActor) (tb : DeallocHookSpec := .ok)
    (hclk : w.findRace? id = some clk) :
    w.deallocateMachine (.provenanced id off) expectedLayout expectedKind (.configured false) actor tb =
      KeyedAllocWorld.detachRaceClock
        (w.deallocate (.provenanced id off) expectedLayout expectedKind tb) := by
  have hrem : (w.removeLive id).1.findRace? id = some clk := by
    unfold KeyedAllocWorld.removeLive
    cases w.findLive? id <;> exact hclk
  simp [KeyedAllocWorld.deallocateMachine, KeyedAllocWorld.deallocate,
    KeyedAllocWorld.deallocateWith, machineDeallocHook, hrem]

/-- The data-race verdict is computed from the allocation's vector clock BEFORE the clock is cleaned
up: the racing deallocation reports `DataRace` (a cleanup-first order would instead report
`MissingVectorClockExtra`, as the last conjunct shows on the pre-cleaned world), and the failed
deallocation still detaches the live entry AND its clock without recording a tombstone. -/
theorem keyedDeallocateMachine_race_checked_before_cleanup (w : KeyedAllocWorld)
    (id : MiriAllocId) (entry : LiveAllocEntry) (clk : RaceClockEntry) (actor : DeallocActor)
    (hlive : w.findLive? id = some entry)
    (hmut : entry.mutability = .mut)
    (hsize : entry.sizeBytes ≠ 0)
    (hclk : w.findRace? id = some clk)
    (hrace : hasDeallocDataRace actor clk = true) :
    let res := w.deallocateMachine (.provenanced id 0) none entry.kind (.configured true) actor .ok
    res.outcome = .error (.hookFailure "DataRace") ∧
    res.detached = some (id, entry) ∧
    res.world.findLive? id = none ∧
    res.world.findRace? id = none ∧
    res.world.findDead? id = w.findDead? id ∧
    ((w.removeRace id).deallocateMachine (.provenanced id 0) none entry.kind (.configured true)
      actor .ok).outcome = .error (.hookFailure "MissingVectorClockExtra") := by
  have hmutF : (entry.mutability == .not) = false := by rw [hmut]; rfl
  have hszT : (entry.sizeBytes != 0) = true := bne_iff_ne.2 hsize
  simp only [KeyedAllocWorld.findLive?] at hlive
  simp only [KeyedAllocWorld.findRace?] at hclk
  simp [KeyedAllocWorld.deallocateMachine, KeyedAllocWorld.deallocateWith,
    KeyedAllocWorld.detachRaceClock, machineDeallocHook, deallocLayoutMismatch?,
    KeyedAllocWorld.removeLive, KeyedAllocWorld.removeRace, hlive, hmutF, hszT,
    KeyedAllocWorld.findRace?, KeyedAllocWorld.findDead?, hclk, hrace, KeyedAllocWorld.findLive?,
    ExtTreeMap0.get?_erase_self]

theorem keyedDeallocateMachine_sameWriter_foreignRead_races (w : KeyedAllocWorld)
    (id : MiriAllocId) (entry : LiveAllocEntry) (clk : RaceClockEntry) (actor : DeallocActor)
    (hlive : w.findLive? id = some entry)
    (hmut : entry.mutability = .mut)
    (hsize : entry.sizeBytes ≠ 0)
    (hclk : w.findRace? id = some clk)
    (_hsameWriter : clk.writerThread = actor.threadId)
    (hforeignReader : clk.readerThread ≠ actor.threadId)
    (hreadNz : clk.readTimestamp ≠ 0)
    (hunsync : actor.viewFor clk.readerThread < clk.readTimestamp) :
    (w.deallocateMachine (.provenanced id 0) none entry.kind (.configured true) actor .ok).outcome =
      .error (.hookFailure "DataRace") := by
  have hrace : hasDeallocDataRace actor clk = true := by
    unfold hasDeallocDataRace
    have h1 : (clk.readerThread != actor.threadId) = true := bne_iff_ne.2 hforeignReader
    have h2 : (clk.readTimestamp != 0) = true := bne_iff_ne.2 hreadNz
    have h3 : decide (actor.viewFor clk.readerThread < clk.readTimestamp) = true :=
      decide_eq_true hunsync
    simp [h1, h2, h3]
  exact (keyedDeallocateMachine_race_checked_before_cleanup w id entry clk actor
    hlive hmut hsize hclk hrace).1

theorem keyedDeallocateMachine_perThreadClock_catches_unsynced_reader (w : KeyedAllocWorld)
    (id : MiriAllocId) (entry : LiveAllocEntry) (clk : RaceClockEntry) (actor : DeallocActor)
    (rt : UInt32) (rts : UInt64)
    (hlive : w.findLive? id = some entry)
    (hmut : entry.mutability = .mut)
    (hsize : entry.sizeBytes ≠ 0)
    (hclk : w.findRace? id = some clk)
    (hmem : (rt, rts) ∈ clk.extraReaders)
    (hforeign : rt ≠ actor.threadId)
    (hrtsNz : rts ≠ 0)
    (hunsync : actor.viewFor rt < rts) :
    (w.deallocateMachine (.provenanced id 0) none entry.kind (.configured true) actor .ok).outcome =
      .error (.hookFailure "DataRace") := by
  have hrace : hasDeallocDataRace actor clk = true := by
    unfold hasDeallocDataRace
    have hextra :
        (clk.extraReaders.any fun p =>
          p.1 != actor.threadId && p.2 != 0 && decide (actor.viewFor p.1 < p.2)) = true := by
      rw [List.any_eq_true]
      refine ⟨(rt, rts), hmem, ?_⟩
      simp [bne_iff_ne.2 hforeign, bne_iff_ne.2 hrtsNz, decide_eq_true hunsync]
    simp [hextra]
  exact (keyedDeallocateMachine_race_checked_before_cleanup w id entry clk actor
    hlive hmut hsize hclk hrace).1

theorem keyedDeallocateMachine_zst_skips_race_check (w : KeyedAllocWorld)
    (id : MiriAllocId) (entry : LiveAllocEntry) (clk : RaceClockEntry) (actor : DeallocActor)
    (hlive : w.findLive? id = some entry)
    (hmut : entry.mutability = .mut)
    (hzst : entry.sizeBytes = 0)
    (hclk : w.findRace? id = some clk)
    (hnotDead : w.findDead? id = none) :
    (w.deallocateMachine (.provenanced id 0) none entry.kind (.configured true) actor .ok).outcome =
      .ok () := by
  have hmutF : (entry.mutability == .not) = false := by rw [hmut]; rfl
  simp only [KeyedAllocWorld.findLive?] at hlive
  simp only [KeyedAllocWorld.findRace?] at hclk
  simp only [KeyedAllocWorld.findDead?] at hnotDead
  simp [KeyedAllocWorld.deallocateMachine, KeyedAllocWorld.deallocateWith,
    KeyedAllocWorld.detachRaceClock, machineDeallocHook, deallocLayoutMismatch?,
    KeyedAllocWorld.removeLive, KeyedAllocWorld.findLive?,
    hlive, hmutF, hzst, KeyedAllocWorld.findRace?, hclk, DeallocHookSpec.run,
    KeyedAllocWorld.findDead?, hnotDead]

theorem keyedAllocateMachine_deallocateMachine_sameThread_ok (w w1 : KeyedAllocWorld)
    (entry : LiveAllocEntry) (mode : RaceDetectorMode)
    (tid : UInt32) (ts : UInt64) (id : MiriAllocId)
    (hmut : entry.mutability = .mut)
    (hnotDead : w.findDead? id = none)
    (halloc : w.allocateMachine entry mode tid ts = (w1, .ok id)) :
    let res := w1.deallocateMachine (.provenanced id 0) (some (entry.sizeBytes, entry.alignPow2))
      entry.kind mode (DeallocActor.ofVClock tid [(tid, ts)]) .ok
    res.outcome = .ok () ∧ res.world.findRace? id = none ∧ res.world.findLive? id = none := by
  have hmutF : (entry.mutability == .not) = false := by rw [hmut]; rfl
  unfold KeyedAllocWorld.allocateMachine KeyedAllocWorld.allocate at halloc
  cases hres : w.reserveAllocId with
  | mk wr ores =>
    rw [hres] at halloc
    cases ores with
    | error e => simp at halloc
    | ok id' =>
      simp only at halloc
      have hEqId : id' = id := by
        cases mode with
        | unconfigured =>
          injection halloc with _ hok; injection hok
        | configured _ =>
          injection halloc with _ hok; injection hok
      subst hEqId
      have hdead_wr : wr.table.dead.get? id' = none := by
        rw [(keyedReserveAllocId_ok_inv hres).2.2.2.2]
        exact hnotDead
      cases mode with
      | unconfigured =>
        injection halloc with hw1 hok
        subst hw1
        simp [KeyedAllocWorld.deallocateMachine, KeyedAllocWorld.deallocateWith,
          KeyedAllocWorld.detachRaceClock, machineDeallocHook, deallocLayoutMismatch?,
          KeyedAllocWorld.insertLive, KeyedAllocWorld.removeLive, KeyedAllocWorld.findLive?,
          KeyedAllocWorld.removeRace, KeyedAllocWorld.findRace?, KeyedAllocWorld.insertDead,
          ExtTreeMap0.get?_insert_self, ExtTreeMap0.get?_erase_self, hmutF, DeallocHookSpec.run,
          KeyedAllocWorld.findDead?, hdead_wr]
      | configured raceDetecting =>
        injection halloc with hw1 hok
        subst hw1
        have hnoRace :
            hasDeallocDataRace (DeallocActor.ofVClock tid [(tid, ts)])
              { writerThread := tid, writeTimestamp := ts, readerThread := tid, readTimestamp := 0, extraReaders := [] } = false := by
          simp [hasDeallocDataRace, DeallocActor.ofVClock]
        simp [KeyedAllocWorld.deallocateMachine, KeyedAllocWorld.deallocateWith,
          KeyedAllocWorld.detachRaceClock, machineDeallocHook, deallocLayoutMismatch?,
          KeyedAllocWorld.setRace, KeyedAllocWorld.insertDead,
          KeyedAllocWorld.insertLive, KeyedAllocWorld.removeLive, KeyedAllocWorld.findLive?,
          KeyedAllocWorld.findRace?, KeyedAllocWorld.removeRace, KeyedAllocWorld.findDead?,
          ExtTreeMap0.get?_insert_self, ExtTreeMap0.get?_erase_self, hmutF, hnoRace,
          DeallocHookSpec.run, hdead_wr]

/-- Contrast theorem: `DeallocActor.ofVClock` catches an unlisted foreign reader (`viewFor = 0`),
whereas a nonzero fallback `observedTimestamp` unsoundly accepts the racing deallocation. -/
theorem deallocActor_ofVClock_catches_unlisted_reader_vs_nonzeroFallback
    (w : KeyedAllocWorld) (id : MiriAllocId) (entry : LiveAllocEntry)
    (hlive : w.findLive? id = some entry)
    (hmut : entry.mutability = .mut)
    (hsize : entry.sizeBytes ≠ 0)
    (hnotDead : w.findDead? id = none)
    (hclk : w.findRace? id = some ⟨1, 2, 1, 0, [(3, 5)]⟩) :
    (w.deallocateMachine (.provenanced id 0) none entry.kind (.configured true)
      (DeallocActor.ofVClock 1 [(2, 10)]) .ok).outcome = .error (.hookFailure "DataRace") ∧
    (w.deallocateMachine (.provenanced id 0) none entry.kind (.configured true)
      ⟨1, 10, [(2, 10)]⟩ .ok).outcome = .ok () := by
  constructor
  · exact keyedDeallocateMachine_perThreadClock_catches_unsynced_reader w id entry
      ⟨1, 2, 1, 0, [(3, 5)]⟩ (DeallocActor.ofVClock 1 [(2, 10)]) 3 5
      hlive hmut hsize hclk (by simp) (by decide) (by decide) (by decide)
  · have hmutF : (entry.mutability == .not) = false := by rw [hmut]; rfl
    have hnoRace : hasDeallocDataRace ⟨1, 10, [(2, 10)]⟩ ⟨1, 2, 1, 0, [(3, 5)]⟩ = false := by
      decide
    simp only [KeyedAllocWorld.findLive?] at hlive
    simp only [KeyedAllocWorld.findRace?] at hclk
    simp only [KeyedAllocWorld.findDead?] at hnotDead
    simp [KeyedAllocWorld.deallocateMachine, KeyedAllocWorld.deallocateWith,
      KeyedAllocWorld.detachRaceClock, machineDeallocHook, deallocLayoutMismatch?,
      KeyedAllocWorld.removeLive, KeyedAllocWorld.findLive?,
      hlive, hmutF, KeyedAllocWorld.findRace?, hclk, hnoRace, DeallocHookSpec.run,
      KeyedAllocWorld.findDead?, hnotDead]

/-! ## Part 2: `#[rustc_no_writable]` (`charon#1619` + `minirust#295`) & Static-Access Retags (`charon#1620`) -/

/-! ### 2A.1 `FnEntryRetagPolicy`, `FnParamRetagMap`, and Upstream `RetagPolicy.create` Mirror -/

/-- Function-entry retag policy for a reference or `Box` parameter (`charon#1619` + `minirust#295`). -/
inductive FnEntryRetagPolicy where
  /-- Retagging skipped (e.g., `!Unpin` `&mut T` or `Box<T>`). -/
  | skipRetag
  /-- Standard `Unpin` `&mut T` / `Box<T>` function-entry retag performing an implicit child write. -/
  | writableChildWrite
  /-- `#[rustc_no_writable]` `&mut T` (or shared `&T`): protected reborrow without implicit write. -/
  | rustcNoWritable
  deriving DecidableEq, Repr, Inhabited

/-- Reference/pointer kind passed to function-entry retag policy selection. -/
inductive RefParamKind where
  | shared
  | mutable
  | box
  deriving DecidableEq, Repr, Inhabited

/-- Compiler type traits governing retag policy (`Miri.TreeBorrows.RetagPolicy.TypeFacts`). -/
structure ParamTypeFacts where
  isUnpin : Bool
  isUnsafeUnpin : Bool
  isFreeze : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Retag configuration flags (`Miri.TreeBorrows.RetagPolicy.PolicyConfig`). -/
structure ParamRetagAttrs where
  implicitWrites : Bool := true
  rustcNoWritable : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Select the `FnEntryRetagPolicy` for a parameter given compiler type facts, reference kind, and attributes. -/
def selectFnEntryPolicy (facts : ParamTypeFacts) (kind : RefParamKind)
    (attrs : ParamRetagAttrs) : FnEntryRetagPolicy :=
  let tyIsUnpin := facts.isUnpin && facts.isUnsafeUnpin
  match kind with
  | .shared => .rustcNoWritable
  | .mutable | .box =>
    if !tyIsUnpin then
      .skipRetag
    else if attrs.implicitWrites && !attrs.rustcNoWritable then
      .writableChildWrite
    else
      .rustcNoWritable

theorem pinned_mutable_or_box_fnEntry_skips_retag (facts : ParamTypeFacts)
    (attrs : ParamRetagAttrs) (hnotUnpin : (facts.isUnpin && facts.isUnsafeUnpin) = false) :
    selectFnEntryPolicy facts .mutable attrs = .skipRetag ∧
    selectFnEntryPolicy facts .box attrs = .skipRetag := by
  simp [selectFnEntryPolicy, hnotUnpin]

theorem selectFnEntryPolicy_rustcNoWritable_mut (facts : ParamTypeFacts)
    (implicitWrites : Bool) (hunpin : (facts.isUnpin && facts.isUnsafeUnpin) = true) :
    selectFnEntryPolicy facts .mutable ⟨implicitWrites, true⟩ = .rustcNoWritable := by
  simp [selectFnEntryPolicy, hunpin]

/-- Per-parameter function-entry retag policy map indexed by MIR local index. -/
structure FnParamRetagMap where
  entries : List (Nat × FnEntryRetagPolicy) := []
  defaultPolicy : FnEntryRetagPolicy := .writableChildWrite
  deriving DecidableEq, Repr, Inhabited

namespace FnParamRetagMap

def empty (defaultPolicy : FnEntryRetagPolicy := .writableChildWrite) : FnParamRetagMap :=
  { entries := [], defaultPolicy }

def set (m : FnParamRetagMap) (paramLocal : Nat) (pol : FnEntryRetagPolicy) : FnParamRetagMap :=
  { m with entries := (paramLocal, pol) :: m.entries.filter (fun p => p.1 != paramLocal) }

def policyFor (m : FnParamRetagMap) (paramLocal : Nat) : FnEntryRetagPolicy :=
  match m.entries.find? (fun p => p.1 == paramLocal) with
  | some (_, pol) => pol
  | none => m.defaultPolicy

private theorem find?_filter_ne_nat (xs : List (Nat × FnEntryRetagPolicy)) (loc loc' : Nat)
    (hne : loc' ≠ loc) :
    (xs.filter (fun p => p.1 != loc)).find? (fun p => p.1 == loc') =
      xs.find? (fun p => p.1 == loc') := by
  induction xs with
  | nil => rfl
  | cons p rest ih =>
    by_cases hp : p.1 = loc
    · subst hp
      have hne' : (p.1 == loc') = false := beq_false_of_ne (fun h => hne h.symm)
      simp [List.find?, hne', ih]
    · have hbne : (p.1 != loc) = true := bne_iff_ne.2 hp
      simp only [List.filter_cons, hbne, ↓reduceIte, List.find?]
      cases p.1 == loc' with
      | true => rfl
      | false => exact ih

theorem policyFor_set (m : FnParamRetagMap) (loc loc' : Nat) (pol : FnEntryRetagPolicy) :
    (m.set loc pol).policyFor loc' = if loc' == loc then pol else m.policyFor loc' := by
  unfold set policyFor
  simp only [List.find?]
  by_cases h : loc' = loc
  · subst h; simp
  · have h1 : (loc == loc') = false := beq_false_of_ne (fun he => h he.symm)
    have h2 : (loc' == loc) = false := beq_false_of_ne h
    simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
    rw [find?_filter_ne_nat m.entries loc loc' h]

theorem policyFor_set_self (m : FnParamRetagMap) (loc : Nat) (pol : FnEntryRetagPolicy) :
    (m.set loc pol).policyFor loc = pol := by
  rw [policyFor_set]; simp

theorem policyFor_set_ne (m : FnParamRetagMap) {loc loc' : Nat} (pol : FnEntryRetagPolicy)
    (hne : loc' ≠ loc) : (m.set loc pol).policyFor loc' = m.policyFor loc' := by
  rw [policyFor_set, beq_false_of_ne hne]; rfl

end FnParamRetagMap

/-! Exact mirror of `Miri.TreeBorrows.RetagPolicy` (`NewPermission::new` in pinned Miri)
requiring zero imports from `lean-miri/vendor/Miri` and zero `Classical.choice`. -/
deriving instance DecidableEq, Repr for Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowPerm

instance : Inhabited Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowPerm := ⟨.disabled⟩

namespace MiriRetagPolicyMirror

inductive RetagMode where
  | none
  | default
  | twoPhase
  | fnEntry
  | raw
  deriving DecidableEq, Repr, Inhabited

inductive ProtectorKind where
  | weakProtector
  | strongProtector
  deriving DecidableEq, Repr, Inhabited

structure NewPermission where
  freezePermission : TreeBorrowPerm
  nonfreezePermission : TreeBorrowPerm
  outsidePermission : TreeBorrowPerm
  protector : Option ProtectorKind
  deriving DecidableEq, Repr

private inductive Part where
  | insideFrozen
  | insideUnsafeCell
  | outside
  deriving DecidableEq, Repr

private def selectedPermission (kind : RefParamKind) (part : Part)
    (frozen isProtected implicitWrites : Bool) : TreeBorrowPerm :=
  match kind with
  | .shared => if frozen then .frozen else .cell
  | .mutable | .box =>
    if implicitWrites && part != .outside then .unique
    else if isProtected || frozen then .reservedFrz false
    else .reservedIM

/-- Verbatim functional mirror of `Miri.TreeBorrows.RetagPolicy.create`. -/
def create (facts : ParamTypeFacts) (kind : RefParamKind) (mode : RetagMode)
    (attrs : ParamRetagAttrs) : Option NewPermission :=
  if mode == .none then none
  else
    let tyIsUnpin := facts.isUnpin && facts.isUnsafeUnpin
    let isProtected := mode == .fnEntry
    let implicitWritesEnabled := isProtected && attrs.implicitWrites && !attrs.rustcNoWritable
    if (kind == .mutable || kind == .box) && !tyIsUnpin then
      none
    else
      let choose (part : Part) :=
        let frozen :=
          match part with
          | .insideFrozen => true
          | .insideUnsafeCell => false
          | .outside => facts.isFreeze
        selectedPermission kind part frozen isProtected implicitWritesEnabled
      let protector :=
        if isProtected then
          some (if kind == .box then .weakProtector else .strongProtector)
        else none
      some {
        freezePermission := choose .insideFrozen
        nonfreezePermission := choose .insideUnsafeCell
        outsidePermission := choose .outside
        protector
      }

/-- Classify an upstream `Option NewPermission` back into `FnEntryRetagPolicy`. -/
def classifyFnEntry : Option NewPermission → FnEntryRetagPolicy
  | none => .skipRetag
  | some p =>
    match p.freezePermission with
    | .unique => .writableChildWrite
    | _ => .rustcNoWritable

end MiriRetagPolicyMirror

/-- Exact correspondence between `selectFnEntryPolicy` and upstream `RetagPolicy.create` across all inputs. -/
theorem selectFnEntryPolicy_eq_upstream_create
    (facts : ParamTypeFacts) (kind : RefParamKind) (attrs : ParamRetagAttrs) :
    MiriRetagPolicyMirror.classifyFnEntry
      (MiriRetagPolicyMirror.create facts kind .fnEntry attrs) =
      selectFnEntryPolicy facts kind attrs := by
  cases facts with | mk u uu frz =>
  cases kind <;> cases attrs with | mk iw rnw =>
  cases u <;> cases uu <;> cases frz <;> cases iw <;> cases rnw <;> rfl

/-! ### 2A.2 Operational Bridge to `Trusted.Rustc.V2026_06_01.MirSemantics` -/

theorem fnEntryRetagPerm_mut_eq_reservedFrz (pointee : RigidTy) :
    fnEntryRetagPerm .mut pointee = TreeBorrowPerm.reservedFrz false := rfl

theorem retagPerm_fnEntry_eq_fnEntryRetagPerm (mutability : Mutability) (pointee : RigidTy) :
    retagPerm .fnEntry mutability pointee = fnEntryRetagPerm mutability pointee := rfl

/-- Post-retag implicit child write overlay for `Trusted.Rustc.V2026_06_01.MirSemantics.MachineState`,
modeling the `writableChildWrite` transition after `evalStmt (.retag .fnEntry place)`.
No-op on zero-sized pointees (`rigidTyIsZeroSized 16 pointee = true`) and non-`&mut` places. -/
def applyParamFnEntryImplicitWrite
    (s : MachineState) (localDecls : List LocalDecl)
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (place : Place) : MirStepNode :=
  match placeTy localDecls layouts place with
  | .some ty =>
    match ty.kind with
    | .ref .mut pointee =>
      match rigidTyIsZeroSized 16 pointee with
      | true => MirStepNode.step s
      | false =>
        match Trusted.Sequence.get? s.frame.locals place.local_ with
        | .some (.init (.ptr ptrVal _)) =>
          match lookupBorrow s.memory.borrows ptrVal.tag with
          | .some childEntry =>
            let ancUB := treeBorrowAncestorsChildAccessUB .write s.memory.borrows childEntry.parentTag
            let protUB :=
              hasProtectedTreeWriteConflict
                s.memory.borrows
                s.memory.borrows
                s.memory.activeProtectors
                childEntry.targetLocal
                (.some childEntry.tag)
                childEntry.targetProjection
                childEntry.rangeOffset
                childEntry.rangeLen
                childEntry.targetFrameDepth
            if ancUB || protUB then
              MirStepNode.fail .ub
            else
              let borrows' :=
                invalidateTreeBorrowsAtProj
                  s.memory.borrows
                  s.memory.borrows
                  childEntry.targetLocal
                  (.some childEntry.tag)
                  childEntry.targetProjection
                  childEntry.rangeOffset
                  childEntry.rangeLen
                  childEntry.targetFrameDepth
              MirStepNode.step { s with memory := { s.memory with borrows := borrows' } }
          | .none => MirStepNode.step s
        | _ => MirStepNode.step s
    | _ => MirStepNode.step s
  | .none => MirStepNode.step s

theorem applyParamFnEntryImplicitWrite_zst_noop
    (s : MachineState) (localDecls : List LocalDecl)
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (place : Place) (ty : Ty) (pointee : RigidTy)
    (hty : placeTy localDecls layouts place = .some ty)
    (href : ty.kind = .ref .mut pointee)
    (hzst : rigidTyIsZeroSized 16 pointee = true) :
    applyParamFnEntryImplicitWrite s localDecls layouts place = MirStepNode.step s := by
  simp [applyParamFnEntryImplicitWrite, hty, href, hzst]

/-- Execute a `StatementKind.retag .fnEntry place` with a per-parameter `FnParamRetagMap` overlay
over `Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt`. -/
def evalFnEntryRetagWithParamMap
    (paramMap : FnParamRetagMap)
    (s : MachineState) (place : Place) (span : String)
    (localDecls : List LocalDecl)
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable) : MirStepNode :=
  match paramMap.policyFor place.local_ with
  | .skipRetag => MirStepNode.step (advanceStmt s s.frame.locals)
  | .rustcNoWritable =>
    evalStmt s ⟨.retag .fnEntry place, span⟩ localDecls layouts
  | .writableChildWrite =>
    match evalStmt s ⟨.retag .fnEntry place, span⟩ localDecls layouts with
    | .tau (.running s') => applyParamFnEntryImplicitWrite s' localDecls layouts place
    | other => other

theorem evalFnEntryRetagWithParamMap_rustcNoWritable_eq_evalStmt
    (paramMap : FnParamRetagMap)
    (s : MachineState) (place : Place) (span : String)
    (localDecls : List LocalDecl)
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (hpol : paramMap.policyFor place.local_ = .rustcNoWritable) :
    evalFnEntryRetagWithParamMap paramMap s place span localDecls layouts =
      evalStmt s ⟨.retag .fnEntry place, span⟩ localDecls layouts := by
  simp [evalFnEntryRetagWithParamMap, hpol]

/-! ### 2A.3 Three Borrow-Tree Retag Models, Bottom-Up `ancestorPathNodes`, and Equivalence -/

/-- Coarse-ranged borrow-tree node used by the `FnEntry` retag models, mirroring
`Miri.TreeBorrows.Tree.LocationState` (`accessed` gates whether a protected foreign transition to
`.disabled` triggers `ProtectedDisabled` UB, `LocationState.lean:139-145`). -/
structure TreeTagNode where
  tag : Nat
  parentTag : Option Nat
  perm : TreeBorrowPerm
  rangeOffset : Nat
  rangeLen : Nat
  protector : Option Nat
  accessed : Bool := true
  deriving DecidableEq, Repr, Inhabited

namespace TreeTagNode

/-- Project `TreeTagNode` into `Anneal.Memory.ByteRangePerm`. -/
def toByteRangePerm (allocId : Nat) (n : TreeTagNode) : Anneal.Memory.ByteRangePerm where
  tag := n.tag
  allocId := allocId
  offset := n.rangeOffset
  len := n.rangeLen
  perm := Anneal.Memory.TreeBorrowPerm.toAbstractPerm n.perm
  protector := n.protector

/-- Whether `n` carries an active protector in `activeProtectors`. -/
def isProtected (n : TreeTagNode) (activeProtectors : List Nat) : Bool :=
  match n.protector with
  | some p => activeProtectors.any (fun q => q == p)
  | none => false

theorem isProtected_eq_toByteRangePerm (allocId : Nat) (n : TreeTagNode)
    (activeProtectors : List Nat) :
    n.isProtected activeProtectors =
      (n.toByteRangePerm allocId).isProtected ⟨activeProtectors⟩ := by
  unfold isProtected toByteRangePerm Anneal.Memory.ByteRangePerm.isProtected
    Anneal.Memory.ProtectorSet.contains
  cases n.protector with
  | none => rfl
  | some p =>
    simp only
    induction activeProtectors with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.any_cons, natListContainsBool]
      have hbeq : (x == p) = Nat.beq x p := by
        cases h : Nat.beq x p with
        | true =>
          have heq : x = p := Nat.eq_of_beq_eq_true h
          subst heq; simp
        | false =>
          have hne : x ≠ p := fun heq => by subst heq; simp at h
          exact beq_false_of_ne hne
      rw [hbeq, ih]
      cases Nat.beq x p <;> rfl

end TreeTagNode

/-- Half-open byte range overlap test (`[aOff, aOff + aLen) ∩ [bOff, bOff + bLen) ≠ ∅`). -/
def rangesOverlap (aOff aLen bOff bLen : Nat) : Bool :=
  aLen != 0 && bLen != 0 && decide (aOff < bOff + bLen) && decide (bOff < aOff + aLen)

/-- Borrow-tree world for function-entry mutable reference retagging. `allocReadOnly` records whether
the retagged pointer's allocation is immutable (`Mutability::Not`, e.g. a `Freeze` `static` or promoted
constant): upstream `tb_reborrow` rejects an implicit FnEntry WRITE into such an allocation before any
tree access (`RetagPipeline.accessTreeForReborrow`: `writeToReadOnly`), while read reborrows ignore it. -/
structure FnEntryBorrowWorld where
  nodes : List TreeTagNode
  activeProtectors : List Nat
  nextTag : Nat
  nextProtector : Nat
  pointeeInitialized : Bool := true
  allocReadOnly : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Structured errors for function-entry mutable borrow-tree retag execution. -/
inductive RetagStepErr where
  | missingParentTag (tag : Nat)
  | disabledParentTag (tag : Nat)
  | writeToReadOnlyAlloc
  | uninitializedPointeeWrite
  | ancestorWriteForbidden (tag : Nat)
  | conflictedProtectedChildWrite (tag : Nat)
  | protectedForeignConflict (tag : Nat)
  deriving DecidableEq, Repr

/-- Find the first `TreeTagNode` with tag `t`. -/
def findNode? (nodes : List TreeTagNode) (t : Nat) : Option TreeTagNode :=
  nodes.find? (fun n => n.tag == t)

/-- Bottom-up ancestor tag path `start -> parent -> ... -> root`, mirroring `TraversalTree.ancestorPath`. -/
def ancestorPathTagsAux (nodes : List TreeTagNode) : Nat → Nat → List Nat
  | 0, cur => [cur]
  | fuel + 1, cur =>
    match findNode? nodes cur with
    | some n =>
      match n.parentTag with
      | some p => cur :: ancestorPathTagsAux nodes fuel p
      | none => [cur]
    | none => [cur]

def ancestorPathTags (nodes : List TreeTagNode) (start : Nat) : List Nat :=
  ancestorPathTagsAux nodes (nodes.length + 1) start

theorem ancestorPathTagsAux_head (nodes : List TreeTagNode) (fuel start : Nat) :
    (ancestorPathTagsAux nodes fuel start).head? = some start := by
  cases fuel with
  | zero => rfl
  | succ f =>
    simp only [ancestorPathTagsAux]
    cases findNode? nodes start with
    | none => rfl
    | some n =>
      cases h : n.parentTag <;> simp [h]

theorem ancestorPathTags_head (nodes : List TreeTagNode) (start : Nat) :
    (ancestorPathTags nodes start).head? = some start :=
  ancestorPathTagsAux_head nodes (nodes.length + 1) start

/-- Bottom-up ancestor node sequence (`start -> parent -> ... -> root`), visiting every node
whose tag appears along `ancestorPathTags` in bottom-up order. -/
def ancestorPathNodes (nodes : List TreeTagNode) (start : Nat) : List TreeTagNode :=
  (ancestorPathTags nodes start).flatMap (fun t => nodes.filter (fun n => n.tag == t))

theorem ancestorPathNodes_head (nodes : List TreeTagNode) (start : Nat) (n : TreeTagNode)
    (hhead : (nodes.filter (fun m => m.tag == start)).head? = some n) :
    (ancestorPathNodes nodes start).head? = some n := by
  unfold ancestorPathNodes
  have hh := ancestorPathTags_head nodes start
  cases hp : ancestorPathTags nodes start with
  | nil => rw [hp] at hh; cases hh
  | cons t rest =>
    rw [hp] at hh
    injection hh with ht
    subst ht
    simp only [List.flatMap_cons]
    cases hf : nodes.filter (fun m => m.tag == t) with
    | nil => rw [hf] at hhead; cases hhead
    | cons m ms =>
      rw [hf] at hhead
      injection hhead with hm
      subst hm
      rfl

/-- Single-node Tree Borrows read transition (`Miri.TreeBorrows.Tree.LocationState.performAccess .Read`):
local non-disabled reads latch `accessed := true`; protected foreign `.unique` disablement raises
`.protectedForeignConflict` iff `n.accessed = true` (`LocationState.lean:144`). -/
def stepNodeOnRangeRead (activeProtectors : List Nat) (isLocal : Bool)
    (off len : Nat) (n : TreeTagNode) : Except RetagStepErr TreeTagNode :=
  if !rangesOverlap off len n.rangeOffset n.rangeLen then
    .ok n
  else if isLocal then
    match n.perm with
    | .disabled => .error (.disabledParentTag n.tag)
    | _ => .ok { n with accessed := true }
  else
    match n.perm with
    | .cell => .ok n
    | .frozen => .ok n
    | .disabled => .ok n
    | .reservedFrz _ =>
      if n.isProtected activeProtectors then .ok { n with perm := .reservedFrz true }
      else .ok n
    | .reservedIM =>
      if n.isProtected activeProtectors then .error (.protectedForeignConflict n.tag)
      else .ok n
    | .unique =>
      if n.isProtected activeProtectors then
        if n.accessed then .error (.protectedForeignConflict n.tag)
        else .ok { n with perm := .disabled }
      else .ok { n with perm := .frozen }

/-- Single-node Tree Borrows write transition (`Miri.TreeBorrows.Tree.LocationState.performAccess .Write`):
local writable transitions latch `accessed := true`; protected foreign transitions to `.disabled`
raise `.protectedForeignConflict` iff `n.accessed = true` (`LocationState.lean:144`). -/
def stepNodeOnRangeWrite (activeProtectors : List Nat) (isLocal : Bool)
    (off len : Nat) (n : TreeTagNode) : Except RetagStepErr TreeTagNode :=
  if !rangesOverlap off len n.rangeOffset n.rangeLen then
    .ok n
  else if isLocal then
    match n.perm with
    | .cell => .ok { n with accessed := true }
    | .reservedFrz true =>
      if n.isProtected activeProtectors then .error (.conflictedProtectedChildWrite n.tag)
      else .ok { n with perm := .unique, accessed := true }
    | .reservedFrz false => .ok { n with perm := .unique, accessed := true }
    | .reservedIM => .ok { n with perm := .unique, accessed := true }
    | .unique => .ok { n with accessed := true }
    | .frozen => .error (.ancestorWriteForbidden n.tag)
    | .disabled => .error (.ancestorWriteForbidden n.tag)
  else
    match n.perm with
    | .cell => .ok n
    | .disabled => .ok n
    | .reservedIM =>
      if n.isProtected activeProtectors then .error (.protectedForeignConflict n.tag)
      else .ok n
    | .reservedFrz _ | .unique | .frozen =>
      if n.isProtected activeProtectors then
        if n.accessed then .error (.protectedForeignConflict n.tag)
        else .ok { n with perm := .disabled }
      else .ok { n with perm := .disabled }

theorem stepNodeOnRangeWrite_foreign_protected_conflict
    (activeProtectors : List Nat) (off len : Nat) (n : TreeTagNode)
    (hov : rangesOverlap off len n.rangeOffset n.rangeLen = true)
    (hprot : n.isProtected activeProtectors = true)
    (hacc : n.accessed = true)
    (hperm : n.perm = .reservedFrz false ∨ n.perm = .reservedFrz true ∨
      n.perm = .reservedIM ∨ n.perm = .unique ∨ n.perm = .frozen) :
    stepNodeOnRangeWrite activeProtectors false off len n =
      .error (.protectedForeignConflict n.tag) := by
  rcases hperm with h | h | h | h | h <;>
    simp [stepNodeOnRangeWrite, hov, hprot, hacc, h]

/-- Unaccessed (`accessed = false`) protected foreign nodes disable silently on foreign writes
without triggering `ProtectedDisabled` UB (`Miri.TreeBorrows.Tree.LocationState.performAccess`,
`LocationState.lean:144`). -/
theorem stepNodeOnRangeWrite_unaccessed_protected_foreign_disables_without_ub
    (activeProtectors : List Nat) (off len : Nat) (n : TreeTagNode)
    (hov : rangesOverlap off len n.rangeOffset n.rangeLen = true)
    (hprot : n.isProtected activeProtectors = true)
    (hunacc : n.accessed = false)
    (hperm : n.perm = .reservedFrz false ∨ n.perm = .reservedFrz true ∨ n.perm = .frozen) :
    stepNodeOnRangeWrite activeProtectors false off len n =
      .ok { n with perm := .disabled } := by
  rcases hperm with h | h | h <;>
    simp [stepNodeOnRangeWrite, hov, hprot, hunacc, h]

/-- Fundamental per-node composition law: read followed by write equals direct write on every
foreign node and every non-`.disabled` local node (for arbitrary `accessed : Bool`). -/
theorem stepNode_read_then_childWrite_eq_parentWrite
    (activeProtectors : List Nat) (isLocal : Bool) (off len : Nat) (n : TreeTagNode)
    (hnotDisabledLocal : ¬ (isLocal = true ∧ n.perm = .disabled)) :
    (stepNodeOnRangeRead activeProtectors isLocal off len n >>=
      stepNodeOnRangeWrite activeProtectors isLocal off len) =
      stepNodeOnRangeWrite activeProtectors isLocal off len n := by
  rcases n with ⟨tag, par, perm, rOff, rLen, prot, acc⟩
  unfold stepNodeOnRangeRead stepNodeOnRangeWrite
  cases hov : rangesOverlap off len rOff rLen with
  | false => simp [Bind.bind, Except.bind, hov]
  | true =>
    cases isLocal with
    | true =>
      cases perm with
      | disabled => exact False.elim (hnotDisabledLocal ⟨rfl, rfl⟩)
      | cell => simp [Bind.bind, Except.bind, hov]
      | frozen => simp [Bind.bind, Except.bind, hov]
      | unique => simp [Bind.bind, Except.bind, hov]
      | reservedIM => simp [Bind.bind, Except.bind, hov]
      | reservedFrz c =>
        cases c with
        | false => simp [Bind.bind, Except.bind, hov]
        | true =>
          cases hprot : (TreeTagNode.mk tag par (.reservedFrz true) rOff rLen prot true).isProtected activeProtectors <;>
            simp [Bind.bind, Except.bind, hov, TreeTagNode.isProtected] at hprot ⊢ <;>
            simp [hprot]
    | false =>
      cases perm with
      | cell => simp [Bind.bind, Except.bind, hov]
      | frozen =>
        cases acc <;> cases hprot : (TreeTagNode.mk tag par .frozen rOff rLen prot false).isProtected activeProtectors <;>
          simp [Bind.bind, Except.bind, hov, TreeTagNode.isProtected] at hprot ⊢ <;>
          simp [hprot]
      | disabled => simp [Bind.bind, Except.bind, hov]
      | reservedIM =>
        cases hprot : (TreeTagNode.mk tag par .reservedIM rOff rLen prot acc).isProtected activeProtectors <;>
          simp [Bind.bind, Except.bind, hov, TreeTagNode.isProtected] at hprot ⊢ <;>
          simp [hprot]
      | reservedFrz c =>
        cases acc <;> cases hprot : (TreeTagNode.mk tag par (.reservedFrz true) rOff rLen prot false).isProtected activeProtectors <;>
          simp [Bind.bind, Except.bind, TreeTagNode.isProtected] at hprot ⊢ <;>
          simp [hov, hprot]
      | unique =>
        cases acc <;> cases hprot : (TreeTagNode.mk tag par .unique rOff rLen prot false).isProtected activeProtectors <;>
          simp [Bind.bind, Except.bind, TreeTagNode.isProtected] at hprot ⊢ <;>
          simp [hov, hprot]

/-- Unconditional success-path per-node equivalence (holds even on `.disabled` local nodes, where both fail). -/
theorem stepNode_read_then_write_ok_iff
    (activeProtectors : List Nat) (isLocal : Bool) (off len : Nat) (n n' : TreeTagNode) :
    (stepNodeOnRangeRead activeProtectors isLocal off len n >>=
      stepNodeOnRangeWrite activeProtectors isLocal off len) = .ok n' ↔
      stepNodeOnRangeWrite activeProtectors isLocal off len n = .ok n' := by
  by_cases h : isLocal = true ∧ n.perm = .disabled
  · rcases h with ⟨rfl, hdis⟩
    unfold stepNodeOnRangeRead stepNodeOnRangeWrite
    cases hov : rangesOverlap off len n.rangeOffset n.rangeLen with
    | false => simp [Bind.bind, Except.bind, hov]
    | true => simp [Bind.bind, Except.bind, hdis]
  · rw [stepNode_read_then_childWrite_eq_parentWrite activeProtectors isLocal off len n h]

/-- Helper: check every node in `xs` under `f` (preserving order and failing on first error). -/
def checkNodesM (f : TreeTagNode → Except RetagStepErr TreeTagNode) :
    List TreeTagNode → Except RetagStepErr Unit
  | [] => .ok ()
  | n :: rest =>
    match f n with
    | .error e => .error e
    | .ok _ => checkNodesM f rest

/-- Helper: map every node in `xs` under `f` (preserving list order, failing on first error). -/
def mapNodesM (f : TreeTagNode → Except RetagStepErr TreeTagNode) :
    List TreeTagNode → Except RetagStepErr (List TreeTagNode)
  | [] => .ok []
  | n :: rest =>
    match f n with
    | .error e => .error e
    | .ok n' =>
      match mapNodesM f rest with
      | .error e => .error e
      | .ok rest' => .ok (n' :: rest')

/-- Constructive pairwise relation on equal-length lists (`0` axioms). -/
inductive ListRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : ListRel R [] []
  | cons {x y xs ys} : R x y → ListRel R xs ys → ListRel R (x :: xs) (y :: ys)

theorem ListRel.exists_of_mem_left {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : ListRel R xs ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys, R x y := by
  induction h with
  | nil => cases hx
  | cons hxy _ ih =>
    cases hx with
    | head => exact ⟨_, List.mem_cons_self .., hxy⟩
    | tail _ hmem =>
      rcases ih hmem with ⟨y, hy, hr⟩
      exact ⟨y, List.mem_cons_of_mem _ hy, hr⟩

theorem ListRel.exists_of_mem_right {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : ListRel R xs ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, R x y := by
  induction h with
  | nil => cases hy
  | cons hxy _ ih =>
    cases hy with
    | head => exact ⟨_, List.mem_cons_self .., hxy⟩
    | tail _ hmem =>
      rcases ih hmem with ⟨x, hx, hr⟩
      exact ⟨x, List.mem_cons_of_mem _ hx, hr⟩

theorem mapNodesM_ok_iff (f : TreeTagNode → Except RetagStepErr TreeTagNode)
    (xs ys : List TreeTagNode) :
    mapNodesM f xs = .ok ys ↔ ListRel (fun x y => f x = .ok y) xs ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact ⟨fun _ => ListRel.nil, fun _ => rfl⟩
    | cons _ _ =>
      constructor
      · intro h; cases h
      · intro h; cases h
  | cons x rest ih =>
    simp only [mapNodesM]
    cases hfx : f x with
    | error e =>
      constructor
      · intro h; cases h
      · intro h; cases h with | cons h1 _ => rw [hfx] at h1; cases h1
    | ok x' =>
      cases hm : mapNodesM f rest with
      | error e =>
        constructor
        · intro h; cases h
        · intro h
          cases h with
          | cons _ hrest =>
            have := (ih _).2 hrest
            rw [hm] at this; cases this
      | ok rest' =>
        constructor
        · intro h
          injection h with hy
          subst hy
          exact ListRel.cons hfx ((ih rest').1 hm)
        · intro h
          cases h with
          | cons hx hrest =>
            rw [hfx] at hx
            injection hx with hx'
            subst hx'
            have h' := (ih _).2 hrest
            rw [hm] at h'
            injection h' with hr
            subst hr; rfl

theorem checkNodesM_ok_iff (f : TreeTagNode → Except RetagStepErr TreeTagNode)
    (xs : List TreeTagNode) :
    checkNodesM f xs = .ok () ↔ ∀ n ∈ xs, ∃ n', f n = .ok n' := by
  induction xs with
  | nil => simp [checkNodesM]
  | cons x rest ih =>
    simp only [checkNodesM]
    cases hfx : f x with
    | error e =>
      constructor
      · intro h; cases h
      · intro h
        rcases h x (List.mem_cons_self ..) with ⟨_, hx⟩
        rw [hfx] at hx; cases hx
    | ok x' =>
      rw [ih]
      constructor
      · intro h n hn
        cases hn with
        | head => exact ⟨x', hfx⟩
        | tail _ hmem => exact h n hmem
      · intro h n hn
        exact h n (List.mem_cons_of_mem _ hn)

theorem mapNodesM_preserves_shape (f : TreeTagNode → Except RetagStepErr TreeTagNode)
    (hshape : ∀ n n', f n = .ok n' → n'.tag = n.tag ∧ n'.parentTag = n.parentTag)
    {xs ys : List TreeTagNode} (h : mapNodesM f xs = .ok ys) :
    ys.length = xs.length ∧
    (∀ t, (findNode? ys t).map (fun n => (n.tag, n.parentTag)) =
      (findNode? xs t).map (fun n => (n.tag, n.parentTag))) := by
  have hrel := (mapNodesM_ok_iff f xs ys).1 h
  clear h
  induction hrel with
  | nil => exact ⟨rfl, fun _ => rfl⟩
  | @cons x y xs' ys' hxy _ ih =>
    rcases hshape x y hxy with ⟨htag, hpar⟩
    refine ⟨by simp [ih.1], ?_⟩
    intro t
    simp only [findNode?, List.find?, htag]
    cases x.tag == t with
    | true => simp [htag, hpar]
    | false => exact ih.2 t

theorem mapNodesM_eq_of_check_and_ok (f : TreeTagNode → Except RetagStepErr TreeTagNode)
    (xs : List TreeTagNode) (hall : ∀ n ∈ xs, ∃ n', f n = .ok n') :
    ∃ ys, mapNodesM f xs = .ok ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x rest ih =>
    rcases hall x (List.mem_cons_self ..) with ⟨x', hx'⟩
    rcases ih (fun n hn => hall n (List.mem_cons_of_mem _ hn)) with ⟨ys, hys⟩
    exact ⟨x' :: ys, by simp [mapNodesM, hx', hys]⟩

/-- Model 1 (Two-Pass): initial reborrow read pass + child creation + (for `.writableChildWrite`)
second pass performing an implicit write through the newly minted child tag. Matches upstream
`RetagPipeline.accessTreeForReborrow`: ZST (`rangeLen == 0`) performs zero parent accesses (even if
the parent is `.disabled` elsewhere), `allocReadOnly` is rejected before any tree access on non-zero
`.writableChildWrite`, and overlapping `.disabled` parents are caught by the per-range tree step. -/
def execFnEntryMutRetag (w : FnEntryBorrowWorld) (parentTag rangeOffset rangeLen : Nat)
    (policy : FnEntryRetagPolicy) (requireInitOnImplicitWrite : Bool := false) :
    Except RetagStepErr (FnEntryBorrowWorld × Nat) :=
  match policy with
  | .skipRetag => .ok (w, parentTag)
  | .rustcNoWritable | .writableChildWrite =>
    match findNode? w.nodes parentTag with
    | none => .error (.missingParentTag parentTag)
    | some _ =>
      let childTag := w.nextTag
      let protId := w.nextProtector
      let activeProtectors' := protId :: w.activeProtectors
      let childBase : TreeTagNode := {
        tag := childTag
        parentTag := some parentTag
        perm := .reservedFrz false
        rangeOffset := rangeOffset
        rangeLen := rangeLen
        protector := some protId
        accessed := true
      }
      if rangeLen == 0 then
        .ok ({ w with
          nodes := childBase :: w.nodes
          activeProtectors := activeProtectors'
          nextTag := childTag + 1
          nextProtector := protId + 1 }, childTag)
      else
        let ancestors := ancestorPathTags w.nodes parentTag
        match policy with
        | .rustcNoWritable =>
          match mapNodesM (fun n => stepNodeOnRangeRead w.activeProtectors (ancestors.contains n.tag) rangeOffset rangeLen n) w.nodes with
          | .error e => .error e
          | .ok nodesAfterRead =>
            .ok ({ w with
              nodes := childBase :: nodesAfterRead
              activeProtectors := activeProtectors'
              nextTag := childTag + 1
              nextProtector := protId + 1 }, childTag)
        | .writableChildWrite =>
          if w.allocReadOnly then
            .error .writeToReadOnlyAlloc
          else if requireInitOnImplicitWrite && !w.pointeeInitialized then
            .error .uninitializedPointeeWrite
          else
            match mapNodesM (fun n => stepNodeOnRangeRead w.activeProtectors (ancestors.contains n.tag) rangeOffset rangeLen n) w.nodes with
            | .error e => .error e
            | .ok nodesAfterRead =>
              let nodesWithChild := childBase :: nodesAfterRead
              let childAncestors := ancestorPathTags nodesWithChild childTag
              match mapNodesM (fun n => stepNodeOnRangeWrite activeProtectors' (childAncestors.contains n.tag) rangeOffset rangeLen n) nodesWithChild with
              | .error e => .error e
              | .ok nodesAfterWrite =>
                .ok ({ w with
                  nodes := nodesAfterWrite
                  activeProtectors := activeProtectors'
                  nextTag := childTag + 1
                  nextProtector := protId + 1 }, childTag)
        | .skipRetag => .ok (w, parentTag)

/-- Model 2 (Flat-List Single-Pass Upstream): applies associated read (`.rustcNoWritable`) or
direct write (`.writableChildWrite`) in `w.nodes` list order and mints the child with its initial perm. -/
def execFnEntryMutRetagUpstream (w : FnEntryBorrowWorld) (parentTag rangeOffset rangeLen : Nat)
    (policy : FnEntryRetagPolicy) (requireInitOnImplicitWrite : Bool := false) :
    Except RetagStepErr (FnEntryBorrowWorld × Nat) :=
  match policy with
  | .skipRetag => .ok (w, parentTag)
  | .rustcNoWritable | .writableChildWrite =>
    match findNode? w.nodes parentTag with
    | none => .error (.missingParentTag parentTag)
    | some _ =>
      let childTag := w.nextTag
      let protId := w.nextProtector
      let activeProtectors' := protId :: w.activeProtectors
      let childInitPerm : TreeBorrowPerm :=
        if rangeLen == 0 then .reservedFrz false
        else match policy with
          | .writableChildWrite => .unique
          | _ => .reservedFrz false
      let child : TreeTagNode := {
        tag := childTag
        parentTag := some parentTag
        perm := childInitPerm
        rangeOffset := rangeOffset
        rangeLen := rangeLen
        protector := some protId
        accessed := true
      }
      if rangeLen == 0 then
        .ok ({ w with
          nodes := child :: w.nodes
          activeProtectors := activeProtectors'
          nextTag := childTag + 1
          nextProtector := protId + 1 }, childTag)
      else
        let ancestors := ancestorPathTags w.nodes parentTag
        match policy with
        | .rustcNoWritable =>
          match mapNodesM (fun n => stepNodeOnRangeRead w.activeProtectors (ancestors.contains n.tag) rangeOffset rangeLen n) w.nodes with
          | .error e => .error e
          | .ok nodes' =>
            .ok ({ w with
              nodes := child :: nodes'
              activeProtectors := activeProtectors'
              nextTag := childTag + 1
              nextProtector := protId + 1 }, childTag)
        | .writableChildWrite =>
          if w.allocReadOnly then
            .error .writeToReadOnlyAlloc
          else if requireInitOnImplicitWrite && !w.pointeeInitialized then
            .error .uninitializedPointeeWrite
          else
            match mapNodesM (fun n => stepNodeOnRangeWrite w.activeProtectors (ancestors.contains n.tag) rangeOffset rangeLen n) w.nodes with
            | .error e => .error e
            | .ok nodes' =>
              .ok ({ w with
                nodes := child :: nodes'
                activeProtectors := activeProtectors'
                nextTag := childTag + 1
                nextProtector := protId + 1 }, childTag)
        | .skipRetag => .ok (w, parentTag)

/-- Check ancestors in bottom-up `ancestorPathNodes` order (`TraversalTree.traverse`: `localEvents`),
then foreign nodes (`foreignEvents`), matching Miri's `Traversal.lean:45-53, 102-118`. -/
def checkAncestorPathM (w : FnEntryBorrowWorld) (parentTag : Nat)
    (stepLocal : TreeTagNode → Except RetagStepErr TreeTagNode) :
    Except RetagStepErr Unit :=
  checkNodesM stepLocal (ancestorPathNodes w.nodes parentTag)

/-- Flat-list ancestor checker (root-first on root-first node lists), used to contrast with
bottom-up `checkAncestorPathM`. -/
def checkAncestorsFlatM (w : FnEntryBorrowWorld) (parentTag : Nat)
    (stepLocal : TreeTagNode → Except RetagStepErr TreeTagNode) :
    Except RetagStepErr Unit :=
  let ancestors := ancestorPathTags w.nodes parentTag
  checkNodesM stepLocal (w.nodes.filter (fun n => ancestors.contains n.tag))

/-- Model 3 (Bottom-Up Source-Order `TraversalTree.traverse`): visits `ancestorPathNodes`
bottom-up (`start -> parent -> ... -> root`) BEFORE foreign nodes, then updates `w.nodes`. -/
def execFnEntryMutRetagSourceOrder (w : FnEntryBorrowWorld) (parentTag rangeOffset rangeLen : Nat)
    (policy : FnEntryRetagPolicy) (requireInitOnImplicitWrite : Bool := false) :
    Except RetagStepErr (FnEntryBorrowWorld × Nat) :=
  match policy with
  | .skipRetag => .ok (w, parentTag)
  | .rustcNoWritable | .writableChildWrite =>
    match findNode? w.nodes parentTag with
    | none => .error (.missingParentTag parentTag)
    | some _ =>
      let childTag := w.nextTag
      let protId := w.nextProtector
      let activeProtectors' := protId :: w.activeProtectors
      let childInitPerm : TreeBorrowPerm :=
        if rangeLen == 0 then .reservedFrz false
        else match policy with
          | .writableChildWrite => .unique
          | _ => .reservedFrz false
      let child : TreeTagNode := {
        tag := childTag
        parentTag := some parentTag
        perm := childInitPerm
        rangeOffset := rangeOffset
        rangeLen := rangeLen
        protector := some protId
        accessed := true
      }
      if rangeLen == 0 then
        .ok ({ w with
          nodes := child :: w.nodes
          activeProtectors := activeProtectors'
          nextTag := childTag + 1
          nextProtector := protId + 1 }, childTag)
      else
        let ancestors := ancestorPathTags w.nodes parentTag
        let foreignNodes := w.nodes.filter (fun n => !ancestors.contains n.tag)
        match policy with
        | .rustcNoWritable =>
          match checkAncestorPathM w parentTag
              (stepNodeOnRangeRead w.activeProtectors true rangeOffset rangeLen) with
          | .error e => .error e
          | .ok () =>
            match checkNodesM (stepNodeOnRangeRead w.activeProtectors false rangeOffset rangeLen) foreignNodes with
            | .error e => .error e
            | .ok () =>
              match mapNodesM (fun n => stepNodeOnRangeRead w.activeProtectors (ancestors.contains n.tag) rangeOffset rangeLen n) w.nodes with
              | .error e => .error e
              | .ok nodes' =>
                .ok ({ w with
                  nodes := child :: nodes'
                  activeProtectors := activeProtectors'
                  nextTag := childTag + 1
                  nextProtector := protId + 1 }, childTag)
        | .writableChildWrite =>
          if w.allocReadOnly then
            .error .writeToReadOnlyAlloc
          else if requireInitOnImplicitWrite && !w.pointeeInitialized then
            .error .uninitializedPointeeWrite
          else
            match checkAncestorPathM w parentTag
                (stepNodeOnRangeWrite w.activeProtectors true rangeOffset rangeLen) with
            | .error e => .error e
            | .ok () =>
              match checkNodesM (stepNodeOnRangeWrite w.activeProtectors false rangeOffset rangeLen) foreignNodes with
              | .error e => .error e
              | .ok () =>
                match mapNodesM (fun n => stepNodeOnRangeWrite w.activeProtectors (ancestors.contains n.tag) rangeOffset rangeLen n) w.nodes with
                | .error e => .error e
                | .ok nodes' =>
                  .ok ({ w with
                    nodes := child :: nodes'
                    activeProtectors := activeProtectors'
                    nextTag := childTag + 1
                    nextProtector := protId + 1 }, childTag)
        | .skipRetag => .ok (w, parentTag)

/-- Upstream `LocationState.skipIfKnownNoop` (`LocationState.lean:76-88`, `NormalTree.lean:62-68`):
on a foreign access overlapping `[off, off + len)`, a `.disabled` node (Read or Write) or a
`.frozen` node (Read only) returns `SkipSelfAndChildren`, pruning itself and every descendant. -/
def foreignNodeSkipsSubtree (isWrite : Bool) (off len : Nat) (n : TreeTagNode) : Bool :=
  rangesOverlap off len n.rangeOffset n.rangeLen &&
    (n.perm == .disabled || (!isWrite && n.perm == .frozen))

/-- Whether foreign node `n` sits strictly underneath a skipped foreign ancestor on `[off, off + len)`
(`TraversalTree.foreignPostorder` with `NormalTreeState.skippedForeignNodes`). -/
def isPrunedForeignNode (nodes : List TreeTagNode) (ancestors : List Nat)
    (isWrite : Bool) (off len : Nat) (n : TreeTagNode) : Bool :=
  !ancestors.contains n.tag &&
    (ancestorPathTags nodes n.tag).tail.any fun t =>
      !ancestors.contains t &&
        match findNode? nodes t with
        | some a => foreignNodeSkipsSubtree isWrite off len a
        | none => false

/-- Model 4 (`SkipSelfAndChildren`-Pruned Bottom-Up Source-Order): mirrors pinned
`Miri.TreeBorrows.Tree.NormalTreeState.performAccess` (`NormalTree.lean:107-112`), visiting
`ancestorPathNodes` bottom-up first and pruning foreign subtrees rooted at a `.disabled` node
(or a `.frozen` node on Read) so descendants beneath a skipped foreign ancestor are neither checked
nor mutated. -/
def execFnEntryMutRetagPrunedSourceOrder (w : FnEntryBorrowWorld)
    (parentTag rangeOffset rangeLen : Nat)
    (policy : FnEntryRetagPolicy) (requireInitOnImplicitWrite : Bool := false) :
    Except RetagStepErr (FnEntryBorrowWorld × Nat) :=
  match policy with
  | .skipRetag => .ok (w, parentTag)
  | .rustcNoWritable | .writableChildWrite =>
    match findNode? w.nodes parentTag with
    | none => .error (.missingParentTag parentTag)
    | some _ =>
      let childTag := w.nextTag
      let protId := w.nextProtector
      let activeProtectors' := protId :: w.activeProtectors
      let childInitPerm : TreeBorrowPerm :=
        if rangeLen == 0 then .reservedFrz false
        else match policy with
          | .writableChildWrite => .unique
          | _ => .reservedFrz false
      let child : TreeTagNode := {
        tag := childTag
        parentTag := some parentTag
        perm := childInitPerm
        rangeOffset := rangeOffset
        rangeLen := rangeLen
        protector := some protId
        accessed := true
      }
      if rangeLen == 0 then
        .ok ({ w with
          nodes := child :: w.nodes
          activeProtectors := activeProtectors'
          nextTag := childTag + 1
          nextProtector := protId + 1 }, childTag)
      else
        let ancestors := ancestorPathTags w.nodes parentTag
        match policy with
        | .rustcNoWritable =>
          let stepPruned (n : TreeTagNode) : Except RetagStepErr TreeTagNode :=
            if ancestors.contains n.tag then
              stepNodeOnRangeRead w.activeProtectors true rangeOffset rangeLen n
            else if isPrunedForeignNode w.nodes ancestors false rangeOffset rangeLen n then
              .ok n
            else
              stepNodeOnRangeRead w.activeProtectors false rangeOffset rangeLen n
          let activeForeign := w.nodes.filter (fun n =>
            !ancestors.contains n.tag &&
              !isPrunedForeignNode w.nodes ancestors false rangeOffset rangeLen n)
          match checkAncestorPathM w parentTag
              (stepNodeOnRangeRead w.activeProtectors true rangeOffset rangeLen) with
          | .error e => .error e
          | .ok () =>
            match checkNodesM (stepNodeOnRangeRead w.activeProtectors false rangeOffset rangeLen) activeForeign with
            | .error e => .error e
            | .ok () =>
              match mapNodesM stepPruned w.nodes with
              | .error e => .error e
              | .ok nodes' =>
                .ok ({ w with
                  nodes := child :: nodes'
                  activeProtectors := activeProtectors'
                  nextTag := childTag + 1
                  nextProtector := protId + 1 }, childTag)
        | .writableChildWrite =>
          if w.allocReadOnly then
            .error .writeToReadOnlyAlloc
          else if requireInitOnImplicitWrite && !w.pointeeInitialized then
            .error .uninitializedPointeeWrite
          else
            let stepPruned (n : TreeTagNode) : Except RetagStepErr TreeTagNode :=
              if ancestors.contains n.tag then
                stepNodeOnRangeWrite w.activeProtectors true rangeOffset rangeLen n
              else if isPrunedForeignNode w.nodes ancestors true rangeOffset rangeLen n then
                .ok n
              else
                stepNodeOnRangeWrite w.activeProtectors false rangeOffset rangeLen n
            let activeForeign := w.nodes.filter (fun n =>
              !ancestors.contains n.tag &&
                !isPrunedForeignNode w.nodes ancestors true rangeOffset rangeLen n)
            match checkAncestorPathM w parentTag
                (stepNodeOnRangeWrite w.activeProtectors true rangeOffset rangeLen) with
            | .error e => .error e
            | .ok () =>
              match checkNodesM (stepNodeOnRangeWrite w.activeProtectors false rangeOffset rangeLen) activeForeign with
              | .error e => .error e
              | .ok () =>
                match mapNodesM stepPruned w.nodes with
                | .error e => .error e
                | .ok nodes' =>
                  .ok ({ w with
                    nodes := child :: nodes'
                    activeProtectors := activeProtectors'
                    nextTag := childTag + 1
                    nextProtector := protId + 1 }, childTag)
        | .skipRetag => .ok (w, parentTag)

/-- Explicit child write through `writerTag` in a `FnEntryBorrowWorld` (used for post-retag activation and parent-write tests). -/
def execWorldRangeWrite (w : FnEntryBorrowWorld) (writerTag rangeOffset rangeLen : Nat) :
    Except RetagStepErr FnEntryBorrowWorld :=
  if rangeLen == 0 then .ok w
  else
    let ancestors := ancestorPathTags w.nodes writerTag
    match checkAncestorPathM w writerTag
        (stepNodeOnRangeWrite w.activeProtectors true rangeOffset rangeLen) with
    | .error e => .error e
    | .ok () =>
      let foreignNodes := w.nodes.filter (fun n => !ancestors.contains n.tag)
      match checkNodesM (stepNodeOnRangeWrite w.activeProtectors false rangeOffset rangeLen) foreignNodes with
      | .error e => .error e
      | .ok () =>
        match mapNodesM (fun n => stepNodeOnRangeWrite w.activeProtectors (ancestors.contains n.tag) rangeOffset rangeLen n) w.nodes with
        | .error e => .error e
        | .ok nodes' => .ok { w with nodes := nodes' }

/-- Explicit range read through `readerTag` in a `FnEntryBorrowWorld` (used to latch `conflicted := true`). -/
def execWorldRangeRead (w : FnEntryBorrowWorld) (readerTag rangeOffset rangeLen : Nat) :
    Except RetagStepErr FnEntryBorrowWorld :=
  if rangeLen == 0 then .ok w
  else
    let ancestors := ancestorPathTags w.nodes readerTag
    match checkAncestorPathM w readerTag
        (stepNodeOnRangeRead w.activeProtectors true rangeOffset rangeLen) with
    | .error e => .error e
    | .ok () =>
      let foreignNodes := w.nodes.filter (fun n => !ancestors.contains n.tag)
      match checkNodesM (stepNodeOnRangeRead w.activeProtectors false rangeOffset rangeLen) foreignNodes with
      | .error e => .error e
      | .ok () =>
        match mapNodesM (fun n => stepNodeOnRangeRead w.activeProtectors (ancestors.contains n.tag) rangeOffset rangeLen n) w.nodes with
        | .error e => .error e
        | .ok nodes' => .ok { w with nodes := nodes' }

theorem fnEntryMutRetag_zst_no_write (w : FnEntryBorrowWorld) (parentTag rangeOffset : Nat)
    (requireInit : Bool) :
    execFnEntryMutRetag w parentTag rangeOffset 0 .writableChildWrite requireInit =
      execFnEntryMutRetag w parentTag rangeOffset 0 .rustcNoWritable requireInit ∧
    execFnEntryMutRetagSourceOrder w parentTag rangeOffset 0 .writableChildWrite requireInit =
      execFnEntryMutRetagSourceOrder w parentTag rangeOffset 0 .rustcNoWritable requireInit := by
  constructor
  · unfold execFnEntryMutRetag
    cases findNode? w.nodes parentTag <;> rfl
  · unfold execFnEntryMutRetagSourceOrder
    cases findNode? w.nodes parentTag <;> rfl

/-- Read-only allocation separation (`RetagPipeline.accessTreeForReborrow`: `writeToReadOnly`): on EVERY
world whose retagged allocation is read-only, a non-zero-sized `writableChildWrite` FnEntry retag through
ANY existing parent tag — EVEN a `.disabled` parent — is rejected with `.writeToReadOnlyAlloc` by all
four models BEFORE any tree access (`RetagPipeline.lean:210-211` precedes `performBorrowAccessRange`). -/
theorem fnEntryMutRetag_readOnlyAlloc_writable_rejected
    (w : FnEntryBorrowWorld) (parentTag rangeOffset rangeLen : Nat) (requireInit : Bool)
    (pNode : TreeTagNode)
    (hro : w.allocReadOnly = true)
    (hparent : findNode? w.nodes parentTag = some pNode)
    (hlen : rangeLen ≠ 0) :
    execFnEntryMutRetag w parentTag rangeOffset rangeLen .writableChildWrite requireInit =
      .error .writeToReadOnlyAlloc ∧
    execFnEntryMutRetagUpstream w parentTag rangeOffset rangeLen .writableChildWrite requireInit =
      .error .writeToReadOnlyAlloc ∧
    execFnEntryMutRetagSourceOrder w parentTag rangeOffset rangeLen .writableChildWrite requireInit =
      .error .writeToReadOnlyAlloc ∧
    execFnEntryMutRetagPrunedSourceOrder w parentTag rangeOffset rangeLen .writableChildWrite requireInit =
      .error .writeToReadOnlyAlloc := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [execFnEntryMutRetag, hparent, hlen, hro]
  · simp [execFnEntryMutRetagUpstream, hparent, hlen, hro]
  · simp [execFnEntryMutRetagSourceOrder, hparent, hlen, hro]
  · simp [execFnEntryMutRetagPrunedSourceOrder, hparent, hlen, hro]

/-- Disabled-parent range and precedence faithfulness (`RetagPipeline.accessTreeForReborrow`):
1. A ZST reborrow (`rangeLen = 0`) through a `.disabled` parent performs zero parent accesses and
   succeeds in all models (`inside.iterAll` is empty).
2. A disjoint-range reborrow (`[4, 8)` when the parent is `.disabled` only on `[0, 4)`) succeeds in
   all models.
3. An overlapping non-zero `.rustcNoWritable` reborrow through a `.disabled` parent fails with
   `.disabledParentTag parentTag`.
4. An overlapping non-zero `.writableChildWrite` reborrow through a `.disabled` parent on a read-only
   allocation fails with `.writeToReadOnlyAlloc` (not `.disabledParentTag`). -/
theorem fnEntryMutRetag_disabledParent_zst_disjoint_and_readOnly_precedence :
    let wDis : FnEntryBorrowWorld := {
      nodes := [⟨0, none, .unique, 0, 8, none, true⟩, ⟨1, some 0, .disabled, 0, 4, none, true⟩]
      activeProtectors := []
      nextTag := 2
      nextProtector := 10
    }
    let wDisRo : FnEntryBorrowWorld := { wDis with allocReadOnly := true }
    (execFnEntryMutRetagSourceOrder wDis 1 0 0 .rustcNoWritable).isOk = true ∧
    (execFnEntryMutRetagSourceOrder wDis 1 0 0 .writableChildWrite).isOk = true ∧
    (execFnEntryMutRetagSourceOrder wDis 1 4 4 .rustcNoWritable).isOk = true ∧
    (execFnEntryMutRetagSourceOrder wDis 1 4 4 .writableChildWrite).isOk = true ∧
    execFnEntryMutRetagSourceOrder wDis 1 0 4 .rustcNoWritable = .error (.disabledParentTag 1) ∧
    execFnEntryMutRetagSourceOrder wDis 1 0 4 .writableChildWrite = .error (.ancestorWriteForbidden 1) ∧
    execFnEntryMutRetagSourceOrder wDisRo 1 0 4 .writableChildWrite = .error .writeToReadOnlyAlloc := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `rustcNoWritable` performs a READ reborrow and therefore never consults allocation mutability:
flipping `allocReadOnly` changes neither success / failure nor the produced nodes, protectors, fresh
counters, or child tag of the source-order model. Together with
`fnEntryMutRetag_readOnlyAlloc_writable_rejected`, `#[rustc_no_writable]` is exactly what makes a
protected `&mut` reborrow into read-only memory acceptable. -/
theorem sourceOrder_rustcNoWritable_ignores_allocReadOnly
    (w : FnEntryBorrowWorld) (ro : Bool) (parentTag rangeOffset rangeLen : Nat) (requireInit : Bool) :
    (execFnEntryMutRetagSourceOrder { w with allocReadOnly := ro } parentTag rangeOffset rangeLen
        .rustcNoWritable requireInit).map
      (fun r => (r.1.nodes, r.1.activeProtectors, r.1.nextTag, r.1.nextProtector, r.2)) =
    (execFnEntryMutRetagSourceOrder w parentTag rangeOffset rangeLen .rustcNoWritable requireInit).map
      (fun r => (r.1.nodes, r.1.activeProtectors, r.1.nextTag, r.1.nextProtector, r.2)) := by
  unfold execFnEntryMutRetagSourceOrder checkAncestorPathM
  dsimp only
  cases findNode? w.nodes parentTag with
  | none => rfl
  | some _ =>
    dsimp only
    cases (rangeLen == 0) with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases checkNodesM (stepNodeOnRangeRead w.activeProtectors true rangeOffset rangeLen)
          (ancestorPathNodes w.nodes parentTag) with
      | error e => rfl
      | ok u1 =>
        cases u1
        dsimp only
        cases checkNodesM (stepNodeOnRangeRead w.activeProtectors false rangeOffset rangeLen)
            (w.nodes.filter (fun n => !(ancestorPathTags w.nodes parentTag).contains n.tag)) with
        | error e => rfl
        | ok u2 =>
          cases u2
          dsimp only
          cases mapNodesM (fun n => stepNodeOnRangeRead w.activeProtectors
              ((ancestorPathTags w.nodes parentTag).contains n.tag) rangeOffset rangeLen n) w.nodes with
          | error e => rfl
          | ok nodes' => rfl

theorem execFnEntryMutRetag_eq_upstream_when_no_implicitWrite
    (w : FnEntryBorrowWorld) (parentTag rangeOffset rangeLen : Nat) (requireInit : Bool) :
    execFnEntryMutRetag w parentTag rangeOffset rangeLen .rustcNoWritable requireInit =
      execFnEntryMutRetagUpstream w parentTag rangeOffset rangeLen .rustcNoWritable requireInit := by
  unfold execFnEntryMutRetag execFnEntryMutRetagUpstream
  cases findNode? w.nodes parentTag with
  | none => rfl
  | some _ =>
    cases hlen : (rangeLen == 0) with
    | true => simp
    | false => simp only [Bool.false_eq_true, ↓reduceIte]

/-- Standard two-branch borrow world (`root 0 -> parent 1` and sibling `2`, e.g. `.frozen` reader). -/
def mkTwoBranchWorld (parentPerm siblingPerm : TreeBorrowPerm)
    (siblingProt : Option Nat := none) (pointeeInitialized : Bool := true) : FnEntryBorrowWorld where
  nodes := [
    ⟨0, none, .unique, 0, 4, none, true⟩,
    ⟨1, some 0, parentPerm, 0, 4, none, true⟩,
    ⟨2, some 0, siblingPerm, 0, 4, siblingProt, true⟩
  ]
  activeProtectors := match siblingProt with | some p => [p] | none => []
  nextTag := 3
  nextProtector := 10
  pointeeInitialized := pointeeInitialized

theorem execFnEntryMutRetag_mkTwoBranch_eq_upstream
    (siblingPerm : TreeBorrowPerm) (siblingProt : Option Nat)
    (pointeeInitialized : Bool) (policy : FnEntryRetagPolicy) (requireInit : Bool) :
    execFnEntryMutRetag (mkTwoBranchWorld .unique siblingPerm siblingProt pointeeInitialized)
      1 0 4 policy requireInit =
      execFnEntryMutRetagUpstream (mkTwoBranchWorld .unique siblingPerm siblingProt pointeeInitialized)
        1 0 4 policy requireInit := by
  cases policy with
  | skipRetag => rfl
  | rustcNoWritable =>
    exact execFnEntryMutRetag_eq_upstream_when_no_implicitWrite _ 1 0 4 requireInit
  | writableChildWrite =>
    cases pointeeInitialized <;> cases requireInit
    · cases siblingProt with
      | none => cases siblingPerm <;> rfl
      | some p =>
        cases siblingPerm <;>
          simp [mkTwoBranchWorld, execFnEntryMutRetag, execFnEntryMutRetagUpstream,
            findNode?, ancestorPathTags, ancestorPathTagsAux, mapNodesM,
            stepNodeOnRangeRead, stepNodeOnRangeWrite, rangesOverlap, TreeTagNode.isProtected]
    · rfl
    · cases siblingProt with
      | none => cases siblingPerm <;> rfl
      | some p =>
        cases siblingPerm <;>
          simp [mkTwoBranchWorld, execFnEntryMutRetag, execFnEntryMutRetagUpstream,
            findNode?, ancestorPathTags, ancestorPathTagsAux, mapNodesM,
            stepNodeOnRangeRead, stepNodeOnRangeWrite, rangesOverlap, TreeTagNode.isProtected]
    · cases siblingProt with
      | none => cases siblingPerm <;> rfl
      | some p =>
        cases siblingPerm <;>
          simp [mkTwoBranchWorld, execFnEntryMutRetag, execFnEntryMutRetagUpstream,
            findNode?, ancestorPathTags, ancestorPathTagsAux, mapNodesM,
            stepNodeOnRangeRead, stepNodeOnRangeWrite, rangesOverlap, TreeTagNode.isProtected]

/-- `rustcNoWritable` preserves an uninitialized pointee and a `.frozen` sibling,
whereas `writableChildWrite` faults on `requireInit = true` and disables the `.frozen` sibling. -/
theorem rustcNoWritable_preserves_uninit_and_frozen_sibling :
    let wUninit := mkTwoBranchWorld .unique .frozen none false
    let wInit := mkTwoBranchWorld .unique .frozen none true
    (∃ w' childTag,
      execFnEntryMutRetagSourceOrder wUninit 1 0 4 .rustcNoWritable true = .ok (w', childTag) ∧
      (findNode? w'.nodes 2).map (·.perm) = some .frozen ∧
      (findNode? w'.nodes childTag).map (·.perm) = some (.reservedFrz false)) ∧
    execFnEntryMutRetagSourceOrder wUninit 1 0 4 .writableChildWrite true =
      .error .uninitializedPointeeWrite ∧
    (∃ w' childTag,
      execFnEntryMutRetagSourceOrder wInit 1 0 4 .writableChildWrite true = .ok (w', childTag) ∧
      (findNode? w'.nodes 2).map (·.perm) = some .disabled ∧
      (findNode? w'.nodes childTag).map (·.perm) = some .unique) := by
  refine ⟨⟨_, 3, rfl, rfl, rfl⟩, rfl, ⟨_, 3, rfl, rfl, rfl⟩⟩

/-- Under `rustcNoWritable`, a subsequent foreign read latches `conflicted := true` on the protected
child (`ReservedFrz true`), causing a later child write to fault with `.conflictedProtectedChildWrite`. -/
theorem rustcNoWritable_foreignRead_latches_conflicted :
    let w0 := mkTwoBranchWorld .unique .frozen none true
    match execFnEntryMutRetagSourceOrder w0 1 0 4 .rustcNoWritable false with
    | .ok (w1, childTag) =>
      match execWorldRangeRead w1 2 0 4 with
      | .ok w2 =>
        (findNode? w2.nodes childTag).map (·.perm) = some (.reservedFrz true) ∧
        execWorldRangeWrite w2 childTag 0 4 = .error (.conflictedProtectedChildWrite childTag)
      | .error _ => False
    | .error _ => False :=
  ⟨rfl, rfl⟩

/-- Under `rustcNoWritable`, a subsequent write through the parent tag faults with
`.protectedForeignConflict` on the protected child. -/
theorem rustcNoWritable_parentWrite_faults_on_protected_child :
    let w0 := mkTwoBranchWorld .unique .frozen none true
    match execFnEntryMutRetagSourceOrder w0 1 0 4 .rustcNoWritable false with
    | .ok (w1, childTag) =>
      execWorldRangeWrite w1 1 0 4 = .error (.protectedForeignConflict childTag)
    | .error _ => False :=
  rfl

/-- Diagnostic separation #1: on a `.disabled` grandparent, two-pass Pass 1 reports
`.disabledParentTag` while single-pass upstream reports `.ancestorWriteForbidden`. -/
theorem execFnEntryMutRetag_disabledGrandparent_diverges_from_upstream :
    let w : FnEntryBorrowWorld := {
      nodes := [⟨0, none, .disabled, 0, 4, none, true⟩, ⟨1, some 0, .unique, 0, 4, none, true⟩]
      activeProtectors := []
      nextTag := 2
      nextProtector := 10
    }
    execFnEntryMutRetag w 1 0 4 .writableChildWrite false = .error (.disabledParentTag 0) ∧
    execFnEntryMutRetagUpstream w 1 0 4 .writableChildWrite false = .error (.ancestorWriteForbidden 0) := by
  exact ⟨rfl, rfl⟩

/-- Diagnostic separation #2: on `[⟨1 (.frozen parent)⟩, ⟨5 (protected .unique child)⟩]`,
two-pass Pass 1 passes `.frozen` and fails on foreign child `5` (`.protectedForeignConflict 5`),
whereas single-pass upstream fails on `.frozen` parent `1` (`.ancestorWriteForbidden 1`). -/
theorem execFnEntryMutRetag_frozenParent_protectedChild_diverges_from_upstream :
    let w : FnEntryBorrowWorld := {
      nodes := [
        ⟨1, none, .frozen, 0, 4, none, true⟩,
        ⟨5, some 1, .unique, 0, 4, some 7, true⟩
      ]
      activeProtectors := [7]
      nextTag := 6
      nextProtector := 10
    }
    execFnEntryMutRetag w 1 0 4 .writableChildWrite false = .error (.protectedForeignConflict 5) ∧
    execFnEntryMutRetagUpstream w 1 0 4 .writableChildWrite false = .error (.ancestorWriteForbidden 1) := by
  exact ⟨rfl, rfl⟩

/-- Traversal-order separation #1: on reversed-list `[⟨5 (protected .unique child)⟩, ⟨1 (.frozen parent)⟩]`,
flat-list `execFnEntryMutRetagUpstream` visits foreign child `5` before local parent `1`,
violating `TraversalTree.traverse`, whereas `execFnEntryMutRetagSourceOrder` reports `.ancestorWriteForbidden 1`. -/
theorem execFnEntryMutRetagUpstream_reversedList_violates_traversalOrder :
    let w : FnEntryBorrowWorld := {
      nodes := [
        ⟨5, some 1, .unique, 0, 4, some 7, true⟩,
        ⟨1, none, .frozen, 0, 4, none, true⟩
      ]
      activeProtectors := [7]
      nextTag := 6
      nextProtector := 10
    }
    execFnEntryMutRetagUpstream w 1 0 4 .writableChildWrite false = .error (.protectedForeignConflict 5) ∧
    execFnEntryMutRetagSourceOrder w 1 0 4 .writableChildWrite false = .error (.ancestorWriteForbidden 1) := by
  exact ⟨rfl, rfl⟩

/-- Traversal-order separation #2 (bottom-up `ancestorPathNodes` vs. root-first flat ancestor scan):
on `[⟨1 (.frozen root)⟩, ⟨2 (protected .reservedFrz true child, parent = some 1)⟩]` retagging `parentTag = 2`,
bottom-up `execFnEntryMutRetagSourceOrder` visits `2` first (`.conflictedProtectedChildWrite 2`),
whereas root-first `checkAncestorsFlatM` hits `1` first (`.ancestorWriteForbidden 1`). -/
theorem execFnEntryMutRetagSourceOrder_bottomUp_vs_flatAncestors :
    let w : FnEntryBorrowWorld := {
      nodes := [
        ⟨1, none, .frozen, 0, 4, none, true⟩,
        ⟨2, some 1, .reservedFrz true, 0, 4, some 9, true⟩
      ]
      activeProtectors := [9]
      nextTag := 3
      nextProtector := 10
    }
    (ancestorPathNodes w.nodes 2).head? = some ⟨2, some 1, .reservedFrz true, 0, 4, some 9, true⟩ ∧
    checkAncestorsFlatM w 2 (stepNodeOnRangeWrite w.activeProtectors true 0 4) =
      .error (.ancestorWriteForbidden 1) ∧
    execFnEntryMutRetagSourceOrder w 2 0 4 .writableChildWrite false =
      .error (.conflictedProtectedChildWrite 2) := by
  exact ⟨rfl, rfl, rfl⟩

/-- Well-formedness of borrow-tree tags and fresh allocator counters. -/
structure BorrowTreeTagsWF (w : FnEntryBorrowWorld) : Prop where
  tagsNodup : (w.nodes.map (·.tag)).Nodup
  nextTagFresh : ∀ n ∈ w.nodes, n.tag ≠ w.nextTag
  parentTagsFresh : ∀ n ∈ w.nodes, n.parentTag ≠ some w.nextTag
  nextProtectorFresh : ∀ n ∈ w.nodes, n.protector ≠ some w.nextProtector

/-- Every ancestor node along `parentTag`'s chain is writable on `[rangeOffset, rangeOffset + rangeLen)`. -/
def AncestorsWritableIn (w : FnEntryBorrowWorld) (parentTag rangeOffset rangeLen : Nat) : Prop :=
  ∀ n ∈ w.nodes, (ancestorPathTags w.nodes parentTag).contains n.tag = true →
    ∃ n', stepNodeOnRangeWrite w.activeProtectors true rangeOffset rangeLen n = .ok n'

/-- Foreign nodes have aligned first-error behavior between Pass 1 read and direct write
(e.g., whenever no protected non-unique foreign node precedes a protected unique foreign node). -/
def ForeignReadWriteErrorAligned (w : FnEntryBorrowWorld) (parentTag rangeOffset rangeLen : Nat) : Prop :=
  let anc := ancestorPathTags w.nodes parentTag
  (∀ n ∈ w.nodes, anc.contains n.tag = false →
    ∃ n', stepNodeOnRangeWrite w.activeProtectors false rangeOffset rangeLen n = .ok n') ∨
  (∀ n ∈ w.nodes, anc.contains n.tag = false →
    (stepNodeOnRangeRead w.activeProtectors false rangeOffset rangeLen n).isOk =
      (stepNodeOnRangeWrite w.activeProtectors false rangeOffset rangeLen n).isOk)

private theorem mem_ancestorPathNodes_iff (nodes : List TreeTagNode) (start : Nat) (n : TreeTagNode) :
    n ∈ ancestorPathNodes nodes start ↔
      n ∈ nodes ∧ (ancestorPathTags nodes start).contains n.tag = true := by
  unfold ancestorPathNodes
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨t, ht, hmem⟩
    rw [List.mem_filter] at hmem
    rcases hmem with ⟨hn, hbeq⟩
    have hteq : n.tag = t := eq_of_beq hbeq
    subst hteq
    exact ⟨hn, List.elem_eq_true_of_mem ht⟩
  · rintro ⟨hn, hcon⟩
    have hmem : n.tag ∈ ancestorPathTags nodes start := List.mem_of_elem_eq_true hcon
    refine ⟨n.tag, hmem, ?_⟩
    rw [List.mem_filter]
    exact ⟨hn, beq_self_eq_true n.tag⟩

private theorem check_anc_and_foreign_ok_iff_mapNodesM
    (w : FnEntryBorrowWorld) (parentTag : Nat)
    (step : Bool → TreeTagNode → Except RetagStepErr TreeTagNode) (ys : List TreeTagNode) :
    (checkAncestorPathM w parentTag (step true) = .ok () ∧
      checkNodesM (step false) (w.nodes.filter (fun n => !(ancestorPathTags w.nodes parentTag).contains n.tag)) = .ok () ∧
      mapNodesM (fun n => step ((ancestorPathTags w.nodes parentTag).contains n.tag) n) w.nodes = .ok ys) ↔
    mapNodesM (fun n => step ((ancestorPathTags w.nodes parentTag).contains n.tag) n) w.nodes = .ok ys := by
  constructor
  · intro h; exact h.2.2
  · intro hmap
    refine ⟨?_, ?_, hmap⟩
    · rw [checkAncestorPathM, checkNodesM_ok_iff]
      intro n hn
      rcases (mem_ancestorPathNodes_iff w.nodes parentTag n).1 hn with ⟨hnIn, hanc⟩
      have hrel := (mapNodesM_ok_iff _ _ _).1 hmap
      rcases ListRel.exists_of_mem_left hrel hnIn with ⟨n', _, hfn⟩
      simp only [hanc] at hfn
      exact ⟨n', hfn⟩
    · rw [checkNodesM_ok_iff]
      intro n hn
      rw [List.mem_filter] at hn
      rcases hn with ⟨hnIn, hnot⟩
      have hanc : (ancestorPathTags w.nodes parentTag).contains n.tag = false := by
        cases h : (ancestorPathTags w.nodes parentTag).contains n.tag with
        | false => rfl
        | true => rw [h] at hnot; cases hnot
      have hrel := (mapNodesM_ok_iff _ _ _).1 hmap
      rcases ListRel.exists_of_mem_left hrel hnIn with ⟨n', _, hfn⟩
      simp only [hanc] at hfn
      exact ⟨n', hfn⟩

/-- Zero-WF success-path equivalence between flat-list upstream and bottom-up source-order models. -/
theorem execFnEntryMutRetagUpstream_ok_iff_sourceOrder_ok
    (w : FnEntryBorrowWorld) (parentTag rangeOffset rangeLen : Nat)
    (policy : FnEntryRetagPolicy) (requireInit : Bool)
    (r : FnEntryBorrowWorld × Nat) :
    execFnEntryMutRetagUpstream w parentTag rangeOffset rangeLen policy requireInit = .ok r ↔
      execFnEntryMutRetagSourceOrder w parentTag rangeOffset rangeLen policy requireInit = .ok r := by
  unfold execFnEntryMutRetagUpstream execFnEntryMutRetagSourceOrder
  cases policy with
  | skipRetag => rfl
  | rustcNoWritable =>
    cases findNode? w.nodes parentTag with
    | none => rfl
    | some _ =>
      cases hlen : (rangeLen == 0) with
      | true => simp
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases hm : mapNodesM (fun n => stepNodeOnRangeRead w.activeProtectors ((ancestorPathTags w.nodes parentTag).contains n.tag) rangeOffset rangeLen n) w.nodes with
        | error e =>
          constructor
          · intro h; cases h
          · intro h
            dsimp only at h
            cases hc1 : checkAncestorPathM w parentTag (stepNodeOnRangeRead w.activeProtectors true rangeOffset rangeLen) with
            | error _ => rw [hc1] at h; cases h
            | ok u1 =>
              cases u1
              rw [hc1] at h; simp only at h
              cases hc2 : checkNodesM (stepNodeOnRangeRead w.activeProtectors false rangeOffset rangeLen)
                  (w.nodes.filter (fun n => !(ancestorPathTags w.nodes parentTag).contains n.tag)) with
              | error _ => rw [hc2] at h; cases h
              | ok u2 => cases u2; rw [hc2] at h; simp only at h; cases h
        | ok nodes' =>
          have hboth := (check_anc_and_foreign_ok_iff_mapNodesM w parentTag
            (fun isLoc n => stepNodeOnRangeRead w.activeProtectors isLoc rangeOffset rangeLen n) nodes').2 hm
          simp only [hboth.1, hboth.2.1]
  | writableChildWrite =>
    cases findNode? w.nodes parentTag with
    | none => rfl
    | some _ =>
      cases hlen : (rangeLen == 0) with
      | true => simp
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rcases Bool.eq_false_or_eq_true w.allocReadOnly with hro | hro
        · simp [hro]
        simp only [hro]
        cases hreq : (requireInit && !w.pointeeInitialized) with
        | true => simp
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases hm : mapNodesM (fun n => stepNodeOnRangeWrite w.activeProtectors ((ancestorPathTags w.nodes parentTag).contains n.tag) rangeOffset rangeLen n) w.nodes with
          | error e =>
            constructor
            · intro h; cases h
            · intro h
              dsimp only at h
              cases hc1 : checkAncestorPathM w parentTag (stepNodeOnRangeWrite w.activeProtectors true rangeOffset rangeLen) with
              | error _ => rw [hc1] at h; cases h
              | ok u1 =>
                cases u1
                rw [hc1] at h; simp only at h
                cases hc2 : checkNodesM (stepNodeOnRangeWrite w.activeProtectors false rangeOffset rangeLen)
                    (w.nodes.filter (fun n => !(ancestorPathTags w.nodes parentTag).contains n.tag)) with
                | error _ => rw [hc2] at h; cases h
                | ok u2 => cases u2; rw [hc2] at h; simp only at h; cases h
          | ok nodes' =>
            have hboth := (check_anc_and_foreign_ok_iff_mapNodesM w parentTag
              (fun isLoc n => stepNodeOnRangeWrite w.activeProtectors isLoc rangeOffset rangeLen n) nodes').2 hm
            simp only [hboth.1, hboth.2.1]

private theorem stepNodeOnRangeRead_preserves_meta
    {ps : List Nat} {isLoc : Bool} {off len : Nat} {n n' : TreeTagNode}
    (h : stepNodeOnRangeRead ps isLoc off len n = .ok n') :
    n'.tag = n.tag ∧ n'.parentTag = n.parentTag ∧ n'.protector = n.protector := by
  unfold stepNodeOnRangeRead at h
  cases hov : rangesOverlap off len n.rangeOffset n.rangeLen with
  | false =>
    simp [hov] at h; subst h; exact ⟨rfl, rfl, rfl⟩
  | true =>
    simp only [hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases isLoc with
    | true =>
      simp only [↓reduceIte] at h
      cases hperm : n.perm <;> rw [hperm] at h <;> simp at h <;> (subst h; exact ⟨rfl, rfl, rfl⟩)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      cases hperm : n.perm <;> rw [hperm] at h
      · injection h with h; subst h; exact ⟨rfl, rfl, rfl⟩
      · cases hprot : n.isProtected ps <;> simp [hprot] at h <;> (subst h; exact ⟨rfl, rfl, rfl⟩)
      · cases hprot : n.isProtected ps <;> simp [hprot] at h; subst h; exact ⟨rfl, rfl, rfl⟩
      · cases hprot : n.isProtected ps <;> cases hacc : n.accessed <;> simp [hprot, hacc] at h <;>
          (subst h; exact ⟨rfl, rfl, rfl⟩)
      · injection h with h; subst h; exact ⟨rfl, rfl, rfl⟩
      · injection h with h; subst h; exact ⟨rfl, rfl, rfl⟩

private theorem ancestorPathTagsAux_of_same_shape {xs ys : List TreeTagNode}
    (hshape : ∀ t, (findNode? ys t).map (fun n => (n.tag, n.parentTag)) =
      (findNode? xs t).map (fun n => (n.tag, n.parentTag)))
    (fuel start : Nat) :
    ancestorPathTagsAux ys fuel start = ancestorPathTagsAux xs fuel start := by
  induction fuel generalizing start with
  | zero => rfl
  | succ f ih =>
    simp only [ancestorPathTagsAux]
    have hs := hshape start
    cases hfy : findNode? ys start with
    | none =>
      rw [hfy] at hs
      cases hfx : findNode? xs start with
      | none => rfl
      | some _ => rw [hfx] at hs; cases hs
    | some ny =>
      rw [hfy] at hs
      cases hfx : findNode? xs start with
      | none => rw [hfx] at hs; cases hs
      | some nx =>
        rw [hfx] at hs
        simp only [Option.map_some] at hs
        injection hs with hp
        have hpar : ny.parentTag = nx.parentTag := (Prod.mk.inj hp).2
        simp only [hpar]
        cases hnp : nx.parentTag with
        | none => rfl
        | some p => simp only [ih p]

private theorem ancestorPathTagsAux_cons_fresh {child : TreeTagNode} {xs : List TreeTagNode}
    (hparFresh : ∀ n ∈ xs, n.parentTag ≠ some child.tag)
    (fuel start : Nat) (hstartNe : start ≠ child.tag) :
    ancestorPathTagsAux (child :: xs) fuel start = ancestorPathTagsAux xs fuel start := by
  induction fuel generalizing start with
  | zero => rfl
  | succ f ih =>
    simp only [ancestorPathTagsAux, findNode?, List.find?]
    have hneq : (child.tag == start) = false := beq_false_of_ne (fun h => hstartNe h.symm)
    simp only [hneq]
    cases hfx : xs.find? (fun n => n.tag == start) with
    | none => rfl
    | some nx =>
      have hmem : nx ∈ xs := List.mem_of_find?_eq_some hfx
      cases hp : nx.parentTag with
      | none => simp [hp]
      | some p =>
        have hpNe : p ≠ child.tag := fun heq => hparFresh nx hmem (hp.trans (congrArg some heq))
        simp only [hp, ih p hpNe]

private theorem mapNodesM_stepRead_then_stepWrite_ok_iff
    (activeProtectors : List Nat) (protId : Nat) (anc : List Nat) (off len : Nat)
    (xs ys : List TreeTagNode)
    (hfreshProt : ∀ n ∈ xs, n.protector ≠ some protId) :
    (∃ xs1,
      mapNodesM (fun n => stepNodeOnRangeRead activeProtectors (anc.contains n.tag) off len n) xs = .ok xs1 ∧
      mapNodesM (fun n => stepNodeOnRangeWrite (protId :: activeProtectors) (anc.contains n.tag) off len n) xs1 = .ok ys) ↔
    mapNodesM (fun n => stepNodeOnRangeWrite activeProtectors (anc.contains n.tag) off len n) xs = .ok ys := by
  induction xs generalizing ys with
  | nil =>
    constructor
    · rintro ⟨xs1, h1, h2⟩
      simp [mapNodesM] at h1; subst h1; exact h2
    · intro h; simp [mapNodesM] at h; subst h; exact ⟨[], rfl, rfl⟩
  | cons x rest ih =>
    have hpx : x.protector ≠ some protId := hfreshProt x (List.mem_cons_self ..)
    have hprest : ∀ n ∈ rest, n.protector ≠ some protId := fun n hn => hfreshProt n (List.mem_cons_of_mem _ hn)
    have hstepEq : ∀ x1,
        stepNodeOnRangeRead activeProtectors (anc.contains x.tag) off len x = .ok x1 →
        stepNodeOnRangeWrite (protId :: activeProtectors) (anc.contains x1.tag) off len x1 =
          stepNodeOnRangeWrite activeProtectors (anc.contains x.tag) off len x1 := by
      intro x1 h1
      rcases stepNodeOnRangeRead_preserves_meta h1 with ⟨htag, _, hprot⟩
      rw [htag]
      have hpx1 : x1.isProtected (protId :: activeProtectors) = x1.isProtected activeProtectors := by
        unfold TreeTagNode.isProtected
        rw [hprot]
        cases hx : x.protector with
        | none => rfl
        | some q =>
          have hne : (protId == q) = false := beq_false_of_ne (fun h => hpx (hx.trans (congrArg some h.symm)))
          simp [List.any_cons, hne]
      unfold stepNodeOnRangeWrite
      simp only [hpx1]
    constructor
    · rintro ⟨xs1, h1, h2⟩
      simp only [mapNodesM] at h1
      cases hr : stepNodeOnRangeRead activeProtectors (anc.contains x.tag) off len x with
      | error _ => rw [hr] at h1; cases h1
      | ok x1 =>
        rw [hr] at h1; simp only at h1
        cases hmr : mapNodesM (fun n => stepNodeOnRangeRead activeProtectors (anc.contains n.tag) off len n) rest with
        | error _ => rw [hmr] at h1; cases h1
        | ok rest1 =>
          rw [hmr] at h1; simp only at h1
          injection h1 with hxs1; subst hxs1
          simp only [mapNodesM] at h2
          rw [hstepEq x1 hr] at h2
          cases hw : stepNodeOnRangeWrite activeProtectors (anc.contains x.tag) off len x1 with
          | error _ => rw [hw] at h2; cases h2
          | ok y =>
            rw [hw] at h2; simp only at h2
            cases hmw : mapNodesM (fun n => stepNodeOnRangeWrite (protId :: activeProtectors) (anc.contains n.tag) off len n) rest1 with
            | error _ => rw [hmw] at h2; cases h2
            | ok ys' =>
              rw [hmw] at h2; simp only at h2
              injection h2 with hys; subst hys
              have hxy : stepNodeOnRangeWrite activeProtectors (anc.contains x.tag) off len x = .ok y := by
                apply (stepNode_read_then_write_ok_iff activeProtectors (anc.contains x.tag) off len x y).1
                simp only [Bind.bind, Except.bind, hr, hw]
              have hrest' := (ih ys' hprest).1 ⟨rest1, hmr, hmw⟩
              simp only [mapNodesM, hxy, hrest']
    · intro h
      simp only [mapNodesM] at h
      cases hw : stepNodeOnRangeWrite activeProtectors (anc.contains x.tag) off len x with
      | error _ => rw [hw] at h; cases h
      | ok y =>
        rw [hw] at h; simp only at h
        cases hmw : mapNodesM (fun n => stepNodeOnRangeWrite activeProtectors (anc.contains n.tag) off len n) rest with
        | error _ => rw [hmw] at h; cases h
        | ok ys' =>
          rw [hmw] at h; simp only at h
          injection h with hys; subst hys
          have hcomp := (stepNode_read_then_write_ok_iff activeProtectors (anc.contains x.tag) off len x y).2 hw
          cases hr : stepNodeOnRangeRead activeProtectors (anc.contains x.tag) off len x with
          | error _ => simp only [Bind.bind, Except.bind, hr] at hcomp; cases hcomp
          | ok x1 =>
            simp only [Bind.bind, Except.bind, hr] at hcomp
            rcases (ih ys' hprest).2 hmw with ⟨rest1, hmr, hmw1⟩
            refine ⟨x1 :: rest1, by simp only [mapNodesM, hr, hmr], ?_⟩
            simp only [mapNodesM, hstepEq x1 hr, hcomp, hmw1]

/-- Hypothesis-free success-path equivalence across all three models (`execFnEntryMutRetag`,
`execFnEntryMutRetagUpstream`, and `execFnEntryMutRetagSourceOrder`) on every `BorrowTreeTagsWF` world. -/
theorem execFnEntryMutRetag_ok_iff_upstream_ok_iff_sourceOrder_ok
    (w : FnEntryBorrowWorld) (hwf : BorrowTreeTagsWF w)
    (parentTag rangeOffset rangeLen : Nat)
    (policy : FnEntryRetagPolicy) (requireInit : Bool)
    (r : FnEntryBorrowWorld × Nat) :
    (execFnEntryMutRetag w parentTag rangeOffset rangeLen policy requireInit = .ok r ↔
      execFnEntryMutRetagUpstream w parentTag rangeOffset rangeLen policy requireInit = .ok r) ∧
    (execFnEntryMutRetagUpstream w parentTag rangeOffset rangeLen policy requireInit = .ok r ↔
      execFnEntryMutRetagSourceOrder w parentTag rangeOffset rangeLen policy requireInit = .ok r) := by
  refine ⟨?_, execFnEntryMutRetagUpstream_ok_iff_sourceOrder_ok w parentTag rangeOffset rangeLen policy requireInit r⟩
  cases policy with
  | skipRetag => rfl
  | rustcNoWritable =>
    rw [execFnEntryMutRetag_eq_upstream_when_no_implicitWrite]
  | writableChildWrite =>
    unfold execFnEntryMutRetag execFnEntryMutRetagUpstream
    cases hfind : findNode? w.nodes parentTag with
    | none => rfl
    | some pNode =>
      have hpMem : pNode ∈ w.nodes := List.mem_of_find?_eq_some hfind
      have hfindBool : (pNode.tag == parentTag) = true :=
        List.find?_some (p := fun (n : TreeTagNode) => n.tag == parentTag) hfind
      have hpTag : pNode.tag = parentTag := beq_iff_eq.1 hfindBool
      have hparentNe : parentTag ≠ w.nextTag := hpTag ▸ hwf.nextTagFresh pNode hpMem
      cases hlen : (rangeLen == 0) with
      | true => simp
      | false =>
        have hlenNz : rangeLen ≠ 0 := fun h => by subst h; simp at hlen
        simp only [Bool.false_eq_true, ↓reduceIte]
        rcases Bool.eq_false_or_eq_true w.allocReadOnly with hro | hro
        · simp [hro]
        simp only [hro]
        cases hreq : (requireInit && !w.pointeeInitialized) with
        | true =>
          simp
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          have hreadShape : ∀ n n',
              stepNodeOnRangeRead w.activeProtectors ((ancestorPathTags w.nodes parentTag).contains n.tag) rangeOffset rangeLen n = .ok n' →
              n'.tag = n.tag ∧ n'.parentTag = n.parentTag := fun _ _ h =>
            let ⟨ht, hp, _⟩ := stepNodeOnRangeRead_preserves_meta h; ⟨ht, hp⟩
          have hchildSelfStep : ∀ (anc : List Nat),
              anc.contains w.nextTag = true →
              stepNodeOnRangeWrite (w.nextProtector :: w.activeProtectors)
                (anc.contains w.nextTag) rangeOffset rangeLen
                { tag := w.nextTag, parentTag := some parentTag, perm := .reservedFrz false,
                  rangeOffset := rangeOffset, rangeLen := rangeLen, protector := some w.nextProtector,
                  accessed := true } =
              .ok { tag := w.nextTag, parentTag := some parentTag, perm := .unique,
                    rangeOffset := rangeOffset, rangeLen := rangeLen, protector := some w.nextProtector,
                    accessed := true } := by
            intro anc hcon
            have hpos : 0 < rangeLen := Nat.pos_of_ne_zero hlenNz
            have hov : rangesOverlap rangeOffset rangeLen rangeOffset rangeLen = true := by
              unfold rangesOverlap
              have hnz : (rangeLen != 0) = true := bne_iff_ne.2 hlenNz
              have hlt : rangeOffset < rangeOffset + rangeLen := Nat.lt_add_of_pos_right hpos
              simp [hnz, hlt]
            rw [hcon]
            simp [stepNodeOnRangeWrite, hov]
          have hancEq : ∀ nodes1,
              mapNodesM (fun n => stepNodeOnRangeRead w.activeProtectors ((ancestorPathTags w.nodes parentTag).contains n.tag) rangeOffset rangeLen n) w.nodes = .ok nodes1 →
              let childBase : TreeTagNode :=
                { tag := w.nextTag, parentTag := some parentTag, perm := .reservedFrz false,
                  rangeOffset := rangeOffset, rangeLen := rangeLen, protector := some w.nextProtector,
                  accessed := true }
              ancestorPathTags (childBase :: nodes1) w.nextTag =
                w.nextTag :: ancestorPathTags w.nodes parentTag := by
            intro nodes1 hmr childBase
            rcases mapNodesM_preserves_shape _ hreadShape hmr with ⟨hlen1, hfind1⟩
            have hparFresh1 : ∀ n ∈ nodes1, n.parentTag ≠ some w.nextTag := by
              intro n hn
              have hrel := (mapNodesM_ok_iff _ _ _).1 hmr
              rcases ListRel.exists_of_mem_right hrel hn with ⟨m, hmIn, hstep⟩
              rw [(hreadShape m n hstep).2]
              exact hwf.parentTagsFresh m hmIn
            unfold ancestorPathTags
            rw [List.length_cons, hlen1]
            change (match findNode? (childBase :: nodes1) w.nextTag with
              | some n => match n.parentTag with
                | some p => w.nextTag :: ancestorPathTagsAux (childBase :: nodes1) (w.nodes.length + 1) p
                | none => [w.nextTag]
              | none => [w.nextTag]) =
              w.nextTag :: ancestorPathTagsAux w.nodes (w.nodes.length + 1) parentTag
            have hfindChild : findNode? (childBase :: nodes1) w.nextTag = some childBase := by
              simp [findNode?, childBase]
            rw [hfindChild]
            dsimp only [childBase]
            congr 1
            rw [ancestorPathTagsAux_cons_fresh (child := childBase) hparFresh1 (w.nodes.length + 1) parentTag hparentNe]
            exact ancestorPathTagsAux_of_same_shape hfind1 (w.nodes.length + 1) parentTag
          have hmapRewrite : ∀ nodes1,
              mapNodesM (fun n => stepNodeOnRangeRead w.activeProtectors ((ancestorPathTags w.nodes parentTag).contains n.tag) rangeOffset rangeLen n) w.nodes = .ok nodes1 →
              mapNodesM (fun n => stepNodeOnRangeWrite (w.nextProtector :: w.activeProtectors)
                ((w.nextTag :: ancestorPathTags w.nodes parentTag).contains n.tag) rangeOffset rangeLen n) nodes1 =
              mapNodesM (fun n => stepNodeOnRangeWrite (w.nextProtector :: w.activeProtectors)
                ((ancestorPathTags w.nodes parentTag).contains n.tag) rangeOffset rangeLen n) nodes1 := by
            intro nodes1 hmr
            have hfresh1 : ∀ n ∈ nodes1, n.tag ≠ w.nextTag := by
              intro n hn
              have hrel := (mapNodesM_ok_iff _ _ _).1 hmr
              rcases ListRel.exists_of_mem_right hrel hn with ⟨m, hmIn, hstep⟩
              rw [(hreadShape m n hstep).1]
              exact hwf.nextTagFresh m hmIn
            clear hmr
            induction nodes1 with
            | nil => rfl
            | cons n rest ih =>
              have hnNe : n.tag ≠ w.nextTag := hfresh1 n (List.mem_cons_self ..)
              have hcon : ((w.nextTag :: ancestorPathTags w.nodes parentTag).contains n.tag) =
                  (ancestorPathTags w.nodes parentTag).contains n.tag := by
                simp [hnNe]
              simp only [mapNodesM, hcon]
              rw [ih (fun m hm => hfresh1 m (List.mem_cons_of_mem _ hm))]
          constructor
          · intro h
            cases hmr : mapNodesM (fun n => stepNodeOnRangeRead w.activeProtectors ((ancestorPathTags w.nodes parentTag).contains n.tag) rangeOffset rangeLen n) w.nodes with
            | error _ => rw [hmr] at h; cases h
            | ok nodes1 =>
              rw [hmr] at h
              simp only [hancEq nodes1 hmr, mapNodesM] at h
              rw [hchildSelfStep _ (by simp)] at h
              rw [hmapRewrite nodes1 hmr] at h
              cases hmw : mapNodesM (fun n => stepNodeOnRangeWrite (w.nextProtector :: w.activeProtectors) ((ancestorPathTags w.nodes parentTag).contains n.tag) rangeOffset rangeLen n) nodes1 with
              | error _ => rw [hmw] at h; cases h
              | ok nodes2 =>
                rw [hmw] at h
                have hdir := (mapNodesM_stepRead_then_stepWrite_ok_iff w.activeProtectors w.nextProtector
                  (ancestorPathTags w.nodes parentTag) rangeOffset rangeLen w.nodes nodes2
                  hwf.nextProtectorFresh).1 ⟨nodes1, hmr, hmw⟩
                rw [hdir]
                exact h
          · intro h
            cases hdir : mapNodesM (fun n => stepNodeOnRangeWrite w.activeProtectors ((ancestorPathTags w.nodes parentTag).contains n.tag) rangeOffset rangeLen n) w.nodes with
            | error _ => rw [hdir] at h; cases h
            | ok nodes2 =>
              rw [hdir] at h
              rcases (mapNodesM_stepRead_then_stepWrite_ok_iff w.activeProtectors w.nextProtector
                (ancestorPathTags w.nodes parentTag) rangeOffset rangeLen w.nodes nodes2
                hwf.nextProtectorFresh).2 hdir with ⟨nodes1, hmr, hmw⟩
              rw [hmr]
              simp only [hancEq nodes1 hmr, mapNodesM]
              rw [hchildSelfStep _ (by simp)]
              rw [hmapRewrite nodes1 hmr, hmw]
              exact h

/-- Helper: when every ancestor succeeds under `step true`, flat-list `mapNodesM` and
source-order `checkAncestorPathM` + foreign check + `mapNodesM` return identical results (even on errors). -/
private theorem mapNodesM_eq_sourceOrder_of_ancestors_ok
    (w : FnEntryBorrowWorld) (parentTag : Nat)
    (step : Bool → TreeTagNode → Except RetagStepErr TreeTagNode)
    (hancOk : ∀ n ∈ w.nodes, (ancestorPathTags w.nodes parentTag).contains n.tag = true →
      ∃ n', step true n = .ok n') :
    (match checkAncestorPathM w parentTag (step true) with
     | .error e => .error e
     | .ok () =>
       match checkNodesM (step false) (w.nodes.filter (fun n => !(ancestorPathTags w.nodes parentTag).contains n.tag)) with
       | .error e => .error e
       | .ok () =>
         mapNodesM (fun n => step ((ancestorPathTags w.nodes parentTag).contains n.tag) n) w.nodes) =
    mapNodesM (fun n => step ((ancestorPathTags w.nodes parentTag).contains n.tag) n) w.nodes := by
  have hc1 : checkAncestorPathM w parentTag (step true) = .ok () := by
    rw [checkAncestorPathM, checkNodesM_ok_iff]
    intro n hn
    rcases (mem_ancestorPathNodes_iff w.nodes parentTag n).1 hn with ⟨hnIn, hanc⟩
    exact hancOk n hnIn hanc
  rw [hc1]
  have hfilt : ∀ xs : List TreeTagNode,
      (∀ n ∈ xs, (ancestorPathTags w.nodes parentTag).contains n.tag = true → ∃ n', step true n = .ok n') →
      (match checkNodesM (step false) (xs.filter (fun n => !(ancestorPathTags w.nodes parentTag).contains n.tag)) with
       | .error e => .error e
       | .ok () => mapNodesM (fun n => step ((ancestorPathTags w.nodes parentTag).contains n.tag) n) xs) =
      mapNodesM (fun n => step ((ancestorPathTags w.nodes parentTag).contains n.tag) n) xs := by
    intro xs hxs
    induction xs with
    | nil => rfl
    | cons x rest ih =>
      have hrest := ih (fun n hn => hxs n (List.mem_cons_of_mem _ hn))
      cases hax : (ancestorPathTags w.nodes parentTag).contains x.tag with
      | true =>
        rcases hxs x (List.mem_cons_self ..) hax with ⟨x', hx'⟩
        simp only [List.filter_cons, hax, Bool.not_true, Bool.false_eq_true, ↓reduceIte, mapNodesM, hx']
        cases hc : checkNodesM (step false) (rest.filter (fun n => !(ancestorPathTags w.nodes parentTag).contains n.tag)) with
        | error e =>
          simp only [hc] at hrest
          rw [← hrest]
        | ok u =>
          cases u
          rfl
      | false =>
        simp only [List.filter_cons, hax, Bool.not_false, ↓reduceIte, checkNodesM, mapNodesM]
        cases hfx : step false x with
        | error e => rfl
        | ok x' =>
          cases hc : checkNodesM (step false) (rest.filter (fun n => !(ancestorPathTags w.nodes parentTag).contains n.tag)) with
          | error e =>
            simp only [hc] at hrest
            rw [← hrest]
          | ok u =>
            cases u
            rfl
  exact hfilt w.nodes hancOk

/-- Under `AncestorsWritableIn`, flat-list upstream and bottom-up source-order agree identically
(on both `.ok` and `.error`, with zero `BorrowTreeTagsWF` needed). -/
theorem execFnEntryMutRetagUpstream_eq_sourceOrder_of_writableAncestors
    (w : FnEntryBorrowWorld) (parentTag rangeOffset rangeLen : Nat)
    (policy : FnEntryRetagPolicy) (requireInit : Bool)
    (hwrit : AncestorsWritableIn w parentTag rangeOffset rangeLen) :
    execFnEntryMutRetagUpstream w parentTag rangeOffset rangeLen policy requireInit =
      execFnEntryMutRetagSourceOrder w parentTag rangeOffset rangeLen policy requireInit := by
  unfold execFnEntryMutRetagUpstream execFnEntryMutRetagSourceOrder
  cases policy with
  | skipRetag => rfl
  | rustcNoWritable =>
    cases findNode? w.nodes parentTag with
    | none => rfl
    | some _ =>
      cases hlen : (rangeLen == 0) with
      | true => simp
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hreadOk : ∀ n ∈ w.nodes, (ancestorPathTags w.nodes parentTag).contains n.tag = true →
            ∃ n', stepNodeOnRangeRead w.activeProtectors true rangeOffset rangeLen n = .ok n' := by
          intro n hn hanc
          rcases hwrit n hn hanc with ⟨n', hw⟩
          have hcomp := (stepNode_read_then_write_ok_iff w.activeProtectors true rangeOffset rangeLen n n').2 hw
          cases hr : stepNodeOnRangeRead w.activeProtectors true rangeOffset rangeLen n with
          | error _ => simp [Bind.bind, Except.bind, hr] at hcomp
          | ok n1 => exact ⟨n1, rfl⟩
        have heq := mapNodesM_eq_sourceOrder_of_ancestors_ok w parentTag
          (fun isLoc n => stepNodeOnRangeRead w.activeProtectors isLoc rangeOffset rangeLen n) hreadOk
        cases hc1 : checkAncestorPathM w parentTag (stepNodeOnRangeRead w.activeProtectors true rangeOffset rangeLen) with
        | error e => simp only [hc1] at heq; rw [← heq]
        | ok u1 =>
          cases u1
          cases hc2 : checkNodesM (stepNodeOnRangeRead w.activeProtectors false rangeOffset rangeLen)
              (w.nodes.filter (fun n => !(ancestorPathTags w.nodes parentTag).contains n.tag)) with
          | error e => simp only [hc1, hc2] at heq; rw [← heq]
          | ok u2 => rfl
  | writableChildWrite =>
    cases findNode? w.nodes parentTag with
    | none => rfl
    | some _ =>
      cases hlen : (rangeLen == 0) with
      | true => simp
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rcases Bool.eq_false_or_eq_true w.allocReadOnly with hro | hro
        · simp [hro]
        simp only [hro]
        cases hreq : (requireInit && !w.pointeeInitialized) with
        | true => simp
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          have heq := mapNodesM_eq_sourceOrder_of_ancestors_ok w parentTag
            (fun isLoc n => stepNodeOnRangeWrite w.activeProtectors isLoc rangeOffset rangeLen n) hwrit
          cases hc1 : checkAncestorPathM w parentTag (stepNodeOnRangeWrite w.activeProtectors true rangeOffset rangeLen) with
          | error e => simp only [hc1] at heq; rw [← heq]
          | ok u1 =>
            cases u1
            cases hc2 : checkNodesM (stepNodeOnRangeWrite w.activeProtectors false rangeOffset rangeLen)
                (w.nodes.filter (fun n => !(ancestorPathTags w.nodes parentTag).contains n.tag)) with
            | error e => simp only [hc1, hc2] at heq; rw [← heq]
            | ok u2 => rfl

/-- Three-model equality under `BorrowTreeTagsWF ∧ AncestorsWritableIn ∧ ForeignReadWriteErrorAligned`. -/
theorem execFnEntryMutRetag_eq_sourceOrder_of_writableAncestors
    (w : FnEntryBorrowWorld) (hwf : BorrowTreeTagsWF w)
    (parentTag rangeOffset rangeLen : Nat)
    (policy : FnEntryRetagPolicy) (requireInit : Bool)
    (hwrit : AncestorsWritableIn w parentTag rangeOffset rangeLen)
    (hfor : ForeignReadWriteErrorAligned w parentTag rangeOffset rangeLen) :
    execFnEntryMutRetag w parentTag rangeOffset rangeLen policy requireInit =
      execFnEntryMutRetagSourceOrder w parentTag rangeOffset rangeLen policy requireInit := by
  rw [← execFnEntryMutRetagUpstream_eq_sourceOrder_of_writableAncestors w parentTag rangeOffset rangeLen policy requireInit hwrit]
  cases hup : execFnEntryMutRetagUpstream w parentTag rangeOffset rangeLen policy requireInit with
  | ok r =>
    exact (execFnEntryMutRetag_ok_iff_upstream_ok_iff_sourceOrder_ok w hwf parentTag rangeOffset rangeLen policy requireInit r).1.2 hup
  | error e =>
    cases policy with
    | skipRetag => simp [execFnEntryMutRetagUpstream] at hup
    | rustcNoWritable =>
      rw [execFnEntryMutRetag_eq_upstream_when_no_implicitWrite, hup]
    | writableChildWrite =>
      unfold execFnEntryMutRetagUpstream at hup
      unfold execFnEntryMutRetag
      cases hfind : findNode? w.nodes parentTag with
      | none => simp only [hfind] at hup ⊢; exact hup
      | some _ =>
        simp only [hfind] at hup ⊢
        cases hlen : (rangeLen == 0) with
        | true => simp only [hlen, ↓reduceIte] at hup; cases hup
        | false =>
          simp only [hlen, Bool.false_eq_true, ↓reduceIte] at hup ⊢
          cases hro : w.allocReadOnly with
          | true =>
            simp only [hro, ↓reduceIte] at hup ⊢
            exact hup
          | false =>
            simp only [hro, Bool.false_eq_true, ↓reduceIte] at hup ⊢
            cases hreq : (requireInit && !w.pointeeInitialized) with
            | true =>
              simp only [hreq, ↓reduceIte] at hup ⊢
              exact hup
            | false =>
              simp only [hreq, Bool.false_eq_true, ↓reduceIte] at hup ⊢
              rcases hfor with hforOk | hforAlign
              · -- Contradiction: all ancestors AND all foreign nodes succeed on write, so `hup` couldn't be `.error e`!
                have hallWrite : ∀ n ∈ w.nodes, ∃ n',
                    stepNodeOnRangeWrite w.activeProtectors ((ancestorPathTags w.nodes parentTag).contains n.tag) rangeOffset rangeLen n = .ok n' := by
                  intro n hn
                  cases ha : (ancestorPathTags w.nodes parentTag).contains n.tag with
                  | true => exact hwrit n hn ha
                  | false => exact hforOk n hn ha
                rcases mapNodesM_eq_of_check_and_ok _ w.nodes hallWrite with ⟨ys, hys⟩
                rw [hys] at hup; cases hup
              · -- Every node either succeeds on both read & write or fails on both with the exact same error!
                have hsameErr : ∀ xs : List TreeTagNode,
                    (∀ n ∈ xs, (ancestorPathTags w.nodes parentTag).contains n.tag = true →
                      ∃ n', stepNodeOnRangeWrite w.activeProtectors true rangeOffset rangeLen n = .ok n') →
                    (∀ n ∈ xs, (ancestorPathTags w.nodes parentTag).contains n.tag = false →
                      (stepNodeOnRangeRead w.activeProtectors false rangeOffset rangeLen n).isOk =
                        (stepNodeOnRangeWrite w.activeProtectors false rangeOffset rangeLen n).isOk) →
                    mapNodesM (fun n => stepNodeOnRangeWrite w.activeProtectors ((ancestorPathTags w.nodes parentTag).contains n.tag) rangeOffset rangeLen n) xs = .error e →
                    mapNodesM (fun n => stepNodeOnRangeRead w.activeProtectors ((ancestorPathTags w.nodes parentTag).contains n.tag) rangeOffset rangeLen n) xs = .error e := by
                  intro xs hxa hxf hmw
                  induction xs with
                  | nil => cases hmw
                  | cons x rest ih =>
                    simp only [mapNodesM] at hmw ⊢
                    cases hax : (ancestorPathTags w.nodes parentTag).contains x.tag with
                    | true =>
                      rcases hxa x (List.mem_cons_self ..) hax with ⟨x', hx'⟩
                      simp only [hax] at hmw ⊢
                      rw [hx'] at hmw
                      have hcomp := (stepNode_read_then_write_ok_iff w.activeProtectors true rangeOffset rangeLen x x').2 hx'
                      cases hr : stepNodeOnRangeRead w.activeProtectors true rangeOffset rangeLen x with
                      | error _ => simp [Bind.bind, Except.bind, hr] at hcomp
                      | ok x1 =>
                        cases hrestw : mapNodesM (fun n => stepNodeOnRangeWrite w.activeProtectors ((ancestorPathTags w.nodes parentTag).contains n.tag) rangeOffset rangeLen n) rest with
                        | ok _ => rw [hrestw] at hmw; cases hmw
                        | error e' =>
                          rw [hrestw] at hmw; injection hmw with he'; subst he'
                          rw [ih (fun n hn => hxa n (List.mem_cons_of_mem _ hn))
                            (fun n hn => hxf n (List.mem_cons_of_mem _ hn)) hrestw]
                    | false =>
                      simp only [hax] at hmw ⊢
                      have hal := hxf x (List.mem_cons_self ..) hax
                      cases hwx : stepNodeOnRangeWrite w.activeProtectors false rangeOffset rangeLen x with
                      | error ew =>
                        rw [hwx] at hmw hal; injection hmw with hew; subst hew
                        cases hrx : stepNodeOnRangeRead w.activeProtectors false rangeOffset rangeLen x with
                        | ok _ => rw [hrx] at hal; cases hal
                        | error er =>
                          have hstep := stepNode_read_then_childWrite_eq_parentWrite w.activeProtectors false rangeOffset rangeLen x (by simp)
                          rw [hrx, hwx] at hstep
                          simp [Bind.bind, Except.bind] at hstep
                          rw [hstep]
                      | ok x' =>
                        rw [hwx] at hmw hal
                        cases hrx : stepNodeOnRangeRead w.activeProtectors false rangeOffset rangeLen x with
                        | error _ => rw [hrx] at hal; cases hal
                        | ok x1 =>
                          cases hrestw : mapNodesM (fun n => stepNodeOnRangeWrite w.activeProtectors ((ancestorPathTags w.nodes parentTag).contains n.tag) rangeOffset rangeLen n) rest with
                          | ok _ => rw [hrestw] at hmw; cases hmw
                          | error e' =>
                            rw [hrestw] at hmw; injection hmw with he'; subst he'
                            rw [ih (fun n hn => hxa n (List.mem_cons_of_mem _ hn))
                              (fun n hn => hxf n (List.mem_cons_of_mem _ hn)) hrestw]
                cases hmw : mapNodesM (fun n => stepNodeOnRangeWrite w.activeProtectors ((ancestorPathTags w.nodes parentTag).contains n.tag) rangeOffset rangeLen n) w.nodes with
                | ok _ => rw [hmw] at hup; cases hup
                | error e' =>
                  rw [hmw] at hup; injection hup with he'; subst he'
                  rw [hsameErr w.nodes hwrit hforAlign hmw]

/-- Unconditional `.frozen` preservation theorem: on EVERY `w : FnEntryBorrowWorld`, whenever
`execFnEntryMutRetagSourceOrder` under `.rustcNoWritable` succeeds, every `.frozen` node in `w.nodes`
retains `.frozen` in `w'.nodes` (and survives verbatim whenever `n.accessed = true`). -/
theorem sourceOrder_rustcNoWritable_preserves_all_frozen_nodes
    (w w' : FnEntryBorrowWorld) (parentTag rangeOffset rangeLen childTag : Nat)
    (requireInit : Bool)
    (hok : execFnEntryMutRetagSourceOrder w parentTag rangeOffset rangeLen .rustcNoWritable requireInit = .ok (w', childTag)) :
    ∀ n ∈ w.nodes, n.perm = .frozen →
      ∃ n' ∈ w'.nodes, n'.tag = n.tag ∧ n'.parentTag = n.parentTag ∧ n'.perm = .frozen ∧
        (n.accessed = true → n' = n) := by
  have hup := (execFnEntryMutRetagUpstream_ok_iff_sourceOrder_ok w parentTag rangeOffset rangeLen .rustcNoWritable requireInit (w', childTag)).2 hok
  unfold execFnEntryMutRetagUpstream at hup
  cases hfind : findNode? w.nodes parentTag with
  | none => simp [hfind] at hup
  | some _ =>
    simp only [hfind] at hup
    cases hlen : (rangeLen == 0) with
    | true =>
      simp only [hlen, ↓reduceIte] at hup
      injection hup with hpair
      have hw' := (Prod.mk.inj hpair).1
      subst hw'
      intro n hn hfrz
      exact ⟨n, List.mem_cons_of_mem _ hn, rfl, rfl, hfrz, fun _ => rfl⟩
    | false =>
      simp only [hlen, Bool.false_eq_true, ↓reduceIte] at hup
      cases hm : mapNodesM (fun n => stepNodeOnRangeRead w.activeProtectors ((ancestorPathTags w.nodes parentTag).contains n.tag) rangeOffset rangeLen n) w.nodes with
      | error _ => rw [hm] at hup; cases hup
      | ok nodes' =>
        rw [hm] at hup
        injection hup with hpair
        have hw' := (Prod.mk.inj hpair).1
        subst hw'
        intro n hn hfrz
        have hrel := (mapNodesM_ok_iff _ _ _).1 hm
        rcases ListRel.exists_of_mem_left hrel hn with ⟨n', hn'Mem, hstep⟩
        refine ⟨n', List.mem_cons_of_mem _ hn'Mem, ?_⟩
        unfold stepNodeOnRangeRead at hstep
        split at hstep
        · injection hstep with hstep; subst hstep; exact ⟨rfl, rfl, hfrz, fun _ => rfl⟩
        · split at hstep
          · rcases n with ⟨nt, np, nperm, noff, nlen, nprot, nacc⟩
            simp only at hfrz; subst hfrz
            simp only at hstep
            injection hstep with hstep; subst hstep
            exact ⟨rfl, rfl, rfl, fun hacc => by simp only at hacc; subst hacc; rfl⟩
          · simp [hfrz] at hstep; subst hstep; exact ⟨rfl, rfl, hfrz, fun _ => rfl⟩

/-- Exact equivalence between Model 4 (`SkipSelfAndChildren`-pruned source-order) and Model 3
(`execFnEntryMutRetagSourceOrder`) whenever no foreign node sits beneath a skipped foreign ancestor. -/
theorem execFnEntryMutRetagPrunedSourceOrder_eq_sourceOrder_of_noSkippedForeignSubtree
    (w : FnEntryBorrowWorld) (parentTag rangeOffset rangeLen : Nat)
    (policy : FnEntryRetagPolicy) (requireInit : Bool)
    (hnoSkip : ∀ n ∈ w.nodes,
      isPrunedForeignNode w.nodes (ancestorPathTags w.nodes parentTag)
        (policy == .writableChildWrite) rangeOffset rangeLen n = false) :
    execFnEntryMutRetagPrunedSourceOrder w parentTag rangeOffset rangeLen policy requireInit =
      execFnEntryMutRetagSourceOrder w parentTag rangeOffset rangeLen policy requireInit := by
  have hfiltEq : ∀ (isWrite : Bool) (xs : List TreeTagNode),
      (∀ n ∈ xs, isPrunedForeignNode w.nodes (ancestorPathTags w.nodes parentTag) isWrite rangeOffset rangeLen n = false) →
      xs.filter (fun n => !(ancestorPathTags w.nodes parentTag).contains n.tag &&
        !isPrunedForeignNode w.nodes (ancestorPathTags w.nodes parentTag) isWrite rangeOffset rangeLen n) =
      xs.filter (fun n => !(ancestorPathTags w.nodes parentTag).contains n.tag) := by
    intro isWrite xs hxs
    induction xs with
    | nil => rfl
    | cons x rest ih =>
      have hx := hxs x (List.mem_cons_self ..)
      simp only [List.filter_cons, hx, Bool.not_false, Bool.and_true]
      rw [ih (fun n hn => hxs n (List.mem_cons_of_mem _ hn))]
  have hmapEq : ∀ (isWrite : Bool) (step : Bool → TreeTagNode → Except RetagStepErr TreeTagNode)
      (xs : List TreeTagNode),
      (∀ n ∈ xs, isPrunedForeignNode w.nodes (ancestorPathTags w.nodes parentTag) isWrite rangeOffset rangeLen n = false) →
      mapNodesM (fun n =>
        if (ancestorPathTags w.nodes parentTag).contains n.tag then step true n
        else if isPrunedForeignNode w.nodes (ancestorPathTags w.nodes parentTag) isWrite rangeOffset rangeLen n then .ok n
        else step false n) xs =
      mapNodesM (fun n => step ((ancestorPathTags w.nodes parentTag).contains n.tag) n) xs := by
    intro isWrite step xs hxs
    induction xs with
    | nil => rfl
    | cons x rest ih =>
      have hx := hxs x (List.mem_cons_self ..)
      have hstepX : (if (ancestorPathTags w.nodes parentTag).contains x.tag then step true x
          else if isPrunedForeignNode w.nodes (ancestorPathTags w.nodes parentTag) isWrite rangeOffset rangeLen x then .ok x
          else step false x) = step ((ancestorPathTags w.nodes parentTag).contains x.tag) x := by
        cases (ancestorPathTags w.nodes parentTag).contains x.tag <;> simp [hx]
      simp only [mapNodesM, hstepX, ih (fun n hn => hxs n (List.mem_cons_of_mem _ hn))]
  unfold execFnEntryMutRetagPrunedSourceOrder execFnEntryMutRetagSourceOrder
  cases policy with
  | skipRetag => rfl
  | rustcNoWritable =>
    have hno : ∀ n ∈ w.nodes, isPrunedForeignNode w.nodes (ancestorPathTags w.nodes parentTag) false rangeOffset rangeLen n = false := hnoSkip
    cases findNode? w.nodes parentTag with
    | none => rfl
    | some _ =>
      cases hlen : (rangeLen == 0) with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hfiltEq false w.nodes hno,
          hmapEq false (fun isLoc n => stepNodeOnRangeRead w.activeProtectors isLoc rangeOffset rangeLen n) w.nodes hno]
  | writableChildWrite =>
    have hno : ∀ n ∈ w.nodes, isPrunedForeignNode w.nodes (ancestorPathTags w.nodes parentTag) true rangeOffset rangeLen n = false := hnoSkip
    cases findNode? w.nodes parentTag with
    | none => rfl
    | some _ =>
      cases hlen : (rangeLen == 0) with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases w.allocReadOnly with
        | true => rfl
        | false =>
          cases (requireInit && !w.pointeeInitialized) with
          | true => rfl
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [hfiltEq true w.nodes hno,
              hmapEq true (fun isLoc n => stepNodeOnRangeWrite w.activeProtectors isLoc rangeOffset rangeLen n) w.nodes hno]

/-- `SkipSelfAndChildren` subtree-pruning separation (`NormalTreeState.performAccess`, `LocationState.lean:76-88`):
1. Under a `.disabled` foreign ancestor (`sib 2 -> cell 3 -> protected .unique 4`, realistic `UnsafeCell`
   inside a disabled outer borrow), unpruned `execFnEntryMutRetagSourceOrder` falsely fails with
   `.protectedForeignConflict 4`, whereas pruned `execFnEntryMutRetagPrunedSourceOrder` SUCCEEDS on both
   `.rustcNoWritable` and `.writableChildWrite` and leaves tag `4` untouched.
2. Under a `.frozen` foreign ancestor (`sib 2 (.frozen) -> protected .unique 3`), `.frozen` skips its
   subtree ONLY on Read (`.rustcNoWritable` succeeds under pruning, fails without pruning), while on
   Write (`.writableChildWrite`) `.frozen` does NOT skip so both models report `.protectedForeignConflict 3`. -/
theorem execFnEntryMutRetagPrunedSourceOrder_skipSelfAndChildren_separation :
    let wDisSub : FnEntryBorrowWorld := {
      nodes := [
        ⟨0, none, .unique, 0, 4, none, true⟩,
        ⟨1, some 0, .unique, 0, 4, none, true⟩,
        ⟨2, some 0, .disabled, 0, 4, none, true⟩,
        ⟨3, some 2, .cell, 0, 4, none, true⟩,
        ⟨4, some 3, .unique, 0, 4, some 7, true⟩
      ]
      activeProtectors := [7]
      nextTag := 5
      nextProtector := 10
    }
    let wFrzSub : FnEntryBorrowWorld := {
      nodes := [
        ⟨0, none, .unique, 0, 4, none, true⟩,
        ⟨1, some 0, .unique, 0, 4, none, true⟩,
        ⟨2, some 0, .frozen, 0, 4, none, true⟩,
        ⟨3, some 2, .unique, 0, 4, some 7, true⟩
      ]
      activeProtectors := [7]
      nextTag := 4
      nextProtector := 10
    }
    execFnEntryMutRetagSourceOrder wDisSub 1 0 4 .rustcNoWritable = .error (.protectedForeignConflict 4) ∧
    execFnEntryMutRetagSourceOrder wDisSub 1 0 4 .writableChildWrite = .error (.protectedForeignConflict 4) ∧
    (execFnEntryMutRetagPrunedSourceOrder wDisSub 1 0 4 .rustcNoWritable).isOk = true ∧
    (execFnEntryMutRetagPrunedSourceOrder wDisSub 1 0 4 .writableChildWrite).isOk = true ∧
    execFnEntryMutRetagSourceOrder wFrzSub 1 0 4 .rustcNoWritable = .error (.protectedForeignConflict 3) ∧
    (execFnEntryMutRetagPrunedSourceOrder wFrzSub 1 0 4 .rustcNoWritable).isOk = true ∧
    execFnEntryMutRetagSourceOrder wFrzSub 1 0 4 .writableChildWrite = .error (.protectedForeignConflict 3) ∧
    execFnEntryMutRetagPrunedSourceOrder wFrzSub 1 0 4 .writableChildWrite = .error (.protectedForeignConflict 3) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### 2B. Static-Access Temporary Retag (`charon#1620`) & Syntactic `is_freeze` Static Mutability -/

/-- Type descriptor for static allocation mutability (`intern.rs:222-229`) and `FreezeVisitor` layout decomposition. -/
inductive StaticTyDesc where
  | freezeScalar (sizeBytes : Nat)
  | unsafeCell (sizeBytes : Nat)
  | padding (sizeBytes : Nat)
  | composite (totalSize : Nat) (fields : List (Nat × StaticTyDesc))
  deriving Repr, Inhabited

mutual
/-- Syntactic `ty.is_freeze` predicate (`rustc_const_eval/src/interpret/intern.rs:222-229`):
returns `false` whenever ANY field is an `UnsafeCell`, even a zero-sized `UnsafeCell<()>`. -/
def StaticTyDesc.isSyntacticFreeze : StaticTyDesc → Bool
  | .freezeScalar _ => true
  | .unsafeCell _ => false
  | .padding _ => true
  | .composite _ fields => fieldsSyntacticFreeze fields

def fieldsSyntacticFreeze : List (Nat × StaticTyDesc) → Bool
  | [] => true
  | (_, d) :: rest => d.isSyntacticFreeze && fieldsSyntacticFreeze rest
end

/-- Static allocation mutability set by `rustc_const_eval` during static interning:
derived from **syntactic** `isSyntacticFreeze` (never from non-empty `FreezeVisitor` segments). -/
def staticAllocMutability (desc : StaticTyDesc) : AllocMutability :=
  if desc.isSyntacticFreeze then .not else .mut

/-- Segment kind emitted by `Miri.TreeBorrows.FreezeVisitor` (`visit_freeze_sensitive`). -/
inductive StaticSegmentKind where
  | freeze
  | unsafeCell
  deriving DecidableEq, Repr, Inhabited

/-- Contiguous byte interval `[offset, offset + len)` classified as `.freeze` or `.unsafeCell`. -/
structure StaticFreezeSegment where
  offset : Nat
  len : Nat
  kind : StaticSegmentKind
  deriving DecidableEq, Repr, Inhabited

mutual
/-- Collect all non-zero-length `UnsafeCell` intervals (mirroring `FreezeVisitor.wholeUnsafeCell`,
which skips `0`-byte `UnsafeCell<()>` segments). -/
def collectNonZeroUnsafeCells (base : Nat) : StaticTyDesc → List (Nat × Nat)
  | .freezeScalar _ => []
  | .padding _ => []
  | .unsafeCell len => if len == 0 then [] else [(base, len)]
  | .composite _ fields => collectFieldsNonZeroUnsafeCells base fields

def collectFieldsNonZeroUnsafeCells (base : Nat) : List (Nat × StaticTyDesc) → List (Nat × Nat)
  | [] => []
  | (off, d) :: rest =>
    collectNonZeroUnsafeCells (base + off) d ++ collectFieldsNonZeroUnsafeCells base rest
end

def StaticTyDesc.totalByteSize : StaticTyDesc → Nat
  | .freezeScalar sz => sz
  | .unsafeCell sz => sz
  | .padding sz => sz
  | .composite total _ => total

private def buildFreezeSegmentsAux (cursor totalSize : Nat) : List (Nat × Nat) → List StaticFreezeSegment
  | [] =>
    if cursor < totalSize then [⟨cursor, totalSize - cursor, .freeze⟩] else []
  | (cellOff, cellLen) :: rest =>
    let lead := if cursor < cellOff then [⟨cursor, cellOff - cursor, .freeze⟩] else []
    let cell := [⟨cellOff, cellLen, .unsafeCell⟩]
    lead ++ cell ++ buildFreezeSegmentsAux (cellOff + cellLen) totalSize rest

/-- Decompose `desc` into `(totalSize, segments)` matching `Miri.TreeBorrows.FreezeVisitor`. -/
def staticFreezeSegments (desc : StaticTyDesc) : Nat × List StaticFreezeSegment :=
  let total := desc.totalByteSize
  (total, buildFreezeSegmentsAux 0 total (collectNonZeroUnsafeCells 0 desc))

/-- Per-segment Tree Borrows permission map on a static allocation. -/
structure StaticBorrowState where
  rootTag : Nat
  activeTag : Nat
  totalSize : Nat
  segments : List (StaticFreezeSegment × TreeBorrowPerm)
  deriving DecidableEq, Repr

/-- Preserved `charon#1620` static-temporary shared retag (`let _tmp = &STATIC; &raw const *_tmp`):
mints `.frozen` on `.freeze` segments and `.cell` on `.unsafeCell` segments. -/
def retagStaticPreservedAt (desc : StaticTyDesc) (rootTag tmpTag : Nat) : StaticBorrowState :=
  let (total, segs) := staticFreezeSegments desc
  { rootTag := rootTag
    activeTag := tmpTag
    totalSize := total
    segments := segs.map fun s =>
      (s, match s.kind with | .freeze => .frozen | .unsafeCell => .cell) }

/-- Pre-`#1620` erased raw address-of (`&raw const STATIC` without temporary shared retag):
retains root `.unique` permission across the entire static allocation. -/
def retagStaticErasedAt (desc : StaticTyDesc) (rootTag : Nat) : StaticBorrowState :=
  let total := desc.totalByteSize
  { rootTag := rootTag
    activeTag := rootTag
    totalSize := total
    segments := if total == 0 then [] else [(⟨0, total, .unsafeCell⟩, .unique)] }

/-- Outcome of writing through `(&raw const STATIC).cast_mut()` at `[writeOff, writeOff + writeLen)`. -/
inductive StaticWriteOutcome where
  | ok
  | readOnlyAlloc
  | ub
  | outOfBounds
  deriving DecidableEq, Repr

/-- Tree-Borrows-only write check (without Miri allocation mutability check). -/
def evalRawMutStaticWriteTB (st : StaticBorrowState) (writeOff writeLen : Nat) : StaticWriteOutcome :=
  if writeOff + writeLen > st.totalSize then .outOfBounds
  else if writeLen == 0 then .ok
  else
    let blocked := st.segments.any fun (seg, perm) =>
      rangesOverlap writeOff writeLen seg.offset seg.len &&
        match perm with
        | .frozen | .disabled => true
        | _ => false
    if blocked then .ub else .ok

/-- Full Miri static write check: enforces `staticAllocMutability desc` first, then Tree Borrows. -/
def evalRawMutStaticWriteMiri (desc : StaticTyDesc) (st : StaticBorrowState)
    (writeOff writeLen : Nat) : StaticWriteOutcome :=
  if writeOff + writeLen > st.totalSize then .outOfBounds
  else if staticAllocMutability desc == .not then .readOnlyAlloc
  else evalRawMutStaticWriteTB st writeOff writeLen

private theorem rangesOverlap_one_true {writeOff segOff segLen : Nat}
    (hlo : segOff ≤ writeOff) (hhi : writeOff < segOff + segLen) :
    rangesOverlap writeOff 1 segOff segLen = true := by
  unfold rangesOverlap
  have h1 : (1 != 0) = true := rfl
  have h2 : (segLen != 0) = true := bne_iff_ne.2 (by omega)
  have h3 : decide (writeOff < segOff + segLen) = true := decide_eq_true hhi
  have h4 : decide (segOff < writeOff + 1) = true := decide_eq_true (by omega)
  simp only [h1, h2, h3, h4, Bool.and_self]

private theorem rangesOverlap_one_false_of_ge {writeOff segOff segLen : Nat}
    (hge : segOff + segLen ≤ writeOff) :
    rangesOverlap writeOff 1 segOff segLen = false := by
  unfold rangesOverlap
  have h3 : decide (writeOff < segOff + segLen) = false := decide_eq_false (by omega)
  simp only [h3, Bool.and_false, Bool.false_and]

private theorem rangesOverlap_one_false_of_lt {writeOff segOff segLen : Nat}
    (hlt : writeOff + 1 ≤ segOff) :
    rangesOverlap writeOff 1 segOff segLen = false := by
  unfold rangesOverlap
  have h4 : decide (segOff < writeOff + 1) = false := decide_eq_false (by omega)
  simp only [h4, Bool.and_false]

theorem static_pureFreeze_preserved_ub_vs_erased_unsound
    (sz rootTag tmpTag writeOff : Nat) (hsz : 0 < sz) (hoff : writeOff < sz) :
    evalRawMutStaticWriteTB (retagStaticPreservedAt (.freezeScalar sz) rootTag tmpTag) writeOff 1 = .ub ∧
    evalRawMutStaticWriteTB (retagStaticErasedAt (.freezeScalar sz) rootTag) writeOff 1 = .ok := by
  have hle : ¬ (writeOff + 1 > sz) := by omega
  have hnz : (sz == 0) = false := beq_false_of_ne (by omega)
  have hov : rangesOverlap writeOff 1 0 sz = true :=
    rangesOverlap_one_true (Nat.zero_le _) (by omega)
  constructor
  · simp [evalRawMutStaticWriteTB, retagStaticPreservedAt, staticFreezeSegments,
      StaticTyDesc.totalByteSize, collectNonZeroUnsafeCells, buildFreezeSegmentsAux, hsz, hle, hov]
  · simp [evalRawMutStaticWriteTB, retagStaticErasedAt, StaticTyDesc.totalByteSize, hnz, hle]

theorem static_pureFreeze_erased_write_caught_by_readOnly_alloc
    (sz rootTag writeOff : Nat) (hoff : writeOff < sz) :
    staticAllocMutability (.freezeScalar sz) = .not ∧
    evalRawMutStaticWriteMiri (.freezeScalar sz)
      (retagStaticErasedAt (.freezeScalar sz) rootTag) writeOff 1 = .readOnlyAlloc := by
  have hle : ¬ (writeOff + 1 > sz) := by omega
  refine ⟨rfl, ?_⟩
  simp [evalRawMutStaticWriteMiri, retagStaticErasedAt, StaticTyDesc.totalByteSize,
    staticAllocMutability, StaticTyDesc.isSyntacticFreeze, hle]

theorem static_pureUnsafeCell_preserved_write_ok
    (sz rootTag tmpTag writeOff : Nat) (hsz : 0 < sz) (hoff : writeOff < sz) :
    staticAllocMutability (.unsafeCell sz) = .mut ∧
    evalRawMutStaticWriteMiri (.unsafeCell sz)
      (retagStaticPreservedAt (.unsafeCell sz) rootTag tmpTag) writeOff 1 = .ok := by
  have hle : ¬ (writeOff + 1 > sz) := by omega
  have hnz : (sz == 0) = false := beq_false_of_ne (by omega)
  refine ⟨rfl, ?_⟩
  simp [evalRawMutStaticWriteMiri, evalRawMutStaticWriteTB, retagStaticPreservedAt,
    staticFreezeSegments, StaticTyDesc.totalByteSize, collectNonZeroUnsafeCells,
    buildFreezeSegmentsAux, staticAllocMutability, StaticTyDesc.isSyntacticFreeze, hnz, hle]

/-- Universal mixed-composite static `(Freeze[frzLen], UnsafeCell[cellLen], Padding[tailLen])`:
`staticAllocMutability = .mut`, so Miri allows writing to the allocation; preserved `#1620` retag
catches writes to BOTH leading `Freeze`/inter-field padding (`writeOff < frzLen`) AND trailing padding
(`frzLen + cellLen ≤ writeOff < frzLen + cellLen + tailLen`) with `.ub`, whereas erased `&raw const`
unsoundly returns `.ok`. -/
theorem static_mixed_miri_separation
    (frzLen cellLen tailLen rootTag tmpTag writeOff : Nat)
    (hfrz : 0 < frzLen) (hcell : 0 < cellLen)
    (hwrite : writeOff < frzLen ∨ (frzLen + cellLen ≤ writeOff ∧ writeOff < frzLen + cellLen + tailLen)) :
    let total := frzLen + cellLen + tailLen
    let desc : StaticTyDesc :=
      .composite total [(0, .freezeScalar frzLen), (frzLen, .unsafeCell cellLen), (frzLen + cellLen, .padding tailLen)]
    staticAllocMutability desc = .mut ∧
    evalRawMutStaticWriteMiri desc (retagStaticPreservedAt desc rootTag tmpTag) writeOff 1 = .ub ∧
    evalRawMutStaticWriteMiri desc (retagStaticErasedAt desc rootTag) writeOff 1 = .ok := by
  have htotalNz : (frzLen + cellLen + tailLen == 0) = false := beq_false_of_ne (by omega)
  have hcellNz : (cellLen == 0) = false := beq_false_of_ne (by omega)
  have hle : ¬ (writeOff + 1 > frzLen + cellLen + tailLen) := by omega
  have hmut : staticAllocMutability
      (.composite (frzLen + cellLen + tailLen)
        [(0, .freezeScalar frzLen), (frzLen, .unsafeCell cellLen), (frzLen + cellLen, .padding tailLen)]) = .mut := by
    simp [staticAllocMutability, StaticTyDesc.isSyntacticFreeze, fieldsSyntacticFreeze]
  refine ⟨hmut, ?_, ?_⟩
  · simp only [evalRawMutStaticWriteMiri, evalRawMutStaticWriteTB, retagStaticPreservedAt,
      staticFreezeSegments, StaticTyDesc.totalByteSize, collectNonZeroUnsafeCells,
      collectFieldsNonZeroUnsafeCells, Nat.zero_add, hcellNz, Bool.false_eq_true, ↓reduceIte,
      List.nil_append, List.append_nil, buildFreezeSegmentsAux, hfrz, hmut, hle]
    rcases hwrite with hlead | ⟨htailLo, htailHi⟩
    · have hovLead : rangesOverlap writeOff 1 0 frzLen = true :=
        rangesOverlap_one_true (Nat.zero_le _) (by omega)
      simp [hovLead]
    · have htailLt : frzLen + cellLen < frzLen + cellLen + tailLen := by omega
      have hsub : frzLen + cellLen + tailLen - (frzLen + cellLen) = tailLen := by omega
      have hovTail : rangesOverlap writeOff 1 (frzLen + cellLen) tailLen = true :=
        rangesOverlap_one_true htailLo htailHi
      simp [htailLt, hsub, hovTail]
  · simp [evalRawMutStaticWriteMiri, evalRawMutStaticWriteTB, retagStaticErasedAt,
      StaticTyDesc.totalByteSize, htotalNz, hmut, hle]

/-- Universal mixed-composite static interior-mutability soundness: writing inside the `UnsafeCell`
region `[frzLen, frzLen + cellLen)` succeeds under preserved `#1620` retag. -/
theorem static_mixed_miri_unsafeCell_write_ok
    (frzLen cellLen tailLen rootTag tmpTag writeOff : Nat)
    (hfrz : 0 < frzLen) (hcell : 0 < cellLen)
    (hlo : frzLen ≤ writeOff) (hhi : writeOff < frzLen + cellLen) :
    let total := frzLen + cellLen + tailLen
    let desc : StaticTyDesc :=
      .composite total [(0, .freezeScalar frzLen), (frzLen, .unsafeCell cellLen), (frzLen + cellLen, .padding tailLen)]
    evalRawMutStaticWriteMiri desc (retagStaticPreservedAt desc rootTag tmpTag) writeOff 1 = .ok := by
  have hcellNz : (cellLen == 0) = false := beq_false_of_ne (by omega)
  have hle : ¬ (writeOff + 1 > frzLen + cellLen + tailLen) := by omega
  have hmut : staticAllocMutability
      (.composite (frzLen + cellLen + tailLen)
        [(0, .freezeScalar frzLen), (frzLen, .unsafeCell cellLen), (frzLen + cellLen, .padding tailLen)]) = .mut := by
    simp [staticAllocMutability, StaticTyDesc.isSyntacticFreeze, fieldsSyntacticFreeze]
  have hnoLead : rangesOverlap writeOff 1 0 frzLen = false :=
    rangesOverlap_one_false_of_ge (by omega)
  by_cases htail : tailLen = 0
  · subst htail
    simp only [Nat.add_zero] at hmut hle
    simp [evalRawMutStaticWriteMiri, evalRawMutStaticWriteTB, retagStaticPreservedAt,
      staticFreezeSegments, StaticTyDesc.totalByteSize, collectNonZeroUnsafeCells,
      collectFieldsNonZeroUnsafeCells, hcellNz, buildFreezeSegmentsAux, hfrz, hmut, hle, hnoLead]
  · have htailLt : frzLen + cellLen < frzLen + cellLen + tailLen := by omega
    have hsub : frzLen + cellLen + tailLen - (frzLen + cellLen) = tailLen := by omega
    have hnoTail : rangesOverlap writeOff 1 (frzLen + cellLen) tailLen = false :=
      rangesOverlap_one_false_of_lt (by omega)
    simp [evalRawMutStaticWriteMiri, evalRawMutStaticWriteTB, retagStaticPreservedAt,
      staticFreezeSegments, StaticTyDesc.totalByteSize, collectNonZeroUnsafeCells,
      collectFieldsNonZeroUnsafeCells, hcellNz, buildFreezeSegmentsAux, hfrz, hmut, hle,
      htailLt, hsub, hnoLead, hnoTail]

/-- Zero-sized `UnsafeCell<()>` composite static `(Freeze[frzLen], UnsafeCell<()>)`:
`FreezeVisitor` emits zero `.unsafeCell` segments (`[⟨0, frzLen, .freeze⟩]`), yet syntactic
`isSyntacticFreeze = false` sets `staticAllocMutability = .mut` (`intern.rs:222-229`), so
preserved `#1620` retag faults with `.ub` on mutating the `Freeze` field while pre-`#1620`
erasure unsoundly succeeds with `.ok`. -/
theorem static_zstUnsafeCell_composite_miri_separation
    (frzLen rootTag tmpTag writeOff : Nat) (hfrz : 0 < frzLen) (hoff : writeOff < frzLen) :
    let desc : StaticTyDesc :=
      .composite frzLen [(0, .freezeScalar frzLen), (frzLen, .unsafeCell 0)]
    (staticFreezeSegments desc).2 = [⟨0, frzLen, .freeze⟩] ∧
    desc.isSyntacticFreeze = false ∧
    staticAllocMutability desc = .mut ∧
    evalRawMutStaticWriteMiri desc (retagStaticPreservedAt desc rootTag tmpTag) writeOff 1 = .ub ∧
    evalRawMutStaticWriteMiri desc (retagStaticErasedAt desc rootTag) writeOff 1 = .ok := by
  have hfrzNz : (frzLen == 0) = false := beq_false_of_ne (by omega)
  have hle : ¬ (writeOff + 1 > frzLen) := by omega
  have hov : rangesOverlap writeOff 1 0 frzLen = true :=
    rangesOverlap_one_true (Nat.zero_le _) (by omega)
  have hsyn : (StaticTyDesc.composite frzLen [(0, .freezeScalar frzLen), (frzLen, .unsafeCell 0)]).isSyntacticFreeze = false := by
    simp [StaticTyDesc.isSyntacticFreeze, fieldsSyntacticFreeze]
  have hmut : staticAllocMutability (.composite frzLen [(0, .freezeScalar frzLen), (frzLen, .unsafeCell 0)]) = .mut := by
    simp [staticAllocMutability, hsyn]
  have hsegs : (staticFreezeSegments (.composite frzLen [(0, .freezeScalar frzLen), (frzLen, .unsafeCell 0)])).2 =
      [⟨0, frzLen, .freeze⟩] := by
    simp [staticFreezeSegments, StaticTyDesc.totalByteSize, collectNonZeroUnsafeCells,
      collectFieldsNonZeroUnsafeCells, buildFreezeSegmentsAux, hfrz]
  refine ⟨hsegs, hsyn, hmut, ?_, ?_⟩
  · simp [evalRawMutStaticWriteMiri, evalRawMutStaticWriteTB, retagStaticPreservedAt,
      staticFreezeSegments, StaticTyDesc.totalByteSize, collectNonZeroUnsafeCells,
      collectFieldsNonZeroUnsafeCells, buildFreezeSegmentsAux, hfrz, hmut, hle, hov]
  · simp [evalRawMutStaticWriteMiri, evalRawMutStaticWriteTB, retagStaticErasedAt,
      StaticTyDesc.totalByteSize, hfrzNz, hmut, hle]

/-! ## Part 3: `[T; N]` `Sized` Fast-Path (`lean-miri#79`), Auto-Trait `dyn Send` VTables (`lean-miri#75`), & Null-VTable Precedence (`lean-miri#82`) -/

/-! ### 3A. Syntactic `Sized` Fast-Path, Custom-DST Metadata Tails, and `getAllocInfo`-Backed `validateSafeThinRef` -/

/-- Structural Rust type model for layout computation, `O(1)` syntactic `Sized` classification,
custom DST metadata tails, and recursive pointee byte validation. -/
inductive ProtoTy where
  | unit
  | never
  | bool
  | char
  | uint (sizeBytes : Nat)
  | fnPtr
  | ref (mutable : Bool) (pointee : ProtoTy)
  | rawPtr (mutable : Bool) (pointee : ProtoTy)
  | array (elem : ProtoTy) (len : Nat)
  | slice (elem : ProtoTy)
  | str
  | dynamic (traitName : String)
  | foreign
  | tuple (fields : List ProtoTy)
  | adt (name : String) (fields : List ProtoTy)
  deriving Repr, Inhabited

/-- Pointer metadata shape required for an unsized pointee tail. -/
inductive DstMetadataKind where
  | sliceLen
  | dynVTable
  | foreignNone
  deriving DecidableEq, Repr, Inhabited

mutual
/-- `O(1)` syntactic `Sized` check (`lean-miri#79`): `.array _ _` immediately returns `true`
without recursing into the element type or computing layout. -/
def isSyntacticallySized : ProtoTy → Bool
  | .unit => true
  | .never => true
  | .bool => true
  | .char => true
  | .uint _ => true
  | .fnPtr => true
  | .ref _ _ => true
  | .rawPtr _ _ => true
  | .array _ _ => true
  | .slice _ => false
  | .str => false
  | .dynamic _ => false
  | .foreign => false
  | .tuple fields => fieldsTailSyntacticallySized fields
  | .adt _ fields => fieldsTailSyntacticallySized fields

def fieldsTailSyntacticallySized : List ProtoTy → Bool
  | [] => true
  | [last] => isSyntacticallySized last
  | _ :: rest => fieldsTailSyntacticallySized rest
end

mutual
/-- Unsized metadata tail classification for a pointee type (including custom struct/tuple DSTs). -/
def unsizedMetadataTail : ProtoTy → Option DstMetadataKind
  | .unit | .never | .bool | .char | .uint _ | .fnPtr | .ref _ _ | .rawPtr _ _ | .array _ _ => none
  | .slice _ | .str => some .sliceLen
  | .dynamic _ => some .dynVTable
  | .foreign => some .foreignNone
  | .tuple fields => fieldsUnsizedMetadataTail fields
  | .adt _ fields => fieldsUnsizedMetadataTail fields

def fieldsUnsizedMetadataTail : List ProtoTy → Option DstMetadataKind
  | [] => none
  | [last] => unsizedMetadataTail last
  | _ :: rest => fieldsUnsizedMetadataTail rest
end

mutual
/-- Extract the existential trait name of a `dyn`-tailed unsized type (or `none` otherwise). -/
def unsizedDynTailTrait? : ProtoTy → Option String
  | .unit | .never | .bool | .char | .uint _ | .fnPtr | .ref _ _ | .rawPtr _ _
  | .array _ _ | .slice _ | .str | .foreign => none
  | .dynamic traitName => some traitName
  | .tuple fields => fieldsUnsizedDynTailTrait? fields
  | .adt _ fields => fieldsUnsizedDynTailTrait? fields

def fieldsUnsizedDynTailTrait? : List ProtoTy → Option String
  | [] => none
  | [last] => unsizedDynTailTrait? last
  | _ :: rest => fieldsUnsizedDynTailTrait? rest
end

mutual
theorem isSyntacticallySized_eq_metadataTail_isNone :
    ∀ (ty : ProtoTy), isSyntacticallySized ty = (unsizedMetadataTail ty).isNone
  | .unit | .never | .bool | .char | .uint _ | .fnPtr | .ref _ _ | .rawPtr _ _
  | .array _ _ | .slice _ | .str | .dynamic _ | .foreign => rfl
  | .tuple fields => fieldsTailSized_eq_metadataTail_isNone fields
  | .adt _ fields => fieldsTailSized_eq_metadataTail_isNone fields

theorem fieldsTailSized_eq_metadataTail_isNone :
    ∀ (fields : List ProtoTy),
      fieldsTailSyntacticallySized fields = (fieldsUnsizedMetadataTail fields).isNone
  | [] => rfl
  | [last] => isSyntacticallySized_eq_metadataTail_isNone last
  | _ :: a :: rest => fieldsTailSized_eq_metadataTail_isNone (a :: rest)
end

mutual
theorem unsizedDynTailTrait?_isSome_eq_dynMeta :
    ∀ (ty : ProtoTy),
      (unsizedDynTailTrait? ty).isSome = (unsizedMetadataTail ty == some .dynVTable)
  | .unit | .never | .bool | .char | .uint _ | .fnPtr | .ref _ _ | .rawPtr _ _
  | .array _ _ | .slice _ | .str | .dynamic _ | .foreign => rfl
  | .tuple fields => fieldsDynTailTrait?_isSome_eq_dynMeta fields
  | .adt _ fields => fieldsDynTailTrait?_isSome_eq_dynMeta fields

theorem fieldsDynTailTrait?_isSome_eq_dynMeta :
    ∀ (fields : List ProtoTy),
      (fieldsUnsizedDynTailTrait? fields).isSome = (fieldsUnsizedMetadataTail fields == some .dynVTable)
  | [] => rfl
  | [last] => unsizedDynTailTrait?_isSome_eq_dynMeta last
  | _ :: a :: rest => fieldsDynTailTrait?_isSome_eq_dynMeta (a :: rest)
end

/-- Maximum legal Rust object size on 64-bit targets (`isize::MAX = 2^63 - 1`). -/
def maxObjectSize64 : Nat := 2^63 - 1

/-- 64-bit `usize::MAX` (`2^64 - 1`). -/
def usizeMax64 : Nat := 2^64 - 1

/-- Layout computation errors. -/
inductive LayoutErr where
  | layoutOverflow
  | unsizedField
  | invalidScalarSize (sz : Nat)
  deriving DecidableEq, Repr

/-- Computed layout summary for `ProtoTy`. -/
structure ProtoLayout where
  sizeBytes : Nat
  alignBytes : Nat
  isSized : Bool
  isInhabited : Bool
  metaKind : Option DstMetadataKind := none
  deriving DecidableEq, Repr

/-- Align `offset` up to the next multiple of `align` (assuming `align ≥ 1`). -/
def alignUpNat (offset align : Nat) : Nat :=
  if align ≤ 1 then offset
  else
    let rem := offset % align
    if rem == 0 then offset else offset + (align - rem)

mutual
/-- Compute layout of `ProtoTy` (mirroring `rustc` `layout_of`). -/
def computeTyLayout : ProtoTy → Except LayoutErr ProtoLayout
  | .unit => .ok ⟨0, 1, true, true, none⟩
  | .never => .ok ⟨0, 1, true, false, none⟩
  | .bool => .ok ⟨1, 1, true, true, none⟩
  | .char => .ok ⟨4, 4, true, true, none⟩
  | .uint sz =>
    if sz == 1 || sz == 2 || sz == 4 || sz == 8 || sz == 16 then
      .ok ⟨sz, sz, true, true, none⟩
    else .error (.invalidScalarSize sz)
  | .fnPtr => .ok ⟨8, 8, true, true, none⟩
  | .ref _ inner =>
    match unsizedMetadataTail inner with
    | none | some .foreignNone => .ok ⟨8, 8, true, true, none⟩
    | some .sliceLen | some .dynVTable => .ok ⟨16, 8, true, true, none⟩
  | .rawPtr _ inner =>
    match unsizedMetadataTail inner with
    | none | some .foreignNone => .ok ⟨8, 8, true, true, none⟩
    | some .sliceLen | some .dynVTable => .ok ⟨16, 8, true, true, none⟩
  | .array elem len =>
    match computeTyLayout elem with
    | .error e => .error e
    | .ok el =>
      if !el.isSized then .error .unsizedField
      else
        let total := el.sizeBytes * len
        if total > maxObjectSize64 then .error .layoutOverflow
        else .ok ⟨total, el.alignBytes, true, len == 0 || el.isInhabited, none⟩
  | .slice elem =>
    match computeTyLayout elem with
    | .error e => .error e
    | .ok el =>
      if !el.isSized then .error .unsizedField
      else .ok ⟨0, el.alignBytes, false, true, some .sliceLen⟩
  | .str => .ok ⟨0, 1, false, true, some .sliceLen⟩
  | .dynamic _ => .ok ⟨0, 1, false, true, some .dynVTable⟩
  | .foreign => .ok ⟨0, 1, false, true, some .foreignNone⟩
  | .tuple fields => computeFieldsLayout 0 1 true fields
  | .adt _ fields => computeFieldsLayout 0 1 true fields

def computeFieldsLayout (curSize curAlign : Nat) (curInhab : Bool) :
    List ProtoTy → Except LayoutErr ProtoLayout
  | [] =>
    let finalSize := alignUpNat curSize curAlign
    if finalSize > maxObjectSize64 then .error .layoutOverflow
    else .ok ⟨finalSize, curAlign, true, curInhab, none⟩
  | [last] =>
    match computeTyLayout last with
    | .error e => .error e
    | .ok l =>
      let off := alignUpNat curSize l.alignBytes
      let nextSize := off + l.sizeBytes
      let nextAlign := Nat.max curAlign l.alignBytes
      let finalSize := if l.isSized then alignUpNat nextSize nextAlign else nextSize
      if finalSize > maxObjectSize64 then .error .layoutOverflow
      else .ok ⟨finalSize, nextAlign, l.isSized, curInhab && l.isInhabited, l.metaKind⟩
  | f :: rest =>
    match computeTyLayout f with
    | .error e => .error e
    | .ok fl =>
      if !fl.isSized then .error .unsizedField
      else
        let off := alignUpNat curSize fl.alignBytes
        let nextSize := off + fl.sizeBytes
        if nextSize > maxObjectSize64 then .error .layoutOverflow
        else computeFieldsLayout nextSize (Nat.max curAlign fl.alignBytes) (curInhab && fl.isInhabited) rest
end

mutual
theorem isSyntacticallySized_eq_of_computeTyLayout_ok :
    ∀ (ty : ProtoTy) {lay : ProtoLayout}, computeTyLayout ty = .ok lay →
      isSyntacticallySized ty = lay.isSized ∧ unsizedMetadataTail ty = lay.metaKind
  | .unit, lay, h => by simp [computeTyLayout] at h; subst h; exact ⟨rfl, rfl⟩
  | .never, lay, h => by simp [computeTyLayout] at h; subst h; exact ⟨rfl, rfl⟩
  | .bool, lay, h => by simp [computeTyLayout] at h; subst h; exact ⟨rfl, rfl⟩
  | .char, lay, h => by simp [computeTyLayout] at h; subst h; exact ⟨rfl, rfl⟩
  | .uint sz, lay, h => by
    unfold computeTyLayout at h
    split at h
    · injection h with h; subst h; exact ⟨rfl, rfl⟩
    · cases h
  | .fnPtr, lay, h => by simp [computeTyLayout] at h; subst h; exact ⟨rfl, rfl⟩
  | .ref _ inner, lay, h => by
    unfold computeTyLayout at h
    split at h <;> (injection h with h; subst h; exact ⟨rfl, rfl⟩)
  | .rawPtr _ inner, lay, h => by
    unfold computeTyLayout at h
    split at h <;> (injection h with h; subst h; exact ⟨rfl, rfl⟩)
  | .array elem len, lay, h => by
    unfold computeTyLayout at h
    cases hl : computeTyLayout elem with
    | error _ => simp [hl] at h
    | ok el =>
      simp only [hl] at h
      split at h
      · cases h
      · split at h
        · cases h
        · injection h with h; subst h; exact ⟨rfl, rfl⟩
  | .slice elem, lay, h => by
    unfold computeTyLayout at h
    cases hl : computeTyLayout elem with
    | error _ => simp [hl] at h
    | ok el =>
      simp only [hl] at h
      split at h
      · cases h
      · injection h with h; subst h; exact ⟨rfl, rfl⟩
  | .str, lay, h => by simp [computeTyLayout] at h; subst h; exact ⟨rfl, rfl⟩
  | .dynamic _, lay, h => by simp [computeTyLayout] at h; subst h; exact ⟨rfl, rfl⟩
  | .foreign, lay, h => by simp [computeTyLayout] at h; subst h; exact ⟨rfl, rfl⟩
  | .tuple fields, lay, h => fieldsTailSyntacticallySized_eq_of_ok 0 1 true fields h
  | .adt _ fields, lay, h => fieldsTailSyntacticallySized_eq_of_ok 0 1 true fields h

theorem fieldsTailSyntacticallySized_eq_of_ok (curSize curAlign : Nat) (curInhab : Bool) :
    ∀ (fields : List ProtoTy) {lay : ProtoLayout},
      computeFieldsLayout curSize curAlign curInhab fields = .ok lay →
      fieldsTailSyntacticallySized fields = lay.isSized ∧
      fieldsUnsizedMetadataTail fields = lay.metaKind
  | [], lay, h => by
    unfold computeFieldsLayout at h
    dsimp only at h
    split at h
    · cases h
    · injection h with h; subst h; exact ⟨rfl, rfl⟩
  | [last], lay, h => by
    unfold computeFieldsLayout at h
    cases hl : computeTyLayout last with
    | error _ => simp [hl] at h
    | ok l =>
      simp only [hl] at h
      split at h <;> split at h
      · cases h
      · injection h with h; subst h
        simpa [fieldsTailSyntacticallySized, fieldsUnsizedMetadataTail] using
          isSyntacticallySized_eq_of_computeTyLayout_ok last hl
      · cases h
      · injection h with h; subst h
        simpa [fieldsTailSyntacticallySized, fieldsUnsizedMetadataTail] using
          isSyntacticallySized_eq_of_computeTyLayout_ok last hl
  | f :: a :: rest, lay, h => by
    unfold computeFieldsLayout at h
    cases hf : computeTyLayout f with
    | error _ => simp [hf] at h
    | ok fl =>
      simp only [hf] at h
      split at h
      · cases h
      · split at h
        · cases h
        · exact fieldsTailSyntacticallySized_eq_of_ok _ _ _ (a :: rest) h
end

/-- Pointer width layout fidelity: thin references / raw pointers (`Sized` or `extern type` pointee)
occupy 8 bytes, whereas slice / `str` / `dyn` wide references and raw pointers occupy 16 bytes
(`ScalarPair`, still `isSized = true`, `metaKind = none`). -/
theorem computeTyLayout_widePtr_vs_thinPtr_size :
    computeTyLayout (.ref false (.uint 4)) = .ok ⟨8, 8, true, true, none⟩ ∧
    computeTyLayout (.ref false .foreign) = .ok ⟨8, 8, true, true, none⟩ ∧
    computeTyLayout (.rawPtr false (.uint 4)) = .ok ⟨8, 8, true, true, none⟩ ∧
    computeTyLayout (.ref false (.slice (.uint 4))) = .ok ⟨16, 8, true, true, none⟩ ∧
    computeTyLayout (.ref false .str) = .ok ⟨16, 8, true, true, none⟩ ∧
    computeTyLayout (.ref false (.dynamic "Send")) = .ok ⟨16, 8, true, true, none⟩ ∧
    computeTyLayout (.rawPtr false (.slice (.uint 4))) = .ok ⟨16, 8, true, true, none⟩ ∧
    computeTyLayout (.rawPtr false (.dynamic "Send")) = .ok ⟨16, 8, true, true, none⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Raw pointer representation for Part 3A metadata-shape validation. -/
inductive RawPtrVal where
  | thin (addr : UInt64)
  | wideSlice (addr len : UInt64)
  | wideDyn (addr vtableAddr : UInt64)
  deriving DecidableEq, Repr

/-- Errors emitted by raw-pointer shape/layout validation. -/
inductive RawPtrErr where
  | layoutFailed (err : LayoutErr)
  | expectedThinPtr
  | expectedWideSliceMeta
  | expectedWideDynMeta
  deriving DecidableEq, Repr

private def checkRawPtrShape (metaKind : Option DstMetadataKind) (ptr : RawPtrVal) :
    Except RawPtrErr Unit :=
  match metaKind, ptr with
  | none, .thin _ => .ok ()
  | some .foreignNone, .thin _ => .ok ()
  | some .sliceLen, .wideSlice _ _ => .ok ()
  | some .dynVTable, .wideDyn _ _ => .ok ()
  | none, _ => .error .expectedThinPtr
  | some .foreignNone, _ => .error .expectedThinPtr
  | some .sliceLen, _ => .error .expectedWideSliceMeta
  | some .dynVTable, _ => .error .expectedWideDynMeta

/-- `lean-miri#79` fast-path raw pointer validator:
if `isSyntacticallySized pointee = true`, skips `computeTyLayout` completely (`O(1)` on `[T; N]`);
if unsized, queries `computeTyLayout` first (matching upstream layout-overflow rejection on unsized DSTs). -/
def validateRawPtrFastPath (pointee : ProtoTy) (ptr : RawPtrVal) : Except RawPtrErr Unit :=
  if isSyntacticallySized pointee then
    checkRawPtrShape none ptr
  else
    match computeTyLayout pointee with
    | .error e => .error (.layoutFailed e)
    | .ok lay => checkRawPtrShape lay.metaKind ptr

/-- Pre-`#79` layout-first raw pointer validator: unconditionally computes `computeTyLayout` first. -/
def validateRawPtrLayoutFirst (pointee : ProtoTy) (ptr : RawPtrVal) : Except RawPtrErr Unit :=
  match computeTyLayout pointee with
  | .error e => .error (.layoutFailed e)
  | .ok lay => checkRawPtrShape lay.metaKind ptr

theorem validateRawPtrFastPath_eq_layoutFirst_of_layoutOk
    (pointee : ProtoTy) (ptr : RawPtrVal) {lay : ProtoLayout}
    (hlay : computeTyLayout pointee = .ok lay) :
    validateRawPtrFastPath pointee ptr = validateRawPtrLayoutFirst pointee ptr := by
  rcases isSyntacticallySized_eq_of_computeTyLayout_ok pointee hlay with ⟨hs, hm⟩
  have hmNone := isSyntacticallySized_eq_metadataTail_isNone pointee
  unfold validateRawPtrFastPath validateRawPtrLayoutFirst
  rw [hlay]
  cases hsz : isSyntacticallySized pointee with
  | true =>
    simp only [↓reduceIte]
    rw [hsz] at hmNone
    cases htail : unsizedMetadataTail pointee with
    | none => rw [← hm, htail]
    | some _ => rw [htail] at hmNone; cases hmNone
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]

theorem validateRawPtrFastPath_eq_layoutFirst_of_unsized
    (pointee : ProtoTy) (ptr : RawPtrVal) (hunsized : isSyntacticallySized pointee = false) :
    validateRawPtrFastPath pointee ptr = validateRawPtrLayoutFirst pointee ptr := by
  simp [validateRawPtrFastPath, validateRawPtrLayoutFirst, hunsized]

theorem validateRawPtrFastPath_ne_layoutFirst_imp
    (pointee : ProtoTy) (ptr : RawPtrVal)
    (hne : validateRawPtrFastPath pointee ptr ≠ validateRawPtrLayoutFirst pointee ptr) :
    isSyntacticallySized pointee = true ∧ ∃ e, computeTyLayout pointee = .error e := by
  cases hsz : isSyntacticallySized pointee with
  | false =>
    exact False.elim (hne (validateRawPtrFastPath_eq_layoutFirst_of_unsized pointee ptr hsz))
  | true =>
    refine ⟨rfl, ?_⟩
    cases hlay : computeTyLayout pointee with
    | ok lay =>
      exact False.elim (hne (validateRawPtrFastPath_eq_layoutFirst_of_layoutOk pointee ptr hlay))
    | error e => exact ⟨e, rfl⟩

/-- Separation witness (`lean-miri#79`): `*const [u8; usize::MAX]` is syntactically `Sized`,
so fast-path accepts `.thin addr` while layout-first rejects with `.layoutFailed .layoutOverflow`. -/
theorem oversized_array_rawPtr_separation (addr : UInt64) :
    validateRawPtrFastPath (.array (.uint 1) usizeMax64) (.thin addr) = .ok () ∧
    validateRawPtrLayoutFirst (.array (.uint 1) usizeMax64) (.thin addr) =
      .error (.layoutFailed .layoutOverflow) := by
  have hlay : computeTyLayout (.array (.uint 1) usizeMax64) = .error .layoutOverflow := by
    simp [computeTyLayout, maxObjectSize64, usizeMax64]
  exact ⟨rfl, by simp [validateRawPtrLayoutFirst, hlay]⟩

theorem slice_dst_rawPtr_requires_wideSliceMeta (addr len : UInt64) :
    validateRawPtrFastPath (.slice (.uint 1)) (.thin addr) = .error .expectedWideSliceMeta ∧
    validateRawPtrFastPath (.slice (.uint 1)) (.wideSlice addr len) = .ok () := by
  exact ⟨rfl, rfl⟩

/-- Unsized pointees with overflowing layouts (`*const ([u8; usize::MAX], [u8])` and
`*const [[u8; usize::MAX]]`) are rejected identically by both validators (matching upstream Miri). -/
theorem unsized_rawPtr_layoutOverflow_rejected_like_upstream (addr len : UInt64) :
    let customDst := ProtoTy.tuple [.array (.uint 1) usizeMax64, .slice (.uint 1)]
    let sliceOfOversized := ProtoTy.slice (.array (.uint 1) usizeMax64)
    validateRawPtrFastPath customDst (.wideSlice addr len) = .error (.layoutFailed .layoutOverflow) ∧
    validateRawPtrLayoutFirst customDst (.wideSlice addr len) = .error (.layoutFailed .layoutOverflow) ∧
    validateRawPtrFastPath sliceOfOversized (.wideSlice addr len) = .error (.layoutFailed .layoutOverflow) ∧
    validateRawPtrLayoutFirst sliceOfOversized (.wideSlice addr len) = .error (.layoutFailed .layoutOverflow) := by
  have h1 : computeTyLayout (.tuple [.array (.uint 1) usizeMax64, .slice (.uint 1)]) = .error .layoutOverflow := by
    simp [computeTyLayout, computeFieldsLayout, maxObjectSize64, usizeMax64]
  have h2 : computeTyLayout (.slice (.array (.uint 1) usizeMax64)) = .error .layoutOverflow := by
    simp [computeTyLayout, maxObjectSize64, usizeMax64]
  refine ⟨by simp [validateRawPtrFastPath, isSyntacticallySized, fieldsTailSyntacticallySized, h1],
    by simp [validateRawPtrLayoutFirst, h1],
    by simp [validateRawPtrFastPath, isSyntacticallySized, h2],
    by simp [validateRawPtrLayoutFirst, h2]⟩

/-- Thin pointer with optional allocation provenance `(allocId, offsetBytes)`. -/
structure ThinPtrVal where
  addr : UInt64
  prov : Option (MiriAllocId × UInt64) := none
  deriving DecidableEq, Repr

/-- Safe thin reference validation errors (`ValidityVisitor.checkSafe`). -/
inductive SafeThinRefErr where
  | layoutFailed (err : LayoutErr)
  | unsizedPointee
  | danglingOrOutOfBoundsSafePtr
  | nullSafePtr
  | uninhabitedPointee
  | unalignedSafePtr (requiredAlign : Nat) (addr : UInt64)
  deriving DecidableEq, Repr

/-- Pointer-access check mirroring `Miri.Memory.checkAndDerefPtr` (`check_and_deref_ptr`) as consumed by
`ValidityMachine.checkPointerAccessResult`:
- a ZERO-sized access succeeds WITHOUT resolving the pointer or consulting any allocation, so dangling,
  dead (use-after-free), or out-of-bounds provenance is irrelevant;
- a non-zero access needs provenance into an allocation that `getAllocInfo` reports as non-`.dead`
  with `[offset, offset + size)` in bounds (function / vtable / type-id globals expose `0` bytes, so
  only live locals and `.static` / `.memory` globals are dereferenceable). -/
def KeyedAllocWorld.checkPtrAccess (w : KeyedAllocWorld) (prov : Option (MiriAllocId × UInt64))
    (sizeBytes : Nat) : Bool :=
  if sizeBytes == 0 then true
  else
    match prov with
    | none => false
    | some (id, off) =>
      match w.getAllocInfo id with
      | some info => info.kind != .dead && decide (off.toNat + sizeBytes ≤ info.sizeBytes.toNat)
      | none => false

/-- Safe thin reference validator aligned with `Miri.Interpreter.ValidityVisitor.checkSafe` (`lines 205-228`)
and `ValidityMachine.scalarMayBeNull`:
1. Computes layout (must be sized).
2. Checks pointer access FIRST via `w.checkPtrAccess` (`getAllocInfo`-backed; zero-sized accesses never
   dangle). A failing access through a provenance-free null address is classified as a null reference
   (`DanglingIntPointer { addr: 0 }`), every other failure as dangling / out-of-bounds.
3. Enforces provenance-agnostic `ptr.addr == 0` null rejection (`scalarMayBeNull`).
4. Checks pointee inhabitedness.
5. Checks alignment AFTER pointer access. -/
def validateSafeThinRef (w : KeyedAllocWorld) (pointee : ProtoTy) (ptr : ThinPtrVal) :
    Except SafeThinRefErr Unit :=
  match computeTyLayout pointee with
  | .error e => .error (.layoutFailed e)
  | .ok lay =>
    if !lay.isSized then .error .unsizedPointee
    else if !w.checkPtrAccess ptr.prov lay.sizeBytes then
      if ptr.prov.isNone && ptr.addr == 0 then .error .nullSafePtr
      else .error .danglingOrOutOfBoundsSafePtr
    else if ptr.addr == 0 then .error .nullSafePtr
    else if !lay.isInhabited then .error .uninhabitedPointee
    else if ptr.addr.toNat % lay.alignBytes != 0 then .error (.unalignedSafePtr lay.alignBytes ptr.addr)
    else .ok ()

/-- `validateSafeThinRef` matches `ValidityVisitor.checkSafe`:
1. `&u32` into an uncached `.static` global (present in `w.globals`, absent from `w.table.live`) succeeds.
2. Zero-address provenanced `&()` (`addr = 0`, valid `prov`) fails with `.nullSafePtr`.
3. Unaligned dangling `&u32` at `addr = 2` fails with `.danglingOrOutOfBoundsSafePtr` before `.unalignedSafePtr`. -/
theorem validateSafeThinRef_staticGlobal_nullProv_and_accessOrder :
    let idStatic : MiriAllocId := ⟨1, by decide⟩
    let w : KeyedAllocWorld :=
      KeyedAllocWorld.empty.registerGlobal idStatic ⟨.static, 4, 2, .not, []⟩
    w.findLive? idStatic = none ∧
    validateSafeThinRef w (.uint 4) ⟨16, some (idStatic, 0)⟩ = .ok () ∧
    validateSafeThinRef w .unit ⟨0, some (idStatic, 0)⟩ = .error .nullSafePtr ∧
    validateSafeThinRef w (.uint 4) ⟨2, none⟩ = .error .danglingOrOutOfBoundsSafePtr := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · unfold validateSafeThinRef
    simp [KeyedAllocWorld.empty, KeyedAllocWorld.registerGlobal, KeyedAllocWorld.getAllocInfo,
      KeyedAllocWorld.findLive?, KeyedAllocWorld.findGlobal?,
      ExtTreeMap0.get?_empty, ExtTreeMap0.get?_insert_self,
      computeTyLayout, KeyedAllocWorld.checkPtrAccess, GlobalAllocEntry.toAllocInfo]
  · unfold validateSafeThinRef
    simp [computeTyLayout, KeyedAllocWorld.checkPtrAccess]
  · rfl

/-- Zero-sized safe references never dangle (`check_and_deref_ptr`: "everything is okay with size 0"):
for EVERY world and EVERY provenance — including provenance into a freed, never-registered, or
out-of-bounds allocation — `&()` is valid iff its address is non-null. -/
theorem validateSafeThinRef_zst_never_dangles (w : KeyedAllocWorld) (ptr : ThinPtrVal) :
    validateSafeThinRef w .unit ptr =
      if ptr.addr == 0 then .error .nullSafePtr else .ok () := by
  unfold validateSafeThinRef
  simp [computeTyLayout, KeyedAllocWorld.checkPtrAccess, Nat.mod_one]

/-- Non-zero-sized safe references: a provenance-free null address is reported as a NULL reference
(`DanglingIntPointer { addr: 0 }`), a provenance-free non-null address as dangling, and provenance into
a tombstoned allocation (use-after-free) or a `0`-byte function / vtable global as dangling — even at
a well-aligned non-null address. -/
theorem validateSafeThinRef_nullInt_dead_and_fnGlobal_classification
    (w : KeyedAllocWorld) (deadId fnId : MiriAllocId) (d : DeadAllocEntry) (g : GlobalAllocEntry)
    (hdeadNotLive : w.findLive? deadId = none) (hdeadNotGlobal : w.findGlobal? deadId = none)
    (hdead : w.findDead? deadId = some d)
    (hfnNotLive : w.findLive? fnId = none) (hfn : w.findGlobal? fnId = some g)
    (hfnKind : g.kind = .function ∨ g.kind = .vtable ∨ g.kind = .typeId) :
    validateSafeThinRef w (.uint 4) ⟨0, none⟩ = .error .nullSafePtr ∧
    validateSafeThinRef w (.uint 4) ⟨16, none⟩ = .error .danglingOrOutOfBoundsSafePtr ∧
    validateSafeThinRef w (.uint 4) ⟨16, some (deadId, 0)⟩ = .error .danglingOrOutOfBoundsSafePtr ∧
    validateSafeThinRef w (.uint 4) ⟨16, some (fnId, 0)⟩ = .error .danglingOrOutOfBoundsSafePtr := by
  have hdeadInfo := ((keyedGetAllocInfo_dead_and_unavailable w deadId hdeadNotLive hdeadNotGlobal).1 d hdead).1
  have hfnInfo := keyedGetAllocInfo_global_kinds w fnId g hfnNotLive hfn
  have hfnSize : g.toAllocInfo.sizeBytes = 0 := (hfnInfo.2.1 hfnKind).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold validateSafeThinRef
    simp [computeTyLayout, KeyedAllocWorld.checkPtrAccess]
  · unfold validateSafeThinRef
    simp [computeTyLayout, KeyedAllocWorld.checkPtrAccess]
  · unfold validateSafeThinRef
    simp [computeTyLayout, KeyedAllocWorld.checkPtrAccess, hdeadInfo]
  · unfold validateSafeThinRef
    simp [computeTyLayout, KeyedAllocWorld.checkPtrAccess, hfnInfo.1, hfnSize]

/-! ### 3B. Principal-Less Auto-Trait `dyn Send` VTables (`lean-miri#75`), `VTableWorldWF`, & `SaltedVTableWorldWF` -/

/-- Constructive UTF-8 raw byte encoding (`0 Classical.choice`, avoiding `String.toList`). -/
def stringToRawNatBytes (s : String) : List Nat :=
  s.toUTF8.toList.map UInt8.toNat

/-- Rust built-in auto traits eligible for principal-less `dyn` objects (`lean-miri#75`). -/
inductive AutoTrait where
  | send
  | sync
  | unpin
  | unwindSafe
  | refUnwindSafe
  deriving DecidableEq, Repr, Inhabited

namespace AutoTrait

def rank : AutoTrait → Nat
  | .send => 0
  | .sync => 1
  | .unpin => 2
  | .unwindSafe => 3
  | .refUnwindSafe => 4

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

def allTraits : List AutoTrait :=
  [.send, .sync, .unpin, .unwindSafe, .refUnwindSafe]

end AutoTrait

/-- Canonical deduplicated, rank-ordered representation of an `AutoTrait` set. -/
def canonicalizeAutoTraits (xs : List AutoTrait) : List AutoTrait :=
  AutoTrait.allTraits.filter (fun a => xs.any (fun x => x == a))

theorem mem_canonicalizeAutoTraits_iff (xs : List AutoTrait) (a : AutoTrait) :
    a ∈ canonicalizeAutoTraits xs ↔ a ∈ xs := by
  unfold canonicalizeAutoTraits AutoTrait.allTraits
  rw [List.mem_filter]
  constructor
  · rintro ⟨_, hany⟩
    rw [List.any_eq_true] at hany
    rcases hany with ⟨x, hx, hbeq⟩
    have heq : x = a := beq_iff_eq.1 hbeq
    subst heq; exact hx
  · intro ha
    refine ⟨by cases a <;> simp, ?_⟩
    rw [List.any_eq_true]
    exact ⟨a, ha, beq_self_eq_true a⟩

theorem canonicalizeAutoTraits_eq_of_mem_iff {xs ys : List AutoTrait}
    (h : ∀ a, a ∈ xs ↔ a ∈ ys) :
    canonicalizeAutoTraits xs = canonicalizeAutoTraits ys := by
  unfold canonicalizeAutoTraits
  congr 1
  funext a
  cases hx : xs.any (fun x => x == a) with
  | true =>
    have hm : a ∈ xs := by
      rw [List.any_eq_true] at hx
      rcases hx with ⟨x, hxm, hbeq⟩
      rw [← beq_iff_eq.1 hbeq]; exact hxm
    have hy : ys.any (fun y => y == a) = true := by
      rw [List.any_eq_true]; exact ⟨a, (h a).1 hm, beq_self_eq_true a⟩
    exact hy.symm
  | false =>
    cases hy : ys.any (fun y => y == a) with
    | false => rfl
    | true =>
      have hm : a ∈ ys := by
        rw [List.any_eq_true] at hy
        rcases hy with ⟨y, hym, hbeq⟩
        rw [← beq_iff_eq.1 hbeq]; exact hym
      have hx' : xs.any (fun x => x == a) = true := by
        rw [List.any_eq_true]; exact ⟨a, (h a).2 hm, beq_self_eq_true a⟩
      rw [hx] at hx'; cases hx'

theorem canonicalizeAutoTraits_idem (xs : List AutoTrait) :
    canonicalizeAutoTraits (canonicalizeAutoTraits xs) = canonicalizeAutoTraits xs :=
  canonicalizeAutoTraits_eq_of_mem_iff (mem_canonicalizeAutoTraits_iff xs)

/-- Canonical set of auto-trait bounds. -/
structure AutoTraitSet where
  traits : List AutoTrait
  canonical : traits = canonicalizeAutoTraits traits
  deriving DecidableEq, Repr

namespace AutoTraitSet

def empty : AutoTraitSet := ⟨[], rfl⟩

def ofList (xs : List AutoTrait) : AutoTraitSet :=
  ⟨canonicalizeAutoTraits xs, (canonicalizeAutoTraits_idem xs).symm⟩

@[ext]
theorem ext {s₁ s₂ : AutoTraitSet} (h : s₁.traits = s₂.traits) : s₁ = s₂ := by
  cases s₁; cases s₂; simp only at h; subst h; rfl

theorem ofList_eq_of_mem_iff {xs ys : List AutoTrait} (h : ∀ a, a ∈ xs ↔ a ∈ ys) :
    ofList xs = ofList ys :=
  ext (canonicalizeAutoTraits_eq_of_mem_iff h)

/-- 5-bit canonical bitmask `< 32` encoding an `AutoTraitSet`. -/
def mask (s : AutoTraitSet) : Nat :=
  (if s.traits.any (· == .send) then 1 else 0) +
  (if s.traits.any (· == .sync) then 2 else 0) +
  (if s.traits.any (· == .unpin) then 4 else 0) +
  (if s.traits.any (· == .unwindSafe) then 8 else 0) +
  (if s.traits.any (· == .refUnwindSafe) then 16 else 0)

theorem mask_lt (s : AutoTraitSet) : s.mask < 32 := by
  unfold mask
  split <;> split <;> split <;> split <;> split <;> omega

theorem mask_injective : Function.Injective mask := by
  intro s₁ s₂ h
  apply ext
  rw [s₁.canonical, s₂.canonical]
  apply canonicalizeAutoTraits_eq_of_mem_iff
  have hbit : ∀ (b c : Bool) (r₁ r₂ : Nat),
      (if b then 1 else 0) + 2 * r₁ = (if c then 1 else 0) + 2 * r₂ → b = c ∧ r₁ = r₂ := by
    intro b c r₁ r₂ heq
    cases b <;> cases c <;> simp at heq ⊢ <;> omega
  have hfact : ∀ b0 b1 b2 b3 b4 : Bool,
      ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
        (if b3 then 8 else 0) + (if b4 then 16 else 0)) =
      (if b0 then 1 else 0) + 2 * ((if b1 then 1 else 0) + 2 * ((if b2 then 1 else 0) +
        2 * ((if b3 then 1 else 0) + 2 * (if b4 then 1 else 0)))) := by
    intro b0 b1 b2 b3 b4
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> rfl
  have hbits : ∀ (b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 : Bool),
      ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
        (if b3 then 8 else 0) + (if b4 then 16 else 0)) =
      ((if c0 then 1 else 0) + (if c1 then 2 else 0) + (if c2 then 4 else 0) +
        (if c3 then 8 else 0) + (if c4 then 16 else 0)) →
      b0 = c0 ∧ b1 = c1 ∧ b2 = c2 ∧ b3 = c3 ∧ b4 = c4 := by
    intro b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 heq
    rw [hfact b0 b1 b2 b3 b4, hfact c0 c1 c2 c3 c4] at heq
    rcases hbit b0 c0 _ _ heq with ⟨e0, r1⟩
    rcases hbit b1 c1 _ _ r1 with ⟨e1, r2⟩
    rcases hbit b2 c2 _ _ r2 with ⟨e2, r3⟩
    rcases hbit b3 c3 _ _ r3 with ⟨e3, r4⟩
    have e4 : b4 = c4 := by cases b4 <;> cases c4 <;> simp at r4 ⊢
    exact ⟨e0, e1, e2, e3, e4⟩
  unfold mask at h
  rcases hbits _ _ _ _ _ _ _ _ _ _ h with ⟨h0, h1, h2, h3, h4⟩
  intro a
  have hiff : ∀ t, (s₁.traits.any (· == t) = s₂.traits.any (· == t)) → (t ∈ s₁.traits ↔ t ∈ s₂.traits) := by
    intro t ht
    constructor
    · intro hm
      have h1' : s₁.traits.any (· == t) = true := List.any_eq_true.2 ⟨t, hm, beq_self_eq_true t⟩
      rw [ht] at h1'
      rcases List.any_eq_true.1 h1' with ⟨y, hym, hbeq⟩
      rw [← beq_iff_eq.1 hbeq]; exact hym
    · intro hm
      have h2' : s₂.traits.any (· == t) = true := List.any_eq_true.2 ⟨t, hm, beq_self_eq_true t⟩
      rw [← ht] at h2'
      rcases List.any_eq_true.1 h2' with ⟨y, hym, hbeq⟩
      rw [← beq_iff_eq.1 hbeq]; exact hym
  cases a
  · exact hiff .send h0
  · exact hiff .sync h1
  · exact hiff .unpin h2
  · exact hiff .unwindSafe h3
  · exact hiff .refUnwindSafe h4

end AutoTraitSet

/-- Constructive Cantor pairing function on `Nat` (`0` axioms). -/
def cantorPair (a b : Nat) : Nat :=
  (a + b) * (a + b + 1) / 2 + b

private theorem cantorPair_diag_lt {s₁ s₂ : Nat} (h : s₁ < s₂) (b₁ b₂ : Nat) (hb₁ : b₁ ≤ s₁) :
    s₁ * (s₁ + 1) / 2 + b₁ < s₂ * (s₂ + 1) / 2 + b₂ := by
  have hstep : (s₁ + 1) * (s₁ + 2) / 2 ≤ s₂ * (s₂ + 1) / 2 := by
    apply Nat.div_le_div_right
    have h1 : s₁ + 1 ≤ s₂ := h
    have h2 : s₁ + 2 ≤ s₂ + 1 := Nat.add_le_add_right h 1
    exact Nat.mul_le_mul h1 h2
  have htri : s₁ * (s₁ + 1) / 2 + (s₁ + 1) = (s₁ + 1) * (s₁ + 2) / 2 := by
    have hstepMul : ∀ m : Nat, (m + 1) * (m + 2) = m * (m + 1) + 2 * (m + 1) := by
      intro m
      rw [Nat.mul_add, Nat.mul_comm (m + 1) m, Nat.mul_comm (m + 1) 2]
    have heven : ∃ q, s₁ * (s₁ + 1) = 2 * q := by
      clear h hstep hb₁
      induction s₁ with
      | zero => exact ⟨0, rfl⟩
      | succ k ih =>
        rcases ih with ⟨q, hq⟩
        exact ⟨q + (k + 1), by rw [hstepMul k, hq]; omega⟩
    rcases heven with ⟨q, hq⟩
    have hq2 : (s₁ + 1) * (s₁ + 2) = 2 * (q + (s₁ + 1)) := by
      rw [hstepMul s₁, hq]; omega
    rw [hq, hq2, Nat.mul_div_right _ (by decide), Nat.mul_div_right _ (by decide)]
  omega

theorem cantorPair_injective : Function.Injective (fun p : Nat × Nat => cantorPair p.1 p.2) := by
  intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  unfold cantorPair at h
  dsimp only at h
  by_cases hlt : a₁ + b₁ < a₂ + b₂
  · exact False.elim (Nat.ne_of_lt (cantorPair_diag_lt hlt b₁ b₂ (Nat.le_add_left b₁ a₁)) h)
  · by_cases hgt : a₂ + b₂ < a₁ + b₁
    · exact False.elim (Nat.ne_of_lt (cantorPair_diag_lt hgt b₂ b₁ (Nat.le_add_left b₂ a₂)) h.symm)
    · have hsum : a₁ + b₁ = a₂ + b₂ := by omega
      rw [hsum] at h
      have hb : b₁ = b₂ := by omega
      have ha : a₁ = a₂ := by omega
      subst ha; subst hb; rfl

/-- Existential trait predicate mirroring `Miri.Interpreter.VTablePredicate`. -/
structure VTablePredSpec where
  id : Nat
  stableKey : Nat
  autoTrait : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Existential trait specification for `dyn Trait + AutoTraits`. -/
structure DynExistentialSpec where
  principal : Option Nat
  autoTraits : AutoTraitSet
  predicates : List VTablePredSpec := []
  deriving DecidableEq, Repr

/-- Effective predicate list combining optional `principal` with explicit `predicates`. -/
def DynExistentialSpec.effectivePreds (s : DynExistentialSpec) : List VTablePredSpec :=
  match s.principal with
  | some p => ⟨p, p, false⟩ :: s.predicates
  | none => s.predicates

/-- Canonical pair-based sorting & deduplication of non-auto-trait predicates (`(stableKey, id)`). -/
private def insertKeyIdSorted (p : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [p]
  | h :: t =>
    if p.1 < h.1 || (p.1 == h.1 && p.2 < h.2) then
      p :: h :: t
    else if p.1 == h.1 && p.2 == h.2 then
      h :: t
    else
      h :: insertKeyIdSorted p t

private def sortDedupKeyIds : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | h :: t => insertKeyIdSorted h (sortDedupKeyIds t)

private theorem insertKeyIdSorted_comm (a b : Nat × Nat) (xs : List (Nat × Nat)) :
    insertKeyIdSorted a (insertKeyIdSorted b xs) = insertKeyIdSorted b (insertKeyIdSorted a xs) := by
  have htrich : ∀ p q : Nat × Nat,
      (p.1 < q.1 || (p.1 == q.1 && p.2 < q.2)) = true ∨
      (p = q) ∨
      (q.1 < p.1 || (q.1 == p.1 && q.2 < p.2)) = true := by
    intro ⟨p1, p2⟩ ⟨q1, q2⟩
    by_cases h1 : p1 < q1
    · left; simp [h1]
    · by_cases h2 : q1 < p1
      · right; right; simp [h2]
      · have h1eq : p1 = q1 := by omega
        subst h1eq
        by_cases h3 : p2 < q2
        · left; simp [h3]
        · by_cases h4 : q2 < p2
          · right; right; simp [h4]
          · right; left; have h2eq : p2 = q2 := by omega
            subst h2eq; rfl
  have hanti : ∀ p q : Nat × Nat,
      (p.1 < q.1 || (p.1 == q.1 && p.2 < q.2)) = true →
      (q.1 < p.1 || (q.1 == p.1 && q.2 < p.2)) = false ∧ (q.1 == p.1 && q.2 == p.2) = false ∧
      (p.1 == q.1 && p.2 == q.2) = false := by
    intro ⟨p1, p2⟩ ⟨q1, q2⟩ h
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with h1 | ⟨h1, h2⟩
    · refine ⟨by simp [show ¬(q1 < p1) by omega, beq_false_of_ne (by omega : q1 ≠ p1)],
        by simp [beq_false_of_ne (by omega : q1 ≠ p1)],
        by simp [beq_false_of_ne (by omega : p1 ≠ q1)]⟩
    · subst h1
      refine ⟨by simp [show ¬(q2 < p2) by omega],
        by simp [beq_false_of_ne (by omega : q2 ≠ p2)],
        by simp [beq_false_of_ne (by omega : p2 ≠ q2)]⟩
  induction xs with
  | nil =>
    simp only [insertKeyIdSorted]
    rcases htrich a b with hab | rfl | hba
    · rcases hanti a b hab with ⟨h1, h2, h3⟩
      simp [hab, h1, h2]
    · simp
    · rcases hanti b a hba with ⟨h1, h2, h3⟩
      simp [hba, h1, h2]
  | cons x rest ih =>
    simp only [insertKeyIdSorted]
    rcases htrich a x with hax | rfl | hxa
    · rcases hanti a x hax with ⟨hxan, hxaeq, haxeq⟩
      rcases htrich b x with hbx | rfl | hxb
      · rcases hanti b x hbx with ⟨hxbn, hxbeq, hbxeq⟩
        simp only [hax, hbx, ↓reduceIte, insertKeyIdSorted]
        rcases htrich a b with hab | rfl | hba
        · rcases hanti a b hab with ⟨hban, hbaeq, _⟩
          simp [hab, hban, hbaeq]
        · simp
        · rcases hanti b a hba with ⟨habn, habeq, _⟩
          simp [hba, habn, habeq]
      · simp [insertKeyIdSorted, hax, hxan, hxaeq]
      · rcases hanti x b hxb with ⟨hbxn, hbxeq, hxbeq⟩
        simp only [hax, hbxn, hbxeq, ↓reduceIte, Bool.false_eq_true, insertKeyIdSorted]
        have hab : (a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)) = true := by
          simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hax hxb ⊢
          rcases hax with h1 | ⟨h1, h2⟩ <;> rcases hxb with h3 | ⟨h3, h4⟩ <;> first | exact Or.inl (by omega) | exact Or.inr ⟨by omega, by omega⟩
        rcases hanti a b hab with ⟨hban, hbaeq, _⟩
        simp [hban, hbaeq]
    · rcases htrich b a with hba | rfl | hab
      · rcases hanti b a hba with ⟨habn, habeq, hbaeq⟩
        simp [insertKeyIdSorted, hba, habn, habeq]
      · simp
      · rcases hanti a b hab with ⟨hban, hbaeq, habeq⟩
        simp [hban, hbaeq, insertKeyIdSorted]
    · rcases hanti x a hxa with ⟨haxn, haxeq, hxaeq⟩
      rcases htrich b x with hbx | rfl | hxb
      · rcases hanti b x hbx with ⟨hxbn, hxbeq, hbxeq⟩
        have hba : (b.1 < a.1 || (b.1 == a.1 && b.2 < a.2)) = true := by
          simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hbx hxa ⊢
          rcases hbx with h1 | ⟨h1, h2⟩ <;> rcases hxa with h3 | ⟨h3, h4⟩ <;> first | exact Or.inl (by omega) | exact Or.inr ⟨by omega, by omega⟩
        rcases hanti b a hba with ⟨habn, habeq, _⟩
        simp [haxn, haxeq, hbx, insertKeyIdSorted, habn, habeq]
      · simp [haxn, haxeq, insertKeyIdSorted]
      · rcases hanti x b hxb with ⟨hbxn, hbxeq, hxbeq⟩
        simp [haxn, haxeq, hbxn, hbxeq, insertKeyIdSorted, ih]

private theorem sortDedupKeyIds_perm {xs ys : List (Nat × Nat)} (h : List.Perm xs ys) :
    sortDedupKeyIds xs = sortDedupKeyIds ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [sortDedupKeyIds, ih]
  | swap x y l => exact insertKeyIdSorted_comm y x (sortDedupKeyIds l)
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Canonical sorted non-auto-trait predicate ID list (using pair sort for exact permutation invariance). -/
def canonicalNonAutoPredIds (preds : List VTablePredSpec) : List Nat :=
  (sortDedupKeyIds ((preds.filter (fun p => !p.autoTrait)).map fun p => (p.stableKey, p.id))).map Prod.snd

/-- Auto-trait-ignoring trait compatibility check (`Miri.Interpreter.VTable.checkForTypeRead`). -/
def vtableMatchesExpectedSpec (actual expected : DynExistentialSpec) : Bool :=
  canonicalNonAutoPredIds actual.effectivePreds == canonicalNonAutoPredIds expected.effectivePreds

theorem vtableMatchesExpectedSpec_ignores_autoTraits
    (p : Option Nat) (a₁ a₂ : AutoTraitSet) (preds : List VTablePredSpec)
    (extraAuto₁ extraAuto₂ : List VTablePredSpec)
    (h1 : ∀ q ∈ extraAuto₁, q.autoTrait = true)
    (h2 : ∀ q ∈ extraAuto₂, q.autoTrait = true) :
    vtableMatchesExpectedSpec ⟨p, a₁, preds ++ extraAuto₁⟩ ⟨p, a₂, preds ++ extraAuto₂⟩ = true := by
  have hfilt : ∀ xs : List VTablePredSpec, (∀ q ∈ xs, q.autoTrait = true) →
      xs.filter (fun q => !q.autoTrait) = [] := by
    intro xs hxs
    induction xs with
    | nil => rfl
    | cons x rest ih =>
      have hx : x.autoTrait = true := hxs x (List.mem_cons_self ..)
      simp [hx, ih (fun q hq => hxs q (List.mem_cons_of_mem _ hq))]
  unfold vtableMatchesExpectedSpec canonicalNonAutoPredIds DynExistentialSpec.effectivePreds
  cases p <;> simp [List.filter_append, hfilt extraAuto₁ h1, hfilt extraAuto₂ h2]

theorem vtableMatchesExpectedSpec_predicate_perm
    (actual expected : DynExistentialSpec)
    (preds' : List VTablePredSpec) (hperm : List.Perm actual.predicates preds') :
    vtableMatchesExpectedSpec { actual with predicates := preds' } expected =
      vtableMatchesExpectedSpec actual expected := by
  have hpeff : List.Perm actual.effectivePreds ({ actual with predicates := preds' }).effectivePreds := by
    unfold DynExistentialSpec.effectivePreds
    cases actual.principal with
    | none => exact hperm
    | some p => exact List.Perm.cons ⟨p, p, false⟩ hperm
  have hsort :
      sortDedupKeyIds (((({ actual with predicates := preds' } : DynExistentialSpec).effectivePreds.filter (fun p => !p.autoTrait)).map fun p => (p.stableKey, p.id))) =
      sortDedupKeyIds ((actual.effectivePreds.filter (fun p => !p.autoTrait)).map fun p => (p.stableKey, p.id)) :=
    sortDedupKeyIds_perm ((hpeff.symm.filter _).map _)
  unfold vtableMatchesExpectedSpec canonicalNonAutoPredIds
  rw [hsort]

/-- Canonical vtable interning key supporting principal-less `dyn Send` (`principal = none`). -/
structure VTableKey where
  concreteTyCode : Nat
  principal : Option Nat
  autoTraits : AutoTraitSet
  deriving DecidableEq, Repr

def mkCanonicalVTableKey (tyCode : Nat) (principal : Option Nat) (autoTraits : List AutoTrait) :
    VTableKey :=
  ⟨tyCode, principal, AutoTraitSet.ofList autoTraits⟩

theorem mkCanonicalVTableKey_perm_eq (tyCode : Nat) (principal : Option Nat)
    {xs ys : List AutoTrait} (h : ∀ a, a ∈ xs ↔ a ∈ ys) :
    mkCanonicalVTableKey tyCode principal xs = mkCanonicalVTableKey tyCode principal ys := by
  unfold mkCanonicalVTableKey
  rw [AutoTraitSet.ofList_eq_of_mem_iff h]

theorem vtableKey_principalLess_ne_principalBearing
    (tyCode : Nat) (p : Nat) (a₁ a₂ : AutoTraitSet) :
    (⟨tyCode, none, a₁⟩ : VTableKey) ≠ ⟨tyCode, some p, a₂⟩ := by
  intro h; cases h

/-- Constructive injective `Nat` code for `VTableKey` (`0` axioms). -/
def encodeVTableKeyCode (k : VTableKey) : Nat :=
  let pCode := match k.principal with | none => 0 | some p => p + 1
  cantorPair k.concreteTyCode (pCode * 32 + k.autoTraits.mask)

theorem encodeVTableKeyCode_injective : Function.Injective encodeVTableKeyCode := by
  intro k₁ k₂ h
  unfold encodeVTableKeyCode at h
  dsimp only at h
  have hp := cantorPair_injective (a₁ := (k₁.concreteTyCode, _)) (a₂ := (k₂.concreteTyCode, _)) h
  have hty : k₁.concreteTyCode = k₂.concreteTyCode := (Prod.mk.inj hp).1
  have htr : (match k₁.principal with | none => 0 | some p => p + 1) * 32 + k₁.autoTraits.mask =
      (match k₂.principal with | none => 0 | some p => p + 1) * 32 + k₂.autoTraits.mask :=
    (Prod.mk.inj hp).2
  have hm1 := k₁.autoTraits.mask_lt
  have hm2 := k₂.autoTraits.mask_lt
  have hpCode : (match k₁.principal with | none => 0 | some p => p + 1) =
      (match k₂.principal with | none => 0 | some p => p + 1) := by omega
  have hmask : k₁.autoTraits.mask = k₂.autoTraits.mask := by omega
  have ha : k₁.autoTraits = k₂.autoTraits := AutoTraitSet.mask_injective hmask
  have hpr : k₁.principal = k₂.principal := by
    cases h1 : k₁.principal with
    | none =>
      cases h2 : k₂.principal with
      | none => rfl
      | some p2 => rw [h1, h2] at hpCode; dsimp only at hpCode; omega
    | some p1 =>
      cases h2 : k₂.principal with
      | none => rw [h1, h2] at hpCode; dsimp only at hpCode; omega
      | some p2 => rw [h1, h2] at hpCode; dsimp only at hpCode; exact congrArg some (by omega)
  cases k₁; cases k₂; simp only at hty hpr ha; subst hty; subst hpr; subst ha; rfl

/-- Symbolic vtable metadata stored per interned vtable `MiriAllocId`. -/
structure VTableData where
  concreteTy : ProtoTy
  concreteTyCode : Nat
  dropFnId : Option MiriAllocId
  sizeBytes : UInt64
  alignPow2 : UInt8
  spec : DynExistentialSpec
  methodSlots : List MiriAllocId := []
  deriving Repr

/-- Construct a principal-less vtable (`dyn Send`, `dyn Send + Sync`, etc.) with zero virtual method slots. -/
def buildPrincipalLessVTable (concreteTy : ProtoTy) (concreteTyCode : Nat)
    (dropFnId : Option MiriAllocId) (sizeBytes : UInt64) (alignPow2 : UInt8)
    (autoTraits : List AutoTrait) : VTableData where
  concreteTy := concreteTy
  concreteTyCode := concreteTyCode
  dropFnId := dropFnId
  sizeBytes := sizeBytes
  alignPow2 := alignPow2
  spec := ⟨none, AutoTraitSet.ofList autoTraits, []⟩
  methodSlots := []

theorem buildPrincipalLessVTable_spec (concreteTy : ProtoTy) (concreteTyCode : Nat)
    (dropFnId : Option MiriAllocId) (sizeBytes : UInt64) (alignPow2 : UInt8)
    (autoTraits : List AutoTrait) :
    let vt := buildPrincipalLessVTable concreteTy concreteTyCode dropFnId sizeBytes alignPow2 autoTraits
    vt.spec.principal = none ∧
    vt.methodSlots = [] ∧
    vt.dropFnId = dropFnId ∧
    vt.sizeBytes = sizeBytes ∧
    vt.alignPow2 = alignPow2 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Resolve a virtual method slot on a vtable. -/
def resolveVirtualMethod (vt : VTableData) (slot : Nat) : Option MiriAllocId :=
  vt.methodSlots[slot]?

theorem principalLess_resolveVirtualMethod_fails (concreteTy : ProtoTy) (concreteTyCode : Nat)
    (dropFnId : Option MiriAllocId) (sizeBytes : UInt64) (alignPow2 : UInt8)
    (autoTraits : List AutoTrait) (slot : Nat) :
    resolveVirtualMethod
      (buildPrincipalLessVTable concreteTy concreteTyCode dropFnId sizeBytes alignPow2 autoTraits)
      slot = none := by
  simp [resolveVirtualMethod, buildPrincipalLessVTable]

/-- Compatibility condition tying a `VTableData` record to its interning `VTableKey`. -/
structure VTableDataMatchesKey (k : VTableKey) (data : VTableData) : Prop where
  tyCode_eq : data.concreteTyCode = k.concreteTyCode
  principal_eq : data.spec.principal = k.principal
  autoTraits_eq : data.spec.autoTraits = k.autoTraits
  preds_canonical :
    canonicalNonAutoPredIds data.spec.effectivePreds =
      match k.principal with | some p => [p] | none => []

/-- Constructive `ExtTreeMap0`-backed vtable registry. -/
structure VTableRegistry where
  keyToAlloc : ExtTreeMap0 Nat MiriAllocId compare := ExtTreeMap0.empty
  allocToData : ExtTreeMap0 MiriAllocId VTableData compare := ExtTreeMap0.empty

namespace VTableRegistry

def empty : VTableRegistry := {}

/-- Intern a vtable in `(reg, w)`: cache hits are idempotent; misses reserve a fresh `MiriAllocId`
and register a `.vtable` global allocation in `w`. -/
def intern (reg : VTableRegistry) (w : KeyedAllocWorld) (key : VTableKey) (data : VTableData) :
    Except AllocIdErr (VTableRegistry × KeyedAllocWorld × MiriAllocId) :=
  let code := encodeVTableKeyCode key
  match reg.keyToAlloc.get? code with
  | some id => .ok (reg, w, id)
  | none =>
    let (w1, res) := w.reserveAllocId
    match res with
    | .error e => .error e
    | .ok id =>
      let w2 := w1.registerGlobal id ⟨.vtable, 24, 3, .not, []⟩
      let reg' : VTableRegistry :=
        { keyToAlloc := reg.keyToAlloc.insert code id
          allocToData := reg.allocToData.insert id data }
      .ok (reg', w2, id)

theorem vtableRegistry_intern_idempotent (reg : VTableRegistry) (w : KeyedAllocWorld)
    (key : VTableKey) (data data₂ : VTableData)
    {reg' : VTableRegistry} {w' : KeyedAllocWorld} {id : MiriAllocId}
    (h : reg.intern w key data = .ok (reg', w', id)) :
    reg'.intern w' key data₂ = .ok (reg', w', id) := by
  unfold intern at h ⊢
  dsimp only at h ⊢
  cases hg : reg.keyToAlloc.get? (encodeVTableKeyCode key) with
  | some id0 =>
    rw [hg] at h; injection h with hpair
    rcases Prod.mk.inj hpair with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
    simp [hg]
  | none =>
    rw [hg] at h
    cases hres : w.reserveAllocId with
    | mk w1 ores =>
      rw [hres] at h
      cases ores with
      | error _ => cases h
      | ok id1 =>
        simp only at h; injection h with hpair
        rcases Prod.mk.inj hpair with ⟨rfl, hrest⟩
        rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
        simp [ExtTreeMap0.get?_insert_self]

/-- Key-to-data registry coherence (including per-type `(dropFnId, sizeBytes, alignPow2)` uniqueness). -/
structure KeyWF (reg : VTableRegistry) : Prop where
  key_has_data :
    ∀ k id, reg.keyToAlloc.get? (encodeVTableKeyCode k) = some id →
      ∃ data, reg.allocToData.get? id = some data ∧ VTableDataMatchesKey k data
  ty_layout_unique :
    ∀ id₁ d₁ id₂ d₂,
      reg.allocToData.get? id₁ = some d₁ →
      reg.allocToData.get? id₂ = some d₂ →
      d₁.concreteTyCode = d₂.concreteTyCode →
      d₁.dropFnId = d₂.dropFnId ∧ d₁.sizeBytes = d₂.sizeBytes ∧ d₁.alignPow2 = d₂.alignPow2

theorem keyWF_empty : KeyWF empty :=
  ⟨fun _ _ h => by simp [empty, ExtTreeMap0.get?_empty] at h,
   fun _ _ _ _ h => by simp [empty, ExtTreeMap0.get?_empty] at h⟩

/-- Allocation-side coherence: every `allocToData` ID is registered as a `.vtable` global in `w`. -/
structure AllocWF (reg : VTableRegistry) (w : KeyedAllocWorld) : Prop where
  data_in_globals :
    ∀ id data, reg.allocToData.get? id = some data →
      ∃ g, w.findGlobal? id = some g ∧ g.kind = .vtable

theorem allocWF_empty : AllocWF empty KeyedAllocWorld.empty :=
  ⟨fun _ _ h => by simp [empty, ExtTreeMap0.get?_empty] at h⟩

theorem allocWF_intern {reg reg' : VTableRegistry} {w w' : KeyedAllocWorld}
    {key : VTableKey} {data : VTableData} {id : MiriAllocId}
    (hawf : AllocWF reg w) (h : reg.intern w key data = .ok (reg', w', id)) :
    AllocWF reg' w' := by
  unfold intern at h
  dsimp only at h
  cases hg : reg.keyToAlloc.get? (encodeVTableKeyCode key) with
  | some id0 =>
    rw [hg] at h; injection h with hpair
    rcases Prod.mk.inj hpair with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
    exact hawf
  | none =>
    rw [hg] at h
    cases hres : w.reserveAllocId with
    | mk w1 ores =>
      rw [hres] at h
      cases ores with
      | error _ => cases h
      | ok id1 =>
        simp only at h; injection h with hpair
        rcases Prod.mk.inj hpair with ⟨rfl, hrest⟩
        rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
        refine ⟨fun q dq hq => ?_⟩
        by_cases hqid : q = id1
        · subst hqid
          refine ⟨⟨.vtable, 24, 3, .not, []⟩, ?_, rfl⟩
          simp [KeyedAllocWorld.registerGlobal, KeyedAllocWorld.findGlobal?, ExtTreeMap0.get?_insert_self]
        · rw [ExtTreeMap0.get?_insert_ne _ _ hqid] at hq
          rcases hawf.data_in_globals q dq hq with ⟨g, hgq, hgk⟩
          refine ⟨g, ?_, hgk⟩
          simp only [KeyedAllocWorld.registerGlobal, KeyedAllocWorld.findGlobal?]
          rw [ExtTreeMap0.get?_insert_ne _ _ hqid]
          unfold KeyedAllocWorld.reserveAllocId at hres
          split at hres
          · simp at hres
          · split at hres
            · simp at hres
            · split at hres
              · simp at hres
              · injection hres with hw1 _; rw [← hw1]; exact hgq

theorem keyWF_intern {reg reg' : VTableRegistry} {w w' : KeyedAllocWorld}
    {key : VTableKey} {data : VTableData} {id : MiriAllocId}
    (hkwf : KeyWF reg)
    (hmatch : VTableDataMatchesKey key data)
    (hfreshAlloc : ∀ idNew, w.reserveAllocId.2 = .ok idNew → reg.allocToData.get? idNew = none)
    (hlayoutMatch : ∀ id₀ d₀, reg.allocToData.get? id₀ = some d₀ →
      d₀.concreteTyCode = data.concreteTyCode →
      d₀.dropFnId = data.dropFnId ∧ d₀.sizeBytes = data.sizeBytes ∧ d₀.alignPow2 = data.alignPow2)
    (h : reg.intern w key data = .ok (reg', w', id)) :
    KeyWF reg' := by
  unfold intern at h
  dsimp only at h
  cases hg : reg.keyToAlloc.get? (encodeVTableKeyCode key) with
  | some id0 =>
    rw [hg] at h; injection h with hpair
    rcases Prod.mk.inj hpair with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
    exact hkwf
  | none =>
    rw [hg] at h
    cases hres : w.reserveAllocId with
    | mk w1 ores =>
      rw [hres] at h
      cases ores with
      | error _ => cases h
      | ok id1 =>
        simp only at h; injection h with hpair
        rcases Prod.mk.inj hpair with ⟨rfl, hrest⟩
        rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
        have hnone1 : reg.allocToData.get? id1 = none := hfreshAlloc id1 (by rw [hres])
        refine ⟨?_, ?_⟩
        · intro k q hq
          by_cases hkeq : encodeVTableKeyCode k = encodeVTableKeyCode key
          · have hk : k = key := encodeVTableKeyCode_injective hkeq
            subst hk
            rw [ExtTreeMap0.get?_insert_self] at hq
            injection hq with hq; subst hq
            exact ⟨data, ExtTreeMap0.get?_insert_self _ _ _, hmatch⟩
          · rw [ExtTreeMap0.get?_insert_ne _ _ hkeq] at hq
            rcases hkwf.key_has_data k q hq with ⟨dq, hdq, hmk⟩
            have hqne : q ≠ id1 := fun heq => by subst heq; rw [hnone1] at hdq; cases hdq
            exact ⟨dq, by rw [ExtTreeMap0.get?_insert_ne _ _ hqne]; exact hdq, hmk⟩
        · intro i₁ d₁ i₂ d₂ h1 h2 hcode
          by_cases hi1 : i₁ = id1 <;> by_cases hi2 : i₂ = id1
          · subst hi1; subst hi2
            rw [ExtTreeMap0.get?_insert_self] at h1 h2
            injection h1 with h1; injection h2 with h2; subst h1; subst h2
            exact ⟨rfl, rfl, rfl⟩
          · subst hi1
            rw [ExtTreeMap0.get?_insert_self] at h1; injection h1 with h1; subst h1
            rw [ExtTreeMap0.get?_insert_ne _ _ hi2] at h2
            rcases hlayoutMatch i₂ d₂ h2 hcode.symm with ⟨a, b, c⟩
            exact ⟨a.symm, b.symm, c.symm⟩
          · subst hi2
            rw [ExtTreeMap0.get?_insert_self] at h2; injection h2 with h2; subst h2
            rw [ExtTreeMap0.get?_insert_ne _ _ hi1] at h1
            exact hlayoutMatch i₁ d₁ h1 hcode
          · rw [ExtTreeMap0.get?_insert_ne _ _ hi1] at h1
            rw [ExtTreeMap0.get?_insert_ne _ _ hi2] at h2
            exact hkwf.ty_layout_unique i₁ d₁ i₂ d₂ h1 h2 hcode

end VTableRegistry

/-- Upcast a vtable at `srcId` to a principal-less auto-trait object (`dyn Send`, etc.). -/
def upcastVTableToAutoTraits (reg : VTableRegistry) (w : KeyedAllocWorld)
    (srcId : MiriAllocId) (targetAutoTraits : List AutoTrait) :
    Option (Except AllocIdErr (VTableRegistry × KeyedAllocWorld × MiriAllocId)) :=
  match reg.allocToData.get? srcId with
  | none => none
  | some srcData =>
    let key := mkCanonicalVTableKey srcData.concreteTyCode none targetAutoTraits
    let upData := buildPrincipalLessVTable
      srcData.concreteTy srcData.concreteTyCode srcData.dropFnId
      srcData.sizeBytes srcData.alignPow2 targetAutoTraits
    some (reg.intern w key upData)

/-- Universal upcast preservation theorem: under `VTableRegistry.KeyWF`, upcasting preserves
`dropFnId`, `sizeBytes`, and `alignPow2` on both fresh allocations and cached hits. -/
theorem upcastVTableToAutoTraits_preserves_drop_size_align
    (reg reg' : VTableRegistry) (w w' : KeyedAllocWorld)
    (srcId dstId : MiriAllocId) (srcData : VTableData) (targetAutoTraits : List AutoTrait)
    (hkwf : VTableRegistry.KeyWF reg)
    (hsrc : reg.allocToData.get? srcId = some srcData)
    (hup : upcastVTableToAutoTraits reg w srcId targetAutoTraits = some (.ok (reg', w', dstId))) :
    ∃ dstData,
      reg'.allocToData.get? dstId = some dstData ∧
      dstData.spec.principal = none ∧
      dstData.dropFnId = srcData.dropFnId ∧
      dstData.sizeBytes = srcData.sizeBytes ∧
      dstData.alignPow2 = srcData.alignPow2 := by
  unfold upcastVTableToAutoTraits at hup
  rw [hsrc] at hup
  injection hup with hint
  unfold VTableRegistry.intern at hint
  dsimp only at hint
  cases hg : reg.keyToAlloc.get? (encodeVTableKeyCode (mkCanonicalVTableKey srcData.concreteTyCode none targetAutoTraits)) with
  | some cachedId =>
    rw [hg] at hint; injection hint with hpair
    rcases Prod.mk.inj hpair with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
    rcases hkwf.key_has_data _ cachedId hg with ⟨d, hd, hmk⟩
    rcases hkwf.ty_layout_unique cachedId d srcId srcData hd hsrc hmk.tyCode_eq with ⟨hd1, hd2, hd3⟩
    exact ⟨d, hd, hmk.principal_eq, hd1, hd2, hd3⟩
  | none =>
    rw [hg] at hint
    cases hres : w.reserveAllocId with
    | mk w1 ores =>
      rw [hres] at hint
      cases ores with
      | error _ => cases hint
      | ok newId =>
        simp only at hint; injection hint with hpair
        rcases Prod.mk.inj hpair with ⟨rfl, hrest⟩
        rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
        exact ⟨_, ExtTreeMap0.get?_insert_self _ _ _, rfl, rfl, rfl, rfl⟩

/-- Complete cross-table + global-allocation coherence invariant closing cached-hit orphan
and fresh-id clobbering gaps (`VTableWorldWF`). -/
structure VTableWorldWF (reg : VTableRegistry) (w : KeyedAllocWorld) : Prop where
  keyWF : VTableRegistry.KeyWF reg
  allocWF : VTableRegistry.AllocWF reg w
  alloc_issued : ∀ id, (reg.allocToData.get? id).isSome = true → w.hasIssued id = true

namespace VTableWorldWF

theorem empty : VTableWorldWF VTableRegistry.empty KeyedAllocWorld.empty :=
  ⟨VTableRegistry.keyWF_empty, VTableRegistry.allocWF_empty,
   fun _ h => by simp [VTableRegistry.empty, ExtTreeMap0.get?_empty] at h⟩

end VTableWorldWF

/-- Salted vtable key incorporating Miri's `globalSalt` (`VTable.lean:120`). -/
structure SaltedVTableKey where
  salt : Nat
  key : VTableKey
  deriving DecidableEq, Repr

def encodeSaltedVTableKeyCode (sk : SaltedVTableKey) : Nat :=
  cantorPair sk.salt (encodeVTableKeyCode sk.key)

theorem encodeSaltedVTableKeyCode_injective : Function.Injective encodeSaltedVTableKeyCode := by
  intro a b h
  unfold encodeSaltedVTableKeyCode at h
  have hp := cantorPair_injective (a₁ := (a.salt, encodeVTableKeyCode a.key)) (a₂ := (b.salt, encodeVTableKeyCode b.key)) h
  have hs : a.salt = b.salt := (Prod.mk.inj hp).1
  have hk : a.key = b.key := encodeVTableKeyCode_injective (Prod.mk.inj hp).2
  cases a; cases b; simp only at hs hk; subst hs; subst hk; rfl

/-- Salted vtable registry where distinct `globalSalt` values intern to distinct `MiriAllocId`s. -/
structure SaltedVTableRegistry where
  keyToAlloc : ExtTreeMap0 Nat MiriAllocId compare := ExtTreeMap0.empty
  allocToData : ExtTreeMap0 MiriAllocId VTableData compare := ExtTreeMap0.empty

namespace SaltedVTableRegistry

def empty : SaltedVTableRegistry := {}

def toVTableRegistry (sreg : SaltedVTableRegistry) : VTableRegistry where
  keyToAlloc := ExtTreeMap0.empty
  allocToData := sreg.allocToData

def internSalted (sreg : SaltedVTableRegistry) (w : KeyedAllocWorld)
    (sk : SaltedVTableKey) (data : VTableData) :
    Except AllocIdErr (SaltedVTableRegistry × KeyedAllocWorld × MiriAllocId) :=
  let code := encodeSaltedVTableKeyCode sk
  match sreg.keyToAlloc.get? code with
  | some id => .ok (sreg, w, id)
  | none =>
    let (w1, res) := w.reserveAllocId
    match res with
    | .error e => .error e
    | .ok id =>
      let w2 := w1.registerGlobal id ⟨.vtable, 24, 3, .not, []⟩
      let sreg' : SaltedVTableRegistry :=
        { keyToAlloc := sreg.keyToAlloc.insert code id
          allocToData := sreg.allocToData.insert id data }
      .ok (sreg', w2, id)

end SaltedVTableRegistry

/-- Cross-table + global-allocation coherence for `SaltedVTableRegistry`. -/
structure SaltedVTableWorldWF (sreg : SaltedVTableRegistry) (w : KeyedAllocWorld) : Prop where
  key_has_data :
    ∀ sk id, sreg.keyToAlloc.get? (encodeSaltedVTableKeyCode sk) = some id →
      ∃ data, sreg.allocToData.get? id = some data ∧ VTableDataMatchesKey sk.key data
  key_inj :
    ∀ sk₁ sk₂ id,
      sreg.keyToAlloc.get? (encodeSaltedVTableKeyCode sk₁) = some id →
      sreg.keyToAlloc.get? (encodeSaltedVTableKeyCode sk₂) = some id →
      sk₁ = sk₂
  alloc_in_globals :
    ∀ id data, sreg.allocToData.get? id = some data →
      ∃ g, w.findGlobal? id = some g ∧ g.kind = .vtable
  alloc_issued :
    ∀ id, (sreg.allocToData.get? id).isSome = true → w.hasIssued id = true

namespace SaltedVTableWorldWF

theorem empty : SaltedVTableWorldWF SaltedVTableRegistry.empty KeyedAllocWorld.empty :=
  ⟨fun _ _ h => by simp [SaltedVTableRegistry.empty, ExtTreeMap0.get?_empty] at h,
   fun _ _ _ h => by simp [SaltedVTableRegistry.empty, ExtTreeMap0.get?_empty] at h,
   fun _ _ h => by simp [SaltedVTableRegistry.empty, ExtTreeMap0.get?_empty] at h,
   fun _ h => by simp [SaltedVTableRegistry.empty, ExtTreeMap0.get?_empty] at h⟩

end SaltedVTableWorldWF

/-! ### 3C. Null-VTable UB Precedence (`lean-miri#82`), Unified `validateRawPtrFull`, & Deferred Recursive Pointee Byte Validator -/

/-- VTable pointer half of a wide `dyn` pointer. -/
inductive VTablePtrVal where
  | null
  | danglingInt (addr : UInt64)
  | provenanced (allocId : MiriAllocId) (offset : UInt64)
  deriving DecidableEq, Repr

/-- Data pointer half of a wide `dyn` pointer. -/
inductive WideDataPtrVal where
  | null
  | danglingInt (addr : UInt64)
  | maybeNull (allocId : MiriAllocId) (offset : UInt64) (addr : UInt64)
  | provenanced (allocId : MiriAllocId) (offset : UInt64) (addr : UInt64)
  deriving DecidableEq, Repr

/-- Deferred recursive pointee byte validation errors (`ValidityVisitor.visit`). -/
inductive PointeeByteErr where
  | uninitPointeeByte
  | outOfBoundsPointeeRead
  | invalidBoolScalar (byte : UInt8)
  | invalidCharScalar (codePoint : UInt32)
  | nullFnPtr
  | nestedNullSafeRef
  | nestedUninhabitedSafeRef
  | nestedUnalignedSafeRef (requiredAlign : UInt64) (addr : UInt64)
  | nestedAddressTooClose (sizeBytes : UInt64)
  | uninhabitedPointee
  | layoutErr (err : LayoutErr)
  | traversalFuelExhausted
  deriving DecidableEq, Repr

/-- Wide `dyn` safe-pointer and vtable validation errors (`lean-miri#82`). -/
inductive WideDynErr where
  | invalidVTableNull
  | invalidVTableDanglingInt (addr : UInt64)
  | invalidVTableNonzeroOffset (allocId : MiriAllocId) (offset : UInt64)
  | invalidVTableNotGlobalVTable (allocId : MiriAllocId)
  | invalidVTableMissingMetadata (allocId : MiriAllocId)
  | invalidVTableTrait (actual expected : DynExistentialSpec)
  | danglingOrOutOfBoundsData (addr : UInt64)
  | addressTooClose (sizeBytes : UInt64)
  | nullSafePointer
  | uninhabitedPointee
  | malformedVTableAlign (alignPow2 : UInt8)
  | unalignedSafePointer (requiredAlign : UInt64) (addr : UInt64)
  | pointeeErr (err : PointeeByteErr)
  deriving DecidableEq, Repr

/-- Validate the vtable metadata half (`Miri.Interpreter.VTable.getPtrVTableTypeRead`). -/
def validateVTableHalf (w : KeyedAllocWorld) (reg : VTableRegistry)
    (vptr : VTablePtrVal) (expected : DynExistentialSpec) : Except WideDynErr VTableData :=
  match vptr with
  | .null => .error .invalidVTableNull
  | .danglingInt addr => .error (.invalidVTableDanglingInt addr)
  | .provenanced id off =>
    if off != 0 then .error (.invalidVTableNonzeroOffset id off)
    else
      match w.findGlobal? id with
      | none => .error (.invalidVTableNotGlobalVTable id)
      | some g =>
        if g.kind != .vtable then .error (.invalidVTableNotGlobalVTable id)
        else
          match reg.allocToData.get? id with
          | none => .error (.invalidVTableMissingMetadata id)
          | some data =>
            if vtableMatchesExpectedSpec data.spec expected then .ok data
            else .error (.invalidVTableTrait data.spec expected)

theorem validateVTableHalf_sound_of_allocWF
    (w : KeyedAllocWorld) (reg : VTableRegistry) (id : MiriAllocId)
    (data : VTableData) (expected : DynExistentialSpec)
    (hawf : VTableRegistry.AllocWF reg w)
    (hdata : reg.allocToData.get? id = some data)
    (hmatch : vtableMatchesExpectedSpec data.spec expected = true) :
    validateVTableHalf w reg (.provenanced id 0) expected = .ok data := by
  rcases hawf.data_in_globals id data hdata with ⟨g, hg, hgk⟩
  simp [validateVTableHalf, hg, hgk, hdata, hmatch]

theorem validateVTableHalf_principalLess_ignores_autoTraits
    (w : KeyedAllocWorld) (reg : VTableRegistry) (id : MiriAllocId) (data : VTableData)
    (a₁ a₂ : AutoTraitSet)
    (hawf : VTableRegistry.AllocWF reg w)
    (hdata : reg.allocToData.get? id = some data)
    (hspec : data.spec = ⟨none, a₁, []⟩) :
    validateVTableHalf w reg (.provenanced id 0) ⟨none, a₂, []⟩ = .ok data := by
  apply validateVTableHalf_sound_of_allocWF w reg id data ⟨none, a₂, []⟩ hawf hdata
  simp [hspec, vtableMatchesExpectedSpec, canonicalNonAutoPredIds, DynExistentialSpec.effectivePreds, sortDedupKeyIds]

theorem validateVTableHalf_principalLess_vs_principal_invalidTrait
    (w : KeyedAllocWorld) (reg : VTableRegistry) (id : MiriAllocId) (data : VTableData)
    (a₁ a₂ : AutoTraitSet) (p : Nat)
    (hawf : VTableRegistry.AllocWF reg w)
    (hdata : reg.allocToData.get? id = some data)
    (hspec : data.spec = ⟨none, a₁, []⟩) :
    validateVTableHalf w reg (.provenanced id 0) ⟨some p, a₂, []⟩ =
      .error (.invalidVTableTrait data.spec ⟨some p, a₂, []⟩) := by
  rcases hawf.data_in_globals id data hdata with ⟨g, hg, hgk⟩
  have hmis : vtableMatchesExpectedSpec data.spec ⟨some p, a₂, []⟩ = false := by
    simp [hspec, vtableMatchesExpectedSpec, canonicalNonAutoPredIds,
      DynExistentialSpec.effectivePreds, sortDedupKeyIds, insertKeyIdSorted]
  simp [validateVTableHalf, hg, hgk, hdata, hmis]

/-- Complete `VTableWorldWF` interning round-trip theorem:
preserves `VTableWorldWF` AND guarantees `validateVTableHalf` succeeds on both fresh allocations and cached hits. -/
theorem VTableWorldWF.intern_roundTrip
    {reg reg' : VTableRegistry} {w w' : KeyedAllocWorld}
    {key : VTableKey} {data : VTableData} {id : MiriAllocId}
    (hwf : VTableWorldWF reg w)
    (hmatch : VTableDataMatchesKey key data)
    (hlayout : ∀ id₀ d₀, reg.allocToData.get? id₀ = some d₀ →
      d₀.concreteTyCode = data.concreteTyCode →
      d₀.dropFnId = data.dropFnId ∧ d₀.sizeBytes = data.sizeBytes ∧ d₀.alignPow2 = data.alignPow2)
    (h : reg.intern w key data = .ok (reg', w', id)) :
    VTableWorldWF reg' w' ∧
    ∀ expected : DynExistentialSpec,
      vtableMatchesExpectedSpec data.spec expected = true →
      ∃ d, validateVTableHalf w' reg' (.provenanced id 0) expected = .ok d := by
  have hfreshAlloc : ∀ idNew, w.reserveAllocId.2 = .ok idNew → reg.allocToData.get? idNew = none := by
    intro idNew hres
    cases hget : reg.allocToData.get? idNew with
    | none => rfl
    | some d =>
      have hiss : w.hasIssued idNew = true := hwf.alloc_issued idNew (by simp [hget])
      unfold KeyedAllocWorld.reserveAllocId at hres
      split at hres
      · simp at hres
      · split at hres
        · simp at hres
        · rename_i idR hof
          split at hres
          · simp at hres
          · rename_i hnot
            simp only at hres; injection hres with heq; subst heq
            simp [hiss] at hnot
  have hkwf' := VTableRegistry.keyWF_intern hwf.keyWF hmatch hfreshAlloc hlayout h
  have hawf' := VTableRegistry.allocWF_intern hwf.allocWF h
  have hiss' : ∀ q, (reg'.allocToData.get? q).isSome = true → w'.hasIssued q = true := by
    unfold VTableRegistry.intern at h
    dsimp only at h
    cases hg : reg.keyToAlloc.get? (encodeVTableKeyCode key) with
    | some _ =>
      rw [hg] at h; injection h with hpair
      rcases Prod.mk.inj hpair with ⟨rfl, hrest⟩
      rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
      exact hwf.alloc_issued
    | none =>
      rw [hg] at h
      cases hres : w.reserveAllocId with
      | mk w1 ores =>
        rw [hres] at h
        cases ores with
        | error _ => cases h
        | ok id1 =>
          simp only at h; injection h with hpair
          rcases Prod.mk.inj hpair with ⟨rfl, hrest⟩
          rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
          intro q hq
          by_cases hqid : q = id1
          · subst hqid
            simp [KeyedAllocWorld.registerGlobal, KeyedAllocWorld.hasIssued,
              ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.get?_insert_self]
          · rw [ExtTreeMap0.get?_insert_ne _ _ hqid] at hq
            have hqiss : w.hasIssued q = true := hwf.alloc_issued q hq
            simp only [KeyedAllocWorld.registerGlobal, KeyedAllocWorld.hasIssued,
              ExtTreeMap0.contains_eq_isSome_get?]
            rw [ExtTreeMap0.get?_insert_ne _ _ hqid]
            unfold KeyedAllocWorld.reserveAllocId at hres
            split at hres
            · simp at hres
            · split at hres
              · simp at hres
              · split at hres
                · simp at hres
                · injection hres with hw1 hok; injection hok with heq; subst heq
                  rw [← hw1]
                  simp only [ExtTreeMap0.get?_insert_ne _ _ hqid]
                  exact hqiss
  refine ⟨⟨hkwf', hawf', hiss'⟩, ?_⟩
  intro expected hexp
  have hidKey : reg'.keyToAlloc.get? (encodeVTableKeyCode key) = some id := by
    unfold VTableRegistry.intern at h
    dsimp only at h
    cases hg : reg.keyToAlloc.get? (encodeVTableKeyCode key) with
    | some id0 =>
      rw [hg] at h; injection h with hpair
      rcases Prod.mk.inj hpair with ⟨rfl, hrest⟩
      rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
      exact hg
    | none =>
      rw [hg] at h
      cases hres : w.reserveAllocId with
      | mk w1 ores =>
        rw [hres] at h
        cases ores with
        | error _ => cases h
        | ok id1 =>
          simp only at h; injection h with hpair
          rcases Prod.mk.inj hpair with ⟨rfl, hrest⟩
          rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
          exact ExtTreeMap0.get?_insert_self _ _ _
  rcases hkwf'.key_has_data key id hidKey with ⟨d, hd, hmd⟩
  have hmatchD : vtableMatchesExpectedSpec d.spec expected = true := by
    unfold vtableMatchesExpectedSpec at hexp ⊢
    rw [hmd.preds_canonical, ← hmatch.preds_canonical]
    exact hexp
  exact ⟨d, validateVTableHalf_sound_of_allocWF w' reg' id d expected hawf' hd hmatchD⟩

/-- Complete `SaltedVTableWorldWF` interning round-trip theorem. -/
theorem SaltedVTableWorldWF.internSalted_roundTrip
    {sreg sreg' : SaltedVTableRegistry} {w w' : KeyedAllocWorld}
    {sk : SaltedVTableKey} {data : VTableData} {id : MiriAllocId}
    (hwf : SaltedVTableWorldWF sreg w)
    (hmatch : VTableDataMatchesKey sk.key data)
    (h : sreg.internSalted w sk data = .ok (sreg', w', id)) :
    SaltedVTableWorldWF sreg' w' ∧
    ∀ expected : DynExistentialSpec,
      vtableMatchesExpectedSpec data.spec expected = true →
      ∃ d, validateVTableHalf w' sreg'.toVTableRegistry (.provenanced id 0) expected = .ok d := by
  unfold SaltedVTableRegistry.internSalted at h
  dsimp only at h
  cases hg : sreg.keyToAlloc.get? (encodeSaltedVTableKeyCode sk) with
  | some id0 =>
    rw [hg] at h; injection h with hpair
    rcases Prod.mk.inj hpair with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
    refine ⟨hwf, ?_⟩
    intro expected hexp
    rcases hwf.key_has_data sk id0 hg with ⟨d, hd, hmd⟩
    have hmatchD : vtableMatchesExpectedSpec d.spec expected = true := by
      unfold vtableMatchesExpectedSpec at hexp ⊢
      rw [hmd.preds_canonical, ← hmatch.preds_canonical]; exact hexp
    have hawf : VTableRegistry.AllocWF sreg.toVTableRegistry w := ⟨hwf.alloc_in_globals⟩
    exact ⟨d, validateVTableHalf_sound_of_allocWF w sreg.toVTableRegistry id0 d expected hawf hd hmatchD⟩
  | none =>
    rw [hg] at h
    cases hres : w.reserveAllocId with
    | mk w1 ores =>
      rw [hres] at h
      cases ores with
      | error _ => cases h
      | ok id1 =>
        simp only at h; injection h with hpair
        rcases Prod.mk.inj hpair with ⟨rfl, hrest⟩
        rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
        have hnone1 : sreg.allocToData.get? id1 = none := by
          cases hget : sreg.allocToData.get? id1 with
          | none => rfl
          | some d =>
            have hiss := hwf.alloc_issued id1 (by simp [hget])
            unfold KeyedAllocWorld.reserveAllocId at hres
            split at hres
            · simp at hres
            · split at hres
              · simp at hres
              · split at hres
                · simp at hres
                · rename_i hnot
                  injection hres with _ hok; injection hok with heq; subst heq
                  simp [hiss] at hnot
        have hwf' : SaltedVTableWorldWF
            { keyToAlloc := sreg.keyToAlloc.insert (encodeSaltedVTableKeyCode sk) id1
              allocToData := sreg.allocToData.insert id1 data }
            (w1.registerGlobal id1 ⟨.vtable, 24, 3, .not, []⟩) := by
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro sk' q hq
            by_cases hkeq : encodeSaltedVTableKeyCode sk' = encodeSaltedVTableKeyCode sk
            · have hsk : sk' = sk := encodeSaltedVTableKeyCode_injective hkeq
              subst hsk
              rw [ExtTreeMap0.get?_insert_self] at hq
              injection hq with hq; subst hq
              exact ⟨data, ExtTreeMap0.get?_insert_self _ _ _, hmatch⟩
            · rw [ExtTreeMap0.get?_insert_ne _ _ hkeq] at hq
              rcases hwf.key_has_data sk' q hq with ⟨dq, hdq, hmk⟩
              have hqne : q ≠ id1 := fun heq => by subst heq; rw [hnone1] at hdq; cases hdq
              exact ⟨dq, by rw [ExtTreeMap0.get?_insert_ne _ _ hqne]; exact hdq, hmk⟩
          · intro sk₁ sk₂ q h1 h2
            by_cases h1eq : encodeSaltedVTableKeyCode sk₁ = encodeSaltedVTableKeyCode sk <;>
            by_cases h2eq : encodeSaltedVTableKeyCode sk₂ = encodeSaltedVTableKeyCode sk
            · exact (encodeSaltedVTableKeyCode_injective h1eq).trans (encodeSaltedVTableKeyCode_injective h2eq).symm
            · rw [h1eq, ExtTreeMap0.get?_insert_self] at h1; injection h1 with hq; subst hq
              rw [ExtTreeMap0.get?_insert_ne _ _ h2eq] at h2
              rcases hwf.key_has_data sk₂ id1 h2 with ⟨_, hd, _⟩
              rw [hnone1] at hd; cases hd
            · rw [h2eq, ExtTreeMap0.get?_insert_self] at h2; injection h2 with hq; subst hq
              rw [ExtTreeMap0.get?_insert_ne _ _ h1eq] at h1
              rcases hwf.key_has_data sk₁ id1 h1 with ⟨_, hd, _⟩
              rw [hnone1] at hd; cases hd
            · rw [ExtTreeMap0.get?_insert_ne _ _ h1eq] at h1
              rw [ExtTreeMap0.get?_insert_ne _ _ h2eq] at h2
              exact hwf.key_inj sk₁ sk₂ q h1 h2
          · intro q dq hq
            by_cases hqid : q = id1
            · subst hqid
              exact ⟨⟨.vtable, 24, 3, .not, []⟩,
                by simp [KeyedAllocWorld.registerGlobal, KeyedAllocWorld.findGlobal?, ExtTreeMap0.get?_insert_self],
                rfl⟩
            · rw [ExtTreeMap0.get?_insert_ne _ _ hqid] at hq
              rcases hwf.alloc_in_globals q dq hq with ⟨g, hgq, hgk⟩
              refine ⟨g, ?_, hgk⟩
              simp only [KeyedAllocWorld.registerGlobal, KeyedAllocWorld.findGlobal?]
              rw [ExtTreeMap0.get?_insert_ne _ _ hqid]
              unfold KeyedAllocWorld.reserveAllocId at hres
              split at hres
              · simp at hres
              · split at hres
                · simp at hres
                · split at hres
                  · simp at hres
                  · injection hres with hw1 _; rw [← hw1]; exact hgq
          · intro q hq
            by_cases hqid : q = id1
            · subst hqid
              simp [KeyedAllocWorld.registerGlobal, KeyedAllocWorld.hasIssued,
                ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.get?_insert_self]
            · rw [ExtTreeMap0.get?_insert_ne _ _ hqid] at hq
              have hqiss : w.hasIssued q = true := hwf.alloc_issued q hq
              simp only [KeyedAllocWorld.registerGlobal, KeyedAllocWorld.hasIssued,
                ExtTreeMap0.contains_eq_isSome_get?]
              rw [ExtTreeMap0.get?_insert_ne _ _ hqid]
              unfold KeyedAllocWorld.reserveAllocId at hres
              split at hres
              · simp at hres
              · split at hres
                · simp at hres
                · split at hres
                  · simp at hres
                  · injection hres with hw1 hok; injection hok with heq; subst heq
                    rw [← hw1]
                    simp only [ExtTreeMap0.get?_insert_ne _ _ hqid]
                    exact hqiss
        refine ⟨hwf', ?_⟩
        intro expected hexp
        have hawf' : VTableRegistry.AllocWF
            ({ keyToAlloc := sreg.keyToAlloc.insert (encodeSaltedVTableKeyCode sk) id1
               allocToData := sreg.allocToData.insert id1 data } : SaltedVTableRegistry).toVTableRegistry
            (w1.registerGlobal id1 ⟨.vtable, 24, 3, .not, []⟩) := ⟨hwf'.alloc_in_globals⟩
        exact ⟨data, validateVTableHalf_sound_of_allocWF _ _ id1 data expected hawf'
          (ExtTreeMap0.get?_insert_self _ _ _) hexp⟩

/-- Distinct `globalSalt` values intern identical `(ty, trait)` vtables to distinct `MiriAllocId`s,
both valid against the same expected spec. -/
theorem saltedVTable_distinct_salts_distinct_allocIds_both_valid
    (sreg0 sreg1 sreg2 : SaltedVTableRegistry) (w0 w1 w2 : KeyedAllocWorld)
    (salt₁ salt₂ : Nat) (key : VTableKey) (data : VTableData)
    (id₁ id₂ : MiriAllocId) (expected : DynExistentialSpec)
    (hwf0 : SaltedVTableWorldWF sreg0 w0)
    (hmatch : VTableDataMatchesKey key data)
    (hneSalt : salt₁ ≠ salt₂)
    (hexp : vtableMatchesExpectedSpec data.spec expected = true)
    (h1 : sreg0.internSalted w0 ⟨salt₁, key⟩ data = .ok (sreg1, w1, id₁))
    (h2 : sreg1.internSalted w1 ⟨salt₂, key⟩ data = .ok (sreg2, w2, id₂)) :
    id₁ ≠ id₂ ∧
    (∃ d₁, validateVTableHalf w2 sreg2.toVTableRegistry (.provenanced id₁ 0) expected = .ok d₁) ∧
    (∃ d₂, validateVTableHalf w2 sreg2.toVTableRegistry (.provenanced id₂ 0) expected = .ok d₂) := by
  rcases SaltedVTableWorldWF.internSalted_roundTrip hwf0 hmatch h1 with ⟨hwf1, _⟩
  rcases SaltedVTableWorldWF.internSalted_roundTrip hwf1 hmatch h2 with ⟨hwf2, hval2⟩
  have hk1_in_1 : sreg1.keyToAlloc.get? (encodeSaltedVTableKeyCode ⟨salt₁, key⟩) = some id₁ := by
    unfold SaltedVTableRegistry.internSalted at h1
    dsimp only at h1
    cases hg : sreg0.keyToAlloc.get? (encodeSaltedVTableKeyCode ⟨salt₁, key⟩) with
    | some i0 =>
      rw [hg] at h1; injection h1 with hpair
      rcases Prod.mk.inj hpair with ⟨rfl, hrest⟩
      rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
      exact hg
    | none =>
      rw [hg] at h1
      cases hres : w0.reserveAllocId with
      | mk _ ores =>
        rw [hres] at h1
        cases ores with
        | error _ => cases h1
        | ok i1 =>
          simp only at h1; injection h1 with hpair
          rcases Prod.mk.inj hpair with ⟨rfl, hrest⟩
          rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
          exact ExtTreeMap0.get?_insert_self _ _ _
  have hcodeNe : encodeSaltedVTableKeyCode ⟨salt₁, key⟩ ≠ encodeSaltedVTableKeyCode ⟨salt₂, key⟩ := by
    intro heq
    have hsk := encodeSaltedVTableKeyCode_injective heq
    injection hsk with hs _; exact hneSalt hs
  have hk1_in_2 : sreg2.keyToAlloc.get? (encodeSaltedVTableKeyCode ⟨salt₁, key⟩) = some id₁ := by
    unfold SaltedVTableRegistry.internSalted at h2
    dsimp only at h2
    cases hg : sreg1.keyToAlloc.get? (encodeSaltedVTableKeyCode ⟨salt₂, key⟩) with
    | some _ =>
      rw [hg] at h2; injection h2 with hpair
      rcases Prod.mk.inj hpair with ⟨rfl, _⟩; exact hk1_in_1
    | none =>
      rw [hg] at h2
      cases hres : w1.reserveAllocId with
      | mk _ ores =>
        rw [hres] at h2
        cases ores with
        | error _ => cases h2
        | ok _ =>
          simp only at h2; injection h2 with hpair
          rcases Prod.mk.inj hpair with ⟨rfl, _⟩
          rw [ExtTreeMap0.get?_insert_ne _ _ hcodeNe]; exact hk1_in_1
  have hk2_in_2 : sreg2.keyToAlloc.get? (encodeSaltedVTableKeyCode ⟨salt₂, key⟩) = some id₂ := by
    unfold SaltedVTableRegistry.internSalted at h2
    dsimp only at h2
    cases hg : sreg1.keyToAlloc.get? (encodeSaltedVTableKeyCode ⟨salt₂, key⟩) with
    | some i0 =>
      rw [hg] at h2; injection h2 with hpair
      rcases Prod.mk.inj hpair with ⟨rfl, hrest⟩
      rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
      exact hg
    | none =>
      rw [hg] at h2
      cases hres : w1.reserveAllocId with
      | mk _ ores =>
        rw [hres] at h2
        cases ores with
        | error _ => cases h2
        | ok i1 =>
          simp only at h2; injection h2 with hpair
          rcases Prod.mk.inj hpair with ⟨rfl, hrest⟩
          rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
          exact ExtTreeMap0.get?_insert_self _ _ _
  refine ⟨?_, ?_, hval2 expected hexp⟩
  · intro heq; subst heq
    have hsk := hwf2.key_inj ⟨salt₁, key⟩ ⟨salt₂, key⟩ id₁ hk1_in_2 hk2_in_2
    injection hsk with hs _; exact hneSalt hs
  · rcases hwf2.key_has_data ⟨salt₁, key⟩ id₁ hk1_in_2 with ⟨d₁, hd₁, hmd₁⟩
    have hmatch1 : vtableMatchesExpectedSpec d₁.spec expected = true := by
      unfold vtableMatchesExpectedSpec at hexp ⊢
      rw [hmd₁.preds_canonical, ← hmatch.preds_canonical]; exact hexp
    exact ⟨d₁, validateVTableHalf_sound_of_allocWF w2 sreg2.toVTableRegistry id₁ d₁ expected
      ⟨hwf2.alloc_in_globals⟩ hd₁ hmatch1⟩

/-- Safe wide-`dyn` pointer validator matching `Miri.Interpreter.ValidityVisitor.checkSafe` (`lines 202-228`, `lean-miri#82`):
1. VTable metadata check FIRST (precedes ALL data-pointer UB).
2. If `!mayDangle`: pointer access check `w.checkPtrAccess` (where bare null / `danglingInt 0` classifies as
   `.nullSafePointer`, provenanced `.maybeNull` checks allocation liveness/bounds BEFORE null, and a
   zero-sized concrete pointee never dangles).
   If `mayDangle`: `addressTooClose` check (`addr + size ≥ 2^64 - 1`) on the pointer's absolute address,
   for integer AND provenanced pointers alike (Miri provenance has `OFFSET_IS_ADDR = true`).
3. Null check (`scalarMayBeNull`).
4. Alignment check (BEFORE concrete-pointee inhabitedness!).
5. Optional byte-free concrete-pointee inhabitedness summary when `recursive && !mayDangle`. -/
def validateWideDynSafePtr (w : KeyedAllocWorld) (reg : VTableRegistry)
    (vptr : VTablePtrVal) (dptr : WideDataPtrVal) (expected : DynExistentialSpec)
    (mayDangle : Bool := false) (recursive : Bool := false) :
    Except WideDynErr VTableData :=
  match validateVTableHalf w reg vptr expected with
  | .error e => .error e
  | .ok vt =>
    let size := vt.sizeBytes
    let align : UInt64 := (1 : UInt64) <<< vt.alignPow2.toUInt64
    let stepAccess : Except WideDynErr UInt64 :=
      if !mayDangle then
        match dptr with
        | .null => .error .nullSafePointer
        | .danglingInt addr =>
          if addr == 0 then .error .nullSafePointer
          else if size == 0 then .ok addr
          else .error (.danglingOrOutOfBoundsData addr)
        | .maybeNull id off addr =>
          if w.checkPtrAccess (some (id, off)) size.toNat then
            if addr == 0 then .error .nullSafePointer else .ok addr
          else .error (.danglingOrOutOfBoundsData addr)
        | .provenanced id off addr =>
          if w.checkPtrAccess (some (id, off)) size.toNat then
            if addr == 0 then .error .nullSafePointer else .ok addr
          else .error (.danglingOrOutOfBoundsData addr)
      else
        match dptr with
        | .null =>
          if size.toNat ≥ usizeMax64 then .error (.addressTooClose size)
          else .error .nullSafePointer
        | .danglingInt addr =>
          if addr.toNat + size.toNat ≥ usizeMax64 then .error (.addressTooClose size)
          else if addr == 0 then .error .nullSafePointer
          else .ok addr
        | .maybeNull _ _ addr =>
          if addr.toNat + size.toNat ≥ usizeMax64 then .error (.addressTooClose size)
          else if addr == 0 then .error .nullSafePointer
          else .ok addr
        | .provenanced _ _ addr =>
          if addr.toNat + size.toNat ≥ usizeMax64 then .error (.addressTooClose size)
          else if addr == 0 then .error .nullSafePointer
          else .ok addr
    match stepAccess with
    | .error e => .error e
    | .ok addr =>
      if vt.alignPow2.toNat > 29 then
        .error (.malformedVTableAlign vt.alignPow2)
      else if align.toNat > 1 && addr.toNat % align.toNat != 0 then
        .error (.unalignedSafePointer align addr)
      else if recursive && !mayDangle then
        match computeTyLayout vt.concreteTy with
        | .ok lay =>
          if !lay.isInhabited then .error .uninhabitedPointee else .ok vt
        | .error e => .error (.pointeeErr (.layoutErr e))
      else .ok vt

/-- Raw wide-`dyn` pointer metadata validator (`ValidityVisitor.primitive .rawPointer` line 326):
validates vtable identity while leaving the data pointer completely unchecked. -/
def validateRawWideDynPtrMeta (w : KeyedAllocWorld) (reg : VTableRegistry)
    (vptr : VTablePtrVal) (_dptr : WideDataPtrVal) (expected : DynExistentialSpec)
    (_recursive : Bool := false) : Except WideDynErr VTableData :=
  validateVTableHalf w reg vptr expected

/-- Unified raw pointer value supporting thin, slice-DST, and full `dyn`-DST pointers. -/
inductive FullRawPtrVal where
  | thin (addr : UInt64)
  | wideSlice (addr len : UInt64)
  | wideDyn (data : WideDataPtrVal) (vtable : VTablePtrVal)
  deriving DecidableEq, Repr

/-- Unified errors for `validateRawPtrFull`. -/
inductive FullRawPtrErr where
  | shapeOrLayout (err : RawPtrErr)
  | vtableInvalid (err : WideDynErr)
  deriving DecidableEq, Repr

/-- Unified end-to-end raw pointer validator integrating Parts 3A, 3B, and 3C:
- Syntactically `Sized` pointees take the `O(1)` fast path (skipping BOTH layout and vtable queries).
- Unsized pointees compute `computeTyLayout` FIRST (rejecting layout overflow before vtable checks),
  then enforce slice/foreign/full-vtable metadata validity (leaving raw data pointers unchecked). -/
def validateRawPtrFull (w : KeyedAllocWorld) (reg : VTableRegistry)
    (resolveTrait : String → DynExistentialSpec)
    (pointee : ProtoTy) (ptr : FullRawPtrVal) : Except FullRawPtrErr Unit :=
  if isSyntacticallySized pointee then
    match ptr with
    | .thin _ => .ok ()
    | _ => .error (.shapeOrLayout .expectedThinPtr)
  else
    match computeTyLayout pointee with
    | .error e => .error (.shapeOrLayout (.layoutFailed e))
    | .ok lay =>
      match lay.metaKind with
      | none | some .foreignNone =>
        match ptr with
        | .thin _ => .ok ()
        | _ => .error (.shapeOrLayout .expectedThinPtr)
      | some .sliceLen =>
        match ptr with
        | .wideSlice _ _ => .ok ()
        | _ => .error (.shapeOrLayout .expectedWideSliceMeta)
      | some .dynVTable =>
        match ptr with
        | .wideDyn dptr vptr =>
          let expected :=
            match unsizedDynTailTrait? pointee with
            | some name => resolveTrait name
            | none => ⟨none, AutoTraitSet.empty, []⟩
          match validateRawWideDynPtrMeta w reg vptr dptr expected with
          | .ok _ => .ok ()
          | .error e => .error (.vtableInvalid e)
        | _ => .error (.shapeOrLayout .expectedWideDynMeta)

/-! #### Part 3C Precedence & Unified Raw-Pointer Theorems -/

theorem wideDyn_invalidVTable_precedes_all_data_ub
    (w : KeyedAllocWorld) (reg : VTableRegistry)
    (vptr : VTablePtrVal) (dptr : WideDataPtrVal) (expected : DynExistentialSpec)
    (mayDangle recursive : Bool) (err : WideDynErr)
    (hvt : validateVTableHalf w reg vptr expected = .error err) :
    validateWideDynSafePtr w reg vptr dptr expected mayDangle recursive = .error err := by
  simp [validateWideDynSafePtr, hvt]

theorem wideDyn_doubleNull_separation
    (w : KeyedAllocWorld) (reg : VTableRegistry) (expected : DynExistentialSpec)
    (mayDangle recursive : Bool) :
    validateWideDynSafePtr w reg .null .null expected mayDangle recursive =
      .error .invalidVTableNull := by
  simp [validateWideDynSafePtr, validateVTableHalf]

theorem wideDyn_validVTable_nullData_reports_nullSafePointer
    (w : KeyedAllocWorld) (reg : VTableRegistry) (vptr : VTablePtrVal)
    (expected : DynExistentialSpec) (vt : VTableData)
    (mayDangle recursive : Bool)
    (hvt : validateVTableHalf w reg vptr expected = .ok vt)
    (hsz : vt.sizeBytes.toNat < usizeMax64) :
    validateWideDynSafePtr w reg vptr .null expected mayDangle recursive =
      .error .nullSafePointer := by
  have hnotClose : ¬ (vt.sizeBytes.toNat ≥ usizeMax64) := by omega
  cases mayDangle <;> simp [validateWideDynSafePtr, hvt, hnotClose]

theorem wideDyn_validVTable_dangling_and_unaligned
    (w : KeyedAllocWorld) (reg : VTableRegistry) (vptr : VTablePtrVal)
    (expected : DynExistentialSpec) (vt : VTableData)
    (liveId : MiriAllocId) (liveEntry : LiveAllocEntry)
    (hvt : validateVTableHalf w reg vptr expected = .ok vt)
    (hsz : vt.sizeBytes = 4) (hal : vt.alignPow2 = 2)
    (hlive : w.findLive? liveId = some liveEntry)
    (hbounds : liveEntry.sizeBytes.toNat ≥ 4) :
    validateWideDynSafePtr w reg vptr (.danglingInt 16) expected false false =
      .error (.danglingOrOutOfBoundsData 16) ∧
    validateWideDynSafePtr w reg vptr (.provenanced liveId 0 2) expected false false =
      .error (.unalignedSafePointer 4 2) := by
  have hinfo : w.getAllocInfo liveId = some ⟨liveEntry.sizeBytes, liveEntry.alignPow2, .liveData, liveEntry.mutability⟩ := by
    simp [KeyedAllocWorld.getAllocInfo, hlive]
  have hle : 4 ≤ liveEntry.sizeBytes.toNat := hbounds
  constructor
  · simp [validateWideDynSafePtr, hvt, hsz]
  · simp [validateWideDynSafePtr, hvt, hsz, hal, hinfo, KeyedAllocWorld.checkPtrAccess, hle]; rfl

/-- Access-before-null for provenanced maybe-null data pointers with a NON-zero-sized concrete pointee:
a zero-address pointer into a never-registered OR tombstoned (use-after-free) allocation reports
dangling, not null. -/
theorem wideDyn_validVTable_maybeNull_dangling_precedes_null
    (w : KeyedAllocWorld) (reg : VTableRegistry) (vptr : VTablePtrVal)
    (expected : DynExistentialSpec) (vt : VTableData) (deadId : MiriAllocId)
    (hvt : validateVTableHalf w reg vptr expected = .ok vt)
    (hsz : vt.sizeBytes ≠ 0)
    (hnoLiveInfo : ∀ info, w.getAllocInfo deadId = some info → info.kind = .dead) :
    validateWideDynSafePtr w reg vptr (.maybeNull deadId 0 0) expected false false =
      .error (.danglingOrOutOfBoundsData 0) := by
  have hszNat : (vt.sizeBytes.toNat == 0) = false := by
    cases hb : (vt.sizeBytes.toNat == 0) with
    | false => rfl
    | true =>
      exfalso
      apply hsz
      have h0 : vt.sizeBytes.toNat = 0 := eq_of_beq hb
      exact UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h0)
  have hacc : w.checkPtrAccess (some (deadId, 0)) vt.sizeBytes.toNat = false := by
    cases hinfo : w.getAllocInfo deadId with
    | none => simp [KeyedAllocWorld.checkPtrAccess, hszNat, hinfo]
    | some info => simp [KeyedAllocWorld.checkPtrAccess, hszNat, hinfo, hnoLiveInfo info hinfo]
  simp [validateWideDynSafePtr, hvt, hacc]

/-- Zero-sized concrete pointees never dangle behind a wide `dyn` pointer: with a `0`-byte align-`1`
vtable type, a non-null provenanced data pointer into ANY allocation (freed, never registered, or out
of bounds) is accepted, and a zero-address one reports null (never dangling). -/
theorem wideDyn_zstConcrete_never_dangles
    (w : KeyedAllocWorld) (reg : VTableRegistry) (vptr : VTablePtrVal)
    (expected : DynExistentialSpec) (vt : VTableData)
    (id : MiriAllocId) (off addr : UInt64)
    (hvt : validateVTableHalf w reg vptr expected = .ok vt)
    (hsz : vt.sizeBytes = 0) (hal : vt.alignPow2 = 0) (haddr : addr ≠ 0) :
    validateWideDynSafePtr w reg vptr (.provenanced id off addr) expected false false = .ok vt ∧
    validateWideDynSafePtr w reg vptr (.maybeNull id off addr) expected false false = .ok vt ∧
    validateWideDynSafePtr w reg vptr (.maybeNull id off 0) expected false false =
      .error .nullSafePointer := by
  have haddrF : (addr == 0) = false := beq_false_of_ne haddr
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [validateWideDynSafePtr, hvt, hsz, hal, haddrF, KeyedAllocWorld.checkPtrAccess]

theorem wideDyn_validVTable_danglingIntZero_reports_null
    (w : KeyedAllocWorld) (reg : VTableRegistry) (vptr : VTablePtrVal)
    (expected : DynExistentialSpec) (vt : VTableData) (recursive : Bool)
    (hvt : validateVTableHalf w reg vptr expected = .ok vt) :
    validateWideDynSafePtr w reg vptr (.danglingInt 0) expected false recursive =
      .error .nullSafePointer := by
  simp [validateWideDynSafePtr, hvt]

theorem wideDyn_mayDangle_addressTooClose_and_uninhabited_concrete_ok
    (w : KeyedAllocWorld) (reg : VTableRegistry) (vptr : VTablePtrVal)
    (expected : DynExistentialSpec) (vt : VTableData)
    (hvt : validateVTableHalf w reg vptr expected = .ok vt)
    (hsz : vt.sizeBytes = 4) (hal : vt.alignPow2 = 2)
    (_hconc : vt.concreteTy = .tuple [.uint 4, .never]) :
    validateWideDynSafePtr w reg vptr (.danglingInt (UInt64.ofNat (usizeMax64 - 4))) expected true true =
      .error (.addressTooClose 4) ∧
    validateWideDynSafePtr w reg vptr (.danglingInt 16) expected true true = .ok vt := by
  constructor
  · simp [validateWideDynSafePtr, hvt, hsz, usizeMax64]
  · simp [validateWideDynSafePtr, hvt, hsz, hal, usizeMax64]

/-- Under `mayDangle`, the address-space-end check applies to PROVENANCED data pointers as well (Miri
pointers carry absolute addresses, so `try_to_scalar_int` succeeds on them): a provenanced or
maybe-null pointer at `usize::MAX - 4` to a 4-byte pointee reports `.addressTooClose`, never `.ok`. -/
theorem wideDyn_mayDangle_provenanced_addressTooClose
    (w : KeyedAllocWorld) (reg : VTableRegistry) (vptr : VTablePtrVal)
    (expected : DynExistentialSpec) (vt : VTableData) (id : MiriAllocId) (off : UInt64)
    (recursive : Bool)
    (hvt : validateVTableHalf w reg vptr expected = .ok vt)
    (hsz : vt.sizeBytes = 4) :
    validateWideDynSafePtr w reg vptr
      (.provenanced id off (UInt64.ofNat (usizeMax64 - 4))) expected true recursive =
      .error (.addressTooClose 4) ∧
    validateWideDynSafePtr w reg vptr
      (.maybeNull id off (UInt64.ofNat (usizeMax64 - 4))) expected true recursive =
      .error (.addressTooClose 4) := by
  constructor <;> simp [validateWideDynSafePtr, hvt, hsz, usizeMax64]

theorem wideDyn_unaligned_precedes_concrete_uninhabited
    (w : KeyedAllocWorld) (reg : VTableRegistry) (vptr : VTablePtrVal)
    (expected : DynExistentialSpec) (vt : VTableData)
    (liveId : MiriAllocId) (liveEntry : LiveAllocEntry)
    (hvt : validateVTableHalf w reg vptr expected = .ok vt)
    (hsz : vt.sizeBytes = 4) (hal : vt.alignPow2 = 2)
    (hconc : vt.concreteTy = .tuple [.uint 4, .never])
    (hlive : w.findLive? liveId = some liveEntry)
    (hbounds : liveEntry.sizeBytes.toNat ≥ 4) :
    validateWideDynSafePtr w reg vptr (.provenanced liveId 0 2) expected false false =
      .error (.unalignedSafePointer 4 2) ∧
    validateWideDynSafePtr w reg vptr (.provenanced liveId 0 2) expected false true =
      .error (.unalignedSafePointer 4 2) ∧
    validateWideDynSafePtr w reg vptr (.provenanced liveId 0 16) expected false false = .ok vt ∧
    validateWideDynSafePtr w reg vptr (.provenanced liveId 0 16) expected false true =
      .error .uninhabitedPointee := by
  have hinfo : w.getAllocInfo liveId = some ⟨liveEntry.sizeBytes, liveEntry.alignPow2, .liveData, liveEntry.mutability⟩ := by
    simp [KeyedAllocWorld.getAllocInfo, hlive]
  have hle : 4 ≤ liveEntry.sizeBytes.toNat := hbounds
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [validateWideDynSafePtr, hvt, hsz, hal, hinfo, KeyedAllocWorld.checkPtrAccess, hle]; rfl
  · simp [validateWideDynSafePtr, hvt, hsz, hal, hinfo, KeyedAllocWorld.checkPtrAccess, hle]; rfl
  · simp [validateWideDynSafePtr, hvt, hsz, hal, hinfo, KeyedAllocWorld.checkPtrAccess, hle]
  · simp [validateWideDynSafePtr, hvt, hsz, hal, hconc, hinfo, KeyedAllocWorld.checkPtrAccess, hle,
      computeTyLayout, computeFieldsLayout, alignUpNat, maxObjectSize64]

theorem rawWideDyn_vtable_checked_data_unchecked
    (w : KeyedAllocWorld) (reg : VTableRegistry)
    (vptr : VTablePtrVal) (dptr : WideDataPtrVal) (expected : DynExistentialSpec)
    (recursive : Bool) (vt : VTableData)
    (hvt : validateVTableHalf w reg vptr expected = .ok vt) :
    validateRawWideDynPtrMeta w reg vptr dptr expected recursive = .ok vt := by
  simp [validateRawWideDynPtrMeta, hvt]

theorem rawWideDyn_shapeCheck_misses_invalid_vtable
    (w : KeyedAllocWorld) (reg : VTableRegistry) (expected : DynExistentialSpec)
    (addr : UInt64) (dptr : WideDataPtrVal) :
    validateRawPtrFastPath (.dynamic "Send") (.wideDyn addr 0) = .ok () ∧
    validateRawWideDynPtrMeta w reg .null dptr expected = .error .invalidVTableNull := by
  exact ⟨rfl, rfl⟩

theorem validateRawPtrFull_sized_skips_layout_and_vtable
    (w : KeyedAllocWorld) (reg : VTableRegistry) (resolveTrait : String → DynExistentialSpec)
    (pointee : ProtoTy) (addr : UInt64)
    (hsized : isSyntacticallySized pointee = true) :
    validateRawPtrFull w reg resolveTrait pointee (.thin addr) = .ok () := by
  simp [validateRawPtrFull, hsized]

theorem validateRawPtrFull_customDynDst_layout_and_vtable_soundness
    (w : KeyedAllocWorld) (reg : VTableRegistry) (resolveTrait : String → DynExistentialSpec)
    (traitName : String) (dptr : WideDataPtrVal) (vptr : VTablePtrVal) :
    let customOverflow := ProtoTy.adt "OverflowDst" [.array (.uint 1) usizeMax64, .dynamic traitName]
    let customValid := ProtoTy.adt "MyDynDst" [.uint 4, .dynamic traitName]
    validateRawPtrFull w reg resolveTrait customOverflow (.wideDyn dptr .null) =
      .error (.shapeOrLayout (.layoutFailed .layoutOverflow)) ∧
    (∀ vt, validateVTableHalf w reg vptr (resolveTrait traitName) = .ok vt →
      validateRawPtrFull w reg resolveTrait customValid (.wideDyn dptr vptr) = .ok ()) ∧
    (∀ err, validateVTableHalf w reg vptr (resolveTrait traitName) = .error err →
      validateRawPtrFull w reg resolveTrait customValid (.wideDyn dptr vptr) = .error (.vtableInvalid err)) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold validateRawPtrFull
    have hns : isSyntacticallySized (.adt "OverflowDst" [.array (.uint 1) usizeMax64, .dynamic traitName]) = false := rfl
    have hov : computeTyLayout (.adt "OverflowDst" [.array (.uint 1) usizeMax64, .dynamic traitName]) = .error .layoutOverflow := by
      simp [computeTyLayout, computeFieldsLayout, maxObjectSize64, usizeMax64]
    simp [hns, hov]
  · intro vt hvt
    unfold validateRawPtrFull
    have hns : isSyntacticallySized (.adt "MyDynDst" [.uint 4, .dynamic traitName]) = false := rfl
    have hlay : computeTyLayout (.adt "MyDynDst" [.uint 4, .dynamic traitName]) = .ok ⟨4, 4, false, true, some .dynVTable⟩ := by
      simp [computeTyLayout, computeFieldsLayout, alignUpNat, maxObjectSize64]
    have htr : unsizedDynTailTrait? (.adt "MyDynDst" [.uint 4, .dynamic traitName]) = some traitName := rfl
    simp [hns, hlay, htr, validateRawWideDynPtrMeta, hvt]
  · intro err herr
    unfold validateRawPtrFull
    have hns : isSyntacticallySized (.adt "MyDynDst" [.uint 4, .dynamic traitName]) = false := rfl
    have hlay : computeTyLayout (.adt "MyDynDst" [.uint 4, .dynamic traitName]) = .ok ⟨4, 4, false, true, some .dynVTable⟩ := by
      simp [computeTyLayout, computeFieldsLayout, alignUpNat, maxObjectSize64]
    have htr : unsizedDynTailTrait? (.adt "MyDynDst" [.uint 4, .dynamic traitName]) = some traitName := rfl
    simp [hns, hlay, htr, validateRawWideDynPtrMeta, herr]

/-! #### Deferred Recursive Pointee Byte Visitor (`validateWideDynSafePtrWithBytes`) -/

/-- Valid Rust Unicode scalar value (`0x0000..=0xD7FF` or `0xE000..=0x10FFFF`). -/
def isUnicodeScalarValue (cp : UInt32) : Bool :=
  decide (cp.toNat ≤ 0xD7FF) || (decide (0xE000 ≤ cp.toNat) && decide (cp.toNat ≤ 0x10FFFF))

/-- Compute `(byteOffset, fieldTy)` pairs for a tuple or single-variant struct matching `computeFieldsLayout`. -/
def fieldByteOffsetsAux (curOff : Nat) : List ProtoTy → Except LayoutErr (List (Nat × ProtoTy))
  | [] => .ok []
  | f :: rest =>
    match computeTyLayout f with
    | .error e => .error e
    | .ok fl =>
      let off := alignUpNat curOff fl.alignBytes
      match fieldByteOffsetsAux (off + fl.sizeBytes) rest with
      | .error e => .error e
      | .ok tail => .ok ((off, f) :: tail)

def fieldByteOffsets (fields : List ProtoTy) : Except LayoutErr (List (Nat × ProtoTy)) :=
  fieldByteOffsetsAux 0 fields

/-- Read `len` bytes starting at `offset` from `bytes`, distinguishing out-of-bounds from `.uninit`. -/
def readInitBytesAt (bytes : List MemByte) (offset len : Nat) :
    Except PointeeByteErr (List (UInt8 × Option MiriAllocId)) :=
  let rec go : Nat → Nat → Except PointeeByteErr (List (UInt8 × Option MiriAllocId))
    | _, 0 => .ok []
    | idx, n + 1 =>
      match bytes[idx]? with
      | none => .error .outOfBoundsPointeeRead
      | some .uninit => .error .uninitPointeeByte
      | some (.init b p) =>
        match go (idx + 1) n with
        | .error e => .error e
        | .ok rest => .ok ((b, p) :: rest)
  go offset len

/-- Little-endian 4-byte unsigned integer decoding. -/
def decodeLeUInt32 : List (UInt8 × Option MiriAllocId) → UInt32
  | [(b0, _), (b1, _), (b2, _), (b3, _)] =>
    UInt32.ofNat (b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216)
  | _ => 0

/-- Little-endian 8-byte unsigned integer decoding. -/
def decodeLeUInt64 : List (UInt8 × Option MiriAllocId) → UInt64
  | [(b0, _), (b1, _), (b2, _), (b3, _), (b4, _), (b5, _), (b6, _), (b7, _)] =>
    UInt64.ofNat (
      b0.toNat +
      b1.toNat * 256 +
      b2.toNat * 65536 +
      b3.toNat * 16777216 +
      b4.toNat * 4294967296 +
      b5.toNat * 1099511627776 +
      b6.toNat * 281474976710656 +
      b7.toNat * 72057594037927936)
  | _ => 0

/-- Nested thin safe reference check under `childSession` (`flags.mayDangle = true, refTracking = none`):
- Rejects unsized pointees (wide references cannot be validated as 8-byte thin pointers).
- Accepts aligned non-null dangling integer `&u32` (does NOT check allocation liveness).
- Rejects zero-address pointers (provenance-agnostic `scalarMayBeNull`), `&!`, unaligned addresses,
  and addresses too close to the address-space end (`addr + size ≥ 2^64 - 1`) — for integer AND
  provenanced pointers alike, since Miri pointers carry absolute addresses (`OFFSET_IS_ADDR = true`). -/
def checkNestedSafeRefChildSession (inner : ProtoTy) (rawBytes : List (UInt8 × Option MiriAllocId)) :
    Except PointeeByteErr Unit :=
  match computeTyLayout inner with
  | .error e => .error (.layoutErr e)
  | .ok lay =>
    if !lay.isSized then
      .error (.layoutErr .unsizedField)
    else
      let addr := decodeLeUInt64 rawBytes
      if addr.toNat + lay.sizeBytes ≥ usizeMax64 then
        .error (.nestedAddressTooClose (UInt64.ofNat lay.sizeBytes))
      else if addr == 0 then
        .error .nestedNullSafeRef
      else if !lay.isInhabited then
        .error .nestedUninhabitedSafeRef
      else if lay.alignBytes > 1 && addr.toNat % lay.alignBytes != 0 then
        .error (.nestedUnalignedSafeRef (UInt64.ofNat lay.alignBytes) addr)
      else .ok ()

/-- Under `childSession` (`mayDangle = true`) the address-space-end check is provenance-agnostic:
a nested `&u32` whose 8 data bytes encode `usize::MAX - 4` is rejected with `.nestedAddressTooClose`
whether or not the bytes carry provenance (Miri pointers carry absolute addresses). -/
theorem checkNestedSafeRefChildSession_addressTooClose_ignores_provenance (prov : Option MiriAllocId) :
    checkNestedSafeRefChildSession (.uint 4)
      [(0xFB, prov), (0xFF, prov), (0xFF, prov), (0xFF, prov),
       (0xFF, prov), (0xFF, prov), (0xFF, prov), (0xFF, prov)] =
      .error (.nestedAddressTooClose 4) := by
  rfl

/-- Fail-closed unsized-inner rejection: `checkNestedSafeRefChildSession` refuses to treat an 8-byte
thin reference slot as a valid wide `&[u32]` / `&dyn Send` pointer. -/
theorem checkNestedSafeRefChildSession_unsizedInner_rejected
    (rawBytes : List (UInt8 × Option MiriAllocId)) :
    checkNestedSafeRefChildSession (.slice (.uint 4)) rawBytes = .error (.layoutErr .unsizedField) ∧
    checkNestedSafeRefChildSession (.dynamic "Send") rawBytes = .error (.layoutErr .unsizedField) :=
  ⟨rfl, rfl⟩

mutual
/-- Recursive pointee byte visitor matching `ValidityVisitor.visit` (`lines 300-471`):
- Fail-closed fuel exhaustion (`fuel = 0 => .error .traversalFuelExhausted`).
- Provenance-agnostic zero-address `fn()` rejection (`scalarMayBeNull`).
- `O(1)` ZST-array index-`0` fast path (`ValidityVisitor.lean:381-386`).
- In-order field traversal running BEFORE post-visit uninhabitedness check (`ValidityVisitor.lean:442-471`). -/
def visitConcreteValue (fuel : Nat) (bytes : List MemByte) (offset : Nat) (ty : ProtoTy) :
    Except PointeeByteErr Unit :=
  match fuel with
  | 0 => .error .traversalFuelExhausted
  | fuel' + 1 =>
    match ty with
    | .never => .error .uninhabitedPointee
    | .unit => .ok ()
    | .bool =>
      match readInitBytesAt bytes offset 1 with
      | .error e => .error e
      | .ok [(b, _)] =>
        if b == 0 || b == 1 then .ok () else .error (.invalidBoolScalar b)
      | .ok _ => .error .outOfBoundsPointeeRead
    | .char =>
      match readInitBytesAt bytes offset 4 with
      | .error e => .error e
      | .ok bs =>
        let cp := decodeLeUInt32 bs
        if isUnicodeScalarValue cp then .ok () else .error (.invalidCharScalar cp)
    | .uint sz =>
      match readInitBytesAt bytes offset sz with
      | .error e => .error e
      | .ok _ => .ok ()
    | .fnPtr =>
      match readInitBytesAt bytes offset 8 with
      | .error e => .error e
      | .ok bs =>
        let addr := decodeLeUInt64 bs
        if addr == 0 then .error .nullFnPtr else .ok ()
    | .rawPtr _ inner =>
      let ptrWidth :=
        match unsizedMetadataTail inner with
        | none | some .foreignNone => 8
        | some .sliceLen | some .dynVTable => 16
      match readInitBytesAt bytes offset ptrWidth with
      | .error e => .error e
      | .ok _ => .ok ()
    | .ref _ inner =>
      match readInitBytesAt bytes offset 8 with
      | .error e => .error e
      | .ok bs => checkNestedSafeRefChildSession inner bs
    | .array elem len =>
      match computeTyLayout elem with
      | .error e => .error (.layoutErr e)
      | .ok el =>
        if !el.isSized then .error (.layoutErr .unsizedField)
        else if el.sizeBytes == 0 then
          if len == 0 then .ok ()
          else visitConcreteValue fuel' bytes offset elem
        else
          visitArrayElems fuel' bytes offset el.sizeBytes elem len
    | .tuple fields =>
      match fieldByteOffsets fields with
      | .error e => .error (.layoutErr e)
      | .ok foffs => visitFieldList fuel' bytes offset foffs
    | .adt _ fields =>
      match fieldByteOffsets fields with
      | .error e => .error (.layoutErr e)
      | .ok foffs => visitFieldList fuel' bytes offset foffs
    | .slice _ | .str | .dynamic _ | .foreign =>
      .error (.layoutErr .unsizedField)

def visitArrayElems (fuel : Nat) (bytes : List MemByte) (offset stride : Nat)
    (elem : ProtoTy) : Nat → Except PointeeByteErr Unit
  | 0 => .ok ()
  | remaining + 1 =>
    match visitConcreteValue fuel bytes offset elem with
    | .error e => .error e
    | .ok () => visitArrayElems fuel bytes (offset + stride) stride elem remaining

def visitFieldList (fuel : Nat) (bytes : List MemByte) (baseOff : Nat) :
    List (Nat × ProtoTy) → Except PointeeByteErr Unit
  | [] => .ok ()
  | (fOff, fTy) :: rest =>
    match visitConcreteValue fuel bytes (baseOff + fOff) fTy with
    | .error e => .error e
    | .ok () => visitFieldList fuel bytes baseOff rest
end

/-- Deferred tracked concrete-pointee visit (`ValidityVisitor.visit`, lines 442-471):
visits fields/contents FIRST and checks `!lay.isInhabited` AFTER visiting. -/
def visitTrackedConcretePointee (fuel : Nat) (bytes : List MemByte) (baseOff : Nat)
    (concreteTy : ProtoTy) : Except PointeeByteErr Unit :=
  match visitConcreteValue fuel bytes baseOff concreteTy with
  | .error e => .error e
  | .ok () =>
    match computeTyLayout concreteTy with
    | .error e => .error (.layoutErr e)
    | .ok lay =>
      if !lay.isInhabited then .error .uninhabitedPointee else .ok ()

/-- Full wide-`dyn` safe-pointer validator with deferred recursive pointee byte checking:
runs root `validateWideDynSafePtr … (recursive := false)` first, then when `recursive && !mayDangle`
loads bytes via `w.findAllocBytes?` (covering live locals AND uncached `.static` / `.memory` globals)
and dispatches `visitTrackedConcretePointee` under `childSession` (`mayDangle = true`), attributing
pointee errors under `.pointeeErr`. -/
def validateWideDynSafePtrWithBytes (w : KeyedAllocWorld) (reg : VTableRegistry)
    (vptr : VTablePtrVal) (dptr : WideDataPtrVal) (expected : DynExistentialSpec)
    (mayDangle : Bool := false) (recursive : Bool := false) (fuel : Nat := 64) :
    Except WideDynErr VTableData :=
  match validateWideDynSafePtr w reg vptr dptr expected mayDangle false with
  | .error e => .error e
  | .ok vt =>
    if recursive && !mayDangle then
      let (bytes, baseOff) :=
        match dptr with
        | .provenanced id off _ => ((w.findAllocBytes? id).getD [], off.toNat)
        | .maybeNull id off _ => ((w.findAllocBytes? id).getD [], off.toNat)
        | .danglingInt _ | .null => ([], 0)
      match visitTrackedConcretePointee fuel bytes baseOff vt.concreteTy with
      | .ok () => .ok vt
      | .error pe => .error (.pointeeErr pe)
    else .ok vt

/-- Helper constructing an `n`-level nested single-element array `[[...[base; 1]...; 1]; 1]`. -/
def nestSingleElemArray : Nat → ProtoTy → ProtoTy
  | 0, base => base
  | n + 1, base => .array (nestSingleElemArray n base) 1

/-- Encode a 64-bit integer as 8 little-endian initialized `MemByte`s with optional provenance. -/
def encodeLeUInt64Bytes (v : UInt64) (prov : Option MiriAllocId := none) : List MemByte :=
  let n := v.toNat
  [ .init (UInt8.ofNat (n % 256)) prov,
    .init (UInt8.ofNat ((n / 256) % 256)) prov,
    .init (UInt8.ofNat ((n / 65536) % 256)) prov,
    .init (UInt8.ofNat ((n / 16777216) % 256)) prov,
    .init (UInt8.ofNat ((n / 4294967296) % 256)) prov,
    .init (UInt8.ofNat ((n / 1099511627776) % 256)) prov,
    .init (UInt8.ofNat ((n / 281474976710656) % 256)) prov,
    .init (UInt8.ofNat ((n / 72057594037927936) % 256)) prov ]

/-- Encode a 32-bit integer as 4 little-endian initialized `MemByte`s. -/
def encodeLeUInt32Bytes (v : UInt32) : List MemByte :=
  let n := v.toNat
  [ .init (UInt8.ofNat (n % 256)) none,
    .init (UInt8.ofNat ((n / 256) % 256)) none,
    .init (UInt8.ofNat ((n / 65536) % 256)) none,
    .init (UInt8.ofNat ((n / 16777216) % 256)) none ]

/-- Recursive byte validation & `childSession` (`mayDangle = true`) theorem:
1. `.uninit` and invalid `0x02 : bool` pass non-recursively and fail recursively.
2. Under `recursive = true`, nested `&u32` at `0` fails (`.nestedNullSafeRef`), nested `&!` at `16` fails
   (`.nestedUninhabitedSafeRef`), and aligned non-null dangling integer `&u32` at `16` SUCCEEDS. -/
theorem wideDyn_recursive_bytes_and_childSession_mayDangle :
    let spec : DynExistentialSpec := ⟨none, AutoTraitSet.ofList [.send], []⟩
    let idVtBool : MiriAllocId := ⟨1, by decide⟩
    let idVtRefU32 : MiriAllocId := ⟨2, by decide⟩
    let idVtRefNever : MiriAllocId := ⟨3, by decide⟩
    let idLive : MiriAllocId := ⟨10, by decide⟩
    let vtBool := buildPrincipalLessVTable .bool 101 none 1 0 [.send]
    let vtRefU32 := buildPrincipalLessVTable (.ref false (.uint 4)) 102 none 8 3 [.send]
    let vtRefNever := buildPrincipalLessVTable (.ref false .never) 103 none 8 3 [.send]
    let reg : VTableRegistry :=
      { keyToAlloc := ExtTreeMap0.empty
        allocToData := ((ExtTreeMap0.empty.insert idVtBool vtBool).insert idVtRefU32 vtRefU32).insert idVtRefNever vtRefNever }
    let wBase : KeyedAllocWorld :=
      ((KeyedAllocWorld.empty.registerGlobal idVtBool ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtRefU32 ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtRefNever ⟨.vtable, 24, 3, .not, []⟩
    let wUninit := wBase.insertLive idLive ⟨1, 0, .stack, .mut, [.uninit]⟩
    let wBadBool := wBase.insertLive idLive ⟨1, 0, .stack, .mut, [.init 2 none]⟩
    let wNullRef := wBase.insertLive idLive ⟨8, 3, .stack, .mut, encodeLeUInt64Bytes 0⟩
    let wDanglingRef := wBase.insertLive idLive ⟨8, 3, .stack, .mut, encodeLeUInt64Bytes 16⟩
    validateWideDynSafePtrWithBytes wUninit reg (.provenanced idVtBool 0) (.provenanced idLive 0 16) spec false false = .ok vtBool ∧
    validateWideDynSafePtrWithBytes wUninit reg (.provenanced idVtBool 0) (.provenanced idLive 0 16) spec false true = .error (.pointeeErr .uninitPointeeByte) ∧
    validateWideDynSafePtrWithBytes wBadBool reg (.provenanced idVtBool 0) (.provenanced idLive 0 16) spec false false = .ok vtBool ∧
    validateWideDynSafePtrWithBytes wBadBool reg (.provenanced idVtBool 0) (.provenanced idLive 0 16) spec false true = .error (.pointeeErr (.invalidBoolScalar 2)) ∧
    validateWideDynSafePtrWithBytes wNullRef reg (.provenanced idVtRefU32 0) (.provenanced idLive 0 16) spec false true = .error (.pointeeErr .nestedNullSafeRef) ∧
    validateWideDynSafePtrWithBytes wDanglingRef reg (.provenanced idVtRefNever 0) (.provenanced idLive 0 16) spec false true = .error (.pointeeErr .nestedUninhabitedSafeRef) ∧
    validateWideDynSafePtrWithBytes wDanglingRef reg (.provenanced idVtRefU32 0) (.provenanced idLive 0 16) spec false true = .ok vtRefU32 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · unfold validateWideDynSafePtrWithBytes validateWideDynSafePtr validateVTableHalf
    simp [KeyedAllocWorld.insertLive, KeyedAllocWorld.registerGlobal, KeyedAllocWorld.getAllocInfo,
      KeyedAllocWorld.findAllocBytes?, KeyedAllocWorld.findLive?, KeyedAllocWorld.findGlobal?,
      ExtTreeMap0.get?_insert,
      buildPrincipalLessVTable, vtableMatchesExpectedSpec, canonicalNonAutoPredIds,
      DynExistentialSpec.effectivePreds, sortDedupKeyIds,
      KeyedAllocWorld.checkPtrAccess, visitTrackedConcretePointee, visitConcreteValue,
      readInitBytesAt, readInitBytesAt.go, encodeLeUInt64Bytes, decodeLeUInt64,
      checkNestedSafeRefChildSession, computeTyLayout, usizeMax64]
    try rfl

/-- Recursive aggregate (`(u8, bool)`), `char`, `fn()`, and deferred `(u32, !)` validation theorem. -/
theorem wideDyn_recursive_aggregate_char_fnPtr_contents :
    let spec : DynExistentialSpec := ⟨none, AutoTraitSet.ofList [.send], []⟩
    let idVtPair : MiriAllocId := ⟨1, by decide⟩
    let idVtChar : MiriAllocId := ⟨2, by decide⟩
    let idVtFn : MiriAllocId := ⟨3, by decide⟩
    let idVtUninhab : MiriAllocId := ⟨4, by decide⟩
    let idLive : MiriAllocId := ⟨10, by decide⟩
    let vtPair := buildPrincipalLessVTable (.tuple [.uint 1, .bool]) 201 none 2 0 [.send]
    let vtChar := buildPrincipalLessVTable .char 202 none 4 2 [.send]
    let vtFn := buildPrincipalLessVTable .fnPtr 203 none 8 3 [.send]
    let vtUninhab := buildPrincipalLessVTable (.tuple [.uint 4, .never]) 204 none 4 2 [.send]
    let reg : VTableRegistry :=
      { keyToAlloc := ExtTreeMap0.empty
        allocToData := (((ExtTreeMap0.empty.insert idVtPair vtPair).insert idVtChar vtChar).insert idVtFn vtFn).insert idVtUninhab vtUninhab }
    let wBase : KeyedAllocWorld :=
      (((KeyedAllocWorld.empty.registerGlobal idVtPair ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtChar ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtFn ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtUninhab ⟨.vtable, 24, 3, .not, []⟩
    let wPairBad := wBase.insertLive idLive ⟨2, 0, .stack, .mut, [.init 7 none, .init 2 none]⟩
    let wPairOk := wBase.insertLive idLive ⟨2, 0, .stack, .mut, [.init 7 none, .init 1 none]⟩
    let wCharSurr := wBase.insertLive idLive ⟨4, 2, .stack, .mut, encodeLeUInt32Bytes 0xD800⟩
    let wFnNull := wBase.insertLive idLive ⟨8, 3, .stack, .mut, encodeLeUInt64Bytes 0⟩
    let wUninhabInit := wBase.insertLive idLive ⟨4, 2, .stack, .mut, encodeLeUInt32Bytes 1⟩
    validateWideDynSafePtrWithBytes wPairBad reg (.provenanced idVtPair 0) (.provenanced idLive 0 16) spec false false = .ok vtPair ∧
    validateWideDynSafePtrWithBytes wPairBad reg (.provenanced idVtPair 0) (.provenanced idLive 0 16) spec false true = .error (.pointeeErr (.invalidBoolScalar 2)) ∧
    validateWideDynSafePtrWithBytes wPairOk reg (.provenanced idVtPair 0) (.provenanced idLive 0 16) spec false true = .ok vtPair ∧
    validateWideDynSafePtrWithBytes wCharSurr reg (.provenanced idVtChar 0) (.provenanced idLive 0 16) spec false true = .error (.pointeeErr (.invalidCharScalar 0xD800)) ∧
    validateWideDynSafePtrWithBytes wFnNull reg (.provenanced idVtFn 0) (.provenanced idLive 0 16) spec false true = .error (.pointeeErr .nullFnPtr) ∧
    validateWideDynSafePtrWithBytes wUninhabInit reg (.provenanced idVtUninhab 0) (.provenanced idLive 0 16) spec false true = .error (.pointeeErr .uninhabitedPointee) := by
  have hfPair : fieldByteOffsets [.uint 1, .bool] = .ok [(0, .uint 1), (1, .bool)] := rfl
  have hlPair : computeTyLayout (.tuple [.uint 1, .bool]) = .ok ⟨2, 1, true, true, none⟩ := rfl
  have hfUninhab : fieldByteOffsets [.uint 4, .never] = .ok [(0, .uint 4), (4, .never)] := rfl
  have hv1 : visitTrackedConcretePointee 64 [.init 7 none, .init 2 none] 0 (.tuple [.uint 1, .bool]) =
      .error (.invalidBoolScalar 2) := by
    simp only [visitTrackedConcretePointee, visitConcreteValue, hfPair, visitFieldList,
      readInitBytesAt, readInitBytesAt.go]; rfl
  have hv2 : visitTrackedConcretePointee 64 [.init 7 none, .init 1 none] 0 (.tuple [.uint 1, .bool]) =
      .ok () := by
    simp only [visitTrackedConcretePointee, visitConcreteValue, hfPair, hlPair, visitFieldList,
      readInitBytesAt, readInitBytesAt.go]; rfl
  have hv3 : visitTrackedConcretePointee 64 (encodeLeUInt32Bytes 0xD800) 0 .char =
      .error (.invalidCharScalar 0xD800) := by
    simp only [visitTrackedConcretePointee, visitConcreteValue, readInitBytesAt, readInitBytesAt.go,
      encodeLeUInt32Bytes, decodeLeUInt32, isUnicodeScalarValue]; rfl
  have hv4 : visitTrackedConcretePointee 64 (encodeLeUInt64Bytes 0) 0 .fnPtr =
      .error .nullFnPtr := by
    simp only [visitTrackedConcretePointee, visitConcreteValue, readInitBytesAt, readInitBytesAt.go,
      encodeLeUInt64Bytes, decodeLeUInt64]; rfl
  have hv5 : visitTrackedConcretePointee 64 (encodeLeUInt32Bytes 1) 0 (.tuple [.uint 4, .never]) =
      .error .uninhabitedPointee := by
    simp only [visitTrackedConcretePointee, visitConcreteValue, hfUninhab, visitFieldList,
      readInitBytesAt, readInitBytesAt.go, encodeLeUInt32Bytes]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold validateWideDynSafePtrWithBytes validateWideDynSafePtr validateVTableHalf
    simp [KeyedAllocWorld.insertLive, KeyedAllocWorld.registerGlobal, KeyedAllocWorld.getAllocInfo,
      KeyedAllocWorld.findLive?, KeyedAllocWorld.findGlobal?, ExtTreeMap0.get?_insert,
      buildPrincipalLessVTable, vtableMatchesExpectedSpec, canonicalNonAutoPredIds,
      DynExistentialSpec.effectivePreds, sortDedupKeyIds, KeyedAllocWorld.checkPtrAccess]
  · unfold validateWideDynSafePtrWithBytes validateWideDynSafePtr validateVTableHalf
    simp [KeyedAllocWorld.insertLive, KeyedAllocWorld.registerGlobal, KeyedAllocWorld.getAllocInfo,
      KeyedAllocWorld.findAllocBytes?, KeyedAllocWorld.findLive?, KeyedAllocWorld.findGlobal?, ExtTreeMap0.get?_insert,
      buildPrincipalLessVTable, vtableMatchesExpectedSpec, canonicalNonAutoPredIds,
      DynExistentialSpec.effectivePreds, sortDedupKeyIds, KeyedAllocWorld.checkPtrAccess, hv1]
  · unfold validateWideDynSafePtrWithBytes validateWideDynSafePtr validateVTableHalf
    simp [KeyedAllocWorld.insertLive, KeyedAllocWorld.registerGlobal, KeyedAllocWorld.getAllocInfo,
      KeyedAllocWorld.findAllocBytes?, KeyedAllocWorld.findLive?, KeyedAllocWorld.findGlobal?, ExtTreeMap0.get?_insert,
      buildPrincipalLessVTable, vtableMatchesExpectedSpec, canonicalNonAutoPredIds,
      DynExistentialSpec.effectivePreds, sortDedupKeyIds, KeyedAllocWorld.checkPtrAccess, hv2]
  · unfold validateWideDynSafePtrWithBytes validateWideDynSafePtr validateVTableHalf
    simp [KeyedAllocWorld.insertLive, KeyedAllocWorld.registerGlobal, KeyedAllocWorld.getAllocInfo,
      KeyedAllocWorld.findAllocBytes?, KeyedAllocWorld.findLive?, KeyedAllocWorld.findGlobal?, ExtTreeMap0.get?_insert,
      buildPrincipalLessVTable, vtableMatchesExpectedSpec, canonicalNonAutoPredIds,
      DynExistentialSpec.effectivePreds, sortDedupKeyIds, KeyedAllocWorld.checkPtrAccess, hv3]
  · unfold validateWideDynSafePtrWithBytes validateWideDynSafePtr validateVTableHalf
    simp [KeyedAllocWorld.insertLive, KeyedAllocWorld.registerGlobal, KeyedAllocWorld.getAllocInfo,
      KeyedAllocWorld.findAllocBytes?, KeyedAllocWorld.findLive?, KeyedAllocWorld.findGlobal?, ExtTreeMap0.get?_insert,
      buildPrincipalLessVTable, vtableMatchesExpectedSpec, canonicalNonAutoPredIds,
      DynExistentialSpec.effectivePreds, sortDedupKeyIds, KeyedAllocWorld.checkPtrAccess, hv4]
  · unfold validateWideDynSafePtrWithBytes validateWideDynSafePtr validateVTableHalf
    simp [KeyedAllocWorld.insertLive, KeyedAllocWorld.registerGlobal, KeyedAllocWorld.getAllocInfo,
      KeyedAllocWorld.findAllocBytes?, KeyedAllocWorld.findLive?, KeyedAllocWorld.findGlobal?, ExtTreeMap0.get?_insert,
      buildPrincipalLessVTable, vtableMatchesExpectedSpec, canonicalNonAutoPredIds,
      DynExistentialSpec.effectivePreds, sortDedupKeyIds, KeyedAllocWorld.checkPtrAccess, hv5]

/-- Field-before-inhabited precedence, provenance-agnostic zero-address `fn()` rejection,
`O(1)` ZST-array index-`0` fast path (`[(); usize::MAX]`, `[!; 0]`, `[!; usize::MAX]`),
and fail-closed depth-`64` fuel exhaustion (`ValidityVisitor.lean:334, 342-346, 381-386, 442-471`). -/
theorem wideDyn_recursive_fieldOrder_nullProvFn_zstArray_and_fuel :
    let spec : DynExistentialSpec := ⟨none, AutoTraitSet.ofList [.send], []⟩
    let idVtBoolNever : MiriAllocId := ⟨1, by decide⟩
    let idVtU32Never : MiriAllocId := ⟨2, by decide⟩
    let idVtFn : MiriAllocId := ⟨3, by decide⟩
    let idVtZstUnitArr : MiriAllocId := ⟨4, by decide⟩
    let idVtZstNeverEmpty : MiriAllocId := ⟨5, by decide⟩
    let idVtZstNeverBig : MiriAllocId := ⟨6, by decide⟩
    let idVtDeep : MiriAllocId := ⟨7, by decide⟩
    let idLive : MiriAllocId := ⟨10, by decide⟩
    let vtBoolNever := buildPrincipalLessVTable (.tuple [.bool, .never]) 301 none 1 0 [.send]
    let vtU32Never := buildPrincipalLessVTable (.tuple [.uint 4, .never]) 302 none 4 2 [.send]
    let vtFn := buildPrincipalLessVTable .fnPtr 303 none 8 3 [.send]
    let vtZstUnitArr := buildPrincipalLessVTable (.array .unit usizeMax64) 304 none 0 0 [.send]
    let vtZstNeverEmpty := buildPrincipalLessVTable (.array .never 0) 305 none 0 0 [.send]
    let vtZstNeverBig := buildPrincipalLessVTable (.array .never usizeMax64) 306 none 0 0 [.send]
    let vtDeep := buildPrincipalLessVTable (nestSingleElemArray 64 .bool) 307 none 1 0 [.send]
    let reg : VTableRegistry :=
      { keyToAlloc := ExtTreeMap0.empty
        allocToData := ((((((ExtTreeMap0.empty.insert idVtBoolNever vtBoolNever).insert idVtU32Never vtU32Never).insert idVtFn vtFn).insert idVtZstUnitArr vtZstUnitArr).insert idVtZstNeverEmpty vtZstNeverEmpty).insert idVtZstNeverBig vtZstNeverBig).insert idVtDeep vtDeep }
    let wBase : KeyedAllocWorld :=
      ((((((KeyedAllocWorld.empty.registerGlobal idVtBoolNever ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtU32Never ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtFn ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtZstUnitArr ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtZstNeverEmpty ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtZstNeverBig ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtDeep ⟨.vtable, 24, 3, .not, []⟩
    let wBoolNeverBad := wBase.insertLive idLive ⟨1, 0, .stack, .mut, [.init 2 none]⟩
    let wU32NeverUninit := wBase.insertLive idLive ⟨4, 2, .stack, .mut, [.uninit, .uninit, .uninit, .uninit]⟩
    let wFnNullProv := wBase.insertLive idLive ⟨8, 3, .stack, .mut, encodeLeUInt64Bytes 0 (some idLive)⟩
    let wDeepBool := wBase.insertLive idLive ⟨1, 0, .stack, .mut, [.init 1 none]⟩
    validateWideDynSafePtrWithBytes wBoolNeverBad reg (.provenanced idVtBoolNever 0) (.provenanced idLive 0 16) spec false true =
      .error (.pointeeErr (.invalidBoolScalar 2)) ∧
    validateWideDynSafePtrWithBytes wU32NeverUninit reg (.provenanced idVtU32Never 0) (.provenanced idLive 0 16) spec false true =
      .error (.pointeeErr .uninitPointeeByte) ∧
    validateWideDynSafePtrWithBytes wFnNullProv reg (.provenanced idVtFn 0) (.provenanced idLive 0 16) spec false true =
      .error (.pointeeErr .nullFnPtr) ∧
    validateWideDynSafePtrWithBytes wBase reg (.provenanced idVtZstUnitArr 0) (.danglingInt 16) spec false true =
      .ok vtZstUnitArr ∧
    validateWideDynSafePtrWithBytes wBase reg (.provenanced idVtZstNeverEmpty 0) (.danglingInt 16) spec false true =
      .ok vtZstNeverEmpty ∧
    validateWideDynSafePtrWithBytes wBase reg (.provenanced idVtZstNeverBig 0) (.danglingInt 16) spec false true =
      .error (.pointeeErr .uninhabitedPointee) ∧
    validateWideDynSafePtrWithBytes wDeepBool reg (.provenanced idVtDeep 0) (.provenanced idLive 0 16) spec false true 64 =
      .error (.pointeeErr .traversalFuelExhausted) := by
  have hdeep : visitConcreteValue 64 [.init 1 none] 0 (nestSingleElemArray 64 .bool) =
      .error .traversalFuelExhausted := by
    have hgen : ∀ n, visitConcreteValue n [.init 1 none] 0 (nestSingleElemArray n .bool) =
        .error .traversalFuelExhausted := by
      intro n
      induction n with
      | zero => simp [visitConcreteValue]
      | succ k ih =>
        have hlay : computeTyLayout (nestSingleElemArray k .bool) = .ok ⟨1, 1, true, true, none⟩ := by
          clear ih
          induction k with
          | zero => rfl
          | succ m ihm =>
            simp [nestSingleElemArray, computeTyLayout, ihm, maxObjectSize64]
        simp [nestSingleElemArray, visitConcreteValue, hlay, visitArrayElems, ih]
    exact hgen 64
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold validateWideDynSafePtrWithBytes validateWideDynSafePtr validateVTableHalf
    simp [KeyedAllocWorld.insertLive, KeyedAllocWorld.registerGlobal, KeyedAllocWorld.getAllocInfo,
      KeyedAllocWorld.findAllocBytes?, KeyedAllocWorld.findLive?, KeyedAllocWorld.findGlobal?, ExtTreeMap0.get?_insert,
      buildPrincipalLessVTable, vtableMatchesExpectedSpec, canonicalNonAutoPredIds,
      DynExistentialSpec.effectivePreds, sortDedupKeyIds, KeyedAllocWorld.checkPtrAccess,
      visitTrackedConcretePointee, visitConcreteValue, visitFieldList, fieldByteOffsets,
      fieldByteOffsetsAux, alignUpNat, readInitBytesAt, readInitBytesAt.go, computeTyLayout]
  · unfold validateWideDynSafePtrWithBytes validateWideDynSafePtr validateVTableHalf
    simp [KeyedAllocWorld.insertLive, KeyedAllocWorld.registerGlobal, KeyedAllocWorld.getAllocInfo,
      KeyedAllocWorld.findAllocBytes?, KeyedAllocWorld.findLive?, KeyedAllocWorld.findGlobal?, ExtTreeMap0.get?_insert,
      buildPrincipalLessVTable, vtableMatchesExpectedSpec, canonicalNonAutoPredIds,
      DynExistentialSpec.effectivePreds, sortDedupKeyIds, KeyedAllocWorld.checkPtrAccess,
      visitTrackedConcretePointee, visitConcreteValue, visitFieldList, fieldByteOffsets,
      fieldByteOffsetsAux, alignUpNat, readInitBytesAt, readInitBytesAt.go, computeTyLayout]
  · unfold validateWideDynSafePtrWithBytes validateWideDynSafePtr validateVTableHalf
    simp [KeyedAllocWorld.insertLive, KeyedAllocWorld.registerGlobal, KeyedAllocWorld.getAllocInfo,
      KeyedAllocWorld.findAllocBytes?, KeyedAllocWorld.findLive?, KeyedAllocWorld.findGlobal?, ExtTreeMap0.get?_insert,
      buildPrincipalLessVTable, vtableMatchesExpectedSpec, canonicalNonAutoPredIds,
      DynExistentialSpec.effectivePreds, sortDedupKeyIds, KeyedAllocWorld.checkPtrAccess,
      visitTrackedConcretePointee, visitConcreteValue, readInitBytesAt, readInitBytesAt.go,
      encodeLeUInt64Bytes, decodeLeUInt64]
  · unfold validateWideDynSafePtrWithBytes validateWideDynSafePtr validateVTableHalf
    simp [KeyedAllocWorld.registerGlobal, KeyedAllocWorld.findGlobal?, ExtTreeMap0.get?_insert,
      buildPrincipalLessVTable, vtableMatchesExpectedSpec, canonicalNonAutoPredIds,
      DynExistentialSpec.effectivePreds, sortDedupKeyIds, visitTrackedConcretePointee,
      visitConcreteValue, computeTyLayout, maxObjectSize64, usizeMax64]
  · unfold validateWideDynSafePtrWithBytes validateWideDynSafePtr validateVTableHalf
    simp [KeyedAllocWorld.registerGlobal, KeyedAllocWorld.findGlobal?, ExtTreeMap0.get?_insert,
      buildPrincipalLessVTable, vtableMatchesExpectedSpec, canonicalNonAutoPredIds,
      DynExistentialSpec.effectivePreds, sortDedupKeyIds, visitTrackedConcretePointee,
      visitConcreteValue, computeTyLayout, maxObjectSize64]
  · unfold validateWideDynSafePtrWithBytes validateWideDynSafePtr validateVTableHalf
    simp [KeyedAllocWorld.registerGlobal, KeyedAllocWorld.findGlobal?, ExtTreeMap0.get?_insert,
      buildPrincipalLessVTable, vtableMatchesExpectedSpec, canonicalNonAutoPredIds,
      DynExistentialSpec.effectivePreds, sortDedupKeyIds, visitTrackedConcretePointee,
      visitConcreteValue, computeTyLayout, usizeMax64]
  · unfold validateWideDynSafePtrWithBytes validateWideDynSafePtr validateVTableHalf
    simp [KeyedAllocWorld.insertLive, KeyedAllocWorld.registerGlobal, KeyedAllocWorld.getAllocInfo,
      KeyedAllocWorld.findAllocBytes?, KeyedAllocWorld.findLive?, KeyedAllocWorld.findGlobal?, ExtTreeMap0.get?_insert,
      buildPrincipalLessVTable, vtableMatchesExpectedSpec, canonicalNonAutoPredIds,
      DynExistentialSpec.effectivePreds, sortDedupKeyIds, KeyedAllocWorld.checkPtrAccess,
      visitTrackedConcretePointee, hdeep]

/-- Fail-closed vtable alignment and concrete-layout checks (`Miri.ABI.Align.MAX.pow2 = 29`,
`ValidityMachine.lean:168`):
1. `alignPow2 = 64` (which would wrap `(1 : UInt64) <<< 64 = 1`) and `alignPow2 = 30` (`> 29`) are
   rejected with `.malformedVTableAlign` instead of silently passing alignment.
2. A malformed concrete pointee layout (e.g. `.uint 3`) fails closed under `recursive = true` with
   `.pointeeErr (.layoutErr (.invalidScalarSize 3))` instead of silently returning `.ok vt`. -/
theorem wideDyn_malformedAlign_and_malformedConcreteLayout_failClosed
    (w : KeyedAllocWorld) (reg : VTableRegistry) (vptr : VTablePtrVal)
    (expected : DynExistentialSpec) (vtBad64 vtBad30 vtBadLay : VTableData)
    (liveId : MiriAllocId) (liveEntry : LiveAllocEntry)
    (hlive : w.findLive? liveId = some liveEntry)
    (hbounds : liveEntry.sizeBytes.toNat ≥ 4) :
    (validateVTableHalf w reg vptr expected = .ok vtBad64 →
      vtBad64.sizeBytes = 4 → vtBad64.alignPow2 = 64 →
      validateWideDynSafePtr w reg vptr (.provenanced liveId 0 16) expected false false =
        .error (.malformedVTableAlign 64)) ∧
    (validateVTableHalf w reg vptr expected = .ok vtBad30 →
      vtBad30.sizeBytes = 4 → vtBad30.alignPow2 = 30 →
      validateWideDynSafePtr w reg vptr (.provenanced liveId 0 16) expected false false =
        .error (.malformedVTableAlign 30)) ∧
    (validateVTableHalf w reg vptr expected = .ok vtBadLay →
      vtBadLay.sizeBytes = 4 → vtBadLay.alignPow2 = 2 → vtBadLay.concreteTy = .uint 3 →
      validateWideDynSafePtr w reg vptr (.provenanced liveId 0 16) expected false true =
        .error (.pointeeErr (.layoutErr (.invalidScalarSize 3)))) := by
  have hinfo : w.getAllocInfo liveId = some ⟨liveEntry.sizeBytes, liveEntry.alignPow2, .liveData, liveEntry.mutability⟩ := by
    simp [KeyedAllocWorld.getAllocInfo, hlive]
  have hle : 4 ≤ liveEntry.sizeBytes.toNat := hbounds
  refine ⟨fun hvt hsz hal => ?_, fun hvt hsz hal => ?_, fun hvt hsz hal hty => ?_⟩
  · simp [validateWideDynSafePtr, hvt, hsz, hal, hinfo, KeyedAllocWorld.checkPtrAccess, hle]
  · simp [validateWideDynSafePtr, hvt, hsz, hal, hinfo, KeyedAllocWorld.checkPtrAccess, hle]
  · simp [validateWideDynSafePtr, hvt, hsz, hal, hty, hinfo, KeyedAllocWorld.checkPtrAccess, hle,
      computeTyLayout]

/-- Recursive pointee byte validation on uncached `.static` / `.memory` globals (`&STATIC as &dyn Send`):
`validateWideDynSafePtrWithBytes` reads bytes via `w.findAllocBytes?` (not only `w.findLive?`), so a
valid immutable `.static` `bool` passes both shallow and recursive validation, an invalid `.static`
`bool = 2` reports `.invalidBoolScalar 2` (never spurious `.outOfBoundsPointeeRead`), and an
uninitialized `.memory` global reports `.uninitPointeeByte`. -/
theorem wideDyn_recursive_staticGlobal_bytes_validated :
    let spec : DynExistentialSpec := ⟨none, AutoTraitSet.ofList [.send], []⟩
    let idVtBool : MiriAllocId := ⟨1, by decide⟩
    let idStaticOk : MiriAllocId := ⟨20, by decide⟩
    let idStaticBad : MiriAllocId := ⟨21, by decide⟩
    let idMemUninit : MiriAllocId := ⟨22, by decide⟩
    let vtBool := buildPrincipalLessVTable .bool 401 none 1 0 [.send]
    let reg : VTableRegistry :=
      { keyToAlloc := ExtTreeMap0.empty
        allocToData := ExtTreeMap0.empty.insert idVtBool vtBool }
    let w : KeyedAllocWorld :=
      (((KeyedAllocWorld.empty.registerGlobal idVtBool ⟨.vtable, 24, 3, .not, []⟩)
        |>.registerGlobal idStaticOk ⟨.static, 1, 0, .not, [.init 1 none]⟩)
        |>.registerGlobal idStaticBad ⟨.static, 1, 0, .not, [.init 2 none]⟩)
        |>.registerGlobal idMemUninit ⟨.memory, 1, 0, .not, [.uninit]⟩
    w.findLive? idStaticOk = none ∧
    validateWideDynSafePtrWithBytes w reg (.provenanced idVtBool 0) (.provenanced idStaticOk 0 16) spec false false =
      .ok vtBool ∧
    validateWideDynSafePtrWithBytes w reg (.provenanced idVtBool 0) (.provenanced idStaticOk 0 16) spec false true =
      .ok vtBool ∧
    validateWideDynSafePtrWithBytes w reg (.provenanced idVtBool 0) (.provenanced idStaticBad 0 16) spec false true =
      .error (.pointeeErr (.invalidBoolScalar 2)) ∧
    validateWideDynSafePtrWithBytes w reg (.provenanced idVtBool 0) (.provenanced idMemUninit 0 16) spec false true =
      .error (.pointeeErr .uninitPointeeByte) := by
  have hvOk : visitTrackedConcretePointee 64 [.init 1 none] 0 .bool = .ok () := by
    simp only [visitTrackedConcretePointee, visitConcreteValue, readInitBytesAt, readInitBytesAt.go,
      computeTyLayout]; rfl
  have hvBad : visitTrackedConcretePointee 64 [.init 2 none] 0 .bool = .error (.invalidBoolScalar 2) := by
    simp only [visitTrackedConcretePointee, visitConcreteValue, readInitBytesAt, readInitBytesAt.go]; rfl
  have hvUninit : visitTrackedConcretePointee 64 [.uninit] 0 .bool = .error .uninitPointeeByte := by
    simp only [visitTrackedConcretePointee, visitConcreteValue, readInitBytesAt, readInitBytesAt.go]; rfl
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · unfold validateWideDynSafePtrWithBytes validateWideDynSafePtr validateVTableHalf
    simp [KeyedAllocWorld.empty, KeyedAllocWorld.registerGlobal, KeyedAllocWorld.getAllocInfo,
      KeyedAllocWorld.findLive?, KeyedAllocWorld.findGlobal?, ExtTreeMap0.get?_empty,
      ExtTreeMap0.get?_insert, buildPrincipalLessVTable, vtableMatchesExpectedSpec,
      canonicalNonAutoPredIds, DynExistentialSpec.effectivePreds, sortDedupKeyIds,
      KeyedAllocWorld.checkPtrAccess, GlobalAllocEntry.toAllocInfo]
  · unfold validateWideDynSafePtrWithBytes validateWideDynSafePtr validateVTableHalf
    simp [KeyedAllocWorld.empty, KeyedAllocWorld.registerGlobal, KeyedAllocWorld.getAllocInfo,
      KeyedAllocWorld.findAllocBytes?, KeyedAllocWorld.findLive?, KeyedAllocWorld.findGlobal?,
      ExtTreeMap0.get?_empty, ExtTreeMap0.get?_insert, buildPrincipalLessVTable,
      vtableMatchesExpectedSpec, canonicalNonAutoPredIds, DynExistentialSpec.effectivePreds,
      sortDedupKeyIds, KeyedAllocWorld.checkPtrAccess, GlobalAllocEntry.toAllocInfo, hvOk]
  · unfold validateWideDynSafePtrWithBytes validateWideDynSafePtr validateVTableHalf
    simp [KeyedAllocWorld.empty, KeyedAllocWorld.registerGlobal, KeyedAllocWorld.getAllocInfo,
      KeyedAllocWorld.findAllocBytes?, KeyedAllocWorld.findLive?, KeyedAllocWorld.findGlobal?,
      ExtTreeMap0.get?_empty, ExtTreeMap0.get?_insert, buildPrincipalLessVTable,
      vtableMatchesExpectedSpec, canonicalNonAutoPredIds, DynExistentialSpec.effectivePreds,
      sortDedupKeyIds, KeyedAllocWorld.checkPtrAccess, GlobalAllocEntry.toAllocInfo, hvBad]
  · unfold validateWideDynSafePtrWithBytes validateWideDynSafePtr validateVTableHalf
    simp [KeyedAllocWorld.empty, KeyedAllocWorld.registerGlobal, KeyedAllocWorld.getAllocInfo,
      KeyedAllocWorld.findAllocBytes?, KeyedAllocWorld.findLive?, KeyedAllocWorld.findGlobal?,
      ExtTreeMap0.get?_empty, ExtTreeMap0.get?_insert, buildPrincipalLessVTable,
      vtableMatchesExpectedSpec, canonicalNonAutoPredIds, DynExistentialSpec.effectivePreds,
      sortDedupKeyIds, KeyedAllocWorld.checkPtrAccess, GlobalAllocEntry.toAllocInfo, hvUninit]

end Anneal.ExtTreeMapAllocAndNoWritable
