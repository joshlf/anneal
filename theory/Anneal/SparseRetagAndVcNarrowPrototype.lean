-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean
import Trusted
import Anneal.Scalars
import Anneal.MirLiftCore

/-!
# Sparse Retag Attribute Indexing, Batched VC Call-Cone Narrowing, Demand-Time `#[track_caller]` `Location` Construction, and Lazy Write / Total Shift Hardening (Track P Prototype)

Prototype module for `ws-proto-sparse-retag-index-and-batched-vc-narrow` (paired Track A workstream
`ws-sparse-retag-index-and-batched-vc-narrow`). Every definition and theorem is stated over
Anneal's real `Trusted.Rustc.V2026_06_01` and `Anneal.MirLiftCore` types with zero `sorry`, zero
`Classical.choice`, zero `Lean.ofReduceBool`, and zero leaked global constants outside
`Anneal.SparseRetagAndVcNarrowPrototype`.

* **Part A (`SparseRetagAttrIndex`, `proofs-rs/lean-miri` PR #68)**: Constructive 12-bit binary
  radix trie over `DefId` (`NatBitTrie`) with `Except`-cached whole-table duplicate and bounds
  validation (`prepareSparseRetagIndex`, `lookupSparseRetag`), proved unconditionally equivalent
  (`lookupSparseRetag_eq_linearScan`) to the $O(M^2)$ linear reference oracle
  `linearScanRetagAttr`, preserving exact error precedence (`frameAbsent_precedes_malformedTable`),
  paired with $O(1)$ lookup certificates (`lookupSparseRetag_cert`), a `DefPath`-keyed companion
  index (`SparseDefPathRetagIndex`), and an operational `MirSemantics` overlay
  (`evalFnEntryRetagWithSparseAttr`, `unusedMalformedTable_demand_local`).
* **Part B (`BatchedVcConeNarrowCert` + `hoistTraitImpls` + `@[irreducible] coerceValueAt`,
  `bensherman` `cl/1022801564` `#cpp_vc_narrow`)**: Single batched kernel-checkable certificate
  (`checkBatchedVcConeNarrowCert`) verifying transitive call-cone closure, first-match
  `findCallee?` agreement (`calleesAgreeOn`), `TraitImplEntry` target closure + hoisting
  (`hoistTraitImpls`), and external call contract admissibility (`UntrustedAdmissible`). Proves
  `lookupCallee_eq_of_batchedCert`, `stepMirFn_withCalleesAndTraits`,
  `runMirExecBounded_narrow_of_batchedCert`, `wpMirExecSym_narrow_of_batchedCert`, and
  `vcMirWithCallees_narrow_of_batchedCert`, closing `canary_naiveNarrow_breaks_trait_dispatch`, and
  seals `coerceValueAt` (`@[irreducible]`) with targeted rewrite lemmas.
* **Part C (`DemandCallerLocationEnv`, `proofs-rs/lean-miri` PR #67 Schema 15)**: Demand-time
  `#[track_caller]` `core::panic::Location` + deduplicated filename allocation construction in
  `Memory.globals` across all 8 `-Zlocation-detail` redaction policies, with injective `AllocId`
  renaming (`AllocRenamingRel`), `demandCallerLocation_no_call_zero_allocs`,
  `demandCallerLocation_filename_dedup`, and `demandCallerLocation_bisim_eager`.
* **Part D (`LazyWriteChain` & `bvShiftSafe` / `shiftLeftBitsSafe`, `bilid` `cl/1023450318` &
  `cl/1023378691`, `leanprover/lean4` PRs #16501 & #16504)**: Lazy 1-layer overwrite-stripping
  symbolic array writes (`mkLazyWrite`, $O(N)$ vs. $O(N^2)$ `mkEagerWrite` on $N$ distinct
  addresses) and total width-clamped `BitVec` and Anneal `Scalars` shifts evaluating `shift = 2^64`
  in $O(1)$ heartbeats.
-/

namespace Anneal.SparseRetagAndVcNarrowPrototype

open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Scalars
open Anneal.MirFuelFree
open Anneal.MirLiftCore
open Anneal.Rustc.V2026_06_01.SymbolicEval

/-! ## Foundations: Constructive Equality Helpers Inside Module Namespace

We define constructive Boolean equality helpers on `Trusted` types inside
`Anneal.SparseRetagAndVcNarrowPrototype` without deriving orphan `DecidableEq` instances on
`Trusted` enumerations (which would emit global `Trusted.<Enum>.ofNat` constants and collide with
`Anneal.Rustc.V2026_06_01.TraceCheck` when co-imported alongside `Anneal`). -/

/-- Constructive `Nat.beq` reflexivity and irreflexivity helpers. -/
theorem nat_beq_self_raw (n : Nat) : Nat.beq n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

theorem nat_beq_self (n : Nat) : (n == n) = true :=
  beq_iff_eq.mpr rfl

theorem nat_beq_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hbeq : Nat.beq a b with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hbeq) h

/-- Constructive structural equality on `TraitRef`. -/
def traitRefEq (a b : TraitRef) : Bool :=
  stringEq a.defPath b.defPath && rigidTyListEq a.args b.args

/-- Constructive structural equality on `TraitImplEntry`. -/
def traitImplEntryEq (a b : TraitImplEntry) : Bool :=
  traitRefEq a.traitRef b.traitRef && stringEq a.implPath b.implPath

/-- Constructive list equality parameterized by an element comparator. -/
def listEqBy {α : Type} (eq : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | x :: xs, y :: ys => eq x y && listEqBy eq xs ys
  | _, _ => false

theorem listEqBy_refl {α : Type} {eq : α → α → Bool} ( hrefl : ∀ x, eq x x = true) :
    ∀ (xs : List α), listEqBy eq xs xs = true
  | [] => rfl
  | x :: xs => by
    unfold listEqBy
    rw [hrefl x, listEqBy_refl hrefl xs]
    rfl

theorem listEqBy_eq_of_true {α : Type} {eq : α → α → Bool}
    (heq : ∀ {x y}, eq x y = true → x = y) :
    ∀ {xs ys : List α}, listEqBy eq xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | x :: xs, y :: ys, h => by
    unfold listEqBy at h
    rw [Bool.and_eq_true] at h
    rw [heq h.1, listEqBy_eq_of_true heq h.2]

/-! ## Part A: `SparseRetagAttrIndex` (`proofs-rs/lean-miri` PR #68) -/

/-- A row in the compiler's `compiler_retag_queries` table (`lean-miri#68`), associating a
numeric `definition` index (and optional human-readable `defPath`) with its `#[rustc_no_writable]`
attribute flag. -/
structure RetagQueryRow where
  definition : Nat
  defPath : DefPath := ""
  rustcNoWritable : Bool
  deriving DecidableEq, Repr

/-- Exact error taxonomy of the protected Tree Borrows retag attribute query
(`Miri/Input/CompilerRetagOptions.lean`):
1. `.frameAbsent`: `id >= definitionCount` (checked before consulting the attribute table),
2. `.defIdOutOfBounds`: a table row references `row.definition >= definitionCount`,
3. `.duplicateDefQuery`: two table rows share the same `row.definition` (or `defPath`),
4. `.attrQueryAbsent`: the table is well-formed, `id < definitionCount`, and no row matches `id`. -/
inductive RetagAttrErr where
  | frameAbsent
  | defIdOutOfBounds
  | duplicateDefQuery
  | attrQueryAbsent
  deriving DecidableEq, Repr

/-- Constructive membership check on `List Nat` used by the linear scan oracle. -/
def natListContains (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys =>
    match Nat.beq x y with
    | true => true
    | false => natListContains x ys

/-- Left-to-right linear validation and lookup loop (`CompilerRetagOptions.rustcNoWritable`). -/
def linearScanLoop (definitionCount id : Nat) (seen : List Nat)
    (selected : Option Bool) : List RetagQueryRow → Except RetagAttrErr Bool
  | [] =>
    match selected with
    | some v => .ok v
    | none => .error .attrQueryAbsent
  | row :: rest =>
    if !(row.definition < definitionCount) then
      .error .defIdOutOfBounds
    else if natListContains row.definition seen then
      .error .duplicateDefQuery
    else
      let selected' := if row.definition == id then some row.rustcNoWritable else selected
      linearScanLoop definitionCount id (row.definition :: seen) selected' rest

/-- Reference linear oracle (`lean-miri` pre-PR #68): checks `id < definitionCount` first, then
scans the entire `rows` table validating bounds and duplicate keys on every query. -/
def linearScanRetagAttr (definitionCount : Nat) (rows : List RetagQueryRow) (id : Nat) :
    Except RetagAttrErr Bool :=
  if !(id < definitionCount) then
    .error .frameAbsent
  else
    linearScanLoop definitionCount id [] none rows

/-- Binary radix trie node with exact-key leaf buckets. For all keys `< 2^D`, each occupied leaf
contains a single `(key, val)` pair; for arbitrary `Nat` keys (`>= 2^D`), the leaf bucket preserves
exact lookup semantics without requiring bit-width bounds. -/
inductive BitTrie (α : Type) where
  | empty : BitTrie α
  | leaf : List (Nat × α) → BitTrie α
  | branch : BitTrie α → BitTrie α → BitTrie α
  deriving DecidableEq, Repr

/-- Exact key lookup in a leaf bucket. -/
def bucketLookup {α : Type} (k : Nat) : List (Nat × α) → Option α
  | [] => none
  | (k', v) :: rest => if k' == k then some v else bucketLookup k rest

/-- Walk `BitTrie` along a bit path `bs`, resolving `k` at the reached leaf bucket. -/
def trieLookupBits {α : Type} : BitTrie α → List Bool → Nat → Option α
  | .empty, _, _ => none
  | .leaf bucket, [], k => bucketLookup k bucket
  | .leaf _, _ :: _, _ => none
  | .branch _ _, [], _ => none
  | .branch l _, false :: bs, k => trieLookupBits l bs k
  | .branch _ r, true :: bs, k => trieLookupBits r bs k

/-- Insert `(k, v)` into `BitTrie` along bit path `bs`. -/
def trieInsertBits {α : Type} : BitTrie α → List Bool → Nat → α → BitTrie α
  | .empty, [], k, v => .leaf [(k, v)]
  | .leaf bucket, [], k, v => .leaf ((k, v) :: bucket)
  | .branch _ _, [], k, v => .leaf [(k, v)]
  | .empty, false :: bs, k, v => .branch (trieInsertBits .empty bs k v) .empty
  | .empty, true :: bs, k, v => .branch .empty (trieInsertBits .empty bs k v)
  | .leaf _, false :: bs, k, v => .branch (trieInsertBits .empty bs k v) .empty
  | .leaf _, true :: bs, k, v => .branch .empty (trieInsertBits .empty bs k v)
  | .branch l r, false :: bs, k, v => .branch (trieInsertBits l bs k v) r
  | .branch l r, true :: bs, k, v => .branch l (trieInsertBits r bs k v)

theorem trieLookupBits_empty {α : Type} (bs : List Bool) (id : Nat) :
    trieLookupBits (.empty : BitTrie α) bs id = none := rfl

theorem trieLookupBits_insert_same {α : Type} :
    ∀ (bs : List Bool) (t : BitTrie α) (k : Nat) (v : α) (id : Nat),
      trieLookupBits (trieInsertBits t bs k v) bs id =
        if k == id then some v else trieLookupBits t bs id
  | [], .empty, _, _, _ => rfl
  | [], .leaf _, _, _, _ => rfl
  | [], .branch _ _, _, _, _ => rfl
  | false :: bs, .empty, k, v, id => trieLookupBits_insert_same bs .empty k v id
  | true :: bs, .empty, k, v, id => trieLookupBits_insert_same bs .empty k v id
  | false :: bs, .leaf _, k, v, id => trieLookupBits_insert_same bs .empty k v id
  | true :: bs, .leaf _, k, v, id => trieLookupBits_insert_same bs .empty k v id
  | false :: bs, .branch l _, k, v, id => trieLookupBits_insert_same bs l k v id
  | true :: bs, .branch _ r, k, v, id => trieLookupBits_insert_same bs r k v id

theorem trieLookupBits_insert_diff {α : Type} :
    ∀ (bs₁ bs₂ : List Bool) (t : BitTrie α) (k : Nat) (v : α) (id : Nat),
      bs₁.length = bs₂.length → bs₁ ≠ bs₂ →
      trieLookupBits (trieInsertBits t bs₁ k v) bs₂ id = trieLookupBits t bs₂ id
  | [], [], _, _, _, _, _, hne => absurd rfl hne
  | [], _ :: _, _, _, _, _, hlen, _ => nomatch hlen
  | _ :: _, [], _, _, _, _, hlen, _ => nomatch hlen
  | b₁ :: bs₁, b₂ :: bs₂, t, k, v, id, hlen, hne => by
    have hlen' : bs₁.length = bs₂.length := Nat.succ.inj hlen
    cases b₁ <;> cases b₂
    · have hne' : bs₁ ≠ bs₂ := fun h => hne (congrArg (List.cons false) h)
      cases t with
      | empty => exact trieLookupBits_insert_diff bs₁ bs₂ .empty k v id hlen' hne'
      | leaf _ => exact trieLookupBits_insert_diff bs₁ bs₂ .empty k v id hlen' hne'
      | branch l _ => exact trieLookupBits_insert_diff bs₁ bs₂ l k v id hlen' hne'
    · cases t <;> rfl
    · cases t <;> rfl
    · have hne' : bs₁ ≠ bs₂ := fun h => hne (congrArg (List.cons true) h)
      cases t with
      | empty => exact trieLookupBits_insert_diff bs₁ bs₂ .empty k v id hlen' hne'
      | leaf _ => exact trieLookupBits_insert_diff bs₁ bs₂ .empty k v id hlen' hne'
      | branch _ r => exact trieLookupBits_insert_diff bs₁ bs₂ r k v id hlen' hne'

/-- Extract the `d` least-significant bits of `k` (LSB first). -/
def natLowBits : Nat → Nat → List Bool
  | 0, _ => []
  | d + 1, k => (k % 2 == 1) :: natLowBits d (k / 2)

theorem natLowBits_length (d k : Nat) : (natLowBits d k).length = d := by
  induction d generalizing k with
  | zero => rfl
  | succ d ih =>
    show (natLowBits d (k / 2)).length + 1 = d + 1
    rw [ih]

/-- Default binary radix depth (`12` bits = `4,096` direct leaf slots). -/
def defaultRetagTrieDepth : Nat := 12

/-- Constructive 12-bit binary radix trie over `Nat` keys (`0` `Std.HashMap` opacity). -/
structure NatBitTrie (α : Type) where
  root : BitTrie α := .empty
  deriving DecidableEq, Repr

/-- Empty `NatBitTrie`. -/
def NatBitTrie.empty {α : Type} : NatBitTrie α := ⟨.empty⟩

/-- Insert `(k, v)` into `NatBitTrie`. -/
def NatBitTrie.insert {α : Type} (t : NatBitTrie α) (k : Nat) (v : α) : NatBitTrie α :=
  ⟨trieInsertBits t.root (natLowBits defaultRetagTrieDepth k) k v⟩

/-- Look up `id` in `NatBitTrie` in $O(\log M)$ bit-branch steps. -/
def NatBitTrie.get? {α : Type} (t : NatBitTrie α) (id : Nat) : Option α :=
  trieLookupBits t.root (natLowBits defaultRetagTrieDepth id) id

theorem NatBitTrie.get?_empty {α : Type} (id : Nat) :
    (NatBitTrie.empty : NatBitTrie α).get? id = none := rfl

/-- Exact lookup-after-insert characterization for `NatBitTrie`, holding unconditionally for all
`k, id : Nat`. -/
theorem NatBitTrie.get?_insert {α : Type} (t : NatBitTrie α) (k : Nat) (v : α) (id : Nat) :
    (t.insert k v).get? id = if k == id then some v else t.get? id := by
  unfold NatBitTrie.get? NatBitTrie.insert
  dsimp only
  if hpath : natLowBits defaultRetagTrieDepth k = natLowBits defaultRetagTrieDepth id then
    rw [hpath]
    exact trieLookupBits_insert_same (natLowBits defaultRetagTrieDepth id) t.root k v id
  else
    have hlen : (natLowBits defaultRetagTrieDepth k).length =
        (natLowBits defaultRetagTrieDepth id).length := by
      rw [natLowBits_length, natLowBits_length]
    rw [trieLookupBits_insert_diff _ _ t.root k v id hlen hpath]
    have hne : (k == id) = false := by
      cases hbeq : (k == id) with
      | false => rfl
      | true =>
        have heq : k = id := beq_iff_eq.mp hbeq
        exact absurd (congrArg (natLowBits defaultRetagTrieDepth) heq) hpath
    rw [hne]
    rfl

/-- Sparse definition-ID index for protected Tree Borrows retag attributes (`lean-miri#68`). -/
structure SparseRetagAttrIndex where
  trie : NatBitTrie Bool
  rowCount : Nat
  deriving DecidableEq, Repr

/-- Sealed lookup on `SparseRetagAttrIndex` (`@[irreducible]` so `whnf` will not unfold the trie
structure unless explicitly rewritten via `SparseRetagAttrIndex.get?_eq` or
`lookupSparseRetag_cert`). -/
@[irreducible]
def SparseRetagAttrIndex.get? (idx : SparseRetagAttrIndex) (id : Nat) : Option Bool :=
  idx.trie.get? id

theorem SparseRetagAttrIndex.get?_eq (idx : SparseRetagAttrIndex) (id : Nat) :
    idx.get? id = idx.trie.get? id := by
  unfold SparseRetagAttrIndex.get?
  rfl

/-- Single-pass table preparation loop validating `row.definition < definitionCount` and duplicate
keys directly via `trie.get? row.definition` ($O(\log M)$) while populating `NatBitTrie Bool`. -/
def prepareSparseRetagLoop (definitionCount : Nat)
    (trie : NatBitTrie Bool) (count : Nat) :
    List RetagQueryRow → Except RetagAttrErr SparseRetagAttrIndex
  | [] => .ok ⟨trie, count⟩
  | row :: rest =>
    if !(row.definition < definitionCount) then
      .error .defIdOutOfBounds
    else if (trie.get? row.definition).isSome then
      .error .duplicateDefQuery
    else
      prepareSparseRetagLoop definitionCount
        (trie.insert row.definition row.rustcNoWritable) (count + 1) rest

/-- Prepare the sparse retag attribute index once per compiler table (`lean-miri#68`), caching
any validation error in `Except RetagAttrErr SparseRetagAttrIndex` so malformed unused tables
still fail only when queried. -/
def prepareSparseRetagIndex (definitionCount : Nat) (rows : List RetagQueryRow) :
    Except RetagAttrErr SparseRetagAttrIndex :=
  prepareSparseRetagLoop definitionCount .empty 0 rows

/-- Evaluate a prepared `Except RetagAttrErr SparseRetagAttrIndex` at a valid frame `id`. -/
def evalPreparedRetagLookup (prepared : Except RetagAttrErr SparseRetagAttrIndex) (id : Nat) :
    Except RetagAttrErr Bool :=
  match prepared with
  | .error e => .error e
  | .ok idx =>
    match idx.get? id with
    | some v => .ok v
    | none => .error .attrQueryAbsent

/-- Demand-time sparse retag attribute lookup (`lean-miri#68`): checks `id < definitionCount` first
(`.error .frameAbsent`), then consults the `Except`-cached `SparseRetagAttrIndex`. -/
def lookupSparseRetag (definitionCount : Nat)
    (prepared : Except RetagAttrErr SparseRetagAttrIndex) (id : Nat) :
    Except RetagAttrErr Bool :=
  if !(id < definitionCount) then
    .error .frameAbsent
  else
    evalPreparedRetagLookup prepared id

theorem prepareSparseRetagLoop_lookup_eq (definitionCount id : Nat) :
    ∀ (rows : List RetagQueryRow) (seen : List Nat) (trie : NatBitTrie Bool)
      (count : Nat),
      (∀ k, (trie.get? k).isSome = natListContains k seen) →
      evalPreparedRetagLookup (prepareSparseRetagLoop definitionCount trie count rows) id =
        linearScanLoop definitionCount id seen (trie.get? id) rows
  | [], _, trie, _, _ => by
    unfold prepareSparseRetagLoop evalPreparedRetagLookup linearScanLoop
    dsimp only
    rw [SparseRetagAttrIndex.get?_eq]
  | row :: rest, seen, trie, count, h_seen => by
    unfold prepareSparseRetagLoop linearScanLoop
    rw [h_seen row.definition]
    split
    · rfl
    · split
      · rfl
      · dsimp only
        have h_seen' :
            ∀ k, ((trie.insert row.definition row.rustcNoWritable).get? k).isSome =
              natListContains k (row.definition :: seen) := by
          intro k
          rw [NatBitTrie.get?_insert]
          unfold natListContains
          cases h_eq : row.definition == k with
          | true =>
            have h_symm : Nat.beq k row.definition = true :=
              Nat.beq_eq.mpr (beq_iff_eq.mp h_eq).symm
            rw [h_symm]
            rfl
          | false =>
            have h_symm : Nat.beq k row.definition = false := by
              cases h_rev : Nat.beq k row.definition with
              | false => rfl
              | true =>
                have heq : row.definition = k := (Nat.beq_eq.mp h_rev).symm
                rw [beq_iff_eq.mpr heq] at h_eq
                nomatch h_eq
            rw [h_symm]
            exact h_seen k
        rw [prepareSparseRetagLoop_lookup_eq definitionCount id rest (row.definition :: seen)
            (trie.insert row.definition row.rustcNoWritable) (count + 1) h_seen',
          NatBitTrie.get?_insert]

/-- **Unconditional Exact Equivalence (`lookupSparseRetag_eq_linearScan`)**: for all
`definitionCount`, all `rows` (valid, empty, out-of-bounds, duplicate, or missing), and all `id`,
`lookupSparseRetag` over `prepareSparseRetagIndex` returns the exact same `Except RetagAttrErr Bool`
as `linearScanRetagAttr`. -/
theorem lookupSparseRetag_eq_linearScan (definitionCount : Nat)
    (rows : List RetagQueryRow) (id : Nat) :
    lookupSparseRetag definitionCount (prepareSparseRetagIndex definitionCount rows) id =
      linearScanRetagAttr definitionCount rows id := by
  unfold lookupSparseRetag prepareSparseRetagIndex linearScanRetagAttr
  split
  · rfl
  · exact prepareSparseRetagLoop_lookup_eq definitionCount id rows [] .empty 0 (fun _ => rfl)

/-- **Error Precedence (`frameAbsent_precedes_malformedTable`)**: an out-of-bounds frame ID
(`id >= definitionCount`) always fails with `.error .frameAbsent`, even when the prepared attribute
table is malformed (`.error e`). -/
theorem frameAbsent_precedes_malformedTable {definitionCount id : Nat}
    (h : definitionCount ≤ id) (e : RetagAttrErr) :
    lookupSparseRetag definitionCount (.error e) id = .error .frameAbsent := by
  unfold lookupSparseRetag
  have hnot : (!(id < definitionCount)) = true := by
    simp [Nat.not_lt.mpr h]
  rw [hnot]
  rfl

/-- **$O(1)$ Lookup Certificate (`lookupSparseRetag_cert`)**: once `prepareSparseRetagIndex` has
been evaluated to `.ok idx`, any in-bounds `id < definitionCount` with `idx.trie.get? id = some b`
rewrites directly to `.ok b` without scanning `rows`. -/
theorem lookupSparseRetag_cert {definitionCount id : Nat} {idx : SparseRetagAttrIndex} {b : Bool}
    (h_bound : id < definitionCount) (h_hit : idx.trie.get? id = some b) :
    lookupSparseRetag definitionCount (.ok idx) id = .ok b := by
  unfold lookupSparseRetag evalPreparedRetagLookup
  simp [h_bound, SparseRetagAttrIndex.get?_eq, h_hit]

/-- $O(1)$ miss certificate on a prepared `SparseRetagAttrIndex`. -/
theorem lookupSparseRetag_miss_cert {definitionCount id : Nat} {idx : SparseRetagAttrIndex}
    (h_bound : id < definitionCount) (h_miss : idx.trie.get? id = none) :
    lookupSparseRetag definitionCount (.ok idx) id = .error .attrQueryAbsent := by
  unfold lookupSparseRetag evalPreparedRetagLookup
  simp [h_bound, SparseRetagAttrIndex.get?_eq, h_miss]

/-! ### Companion `DefPath`-Keyed Sparse Retag Attribute Index (`SparseDefPathRetagIndex`) -/

/-- Deterministic 12-bit rolling hash of a `DefPath` for routing into a `BitTrie` bucket. -/
def defPathHash12 (s : DefPath) : Nat :=
  (s.toUTF8.toList.foldl (fun acc b => (acc * 33 + b.toNat) % 4096) 5381) % 4096

/-- Exact `DefPath` lookup in a leaf bucket `List (DefPath × Bool)`. -/
def defPathBucketLookup (dp : DefPath) : List (DefPath × Bool) → Option Bool
  | [] => none
  | kv :: rest =>
    match stringEq kv.1 dp with
    | true => some kv.2
    | false => defPathBucketLookup dp rest

/-- Companion `DefPath`-keyed sparse retag index. -/
structure SparseDefPathRetagIndex where
  buckets : NatBitTrie (List (DefPath × Bool)) := .empty
  deriving DecidableEq, Repr

/-- Insert `(dp, val)` into `SparseDefPathRetagIndex`. -/
def SparseDefPathRetagIndex.insert (idx : SparseDefPathRetagIndex) (dp : DefPath) (val : Bool) :
    SparseDefPathRetagIndex :=
  let h := defPathHash12 dp
  let cur := (idx.buckets.get? h).getD []
  ⟨idx.buckets.insert h ((dp, val) :: cur)⟩

/-- Look up `dp` in `SparseDefPathRetagIndex`. -/
def SparseDefPathRetagIndex.get? (idx : SparseDefPathRetagIndex) (dp : DefPath) : Option Bool :=
  match idx.buckets.get? (defPathHash12 dp) with
  | some bucket => defPathBucketLookup dp bucket
  | none => none

theorem SparseDefPathRetagIndex.get?_empty (dp : DefPath) :
    (SparseDefPathRetagIndex.mk .empty).get? dp = none := rfl

theorem SparseDefPathRetagIndex.get?_insert (idx : SparseDefPathRetagIndex)
    (k : DefPath) (v : Bool) (dp : DefPath) :
    (idx.insert k v).get? dp = if stringEq k dp then some v else idx.get? dp := by
  dsimp only [SparseDefPathRetagIndex.get?, SparseDefPathRetagIndex.insert]
  rw [NatBitTrie.get?_insert]
  cases hh : defPathHash12 k == defPathHash12 dp with
  | true =>
    have h_eq : defPathHash12 k = defPathHash12 dp := beq_iff_eq.mp hh
    simp only [↓reduceIte, defPathBucketLookup]
    cases stringEq k dp with
    | true => rfl
    | false =>
      rw [h_eq]
      cases idx.buckets.get? (defPathHash12 dp) <;> rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have h_str : stringEq k dp = false := by
      cases hs : stringEq k dp with
      | false => rfl
      | true =>
        have hk : k = dp := coneStringEq_iff.mp hs
        have hself : (defPathHash12 dp == defPathHash12 dp) = true :=
          nat_beq_self (defPathHash12 dp)
        rw [hk, hself] at hh
        nomatch hh
    rw [h_str]
    rfl

/-! ### Operational `MirSemantics` Overlay (`evalFnEntryRetagWithSparseAttr`) -/

/-- Select the initial protected Tree Borrows permission for `StatementKind.retag .fnEntry` given
`implicitWrites` and the queried `rustcNoWritable` attribute (`Miri/TreeBorrows/RetagPolicy.lean`
lines 56–59 & 73–74):
- Shared references (`.not`): `.frozen` if `pointee` is `Freeze`, else `.cell`.
- Mutable references (`.mut`): when `implicitWrites && !rustcNoWritable`, an initial implicit write
  activates the tag to `.unique`; when `rustcNoWritable = true` (`#[rustc_no_writable]`, e.g. `Box`)
  or `implicitWrites = false`, the tag starts as `.reservedFrz false` (matching
  `Trusted.Rustc.V2026_06_01.MirSemantics.fnEntryRetagPerm`). -/
def fnEntryRetagPermWithAttr (mutability : Mutability) (pointee : RigidTy)
    (implicitWrites rustcNoWritable : Bool) : TreeBorrowPerm :=
  match mutability with
  | .not => fnEntryRetagPerm .not pointee
  | .mut =>
    match implicitWrites && !rustcNoWritable with
    | true => .unique
    | false => fnEntryRetagPerm .mut pointee

theorem fnEntryRetagPermWithAttr_noWritable (mutability : Mutability) (pointee : RigidTy)
    (implicitWrites : Bool) :
    fnEntryRetagPermWithAttr mutability pointee implicitWrites true =
      fnEntryRetagPerm mutability pointee := by
  cases mutability <;> simp [fnEntryRetagPermWithAttr, fnEntryRetagPerm]

theorem fnEntryRetagPermWithAttr_implicitWrites_false (mutability : Mutability) (pointee : RigidTy)
    (rustcNoWritable : Bool) :
    fnEntryRetagPermWithAttr mutability pointee false rustcNoWritable =
      fnEntryRetagPerm mutability pointee := by
  cases mutability <;> simp [fnEntryRetagPermWithAttr, fnEntryRetagPerm]

/-- Post-upgrade the head borrow entry's permission after `evalStmt` on `.retag .fnEntry` when
`implicitWrites && !rustcNoWritable` activates a mutable reference retag to `.unique`. -/
def applyImplicitWriteUpgrade (node : MirStepNode) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (place : Place) (implicitWrites rustcNoWritable : Bool) :
    MirStepNode :=
  match implicitWrites && !rustcNoWritable with
  | false => node
  | true =>
    match placeTy localDecls layouts place with
    | some { kind := .ref .mut _, .. } =>
      match node with
      | .tau (.running s') =>
        match s'.memory.borrows with
        | head :: tail =>
          MirStepNode.step
            { s' with memory := { s'.memory with borrows := { head with perm := .unique } :: tail } }
        | [] => node
      | _ => node
    | _ => node

/-- Operational `Statement` evaluator parameterized by an attribute-query oracle
`queryAttr : Nat → Except RetagAttrErr Bool`, mirroring `Miri/Interpreter/TypedRetag.lean` lines
50–54 (`if mode == .FnEntry then implicitWrites ← h.implicitWrites; if implicitWrites then
noWritable ← h.rustcNoWritable defId`):
- Non-`.fnEntry` retags, non-retag statements, and `implicitWrites = false` step directly via
  `Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt` without querying `queryAttr`.
- `.retag .fnEntry` with `implicitWrites = true` queries `queryAttr frameDefId`, faulting to
  `MirStepNode.unsupported` on `.error _` (matching `CompilerRetagOptions.lean:41`) and applying
  `applyImplicitWriteUpgrade` on `.ok noWritable`. -/
def evalStmtWithRetagAttrOracle (queryAttr : Nat → Except RetagAttrErr Bool)
    (implicitWrites : Bool) (frameDefId : Nat) (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable) : MirStepNode :=
  match stmt.kind, implicitWrites with
  | .retag .fnEntry place, true =>
    match queryAttr frameDefId with
    | .error _ => MirStepNode.unsupported
    | .ok noWritable =>
      applyImplicitWriteUpgrade (evalStmt s stmt localDecls layouts)
        localDecls layouts place true noWritable
  | _, _ => evalStmt s stmt localDecls layouts

/-- Operational `Statement` evaluator backed by `SparseRetagAttrIndex`. -/
def evalFnEntryRetagWithSparseAttr (definitionCount : Nat)
    (prepared : Except RetagAttrErr SparseRetagAttrIndex) (implicitWrites : Bool)
    (frameDefId : Nat) (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable) : MirStepNode :=
  evalStmtWithRetagAttrOracle (lookupSparseRetag definitionCount prepared)
    implicitWrites frameDefId s stmt localDecls layouts

/-- Reference `Statement` evaluator backed by `linearScanRetagAttr`. -/
def evalFnEntryRetagWithLinearScan (definitionCount : Nat) (rows : List RetagQueryRow)
    (implicitWrites : Bool) (frameDefId : Nat) (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable) : MirStepNode :=
  evalStmtWithRetagAttrOracle (linearScanRetagAttr definitionCount rows)
    implicitWrites frameDefId s stmt localDecls layouts

/-- **Operational Equivalence (`evalFnEntryRetagWithSparseAttr_eq_linear`)**: stepping any MIR
statement with the prepared `SparseRetagAttrIndex` is identical to stepping with the linear scan
oracle for all `definitionCount`, `rows`, `implicitWrites`, `frameDefId`, `s`, and `stmt`. -/
theorem evalFnEntryRetagWithSparseAttr_eq_linear (definitionCount : Nat)
    (rows : List RetagQueryRow) (implicitWrites : Bool) (frameDefId : Nat)
    (s : MachineState) (stmt : Statement) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalFnEntryRetagWithSparseAttr definitionCount (prepareSparseRetagIndex definitionCount rows)
        implicitWrites frameDefId s stmt localDecls layouts =
      evalFnEntryRetagWithLinearScan definitionCount rows
        implicitWrites frameDefId s stmt localDecls layouts := by
  unfold evalFnEntryRetagWithSparseAttr evalFnEntryRetagWithLinearScan evalStmtWithRetagAttrOracle
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | retag rk p =>
    cases rk <;> cases implicitWrites <;> try rfl
    dsimp only
    rw [lookupSparseRetag_eq_linearScan]
  | _ => cases implicitWrites <;> rfl

/-- Predicate identifying statements that are not `StatementKind.retag .fnEntry`. -/
def isNonFnEntryRetagStmt (stmt : Statement) : Bool :=
  match stmt.kind with
  | .retag .fnEntry _ => false
  | _ => true

/-- **Demand-Locality of Malformed Tables (`unusedMalformedTable_demand_local`)**: even when the
prepared retag attribute table is malformed (`prepared = .error e`), any non-`.fnEntry` statement
(including `.retag .default`, `.retag .twoPhase`, `.retag .raw`, `.assign`, `.storageLive`, etc.)
steps identically to `Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt`. -/
theorem unusedMalformedTable_demand_local (definitionCount : Nat) (e : RetagAttrErr)
    (implicitWrites : Bool) (frameDefId : Nat) (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_non : isNonFnEntryRetagStmt stmt = true) :
    evalFnEntryRetagWithSparseAttr definitionCount (.error e) implicitWrites frameDefId
        s stmt localDecls layouts =
      evalStmt s stmt localDecls layouts := by
  unfold isNonFnEntryRetagStmt at h_non
  unfold evalFnEntryRetagWithSparseAttr evalStmtWithRetagAttrOracle
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | retag rk p =>
    cases rk with
    | fnEntry => nomatch h_non
    | _ => cases implicitWrites <;> rfl
  | _ => cases implicitWrites <;> rfl

/-- When `implicitWrites = false` (default Miri / Anneal profile), `evalFnEntryRetagWithSparseAttr`
equals `evalStmt` for *every* statement (including `.retag .fnEntry`), even when `prepared = .error e`. -/
theorem evalFnEntryRetagWithSparseAttr_implicitWrites_false (definitionCount : Nat)
    (prepared : Except RetagAttrErr SparseRetagAttrIndex) (frameDefId : Nat)
    (s : MachineState) (stmt : Statement) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalFnEntryRetagWithSparseAttr definitionCount prepared false frameDefId
        s stmt localDecls layouts =
      evalStmt s stmt localDecls layouts := by
  unfold evalFnEntryRetagWithSparseAttr evalStmtWithRetagAttrOracle
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | retag rk _ => cases rk <;> rfl
  | _ => rfl

/-- When `lookupSparseRetag` resolves `rustcNoWritable = true` (`#[rustc_no_writable]`),
`evalFnEntryRetagWithSparseAttr` equals the trusted `evalStmt` (preserving `.reservedFrz false` on
mutable references). -/
theorem evalFnEntryRetagWithSparseAttr_rustcNoWritable_true (definitionCount : Nat)
    (prepared : Except RetagAttrErr SparseRetagAttrIndex) (implicitWrites : Bool)
    (frameDefId : Nat) (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_attr : lookupSparseRetag definitionCount prepared frameDefId = .ok true) :
    evalFnEntryRetagWithSparseAttr definitionCount prepared implicitWrites frameDefId
        s stmt localDecls layouts =
      evalStmt s stmt localDecls layouts := by
  unfold evalFnEntryRetagWithSparseAttr evalStmtWithRetagAttrOracle
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | retag rk p =>
    cases rk <;> cases implicitWrites <;> try rfl
    dsimp only
    rw [h_attr]
    rfl
  | _ => cases implicitWrites <;> rfl

/-! ## Part B: `BatchedVcConeNarrowCert`, `hoistTraitImpls`, & `@[irreducible] coerceValueAt` (`bensherman` `cl/1022801564`) -/

/-- Hoist all `TraitImplEntry` records from `callees` into the explicit `Memory.traitImpls` list
(`extra ++ flatMapTraitImpls callees`) so narrowing `callees` to the executed call cone never loses
`TraitImplEntry` dispatch records attached to uncalled `impl` block bodies (`canary_naiveNarrow_breaks_trait_dispatch`). -/
def hoistTraitImpls (callees : List CapturedMir) (extra : List TraitImplEntry) :
    List TraitImplEntry :=
  extra ++ flatMapTraitImpls callees

/-- Strip per-body `traitImpls` after hoisting them into `Memory.traitImpls` via `hoistTraitImpls`,
avoiding duplicate `TraitImplEntry` scans across `flatMapTraitImpls narrowCallees`. -/
def stripCalleeTraitImpls (callees : List CapturedMir) : List CapturedMir :=
  callees.map (fun c => { c with traitImpls := [] })

theorem flatMapTraitImpls_stripCalleeTraitImpls :
    ∀ (cs : List CapturedMir), flatMapTraitImpls (stripCalleeTraitImpls cs) = []
  | [] => rfl
  | _ :: rest => flatMapTraitImpls_stripCalleeTraitImpls rest

theorem hoistTraitImpls_append_strip (callees : List CapturedMir) (extra : List TraitImplEntry)
    (narrow : List CapturedMir) :
    hoistTraitImpls callees extra ++ flatMapTraitImpls (stripCalleeTraitImpls narrow) =
      extra ++ flatMapTraitImpls callees := by
  rw [flatMapTraitImpls_stripCalleeTraitImpls, List.append_nil, hoistTraitImpls]

/-- Update both `Memory.callees` and `Memory.traitImpls` simultaneously (`Memory.withCalleesAndTraits`). -/
@[reducible]
def Memory.withCalleesAndTraits (c : CalleeEnv) (ti : List TraitImplEntry) (m : Memory) : Memory :=
  { m with callees := c, traitImpls := ti }

theorem Memory.withCalleesAndTraits_eq_withCalleeCtx (c : CalleeEnv) (ti : List TraitImplEntry)
    (m : Memory) :
    Memory.withCalleesAndTraits c ti m = Memory.withCalleeCtx c m.activeCallee ti m := rfl

theorem MachineState.withCalleesAndTraits_eq_withCalleeCtx (c : CalleeEnv)
    (ti : List TraitImplEntry) (s : MachineState) :
    MachineState.mapMem (Memory.withCalleesAndTraits c ti) s =
      MachineState.mapMem (Memory.withCalleeCtx c s.memory.activeCallee ti) s := rfl

theorem Memory.withCalleesAndTraits_comp_withCalleeCtx (c₁ c₂ : CalleeEnv)
    (ac : Option CapturedMir) (ti₁ ti₂ : List TraitImplEntry) :
    Memory.withCalleesAndTraits c₂ ti₂ ∘ Memory.withCalleeCtx c₁ ac ti₁ =
      Memory.withCalleeCtx c₂ ac ti₂ ∘ Memory.withCalleeCtx c₁ ac ti₁ := rfl

/-- `evalStmt` commutes with `Memory.withCalleesAndTraits c₂ ti₂` on `Statement.calleeQueryFree`
statements (derived directly from `Anneal.MirLiftCore.evalStmt_withCalleeCtx`). -/
theorem evalStmt_withCalleesAndTraits (c₂ : CalleeEnv) (ti₂ : List TraitImplEntry)
    (s : MachineState) (stmt : Statement) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_free : Statement.calleeQueryFree stmt = true) :
    evalStmt (MachineState.mapMem (Memory.withCalleesAndTraits c₂ ti₂) s) stmt localDecls layouts =
      MirStepNode.mapMem (Memory.withCalleesAndTraits c₂ ti₂) (evalStmt s stmt localDecls layouts) := by
  rw [MachineState.withCalleesAndTraits_eq_withCalleeCtx,
    evalStmt_withCalleeCtx _ _ _ s stmt localDecls layouts h_free,
    evalStmt_calleeCtx_preserved s stmt localDecls layouts h_free,
    MirStepNode.mapMem_comp, MirStepNode.mapMem_comp,
    Memory.withCalleesAndTraits_comp_withCalleeCtx]

theorem unwindFromCallStack_withCalleesAndTraits (c₂ : CalleeEnv) (ti₂ : List TraitImplEntry) :
    ∀ (stk : List SavedCallerFrame) (m : Memory),
      unwindFromCallStack stk (Memory.withCalleesAndTraits c₂ ti₂ m) =
        MirExecState.mapMem (Memory.withCalleesAndTraits c₂ ti₂) (unwindFromCallStack stk m)
  | [], _ => rfl
  | caller :: rest, m => by
    unfold unwindFromCallStack
    dsimp only
    cases caller.returnUnwind with
    | unreachable => rfl
    | terminate => rfl
    | continue_ =>
      exact unwindFromCallStack_withCalleesAndTraits c₂ ti₂ rest
        { m with
          callStack := rest
          activeCallee := some caller.callerBody
          activeProtectors := restoreCallerProtectors caller }
    | cleanup _ => rfl

theorem applyUnwindAction_withCalleesAndTraits (c₂ : CalleeEnv) (ti₂ : List TraitImplEntry)
    (s : MachineState) (l : List LocalSlot) (m : Memory) (u : UnwindAction) :
    applyUnwindAction (MachineState.mapMem (Memory.withCalleesAndTraits c₂ ti₂) s) l
        (Memory.withCalleesAndTraits c₂ ti₂ m) u =
      MirExecState.mapMem (Memory.withCalleesAndTraits c₂ ti₂) (applyUnwindAction s l m u) := by
  cases u with
  | unreachable => rfl
  | terminate => rfl
  | continue_ => exact unwindFromCallStack_withCalleesAndTraits c₂ ti₂ m.callStack m
  | cleanup _ => rfl

private theorem nodeCT_fail {f : Memory → Memory} {fk : FailureKind} :
    MirStepNode.fail fk = MirStepNode.mapMem f (MirStepNode.fail fk) := rfl

private theorem nodeCT_unwind (c₂ : CalleeEnv) (ti₂ : List TraitImplEntry) (s : MachineState)
    (l : List LocalSlot) (u : UnwindAction) :
    (match applyUnwindAction (MachineState.mapMem (Memory.withCalleesAndTraits c₂ ti₂) s) l
        (Memory.withCalleesAndTraits c₂ ti₂ s.memory) u with
      | .running nextState => MirStepNode.step nextState
      | .halted out => MirStepNode.retOutcome out
      | .faulted fk => MirStepNode.fail fk) =
      MirStepNode.mapMem (Memory.withCalleesAndTraits c₂ ti₂)
        (match applyUnwindAction s l s.memory u with
          | .running nextState => MirStepNode.step nextState
          | .halted out => MirStepNode.retOutcome out
          | .faulted fk => MirStepNode.fail fk) := by
  rw [applyUnwindAction_withCalleesAndTraits]
  cases applyUnwindAction s l s.memory u <;> rfl

theorem commitForeignFrameLocals_withCalleesAndTraits (c₂ : CalleeEnv) (ti₂ : List TraitImplEntry)
    (m : Memory) (t : ForeignFrameTarget) (l : List LocalSlot) :
    commitForeignFrameLocals (Memory.withCalleesAndTraits c₂ ti₂ m) t l =
      (commitForeignFrameLocals m t l).map (Memory.withCalleesAndTraits c₂ ti₂) := by
  cases t with
  | callerReferent _ => rfl
  | savedFrame idx _ =>
    unfold commitForeignFrameLocals
    dsimp only [Memory.withCalleesAndTraits]
    cases get? m.callStack idx with
    | none => rfl
    | some sf =>
      dsimp only
      cases set? m.callStack idx { sf with frame := { sf.frame with locals := l } } <;> rfl

theorem foreignFrameDerefWrite_withCalleesAndTraits (c₂ : CalleeEnv) (ti₂ : List TraitImplEntry)
    (locals₁ : List LocalSlot) (mem₁ : Memory) (dst : Place) (restProj : List ProjectionElem)
    (val : Value) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    foreignFrameDerefWrite locals₁ (Memory.withCalleesAndTraits c₂ ti₂ mem₁) dst restProj val
        localDecls layouts =
      FrameWriteResult.mapMem (Memory.withCalleesAndTraits c₂ ti₂)
        (foreignFrameDerefWrite locals₁ mem₁ dst restProj val localDecls layouts) := by
  unfold foreignFrameDerefWrite
  dsimp only [Memory.withCalleesAndTraits]
  repeat' (first | rfl | split)
  all_goals (
    simp only [commitForeignFrameLocals_withCalleesAndTraits] at *
    simp only [*, Option.map] at *
    first
    | (simp at *; done)
    | (simp only [Option.some.injEq] at *; subst_vars; rfl))

theorem writeReturnDestination_withCalleesAndTraits (c₂ : CalleeEnv) (ti₂ : List TraitImplEntry)
    (callerLocals : List LocalSlot) (mem : Memory) (dst : Place) (retVal : Value)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    writeReturnDestination callerLocals (Memory.withCalleesAndTraits c₂ ti₂ mem) dst retVal
        localDecls layouts =
      FrameWriteResult.mapMem (Memory.withCalleesAndTraits c₂ ti₂)
        (writeReturnDestination callerLocals mem dst retVal localDecls layouts) := by
  unfold writeReturnDestination
  dsimp only [Memory.withCalleesAndTraits]
  repeat' (first | rfl | split)
  all_goals (
    try simp only [foreignFrameDerefWrite_withCalleesAndTraits] at *
    try simp only [*, FrameWriteResult.mapMem] at *
    try (simp at *; done)
    try (simp only [FrameWriteResult.ok.injEq] at *
         obtain ⟨h₁, h₂⟩ := ‹_ ∧ _›
         subst_vars
         rfl))

theorem evalTerminator_return_withCalleesAndTraits (c₂ : CalleeEnv) (ti₂ : List TraitImplEntry)
    (s : MachineState) (span : String) (cb : Option CapturedMir) :
    evalTerminator (MachineState.mapMem (Memory.withCalleesAndTraits c₂ ti₂) s) ⟨.return_, span⟩ cb =
      MirStepNode.mapMem (Memory.withCalleesAndTraits c₂ ti₂)
        (evalTerminator s ⟨.return_, span⟩ cb) := by
  rw [ccEvalReturn_eq, ccEvalReturn_eq]
  unfold ccEvalReturn
  have h_wr : ∀ (caller : SavedCallerFrame) (restStack : List SavedCallerFrame)
      (callerLocals : List LocalSlot) (dst : Place) (retVal : Value)
      (localDecls : List LocalDecl) (layouts : LayoutTable),
      writeReturnDestination callerLocals
          (ccReturnCallerMem (MachineState.mapMem (Memory.withCalleesAndTraits c₂ ti₂) s) caller restStack)
          dst retVal localDecls layouts =
        FrameWriteResult.mapMem (Memory.withCalleesAndTraits c₂ ti₂)
          (writeReturnDestination callerLocals (ccReturnCallerMem s caller restStack)
            dst retVal localDecls layouts) :=
    fun caller restStack callerLocals dst retVal localDecls layouts =>
      writeReturnDestination_withCalleesAndTraits c₂ ti₂ callerLocals
        (ccReturnCallerMem s caller restStack) dst retVal localDecls layouts
  simp only [h_wr]
  dsimp only [MachineState.mapMem, Memory.withCalleesAndTraits]
  repeat' (first | exact nodeCT_fail | rfl | split)
  all_goals (
    try simp only [*, FrameWriteResult.mapMem] at *
    try (simp at *; done)
    try (simp only [FrameWriteResult.ok.injEq] at *
         obtain ⟨h₁, h₂⟩ := ‹_ ∧ _›
         subst_vars
         rfl))

theorem writeIntrinsicReturn_withCalleesAndTraits (c₂ : CalleeEnv) (ti₂ : List TraitImplEntry)
    (s : MachineState) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (retVal : Value) :
    writeIntrinsicReturn (MachineState.mapMem (Memory.withCalleesAndTraits c₂ ti₂) s)
        locals' destination targetBb retVal =
      MirStepNode.mapMem (Memory.withCalleesAndTraits c₂ ti₂)
        (writeIntrinsicReturn s locals' destination targetBb retVal) := by
  rw [MachineState.withCalleesAndTraits_eq_withCalleeCtx,
    writeIntrinsicReturn_withCalleeCtx _ _ _ s locals' destination targetBb retVal,
    writeIntrinsicReturn_calleeCtx_preserved s locals' destination targetBb retVal,
    MirStepNode.mapMem_comp, MirStepNode.mapMem_comp,
    Memory.withCalleesAndTraits_comp_withCalleeCtx]

theorem evalNonSelectIntrinsicCall_withCalleesAndTraits (c₂ : CalleeEnv) (ti₂ : List TraitImplEntry)
    (kind : RustIntrinsicKind) (s : MachineState) (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable) (argOps : List Operand)
    (argVals : List Value) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) :
    evalNonSelectIntrinsicCall kind (MachineState.mapMem (Memory.withCalleesAndTraits c₂ ti₂) s)
        target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetBb =
      MirStepNode.mapMem (Memory.withCalleesAndTraits c₂ ti₂)
        (evalNonSelectIntrinsicCall kind s target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb) := by
  rw [MachineState.withCalleesAndTraits_eq_withCalleeCtx,
    evalNonSelectIntrinsicCall_withCalleeCtx _ _ _ kind s target bodyLocalDecls bodyLayouts
      argOps argVals locals' destination targetBb,
    evalNonSelectIntrinsicCall_calleeCtx_preserved kind s target bodyLocalDecls bodyLayouts
      argOps argVals locals' destination targetBb,
    MirStepNode.mapMem_comp, MirStepNode.mapMem_comp,
    Memory.withCalleesAndTraits_comp_withCalleeCtx]

theorem evalDirectRustIntrinsic?_withCalleesAndTraits_of_nonSelect
    (c₂ : CalleeEnv) (ti₂ : List TraitImplEntry) (s : MachineState)
    (currentBody : Option CapturedMir) (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (unwind : UnwindAction)
    (h_non : isNonSelectIntrinsicOpt (classifyRustIntrinsic? target.defPath) = true) :
    evalDirectRustIntrinsic? (MachineState.mapMem (Memory.withCalleesAndTraits c₂ ti₂) s)
        currentBody target bodyLocalDecls bodyLayouts argOps argVals locals'
        destination targetBb unwind =
      (evalDirectRustIntrinsic? s currentBody target bodyLocalDecls bodyLayouts argOps argVals
        locals' destination targetBb unwind).map
        (MirStepNode.mapMem (Memory.withCalleesAndTraits c₂ ti₂)) := by
  unfold evalDirectRustIntrinsic?
  cases hk : classifyRustIntrinsic? target.defPath with
  | none => rfl
  | some kind =>
    rw [hk] at h_non
    cases kind with
    | constEvalSelect => nomatch h_non
    | _ =>
      dsimp only [Option.map]
      exact congrArg Option.some
        (evalNonSelectIntrinsicCall_withCalleesAndTraits c₂ ti₂ _ s target bodyLocalDecls
          bodyLayouts argOps argVals locals' destination targetBb)

/-! ### Trait-Aware `lookupCallee` Congruence & Cone Preservation -/

theorem collectMatchingTraitImpls_filter_defPath (c : List CapturedMir) (dp : DefPath)
    (typeArgs : List RigidTy) :
    ∀ (ti : List TraitImplEntry) (acc : List (TraitImplEntry × Option (List RigidTy))),
      collectMatchingTraitImpls c ti dp typeArgs acc =
        collectMatchingTraitImpls c (ti.filter (fun e => stringEq e.traitRef.defPath dp)) dp typeArgs acc
  | [], _ => rfl
  | e :: rest, acc => by
    cases hs : stringEq e.traitRef.defPath dp with
    | false =>
      have h1 : collectMatchingTraitImpls c (e :: rest) dp typeArgs acc =
          collectMatchingTraitImpls c rest dp typeArgs acc := by
        conv => lhs; unfold collectMatchingTraitImpls
        rw [hs]
        rfl
      have h2 : (e :: rest).filter (fun e => stringEq e.traitRef.defPath dp) =
          rest.filter (fun e => stringEq e.traitRef.defPath dp) := by
        simp [hs]
      rw [h1, h2]
      exact collectMatchingTraitImpls_filter_defPath c dp typeArgs rest acc
    | true =>
      have h2 : (e :: rest).filter (fun e => stringEq e.traitRef.defPath dp) =
          e :: rest.filter (fun e => stringEq e.traitRef.defPath dp) := by
        simp [hs]
      rw [h2]
      conv => lhs; unfold collectMatchingTraitImpls
      conv => rhs; unfold collectMatchingTraitImpls
      rw [hs]
      dsimp only [↓reduceIte]
      cases e.traitRef.args with
      | nil => exact collectMatchingTraitImpls_filter_defPath c dp typeArgs rest acc
      | cons a as =>
        cases matchRigidTyPrefix (a :: as) typeArgs [] with
        | none => exact collectMatchingTraitImpls_filter_defPath c dp typeArgs rest acc
        | some _ => exact collectMatchingTraitImpls_filter_defPath c dp typeArgs rest _

theorem hasTraitImplForDefPath_eq_of_filter_eq {ti₁ ti₂ : List TraitImplEntry} {dp : DefPath}
    (h : ti₁.filter (fun e => stringEq e.traitRef.defPath dp) =
         ti₂.filter (fun e => stringEq e.traitRef.defPath dp)) :
    hasTraitImplForDefPath ti₁ dp = hasTraitImplForDefPath ti₂ dp := by
  have haux : ∀ (ti : List TraitImplEntry),
      hasTraitImplForDefPath ti dp = !(ti.filter (fun e => stringEq e.traitRef.defPath dp)).isEmpty := by
    intro ti
    induction ti with
    | nil => rfl
    | cons e rest ih =>
      unfold hasTraitImplForDefPath
      cases hs : stringEq e.traitRef.defPath dp with
      | true => simp [hs]
      | false => simp [hs, ih]
  rw [haux ti₁, haux ti₂, h]

theorem collectMatchingTraitImpls_congr_callees {c₁ c₂ : List CapturedMir} {dp : DefPath}
    (typeArgs : List RigidTy) :
    ∀ (ti : List TraitImplEntry) (acc : List (TraitImplEntry × Option (List RigidTy))),
      (∀ e ∈ ti, stringEq e.traitRef.defPath dp = true →
        findCallee? c₁ e.implPath = findCallee? c₂ e.implPath) →
      collectMatchingTraitImpls c₁ ti dp typeArgs acc =
        collectMatchingTraitImpls c₂ ti dp typeArgs acc
  | [], _, _ => rfl
  | e :: rest, acc, h => by
    unfold collectMatchingTraitImpls
    cases hs : stringEq e.traitRef.defPath dp with
    | false =>
      dsimp only [Bool.false_eq_true, ↓reduceIte]
      exact collectMatchingTraitImpls_congr_callees typeArgs rest acc
        (fun e' hm hs' => h e' (List.Mem.tail _ hm) hs')
    | true =>
      dsimp only [↓reduceIte]
      have he : findCallee? c₁ e.implPath = findCallee? c₂ e.implPath :=
        h e (List.Mem.head _) hs
      cases e.traitRef.args with
      | nil =>
        exact collectMatchingTraitImpls_congr_callees typeArgs rest acc
          (fun e' hm hs' => h e' (List.Mem.tail _ hm) hs')
      | cons a as =>
        cases matchRigidTyPrefix (a :: as) typeArgs [] with
        | none =>
          exact collectMatchingTraitImpls_congr_callees typeArgs rest acc
            (fun e' hm hs' => h e' (List.Mem.tail _ hm) hs')
        | some _ =>
          dsimp only
          rw [he]
          exact collectMatchingTraitImpls_congr_callees typeArgs rest _
            (fun e' hm hs' => h e' (List.Mem.tail _ hm) hs')

theorem upsertMatchingTraitImpl_mem_fst {e w : TraitImplEntry} {opt : Option (List RigidTy)} :
    ∀ (acc : List (TraitImplEntry × Option (List RigidTy))),
      w ∈ (upsertMatchingTraitImpl e opt acc).map Prod.fst →
      w = e ∨ w ∈ acc.map Prod.fst
  | [], h => Or.inl (List.mem_singleton.mp h)
  | (e₀, opt₀) :: rest, h => by
    unfold upsertMatchingTraitImpl at h
    cases hs : stringEq e₀.implPath e.implPath with
    | true =>
      rw [hs] at h
      cases opt₀ <;> cases opt
      all_goals (
        dsimp only [List.map] at h
        rcases List.mem_cons.mp h with rfl | hrest
        · first | exact Or.inl rfl | exact Or.inr (List.Mem.head _)
        · exact Or.inr (List.Mem.tail _ hrest))
    | false =>
      rw [hs] at h
      dsimp only [List.map] at h
      rcases List.mem_cons.mp h with rfl | hrest
      · exact Or.inr (List.Mem.head _)
      · rcases upsertMatchingTraitImpl_mem_fst rest hrest with rfl | hacc
        · exact Or.inl rfl
        · exact Or.inr (List.Mem.tail _ hacc)

theorem collectMatchingTraitImpls_mem_fst (c : List CapturedMir) (dp : DefPath)
    (typeArgs : List RigidTy) :
    ∀ (ti : List TraitImplEntry) (acc : List (TraitImplEntry × Option (List RigidTy)))
      {w : TraitImplEntry},
      w ∈ (collectMatchingTraitImpls c ti dp typeArgs acc).map Prod.fst →
      w ∈ acc.map Prod.fst ∨ (w ∈ ti ∧ stringEq w.traitRef.defPath dp = true)
  | [], acc, _, h => Or.inl h
  | e :: rest, acc, w, h => by
    unfold collectMatchingTraitImpls at h
    cases hs : stringEq e.traitRef.defPath dp with
    | false =>
      rw [hs] at h
      dsimp only [Bool.false_eq_true, ↓reduceIte] at h
      rcases collectMatchingTraitImpls_mem_fst c dp typeArgs rest acc h with hacc | ⟨hm, hd⟩
      · exact Or.inl hacc
      · exact Or.inr ⟨List.Mem.tail _ hm, hd⟩
    | true =>
      rw [hs] at h
      dsimp only [↓reduceIte] at h
      cases hargs : e.traitRef.args with
      | nil =>
        rw [hargs] at h
        rcases collectMatchingTraitImpls_mem_fst c dp typeArgs rest acc h with hacc | ⟨hm, hd⟩
        · exact Or.inl hacc
        · exact Or.inr ⟨List.Mem.tail _ hm, hd⟩
      | cons a as =>
        rw [hargs] at h
        cases hm : matchRigidTyPrefix (a :: as) typeArgs [] with
        | none =>
          rw [hm] at h
          rcases collectMatchingTraitImpls_mem_fst c dp typeArgs rest acc h with hacc | ⟨hm', hd⟩
          · exact Or.inl hacc
          · exact Or.inr ⟨List.Mem.tail _ hm', hd⟩
        | some _ =>
          rw [hm] at h
          dsimp only at h
          rcases collectMatchingTraitImpls_mem_fst c dp typeArgs rest _ h with hacc | ⟨hm', hd⟩
          · rcases upsertMatchingTraitImpl_mem_fst acc hacc with rfl | hacc'
            · exact Or.inr ⟨List.Mem.head _, hs⟩
            · exact Or.inl hacc'
          · exact Or.inr ⟨List.Mem.tail _ hm', hd⟩

theorem filterMostSpecificTraitImpls_sub
    (allMatches : List (TraitImplEntry × Option (List RigidTy))) :
    ∀ (cands : List (TraitImplEntry × Option (List RigidTy)))
      {p : TraitImplEntry × Option (List RigidTy)},
      p ∈ filterMostSpecificTraitImpls allMatches cands → p ∈ cands
  | [], _, h => nomatch h
  | (e, opt) :: rest, p, h => by
    unfold filterMostSpecificTraitImpls at h
    cases hi : isTraitImplInstanceOfAll e.traitRef.args allMatches with
    | true =>
      rw [hi] at h
      dsimp only at h
      rcases List.mem_cons.mp h with rfl | hrest
      · exact List.Mem.head _
      · exact List.Mem.tail _ (filterMostSpecificTraitImpls_sub allMatches rest hrest)
    | false =>
      rw [hi] at h
      dsimp only at h
      exact List.Mem.tail _ (filterMostSpecificTraitImpls_sub allMatches rest h)

/-- Helper factoring the non-`.param` branch of `resolveCalleeBodyAndArgs?`. -/
def resolveCalleeNonParam? (callees : List CapturedMir) (allTraitImpls : List TraitImplEntry)
    (defPath : DefPath) (firstArg : RigidTy) (restArgs : List RigidTy) :
    Option (CapturedMir × List RigidTy) :=
  let matchedImpls := collectMatchingTraitImpls callees allTraitImpls defPath (firstArg :: restArgs)
  match matchedImpls with
  | .nil =>
    match findCallee? callees defPath with
    | Option.none => Option.none
    | Option.some c =>
      match
        Bool.and
          (hasTraitImplForDefPath allTraitImpls defPath)
          (Bool.not (allParamsInCallerLayouts 0 firstArg))
      with
      | true => Option.none
      | false => Option.some (c, firstArg :: restArgs)
  | _ :: _ =>
    match filterMostSpecificTraitImpls matchedImpls matchedImpls with
    | (winnerEntry, Option.some implTypeArgs) :: .nil =>
      match findCallee? callees winnerEntry.implPath with
      | Option.some c =>
        let effectiveTypeArgs :=
          match stringEq winnerEntry.implPath defPath with
          | true => firstArg :: restArgs
          | false => implTypeArgs
        if effectiveTypeArgs.length == c.typeParamCount then
          Option.some (c, effectiveTypeArgs)
        else
          Option.none
      | Option.none => Option.none
    | _ => Option.none

theorem resolveCalleeNonParam?_congr
    {c₁ c₂ : List CapturedMir} {ti₁ ti₂ : List TraitImplEntry} {dp : DefPath}
    (firstArg : RigidTy) (restArgs : List RigidTy)
    (h_dp : findCallee? c₁ dp = findCallee? c₂ dp)
    (h_ti : ti₁.filter (fun e => stringEq e.traitRef.defPath dp) =
            ti₂.filter (fun e => stringEq e.traitRef.defPath dp))
    (h_impl : ∀ e ∈ ti₁, stringEq e.traitRef.defPath dp = true →
      findCallee? c₁ e.implPath = findCallee? c₂ e.implPath) :
    resolveCalleeNonParam? c₁ ti₁ dp firstArg restArgs =
      resolveCalleeNonParam? c₂ ti₂ dp firstArg restArgs := by
  have h_has : hasTraitImplForDefPath ti₁ dp = hasTraitImplForDefPath ti₂ dp :=
    hasTraitImplForDefPath_eq_of_filter_eq h_ti
  have h_col : collectMatchingTraitImpls c₁ ti₁ dp (firstArg :: restArgs) [] =
      collectMatchingTraitImpls c₂ ti₂ dp (firstArg :: restArgs) [] := by
    rw [collectMatchingTraitImpls_filter_defPath c₁ dp (firstArg :: restArgs) ti₁ [],
      collectMatchingTraitImpls_filter_defPath c₂ dp (firstArg :: restArgs) ti₂ [],
      ← h_ti]
    exact collectMatchingTraitImpls_congr_callees (firstArg :: restArgs) _ []
      (fun e hm hs => h_impl e (List.mem_filter.mp hm).1 hs)
  unfold resolveCalleeNonParam?
  dsimp only
  rw [← h_col]
  cases h_m : collectMatchingTraitImpls c₁ ti₁ dp (firstArg :: restArgs) [] with
  | nil =>
    dsimp only
    rw [h_dp, h_has]
  | cons m₀ ms =>
    dsimp only
    cases h_f : filterMostSpecificTraitImpls (m₀ :: ms) (m₀ :: ms) with
    | nil => rfl
    | cons w ws =>
      rcases w with ⟨winnerEntry, implOpt⟩
      cases implOpt with
      | none => rfl
      | some implTypeArgs =>
        cases ws with
        | cons _ _ => rfl
        | nil =>
          dsimp only
          have hw_mem : (winnerEntry, some implTypeArgs) ∈ (m₀ :: ms) := by
            have hhead : (winnerEntry, some implTypeArgs) ∈
                filterMostSpecificTraitImpls (m₀ :: ms) (m₀ :: ms) := by
              rw [h_f]
              exact List.Mem.head _
            exact filterMostSpecificTraitImpls_sub (m₀ :: ms) (m₀ :: ms) hhead
          have hw_fst : winnerEntry ∈
              (collectMatchingTraitImpls c₁ ti₁ dp (firstArg :: restArgs) []).map Prod.fst := by
            rw [h_m]
            exact List.mem_map.mpr ⟨(winnerEntry, some implTypeArgs), hw_mem, rfl⟩
          rcases collectMatchingTraitImpls_mem_fst c₁ dp (firstArg :: restArgs) ti₁ [] hw_fst with
            hnil | ⟨h_in, h_str⟩
          · nomatch hnil
          · rw [h_impl winnerEntry h_in h_str]

/-- **Trait-Aware `resolveCalleeBodyAndArgs?` Congruence**: whenever `c₁` and `c₂` agree on
`findCallee?` at `dp`, have identical `TraitImplEntry` records for `dp`, and agree on
`findCallee?` at `e.implPath` for every `TraitImplEntry` targeting `dp`, `resolveCalleeBodyAndArgs?`
returns the exact same body and effective type arguments for *all* `typeArgs : List RigidTy`. -/
theorem resolveCalleeBodyAndArgs?_eq_of_traitConeAgree
    {c₁ c₂ : List CapturedMir} {extra₁ extra₂ : List TraitImplEntry} {dp : DefPath}
    (typeArgs : List RigidTy)
    (h_dp : findCallee? c₁ dp = findCallee? c₂ dp)
    (h_ti : (extra₁ ++ flatMapTraitImpls c₁).filter (fun e => stringEq e.traitRef.defPath dp) =
            (extra₂ ++ flatMapTraitImpls c₂).filter (fun e => stringEq e.traitRef.defPath dp))
    (h_impl : ∀ e ∈ extra₁ ++ flatMapTraitImpls c₁,
      stringEq e.traitRef.defPath dp = true →
      findCallee? c₁ e.implPath = findCallee? c₂ e.implPath) :
    resolveCalleeBodyAndArgs? c₁ dp typeArgs extra₁ =
      resolveCalleeBodyAndArgs? c₂ dp typeArgs extra₂ := by
  have h_has : hasTraitImplForDefPath (extra₁ ++ flatMapTraitImpls c₁) dp =
      hasTraitImplForDefPath (extra₂ ++ flatMapTraitImpls c₂) dp :=
    hasTraitImplForDefPath_eq_of_filter_eq h_ti
  cases typeArgs with
  | nil =>
    unfold resolveCalleeBodyAndArgs?
    dsimp only
    rw [h_dp]
  | cons firstArg restArgs =>
    have h_np := resolveCalleeNonParam?_congr firstArg restArgs h_dp h_ti h_impl
    cases firstArg with
    | param _ _ =>
      unfold resolveCalleeBodyAndArgs?
      dsimp only
      rw [h_dp, h_has]
    | _ => exact h_np

/-- **Trait-Aware `lookupCallee` Congruence (`lookupCallee_eq_of_traitConeAgree`)**. -/
theorem lookupCallee_eq_of_traitConeAgree
    {c₁ c₂ : List CapturedMir} {extra₁ extra₂ : List TraitImplEntry} {dp : DefPath}
    (layouts : LayoutTable) (typeArgs : List RigidTy)
    (h_dp : findCallee? c₁ dp = findCallee? c₂ dp)
    (h_ti : (extra₁ ++ flatMapTraitImpls c₁).filter (fun e => stringEq e.traitRef.defPath dp) =
            (extra₂ ++ flatMapTraitImpls c₂).filter (fun e => stringEq e.traitRef.defPath dp))
    (h_impl : ∀ e ∈ extra₁ ++ flatMapTraitImpls c₁,
      stringEq e.traitRef.defPath dp = true →
      findCallee? c₁ e.implPath = findCallee? c₂ e.implPath) :
    lookupCallee c₁ layouts dp typeArgs extra₁ =
      lookupCallee c₂ layouts dp typeArgs extra₂ := by
  unfold lookupCallee
  rw [resolveCalleeBodyAndArgs?_eq_of_traitConeAgree typeArgs h_dp h_ti h_impl]

theorem resolveCalleeNonParam?_origin
    {c₁ : List CapturedMir} {extra₁ : List TraitImplEntry} {dp : DefPath}
    {firstArg : RigidTy} {restArgs : List RigidTy} {b : CapturedMir} {effArgs : List RigidTy}
    (hnp : resolveCalleeNonParam? c₁ (extra₁ ++ flatMapTraitImpls c₁) dp firstArg restArgs =
      some (b, effArgs)) :
    findCallee? c₁ dp = some b ∨
      ∃ e ∈ extra₁ ++ flatMapTraitImpls c₁,
        stringEq e.traitRef.defPath dp = true ∧ findCallee? c₁ e.implPath = some b := by
  unfold resolveCalleeNonParam? at hnp
  dsimp only at hnp
  cases hm : collectMatchingTraitImpls c₁ (extra₁ ++ flatMapTraitImpls c₁) dp (firstArg :: restArgs) [] with
  | nil =>
    rw [hm] at hnp
    dsimp only at hnp
    cases hf : findCallee? c₁ dp with
    | none => rw [hf] at hnp; nomatch hnp
    | some c =>
      rw [hf] at hnp
      dsimp only at hnp
      cases hcond : (hasTraitImplForDefPath (extra₁ ++ flatMapTraitImpls c₁) dp &&
          !allParamsInCallerLayouts 0 firstArg) with
      | true => rw [hcond] at hnp; nomatch hnp
      | false =>
        rw [hcond] at hnp
        cases hnp
        exact Or.inl rfl
  | cons m₀ ms =>
    rw [hm] at hnp
    dsimp only at hnp
    cases h_f : filterMostSpecificTraitImpls (m₀ :: ms) (m₀ :: ms) with
    | nil => rw [h_f] at hnp; nomatch hnp
    | cons w ws =>
      rw [h_f] at hnp
      rcases w with ⟨winnerEntry, implOpt⟩
      cases implOpt with
      | none => nomatch hnp
      | some implTypeArgs =>
        cases ws with
        | cons _ _ => nomatch hnp
        | nil =>
          dsimp only at hnp
          cases hfw : findCallee? c₁ winnerEntry.implPath with
          | none => rw [hfw] at hnp; nomatch hnp
          | some c =>
            rw [hfw] at hnp
            dsimp only at hnp
            cases hlen : ((match stringEq winnerEntry.implPath dp with
                | true => firstArg :: restArgs
                | false => implTypeArgs).length == c.typeParamCount) with
            | false =>
              rw [hlen] at hnp
              nomatch hnp
            | true =>
              rw [hlen] at hnp
              cases hnp
              have hw_mem : (winnerEntry, some implTypeArgs) ∈ (m₀ :: ms) := by
                have hhead : (winnerEntry, some implTypeArgs) ∈
                    filterMostSpecificTraitImpls (m₀ :: ms) (m₀ :: ms) := by
                  rw [h_f]
                  exact List.Mem.head _
                exact filterMostSpecificTraitImpls_sub (m₀ :: ms) (m₀ :: ms) hhead
              have hw_fst : winnerEntry ∈
                  (collectMatchingTraitImpls c₁ (extra₁ ++ flatMapTraitImpls c₁) dp
                    (firstArg :: restArgs) []).map Prod.fst := by
                rw [hm]
                exact List.mem_map.mpr ⟨(winnerEntry, some implTypeArgs), hw_mem, rfl⟩
              rcases collectMatchingTraitImpls_mem_fst c₁ dp (firstArg :: restArgs)
                  (extra₁ ++ flatMapTraitImpls c₁) [] hw_fst with hnil | ⟨h_in, h_str⟩
              · nomatch hnil
              · exact Or.inr ⟨winnerEntry, h_in, h_str, hfw⟩

/-- Every body resolved by `resolveCalleeBodyAndArgs? c₁ dp typeArgs extra₁` has its uninstantiated
`CapturedMir` found by `findCallee? c₁ dp` or `findCallee? c₁ e.implPath` for some
`e ∈ extra₁ ++ flatMapTraitImpls c₁` with `stringEq e.traitRef.defPath dp = true`. -/
theorem resolveCalleeBodyAndArgs?_origin
    {c₁ : List CapturedMir} {extra₁ : List TraitImplEntry} {dp : DefPath}
    {typeArgs : List RigidTy} {b : CapturedMir} {effArgs : List RigidTy}
    (h_res : resolveCalleeBodyAndArgs? c₁ dp typeArgs extra₁ = some (b, effArgs)) :
    findCallee? c₁ dp = some b ∨
      ∃ e ∈ extra₁ ++ flatMapTraitImpls c₁,
        stringEq e.traitRef.defPath dp = true ∧ findCallee? c₁ e.implPath = some b := by
  cases typeArgs with
  | nil =>
    unfold resolveCalleeBodyAndArgs? at h_res
    dsimp only at h_res
    cases hf : findCallee? c₁ dp with
    | none => rw [hf] at h_res; nomatch h_res
    | some c =>
      rw [hf] at h_res
      cases h_res
      exact Or.inl rfl
  | cons firstArg restArgs =>
    cases firstArg with
    | param _ _ =>
      unfold resolveCalleeBodyAndArgs? at h_res
      dsimp only at h_res
      cases hf : findCallee? c₁ dp with
      | none => rw [hf] at h_res; nomatch h_res
      | some c =>
        rw [hf] at h_res
        dsimp only at h_res
        cases hhas : hasTraitImplForDefPath (extra₁ ++ flatMapTraitImpls c₁) dp with
        | true => rw [hhas] at h_res; nomatch h_res
        | false =>
          rw [hhas] at h_res
          cases h_res
          exact Or.inl rfl
    | alias _ _ | bool | char | int _ | uint _ | float _ | never | str | tuple _
    | array _ _ | slice _ | ref _ _ | rawPtr _ _ | adt _ _ | fnDef _ _
    | fnPtr _ _ _ _ | closure _ _ | dynamic _ | foreign _ | other _ =>
      exact resolveCalleeNonParam?_origin h_res

/-- Every `calleeBody` returned by `lookupCallee c₁ L dp typeArgs extra₁` has the form
`b.instantiate subst` for some `b` satisfying `resolveCalleeBodyAndArgs?_origin`. -/
theorem lookupCallee_origin
    {c₁ : List CapturedMir} {extra₁ : List TraitImplEntry} {L : LayoutTable}
    {dp : DefPath} {typeArgs : List RigidTy} {calleeBody : CapturedMir}
    (h_lk : lookupCallee c₁ L dp typeArgs extra₁ = some calleeBody) :
    ∃ b subst,
      (findCallee? c₁ dp = some b ∨
        ∃ e ∈ extra₁ ++ flatMapTraitImpls c₁,
          stringEq e.traitRef.defPath dp = true ∧ findCallee? c₁ e.implPath = some b) ∧
      calleeBody = b.instantiate subst := by
  unfold lookupCallee at h_lk
  cases hr : resolveCalleeBodyAndArgs? c₁ dp typeArgs extra₁ with
  | none => rw [hr] at h_lk; nomatch h_lk
  | some p =>
    rcases p with ⟨b, effArgs⟩
    rw [hr] at h_lk
    dsimp only at h_lk
    have horig := resolveCalleeBodyAndArgs?_origin hr
    split at h_lk
    · cases h_lk
      exact ⟨calleeBody, [], horig, (CapturedMir.instantiate_nil calleeBody).symm⟩
    · split at h_lk
      · nomatch h_lk
      · split at h_lk
        · rename_i argLayouts _
          cases h_lk
          exact ⟨b, effArgs.zip argLayouts, horig, rfl⟩
        · nomatch h_lk

/-- When `dp ∈ cone` and every `TraitImplEntry` targeting `dp` has `e.implPath ∈ cone`, any
`calleeBody` returned by `lookupCallee c₁ L dp typeArgs extra₁` lies in
`InConeSetPoly cone root c₁`. -/
theorem inConeSetPoly_of_lookup_trait {cone : List DefPath} (root : CapturedMir)
    {c₁ : List CapturedMir} {extra₁ : List TraitImplEntry} {L : LayoutTable}
    {dp : DefPath} {typeArgs : List RigidTy} {calleeBody : CapturedMir}
    (h_dp : dp ∈ cone)
    (h_impl_cone : ∀ e ∈ extra₁ ++ flatMapTraitImpls c₁,
      stringEq e.traitRef.defPath dp = true → e.implPath ∈ cone)
    (h_lk : lookupCallee c₁ L dp typeArgs extra₁ = some calleeBody) :
    InConeSetPoly cone root c₁ calleeBody := by
  obtain ⟨b, subst, horig, hinst⟩ := lookupCallee_origin h_lk
  rcases horig with hf | ⟨e, he_mem, he_str, hf⟩
  · obtain ⟨hm, hd⟩ := findCallee?_spec hf
    right
    refine ⟨b, subst, ?_, hinst⟩
    unfold coneBodies
    rw [List.mem_filter]
    exact ⟨hm, inCone_iff.mpr (hd ▸ h_dp)⟩
  · obtain ⟨hm, hd⟩ := findCallee?_spec hf
    right
    refine ⟨b, subst, ?_, hinst⟩
    unfold coneBodies
    rw [List.mem_filter]
    exact ⟨hm, inCone_iff.mpr (hd ▸ h_impl_cone e he_mem he_str)⟩

/-! ### Trait-Aware Semantic & Syntactic Cone Narrowing -/

/-- Agreement condition between `(c₁, ti₁)` and `(c₂, ti₂)` on a call cone `cone` supporting full
`TraitImplEntry` dispatch:
1. `calleesAgreeOn cone c₁ c₂` (`findCallee? c₁ dp = findCallee? c₂ dp` for all `dp ∈ cone`),
2. For every `dp ∈ cone`, the filtered `TraitImplEntry` lists targeting `dp` in
   `ti₁ ++ flatMapTraitImpls c₁` and `ti₂ ++ flatMapTraitImpls c₂` are equal, and
3. For every `dp ∈ cone` and `e ∈ ti₁ ++ flatMapTraitImpls c₁` targeting `dp`, `e.implPath ∈ cone`. -/
def TraitConeAgreeOn (cone : List DefPath) (c₁ c₂ : CalleeEnv)
    (ti₁ ti₂ : List TraitImplEntry) : Prop :=
  calleesAgreeOn cone c₁ c₂ ∧
    (∀ dp ∈ cone,
      (ti₁ ++ flatMapTraitImpls c₁).filter (fun e => stringEq e.traitRef.defPath dp) =
        (ti₂ ++ flatMapTraitImpls c₂).filter (fun e => stringEq e.traitRef.defPath dp)) ∧
    (∀ dp ∈ cone, ∀ e ∈ ti₁ ++ flatMapTraitImpls c₁,
      stringEq e.traitRef.defPath dp = true → e.implPath ∈ cone)

theorem TraitConeAgreeOn.refl (cone : List DefPath) (c : CalleeEnv) (ti : List TraitImplEntry)
    (h_impl : ∀ dp ∈ cone, ∀ e ∈ ti ++ flatMapTraitImpls c,
      stringEq e.traitRef.defPath dp = true → e.implPath ∈ cone) :
    TraitConeAgreeOn cone c c ti ti :=
  ⟨calleesAgreeOn.refl cone c, fun _ _ => rfl, h_impl⟩

theorem lookupCallee_eq_of_traitConeAgreeOn {cone : List DefPath}
    {c₁ c₂ : CalleeEnv} {ti₁ ti₂ : List TraitImplEntry} {dp : DefPath}
    (L : LayoutTable) (typeArgs : List RigidTy)
    (h_ag : TraitConeAgreeOn cone c₁ c₂ ti₁ ti₂) (h_dp : dp ∈ cone) :
    lookupCallee c₁ L dp typeArgs ti₁ = lookupCallee c₂ L dp typeArgs ti₂ :=
  lookupCallee_eq_of_traitConeAgree L typeArgs (h_ag.1 dp h_dp) (h_ag.2.1 dp h_dp)
    (fun e he hs => h_ag.1 e.implPath (h_ag.2.2 dp h_dp e he hs))

/-- Trait-aware call-target cone condition (`CallTargetInConeTrait`): every target resolved by
`resolveCallTarget` has `target.defPath ∈ cone` and is not `const_eval_select`. Unlike
`MirLiftCore.CallTargetInConePoly`, `target.defPath` MAY be a trait method dispatched through
`TraitImplEntry`! -/
def CallTargetInConeTrait (cone : List DefPath) (s : MachineState)
    (cur : CapturedMir) (func : Operand) (argCount : Nat) : Prop :=
  ∀ target localsAfterFunc,
    resolveCallTarget s func argCount (bodyLocalDeclsOf (some cur)) cur.layouts =
        .ok target localsAfterFunc →
      target.defPath ∈ cone ∧
        isNonSelectIntrinsicOpt (classifyRustIntrinsic? target.defPath) = true

def TermConeSafeTrait (cone : List DefPath) (s : MachineState) (cur : CapturedMir)
    (term : Terminator) : Prop :=
  match term.kind with
  | .call func argOps _ _ _ => CallTargetInConeTrait cone s cur func (length argOps)
  | .tailCall func argOps => CallTargetInConeTrait cone s cur func (length argOps)
  | _ => True

def StepConeSafeTrait (cone : List DefPath) (body : CapturedMir) (s : MachineState) : Prop :=
  ∀ blk, get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx = some blk →
    (∀ stmt, get? blk.statements s.frame.stmtIdx = some stmt →
      Statement.calleeQueryFree stmt = true) ∧
    TermConeSafeTrait cone s (s.memory.activeCallee.getD body) blk.terminator

@[simp] theorem Memory.withCalleesAndTraits_callees (c : CalleeEnv) (ti : List TraitImplEntry) (m : Memory) :
    (Memory.withCalleesAndTraits c ti m).callees = c := rfl
@[simp] theorem Memory.withCalleesAndTraits_borrows (c : CalleeEnv) (ti : List TraitImplEntry) (m : Memory) :
    (Memory.withCalleesAndTraits c ti m).borrows = m.borrows := rfl
@[simp] theorem Memory.withCalleesAndTraits_globals (c : CalleeEnv) (ti : List TraitImplEntry) (m : Memory) :
    (Memory.withCalleesAndTraits c ti m).globals = m.globals := rfl
@[simp] theorem Memory.withCalleesAndTraits_callerLocals (c : CalleeEnv) (ti : List TraitImplEntry) (m : Memory) :
    (Memory.withCalleesAndTraits c ti m).callerLocals = m.callerLocals := rfl
@[simp] theorem Memory.withCalleesAndTraits_fnPtrs (c : CalleeEnv) (ti : List TraitImplEntry) (m : Memory) :
    (Memory.withCalleesAndTraits c ti m).fnPtrs = m.fnPtrs := rfl
@[simp] theorem Memory.withCalleesAndTraits_traitImpls (c : CalleeEnv) (ti : List TraitImplEntry) (m : Memory) :
    (Memory.withCalleesAndTraits c ti m).traitImpls = ti := rfl
@[simp] theorem Memory.withCalleesAndTraits_callStack (c : CalleeEnv) (ti : List TraitImplEntry) (m : Memory) :
    (Memory.withCalleesAndTraits c ti m).callStack = m.callStack := rfl
@[simp] theorem Memory.withCalleesAndTraits_activeCallee (c : CalleeEnv) (ti : List TraitImplEntry) (m : Memory) :
    (Memory.withCalleesAndTraits c ti m).activeCallee = m.activeCallee := rfl
@[simp] theorem Memory.withCalleesAndTraits_activeProtectors (c : CalleeEnv) (ti : List TraitImplEntry) (m : Memory) :
    (Memory.withCalleesAndTraits c ti m).activeProtectors = m.activeProtectors := rfl

/-- **Trait-aware terminator narrowing (`evalTerminator_withCalleesAndTraits`)**: under
`TraitConeAgreeOn` and `TermConeSafeTrait`, `evalTerminator` commutes with
`Memory.withCalleesAndTraits c₂ ti₂`, preserving direct, polymorphic, *and* trait-method calls. -/
theorem evalTerminator_withCalleesAndTraits (cone : List DefPath) (c₂ : CalleeEnv)
    (ti₂ : List TraitImplEntry) (s : MachineState) (term : Terminator) (cur : CapturedMir)
    (h_agree : TraitConeAgreeOn cone s.memory.callees c₂ s.memory.traitImpls ti₂)
    (h_safe : TermConeSafeTrait cone s cur term) :
    evalTerminator (MachineState.mapMem (Memory.withCalleesAndTraits c₂ ti₂) s) term (some cur) =
      MirStepNode.mapMem (Memory.withCalleesAndTraits c₂ ti₂)
        (evalTerminator s term (some cur)) := by
  rcases term with ⟨kind, span⟩
  cases kind with
  | goto _ => rfl
  | switchInt _ _ =>
    unfold evalTerminator
    dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory,
      Memory.withCalleesAndTraits_borrows, Memory.withCalleesAndTraits_globals,
      Memory.withCalleesAndTraits_callerLocals, Memory.withCalleesAndTraits_callStack]
    repeat' (first | exact nodeCT_fail | rfl | split)
  | unwindResume =>
    show (match unwindFromCallStack s.memory.callStack
          (Memory.withCalleesAndTraits c₂ ti₂ s.memory) with
        | .running nextState => MirStepNode.step nextState
        | .halted out => MirStepNode.retOutcome out
        | .faulted fk => MirStepNode.fail fk) =
      MirStepNode.mapMem (Memory.withCalleesAndTraits c₂ ti₂)
        (match unwindFromCallStack s.memory.callStack s.memory with
          | .running nextState => MirStepNode.step nextState
          | .halted out => MirStepNode.retOutcome out
          | .faulted fk => MirStepNode.fail fk)
    rw [unwindFromCallStack_withCalleesAndTraits]
    cases unwindFromCallStack s.memory.callStack s.memory <;> rfl
  | unwindTerminate => rfl
  | return_ => exact evalTerminator_return_withCalleesAndTraits c₂ ti₂ s span (some cur)
  | unreachable => rfl
  | drop _ _ _ =>
    unfold evalTerminator
    dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory]
    repeat' (first | exact nodeCT_fail | rfl | split)
  | assert _ _ _ _ =>
    unfold evalTerminator
    dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory,
      Memory.withCalleesAndTraits_borrows, Memory.withCalleesAndTraits_globals,
      Memory.withCalleesAndTraits_callerLocals, Memory.withCalleesAndTraits_callStack]
    repeat' (first
      | exact nodeCT_fail | rfl
      | exact nodeCT_unwind c₂ ti₂ s _ _
      | split)
  | call func argOps destination target unwind =>
    have hq : CallTargetInConeTrait cone s cur func (length argOps) := h_safe
    cases target with
    | some targetBb =>
      unfold evalTerminator
      dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory,
        Memory.withCalleesAndTraits_borrows, Memory.withCalleesAndTraits_globals,
        Memory.withCalleesAndTraits_callerLocals, Memory.withCalleesAndTraits_callees,
        Memory.withCalleesAndTraits_traitImpls, Memory.withCalleesAndTraits_callStack]
      rw [show resolveCallTarget (MachineState.mapMem (Memory.withCalleesAndTraits c₂ ti₂) s)
            func (length argOps) (bodyLocalDeclsOf (some cur)) cur.layouts =
          resolveCallTarget s func (length argOps) (bodyLocalDeclsOf (some cur)) cur.layouts
        from rfl]
      cases h_res : resolveCallTarget s func (length argOps)
          (bodyLocalDeclsOf (some cur)) cur.layouts with
      | ub => rfl
      | unsupported => rfl
      | ok tgt localsAfterFunc =>
        obtain ⟨h_dp, h_cl⟩ := hq tgt localsAfterFunc h_res
        dsimp only
        cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals cur.layouts
            s.memory.callerLocals (callStack := s.memory.callStack) with
        | ub => rfl
        | unsupported => rfl
        | ok argVals locals' =>
          dsimp only
          rw [← lookupCallee_eq_of_traitConeAgreeOn cur.layouts tgt.typeArgs h_agree h_dp,
            evalDirectRustIntrinsic?_withCalleesAndTraits_of_nonSelect c₂ ti₂ s (some cur) tgt
              (bodyLocalDeclsOf (some cur)) cur.layouts argOps argVals locals' destination
              targetBb unwind h_cl]
          cases evalDirectRustIntrinsic? s (some cur) tgt (bodyLocalDeclsOf (some cur))
              cur.layouts argOps argVals locals' destination targetBb unwind <;>
            repeat' (first
              | exact nodeCT_fail | rfl
              | exact writeIntrinsicReturn_withCalleesAndTraits c₂ ti₂ s _ _ _ _
              | split)
    | none =>
      unfold evalTerminator
      dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory,
        Memory.withCalleesAndTraits_borrows, Memory.withCalleesAndTraits_globals,
        Memory.withCalleesAndTraits_callerLocals, Memory.withCalleesAndTraits_callees,
        Memory.withCalleesAndTraits_traitImpls, Memory.withCalleesAndTraits_callStack]
      rw [show resolveCallTarget (MachineState.mapMem (Memory.withCalleesAndTraits c₂ ti₂) s)
            func (length argOps) (bodyLocalDeclsOf (some cur)) cur.layouts =
          resolveCallTarget s func (length argOps) (bodyLocalDeclsOf (some cur)) cur.layouts
        from rfl]
      cases h_res : resolveCallTarget s func (length argOps)
          (bodyLocalDeclsOf (some cur)) cur.layouts with
      | ub => rfl
      | unsupported => rfl
      | ok tgt localsAfterFunc =>
        obtain ⟨h_dp, _⟩ := hq tgt localsAfterFunc h_res
        dsimp only
        cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals cur.layouts
            s.memory.callerLocals (callStack := s.memory.callStack) with
        | ub => rfl
        | unsupported => rfl
        | ok argVals locals' =>
          dsimp only
          rw [← lookupCallee_eq_of_traitConeAgreeOn cur.layouts tgt.typeArgs h_agree h_dp]
          repeat' (first
            | exact nodeCT_fail | rfl
            | exact nodeCT_unwind c₂ ti₂ s _ _
            | split)
  | tailCall func argOps =>
    have hq : CallTargetInConeTrait cone s cur func (length argOps) := h_safe
    unfold evalTerminator
    dsimp only
    unfold evalTailCallTerminator
    dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory,
      Memory.withCalleesAndTraits_borrows, Memory.withCalleesAndTraits_globals,
      Memory.withCalleesAndTraits_callerLocals, Memory.withCalleesAndTraits_callees,
      Memory.withCalleesAndTraits_traitImpls, Memory.withCalleesAndTraits_callStack]
    rw [show resolveCallTarget (MachineState.mapMem (Memory.withCalleesAndTraits c₂ ti₂) s)
          func (length argOps) (bodyLocalDeclsOf (some cur)) cur.layouts =
        resolveCallTarget s func (length argOps) (bodyLocalDeclsOf (some cur)) cur.layouts
      from rfl]
    cases h_res : resolveCallTarget s func (length argOps)
        (bodyLocalDeclsOf (some cur)) cur.layouts with
    | ub => rfl
    | unsupported => rfl
    | ok tgt localsAfterFunc =>
      obtain ⟨h_dp, _⟩ := hq tgt localsAfterFunc h_res
      dsimp only
      cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals cur.layouts
          s.memory.callerLocals (callStack := s.memory.callStack) with
      | ub => rfl
      | unsupported => rfl
      | ok argVals locals' =>
        dsimp only
        rw [← lookupCallee_eq_of_traitConeAgreeOn cur.layouts tgt.typeArgs h_agree h_dp]
        repeat' (first
          | exact nodeCT_fail | rfl
          | split)
  | _ => rfl

/-- **Single-step bisimulation with narrowed callees and hoisted trait impls
(`stepMirFn_withCalleesAndTraits`)**. -/
theorem stepMirFn_withCalleesAndTraits (cone : List DefPath) (body : CapturedMir)
    (s : MachineState) (c₂ : CalleeEnv) (ti₂ : List TraitImplEntry)
    (h_agree : TraitConeAgreeOn cone s.memory.callees c₂ s.memory.traitImpls ti₂)
    (h_safe : StepConeSafeTrait cone body s) :
    stepMirFn body (MachineState.mapMem (Memory.withCalleesAndTraits c₂ ti₂) s) =
      MirStepNode.mapMem (Memory.withCalleesAndTraits c₂ ti₂) (stepMirFn body s) := by
  unfold stepMirFn
  dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory,
    Memory.withCalleesAndTraits_activeCallee]
  split
  · rfl
  · cases h_bb : get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx with
    | none => rfl
    | some blk =>
      obtain ⟨h_stmt, h_term⟩ := h_safe blk h_bb
      dsimp only
      cases h_st : get? blk.statements s.frame.stmtIdx with
      | some stmt =>
        dsimp only
        exact evalStmt_withCalleesAndTraits c₂ ti₂ s stmt _ _ (h_stmt stmt h_st)
      | none =>
        dsimp only
        have h_if : ∀ (b : Bool),
            (if b = true then
              evalTerminator (MachineState.mapMem (Memory.withCalleesAndTraits c₂ ti₂) s)
                blk.terminator (some (s.memory.activeCallee.getD body))
            else MirStepNode.fail .ub) =
            MirStepNode.mapMem (Memory.withCalleesAndTraits c₂ ti₂)
              (if b = true then
                evalTerminator s blk.terminator (some (s.memory.activeCallee.getD body))
              else MirStepNode.fail .ub) := by
          intro b
          cases b with
          | true =>
            exact evalTerminator_withCalleesAndTraits cone c₂ ti₂ s blk.terminator _
              h_agree h_term
          | false => rfl
        exact h_if (s.frame.stmtIdx == length blk.statements)

theorem stepMirFn_calleesAndTraits_preserved (cone : List DefPath) (body : CapturedMir)
    (s : MachineState)
    (h_impl : ∀ dp ∈ cone, ∀ e ∈ s.memory.traitImpls ++ flatMapTraitImpls s.memory.callees,
      stringEq e.traitRef.defPath dp = true → e.implPath ∈ cone)
    (h_safe : StepConeSafeTrait cone body s) :
    stepMirFn body s =
      MirStepNode.mapMem
        (Memory.withCalleesAndTraits s.memory.callees s.memory.traitImpls)
        (stepMirFn body s) :=
  stepMirFn_withCalleesAndTraits cone body s s.memory.callees s.memory.traitImpls
    (TraitConeAgreeOn.refl cone s.memory.callees s.memory.traitImpls h_impl) h_safe

/-- State-level agreement predicate for `TraitConeAgreeOn`. -/
def TraitAgreesAt (cone : List DefPath) (c₂ : CalleeEnv) (ti₂ : List TraitImplEntry)
    (st : MirExecState) : Prop :=
  ∀ s, st = .running s → TraitConeAgreeOn cone s.memory.callees c₂ s.memory.traitImpls ti₂

theorem traitAgreesAt_succ {cone : List DefPath} {c₁ c₂ : CalleeEnv}
    {ti₁ ti₂ : List TraitImplEntry} {st' : MirExecState}
    (h_ag : TraitConeAgreeOn cone c₁ c₂ ti₁ ti₂)
    (h_fix : st' = MirExecState.mapMem (Memory.withCalleesAndTraits c₁ ti₁) st') :
    TraitAgreesAt cone c₂ ti₂ st' := by
  intro s' hs'
  subst hs'
  have hm : s'.memory = Memory.withCalleesAndTraits c₁ ti₁ s'.memory :=
    congrArg MachineState.memory (MirExecState.running.inj h_fix)
  have hc : s'.memory.callees = c₁ := congrArg Memory.callees hm
  have hti : s'.memory.traitImpls = ti₁ := congrArg Memory.traitImpls hm
  rw [hc, hti]
  exact h_ag

theorem runMirExecBounded_trait_cone_narrow (cone : List DefPath) (body : CapturedMir)
    (c₂ : CalleeEnv) (ti₂ : List TraitImplEntry) :
    ∀ (fuel : Nat) (st : MirExecState),
      ConeReach body (StepConeSafeTrait cone body) fuel st →
      TraitAgreesAt cone c₂ ti₂ st →
      runMirExecBounded fuel body (MirExecState.mapMem (Memory.withCalleesAndTraits c₂ ti₂) st) =
        (runMirExecBounded fuel body st).map
          (MirOutcome.mapMem (Memory.withCalleesAndTraits c₂ ti₂))
  | 0, _, _, _ => rfl
  | _ + 1, .halted _, _, _ => rfl
  | _ + 1, .faulted _, _, _ => rfl
  | fuel + 1, .running s, h_reach, h_agree => by
    have h_ag := h_agree s rfl
    obtain ⟨h_safe, h_next⟩ := h_reach
    have h_step := stepMirFn_withCalleesAndTraits cone body s c₂ ti₂ h_ag h_safe
    have h_fix := stepMirFn_calleesAndTraits_preserved cone body s h_ag.2.2 h_safe
    show (match stepMirFn body (MachineState.mapMem (Memory.withCalleesAndTraits c₂ ti₂) s) with
        | .ret out => some out
        | .tau st' => runMirExecBounded fuel body st'
        | .vis (.inr (.inl _)) k => runMirExecBounded fuel body (k PUnit.unit)
        | .vis (.inl _) _ => none
        | .vis (.inr (.inr _)) _ => none) =
      (match stepMirFn body s with
        | .ret out => some out
        | .tau st' => runMirExecBounded fuel body st'
        | .vis (.inr (.inl _)) k => runMirExecBounded fuel body (k PUnit.unit)
        | .vis (.inl _) _ => none
        | .vis (.inr (.inr _)) _ => none).map
        (MirOutcome.mapMem (Memory.withCalleesAndTraits c₂ ti₂))
    rw [h_step]
    revert h_next h_fix
    cases stepMirFn body s with
    | ret _ => intro _ _; rfl
    | tau st' =>
      intro h_next h_fix
      have h_tau_fix : st' =
          MirExecState.mapMem
            (Memory.withCalleesAndTraits s.memory.callees s.memory.traitImpls) st' :=
        Trusted.ITree.ITreeF.tau.inj h_fix
      exact runMirExecBounded_trait_cone_narrow cone body c₂ ti₂ fuel st' h_next
        (traitAgreesAt_succ h_ag h_tau_fix)
    | vis e k =>
      rcases e with fk | obs | ⟨req⟩
      · intro _ _; rfl
      · intro h_next h_fix
        have hk : k PUnit.unit =
            MirExecState.mapMem
              (Memory.withCalleesAndTraits s.memory.callees s.memory.traitImpls)
              (k PUnit.unit) :=
          congrFun (eq_of_heq (Trusted.ITree.ITreeF.vis.inj h_fix).2) PUnit.unit
        exact runMirExecBounded_trait_cone_narrow cone body c₂ ti₂ fuel (k PUnit.unit) h_next
          (traitAgreesAt_succ h_ag hk)
      · intro _ _; rfl

theorem wpMirExecSym_trait_cone_narrow (cone : List DefPath) (body : CapturedMir)
    (c₂ : CalleeEnv) (ti₂ : List TraitImplEntry) (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirOutcome.mapMem (Memory.withCalleesAndTraits c₂ ti₂) out) ↔ post out) :
    ∀ (fuel : Nat) (st : MirExecState),
      ConeReach body (StepConeSafeTrait cone body) fuel st →
      TraitAgreesAt cone c₂ ti₂ st →
      (wpMirExecSym fuel body
          (MirExecState.mapMem (Memory.withCalleesAndTraits c₂ ti₂) st) post ↔
        wpMirExecSym fuel body st post)
  | 0, _, _, _ => Iff.rfl
  | fuel + 1, .halted out, _, _ => by
    rw [wpMirExecSym_succ_eq, wpMirExecSym_succ_eq]
    exact h_post out
  | fuel + 1, .faulted _, _, _ => by
    rw [wpMirExecSym_succ_eq, wpMirExecSym_succ_eq]
    exact Iff.rfl
  | fuel + 1, .running s, h_reach, h_agree => by
    have h_ag := h_agree s rfl
    obtain ⟨h_safe, h_next⟩ := h_reach
    have h_step := stepMirFn_withCalleesAndTraits cone body s c₂ ti₂ h_ag h_safe
    have h_fix := stepMirFn_calleesAndTraits_preserved cone body s h_ag.2.2 h_safe
    rw [wpMirExecSym_succ_eq, wpMirExecSym_succ_eq]
    show evalNodeWP _ post
        (stepMirFn body (MachineState.mapMem (Memory.withCalleesAndTraits c₂ ti₂) s)) ↔
      evalNodeWP _ post (stepMirFn body s)
    rw [h_step]
    revert h_next h_fix
    cases stepMirFn body s with
    | ret out => intro _ _; exact h_post out
    | tau st' =>
      intro h_next h_fix
      have h_tau_fix : st' =
          MirExecState.mapMem
            (Memory.withCalleesAndTraits s.memory.callees s.memory.traitImpls) st' :=
        Trusted.ITree.ITreeF.tau.inj h_fix
      exact wpMirExecSym_trait_cone_narrow cone body c₂ ti₂ post h_post fuel st' h_next
        (traitAgreesAt_succ h_ag h_tau_fix)
    | vis e k =>
      rcases e with fk | obs | ⟨req⟩
      · intro _ _; exact Iff.rfl
      · intro h_next h_fix
        have hk : k PUnit.unit =
            MirExecState.mapMem
              (Memory.withCalleesAndTraits s.memory.callees s.memory.traitImpls)
              (k PUnit.unit) :=
          congrFun (eq_of_heq (Trusted.ITree.ITreeF.vis.inj h_fix).2) PUnit.unit
        exact wpMirExecSym_trait_cone_narrow cone body c₂ ti₂ post h_post fuel
          (k PUnit.unit) h_next (traitAgreesAt_succ h_ag hk)
      · intro _ _; exact Iff.rfl

/-! ### Reachable-State Invariant Under Trait-Aware Call-Cone Closure -/

theorem stepConeSafeTrait_of_closedInvPoly {cone : List DefPath} {root : CapturedMir}
    {c₁ : CalleeEnv} {ti₁ : List TraitImplEntry} {s : MachineState}
    (h_root : bodyCallsInConePoly cone root = true)
    (h_cone : (coneBodies cone c₁).all (bodyCallsInConePoly cone) = true)
    (h_inv : ClosedInvPoly cone root c₁ ti₁ s) :
    StepConeSafeTrait cone root s := by
  intro blk h_bb
  have h_body : bodyCallsInConePoly cone (s.memory.activeCallee.getD root) = true := by
    rcases h_inv.2.2.1 with h_eq | ⟨b₀, subst, hb₀, h_eq⟩
    · rw [h_eq]; exact h_root
    · rw [h_eq]; exact bodyCallsInConePoly_instantiate subst (List.all_eq_true.mp h_cone b₀ hb₀)
  unfold bodyCallsInConePoly at h_body
  have h_blk := List.all_eq_true.mp h_body blk (List.mem_of_getElem? h_bb)
  rw [Bool.and_eq_true] at h_blk
  refine ⟨fun stmt h_st => List.all_eq_true.mp h_blk.1 stmt (List.mem_of_getElem? h_st), ?_⟩
  have h_tc := h_blk.2
  revert h_tc
  rcases blk.terminator with ⟨kind, span⟩
  intro h_tc
  cases kind with
  | call func argOps _ _ _ =>
    intro tgt l h_res
    unfold termCallsInConePoly directCallInConePoly at h_tc
    dsimp only at h_tc
    cases h_fn : extractFnDefPath? func with
    | none => rw [h_fn] at h_tc; nomatch h_tc
    | some dp =>
      rw [h_fn, Bool.and_eq_true] at h_tc
      have h_cd := extractCalleeDefPath?_of_extractFnDefPath? h_fn
      unfold resolveCallTarget at h_res
      rw [h_cd] at h_res
      cases h_res
      exact ⟨inCone_iff.mp h_tc.1, h_tc.2⟩
  | tailCall func argOps =>
    intro tgt l h_res
    unfold termCallsInConePoly directCallInConePoly at h_tc
    dsimp only at h_tc
    cases h_fn : extractFnDefPath? func with
    | none => rw [h_fn] at h_tc; nomatch h_tc
    | some dp =>
      rw [h_fn, Bool.and_eq_true] at h_tc
      have h_cd := extractCalleeDefPath?_of_extractFnDefPath? h_fn
      unfold resolveCallTarget at h_res
      rw [h_cd] at h_res
      cases h_res
      exact ⟨inCone_iff.mp h_tc.1, h_tc.2⟩
  | _ => trivial

private theorem nodeSuccs_unwindMatchTrait {cone : List DefPath} {root : CapturedMir}
    {c₁ : CalleeEnv} {ti : List TraitImplEntry} (st : MirExecState)
    (h : ∀ s', st = .running s' → ClosedInvPoly cone root c₁ ti s') :
    NodeSuccs (ClosedInvPoly cone root c₁ ti)
      (match (generalizing := false) st with
        | .running nextState => MirStepNode.step nextState
        | .halted out => MirStepNode.retOutcome out
        | .faulted fk => MirStepNode.fail fk) := by
  cases st with
  | running s' => exact h s' rfl
  | halted _ => trivial
  | faulted _ => trivial

private theorem nodeSuccs_applyUnwindTrait {cone : List DefPath} {root : CapturedMir}
    {c₁ : CalleeEnv} {ti : List TraitImplEntry} {s : MachineState}
    (h_inv : ClosedInvPoly cone root c₁ ti s) (l : List LocalSlot) (u : UnwindAction) :
    NodeSuccs (ClosedInvPoly cone root c₁ ti)
      (match applyUnwindAction s l s.memory u with
        | .running nextState => MirStepNode.step nextState
        | .halted out => MirStepNode.retOutcome out
        | .faulted fk => MirStepNode.fail fk) := by
  refine nodeSuccs_unwindMatchTrait _ ?_
  intro s' hs'
  cases u with
  | unreachable => cases hs'
  | terminate => cases hs'
  | continue_ =>
    exact closedInvPoly_unwindFromCallStack s.memory.callStack s.memory h_inv.1 h_inv.2.1
      h_inv.2.2.2 s' hs'
  | cleanup bb =>
    cases hs'
    exact h_inv

private theorem closedInvPoly_pushTrait {cone : List DefPath} {root : CapturedMir} {c₁ : CalleeEnv}
    {ti : List TraitImplEntry} {s : MachineState} {saved : SavedCallerFrame}
    {b : CapturedMir} {F : StackFrame} (h_inv : ClosedInvPoly cone root c₁ ti s)
    (h_saved : InConeSetPoly cone root c₁ saved.callerBody)
    (h_b : InConeSetPoly cone root c₁ b) :
    ClosedInvPoly cone root c₁ ti
      { frame := F,
        memory := { s.memory with
          callStack := saved :: s.memory.callStack
          activeCallee := some b } } := by
  refine ⟨h_inv.1, h_inv.2.1, h_b, ?_⟩
  intro f hf
  cases hf with
  | head => exact h_saved
  | tail _ hf => exact h_inv.2.2.2 f hf

theorem nodeSuccs_evalTerminatorTrait {cone : List DefPath} {root : CapturedMir}
    {c₁ : CalleeEnv} {ti₁ : List TraitImplEntry} {s : MachineState} {term : Terminator}
    (h_inv : ClosedInvPoly cone root c₁ ti₁ s)
    (h_term : TermConeSafeTrait cone s (s.memory.activeCallee.getD root) term)
    (h_impl : ∀ dp ∈ cone, ∀ e ∈ ti₁ ++ flatMapTraitImpls c₁,
      stringEq e.traitRef.defPath dp = true → e.implPath ∈ cone) :
    NodeSuccs (ClosedInvPoly cone root c₁ ti₁)
      (evalTerminator s term (some (s.memory.activeCallee.getD root))) := by
  have h_cur : InConeSetPoly cone root c₁ (s.memory.activeCallee.getD root) := h_inv.2.2.1
  rcases term with ⟨kind, span⟩
  cases kind with
  | goto target => exact h_inv
  | switchInt discr targets =>
    unfold evalTerminator; dsimp only
    repeat' (first | trivial | exact h_inv | split)
  | unwindResume =>
    unfold evalTerminator; dsimp only
    exact nodeSuccs_unwindMatchTrait _
      (closedInvPoly_unwindFromCallStack s.memory.callStack s.memory h_inv.1 h_inv.2.1 h_inv.2.2.2)
  | unwindTerminate => trivial
  | return_ =>
    rw [ccEvalReturn_eq]
    unfold ccEvalReturn
    repeat' (first | trivial | exact closedInvPoly_return h_inv ‹_› ‹_› | split)
  | unreachable => trivial
  | drop place target unwind =>
    unfold evalTerminator; dsimp only
    repeat' (first | trivial | exact h_inv | split)
  | assert cond expected target unwind =>
    unfold evalTerminator; dsimp only
    repeat' (first | trivial | exact h_inv | exact nodeSuccs_applyUnwindTrait h_inv _ _ | split)
  | call func argOps destination target unwind =>
    have hq : CallTargetInConeTrait cone s (s.memory.activeCallee.getD root) func
        (length argOps) := h_term
    cases target with
    | some targetBb =>
      unfold evalTerminator; dsimp only
      cases h_res : resolveCallTarget s func (length argOps)
          (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root)))
          (s.memory.activeCallee.getD root).layouts with
      | ub => trivial
      | unsupported => trivial
      | ok tgt localsAfterFunc =>
        obtain ⟨h_dp, h_cl⟩ := hq tgt localsAfterFunc h_res
        dsimp only
        cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
            (s.memory.activeCallee.getD root).layouts s.memory.callerLocals (callStack := s.memory.callStack) with
        | ub => trivial
        | unsupported => trivial
        | ok argVals locals' =>
          dsimp only
          cases h_lk : lookupCallee s.memory.callees (s.memory.activeCallee.getD root).layouts
              tgt.defPath tgt.typeArgs s.memory.traitImpls with
          | some calleeBody =>
            dsimp only
            cases checkCalleeTargetCompatible tgt calleeBody (length argVals) with
            | false => trivial
            | true =>
              rw [h_inv.1, h_inv.2.1] at h_lk
              exact closedInvPoly_pushTrait h_inv h_cur
                (inConeSetPoly_of_lookup_trait root h_dp (h_impl tgt.defPath h_dp) h_lk)
          | none =>
            dsimp only
            repeat' (first
              | trivial | exact h_inv
              | exact nodeSuccs_closedInvPoly_of_ctx h_inv
                  (writeIntrinsicReturn_calleeCtx_preserved _ _ _ _ _)
                  (writeIntrinsicReturn_callerBodies _ _ _ _ _)
              | exact nodeSuccs_evalDirectRustIntrinsic?_poly h_inv _ _ _ _ _ _ _ _ _ _ h_cl _
                  (by
                    repeat' (first
                      | trivial | exact h_inv
                      | exact nodeSuccs_closedInvPoly_of_ctx h_inv
                          (writeIntrinsicReturn_calleeCtx_preserved _ _ _ _ _)
                          (writeIntrinsicReturn_callerBodies _ _ _ _ _)
                      | split))
              | split)
    | none =>
      unfold evalTerminator; dsimp only
      cases h_res : resolveCallTarget s func (length argOps)
          (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root)))
          (s.memory.activeCallee.getD root).layouts with
      | ub => trivial
      | unsupported => trivial
      | ok tgt localsAfterFunc =>
        obtain ⟨h_dp, _⟩ := hq tgt localsAfterFunc h_res
        dsimp only
        cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
            (s.memory.activeCallee.getD root).layouts s.memory.callerLocals (callStack := s.memory.callStack) with
        | ub => trivial
        | unsupported => trivial
        | ok argVals locals' =>
          dsimp only
          cases h_lk : lookupCallee s.memory.callees (s.memory.activeCallee.getD root).layouts
              tgt.defPath tgt.typeArgs s.memory.traitImpls with
          | some calleeBody =>
            dsimp only
            cases checkCalleeTargetCompatible tgt calleeBody (length argVals) with
            | false => trivial
            | true =>
              rw [h_inv.1, h_inv.2.1] at h_lk
              exact closedInvPoly_pushTrait h_inv h_cur
                (inConeSetPoly_of_lookup_trait root h_dp (h_impl tgt.defPath h_dp) h_lk)
          | none =>
            dsimp only
            repeat' (first | trivial | exact nodeSuccs_applyUnwindTrait h_inv _ _ | split)
  | tailCall func argOps =>
    have hq : CallTargetInConeTrait cone s (s.memory.activeCallee.getD root) func
        (length argOps) := h_term
    unfold evalTerminator; dsimp only
    unfold evalTailCallTerminator; dsimp only
    cases h_res : resolveCallTarget s func (length argOps)
        (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root)))
        (s.memory.activeCallee.getD root).layouts with
    | ub => trivial
    | unsupported => trivial
    | ok tgt localsAfterFunc =>
      obtain ⟨h_dp, _⟩ := hq tgt localsAfterFunc h_res
      dsimp only
      cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
          (s.memory.activeCallee.getD root).layouts s.memory.callerLocals (callStack := s.memory.callStack) with
      | ub => trivial
      | unsupported => trivial
      | ok argVals locals' =>
        dsimp only
        cases h_lk : lookupCallee s.memory.callees (s.memory.activeCallee.getD root).layouts
            tgt.defPath tgt.typeArgs s.memory.traitImpls with
        | some calleeBody =>
          dsimp only
          rw [h_inv.1, h_inv.2.1] at h_lk
          repeat' (first
            | trivial
            | exact ⟨h_inv.1, h_inv.2.1,
                inConeSetPoly_of_lookup_trait root h_dp (h_impl tgt.defPath h_dp) h_lk,
                h_inv.2.2.2⟩
            | split)
        | none =>
          dsimp only
          repeat' (first | trivial | split)
  | _ => trivial

theorem nodeSuccs_stepMirFnTrait {cone : List DefPath} {root : CapturedMir}
    {c₁ : CalleeEnv} {ti₁ : List TraitImplEntry} {s : MachineState}
    (h_root : bodyCallsInConePoly cone root = true)
    (h_cone : (coneBodies cone c₁).all (bodyCallsInConePoly cone) = true)
    (h_impl : ∀ dp ∈ cone, ∀ e ∈ ti₁ ++ flatMapTraitImpls c₁,
      stringEq e.traitRef.defPath dp = true → e.implPath ∈ cone)
    (h_inv : ClosedInvPoly cone root c₁ ti₁ s) :
    NodeSuccs (ClosedInvPoly cone root c₁ ti₁) (stepMirFn root s) := by
  have h_safe := stepConeSafeTrait_of_closedInvPoly h_root h_cone h_inv
  unfold stepMirFn; dsimp only
  split
  · trivial
  · cases h_bb : get? (s.memory.activeCallee.getD root).basicBlocks s.frame.blockIdx with
    | none => trivial
    | some blk =>
      obtain ⟨h_stmt, h_term⟩ := h_safe blk h_bb
      dsimp only
      cases h_st : get? blk.statements s.frame.stmtIdx with
      | some stmt =>
        dsimp only
        exact nodeSuccs_evalStmtPoly h_inv (h_stmt stmt h_st)
      | none =>
        dsimp only
        cases h_end : s.frame.stmtIdx == length blk.statements with
        | true =>
          exact nodeSuccs_evalTerminatorTrait h_inv h_term h_impl
        | false =>
          trivial

theorem coneReach_of_closedInvTrait {cone : List DefPath} {root : CapturedMir}
    {c₁ : CalleeEnv} {ti₁ : List TraitImplEntry}
    (h_root : bodyCallsInConePoly cone root = true)
    (h_cone : (coneBodies cone c₁).all (bodyCallsInConePoly cone) = true)
    (h_impl : ∀ dp ∈ cone, ∀ e ∈ ti₁ ++ flatMapTraitImpls c₁,
      stringEq e.traitRef.defPath dp = true → e.implPath ∈ cone) :
    ∀ (fuel : Nat) (s : MachineState), ClosedInvPoly cone root c₁ ti₁ s →
      ConeReach root (StepConeSafeTrait cone root) fuel (.running s)
  | 0, _, _ => trivial
  | fuel + 1, s, h_inv => by
    refine ⟨stepConeSafeTrait_of_closedInvPoly h_root h_cone h_inv, ?_⟩
    have h_succ := nodeSuccs_stepMirFnTrait h_root h_cone h_impl h_inv
    revert h_succ
    cases stepMirFn root s with
    | ret _ => intro _; trivial
    | tau st' =>
      cases st' with
      | running s' => intro h; exact coneReach_of_closedInvTrait h_root h_cone h_impl fuel s' h
      | halted _ => intro _; cases fuel <;> trivial
      | faulted _ => intro _; cases fuel <;> trivial
    | vis e k =>
      rcases e with fk | obs | ⟨req⟩
      · intro _; trivial
      · intro h
        show ConeReach root _ fuel (k PUnit.unit)
        revert h
        show (match k PUnit.unit with
          | .running s' => ClosedInvPoly cone root c₁ ti₁ s'
          | _ => True) → _
        cases k PUnit.unit with
        | running s' => intro h; exact coneReach_of_closedInvTrait h_root h_cone h_impl fuel s' h
        | halted _ => intro _; cases fuel <;> trivial
        | faulted _ => intro _; cases fuel <;> trivial
      · intro _; trivial

/-! ### External Summary Environment & Batched VC Cone Narrowing Certificate (`#cpp_vc_narrow`) -/

/-- External call summary entry associating an external `DefPath` with a deterministic return-value
contract identifier (`summaryTag : Nat`). -/
structure ExternalCallSummary where
  defPath : DefPath
  summaryTag : Nat
  deriving DecidableEq, Repr

abbrev ExternalSummaryEnv := List ExternalCallSummary

/-- Look up the first matching external summary for `dp`. -/
def findExternalSummary? (env : ExternalSummaryEnv) (dp : DefPath) : Option ExternalCallSummary :=
  env.find? (fun s => stringEq s.defPath dp)

/-- `UntrustedAdmissible`: external call summaries are admissible with respect to `callees` when no
external summary shadows an internal linked body in `callees` (`findCallee? callees s.defPath = none`). -/
def checkUntrustedAdmissible (callees : List CapturedMir) (extEnv : ExternalSummaryEnv) : Bool :=
  extEnv.all (fun s => (findCallee? callees s.defPath).isNone)

/-- Decidable agreement of two external summary environments on all definition paths in `cone`. -/
def checkExternalSummariesAgreeOn (cone : List DefPath)
    (ext₁ ext₂ : ExternalSummaryEnv) : Bool :=
  cone.all (fun dp => decide (findExternalSummary? ext₁ dp = findExternalSummary? ext₂ dp))

/-- Decidable first-match `findCallee?` agreement between `c₁` and `c₂` on `cone`. -/
def checkCalleesAgreeOn (cone : List DefPath) (c₁ c₂ : List CapturedMir) : Bool :=
  cone.all (fun dp =>
    match findCallee? c₁ dp, findCallee? c₂ dp with
    | none, none => true
    | some b₁, some b₂ =>
      stringEq b₁.defPath b₂.defPath &&
        decide (b₁.argCount = b₂.argCount) &&
        decide (b₁.typeParamCount = b₂.typeParamCount) &&
        decide (b₁.basicBlocks.length = b₂.basicBlocks.length)
    | _, _ => false)

/-- Decidable check that for every `dp ∈ cone`:
1. every `TraitImplEntry` targeting `dp` in `ti₁ ++ flatMapTraitImpls c₁` has `e.implPath ∈ cone`,
   and
2. `findCallee? c₂ e.implPath` is present (`isSome`, rejecting missing impl bodies). -/
def checkTraitImplConeClosed (cone : List DefPath) (c₁ c₂ : List CapturedMir)
    (ti₁ : List TraitImplEntry) : Bool :=
  let allTi₁ := ti₁ ++ flatMapTraitImpls c₁
  cone.all (fun dp =>
    allTi₁.all (fun e =>
      if stringEq e.traitRef.defPath dp then
        inCone cone e.implPath && (findCallee? c₂ e.implPath).isSome
      else
        true))

theorem traitImplConeClosed_imp {cone : List DefPath} {c₁ c₂ : List CapturedMir}
    {ti₁ : List TraitImplEntry}
    (h : checkTraitImplConeClosed cone c₁ c₂ ti₁ = true) :
    ∀ dp ∈ cone, ∀ e ∈ ti₁ ++ flatMapTraitImpls c₁,
      stringEq e.traitRef.defPath dp = true → e.implPath ∈ cone := by
  intro dp hdp e he hs
  unfold checkTraitImplConeClosed at h
  have h1 := List.all_eq_true.mp h dp hdp
  have h2 := List.all_eq_true.mp h1 e he
  simp only [hs, ↓reduceIte, Bool.and_eq_true] at h2
  exact inCone_iff.mp h2.1

/-- Canonical trait-preserving narrowing of `fullCallees` to `cone`:
- `narrowCallees := stripCalleeTraitImpls (coneBodies cone fullCallees)` (or `coneBodies cone fullCallees`),
- `hoistedExtra := hoistTraitImpls fullCallees extra`. -/
def narrowCalleesWithHoistedTraits (cone : List DefPath) (fullCallees : List CapturedMir)
    (extra : List TraitImplEntry) : List CapturedMir × List TraitImplEntry :=
  (coneBodies cone fullCallees, hoistTraitImpls fullCallees extra)

/-- Single batched VC call-cone + trait-impl + external-summary narrowing certificate checker
(`#cpp_vc_narrow`, `cl/1022801564`):
Checks in one `decide +kernel` invocation:
1. `bodyCallsInConePoly cone rootBody`
2. `(coneBodies cone fullCallees).all (bodyCallsInConePoly cone)`
3. `checkCalleesAgreeOn cone fullCallees narrowCallees`
4. `checkTraitImplConeClosed cone fullCallees narrowCallees extra₁`
5. `checkUntrustedAdmissible fullCallees fullExt` and
   `checkExternalSummariesAgreeOn cone fullExt narrowExt`. -/
def checkBatchedVcConeNarrowCert (cone : List DefPath) (rootBody : CapturedMir)
    (fullCallees narrowCallees : List CapturedMir)
    (extra₁ extra₂ : List TraitImplEntry)
    (fullExt narrowExt : ExternalSummaryEnv := []) : Bool :=
  bodyCallsInConePoly cone rootBody &&
    (coneBodies cone fullCallees).all (bodyCallsInConePoly cone) &&
    checkCalleesAgreeOn cone fullCallees narrowCallees &&
    checkTraitImplConeClosed cone fullCallees narrowCallees extra₁ &&
    cone.all (fun dp =>
      listEqBy traitImplEntryEq
        ((extra₁ ++ flatMapTraitImpls fullCallees).filter (fun e => stringEq e.traitRef.defPath dp))
        ((extra₂ ++ flatMapTraitImpls narrowCallees).filter (fun e => stringEq e.traitRef.defPath dp))) &&
    checkUntrustedAdmissible fullCallees fullExt &&
    checkExternalSummariesAgreeOn cone fullExt narrowExt

/-- Propositional batched VC narrowing certificate combining `checkBatchedVcConeNarrowCert = true`
with `TraitConeAgreeOn cone fullCallees narrowCallees extra₁ extra₂`. For the canonical
`(stripCalleeTraitImpls (coneBodies cone fullCallees), hoistTraitImpls fullCallees extra₁)` or
`(coneBodies cone fullCallees, extra₁)` when hoisted, `TraitConeAgreeOn` is discharged
automatically by `traitConeAgreeOn_of_batchedCert`. -/
structure BatchedVcConeNarrowCert (cone : List DefPath) (rootBody : CapturedMir)
    (fullCallees narrowCallees : List CapturedMir)
    (extra₁ extra₂ : List TraitImplEntry)
    (fullExt narrowExt : ExternalSummaryEnv := []) : Prop where
  certOk :
    checkBatchedVcConeNarrowCert cone rootBody fullCallees narrowCallees
      extra₁ extra₂ fullExt narrowExt = true
  calleesAgree : calleesAgreeOn cone fullCallees narrowCallees
  traitFilterAgree :
    ∀ dp ∈ cone,
      (extra₁ ++ flatMapTraitImpls fullCallees).filter (fun e => stringEq e.traitRef.defPath dp) =
        (extra₂ ++ flatMapTraitImpls narrowCallees).filter (fun e => stringEq e.traitRef.defPath dp)

theorem BatchedVcConeNarrowCert.rootInCone {cone : List DefPath} {rootBody : CapturedMir}
    {fullCallees narrowCallees : List CapturedMir} {extra₁ extra₂ : List TraitImplEntry}
    {fullExt narrowExt : ExternalSummaryEnv}
    (h : BatchedVcConeNarrowCert cone rootBody fullCallees narrowCallees extra₁ extra₂ fullExt narrowExt) :
    bodyCallsInConePoly cone rootBody = true := by
  have hc := h.certOk
  unfold checkBatchedVcConeNarrowCert at hc
  simp only [Bool.and_eq_true] at hc
  exact hc.1.1.1.1.1.1

theorem BatchedVcConeNarrowCert.coneBodiesInCone {cone : List DefPath} {rootBody : CapturedMir}
    {fullCallees narrowCallees : List CapturedMir} {extra₁ extra₂ : List TraitImplEntry}
    {fullExt narrowExt : ExternalSummaryEnv}
    (h : BatchedVcConeNarrowCert cone rootBody fullCallees narrowCallees extra₁ extra₂ fullExt narrowExt) :
    (coneBodies cone fullCallees).all (bodyCallsInConePoly cone) = true := by
  have hc := h.certOk
  unfold checkBatchedVcConeNarrowCert at hc
  simp only [Bool.and_eq_true] at hc
  exact hc.1.1.1.1.1.2

theorem BatchedVcConeNarrowCert.traitImplsInCone {cone : List DefPath} {rootBody : CapturedMir}
    {fullCallees narrowCallees : List CapturedMir} {extra₁ extra₂ : List TraitImplEntry}
    {fullExt narrowExt : ExternalSummaryEnv}
    (h : BatchedVcConeNarrowCert cone rootBody fullCallees narrowCallees extra₁ extra₂ fullExt narrowExt) :
    ∀ dp ∈ cone, ∀ e ∈ extra₁ ++ flatMapTraitImpls fullCallees,
      stringEq e.traitRef.defPath dp = true → e.implPath ∈ cone := by
  have hc := h.certOk
  unfold checkBatchedVcConeNarrowCert at hc
  simp only [Bool.and_eq_true] at hc
  exact traitImplConeClosed_imp hc.1.1.1.2

theorem BatchedVcConeNarrowCert.toTraitConeAgreeOn {cone : List DefPath} {rootBody : CapturedMir}
    {fullCallees narrowCallees : List CapturedMir} {extra₁ extra₂ : List TraitImplEntry}
    {fullExt narrowExt : ExternalSummaryEnv}
    (h : BatchedVcConeNarrowCert cone rootBody fullCallees narrowCallees extra₁ extra₂ fullExt narrowExt) :
    TraitConeAgreeOn cone fullCallees narrowCallees extra₁ extra₂ :=
  ⟨h.calleesAgree, h.traitFilterAgree, h.traitImplsInCone⟩

theorem BatchedVcConeNarrowCert.untrustedAdmissible {cone : List DefPath} {rootBody : CapturedMir}
    {fullCallees narrowCallees : List CapturedMir} {extra₁ extra₂ : List TraitImplEntry}
    {fullExt narrowExt : ExternalSummaryEnv}
    (h : BatchedVcConeNarrowCert cone rootBody fullCallees narrowCallees extra₁ extra₂ fullExt narrowExt) :
    checkUntrustedAdmissible fullCallees fullExt = true ∧
      checkExternalSummariesAgreeOn cone fullExt narrowExt = true := by
  have hc := h.certOk
  unfold checkBatchedVcConeNarrowCert at hc
  simp only [Bool.and_eq_true] at hc
  exact ⟨hc.1.2, hc.2⟩

/-- `lookupCallee` equivalence from a `BatchedVcConeNarrowCert`. -/
theorem lookupCallee_eq_of_batchedCert {cone : List DefPath} {rootBody : CapturedMir}
    {fullCallees narrowCallees : List CapturedMir} {extra₁ extra₂ : List TraitImplEntry}
    {fullExt narrowExt : ExternalSummaryEnv}
    (h : BatchedVcConeNarrowCert cone rootBody fullCallees narrowCallees extra₁ extra₂ fullExt narrowExt)
    (layouts : LayoutTable) {dp : DefPath} (h_dp : dp ∈ cone) (typeArgs : List RigidTy) :
    lookupCallee fullCallees layouts dp typeArgs extra₁ =
      lookupCallee narrowCallees layouts dp typeArgs extra₂ :=
  lookupCallee_eq_of_traitConeAgreeOn layouts typeArgs h.toTraitConeAgreeOn h_dp

/-- **Core Bounded Execution Narrowing Theorem (`runMirExecBounded_narrow_of_batchedCert`)**:
A single `BatchedVcConeNarrowCert` narrows `(fullCallees, extra₁)` to `(narrowCallees, extra₂)`
across `runMirExecBounded` for any fuel and any entry state with `s.memory.callees = fullCallees`,
`s.memory.traitImpls = extra₁`, `s.memory.activeCallee = none`, and `s.memory.callStack = []`. -/
theorem runMirExecBounded_narrow_of_batchedCert {cone : List DefPath} {rootBody : CapturedMir}
    {fullCallees narrowCallees : List CapturedMir} {extra₁ extra₂ : List TraitImplEntry}
    {fullExt narrowExt : ExternalSummaryEnv}
    (h_cert : BatchedVcConeNarrowCert cone rootBody fullCallees narrowCallees
      extra₁ extra₂ fullExt narrowExt)
    (fuel : Nat) (s : MachineState)
    (h_callees : s.memory.callees = fullCallees)
    (h_traits : s.memory.traitImpls = extra₁)
    (h_ac : s.memory.activeCallee = none)
    (h_cs : s.memory.callStack = []) :
    runMirExecBounded fuel rootBody
        (.running (MachineState.mapMem (Memory.withCalleesAndTraits narrowCallees extra₂) s)) =
      (runMirExecBounded fuel rootBody (.running s)).map
        (MirOutcome.mapMem (Memory.withCalleesAndTraits narrowCallees extra₂)) := by
  have h_inv : ClosedInvPoly cone rootBody fullCallees extra₁ s := by
    refine ⟨h_callees, h_traits, ?_, ?_⟩
    · rw [h_ac]; exact Or.inl rfl
    · intro f hf; rw [h_cs] at hf; nomatch hf
  have h_reach := coneReach_of_closedInvTrait h_cert.rootInCone h_cert.coneBodiesInCone
    h_cert.traitImplsInCone fuel s h_inv
  have h_at : TraitAgreesAt cone narrowCallees extra₂ (.running s) := by
    intro s' hs'
    cases hs'
    rw [h_callees, h_traits]
    exact h_cert.toTraitConeAgreeOn
  exact runMirExecBounded_trait_cone_narrow cone rootBody narrowCallees extra₂ fuel
    (.running s) h_reach h_at

/-- **Core Symbolic WP Narrowing Theorem (`wpMirExecSym_narrow_of_batchedCert`)**:
Under `BatchedVcConeNarrowCert`, `wpMirExecSym` in the narrowed `(narrowCallees, extra₂)`
environment is logically equivalent (`↔`) to `wpMirExecSym` in `(fullCallees, extra₁)` for any
postcondition invariant under `Memory.withCalleesAndTraits narrowCallees extra₂`. -/
theorem wpMirExecSym_narrow_of_batchedCert {cone : List DefPath} {rootBody : CapturedMir}
    {fullCallees narrowCallees : List CapturedMir} {extra₁ extra₂ : List TraitImplEntry}
    {fullExt narrowExt : ExternalSummaryEnv}
    (h_cert : BatchedVcConeNarrowCert cone rootBody fullCallees narrowCallees
      extra₁ extra₂ fullExt narrowExt)
    (fuel : Nat) (s : MachineState)
    (h_callees : s.memory.callees = fullCallees)
    (h_traits : s.memory.traitImpls = extra₁)
    (h_ac : s.memory.activeCallee = none)
    (h_cs : s.memory.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirOutcome.mapMem (Memory.withCalleesAndTraits narrowCallees extra₂) out) ↔ post out) :
    wpMirExecSym fuel rootBody
        (.running (MachineState.mapMem (Memory.withCalleesAndTraits narrowCallees extra₂) s))
        post ↔
      wpMirExecSym fuel rootBody (.running s) post := by
  have h_inv : ClosedInvPoly cone rootBody fullCallees extra₁ s := by
    refine ⟨h_callees, h_traits, ?_, ?_⟩
    · rw [h_ac]; exact Or.inl rfl
    · intro f hf; rw [h_cs] at hf; nomatch hf
  have h_reach := coneReach_of_closedInvTrait h_cert.rootInCone h_cert.coneBodiesInCone
    h_cert.traitImplsInCone fuel s h_inv
  have h_at : TraitAgreesAt cone narrowCallees extra₂ (.running s) := by
    intro s' hs'
    cases hs'
    rw [h_callees, h_traits]
    exact h_cert.toTraitConeAgreeOn
  exact wpMirExecSym_trait_cone_narrow cone rootBody narrowCallees extra₂ post h_post fuel
    (.running s) h_reach h_at

/-- Verification Condition wrapper (`vcMirWithCallees`) pairing `wpMirExecSym` with external
summary environment lookup on `cone`. -/
def vcMirWithCallees (fuel : Nat) (rootBody : CapturedMir) (s : MachineState)
    (callees : List CapturedMir) (traitImpls : List TraitImplEntry)
    (extEnv : ExternalSummaryEnv) (cone : List DefPath) (post : MirOutcome → Prop) : Prop :=
  wpMirExecSym fuel rootBody
      (.running (MachineState.mapMem (Memory.withCalleesAndTraits callees traitImpls) s)) post ∧
    ∀ dp ∈ cone, (findCallee? callees dp).isNone = true →
      findExternalSummary? extEnv dp = findExternalSummary? extEnv dp

/-- **Combined VC + External-Summary Narrowing Theorem (`vcMirWithCallees_narrow_of_batchedCert`)**:
Narrows both `(fullCallees, extra₁)` and `fullExt` to `(narrowCallees, extra₂)` and `narrowExt` in
one `BatchedVcConeNarrowCert` step, plus proves that `findExternalSummary? fullExt dp =
findExternalSummary? narrowExt dp` for every `dp ∈ cone` and no external summary in `fullExt`
shadows an internal callee. -/
theorem vcMirWithCallees_narrow_of_batchedCert {cone : List DefPath} {rootBody : CapturedMir}
    {fullCallees narrowCallees : List CapturedMir} {extra₁ extra₂ : List TraitImplEntry}
    {fullExt narrowExt : ExternalSummaryEnv}
    (h_cert : BatchedVcConeNarrowCert cone rootBody fullCallees narrowCallees
      extra₁ extra₂ fullExt narrowExt)
    (fuel : Nat) (s : MachineState)
    (h_callees : s.memory.callees = fullCallees)
    (h_traits : s.memory.traitImpls = extra₁)
    (h_ac : s.memory.activeCallee = none)
    (h_cs : s.memory.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirOutcome.mapMem (Memory.withCalleesAndTraits narrowCallees extra₂) out) ↔ post out) :
    (vcMirWithCallees fuel rootBody s narrowCallees extra₂ narrowExt cone post ↔
      vcMirWithCallees fuel rootBody s fullCallees extra₁ fullExt cone post) ∧
    (∀ dp ∈ cone, findExternalSummary? fullExt dp = findExternalSummary? narrowExt dp) ∧
    (∀ ext ∈ fullExt, findCallee? fullCallees ext.defPath = none) := by
  have h_self : MachineState.mapMem (Memory.withCalleesAndTraits fullCallees extra₁) s = s := by
    cases s with
    | mk frame mem =>
      dsimp only [MachineState.mapMem, Memory.withCalleesAndTraits] at h_callees h_traits ⊢
      cases mem
      dsimp only at h_callees h_traits
      subst h_callees h_traits
      rfl
  have h_wp := wpMirExecSym_narrow_of_batchedCert h_cert fuel s h_callees h_traits h_ac h_cs
    post h_post
  obtain ⟨h_adm, h_ext_ag⟩ := h_cert.untrustedAdmissible
  refine ⟨?_, ?_, ?_⟩
  · unfold vcMirWithCallees
    rw [h_self]
    exact ⟨fun ⟨hw, _⟩ => ⟨h_wp.mp hw, fun _ _ _ => rfl⟩,
      fun ⟨hw, _⟩ => ⟨h_wp.mpr hw, fun _ _ _ => rfl⟩⟩
  · intro dp hdp
    unfold checkExternalSummariesAgreeOn at h_ext_ag
    exact of_decide_eq_true (List.all_eq_true.mp h_ext_ag dp hdp)
  · intro ext hext
    unfold checkUntrustedAdmissible at h_adm
    exact Option.isNone_iff_eq_none.mp (List.all_eq_true.mp h_adm ext hext)

/-! ### Non-Reducible Value-to-Storage Coercion (`@[irreducible] coerceValueAt`, `cl/1022801564`) -/

/-- Compute the byte width of an unsigned integer type under `layouts`. -/
def uintTyByteWidth (layouts : LayoutTable) : UintTy → Nat
  | .u8 => 1
  | .u16 => 2
  | .u32 => 4
  | .u64 => 8
  | .u128 => 16
  | .usize => layoutPointerBytes layouts

/-- Compute the byte width of a signed integer type under `layouts`. -/
def intTyByteWidth (layouts : LayoutTable) : IntTy → Nat
  | .i8 => 1
  | .i16 => 2
  | .i32 => 4
  | .i64 => 8
  | .i128 => 16
  | .isize => layoutPointerBytes layouts

/-- Non-reducible value-to-storage coercion (`@[irreducible] coerceValueAt`, inspired by
`bensherman`'s `Cpp.Exec.coerceAt` in `cl/1022801564`): validates and canonicalizes a runtime
`Value` at target type `ty` without allowing `whnf` / `isDefEq` to unfold layout-table and
bit-wrapping case splits during symbolic VC generation. -/
@[irreducible]
def coerceValueAt (layouts : LayoutTable) (ty : RigidTy) (v : Value) : Option Value :=
  match ty with
  | .bool =>
    match v with
    | .scalar sc =>
      match sc.sizeBytes == 1 && (sc.bits == 0 || sc.bits == 1) with
      | true => some (.scalar sc)
      | false => none
    | .unit | .ptr _ _ | .aggregate _ _ => none
  | .int it =>
    match v with
    | .scalar sc =>
      let w := intTyByteWidth layouts it
      match sc.sizeBytes == w with
      | true => some (.scalar ⟨wrapScalarBits sc.bits (scalarModulus w), w⟩)
      | false => none
    | .unit | .ptr _ _ | .aggregate _ _ => none
  | .uint ut =>
    match v with
    | .scalar sc =>
      let w := uintTyByteWidth layouts ut
      match sc.sizeBytes == w with
      | true => some (.scalar ⟨wrapScalarBits sc.bits (scalarModulus w), w⟩)
      | false => none
    | .unit | .ptr _ _ | .aggregate _ _ => none
  | .tuple tys =>
    match v with
    | .unit =>
      match tys with
      | [] => some .unit
      | _ :: _ => none
    | .aggregate vIdx fields =>
      match tys with
      | [] => none
      | _ :: _ =>
        match vIdx with
        | 0 => some (.aggregate 0 fields)
        | _ + 1 => none
    | .scalar _ | .ptr _ _ => none
  | .ref _ _ =>
    match v with
    | .ptr ptrVal sz =>
      match sz == layoutPointerBytes layouts with
      | true => some (.ptr ptrVal sz)
      | false => none
    | .unit | .scalar _ | .aggregate _ _ => none
  | .rawPtr _ _ =>
    match v with
    | .ptr ptrVal sz =>
      match sz == layoutPointerBytes layouts with
      | true => some (.ptr ptrVal sz)
      | false => none
    | .unit | .scalar _ | .aggregate _ _ => none
  | .adt _ _ =>
    match v with
    | .aggregate vIdx fields => some (.aggregate vIdx fields)
    | .unit | .scalar _ | .ptr _ _ => none
  | .param _ _ | .alias _ _ | .char | .float _ | .never | .str
  | .array _ _ | .slice _ | .fnDef _ _ | .fnPtr _ _ _ _ | .closure _ _
  | .dynamic _ | .foreign _ | .other _ => none

/-- Targeted rewrite lemma for `coerceValueAt` at `.uint .u32`. -/
theorem coerceValueAt_u32 (layouts : LayoutTable) (bits : Nat) :
    coerceValueAt layouts (.uint .u32) (.scalar ⟨bits, 4⟩) =
      some (.scalar ⟨wrapScalarBits bits (scalarModulus 4), 4⟩) := by
  with_unfolding_all rfl

/-- Targeted rewrite lemma for `coerceValueAt` at `.bool`. -/
theorem coerceValueAt_bool (layouts : LayoutTable) (b : Bool) :
    coerceValueAt layouts .bool (.scalar (boolToScalar b)) =
      some (.scalar (boolToScalar b)) := by
  cases b <;> with_unfolding_all rfl

/-- Targeted rewrite lemma for `coerceValueAt` at thin references `.ref mutab pointee`. -/
theorem coerceValueAt_ref (layouts : LayoutTable) (mutab : Mutability) (pointee : RigidTy)
    (ptrVal : ProvenancePtr) :
    coerceValueAt layouts (.ref mutab pointee) (.ptr ptrVal (layoutPointerBytes layouts)) =
      some (.ptr ptrVal (layoutPointerBytes layouts)) := by
  delta coerceValueAt
  dsimp only
  rw [nat_beq_self]

/-- Targeted rewrite lemma for `coerceValueAt` at `.adt defPath args`. -/
theorem coerceValueAt_adt_exact (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy)
    (vIdx : VariantIdx) (fields : List Value) :
    coerceValueAt layouts (.adt defPath args) (.aggregate vIdx fields) =
      some (.aggregate vIdx fields) := by
  with_unfolding_all rfl

/-- Idempotence of `coerceValueAt` across all supported types and values (`0` `Classical.choice`). -/
theorem coerceValueAt_idempotent (layouts : LayoutTable) (ty : RigidTy) (v v' : Value)
    (h : coerceValueAt layouts ty v = some v') :
    coerceValueAt layouts ty v' = some v' := by
  delta coerceValueAt at h ⊢
  cases ty <;> cases v <;> try contradiction
  · rename_i sc
    dsimp only at h
    cases hcond : (sc.sizeBytes == 1 && (sc.bits == 0 || sc.bits == 1)) with
    | false => rw [hcond] at h; nomatch h
    | true =>
      rw [hcond] at h
      cases h
      dsimp only
      rw [hcond]
  · rename_i it sc
    dsimp only at h
    cases hsz : sc.sizeBytes == intTyByteWidth layouts it with
    | false => rw [hsz] at h; nomatch h
    | true =>
      rw [hsz] at h
      cases h
      dsimp only
      rw [nat_beq_self]
      have hmod : wrapScalarBits (wrapScalarBits sc.bits (scalarModulus (intTyByteWidth layouts it)))
          (scalarModulus (intTyByteWidth layouts it)) =
          wrapScalarBits sc.bits (scalarModulus (intTyByteWidth layouts it)) := by
        rw [wrapScalarBits_eq_mod_modulus, wrapScalarBits_eq_mod_modulus, Nat.mod_mod]
      rw [hmod]
  · rename_i ut sc
    dsimp only at h
    cases hsz : sc.sizeBytes == uintTyByteWidth layouts ut with
    | false => rw [hsz] at h; nomatch h
    | true =>
      rw [hsz] at h
      cases h
      dsimp only
      rw [nat_beq_self]
      have hmod : wrapScalarBits (wrapScalarBits sc.bits (scalarModulus (uintTyByteWidth layouts ut)))
          (scalarModulus (uintTyByteWidth layouts ut)) =
          wrapScalarBits sc.bits (scalarModulus (uintTyByteWidth layouts ut)) := by
        rw [wrapScalarBits_eq_mod_modulus, wrapScalarBits_eq_mod_modulus, Nat.mod_mod]
      rw [hmod]
  · rename_i tys
    dsimp only at h
    cases tys with
    | nil => cases h; rfl
    | cons _ _ => nomatch h
  · rename_i tys vIdx fields
    dsimp only at h
    cases tys with
    | nil => nomatch h
    | cons _ _ =>
      dsimp only at h
      cases vIdx with
      | zero => cases h; rfl
      | succ _ => nomatch h
  · rename_i m pt ptrVal sz
    dsimp only at h
    cases hsz : sz == layoutPointerBytes layouts with
    | false => rw [hsz] at h; nomatch h
    | true =>
      rw [hsz] at h
      cases h
      dsimp only
      rw [hsz]
  · rename_i m pt ptrVal sz
    dsimp only at h
    cases hsz : sz == layoutPointerBytes layouts with
    | false => rw [hsz] at h; nomatch h
    | true =>
      rw [hsz] at h
      cases h
      dsimp only
      rw [hsz]
  · rename_i dp args vIdx fields
    dsimp only at h
    cases h
    rfl

/-! ### Trait-Dispatch & Negative Narrowing Canaries (`canary_naiveNarrow_breaks_trait_dispatch`) -/

/-- Standard 4-byte `u32` primitive layout (`layoutIdx = 0`). -/
def protoU32Layout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- Standard 1-byte `bool` layout (`layoutIdx = 1`). -/
def protoBoolLayout : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- Prototype `LayoutTable` with `u32` at `0` and `bool` at `1`. -/
def protoLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [protoU32Layout, protoBoolLayout] }

def protoU32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
def protoBoolTy : Ty := { kind := .bool, layoutIdx := 1 }
def protoCircleTy : RigidTy := .adt "proto::Circle" []

def protoRetU32Abi : FnAbi :=
  { args := [], ret := ⟨protoU32Layout, .direct⟩, conv := .rust, canUnwind := true }

def protoU32Const (n : Nat) : Operand :=
  .constant ⟨protoU32Ty, .scalar (.int ⟨n, 4⟩)⟩

def protoBoolConst (b : Bool) : Operand :=
  .constant ⟨protoBoolTy, .scalar (.int ⟨if b then 1 else 0, 1⟩)⟩

def protoFnConst (dp : DefPath) (targs : List RigidTy := []) : Operand :=
  .constant ⟨⟨.fnDef dp targs, 0⟩, .zeroSized⟩

/-- Construct a leaf `CapturedMir` body returning `retVal : u32` (`_0 = const retVal; return`). -/
def protoLeaf (dp : DefPath) (retVal : Nat) (typeParamCount : Nat := 0)
    (traitImpls : List TraitImplEntry := []) : CapturedMir :=
  { defPath := dp
    phase := .runtimePostCleanup
    role := .subject
    argCount := 0
    localDecls := [⟨.mut, protoU32Ty, some "_0"⟩]
    basicBlocks := [
      { statements := [⟨.assign ⟨0, []⟩ (.use (protoU32Const retVal)), "leaf:assign"⟩]
        terminator := ⟨.return_, "leaf:ret"⟩
        isCleanup := false }
    ]
    fnAbi := protoRetU32Abi
    layouts := protoLayouts
    allocations := []
    typeParamCount := typeParamCount
    traitImpls := traitImpls }

/-- `TraitImplEntry` registering `<Circle as Area>::area` -> `"proto::<impl Area for Circle>::area"`. -/
def protoAreaEntry : TraitImplEntry :=
  { traitRef := { defPath := "proto::Area::area", args := [protoCircleTy] }
    implPath := "proto::<impl Area for Circle>::area" }

/-- Concrete implementation body `fn <impl Area for Circle>::area() -> u32 { 31 }`. -/
def protoCircleArea : CapturedMir :=
  protoLeaf "proto::<impl Area for Circle>::area" 31 0 []

/-- Uncalled `impl Area for Circle` carrier body that holds `protoAreaEntry` in `c.traitImpls`. -/
def protoAreaImplHolder : CapturedMir :=
  protoLeaf "proto::<impl Area for Circle>" 0 0 [protoAreaEntry]

/-- Polymorphic helper `fn poly<T>() -> u32 { 7 }` (`typeParamCount = 1`). -/
def protoPoly : CapturedMir :=
  protoLeaf "proto::poly" 7 1 []

/-- Unrelated filler callees outside the call cone. -/
def protoFillerA : CapturedMir := protoLeaf "proto::filler_a" 100 0 []
def protoFillerB : CapturedMir := protoLeaf "proto::filler_b" 200 0 []
def protoGDead : CapturedMir := protoLeaf "proto::g_dead" 999 0 []

/-- Call block `_0 = dp::<targs>() -> nextBb`. -/
def protoCallBlock (dp : DefPath) (targs : List RigidTy) (nextBb : BasicBlockIdx) :
    BasicBlockData :=
  { statements := []
    terminator := ⟨.call (protoFnConst dp targs) [] ⟨0, []⟩ (some nextBb) .continue_, "call"⟩
    isCleanup := false }

/-- Root MIR body calling `poly::<u32>()` followed by `<Circle as Area>::area()`. -/
def traitCallRootMir : CapturedMir :=
  { defPath := "proto::trait_root"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 0
    localDecls := [⟨.mut, protoU32Ty, some "_0"⟩]
    basicBlocks := [
      protoCallBlock "proto::poly" [.uint .u32] 1,
      protoCallBlock "proto::Area::area" [protoCircleTy] 2,
      { statements := [], terminator := ⟨.return_, "ret"⟩, isCleanup := false }
    ]
    fnAbi := protoRetU32Abi
    layouts := protoLayouts
    allocations := [] }

/-- Full callee table containing fillers, `protoPoly`, the uncalled `protoAreaImplHolder`, and
`protoCircleArea`. -/
def protoFullCallees : List CapturedMir :=
  [protoFillerA, protoGDead, protoPoly, protoAreaImplHolder, protoFillerB, protoCircleArea]

/-- Call cone of `traitCallRootMir` (including the trait method `"proto::Area::area"` and its
resolved impl target `"proto::<impl Area for Circle>::area"`, but NOT the uncalled carrier
`"proto::<impl Area for Circle>"`). -/
def protoTraitCone : List DefPath :=
  ["proto::poly", "proto::Area::area", "proto::<impl Area for Circle>::area"]

/-- Naive `DefPath`-only cone narrowing (`MirLiftCore.coneBodies protoTraitCone protoFullCallees`),
which drops `protoAreaImplHolder` and loses `protoAreaEntry`! -/
def protoNaiveNarrowCallees : List CapturedMir :=
  coneBodies protoTraitCone protoFullCallees

/-- Trait-preserving narrowed callees (`stripCalleeTraitImpls protoNaiveNarrowCallees`) paired
with `hoistTraitImpls protoFullCallees []`. -/
def protoHoistedExtra : List TraitImplEntry :=
  hoistTraitImpls protoFullCallees []

/-- **Canary 1 (`canary_naiveNarrow_breaks_trait_dispatch`)**:
1. In `protoFullCallees`, `lookupCallee` resolves `Area::area::<Circle>` to `some protoCircleArea`
   and `runMirExecBounded 12 traitCallRootMir` halts normally with `31 : u32`.
2. Naive `DefPath` cone narrowing (`protoNaiveNarrowCallees` without `hoistTraitImpls`) drops the
   uncalled `protoAreaImplHolder` body, so `lookupCallee` returns `none` and `runMirExecBounded`
   stalls (`= none`) on an unlinked external call.
3. `MirLiftCore.CallConeClosedPoly` fails closed (`= false`) on `traitCallRootMir` because
   `"proto::Area::area"` has a registered `TraitImplEntry`. -/
theorem canary_naiveNarrow_breaks_trait_dispatch :
    lookupCallee protoFullCallees protoLayouts "proto::Area::area" [protoCircleTy] [] =
      some protoCircleArea ∧
    lookupCallee protoNaiveNarrowCallees protoLayouts "proto::Area::area" [protoCircleTy] [] =
      none ∧
    ((runMirExecBounded 12 traitCallRootMir
        (.running (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir []
          emptyMemory protoFullCallees))).map
      (fun out => match out with | .normal (v, _) => some v | _ => none)) =
      some (some (Value.scalar ⟨31, 4⟩)) ∧
    runMirExecBounded 12 traitCallRootMir
      (.running (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir []
        emptyMemory protoNaiveNarrowCallees)) = none ∧
    CallConeClosedPoly protoTraitCone traitCallRootMir protoFullCallees [] = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Constructive certificate proof that `protoTraitCone`, `protoFullCallees`, and
`(protoNaiveNarrowCallees, protoHoistedExtra)` satisfy `BatchedVcConeNarrowCert`. -/
theorem protoTraitBatchedCert :
    BatchedVcConeNarrowCert protoTraitCone traitCallRootMir
      protoFullCallees protoNaiveNarrowCallees [] protoHoistedExtra [] [] where
  certOk := by decide +kernel
  calleesAgree := calleesAgreeOn_coneBodies protoTraitCone protoFullCallees
  traitFilterAgree := by
    intro dp hdp
    simp only [protoTraitCone, List.mem_cons, List.not_mem_nil, or_false] at hdp
    rcases hdp with rfl | rfl | rfl <;> rfl

/-- **Canary 2 (`canary_traitDispatch_preserved_under_batchedVcNarrow`)**:
`BatchedVcConeNarrowCert` + `hoistTraitImpls` accepts `traitCallRootMir` (`checkBatchedVcConeNarrowCert = true`)
and proves that narrowing `(protoFullCallees, [])` to `(protoNaiveNarrowCallees, protoHoistedExtra)`
preserves both `runMirExecBounded` and `wpMirExecSym` (`31 : u32`). -/
theorem canary_traitDispatch_preserved_under_batchedVcNarrow :
    checkBatchedVcConeNarrowCert protoTraitCone traitCallRootMir
      protoFullCallees protoNaiveNarrowCallees [] protoHoistedExtra [] [] = true ∧
    (wpMirExecSym 12 traitCallRootMir
      (.running (MachineState.mapMem
        (Memory.withCalleesAndTraits protoNaiveNarrowCallees protoHoistedExtra)
        (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir [] emptyMemory protoFullCallees)))
      (fun out => match out with | .normal (v, _) => v = Value.scalar ⟨31, 4⟩ | _ => False) ↔
    wpMirExecSym 12 traitCallRootMir
      (.running (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir []
        emptyMemory protoFullCallees))
      (fun out => match out with | .normal (v, _) => v = Value.scalar ⟨31, 4⟩ | _ => False)) := by
  refine ⟨protoTraitBatchedCert.certOk, ?_⟩
  exact wpMirExecSym_narrow_of_batchedCert protoTraitBatchedCert 12
    (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir [] emptyMemory protoFullCallees)
    rfl rfl rfl rfl
    (fun out => match out with | .normal (v, _) => v = Value.scalar ⟨31, 4⟩ | _ => False)
    (fun out => by rcases out with ⟨v, m⟩ | _ | _ <;> exact Iff.rfl)

/-- Negative Canary 1: duplicate callee shadowing mismatch (`fullCallees` has `[v1, v2]` where `v1`
has 1 block and `v2` has 2 blocks, while `narrowCallees` drops `v1` and exposes shadowed `v2`) is
rejected by `checkBatchedVcConeNarrowCert`. -/
def protoDupShadowV2 : CapturedMir :=
  { protoLeaf "proto::poly" 7 1 [] with
    basicBlocks := [
      { statements := [], terminator := ⟨.goto 1, "g"⟩, isCleanup := false },
      { statements := [⟨.assign ⟨0, []⟩ (.use (protoU32Const 99)), "a"⟩],
        terminator := ⟨.return_, "r"⟩, isCleanup := false }
    ] }

theorem canary_duplicateShadow_rejected :
    checkBatchedVcConeNarrowCert protoTraitCone traitCallRootMir
      (protoPoly :: protoDupShadowV2 :: protoFullCallees)
      [protoDupShadowV2, protoCircleArea] [] protoHoistedExtra [] [] = false := by
  decide +kernel

/-- Negative Canary 2: external summary shadowing an internal callee in `fullCallees` violates
`checkUntrustedAdmissible` and is rejected by `checkBatchedVcConeNarrowCert`. -/
theorem canary_externalShadowsInternal_rejected :
    checkBatchedVcConeNarrowCert protoTraitCone traitCallRootMir
      protoFullCallees protoNaiveNarrowCallees [] protoHoistedExtra
      [⟨"proto::poly", 1⟩] [⟨"proto::poly", 1⟩] = false := by
  decide +kernel

/-- Negative Canary 3: omitting the `TraitImplEntry.implPath` target body (`protoCircleArea`) from
`narrowCallees` is rejected by `checkBatchedVcConeNarrowCert`. -/
theorem canary_missingTraitImplBody_rejected :
    checkBatchedVcConeNarrowCert protoTraitCone traitCallRootMir
      protoFullCallees [protoPoly] [] protoHoistedExtra [] [] = false := by
  decide +kernel

/-! ## Part C: `DemandCallerLocationEnv` (`proofs-rs/lean-miri` PR #67 Schema 15) -/

/-- Exact source-map expansion position exported by Schema 15 (`lean-miri#67`). -/
structure SourceExpansionPos where
  fileSymbol : String
  fileBytes : List UInt8
  line : UInt32
  column : UInt32
  deriving DecidableEq, Repr

/-- `-Zlocation-detail` redaction policy (`file`, `line`, `column` booleans — 8 combinations). -/
structure LocationDetailPolicy where
  file : Bool := true
  line : Bool := true
  column : Bool := true
  deriving DecidableEq, Repr

/-- Exhaustive enumeration of all 8 `LocationDetailPolicy` combinations. -/
def allLocationDetailPolicies : List LocationDetailPolicy :=
  [ ⟨false, false, false⟩, ⟨false, false, true⟩, ⟨false, true, false⟩, ⟨false, true, true⟩,
    ⟨true, false, false⟩, ⟨true, false, true⟩, ⟨true, true, false⟩, ⟨true, true, true⟩ ]

theorem allLocationDetailPolicies_length : allLocationDetailPolicies.length = 8 := rfl

theorem mem_allLocationDetailPolicies (p : LocationDetailPolicy) :
    p ∈ allLocationDetailPolicies := by
  rcases p with ⟨f, l, c⟩
  cases f <;> cases l <;> cases c <;> decide

/-- UTF-8 byte sequence of `"<redacted>"` used when `policy.file = false`. -/
def redactedFileBytes : List UInt8 :=
  [60, 114, 101, 100, 97, 99, 116, 101, 100, 62]

/-- Apply a `-Zlocation-detail` redaction policy to a `SourceExpansionPos`:
disabled `file` redacts to `"<redacted>"` (`redactedFileBytes`), and disabled `line`/`column`
redact to `0`. -/
def applyLocationDetailPolicy (pol : LocationDetailPolicy) (pos : SourceExpansionPos) :
    SourceExpansionPos :=
  { fileSymbol := if pol.file then pos.fileSymbol else "<redacted>"
    fileBytes := if pol.file then pos.fileBytes else redactedFileBytes
    line := if pol.line then pos.line else 0
    column := if pol.column then pos.column else 0 }

theorem applyLocationDetailPolicy_idempotent (pol : LocationDetailPolicy)
    (pos : SourceExpansionPos) :
    applyLocationDetailPolicy pol (applyLocationDetailPolicy pol pos) =
      applyLocationDetailPolicy pol pos := by
  unfold applyLocationDetailPolicy
  cases pol.file <;> cases pol.line <;> cases pol.column <;> rfl

/-- Per-frame caller-location metadata (`FrameLocMeta`):
- `defPath`: frame function identity,
- `callSitePos`: source position of the call site in the caller that invoked this frame,
- `isTrackCaller`: whether this frame carries `#[track_caller]`,
- `detailPolicy`: active `-Zlocation-detail` policy. -/
structure FrameLocMeta where
  defPath : DefPath
  callSitePos : SourceExpansionPos
  isTrackCaller : Bool
  detailPolicy : LocationDetailPolicy := {}
  deriving DecidableEq, Repr

/-- Bottom-up stack walk (`Miri/Interpreter/VirtualCalls.lean:168-198` `caller_location_span`):
given the call stack from innermost active frame outward (`active :: callers`), walks outward
across `isTrackCaller = true` frames and returns the `callSitePos` of the outermost consecutive
`#[track_caller]` frame (redacted under `active.detailPolicy`). -/
def resolveTrackCallerWalkUpAux (pol : LocationDetailPolicy)
    (curPos : SourceExpansionPos) : List FrameLocMeta → SourceExpansionPos
  | [] => applyLocationDetailPolicy pol curPos
  | f :: rest =>
    if f.isTrackCaller then
      resolveTrackCallerWalkUpAux pol f.callSitePos rest
    else
      applyLocationDetailPolicy pol curPos

def resolveTrackCallerStack (active : FrameLocMeta) (callers : List FrameLocMeta) :
    SourceExpansionPos :=
  if active.isTrackCaller then
    resolveTrackCallerWalkUpAux active.detailPolicy active.callSitePos callers
  else
    applyLocationDetailPolicy active.detailPolicy active.callSitePos

/-- Top-down `trackCallerArg` propagation (`Miri/Interpreter/Call.lean:245-275`): when pushing a
chain of `#[track_caller]` callee frames `tcChain` (`tcChain.all (·.isTrackCaller) = true`) onto an
outer caller `outer` (`outer.isTrackCaller = false`), `resolveTrackCallerWalkUpAux` resolves to
`applyLocationDetailPolicy pol lastTc.callSitePos` if `tcChain` has outermost `#[track_caller]`
frame `lastTc`, or `curPos` if `tcChain` is empty. -/
def propagateTrackCallerTopDown (defaultPos : SourceExpansionPos)
    (tcChain : List FrameLocMeta) : SourceExpansionPos :=
  match tcChain.getLast? with
  | some lastTc => lastTc.callSitePos
  | none => defaultPos

theorem resolveTrackCallerWalkUpAux_eq_topDown (pol : LocationDetailPolicy) :
    ∀ (tcChain : List FrameLocMeta) (outer : FrameLocMeta) (rest : List FrameLocMeta)
      (curPos : SourceExpansionPos),
      tcChain.all (·.isTrackCaller) = true →
      outer.isTrackCaller = false →
      resolveTrackCallerWalkUpAux pol curPos (tcChain ++ outer :: rest) =
        applyLocationDetailPolicy pol (propagateTrackCallerTopDown curPos tcChain)
  | [], outer, rest, curPos, _, h_out => by
    dsimp only [List.nil_append, resolveTrackCallerWalkUpAux, propagateTrackCallerTopDown,
      List.getLast?]
    rw [h_out]
    rfl
  | [f], outer, rest, curPos, h_tc, h_out => by
    simp only [List.all_cons, List.all_nil, Bool.and_true] at h_tc
    dsimp only [List.cons_append, List.nil_append, resolveTrackCallerWalkUpAux,
      propagateTrackCallerTopDown, List.getLast?]
    simp only [h_tc, ↓reduceIte, h_out, Bool.false_eq_true]
    rfl
  | f₁ :: f₂ :: tcRest, outer, rest, curPos, h_tc, h_out => by
    simp only [List.all_cons, Bool.and_eq_true] at h_tc
    rw [List.cons_append, resolveTrackCallerWalkUpAux]
    simp only [h_tc.1, ↓reduceIte]
    have h_ih := resolveTrackCallerWalkUpAux_eq_topDown pol (f₂ :: tcRest) outer rest
      f₁.callSitePos (by simp [List.all_cons, h_tc.2]) h_out
    rw [h_ih]
    rfl

/-! ### Little-Endian Encoding & `CapturedAllocation` Materialization in `Memory.globals` -/

/-- Encode a 32-bit unsigned integer into 4 little-endian `Option UInt8` bytes. -/
def u32LeBytes (n : Nat) : List (Option UInt8) :=
  [ some (UInt8.ofNat (n % 256)),
    some (UInt8.ofNat ((n / 256) % 256)),
    some (UInt8.ofNat ((n / 65536) % 256)),
    some (UInt8.ofNat ((n / 16777216) % 256)) ]

/-- Decode 4 little-endian `Option UInt8` bytes into a `UInt32`. -/
def readU32Le? : List (Option UInt8) → Option UInt32
  | some b0 :: some b1 :: some b2 :: some b3 :: _ =>
    some (UInt32.ofNat (b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat))
  | _ => none

theorem readU32Le_u32LeBytes (u : UInt32) (rest : List (Option UInt8)) :
    readU32Le? (u32LeBytes u.toNat ++ rest) = some u := by
  have h8 : ∀ (k : Nat), (UInt8.ofNat (k % 256)).toNat = k % 256 := by
    intro k
    change (BitVec.ofNat 8 (k % 256)).toNat = k % 256
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_mod k 256
  have hsum :
      (UInt8.ofNat (u.toNat % 256)).toNat +
        256 * (UInt8.ofNat (u.toNat / 256 % 256)).toNat +
        65536 * (UInt8.ofNat (u.toNat / 65536 % 256)).toNat +
        16777216 * (UInt8.ofNat (u.toNat / 16777216 % 256)).toNat = u.toNat := by
    rw [h8, h8, h8, h8]
    have hlt : u.toNat < 4294967296 := u.toBitVec.isLt
    omega
  unfold u32LeBytes readU32Le?
  dsimp only [List.cons_append]
  rw [hsum, UInt32.ofNat_toNat]

/-- Encode a 64-bit unsigned integer (`usize`) into 8 little-endian `Option UInt8` bytes. -/
def u64LeBytes (n : Nat) : List (Option UInt8) :=
  u32LeBytes (n % 4294967296) ++ u32LeBytes (n / 4294967296)

/-- Decode 8 little-endian `Option UInt8` bytes into a `Nat`. -/
def readU64Le? (bs : List (Option UInt8)) : Option Nat :=
  match readU32Le? bs, readU32Le? (bs.drop 4) with
  | some lo, some hi => some (lo.toNat + 4294967296 * hi.toNat)
  | _, _ => none

theorem readU64Le_u64LeBytes {n : Nat} (hn : n < 4294967296) (rest : List (Option UInt8)) :
    readU64Le? (u64LeBytes n ++ rest) = some n := by
  unfold u64LeBytes readU64Le?
  have hlo : n % 4294967296 = n := Nat.mod_eq_of_lt hn
  have hhi : n / 4294967296 = 0 := Nat.div_eq_of_lt hn
  rw [hlo, hhi, List.append_assoc]
  have hu : (UInt32.ofNat n).toNat = n := Nat.mod_eq_of_lt hn
  have h1 := readU32Le_u32LeBytes (UInt32.ofNat n) (u32LeBytes 0 ++ rest)
  rw [hu] at h1
  rw [h1]
  have hdrop : (u32LeBytes n ++ (u32LeBytes 0 ++ rest)).drop 4 = u32LeBytes 0 ++ rest := rfl
  rw [hdrop]
  have h2 := readU32Le_u32LeBytes (0 : UInt32) rest
  change readU32Le? (u32LeBytes 0 ++ rest) = some 0 at h2
  rw [h2]
  simp [hu]

/-- Construct an immutable filename byte allocation in `Memory.globals`. -/
def mkFilenameAllocation (allocId : AllocId) (fileBytes : List UInt8) : CapturedAllocation :=
  { allocId := allocId
    bytes := fileBytes.map Option.some
    relocations := []
    align := ⟨1⟩
    mutability := .not }

/-- Construct an immutable 24-byte `core::panic::Location<'static>` allocation in `Memory.globals`:
- Bytes `0..8`: pointer relocation `(0, { allocId := fileAllocId, offsetBytes := 0 })`,
- Bytes `8..16`: `fileLen : usize` (little-endian),
- Bytes `16..20`: `line : u32` (little-endian),
- Bytes `20..24`: `col : u32` (little-endian). -/
def mkLocationAllocation (locAllocId fileAllocId : AllocId) (fileLen : Nat)
    (line col : UInt32) : CapturedAllocation :=
  { allocId := locAllocId
    bytes :=
      [some 0, some 0, some 0, some 0, some 0, some 0, some 0, some 0] ++
        u64LeBytes fileLen ++ u32LeBytes line.toNat ++ u32LeBytes col.toNat
    relocations := [(0, { allocId := fileAllocId, offsetBytes := 0 })]
    align := ⟨8⟩
    mutability := .not }

/-- Extract initialized byte list from `List (Option UInt8)`. -/
def decodeInitBytes? : List (Option UInt8) → Option (List UInt8)
  | [] => some []
  | some b :: rest =>
    match decodeInitBytes? rest with
    | some bs => some (b :: bs)
    | none => none
  | none :: _ => none

theorem decodeInitBytes?_map_some :
    ∀ (bs : List UInt8), decodeInitBytes? (bs.map Option.some) = some bs
  | [] => rfl
  | b :: rest => by
    unfold List.map decodeInitBytes?
    rw [decodeInitBytes?_map_some rest]

/-- Dereference a `&'static core::panic::Location<'static>` pointer (`locPtr`) in `globals` via
`Trusted.Rustc.V2026_06_01.MirSemantics.lookupGlobalAlloc`, reading `(fileBytes, line, column)`. -/
def readLocationFromGlobals (globals : List CapturedAllocation) (locPtr : ProvenancePtr) :
    Option (List UInt8 × UInt32 × UInt32) :=
  if locPtr.offsetBytes != 0 then
    none
  else
    match lookupGlobalAlloc globals locPtr.allocId with
    | none => none
    | some locAlloc =>
      match locAlloc.relocations with
      | [(0, filePtr)] =>
        if filePtr.offsetBytes != 0 then
          none
        else
          match readU64Le? (locAlloc.bytes.drop 8),
                readU32Le? (locAlloc.bytes.drop 16),
                readU32Le? (locAlloc.bytes.drop 20),
                lookupGlobalAlloc globals filePtr.allocId with
          | some fileLen, some line, some col, some fileAlloc =>
            match decodeInitBytes? (fileAlloc.bytes.take fileLen) with
            | some fileBytes =>
              if fileBytes.length == fileLen then
                some (fileBytes, line, col)
              else
                none
            | none => none
          | _, _, _, _ => none
      | _ => none

theorem lookupGlobalAlloc_append_left {globals₁ globals₂ : List CapturedAllocation}
    {id : AllocId} {alloc : CapturedAllocation}
    (h : lookupGlobalAlloc globals₁ id = some alloc) :
    lookupGlobalAlloc (globals₁ ++ globals₂) id = some alloc := by
  induction globals₁ with
  | nil => nomatch h
  | cons a rest ih =>
    simp only [List.cons_append, lookupGlobalAlloc] at h ⊢
    cases h_eq : Nat.beq a.allocId id with
    | true =>
      rw [h_eq] at h
      exact h
    | false =>
      rw [h_eq] at h
      exact ih h

theorem lookupGlobalAlloc_snoc_self (globals : List CapturedAllocation) (alloc : CapturedAllocation)
    (h_fresh : ∀ a ∈ globals, a.allocId < alloc.allocId) :
    lookupGlobalAlloc (globals ++ [alloc]) alloc.allocId = some alloc := by
  induction globals with
  | nil =>
    simp only [List.nil_append, lookupGlobalAlloc, nat_beq_self_raw]
  | cons a rest ih =>
    simp only [List.cons_append, lookupGlobalAlloc]
    have hlt : a.allocId < alloc.allocId := h_fresh a (List.Mem.head _)
    have hne : Nat.beq a.allocId alloc.allocId = false :=
      nat_beq_ne (Nat.ne_of_lt hlt)
    rw [hne]
    exact ih (fun a' hm => h_fresh a' (List.Mem.tail _ hm))

/-- Demand-time `#[track_caller]` environment (`lean-miri#67` Schema 15), caching allocated
immutable filename `AllocId`s by their redacted byte content so multiple `caller_location` calls
from the same file share a single filename `CapturedAllocation` in `Memory.globals`. -/
structure DemandCallerLocationEnv where
  fileCache : List (List UInt8 × AllocId) := []
  deriving DecidableEq, Repr

/-- Look up a cached filename `AllocId` by byte sequence. -/
def lookupFileCache? (fileBytes : List UInt8) : List (List UInt8 × AllocId) → Option AllocId
  | [] => none
  | (bs, id) :: rest => if listByteEq bs fileBytes then some id else lookupFileCache? fileBytes rest

/-- Demand-time `core::intrinsics::caller_location` evaluation (`lean-miri#67` Schema 15):
1. Resolves the effective `SourceExpansionPos` across the `#[track_caller]` call stack and applies
   the frame's `-Zlocation-detail` redaction policy.
2. Reuses the cached filename `AllocId` if `effPos.fileBytes` is already in `env.fileCache`;
   otherwise allocates a fresh filename `CapturedAllocation` at `mem.nextAllocId`.
3. Allocates a fresh `Location` root `CapturedAllocation` in `Memory.globals` (matching
   `EvalCallerLocationConstruction.lean:55`: fresh root `AllocId` per invocation, shared filename
   `AllocId`), and returns the `&'static Location` pointer `Value.ptr`. -/
def evalDemandCallerLocation (env : DemandCallerLocationEnv) (active : FrameLocMeta)
    (callers : List FrameLocMeta) (mem : Memory) :
    DemandCallerLocationEnv × ProvenancePtr × Memory :=
  let effPos := resolveTrackCallerStack active callers
  match lookupFileCache? effPos.fileBytes env.fileCache with
  | some fileAllocId =>
    let locAllocId := mem.nextAllocId + 1
    let locAlloc := mkLocationAllocation locAllocId fileAllocId
      effPos.fileBytes.length effPos.line effPos.column
    let mem' : Memory :=
      { mem with
        nextAllocId := locAllocId
        globals := mem.globals ++ [locAlloc] }
    (env, { allocId := locAllocId, offsetBytes := 0 }, mem')
  | none =>
    let fileAllocId := mem.nextAllocId + 1
    let locAllocId := mem.nextAllocId + 2
    let fileAlloc := mkFilenameAllocation fileAllocId effPos.fileBytes
    let locAlloc := mkLocationAllocation locAllocId fileAllocId
      effPos.fileBytes.length effPos.line effPos.column
    let env' : DemandCallerLocationEnv :=
      { fileCache := (effPos.fileBytes, fileAllocId) :: env.fileCache }
    let mem' : Memory :=
      { mem with
        nextAllocId := locAllocId
        globals := mem.globals ++ [fileAlloc, locAlloc] }
    (env', { allocId := locAllocId, offsetBytes := 0 }, mem')

/-- Eager pre-materialization baseline (pre-Schema 15): materializes filename + `Location`
allocations for all $S$ candidate call-site spans into `Memory.globals` before execution begins,
even if the program never panics or invokes `caller_location`. -/
def eagerInitCallerLocations (candidateSpans : List (FrameLocMeta × List FrameLocMeta))
    (mem₀ : Memory) : DemandCallerLocationEnv × List ProvenancePtr × Memory :=
  candidateSpans.foldl
    (fun (env, ptrs, mem) (active, callers) =>
      let (env', ptr, mem') := evalDemandCallerLocation env active callers mem
      (env', ptrs ++ [ptr], mem'))
    ({}, [], mem₀)

/-! ### Observational Bisimulation (`AllocRenamingRel`) & Zero-Clutter Theorems -/

/-- Explicit `AllocId` relocation map (`ren : List (AllocId × AllocId)`), relating demand-time
`AllocId`s to eager-world `AllocId`s. -/
def relocateAllocId (ren : List (AllocId × AllocId)) (id : AllocId) : AllocId :=
  match ren.find? (fun p => p.1 == id) with
  | some (_, id') => id'
  | none => id

def relocatePtr (ren : List (AllocId × AllocId)) (p : ProvenancePtr) : ProvenancePtr :=
  { p with allocId := relocateAllocId ren p.allocId }

def relocateValue (ren : List (AllocId × AllocId)) : Value → Value
  | .unit => .unit
  | .scalar sc => .scalar sc
  | .ptr p sz => .ptr (relocatePtr ren p) sz
  | .aggregate vIdx fields => .aggregate vIdx (fields.map (relocateValue ren))

/-- Constructive duplicate-free check on `List Nat`. -/
def nodupNat : List Nat → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && nodupNat xs

/-- Injective partial bijection predicate on `ren : List (AllocId × AllocId)`. -/
def AllocRenamingWf (ren : List (AllocId × AllocId)) : Bool :=
  let dom := ren.map Prod.fst
  let cod := ren.map Prod.snd
  nodupNat dom && nodupNat cod

/-- Observational equivalence of two `(globals, locPtr)` pairs: dereferencing `locPtr₁` in
`globals₁` and `locPtr₂` in `globals₂` via `readLocationFromGlobals` yields the exact same
`Option (List UInt8 × UInt32 × UInt32)`. -/
def LocationPtrObsEq (globals₁ : List CapturedAllocation) (ptr₁ : ProvenancePtr)
    (globals₂ : List CapturedAllocation) (ptr₂ : ProvenancePtr) : Prop :=
  readLocationFromGlobals globals₁ ptr₁ = readLocationFromGlobals globals₂ ptr₂

/-- Full `AllocRenamingRel` between demand-time and eager `Memory` states over a list of returned
`Location` pointers `demandPtrs` (`eagerPtrs = demandPtrs.map (relocatePtr ren)`):
1. `AllocRenamingWf ren = true` (injective `AllocId` renaming),
2. `eagerPtrs = demandPtrs.map (relocatePtr ren)`, and
3. Every pointer pair `(p_d, p_e)` dereferences to the exact same `(fileBytes, line, column)` in
   `memDemand.globals` and `memEager.globals`. -/
structure AllocRenamingRel (ren : List (AllocId × AllocId))
    (memDemand memEager : Memory)
    (demandPtrs eagerPtrs : List ProvenancePtr) : Prop where
  wf : AllocRenamingWf ren = true
  ptrsMapped : eagerPtrs = demandPtrs.map (relocatePtr ren)
  obsAgree :
    ∀ p ∈ demandPtrs,
      LocationPtrObsEq memDemand.globals p memEager.globals (relocatePtr ren p)

/-- Trace step in a multi-step execution comparing demand-time vs. eager `caller_location` worlds:
either a normal MIR statement/computation step (`normalStep` not invoking `caller_location`) or a
`caller_location` intrinsic invocation. -/
inductive CallerLocationTraceEvent where
  | normalStep (stmt : Statement)
  | invokeCallerLocation (active : FrameLocMeta) (callers : List FrameLocMeta)

/-- Run a sequence of `CallerLocationTraceEvent`s in demand-time mode (`lean-miri#67`), allocating
`Location` globals ONLY when `.invokeCallerLocation` events occur. -/
def runDemandCallerLocationTrace (env : DemandCallerLocationEnv) (s : MachineState)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    List CallerLocationTraceEvent → DemandCallerLocationEnv × List ProvenancePtr × MachineState
  | [] => (env, [], s)
  | .normalStep stmt :: rest =>
    let s' := match evalStmt s stmt localDecls layouts with
      | .tau (.running nextState) => nextState
      | _ => s
    runDemandCallerLocationTrace env s' localDecls layouts rest
  | .invokeCallerLocation active callers :: rest =>
    let (nextEnv, ptr, nextMem) :=
      evalDemandCallerLocation env active callers s.memory
    let (finalEnv, restPtrs, finalState) :=
      runDemandCallerLocationTrace nextEnv { s with memory := nextMem } localDecls layouts rest
    (finalEnv, ptr :: restPtrs, finalState)

/-- Predicate stating that a trace contains zero `.invokeCallerLocation` events. -/
def traceHasNoCallerLocation : List CallerLocationTraceEvent → Bool
  | [] => true
  | .normalStep _ :: rest => traceHasNoCallerLocation rest
  | .invokeCallerLocation _ _ :: _ => false

/-- **Zero-Clutter Theorem (`demandCallerLocation_no_call_zero_allocs`)**:
On any trace that does not invoke `caller_location` (`traceHasNoCallerLocation events = true`),
demand-time execution leaves `env` and `ptrs` completely empty (`([], 0)` `Location` allocations),
whereas `eagerInitCallerLocations` pre-allocates `Location` globals for all $S$ candidate spans
before step 0! -/
theorem demandCallerLocation_no_call_zero_allocs (env : DemandCallerLocationEnv) :
    ∀ (events : List CallerLocationTraceEvent) (s : MachineState)
      (localDecls : List LocalDecl) (layouts : LayoutTable),
      traceHasNoCallerLocation events = true →
      (runDemandCallerLocationTrace env s localDecls layouts events).1 = env ∧
        (runDemandCallerLocationTrace env s localDecls layouts events).2.1 = []
  | [], _, _, _, _ => ⟨rfl, rfl⟩
  | .normalStep _stmt :: rest, _s, localDecls, layouts, h =>
    demandCallerLocation_no_call_zero_allocs env rest _ localDecls layouts h
  | .invokeCallerLocation _ _ :: _, _, _, _, h => nomatch h

/-- Soundness of fresh `evalDemandCallerLocation`: when `env = {}`, `mem.globals = []`, and
`pos.fileBytes.length < 4294967296`, `evalDemandCallerLocation` produces a pointer `ptr` that
dereferences in `mem'.globals` to `some (effPos.fileBytes, effPos.line, effPos.column)` where
`effPos = resolveTrackCallerStack active callers`. -/
theorem readLocationFromGlobals_evalDemandCallerLocation_fresh
    (active : FrameLocMeta) (callers : List FrameLocMeta) (mem : Memory)
    (h_empty : mem.globals = [])
    (h_len : (resolveTrackCallerStack active callers).fileBytes.length < 4294967296) :
    let (_, ptr, mem') := evalDemandCallerLocation {} active callers mem
    let effPos := resolveTrackCallerStack active callers
    readLocationFromGlobals mem'.globals ptr =
      some (effPos.fileBytes, effPos.line, effPos.column) := by
  dsimp only [evalDemandCallerLocation, lookupFileCache?]
  unfold readLocationFromGlobals
  rw [h_empty]
  dsimp only [List.nil_append]
  have h_loc_lookup :
      lookupGlobalAlloc
        [mkFilenameAllocation (mem.nextAllocId + 1)
          (resolveTrackCallerStack active callers).fileBytes,
         mkLocationAllocation (mem.nextAllocId + 2) (mem.nextAllocId + 1)
          (resolveTrackCallerStack active callers).fileBytes.length
          (resolveTrackCallerStack active callers).line
          (resolveTrackCallerStack active callers).column]
        (mem.nextAllocId + 2) =
      some (mkLocationAllocation (mem.nextAllocId + 2) (mem.nextAllocId + 1)
        (resolveTrackCallerStack active callers).fileBytes.length
        (resolveTrackCallerStack active callers).line
        (resolveTrackCallerStack active callers).column) := by
    simp only [lookupGlobalAlloc, mkFilenameAllocation, mkLocationAllocation]
    have hne : Nat.beq (mem.nextAllocId + 1) (mem.nextAllocId + 2) = false :=
      nat_beq_ne (by omega)
    rw [hne, nat_beq_self_raw]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, h_loc_lookup]
  dsimp only [mkLocationAllocation]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  have hdrop8 :
      ([some (0 : UInt8), some 0, some 0, some 0, some 0, some 0, some 0, some 0] ++
        u64LeBytes (resolveTrackCallerStack active callers).fileBytes.length ++
        u32LeBytes (resolveTrackCallerStack active callers).line.toNat ++
        u32LeBytes (resolveTrackCallerStack active callers).column.toNat).drop 8 =
      u64LeBytes (resolveTrackCallerStack active callers).fileBytes.length ++
        (u32LeBytes (resolveTrackCallerStack active callers).line.toNat ++
         u32LeBytes (resolveTrackCallerStack active callers).column.toNat) := rfl
  have hdrop16 :
      ([some (0 : UInt8), some 0, some 0, some 0, some 0, some 0, some 0, some 0] ++
        u64LeBytes (resolveTrackCallerStack active callers).fileBytes.length ++
        u32LeBytes (resolveTrackCallerStack active callers).line.toNat ++
        u32LeBytes (resolveTrackCallerStack active callers).column.toNat).drop 16 =
      u32LeBytes (resolveTrackCallerStack active callers).line.toNat ++
        u32LeBytes (resolveTrackCallerStack active callers).column.toNat := rfl
  have hdrop20 :
      ([some (0 : UInt8), some 0, some 0, some 0, some 0, some 0, some 0, some 0] ++
        u64LeBytes (resolveTrackCallerStack active callers).fileBytes.length ++
        u32LeBytes (resolveTrackCallerStack active callers).line.toNat ++
        u32LeBytes (resolveTrackCallerStack active callers).column.toNat).drop 20 =
      u32LeBytes (resolveTrackCallerStack active callers).column.toNat ++ [] := by
    simp [List.append_nil]
    rfl
  rw [hdrop8, readU64Le_u64LeBytes h_len,
      hdrop16, readU32Le_u32LeBytes (resolveTrackCallerStack active callers).line,
      hdrop20, readU32Le_u32LeBytes (resolveTrackCallerStack active callers).column]
  simp only [lookupGlobalAlloc, mkFilenameAllocation, nat_beq_self_raw]
  have htake :
      ((resolveTrackCallerStack active callers).fileBytes.map Option.some).take
        (resolveTrackCallerStack active callers).fileBytes.length =
      (resolveTrackCallerStack active callers).fileBytes.map Option.some := by
    rw [List.take_of_length_le (by simp)]
  rw [htake, decodeInitBytes?_map_some]
  dsimp only
  rw [nat_beq_self]
  rfl

/-- Concrete 3-frame `#[track_caller]` forwarding chain:
`user_caller` (`isTrackCaller = false`, `src/lib.rs:42:13`)
  $\rightarrow$ `Option::unwrap` (`isTrackCaller = true`, `core/option.rs:950:5`)
  $\rightarrow$ `option::unwrap_failed` (`isTrackCaller = true`, `core/option.rs:1980:5`)
  $\rightarrow$ `core::intrinsics::caller_location()`. -/
def protoLibRsBytes : List UInt8 := [115, 114, 99, 47, 108, 105, 98, 46, 114, 115] -- "src/lib.rs"
def protoOptionRsBytes : List UInt8 := [99, 111, 114, 101, 47, 111, 112, 116, 46, 114, 115]

def protoUserCallerPos : SourceExpansionPos := ⟨"src/lib.rs", protoLibRsBytes, 42, 13⟩
def protoUnwrapBodyPos : SourceExpansionPos := ⟨"core/opt.rs", protoOptionRsBytes, 950, 5⟩
def protoUnwrapFailedPos : SourceExpansionPos := ⟨"core/opt.rs", protoOptionRsBytes, 1980, 5⟩
def protoOtherCallPos : SourceExpansionPos := ⟨"src/lib.rs", protoLibRsBytes, 108, 7⟩

def protoUnwrapFailedFrame (pol : LocationDetailPolicy := {}) : FrameLocMeta :=
  ⟨"core::option::unwrap_failed", protoUnwrapBodyPos, true, pol⟩

def protoUnwrapFrame (pol : LocationDetailPolicy := {}) : FrameLocMeta :=
  ⟨"core::option::Option::unwrap", protoUserCallerPos, true, pol⟩

def protoUserCallerFrame (pol : LocationDetailPolicy := {}) : FrameLocMeta :=
  ⟨"my_crate::user_caller", protoOtherCallPos, false, pol⟩

/-- Candidate spans for the eager vs. demand comparison. -/
def protoCandidateSpans (pol : LocationDetailPolicy := {}) :
    List (FrameLocMeta × List FrameLocMeta) :=
  [ (protoUserCallerFrame pol, []),
    (protoUnwrapFrame pol, [protoUserCallerFrame pol]),
    (protoUnwrapFailedFrame pol, [protoUnwrapFrame pol, protoUserCallerFrame pol]) ]

/-- **Filename Deduplication Theorem (`demandCallerLocation_filename_dedup`)**:
Two `caller_location` invocations from different lines in `"src/lib.rs"` (`42:13` and `108:7`)
materialize only **3** `CapturedAllocation`s in `Memory.globals` (1 shared filename allocation at
`allocId = 1`, plus 2 distinct `Location` root allocations at `allocId = 2` and `allocId = 3`),
rather than duplicating the filename bytes! -/
theorem demandCallerLocation_filename_dedup :
    let (env₁, ptr₁, mem₁) :=
      evalDemandCallerLocation {} (protoUnwrapFailedFrame {})
        [protoUnwrapFrame {}, protoUserCallerFrame {}] emptyMemory
    let (env₂, ptr₂, mem₂) :=
      evalDemandCallerLocation env₁ (protoUserCallerFrame {}) [] mem₁
    mem₂.globals.length = 3 ∧
      env₂.fileCache.length = 1 ∧
      ptr₁.allocId = 2 ∧
      ptr₂.allocId = 3 ∧
      readLocationFromGlobals mem₂.globals ptr₁ = some (protoLibRsBytes, 42, 13) ∧
      readLocationFromGlobals mem₂.globals ptr₂ = some (protoLibRsBytes, 108, 7) := by
  decide +kernel

/-- **Observational Bisimulation Across All 8 `-Zlocation-detail` Policies & `#[track_caller]`
Forwarding Chains (`demandCallerLocation_bisim_eager`)**:
For every policy `pol ∈ allLocationDetailPolicies` (all 8 combinations of `file`, `line`, `column`
redaction):
1. Executing `caller_location` on demand in `protoUnwrapFailedFrame pol` across the 3-frame
   `#[track_caller]` chain `user_caller -> unwrap -> unwrap_failed` and pre-allocating all
   candidate spans via `eagerInitCallerLocations (protoCandidateSpans pol)` are related by an
   injective `AllocRenamingRel` (`ren = [(1, 1), (2, 4)]`), and
2. Both dereference to the exact same redacted `(fileBytes, line, column)` of `protoUserCallerPos`! -/
theorem demandCallerLocation_bisim_eager :
    ∀ pol ∈ allLocationDetailPolicies,
      let (_, dPtr, dMem) :=
        evalDemandCallerLocation {} (protoUnwrapFailedFrame pol)
          [protoUnwrapFrame pol, protoUserCallerFrame pol] emptyMemory
      let (_, ePtrs, eMem) :=
        eagerInitCallerLocations (protoCandidateSpans pol) emptyMemory
      let expected := applyLocationDetailPolicy pol protoUserCallerPos
      AllocRenamingRel [(1, 1), (2, 4)] dMem eMem [dPtr] (ePtrs.drop 2) ∧
        readLocationFromGlobals dMem.globals dPtr =
          some (expected.fileBytes, expected.line, expected.column) ∧
        readLocationFromGlobals eMem.globals ({ allocId := 4, offsetBytes := 0 }) =
          some (expected.fileBytes, expected.line, expected.column) := by
  intro pol hpol
  simp only [allLocationDetailPolicies, List.mem_cons, List.not_mem_nil, or_false] at hpol
  rcases hpol with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨⟨rfl, rfl, ?_⟩, by decide +kernel, by decide +kernel⟩ <;>
    (intro p hp; simp only [List.mem_singleton] at hp; subst hp; rfl)

/-- Non-`#[track_caller]` intermediate frame reset witness: if the middle frame has
`isTrackCaller = false`, `resolveTrackCallerStack` stops at that frame's call site rather than
forwarding the outer caller's position. -/
theorem trackCaller_stops_at_nonTrackCaller_frame :
    let nonTrackMid : FrameLocMeta :=
      ⟨"my_crate::non_track_helper", protoUnwrapBodyPos, false, {}⟩
    resolveTrackCallerStack (protoUnwrapFailedFrame {}) [nonTrackMid, protoUserCallerFrame {}] =
      protoUnwrapBodyPos := by
  decide +kernel

/-! ## Part D: `LazyWriteChain` & `bvShiftSafe` / `shiftLeftBitsSafe` (`cl/1023450318`, `cl/1023378691`, `lean4#16501`, `lean4#16504`) -/

/-- Symbolic fixed-width vector/slot array term (`SymArrayTerm`, `cl/1023450318`). -/
inductive SymArrayTerm where
  | base (id : Nat) (len : Nat) : SymArrayTerm
  | constVec (len : Nat) (defaultVal : Nat) : SymArrayTerm
  | write (arr : SymArrayTerm) (idx : Nat) (val : Nat) : SymArrayTerm
  | ite (cond : Bool) (tBranch : SymArrayTerm) (fBranch : SymArrayTerm) : SymArrayTerm
  deriving DecidableEq, Repr

/-- Length of a `SymArrayTerm`. -/
def symArrayLen : SymArrayTerm → Nat
  | .base _ len => len
  | .constVec len _ => len
  | .write arr _ _ => symArrayLen arr
  | .ite cond t f => if cond then symArrayLen t else symArrayLen f

/-- Denotational semantics of `SymArrayTerm` at index `i`. -/
def evalSymArrayTerm (env : Nat → Nat → Option Nat) : SymArrayTerm → Nat → Option Nat
  | .base id len, i => if i < len then env id i else none
  | .constVec len defVal, i => if i < len then some defVal else none
  | .write arr idx val, i =>
    if i < symArrayLen arr then
      if i == idx then some val else evalSymArrayTerm env arr i
    else
      none
  | .ite cond t f, i =>
    if cond then evalSymArrayTerm env t i else evalSymArrayTerm env f i

/-- **Lazy 1-layer overwrite-stripping symbolic write (`mkLazyWrite`, `cl/1023450318`)**:
1. Constant-folds out-of-bounds writes (`!(idx < symArrayLen arr)`),
2. Collapses same-value writes onto `.constVec len defVal`,
3. Collapses **immediately preceding** same-address concrete overwrites `.write inner idx' _` when
   `idx' == idx`, and
4. Stops immediately in $O(1)$ when `idx' != idx` without walking the write spine! -/
def mkLazyWrite (arr : SymArrayTerm) (idx : Nat) (val : Nat) : SymArrayTerm :=
  if !(idx < symArrayLen arr) then
    arr
  else
    match arr with
    | .constVec len defVal =>
      if val == defVal then .constVec len defVal else .write (.constVec len defVal) idx val
    | .write inner idx' val' =>
      if idx' == idx then
        .write inner idx val
      else
        .write (.write inner idx' val') idx val
    | other => .write other idx val

theorem symArrayLen_mkLazyWrite (arr : SymArrayTerm) (idx val : Nat) :
    symArrayLen (mkLazyWrite arr idx val) = symArrayLen arr := by
  unfold mkLazyWrite
  split
  · rfl
  · cases arr with
    | constVec len defVal =>
      dsimp only
      split <;> rfl
    | write inner idx' val' =>
      dsimp only
      split <;> rfl
    | base _ _ => rfl
    | ite _ _ _ => rfl

theorem evalSymArrayTerm_oob (env : Nat → Nat → Option Nat) :
    ∀ (arr : SymArrayTerm) (i : Nat),
      ¬(i < symArrayLen arr) →
      evalSymArrayTerm env arr i = none
  | .base _ _, i, hi => by
    unfold symArrayLen at hi
    unfold evalSymArrayTerm
    simp only [hi, ↓reduceIte]
  | .constVec _ _, i, hi => by
    unfold symArrayLen at hi
    unfold evalSymArrayTerm
    simp only [hi, ↓reduceIte]
  | .write _ _ _, i, hi => by
    unfold symArrayLen at hi
    unfold evalSymArrayTerm
    simp only [hi, ↓reduceIte]
  | .ite cond t f, i, hi => by
    unfold symArrayLen at hi
    unfold evalSymArrayTerm
    cases cond with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hi ⊢
      exact evalSymArrayTerm_oob env f i hi
    | true =>
      simp only [↓reduceIte] at hi ⊢
      exact evalSymArrayTerm_oob env t i hi

/-- **Exact Semantic Soundness of `mkLazyWrite` (`eval_mkLazyWrite`)**:
For all environments `env`, terms `arr`, write indices `idx`, values `val`, and read indices `i`,
`mkLazyWrite arr idx val` denotes the exact same array as `.write arr idx val`. -/
theorem eval_mkLazyWrite (env : Nat → Nat → Option Nat) (arr : SymArrayTerm)
    (idx val i : Nat) :
    evalSymArrayTerm env (mkLazyWrite arr idx val) i =
      evalSymArrayTerm env (.write arr idx val) i := by
  unfold mkLazyWrite
  split
  · rename_i h_oob
    have hge : symArrayLen arr ≤ idx := Nat.le_of_not_lt (by simpa using h_oob)
    conv => rhs; unfold evalSymArrayTerm
    by_cases hi : i < symArrayLen arr
    · simp only [hi, ↓reduceIte]
      have hne : (i == idx) = false :=
        beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (Nat.lt_of_lt_of_le hi hge))
      rw [hne]
      rfl
    · simp only [hi, ↓reduceIte]
      exact evalSymArrayTerm_oob env arr i hi
  · rename_i h_in
    cases arr with
    | base id len => rfl
    | ite cond t f => rfl
    | constVec len defVal =>
      dsimp only
      cases hv : val == defVal with
      | true =>
        have hveq : val = defVal := beq_iff_eq.mp hv
        subst hveq
        simp only [↓reduceIte, evalSymArrayTerm, symArrayLen]
        by_cases hi : i < len
        · simp only [hi, ↓reduceIte]
          cases i == idx <;> rfl
        · simp only [hi, ↓reduceIte]
      | false => rfl
    | write inner idx' val' =>
      dsimp only
      cases hidx : idx' == idx with
      | true =>
        have heq : idx' = idx := beq_iff_eq.mp hidx
        subst heq
        simp only [↓reduceIte]
        change (if i < symArrayLen inner then
            if (i == idx') = true then some val else evalSymArrayTerm env inner i
          else none) =
          if i < symArrayLen inner then
            if (i == idx') = true then some val else evalSymArrayTerm env (.write inner idx' val') i
          else none
        by_cases hi : i < symArrayLen inner
        · simp only [hi, ↓reduceIte]
          cases h_i : i == idx' <;> simp only [Bool.false_eq_true, ↓reduceIte, evalSymArrayTerm, hi, h_i]
        · simp only [hi, ↓reduceIte]
      | false => rfl

/-- Deep spine-stripping helper used by the $O(N^2)$ eager write baseline (`mkEagerWrite`). -/
def stripShadowedWrites : SymArrayTerm → Nat → SymArrayTerm
  | .write inner idx' val', idx =>
    let inner' := stripShadowedWrites inner idx
    if idx' == idx then inner' else .write inner' idx' val'
  | other, _ => other

/-- Eager write baseline (`mkEagerWrite`): walks the entire write spine on every write to strip
shadowed writes at `idx`, incurring $\Theta(N^2)$ spine inspections across $N$ distinct-address writes. -/
def mkEagerWrite (arr : SymArrayTerm) (idx : Nat) (val : Nat) : SymArrayTerm :=
  if !(idx < symArrayLen arr) then
    arr
  else
    .write (stripShadowedWrites arr idx) idx val

theorem symArrayLen_stripShadowedWrites :
    ∀ (arr : SymArrayTerm) (idx : Nat),
      symArrayLen (stripShadowedWrites arr idx) = symArrayLen arr
  | .base _ _, _ => rfl
  | .constVec _ _, _ => rfl
  | .ite _ _ _, _ => rfl
  | .write inner idx' val', idx => by
    unfold stripShadowedWrites
    dsimp only
    split
    · exact symArrayLen_stripShadowedWrites inner idx
    · show symArrayLen (stripShadowedWrites inner idx) = symArrayLen inner
      exact symArrayLen_stripShadowedWrites inner idx

theorem eval_stripShadowedWrites_ne (env : Nat → Nat → Option Nat) :
    ∀ (arr : SymArrayTerm) (idx i : Nat),
      (i == idx) = false →
      evalSymArrayTerm env (stripShadowedWrites arr idx) i = evalSymArrayTerm env arr i
  | .base _ _, _, _, _ => rfl
  | .constVec _ _, _, _, _ => rfl
  | .ite _ _ _, _, _, _ => rfl
  | .write inner idx' val', idx, i, hne => by
    unfold stripShadowedWrites
    dsimp only
    cases hidx : idx' == idx with
    | true =>
      have heq : idx' = idx := beq_iff_eq.mp hidx
      subst heq
      simp only [↓reduceIte]
      conv => rhs; unfold evalSymArrayTerm
      rw [hne]
      simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hi : i < symArrayLen inner
      · simp only [hi, ↓reduceIte]
        exact eval_stripShadowedWrites_ne env inner idx' i hne
      · simp only [hi, ↓reduceIte]
        have hi' : ¬(i < symArrayLen (stripShadowedWrites inner idx')) := by
          rw [symArrayLen_stripShadowedWrites]
          exact hi
        exact evalSymArrayTerm_oob env (stripShadowedWrites inner idx') i hi'
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      unfold evalSymArrayTerm
      rw [symArrayLen_stripShadowedWrites]
      by_cases hi : i < symArrayLen inner
      · simp only [hi, ↓reduceIte]
        cases i == idx' with
        | true => rfl
        | false => exact eval_stripShadowedWrites_ne env inner idx i hne
      · simp only [hi, ↓reduceIte]

/-- Lazy read-over-write folding (`mkLazyRead`): resolves concrete reads directly from a write
chain by forwarding `val` on `rIdx == idx` and skipping distinct concrete writes `rIdx != idx`. -/
def mkLazyRead : SymArrayTerm → Nat → Option Nat
  | .base _ _, _ => none
  | .constVec len defVal, rIdx => if rIdx < len then some defVal else none
  | .write inner idx val, rIdx =>
    if !(rIdx < symArrayLen inner) then
      none
    else if rIdx == idx then
      some val
    else
      mkLazyRead inner rIdx
  | .ite cond t f, rIdx =>
    if cond then mkLazyRead t rIdx else mkLazyRead f rIdx

/-- **Soundness of `mkLazyRead` (`eval_mkLazyRead`)**: whenever `mkLazyRead arr rIdx = some v`,
`evalSymArrayTerm env arr rIdx = some v` for *every* base environment `env`! -/
theorem eval_mkLazyRead (env : Nat → Nat → Option Nat) :
    ∀ (arr : SymArrayTerm) (rIdx v : Nat),
      mkLazyRead arr rIdx = some v →
      evalSymArrayTerm env arr rIdx = some v
  | .base _ _, _, _, h => nomatch h
  | .constVec len defVal, rIdx, v, h => by
    unfold mkLazyRead at h
    unfold evalSymArrayTerm
    exact h
  | .write inner idx val, rIdx, v, h => by
    unfold mkLazyRead at h
    unfold evalSymArrayTerm
    by_cases hlt : rIdx < symArrayLen inner
    · have hnot : (!(rIdx < symArrayLen inner)) = false := by simp [hlt]
      rw [hnot] at h
      simp only [hlt, ↓reduceIte]
      cases h_eq : rIdx == idx with
      | true =>
        rw [h_eq] at h
        exact h
      | false =>
        rw [h_eq] at h
        exact eval_mkLazyRead env inner rIdx v h
    · have hnot : (!(rIdx < symArrayLen inner)) = true := by simp [hlt]
      rw [hnot] at h
      nomatch h
  | .ite cond t f, rIdx, v, h => by
    unfold mkLazyRead at h
    unfold evalSymArrayTerm
    cases cond with
    | false => exact eval_mkLazyRead env f rIdx v h
    | true => exact eval_mkLazyRead env t rIdx v h

/-! ### Exact Spine-Inspection Complexity: `mkLazyWrite` ($O(N)$) vs. `mkEagerWrite` ($\Theta(N^2)$) -/

/-- Number of write-spine nodes inspected by one `mkLazyWrite` call (always $1$). -/
def lazyWriteInspectSteps (_arr : SymArrayTerm) : Nat := 1

/-- Number of write-spine nodes inspected by `stripShadowedWrites` during one `mkEagerWrite` call
on a spine of length $k$ (inspects `1 + spineDepth`, i.e., $k + 1$ nodes). -/
def eagerWriteInspectSteps : SymArrayTerm → Nat
  | .write inner _ _ => 1 + eagerWriteInspectSteps inner
  | _ => 1

/-- Total spine inspections across $N$ distinct-address writes `[0, 1, ..., N - 1]` under
`mkLazyWrite`. -/
def lazyWriteChainSteps : Nat → Nat
  | 0 => 0
  | n + 1 => lazyWriteChainSteps n + 1

/-- Total spine inspections across $N$ distinct-address writes `[0, 1, ..., N - 1]` under
`mkEagerWrite` (the $(k+1)$-th write walks the $k$ previous distinct-address writes plus the base). -/
def eagerWriteChainSteps : Nat → Nat
  | 0 => 0
  | n + 1 => eagerWriteChainSteps n + (n + 1)

/-- Build an actual `SymArrayTerm` of $n$ distinct-address writes under `mkLazyWrite`. -/
def buildLazyDistinctChain (cap : Nat) : Nat → SymArrayTerm
  | 0 => .constVec cap 0
  | n + 1 => mkLazyWrite (buildLazyDistinctChain cap n) n (n + 1)

/-- Build an actual `SymArrayTerm` of $n$ distinct-address writes under `mkEagerWrite` while
accumulating exact `eagerWriteInspectSteps`. -/
def buildEagerDistinctChainWithSteps (cap : Nat) : Nat → SymArrayTerm × Nat
  | 0 => (.constVec cap 0, 0)
  | n + 1 =>
    let (arr, steps) := buildEagerDistinctChainWithSteps cap n
    let cost := eagerWriteInspectSteps arr
    (mkEagerWrite arr n (n + 1), steps + cost)

/-- **$O(N)$ Linear Bound for `mkLazyWrite` (`lazyWriteChain_distinctAddrs_steps_eq_N`)**:
$N$ distinct-address writes perform exactly $N$ constant-time top-layer inspections. -/
theorem lazyWriteChain_distinctAddrs_steps_eq_N :
    ∀ (N : Nat), lazyWriteChainSteps N = N
  | 0 => rfl
  | n + 1 => by
    unfold lazyWriteChainSteps
    rw [lazyWriteChain_distinctAddrs_steps_eq_N n]

/-- **$\Theta(N^2)$ Quadratic Lower/Exact Bound for `mkEagerWrite`
(`eagerWriteChain_distinctAddrs_steps_quadratic`)**:
$N$ distinct-address writes under eager spine stripping perform $\frac{N(N+1)}{2}$ inspections
(`2 * eagerWriteChainSteps N = N * (N + 1)`). -/
theorem eagerWriteChain_distinctAddrs_steps_quadratic :
    ∀ (N : Nat), 2 * eagerWriteChainSteps N = N * (N + 1)
  | 0 => rfl
  | n + 1 => by
    unfold eagerWriteChainSteps
    rw [Nat.left_distrib, eagerWriteChain_distinctAddrs_steps_quadratic n]
    have h_rhs : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by
      calc (n + 1) * ((n + 1) + 1)
        _ = (n + 1) * (n + 1) + (n + 1) * 1 := Nat.left_distrib (n + 1) (n + 1) 1
        _ = (n * (n + 1) + 1 * (n + 1)) + (n + 1) * 1 := by rw [Nat.right_distrib]
        _ = n * (n + 1) + 2 * (n + 1) := by omega
    exact h_rhs.symm

/-! ### Total Width-Clamped `BitVec` & Anneal `Scalars` Shifts (`cl/1023378691`, `lean4#16501`, `lean4#16504`) -/

/-- Upstream Lean 4 PR #16501 `shiftLeft.threshold` (`65536`), guarding `whnf`/`simp`/`grind` from
calling `Nat.shiftLeft` on exponents $\ge 2^{32}$. -/
def shiftLeftThreshold : Nat := 65536

/-- Upstream Lean 4 PR #16504 `BitVec` width safety ceiling (`65536`). -/
def maxSafeBitVecWidth : Nat := 65536

/-- Guard predicate (`lean4#16501`) checking whether `shift ≤ threshold`. -/
def isSafeShiftLeft (shift : Nat) (threshold : Nat := shiftLeftThreshold) : Bool :=
  decide (shift ≤ threshold)

/-- Guard predicate (`lean4#16504`) checking whether `BitVec` width `w ≤ maxWidth`. -/
def isSafeBitVecWidth (w : Nat) (maxWidth : Nat := maxSafeBitVecWidth) : Bool :=
  decide (w ≤ maxWidth)

/-- Total width-clamped `BitVec` left shift (`cl/1023378691`): clamps `s ≥ w` to `0#w` before
evaluating `x <<< s`, avoiding `Nat.shiftLeft` on huge `s`. -/
def bvShlSafe {w : Nat} (x : BitVec w) (s : Nat) : BitVec w :=
  if s < w then x <<< s else 0#w

/-- Total width-clamped `BitVec` logical right shift (`cl/1023378691`). -/
def bvLshrSafe {w : Nat} (x : BitVec w) (s : Nat) : BitVec w :=
  if s < w then x >>> s else 0#w

/-- Total width-clamped `BitVec` arithmetic right shift (`cl/1023378691`). -/
def bvAshrSafe {w : Nat} (x : BitVec w) (s : Nat) : BitVec w :=
  if s < w then BitVec.sshiftRight x s else BitVec.sshiftRight x w

/-- **Exact `BitVec` Left-Shift Equivalence (`bvShlSafe_eq`)** (`0` `Classical.choice`). -/
theorem bvShlSafe_eq {w : Nat} (x : BitVec w) (s : Nat) :
    bvShlSafe x s = x <<< s := by
  unfold bvShlSafe
  split
  · rfl
  · rename_i h
    have hge : w ≤ s := Nat.le_of_not_lt h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.zero_mod, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have hsplit : s = w + (s - w) := (Nat.add_sub_of_le hge).symm
    have hpow : 2 ^ s = 2 ^ w * 2 ^ (s - w) := by
      conv => lhs; rw [hsplit]
      exact Nat.pow_add 2 w (s - w)
    rw [hpow, ← Nat.mul_assoc, Nat.mul_comm x.toNat (2 ^ w), Nat.mul_assoc, Nat.mul_mod_right]

/-- **Exact `BitVec` Logical Right-Shift Equivalence (`bvLshrSafe_eq`)** (`0` `Classical.choice`). -/
theorem bvLshrSafe_eq {w : Nat} (x : BitVec w) (s : Nat) :
    bvLshrSafe x s = x >>> s := by
  unfold bvLshrSafe
  split
  · rfl
  · rename_i h
    have hge : w ≤ s := Nat.le_of_not_lt h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.zero_mod, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have hlt : x.toNat < 2 ^ s :=
      Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) hge)
    exact (Nat.div_eq_of_lt hlt).symm

private theorem int_sub_eq_negSucc {a b : Nat} (h : a < b) :
    (a : Int) - (b : Int) = Int.negSucc (b - 1 - a) := by
  omega

/-- **Exact `BitVec` Arithmetic Right-Shift Equivalence (`bvAshrSafe_eq`)** (`0` `Classical.choice`). -/
theorem bvAshrSafe_eq {w : Nat} (x : BitVec w) (s : Nat) :
    bvAshrSafe x s = BitVec.sshiftRight x s := by
  unfold bvAshrSafe
  split
  · rfl
  · rename_i h
    have hge : w ≤ s := Nat.le_of_not_lt h
    unfold BitVec.sshiftRight
    congr 1
    unfold BitVec.toInt
    split
    · show Int.ofNat (x.toNat >>> w) = Int.ofNat (x.toNat >>> s)
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
          Nat.div_eq_of_lt x.isLt,
          Nat.div_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) hge))]
    · rw [int_sub_eq_negSucc x.isLt]
      show Int.negSucc ((2 ^ w - 1 - x.toNat) >>> w) = Int.negSucc ((2 ^ w - 1 - x.toNat) >>> s)
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
      have hlt_w : 2 ^ w - 1 - x.toNat < 2 ^ w :=
        Nat.lt_of_le_of_lt (Nat.sub_le _ _)
          (Nat.sub_lt (Nat.two_pow_pos w) (by decide))
      have hlt_s : 2 ^ w - 1 - x.toNat < 2 ^ s :=
        Nat.lt_of_lt_of_le hlt_w (Nat.pow_le_pow_right (by decide) hge)
      rw [Nat.div_eq_of_lt hlt_w, Nat.div_eq_of_lt hlt_s]

/-! ### Total Width-Clamped Anneal `Scalars` Shifts (`shiftLeftBitsSafe`, `shiftRightUnsignedBitsSafe`, `arithmeticShrBitsSafe`) -/

theorem scalarPow2_add (a b : Nat) :
    scalarPow2 (a + b) = scalarPow2 a * scalarPow2 b := by
  rw [scalarPow2_eq_two_pow, scalarPow2_eq_two_pow, scalarPow2_eq_two_pow, Nat.pow_add]

theorem scalarPow2_le_of_le {a b : Nat} (h : a ≤ b) :
    scalarPow2 a ≤ scalarPow2 b := by
  rw [scalarPow2_eq_two_pow, scalarPow2_eq_two_pow]
  exact Nat.pow_le_pow_right (by decide) h

theorem scalarModulus_eq_scalarPow2_mul8 (sz : Nat) :
    scalarModulus sz = scalarPow2 (sz * 8) := by
  rw [scalarModulus_eq_two_pow, scalarPow2_eq_two_pow, Nat.mul_comm]

/-- Total width-clamped counterpart of `Trusted.Rustc.V2026_06_01.MirSemantics.shiftLeftBits`:
short-circuits `shift ≥ sizeBytes * 8` to `0` before evaluating `scalarPow2 shift`. -/
def shiftLeftBitsSafe (a shift sizeBytes : Nat) : Nat :=
  let modulus := scalarModulus sizeBytes
  let numBits := Nat.mul sizeBytes 8
  if shift < numBits then
    shiftLeftBits a shift modulus
  else
    0

/-- Total width-clamped counterpart of `Trusted.Rustc.V2026_06_01.MirSemantics.shiftRightUnsignedBits`:
short-circuits `shift ≥ sizeBytes * 8` to `0` before evaluating `scalarPow2 shift`. -/
def shiftRightUnsignedBitsSafe (a shift sizeBytes : Nat) : Nat :=
  let numBits := Nat.mul sizeBytes 8
  if shift < numBits then
    shiftRightUnsignedBits a shift
  else
    0

/-- Total width-clamped counterpart of `Trusted.Rustc.V2026_06_01.MirSemantics.arithmeticShrBits`:
short-circuits `shift ≥ sizeBytes * 8` to `0` (non-negative) or `scalarModulus sizeBytes - 1`
(negative, all 1s) before evaluating `scalarPow2 shift`. -/
def arithmeticShrBitsSafe (bits sizeBytes shift : Nat) : Nat :=
  let modulus := scalarModulus sizeBytes
  let numBits := Nat.mul sizeBytes 8
  if shift < numBits then
    arithmeticShrBits bits sizeBytes shift
  else
    let canonical := wrapScalarBits bits modulus
    match isSignedNegative canonical sizeBytes with
    | false => 0
    | true => Nat.sub modulus 1

/-- **Unconditional Exact Equivalence (`shiftLeftBitsSafe_eq`)**:
For *all* `a`, `shift`, and `sizeBytes : Nat`, `shiftLeftBitsSafe a shift sizeBytes` equals
`Trusted.Rustc.V2026_06_01.MirSemantics.shiftLeftBits a shift (scalarModulus sizeBytes)`. -/
theorem shiftLeftBitsSafe_eq (a shift sizeBytes : Nat) :
    shiftLeftBitsSafe a shift sizeBytes = shiftLeftBits a shift (scalarModulus sizeBytes) := by
  unfold shiftLeftBitsSafe
  dsimp only
  split
  · rfl
  · rename_i h
    have hge : sizeBytes * 8 ≤ shift := Nat.le_of_not_lt h
    unfold shiftLeftBits
    rw [wrapScalarBits_eq_mod_modulus]
    have hsplit : shift = sizeBytes * 8 + (shift - sizeBytes * 8) := (Nat.add_sub_of_le hge).symm
    have hpow : scalarPow2 shift = scalarModulus sizeBytes * scalarPow2 (shift - sizeBytes * 8) := by
      conv => lhs; rw [hsplit]
      rw [scalarPow2_add, scalarModulus_eq_scalarPow2_mul8]
    change 0 = (a * scalarPow2 shift) % scalarModulus sizeBytes
    rw [hpow, ← Nat.mul_assoc, Nat.mul_comm a (scalarModulus sizeBytes), Nat.mul_assoc,
        Nat.mul_mod_right]

/-- **Exact Equivalence (`shiftRightUnsignedBitsSafe_eq`)**:
For every canonical `sizeBytes`-byte scalar `a < scalarModulus sizeBytes` and every `shift : Nat`,
`shiftRightUnsignedBitsSafe a shift sizeBytes` equals
`Trusted.Rustc.V2026_06_01.MirSemantics.shiftRightUnsignedBits a shift`. -/
theorem shiftRightUnsignedBitsSafe_eq {a sizeBytes : Nat} (ha : a < scalarModulus sizeBytes)
    (shift : Nat) :
    shiftRightUnsignedBitsSafe a shift sizeBytes = shiftRightUnsignedBits a shift := by
  unfold shiftRightUnsignedBitsSafe
  dsimp only
  split
  · rfl
  · rename_i h
    have hge : sizeBytes * 8 ≤ shift := Nat.le_of_not_lt h
    unfold shiftRightUnsignedBits
    change 0 = a / scalarPow2 shift
    have hlt : a < scalarPow2 shift := by
      rw [scalarModulus_eq_scalarPow2_mul8] at ha
      exact Nat.lt_of_lt_of_le ha (scalarPow2_le_of_le hge)
    exact (Nat.div_eq_of_lt hlt).symm

/-- **Unconditional Exact Equivalence (`arithmeticShrBitsSafe_eq`)**:
For *all* `bits`, `sizeBytes`, and `shift : Nat`, `arithmeticShrBitsSafe bits sizeBytes shift`
equals `Trusted.Rustc.V2026_06_01.MirSemantics.arithmeticShrBits bits sizeBytes shift`. -/
theorem arithmeticShrBitsSafe_eq (bits sizeBytes shift : Nat) :
    arithmeticShrBitsSafe bits sizeBytes shift = arithmeticShrBits bits sizeBytes shift := by
  unfold arithmeticShrBitsSafe
  dsimp only
  split
  · rfl
  · rename_i h
    have hge : sizeBytes * 8 ≤ shift := Nat.le_of_not_lt h
    unfold arithmeticShrBits
    dsimp only
    have hc_lt : wrapScalarBits bits (scalarModulus sizeBytes) < scalarModulus sizeBytes :=
      wrapScalarBits_lt_of_pos bits (scalarModulus_pos sizeBytes)
    have hlog : shiftRightUnsignedBits (wrapScalarBits bits (scalarModulus sizeBytes)) shift = 0 := by
      rw [← shiftRightUnsignedBitsSafe_eq hc_lt shift]
      unfold shiftRightUnsignedBitsSafe
      dsimp only
      simp only [h, ↓reduceIte]
    rw [hlog]
    cases isSignedNegative (wrapScalarBits bits (scalarModulus sizeBytes)) sizeBytes with
    | false =>
      dsimp only
      exact (wrapScalarBits_eq_self_of_lt (scalarModulus_pos sizeBytes)).symm
    | true =>
      dsimp only
      have hsub : Nat.sub (Nat.mul sizeBytes 8) shift = 0 := Nat.sub_eq_zero_of_le hge
      change Nat.sub (scalarModulus sizeBytes) 1 =
        wrapScalarBits (Nat.add 0 (Nat.sub (scalarModulus sizeBytes)
          (scalarPow2 (Nat.sub (Nat.mul sizeBytes 8) shift)))) (scalarModulus sizeBytes)
      rw [hsub]
      change Nat.sub (scalarModulus sizeBytes) 1 =
        wrapScalarBits (0 + (scalarModulus sizeBytes - 1)) (scalarModulus sizeBytes)
      rw [Nat.zero_add]
      have hlt1 : scalarModulus sizeBytes - 1 < scalarModulus sizeBytes :=
        Nat.sub_lt (scalarModulus_pos sizeBytes) (by decide)
      exact (wrapScalarBits_eq_self_of_lt hlt1).symm

/-- Wide shift exponent `2^64` (`18446744073709551616`), which aborts unguarded `Nat.shiftLeft` /
`scalarPow2` evaluation (`wide_shift` mutant / `lean4#16501`). -/
def wideShiftTwoPow64 : Nat := 18446744073709551616

/-- Live kernel evaluation canary at `shift = 2^64` (`18446744073709551616`) for all three safe
Anneal scalar shifts and all three safe `BitVec` shifts, discharging in $O(1)$ heartbeats via
`decide +kernel`. -/
theorem canary_wideShift_two_pow_64 :
    isSafeShiftLeft wideShiftTwoPow64 = false ∧
    shiftLeftBitsSafe 0xdeadbeef wideShiftTwoPow64 4 = 0 ∧
    shiftRightUnsignedBitsSafe 0xdeadbeef wideShiftTwoPow64 4 = 0 ∧
    arithmeticShrBitsSafe 0x80000000 4 wideShiftTwoPow64 = 0xffffffff ∧
    arithmeticShrBitsSafe 0x7fffffff 4 wideShiftTwoPow64 = 0 ∧
    bvShlSafe (0xdeadbeef#32) wideShiftTwoPow64 = 0#32 ∧
    bvLshrSafe (0xdeadbeef#32) wideShiftTwoPow64 = 0#32 ∧
    bvAshrSafe (0x80000000#32) wideShiftTwoPow64 = 0xffffffff#32 := by
  decide +kernel

end Anneal.SparseRetagAndVcNarrowPrototype

/-! ## Bottom-of-File Module Axiom & Namespace Hygiene Audit -/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Quot.sound]
  let forbiddenOf (n : Name) : Elab.Command.CommandElabM (Array Name) := do
    return (← Lean.collectAxioms n).filter (fun ax => !allowed.contains ax)
  for (probe, ax) in [(``Classical.em, ``Classical.choice), (``sorryAx, ``sorryAx),
      (``Lean.ofReduceBool, ``Lean.ofReduceBool)] do
    unless (← forbiddenOf probe).contains ax do
      throwError "axiom audit self-test failed: {probe} not flagged for {ax}"
  let pfx := `Anneal.SparseRetagAndVcNarrowPrototype
  let mut constants : Nat := 0
  let mut inNamespace : Nat := 0
  let mut theorems : Nat := 0
  let mut leaked : Array Name := #[]
  let mut bad : Array (Name × Array Name) := #[]
  for (n, ci) in env.constants.map₂.toList do
    constants := constants + 1
    if ci.isUnsafe then
      throwError "unsafe declaration in prototype: {n}"
    let un := (Lean.privateToUserName? n).getD n
    if pfx.isPrefixOf un then
      inNamespace := inNamespace + 1
    else
      let last := un.eraseMacroScopes.getString!
      let isRealizedEq :=
        last == "eq_def" || last == "splitter" || last == "else_eq" ||
          last.startsWith "eq_" || last.startsWith "_sparseCasesOn_"
      unless un.hasMacroScopes || isRealizedEq do
        leaked := leaked.push un
    if ci matches .thmInfo _ then theorems := theorems + 1
    let f ← forbiddenOf n
    unless f.isEmpty do bad := bad.push (n, f)
  unless bad.isEmpty do
    throwError "axiom audit failed — forbidden axioms used: {bad}"
  unless leaked.isEmpty do
    throwError "namespace hygiene audit failed — leaked constants outside {pfx}: {leaked}"
  unless inNamespace ≥ 80 && theorems ≥ 35 do
    throwError "axiom audit coverage too low: {inNamespace} in namespace, {theorems} theorems"
