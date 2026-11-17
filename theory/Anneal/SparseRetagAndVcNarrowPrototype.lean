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

* **Part A (`SparseRetagAttrIndex`, `proofs-rs/lean-miri` PR #68)**: binary radix trie over
  `DefId` (`NatBitTrie`, 12 low bits + exact-key leaf buckets) with `Except`-cached whole-table
  duplicate and bounds validation (`prepareSparseRetagIndex`, `lookupSparseRetag`), proved
  unconditionally equivalent (`lookupSparseRetag_eq_linearScan`) to the linear reference oracle
  `linearScanRetagAttr` (which re-validates the table with an `O(M)` duplicate scan per row, i.e.
  `O(M^2)` per query, mirroring `lean-miri`'s `CompilerRetagOptions.rustcNoWritable`), preserving
  exact error precedence (`frameAbsent_precedes_malformedTable`), with hit/miss certificates, a
  `DefPath`-keyed companion index, and an operational `StatementKind.retag .fnEntry` overlay whose
  implicit-write upgrade targets only the freshly created child tag
  (`applyImplicitWriteUpgrade_of_no_fresh_child`).
* **Part B (`BatchedVcConeNarrowCert` + `hoistTraitImpls` + `@[irreducible] coerceValueAt`,
  `bensherman` `cl/1022801564` `#cpp_vc_narrow`)**: ONE Boolean checker
  (`checkBatchedVcConeNarrowCert`, discharged by a single `decide +kernel`) from which every field
  of the propositional certificate is derived (`BatchedVcConeNarrowCert.ofCheck`): closed
  direct/polymorphic/trait-method call cone, mask-based first-match `findCallee?` preservation
  (duplicate shadowing included, no body equality needed), `TraitImplEntry` target closure with
  `hoistTraitImpls`, and external-contract admissibility (`UntrustedAdmissible`, summary
  agreement). `computeBatchedVcNarrowCert` / `collectTraitConeBodies` compute the certificate
  data. Core theorems: `runMirExecBounded_narrow_of_batchedCert`,
  `wpMirExecSym_narrow_of_batchedCert`, and `vcMirWithCallees_narrow_of_batchedCert` over a
  contract-aware WP (`wpMirExecExt`) in which cone summaries genuinely restrict external-call
  answers (`canary_externalSummary_vc`). `coerceValueAt` is sealed (`@[irreducible]`) with targeted
  rewrite lemmas.
* **Part C (`DemandCallerLocationEnv`, `proofs-rs/lean-miri` PR #67 Schema 15)**: demand-time
  `#[track_caller]` `core::panic::Location` + deduplicated filename allocation in `Memory.globals`
  (fresh ids drawn from the *next fresh* `Memory.nextAllocId`), `find_closest_untracked_caller_location`
  resolution with per-crate `-Zlocation-detail` policies (all 8 combinations, `Option` call sites),
  and general theorems over ALL call-site tables and traces: `demandCallerLocation_bisim_eager`,
  `demandCallerLocation_no_call_zero_allocs`, `eagerCallerLocation_clutter`, and
  `allocRenamingRel_of_readLocations`.
* **Part D (`LazyWriteChain` & `bvShiftSafe` / `shiftLeftBitsSafe`, `bilid` `cl/1023450318` &
  `cl/1023378691`, `leanprover/lean4` PRs #16501 & #16504)**: static-width lazy 1-layer
  overwrite-stripping writes (`mkLazyWrite`: `O(1)` per write) vs. spine-stripping `mkEagerWrite`,
  with step counts proved on instrumented copies of the implementations (`N` vs. `N(N+1)/2`), and
  total width-clamped `BitVec` / Anneal `Scalars` shifts evaluating `shift = 2^64` in the kernel.
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

private theorem mod_two_eq_of_beq_one_eq {a b : Nat}
    (h : (a % 2 == 1) = (b % 2 == 1)) : a % 2 = b % 2 := by
  have ha : a % 2 < 2 := Nat.mod_lt a (by decide)
  have hb : b % 2 < 2 := Nat.mod_lt b (by decide)
  generalize hr₁ : a % 2 = r₁ at ha h
  generalize hr₂ : b % 2 = r₂ at hb h
  match r₁, r₂ with
  | 0, 0 => rfl
  | 1, 1 => rfl
  | 0, 1 => nomatch h
  | 1, 0 => nomatch h
  | _ + 2, _ => omega
  | _, _ + 2 => omega

/-- **Injectivity of `natLowBits d` on `< 2^d` (`natLowBits_inj_of_lt_pow2`)**: any two keys
`k₁, k₂ < 2^d` with the same `d`-bit path are equal, so no two distinct keys `< 2^d` ever share a
leaf bucket. -/
theorem natLowBits_inj_of_lt_pow2 :
    ∀ (d : Nat) {k₁ k₂ : Nat},
      k₁ < 2 ^ d → k₂ < 2 ^ d →
      natLowBits d k₁ = natLowBits d k₂ → k₁ = k₂
  | 0, k₁, k₂, h₁, h₂, _ => by omega
  | d + 1, k₁, k₂, h₁, h₂, heq => by
    unfold natLowBits at heq
    injection heq with hbit hrest
    have hpow : 2 ^ (d + 1) = 2 ^ d * 2 := Nat.pow_succ 2 d
    have hk₁ : k₁ / 2 < 2 ^ d := by omega
    have hk₂ : k₂ / 2 < 2 ^ d := by omega
    have hdiv : k₁ / 2 = k₂ / 2 := natLowBits_inj_of_lt_pow2 d hk₁ hk₂ hrest
    have hmod : k₁ % 2 = k₂ % 2 := mod_two_eq_of_beq_one_eq hbit
    have h1 := Nat.div_add_mod k₁ 2
    have h2 := Nat.div_add_mod k₂ 2
    rw [hdiv, hmod] at h1
    exact h1.symm.trans h2

/-- Default minimum binary radix depth (`12` bits = `4,096` direct leaf slots). -/
def defaultRetagTrieDepth : Nat := 12

/-- Adaptive binary radix depth scaling with `definitionCount` (`max 12 (log2 definitionCount + 1)`),
guaranteeing `definitionCount ≤ 2 ^ adaptiveRetagTrieDepth definitionCount` so every valid
`DefId < definitionCount` has a unique bit path (`adaptiveRetagTrieDepth_bitPath_injective`) even
when `definitionCount > 4096`. -/
def adaptiveRetagTrieDepth (definitionCount : Nat) : Nat :=
  max defaultRetagTrieDepth (definitionCount.log2 + 1)

theorem lt_two_pow_adaptiveRetagTrieDepth {definitionCount id : Nat}
    (h : id < definitionCount) : id < 2 ^ adaptiveRetagTrieDepth definitionCount := by
  have hlog : definitionCount ≤ 2 ^ (definitionCount.log2 + 1) :=
    Nat.le_of_lt Nat.lt_log2_self
  have hle : definitionCount.log2 + 1 ≤ adaptiveRetagTrieDepth definitionCount :=
    Nat.le_max_right defaultRetagTrieDepth (definitionCount.log2 + 1)
  have hpow : 2 ^ (definitionCount.log2 + 1) ≤ 2 ^ adaptiveRetagTrieDepth definitionCount :=
    Nat.pow_le_pow_right (by decide) hle
  exact Nat.lt_of_lt_of_le h (Nat.le_trans hlog hpow)

theorem adaptiveRetagTrieDepth_bitPath_injective {definitionCount k₁ k₂ : Nat}
    (h₁ : k₁ < definitionCount) (h₂ : k₂ < definitionCount)
    (heq : natLowBits (adaptiveRetagTrieDepth definitionCount) k₁ =
      natLowBits (adaptiveRetagTrieDepth definitionCount) k₂) :
    k₁ = k₂ :=
  natLowBits_inj_of_lt_pow2 (adaptiveRetagTrieDepth definitionCount)
    (lt_two_pow_adaptiveRetagTrieDepth h₁) (lt_two_pow_adaptiveRetagTrieDepth h₂) heq

/-- Constructive binary radix trie over `Nat` keys with configurable bit depth `depth`
(defaulting to `defaultRetagTrieDepth = 12`, and scaling via `adaptiveRetagTrieDepth` in
`prepareSparseRetagIndex`). -/
structure NatBitTrie (α : Type) where
  root : BitTrie α := .empty
  depth : Nat := defaultRetagTrieDepth
  deriving DecidableEq, Repr

/-- Empty `NatBitTrie` at bit depth `depth` (default `12`). -/
def NatBitTrie.empty {α : Type} (depth : Nat := defaultRetagTrieDepth) : NatBitTrie α :=
  ⟨.empty, depth⟩

/-- Insert `(k, v)` into `NatBitTrie`. -/
def NatBitTrie.insert {α : Type} (t : NatBitTrie α) (k : Nat) (v : α) : NatBitTrie α :=
  ⟨trieInsertBits t.root (natLowBits t.depth k) k v, t.depth⟩

/-- Look up `id` in `NatBitTrie` in $O(\text{depth})$ bit-branch steps. -/
def NatBitTrie.get? {α : Type} (t : NatBitTrie α) (id : Nat) : Option α :=
  trieLookupBits t.root (natLowBits t.depth id) id

theorem NatBitTrie.get?_empty {α : Type} (id : Nat) (depth : Nat := defaultRetagTrieDepth) :
    (NatBitTrie.empty depth : NatBitTrie α).get? id = none := rfl

/-- Exact lookup-after-insert characterization for `NatBitTrie`, holding unconditionally for all
`t`, `k`, `v`, and `id : Nat`. -/
theorem NatBitTrie.get?_insert {α : Type} (t : NatBitTrie α) (k : Nat) (v : α) (id : Nat) :
    (t.insert k v).get? id = if k == id then some v else t.get? id := by
  unfold NatBitTrie.get? NatBitTrie.insert
  dsimp only
  if hpath : natLowBits t.depth k = natLowBits t.depth id then
    rw [hpath]
    exact trieLookupBits_insert_same (natLowBits t.depth id) t.root k v id
  else
    have hlen : (natLowBits t.depth k).length =
        (natLowBits t.depth id).length := by
      rw [natLowBits_length, natLowBits_length]
    rw [trieLookupBits_insert_diff _ _ t.root k v id hlen hpath]
    have hne : (k == id) = false := by
      cases hbeq : (k == id) with
      | false => rfl
      | true =>
        have heq : k = id := beq_iff_eq.mp hbeq
        exact absurd (congrArg (natLowBits t.depth) heq) hpath
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
keys directly via `trie.get? row.definition` ($O(\log D)$) while populating `NatBitTrie Bool`. -/
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

/-- Prepare the sparse retag attribute index once per compiler table (`lean-miri#68`), using
`adaptiveRetagTrieDepth definitionCount` (`≥ 12` and `≥ log2 definitionCount + 1`) and caching
any validation error in `Except RetagAttrErr SparseRetagAttrIndex` so malformed unused tables
still fail only when queried. -/
def prepareSparseRetagIndex (definitionCount : Nat) (rows : List RetagQueryRow) :
    Except RetagAttrErr SparseRetagAttrIndex :=
  prepareSparseRetagLoop definitionCount (.empty (adaptiveRetagTrieDepth definitionCount)) 0 rows

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
  · exact prepareSparseRetagLoop_lookup_eq definitionCount id rows []
      (.empty (adaptiveRetagTrieDepth definitionCount)) 0 (fun _ => rfl)

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

/-- Perform the Tree Borrows initial implicit child write on the protected child created by
`evalStmt` on `.retag .fnEntry` when `implicitWrites && !rustcNoWritable` activates a mutable
reference at function entry (`Miri/TreeBorrows/RetagPolicy.lean` & `Statements.lean:1770-1864`):
1. The fresh child is identified by its tag (`head.tag = preTag ∧ s'.memory.nextTag = preTag + 1`),
   so retag paths that create no child (ZSTs, slices, globals) leave `borrows` untouched.
2. Interior-mutable `.cell` references (`&mut UnsafeCell<T>`) remain `.cell` without an activating
   write (`applyImplicitWriteUpgrade_cell_noop`).
3. For `Freeze` mutable references (`head.perm = .reservedFrz false`), performs the full Tree
   Borrows child write through `head.tag`:
   - Checks ancestor child-write UB (`treeBorrowAncestorsChildAccessUB .write`, e.g. reborrowing
     `&mut T` from a `.frozen` parent) and protected foreign write conflicts
     (`hasProtectedTreeWriteConflict`), faulting with `MirStepNode.fail .ub` if either fires;
   - Transitions all affected borrow entries via `invalidateTreeBorrowsAtProj` (promoting `head` to
     `.unique`, preserving local ancestors, and disabling conflicting foreign `.frozen` / `.unique`
     siblings). -/
def applyImplicitWriteUpgrade (preTag : Nat) (node : MirStepNode) (localDecls : List LocalDecl)
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
          match Nat.beq head.tag preTag && Nat.beq s'.memory.nextTag (preTag + 1) with
          | true =>
            match head.perm with
            | .cell => node
            | _ =>
              let allBorrows := head :: tail
              let writeUB :=
                treeBorrowAncestorsChildAccessUB .write allBorrows head.parentTag ||
                  hasProtectedTreeWriteConflict allBorrows allBorrows s'.memory.activeProtectors
                    head.targetLocal (.some head.tag) head.targetProjection
                    head.rangeOffset head.rangeLen head.targetFrameDepth
              match writeUB with
              | true => MirStepNode.fail .ub
              | false =>
                MirStepNode.step
                  { s' with memory := { s'.memory with
                      borrows :=
                        invalidateTreeBorrowsAtProj allBorrows allBorrows head.targetLocal
                          (.some head.tag) head.targetProjection head.rangeOffset
                          head.rangeLen head.targetFrameDepth } }
          | false => node
        | [] => node
      | _ => node
    | _ => node

/-- When the fresh child has permission `.cell` (`&mut UnsafeCell<T>`), `applyImplicitWriteUpgrade`
preserves `.cell` without overwriting it to `.unique`. -/
theorem applyImplicitWriteUpgrade_cell_noop (preTag : Nat) (s' : MachineState)
    (head : BorrowEntry) (tail : List BorrowEntry)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (place : Place)
    (implicitWrites rustcNoWritable : Bool)
    (h_borrows : s'.memory.borrows = head :: tail) (h_cell : head.perm = .cell) :
    applyImplicitWriteUpgrade preTag (.tau (.running s')) localDecls layouts place
        implicitWrites rustcNoWritable = .tau (.running s') := by
  unfold applyImplicitWriteUpgrade
  cases implicitWrites && !rustcNoWritable with
  | false => rfl
  | true =>
    dsimp only
    split
    · rw [h_borrows]
      dsimp only
      split
      · rw [h_cell]
      · rfl
    · rfl

/-- **Child-targeting of the implicit-write overlay**: when the step created no fresh child
(`nextTag` unchanged), `applyImplicitWriteUpgrade` is the identity — no unrelated borrow entry is
ever rewritten. -/
theorem applyImplicitWriteUpgrade_of_no_fresh_child (preTag : Nat) (s' : MachineState)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (place : Place)
    (implicitWrites rustcNoWritable : Bool) (h : s'.memory.nextTag = preTag) :
    applyImplicitWriteUpgrade preTag (.tau (.running s')) localDecls layouts place
        implicitWrites rustcNoWritable = .tau (.running s') := by
  have hb : Nat.beq s'.memory.nextTag (preTag + 1) = false := by
    rw [h]
    exact nat_beq_ne (Nat.ne_of_lt (Nat.lt_succ_self preTag))
  unfold applyImplicitWriteUpgrade
  cases implicitWrites && !rustcNoWritable with
  | false => rfl
  | true =>
    dsimp only
    split
    · split
      · rw [hb, Bool.and_false]
      · rfl
    · rfl

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
      applyImplicitWriteUpgrade s.memory.nextTag (evalStmt s stmt localDecls layouts)
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

/-- **Tree Borrows Implicit-Write Soundness Canary (`canary_implicitWrite_treeBorrows_full`)**:
1. A `.cell` child (`&mut UnsafeCell<T>`) is preserved as `.cell` (not clobbered to `.unique`).
2. A `.reservedFrz false` child whose parent has `.frozen` permission faults to
   `MirStepNode.fail .ub` under implicit write (`treeBorrowAncestorsChildAccessUB .write` = true).
3. A foreign `.frozen` sibling on the same local/range is disabled (`.disabled`) when a
   `.reservedFrz false` child upgrades to `.unique` via `invalidateTreeBorrowsAtProj`. -/
theorem canary_implicitWrite_treeBorrows_full :
    let emptyLayouts : LayoutTable := { pointerBits := 64, isLittleEndian := true, entries := [] }
    let refMutTy : Ty := { kind := .ref .mut (.uint .u32), layoutIdx := 0 }
    let u32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
    let ldecls : List LocalDecl := [⟨.mut, u32Ty, some "_0"⟩, ⟨.mut, refMutTy, some "_1"⟩]
    let place1 : Place := ⟨1, []⟩
    let baseFrame : StackFrame := { locals := [], blockIdx := 0, stmtIdx := 0 }
    let parentFrz : BorrowEntry :=
      { tag := 1, targetLocal := 0, targetProjection := [], perm := .frozen, rangeLen := 4 }
    let childOfFrz : BorrowEntry :=
      { tag := 2, targetLocal := 0, targetProjection := [], perm := .reservedFrz false,
        parentTag := some 1, rangeLen := 4 }
    let stateFrzChild : MachineState :=
      { frame := baseFrame,
        memory := { emptyMemory with borrows := [childOfFrz, parentFrz], nextTag := 3 } }
    let parentUniq : BorrowEntry :=
      { tag := 1, targetLocal := 0, targetProjection := [], perm := .unique, rangeLen := 4 }
    let foreignSiblingFrz : BorrowEntry :=
      { tag := 2, targetLocal := 0, targetProjection := [], perm := .frozen,
        parentTag := some 1, rangeLen := 4 }
    let childReserved : BorrowEntry :=
      { tag := 3, targetLocal := 0, targetProjection := [], perm := .reservedFrz false,
        parentTag := some 1, rangeLen := 4 }
    let stateSibling : MachineState :=
      { frame := baseFrame,
        memory := { emptyMemory with
          borrows := [childReserved, foreignSiblingFrz, parentUniq], nextTag := 4 } }
    let childCell : BorrowEntry :=
      { tag := 2, targetLocal := 0, targetProjection := [], perm := .cell,
        parentTag := some 1, rangeLen := 4 }
    let stateCell : MachineState :=
      { frame := baseFrame,
        memory := { emptyMemory with borrows := [childCell, parentUniq], nextTag := 3 } }
    let permCode (p : TreeBorrowPerm) : Nat :=
      match p with
      | .unique => 1
      | .disabled => 2
      | .cell => 3
      | _ => 0
    (match applyImplicitWriteUpgrade 2 (.tau (.running stateCell)) ldecls emptyLayouts place1 true false with
      | .tau (.running s') => s'.memory.borrows.map (fun b => (b.tag, permCode b.perm))
      | _ => []) = [(2, 3), (1, 1)] ∧
    (match applyImplicitWriteUpgrade 2 (.tau (.running stateFrzChild)) ldecls emptyLayouts place1 true false with
      | .vis (.inl (.fail .ub)) _ => true
      | _ => false) = true ∧
    (match applyImplicitWriteUpgrade 3 (.tau (.running stateSibling)) ldecls emptyLayouts place1 true false with
      | .tau (.running s') => s'.memory.borrows.map (fun b => (b.tag, permCode b.perm))
      | _ => []) = [(3, 1), (2, 2), (1, 1)] := by
  decide +kernel

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

/-- External call summary entry associating an external `DefPath` with a return-value contract
identifier (`summaryTag : Nat`, interpreted by an `ExternalContractInterp`). -/
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

/-- Decidable check that for every `dp ∈ cone`, every `TraitImplEntry` targeting `dp` in
`ti₁ ++ flatMapTraitImpls c₁` has `e.implPath ∈ cone` and a body in `c₂` (rejecting missing impl
bodies). -/
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

/-! #### Mask-Based Callee Narrowing (sound first-match preservation without body equality) -/

/-- Keep the callees whose mask bit is `true` (missing bits drop the callee). -/
def selectByMask : List CapturedMir → List Bool → List CapturedMir
  | [], _ => []
  | _ :: _, [] => []
  | c :: cs, b :: bs => if b then c :: selectByMask cs bs else selectByMask cs bs

/-- Index of the first callee whose `defPath` is `dp` (the entry `findCallee?` returns). -/
def firstCalleeIdx? : List CapturedMir → DefPath → Option Nat
  | [], _ => none
  | c :: cs, dp => if stringEq c.defPath dp then some 0 else (firstCalleeIdx? cs dp).map (· + 1)

/-- For every `dp ∈ cone`, the mask keeps the *first* full-table entry for `dp`, so a shadowed
duplicate can never be exposed by the narrowing (string/index-only check: no `CapturedMir`
equality is needed). -/
def checkMaskKeepsFirstMatch (cone : List DefPath) (full : List CapturedMir)
    (mask : List Bool) : Bool :=
  cone.all (fun dp =>
    match firstCalleeIdx? full dp with
    | none => true
    | some i => mask.getD i false)

theorem firstCalleeIdx?_cons (c : CapturedMir) (cs : List CapturedMir) (dp : DefPath) :
    firstCalleeIdx? (c :: cs) dp =
      if stringEq c.defPath dp then some 0 else (firstCalleeIdx? cs dp).map (· + 1) := rfl

theorem findCallee?_cons (c : CapturedMir) (cs : List CapturedMir) (dp : DefPath) :
    findCallee? (c :: cs) dp =
      match stringEq c.defPath dp with
      | true => some c
      | false => findCallee? cs dp := rfl

theorem findCallee?_eq_none_of_firstCalleeIdx? :
    ∀ {cs : List CapturedMir} {dp : DefPath}, firstCalleeIdx? cs dp = none → findCallee? cs dp = none
  | [], _, _ => rfl
  | c :: cs, dp, h => by
    rw [firstCalleeIdx?_cons] at h
    rw [findCallee?_cons]
    cases hs : stringEq c.defPath dp with
    | true => rw [hs] at h; nomatch h
    | false =>
      rw [hs] at h
      dsimp only
      cases hj : firstCalleeIdx? cs dp with
      | none => exact findCallee?_eq_none_of_firstCalleeIdx? hj
      | some j => rw [hj] at h; nomatch h

theorem findCallee?_selectByMask :
    ∀ (full : List CapturedMir) (mask : List Bool) (dp : DefPath),
      (match firstCalleeIdx? full dp with
        | none => true
        | some i => mask.getD i false) = true →
      findCallee? (selectByMask full mask) dp = findCallee? full dp
  | [], _, _, _ => rfl
  | c :: cs, mask, dp, h => by
    cases hs : stringEq c.defPath dp with
    | true =>
      have hfi : firstCalleeIdx? (c :: cs) dp = some 0 := by
        rw [firstCalleeIdx?_cons, hs]
        rfl
      rw [hfi] at h
      cases mask with
      | nil => nomatch h
      | cons b bs =>
        cases b with
        | false => nomatch h
        | true =>
          show findCallee? (c :: selectByMask cs bs) dp = findCallee? (c :: cs) dp
          rw [findCallee?_cons, findCallee?_cons, hs]
    | false =>
      have hfi : firstCalleeIdx? (c :: cs) dp = (firstCalleeIdx? cs dp).map (· + 1) := by
        rw [firstCalleeIdx?_cons, hs]
        rfl
      have hfull : findCallee? (c :: cs) dp = findCallee? cs dp := by
        rw [findCallee?_cons, hs]
      rw [hfi] at h
      rw [hfull]
      cases mask with
      | nil =>
        cases hj : firstCalleeIdx? cs dp with
        | none => exact (findCallee?_eq_none_of_firstCalleeIdx? hj).symm
        | some j => rw [hj] at h; nomatch h
      | cons b bs =>
        have ih := findCallee?_selectByMask cs bs dp (by
          cases hj : firstCalleeIdx? cs dp with
          | none => rfl
          | some j =>
            rw [hj] at h
            exact h)
        cases b with
        | false => exact ih
        | true =>
          show findCallee? (c :: selectByMask cs bs) dp = findCallee? cs dp
          rw [findCallee?_cons, hs]
          exact ih

theorem calleesAgreeOn_selectByMask {cone : List DefPath} {full : List CapturedMir}
    {mask : List Bool} (h : checkMaskKeepsFirstMatch cone full mask = true) :
    calleesAgreeOn cone full (selectByMask full mask) := by
  intro dp hdp
  exact (findCallee?_selectByMask full mask dp (List.all_eq_true.mp h dp hdp)).symm

/-- Drop the callees whose mask bit is `true` (complement of `selectByMask`), collecting the
dropped bodies whose `TraitImplEntry` records must be hoisted into `Memory.traitImpls`. -/
def dropByMask : List CapturedMir → List Bool → List CapturedMir
  | [], _ => []
  | cs, [] => cs
  | c :: cs, b :: bs => if b then dropByMask cs bs else c :: dropByMask cs bs

/-- Mask-aware trait-impl hoisting (`hoistMaskTraitImpls`): hoists `TraitImplEntry` records only
from the *dropped* callees (`dropByMask fullCallees mask`) into `Memory.traitImpls`, while *kept*
callees (`selectByMask fullCallees mask`) retain their own `c.traitImpls` in `Memory.callees`
without duplicating dispatch records! -/
def hoistMaskTraitImpls (fullCallees : List CapturedMir) (mask : List Bool)
    (extra : List TraitImplEntry) : List TraitImplEntry :=
  extra ++ flatMapTraitImpls (dropByMask fullCallees mask)

/-- Check that for every `dp ∈ cone`, `TraitImplEntry` records targeting `dp` in `fullCallees`
live either in dropped carrier bodies (`dropByMask`) or in kept `impl` bodies (`selectByMask`).
Unlike `checkKeptCarryNoConeTraitImpls`, this succeeds when kept `impl` bodies carry their own
`TraitImplEntry` records (the standard `rustc-capture` layout). -/
def checkMaskTraitPartition (cone : List DefPath) (fullCallees : List CapturedMir)
    (mask : List Bool) : Bool :=
  cone.all (fun dp =>
    ((flatMapTraitImpls (selectByMask fullCallees mask)).all
      (fun e => !stringEq e.traitRef.defPath dp)) ||
    ((flatMapTraitImpls (dropByMask fullCallees mask)).all
      (fun e => !stringEq e.traitRef.defPath dp)))

private theorem filter_eq_nil_of_all_not {α : Type} (p : α → Bool) :
    ∀ (xs : List α), xs.all (fun x => !p x) = true → xs.filter p = []
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    cases hx : p x with
    | true => rw [hx] at h; nomatch h.1
    | false =>
      simp only [List.filter, hx]
      exact filter_eq_nil_of_all_not p xs h.2

private theorem flatMapTraitImpls_dropByMask_filter_eq (p : TraitImplEntry → Bool) :
    ∀ (full : List CapturedMir) (mask : List Bool),
      (flatMapTraitImpls (selectByMask full mask)).filter p = [] →
      (flatMapTraitImpls (dropByMask full mask)).filter p = (flatMapTraitImpls full).filter p
  | [], _ , _ => rfl
  | _ :: _, [], _ => rfl
  | c :: cs, b :: bs, h => by
    cases b with
    | false =>
      show (c.traitImpls ++ flatMapTraitImpls (dropByMask cs bs)).filter p =
        (c.traitImpls ++ flatMapTraitImpls cs).filter p
      rw [List.filter_append, List.filter_append,
        flatMapTraitImpls_dropByMask_filter_eq p cs bs h]
    | true =>
      change (c.traitImpls ++ flatMapTraitImpls (selectByMask cs bs)).filter p = [] at h
      rw [List.filter_append] at h
      have hc : c.traitImpls.filter p = [] := (List.append_eq_nil_iff.mp h).1
      have hcs : (flatMapTraitImpls (selectByMask cs bs)).filter p = [] :=
        (List.append_eq_nil_iff.mp h).2
      show (flatMapTraitImpls (dropByMask cs bs)).filter p =
        (c.traitImpls ++ flatMapTraitImpls cs).filter p
      rw [List.filter_append, hc, List.nil_append]
      exact flatMapTraitImpls_dropByMask_filter_eq p cs bs hcs

private theorem flatMapTraitImpls_selectByMask_filter_eq (p : TraitImplEntry → Bool) :
    ∀ (full : List CapturedMir) (mask : List Bool),
      (flatMapTraitImpls (dropByMask full mask)).filter p = [] →
      (flatMapTraitImpls (selectByMask full mask)).filter p = (flatMapTraitImpls full).filter p
  | [], _, _ => rfl
  | _ :: _, [], h => h.symm
  | c :: cs, b :: bs, h => by
    cases b with
    | true =>
      show (c.traitImpls ++ flatMapTraitImpls (selectByMask cs bs)).filter p =
        (c.traitImpls ++ flatMapTraitImpls cs).filter p
      rw [List.filter_append, List.filter_append,
        flatMapTraitImpls_selectByMask_filter_eq p cs bs h]
    | false =>
      change (c.traitImpls ++ flatMapTraitImpls (dropByMask cs bs)).filter p = [] at h
      rw [List.filter_append] at h
      have hc : c.traitImpls.filter p = [] := (List.append_eq_nil_iff.mp h).1
      have hcs : (flatMapTraitImpls (dropByMask cs bs)).filter p = [] :=
        (List.append_eq_nil_iff.mp h).2
      show (flatMapTraitImpls (selectByMask cs bs)).filter p =
        (c.traitImpls ++ flatMapTraitImpls cs).filter p
      rw [List.filter_append, hc, List.nil_append]
      exact flatMapTraitImpls_selectByMask_filter_eq p cs bs hcs

theorem traitFilter_hoistMask_eq {cone : List DefPath} {full : List CapturedMir}
    {mask : List Bool} {extra : List TraitImplEntry}
    (h : checkMaskTraitPartition cone full mask = true)
    {dp : DefPath} (hdp : dp ∈ cone) :
    (extra ++ flatMapTraitImpls full).filter (fun e => stringEq e.traitRef.defPath dp) =
      (hoistMaskTraitImpls full mask extra ++ flatMapTraitImpls (selectByMask full mask)).filter
        (fun e => stringEq e.traitRef.defPath dp) := by
  have hpart := List.all_eq_true.mp h dp hdp
  unfold hoistMaskTraitImpls
  rw [List.filter_append, List.filter_append, List.filter_append]
  cases hsel : (flatMapTraitImpls (selectByMask full mask)).all
      (fun e => !stringEq e.traitRef.defPath dp) with
  | true =>
    have hnil := filter_eq_nil_of_all_not (fun (e : TraitImplEntry) => stringEq e.traitRef.defPath dp) _ hsel
    rw [hnil, List.append_nil,
      flatMapTraitImpls_dropByMask_filter_eq (fun (e : TraitImplEntry) => stringEq e.traitRef.defPath dp) full mask hnil]
  | false =>
    rw [hsel, Bool.false_or] at hpart
    have hnil := filter_eq_nil_of_all_not (fun (e : TraitImplEntry) => stringEq e.traitRef.defPath dp) _ hpart
    rw [hnil, List.append_nil,
      flatMapTraitImpls_selectByMask_filter_eq (fun (e : TraitImplEntry) => stringEq e.traitRef.defPath dp) full mask hnil]

/-- Kept bodies carry no `TraitImplEntry` targeting a cone path, so hoisting every entry with
`hoistTraitImpls` cannot duplicate cone dispatch records (fail-closed restriction). -/
def checkKeptCarryNoConeTraitImpls (cone : List DefPath) (narrow : List CapturedMir) : Bool :=
  (flatMapTraitImpls narrow).all (fun e => !inCone cone e.traitRef.defPath)

theorem traitFilter_hoist_eq {cone : List DefPath} {full narrow : List CapturedMir}
    {extra : List TraitImplEntry} (h : checkKeptCarryNoConeTraitImpls cone narrow = true)
    {dp : DefPath} (hdp : dp ∈ cone) :
    (extra ++ flatMapTraitImpls full).filter (fun e => stringEq e.traitRef.defPath dp) =
      (hoistTraitImpls full extra ++ flatMapTraitImpls narrow).filter
        (fun e => stringEq e.traitRef.defPath dp) := by
  have hgen : ∀ (l : List TraitImplEntry),
      l.all (fun e => !inCone cone e.traitRef.defPath) = true →
      l.filter (fun e => stringEq e.traitRef.defPath dp) = [] := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons e rest ih =>
      intro hall
      rw [List.all_cons, Bool.and_eq_true] at hall
      have hs : stringEq e.traitRef.defPath dp = false := by
        cases hs : stringEq e.traitRef.defPath dp with
        | false => rfl
        | true =>
          have hin : inCone cone e.traitRef.defPath = true := by
            rw [coneStringEq_iff.mp hs]
            exact inCone_iff.mpr hdp
          have hno := hall.1
          rw [hin] at hno
          nomatch hno
      simp only [List.filter, hs]
      exact ih hall.2
  have hnil : (flatMapTraitImpls narrow).filter (fun e => stringEq e.traitRef.defPath dp) = [] :=
    hgen _ h
  conv => rhs; rw [List.filter_append, hnil, List.append_nil]
  rfl

/-- Single batched VC call-cone + trait-impl + external-summary narrowing certificate checker
(`#cpp_vc_narrow`, `cl/1022801564`), checked in ONE `decide +kernel` call. The narrowed
environment is *determined by the certificate data*: `narrowCallees := selectByMask fullCallees
mask` and `hoistedExtra := hoistTraitImpls fullCallees extra`. Checks:
1. `bodyCallsInConePoly cone rootBody` and `(coneBodies cone fullCallees).all (bodyCallsInConePoly cone)`
   (closed direct/polymorphic/trait-method call cone),
2. `checkMaskKeepsFirstMatch` (first-match `findCallee?` agreement, incl. duplicate shadowing),
3. `checkTraitImplConeClosed` (every `TraitImplEntry` target of a cone path is in the cone and
   has a body in the narrowed table),
4. `checkKeptCarryNoConeTraitImpls` (hoisting cannot duplicate cone dispatch records),
5. `checkUntrustedAdmissible` + `checkExternalSummariesAgreeOn` (external contracts). -/
def checkBatchedVcConeNarrowCert (cone : List DefPath) (rootBody : CapturedMir)
    (fullCallees : List CapturedMir) (mask : List Bool) (extra : List TraitImplEntry)
    (fullExt narrowExt : ExternalSummaryEnv := []) : Bool :=
  bodyCallsInConePoly cone rootBody &&
    (coneBodies cone fullCallees).all (bodyCallsInConePoly cone) &&
    checkMaskKeepsFirstMatch cone fullCallees mask &&
    checkTraitImplConeClosed cone fullCallees (selectByMask fullCallees mask) extra &&
    checkKeptCarryNoConeTraitImpls cone (selectByMask fullCallees mask) &&
    checkUntrustedAdmissible fullCallees fullExt &&
    checkExternalSummariesAgreeOn cone fullExt narrowExt

/-- Propositional batched VC narrowing certificate for an arbitrary narrowed environment
`(narrowCallees, extra₂, narrowExt)`; `BatchedVcConeNarrowCert.ofCheck` derives *every* field from
the single Boolean `checkBatchedVcConeNarrowCert`. -/
structure BatchedVcConeNarrowCert (cone : List DefPath) (rootBody : CapturedMir)
    (fullCallees narrowCallees : List CapturedMir)
    (extra₁ extra₂ : List TraitImplEntry)
    (fullExt narrowExt : ExternalSummaryEnv := []) : Prop where
  rootInCone : bodyCallsInConePoly cone rootBody = true
  coneBodiesInCone : (coneBodies cone fullCallees).all (bodyCallsInConePoly cone) = true
  traitConeAgree : TraitConeAgreeOn cone fullCallees narrowCallees extra₁ extra₂
  untrustedAdmissible : ∀ ext ∈ fullExt, findCallee? fullCallees ext.defPath = none
  extAgree : ∀ dp ∈ cone, findExternalSummary? fullExt dp = findExternalSummary? narrowExt dp

/-- **Soundness of the single batched checker (`BatchedVcConeNarrowCert.ofCheck`)**. -/
theorem BatchedVcConeNarrowCert.ofCheck {cone : List DefPath} {rootBody : CapturedMir}
    {fullCallees : List CapturedMir} {mask : List Bool} {extra : List TraitImplEntry}
    {fullExt narrowExt : ExternalSummaryEnv}
    (h : checkBatchedVcConeNarrowCert cone rootBody fullCallees mask extra fullExt narrowExt = true) :
    BatchedVcConeNarrowCert cone rootBody fullCallees (selectByMask fullCallees mask)
      extra (hoistTraitImpls fullCallees extra) fullExt narrowExt := by
  unfold checkBatchedVcConeNarrowCert at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h_root, h_cone⟩, h_mask⟩, h_closed⟩, h_kept⟩, h_adm⟩, h_ext⟩ := h
  refine ⟨h_root, h_cone, ⟨calleesAgreeOn_selectByMask h_mask,
    fun dp hdp => traitFilter_hoist_eq h_kept hdp, traitImplConeClosed_imp h_closed⟩, ?_, ?_⟩
  · intro ext hext
    unfold checkUntrustedAdmissible at h_adm
    exact Option.isNone_iff_eq_none.mp (List.all_eq_true.mp h_adm ext hext)
  · intro dp hdp
    unfold checkExternalSummariesAgreeOn at h_ext
    exact of_decide_eq_true (List.all_eq_true.mp h_ext dp hdp)

/-- Mask-aware batched VC certificate checker (`checkBatchedVcConeNarrowCertMask`): uses
`checkMaskTraitPartition` and `hoistMaskTraitImpls` so kept cone bodies that carry their own
`TraitImplEntry` records (the standard `rustc-capture` layout) are certified without duplicating
dispatch records. -/
def checkBatchedVcConeNarrowCertMask (cone : List DefPath) (rootBody : CapturedMir)
    (fullCallees : List CapturedMir) (mask : List Bool) (extra : List TraitImplEntry)
    (fullExt narrowExt : ExternalSummaryEnv := []) : Bool :=
  bodyCallsInConePoly cone rootBody &&
    (coneBodies cone fullCallees).all (bodyCallsInConePoly cone) &&
    checkMaskKeepsFirstMatch cone fullCallees mask &&
    checkTraitImplConeClosed cone fullCallees (selectByMask fullCallees mask) extra &&
    checkMaskTraitPartition cone fullCallees mask &&
    checkUntrustedAdmissible fullCallees fullExt &&
    checkExternalSummariesAgreeOn cone fullExt narrowExt

/-- **Soundness of the mask-aware batched checker (`BatchedVcConeNarrowCert.ofCheckMask`)**:
derives `BatchedVcConeNarrowCert` with `hoistMaskTraitImpls fullCallees mask extra`, supporting
both dropped carrier bodies and kept `impl` bodies carrying `TraitImplEntry` records. -/
theorem BatchedVcConeNarrowCert.ofCheckMask {cone : List DefPath} {rootBody : CapturedMir}
    {fullCallees : List CapturedMir} {mask : List Bool} {extra : List TraitImplEntry}
    {fullExt narrowExt : ExternalSummaryEnv}
    (h : checkBatchedVcConeNarrowCertMask cone rootBody fullCallees mask extra fullExt narrowExt = true) :
    BatchedVcConeNarrowCert cone rootBody fullCallees (selectByMask fullCallees mask)
      extra (hoistMaskTraitImpls fullCallees mask extra) fullExt narrowExt := by
  unfold checkBatchedVcConeNarrowCertMask at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h_root, h_cone⟩, h_mask⟩, h_closed⟩, h_part⟩, h_adm⟩, h_ext⟩ := h
  refine ⟨h_root, h_cone, ⟨calleesAgreeOn_selectByMask h_mask,
    fun dp hdp => traitFilter_hoistMask_eq h_part hdp, traitImplConeClosed_imp h_closed⟩, ?_, ?_⟩
  · intro ext hext
    unfold checkUntrustedAdmissible at h_adm
    exact Option.isNone_iff_eq_none.mp (List.all_eq_true.mp h_adm ext hext)
  · intro dp hdp
    unfold checkExternalSummariesAgreeOn at h_ext
    exact of_decide_eq_true (List.all_eq_true.mp h_ext dp hdp)

theorem BatchedVcConeNarrowCert.toTraitConeAgreeOn {cone : List DefPath} {rootBody : CapturedMir}
    {fullCallees narrowCallees : List CapturedMir} {extra₁ extra₂ : List TraitImplEntry}
    {fullExt narrowExt : ExternalSummaryEnv}
    (h : BatchedVcConeNarrowCert cone rootBody fullCallees narrowCallees extra₁ extra₂ fullExt narrowExt) :
    TraitConeAgreeOn cone fullCallees narrowCallees extra₁ extra₂ :=
  h.traitConeAgree

/-- `lookupCallee` equivalence from a `BatchedVcConeNarrowCert` across all cone call keys. -/
theorem lookupCallee_eq_of_batchedCert {cone : List DefPath} {rootBody : CapturedMir}
    {fullCallees narrowCallees : List CapturedMir} {extra₁ extra₂ : List TraitImplEntry}
    {fullExt narrowExt : ExternalSummaryEnv}
    (h : BatchedVcConeNarrowCert cone rootBody fullCallees narrowCallees extra₁ extra₂ fullExt narrowExt)
    (layouts : LayoutTable) {dp : DefPath} (h_dp : dp ∈ cone) (typeArgs : List RigidTy) :
    lookupCallee fullCallees layouts dp typeArgs extra₁ =
      lookupCallee narrowCallees layouts dp typeArgs extra₂ :=
  lookupCallee_eq_of_traitConeAgreeOn layouts typeArgs h.toTraitConeAgreeOn h_dp

/-- Entry-state invariant shared by the narrowing theorems. -/
theorem closedInvPoly_entry {cone : List DefPath} {rootBody : CapturedMir}
    {fullCallees : List CapturedMir} {extra₁ : List TraitImplEntry} {s : MachineState}
    (h_callees : s.memory.callees = fullCallees) (h_traits : s.memory.traitImpls = extra₁)
    (h_ac : s.memory.activeCallee = none) (h_cs : s.memory.callStack = []) :
    ClosedInvPoly cone rootBody fullCallees extra₁ s := by
  refine ⟨h_callees, h_traits, ?_, ?_⟩
  · rw [h_ac]; exact Or.inl rfl
  · intro f hf; rw [h_cs] at hf; nomatch hf

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
  have h_inv : ClosedInvPoly cone rootBody fullCallees extra₁ s :=
    closedInvPoly_entry h_callees h_traits h_ac h_cs
  have h_reach := coneReach_of_closedInvTrait h_cert.rootInCone h_cert.coneBodiesInCone
    h_cert.traitConeAgree.2.2 fuel s h_inv
  have h_at : TraitAgreesAt cone narrowCallees extra₂ (.running s) := by
    intro s' hs'
    cases hs'
    rw [h_callees, h_traits]
    exact h_cert.toTraitConeAgreeOn
  exact runMirExecBounded_trait_cone_narrow cone rootBody narrowCallees extra₂ fuel
    (.running s) h_reach h_at

/-- **Core Symbolic WP Narrowing Theorem (`wpMirExecSym_narrow_of_batchedCert`)**. -/
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
  have h_inv : ClosedInvPoly cone rootBody fullCallees extra₁ s :=
    closedInvPoly_entry h_callees h_traits h_ac h_cs
  have h_reach := coneReach_of_closedInvTrait h_cert.rootInCone h_cert.coneBodiesInCone
    h_cert.traitConeAgree.2.2 fuel s h_inv
  have h_at : TraitAgreesAt cone narrowCallees extra₂ (.running s) := by
    intro s' hs'
    cases hs'
    rw [h_callees, h_traits]
    exact h_cert.toTraitConeAgreeOn
  exact wpMirExecSym_trait_cone_narrow cone rootBody narrowCallees extra₂ post h_post fuel
    (.running s) h_reach h_at

/-! #### Contract-Aware Verification Conditions (`vcMirWithCallees`) -/

/-- Interpretation of external call contracts: `contracts tag req ans` holds when answer `ans` to
request `req` satisfies the summary contract identified by `tag`. -/
abbrev ExternalContractInterp := Nat → MirCallReq → MirCallAns → Prop

/-- External summary lookup restricted to the call cone (summaries outside the cone are never
trusted; a reachable external call outside the cone is havoc'd, which is conservative). -/
def coneSummary? (cone : List DefPath) (extEnv : ExternalSummaryEnv) (dp : DefPath) :
    Option ExternalCallSummary :=
  if inCone cone dp then findExternalSummary? extEnv dp else none

/-- `evalNodeWP` (`SymbolicEval`) with external-call answers restricted by cone summaries: an
external call to `dp` with summary `s` only considers answers satisfying `contracts s.summaryTag`;
without a summary every answer is considered (havoc), exactly as in `wpMirExecSym`. -/
def evalNodeWPExt (contracts : ExternalContractInterp) (cone : List DefPath)
    (extEnv : ExternalSummaryEnv) (cont : MirExecState → Prop) (post : MirOutcome → Prop) :
    MirStepNode → Prop
  | .ret out => post out
  | .tau st' => cont st'
  | .vis (.inl _) _ => False
  | .vis (.inr (.inl _)) k => cont (k PUnit.unit)
  | .vis (.inr (.inr (.call req))) k =>
    match coneSummary? cone extEnv req.defPath with
    | some s => ∀ ans : MirCallAns, contracts s.summaryTag req ans → cont (k ans)
    | none => ∀ ans : MirCallAns, cont (k ans)

/-- Fuel-bounded contract-aware WP over `MirExecState`. -/
def wpMirExecExt (contracts : ExternalContractInterp) (cone : List DefPath)
    (extEnv : ExternalSummaryEnv) : Nat → CapturedMir → MirExecState → (MirOutcome → Prop) → Prop
  | 0, _, _, _ => False
  | fuel + 1, body, st, post =>
    evalNodeWPExt contracts cone extEnv (fun st' => wpMirExecExt contracts cone extEnv fuel body st' post)
      post (stepMirState body st)

/-- With no summaries, the contract-aware WP is exactly `wpMirExecSym`. -/
theorem wpMirExecExt_nil_iff (contracts : ExternalContractInterp) (cone : List DefPath)
    (body : CapturedMir) (post : MirOutcome → Prop) :
    ∀ (fuel : Nat) (st : MirExecState),
      wpMirExecExt contracts cone [] fuel body st post ↔ wpMirExecSym fuel body st post
  | 0, _ => Iff.rfl
  | fuel + 1, st => by
    rw [wpMirExecSym_succ_eq]
    show evalNodeWPExt contracts cone [] _ post (stepMirState body st) ↔ _
    cases stepMirState body st with
    | ret out => exact Iff.rfl
    | tau st' => exact wpMirExecExt_nil_iff contracts cone body post fuel st'
    | vis e k =>
      rcases e with fk | obs | ⟨req⟩
      · exact Iff.rfl
      · exact wpMirExecExt_nil_iff contracts cone body post fuel (k PUnit.unit)
      · cases req with | call req => ?_
        have hnone : coneSummary? cone [] req.defPath = none := by
          unfold coneSummary?
          split <;> rfl
        show (match coneSummary? cone [] req.defPath with
          | some s => ∀ ans, contracts s.summaryTag req ans → wpMirExecExt contracts cone [] fuel body (k ans) post
          | none => ∀ ans, wpMirExecExt contracts cone [] fuel body (k ans) post) ↔
          ∀ ans, wpMirExecSym fuel body (k ans) post
        rw [hnone]
        exact forall_congr' (fun ans => wpMirExecExt_nil_iff contracts cone body post fuel (k ans))

/-- Summaries only weaken the obligation: the havoc WP implies the contract-aware WP. -/
theorem wpMirExecExt_of_wpMirExecSym (contracts : ExternalContractInterp) (cone : List DefPath)
    (extEnv : ExternalSummaryEnv) (body : CapturedMir) (post : MirOutcome → Prop) :
    ∀ (fuel : Nat) (st : MirExecState),
      wpMirExecSym fuel body st post → wpMirExecExt contracts cone extEnv fuel body st post
  | 0, _, h => h
  | fuel + 1, st, h => by
    rw [wpMirExecSym_succ_eq] at h
    show evalNodeWPExt contracts cone extEnv _ post (stepMirState body st)
    revert h
    cases stepMirState body st with
    | ret out => exact id
    | tau st' => exact wpMirExecExt_of_wpMirExecSym contracts cone extEnv body post fuel st'
    | vis e k =>
      rcases e with fk | obs | ⟨req⟩
      · exact id
      · exact wpMirExecExt_of_wpMirExecSym contracts cone extEnv body post fuel (k PUnit.unit)
      · cases req with | call req => ?_
        intro h
        show match coneSummary? cone extEnv req.defPath with
          | some s => ∀ ans, contracts s.summaryTag req ans → wpMirExecExt contracts cone extEnv fuel body (k ans) post
          | none => ∀ ans, wpMirExecExt contracts cone extEnv fuel body (k ans) post
        cases coneSummary? cone extEnv req.defPath with
        | some _ =>
          exact fun ans _ => wpMirExecExt_of_wpMirExecSym contracts cone extEnv body post fuel (k ans) (h ans)
        | none =>
          exact fun ans => wpMirExecExt_of_wpMirExecSym contracts cone extEnv body post fuel (k ans) (h ans)

/-- A run that terminates without external calls (`runMirExecBounded = some out`) discharges
the contract-aware WP exactly when `post out` holds (sufficiency). -/
theorem wpMirExecExt_of_run (contracts : ExternalContractInterp) (cone : List DefPath)
    (extEnv : ExternalSummaryEnv) (body : CapturedMir) (post : MirOutcome → Prop) :
    ∀ (fuel : Nat) (st : MirExecState) (out : MirOutcome),
      runMirExecBounded fuel body st = some out → post out →
      wpMirExecExt contracts cone extEnv fuel body st post
  | 0, _, _, h, _ => nomatch h
  | fuel + 1, st, out, h, hp => by
    show evalNodeWPExt contracts cone extEnv _ post (stepMirState body st)
    unfold runMirExecBounded at h
    revert h
    cases stepMirState body st with
    | ret o => intro h; cases h; exact hp
    | tau st' => exact fun h => wpMirExecExt_of_run contracts cone extEnv body post fuel st' out h hp
    | vis e k =>
      rcases e with fk | obs | c
      · intro h; nomatch h
      · exact fun h => wpMirExecExt_of_run contracts cone extEnv body post fuel (k PUnit.unit) out h hp
      · intro h; nomatch h

/-- ... and necessity: the WP of a terminating external-call-free run implies `post out`. -/
theorem post_of_wpMirExecExt_run (contracts : ExternalContractInterp) (cone : List DefPath)
    (extEnv : ExternalSummaryEnv) (body : CapturedMir) (post : MirOutcome → Prop) :
    ∀ (fuel : Nat) (st : MirExecState) (out : MirOutcome),
      runMirExecBounded fuel body st = some out →
      wpMirExecExt contracts cone extEnv fuel body st post → post out
  | 0, _, _, h, _ => nomatch h
  | fuel + 1, st, out, h, hw => by
    change evalNodeWPExt contracts cone extEnv _ post (stepMirState body st) at hw
    unfold runMirExecBounded at h
    cases hs : stepMirState body st with
    | ret o =>
      rw [hs] at h hw
      cases h
      exact hw
    | tau st' =>
      rw [hs] at h hw
      exact post_of_wpMirExecExt_run contracts cone extEnv body post fuel st' out h hw
    | vis e k =>
      rw [hs] at h hw
      rcases e with fk | obs | c
      · nomatch h
      · exact post_of_wpMirExecExt_run contracts cone extEnv body post fuel (k PUnit.unit) out h hw
      · nomatch h

/-- Summary-environment congruence (on unmapped states, e.g. after an external call answer). -/
theorem wpMirExecExt_congr_ext (contracts : ExternalContractInterp) (cone : List DefPath)
    {ext₁ ext₂ : ExternalSummaryEnv} (h_ext : ∀ dp, coneSummary? cone ext₂ dp = coneSummary? cone ext₁ dp)
    (body : CapturedMir) (post : MirOutcome → Prop) :
    ∀ (fuel : Nat) (st : MirExecState),
      wpMirExecExt contracts cone ext₂ fuel body st post ↔ wpMirExecExt contracts cone ext₁ fuel body st post
  | 0, _ => Iff.rfl
  | fuel + 1, st => by
    show evalNodeWPExt contracts cone ext₂ _ post (stepMirState body st) ↔
      evalNodeWPExt contracts cone ext₁ _ post (stepMirState body st)
    cases stepMirState body st with
    | ret out => exact Iff.rfl
    | tau st' => exact wpMirExecExt_congr_ext contracts cone h_ext body post fuel st'
    | vis e k =>
      rcases e with fk | obs | ⟨req⟩
      · exact Iff.rfl
      · exact wpMirExecExt_congr_ext contracts cone h_ext body post fuel (k PUnit.unit)
      · cases req with | call req => ?_
        show (match coneSummary? cone ext₂ req.defPath with
          | some s => ∀ ans, contracts s.summaryTag req ans → wpMirExecExt contracts cone ext₂ fuel body (k ans) post
          | none => ∀ ans, wpMirExecExt contracts cone ext₂ fuel body (k ans) post) ↔
          (match coneSummary? cone ext₁ req.defPath with
          | some s => ∀ ans, contracts s.summaryTag req ans → wpMirExecExt contracts cone ext₁ fuel body (k ans) post
          | none => ∀ ans, wpMirExecExt contracts cone ext₁ fuel body (k ans) post)
        rw [h_ext req.defPath]
        cases coneSummary? cone ext₁ req.defPath with
        | some s =>
          exact forall_congr' (fun ans => imp_congr_right (fun _ =>
            wpMirExecExt_congr_ext contracts cone h_ext body post fuel (k ans)))
        | none =>
          exact forall_congr' (fun ans => wpMirExecExt_congr_ext contracts cone h_ext body post fuel (k ans))

/-- Trait-aware narrowing of the contract-aware WP (narrowing callees, trait impls, *and* the
external summary environment simultaneously). -/
theorem wpMirExecExt_trait_cone_narrow (cone : List DefPath) (body : CapturedMir)
    (c₂ : CalleeEnv) (ti₂ : List TraitImplEntry) (contracts : ExternalContractInterp)
    {ext₁ ext₂ : ExternalSummaryEnv} (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirOutcome.mapMem (Memory.withCalleesAndTraits c₂ ti₂) out) ↔ post out)
    (h_contract : ∀ tag req ans,
      contracts tag { req with memory := Memory.withCalleesAndTraits c₂ ti₂ req.memory } ans ↔
        contracts tag req ans)
    (h_ext : ∀ dp, coneSummary? cone ext₂ dp = coneSummary? cone ext₁ dp) :
    ∀ (fuel : Nat) (st : MirExecState),
      ConeReach body (StepConeSafeTrait cone body) fuel st →
      TraitAgreesAt cone c₂ ti₂ st →
      (wpMirExecExt contracts cone ext₂ fuel body
          (MirExecState.mapMem (Memory.withCalleesAndTraits c₂ ti₂) st) post ↔
        wpMirExecExt contracts cone ext₁ fuel body st post)
  | 0, _, _, _ => Iff.rfl
  | fuel + 1, .halted out, _, _ => h_post out
  | fuel + 1, .faulted _, _, _ => Iff.rfl
  | fuel + 1, .running s, h_reach, h_agree => by
    have h_ag := h_agree s rfl
    obtain ⟨h_safe, h_next⟩ := h_reach
    have h_step := stepMirFn_withCalleesAndTraits cone body s c₂ ti₂ h_ag h_safe
    have h_fix := stepMirFn_calleesAndTraits_preserved cone body s h_ag.2.2 h_safe
    show evalNodeWPExt contracts cone ext₂ _ post
        (stepMirFn body (MachineState.mapMem (Memory.withCalleesAndTraits c₂ ti₂) s)) ↔
      evalNodeWPExt contracts cone ext₁ _ post (stepMirFn body s)
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
      exact wpMirExecExt_trait_cone_narrow cone body c₂ ti₂ contracts post h_post h_contract h_ext
        fuel st' h_next (traitAgreesAt_succ h_ag h_tau_fix)
    | vis e k =>
      rcases e with fk | obs | ⟨req⟩
      · intro _ _; exact Iff.rfl
      · intro h_next h_fix
        have hk : k PUnit.unit =
            MirExecState.mapMem
              (Memory.withCalleesAndTraits s.memory.callees s.memory.traitImpls)
              (k PUnit.unit) :=
          congrFun (eq_of_heq (Trusted.ITree.ITreeF.vis.inj h_fix).2) PUnit.unit
        exact wpMirExecExt_trait_cone_narrow cone body c₂ ti₂ contracts post h_post h_contract h_ext
          fuel (k PUnit.unit) h_next (traitAgreesAt_succ h_ag hk)
      · cases req with | call req => ?_
        intro _ _
        show (match coneSummary? cone ext₂ req.defPath with
          | some s => ∀ ans, contracts s.summaryTag
              { req with memory := Memory.withCalleesAndTraits c₂ ti₂ req.memory } ans →
              wpMirExecExt contracts cone ext₂ fuel body (k ans) post
          | none => ∀ ans, wpMirExecExt contracts cone ext₂ fuel body (k ans) post) ↔
          (match coneSummary? cone ext₁ req.defPath with
          | some s => ∀ ans, contracts s.summaryTag req ans →
              wpMirExecExt contracts cone ext₁ fuel body (k ans) post
          | none => ∀ ans, wpMirExecExt contracts cone ext₁ fuel body (k ans) post)
        rw [h_ext req.defPath]
        cases coneSummary? cone ext₁ req.defPath with
        | some sm =>
          exact forall_congr' (fun ans => imp_congr (h_contract sm.summaryTag req ans)
            (wpMirExecExt_congr_ext contracts cone h_ext body post fuel (k ans)))
        | none =>
          exact forall_congr' (fun ans => wpMirExecExt_congr_ext contracts cone h_ext body post fuel (k ans))

/-- Verification condition: contract-aware WP of `rootBody` from `s` with callee table `callees`,
trait impls `traitImpls`, and external summaries `extEnv` (trusted only on `cone`). -/
def vcMirWithCallees (contracts : ExternalContractInterp) (fuel : Nat) (rootBody : CapturedMir)
    (s : MachineState) (callees : List CapturedMir) (traitImpls : List TraitImplEntry)
    (extEnv : ExternalSummaryEnv) (cone : List DefPath) (post : MirOutcome → Prop) : Prop :=
  wpMirExecExt contracts cone extEnv fuel rootBody
    (.running (MachineState.mapMem (Memory.withCalleesAndTraits callees traitImpls) s)) post

/-- **Combined VC + External-Contract Narrowing Theorem (`vcMirWithCallees_narrow_of_batchedCert`)**:
one `BatchedVcConeNarrowCert` narrows `Memory.callees`, `Memory.traitImpls` (hoisted), AND the
external summary environment, preserving the contract-aware VC for every postcondition and
contract interpretation insensitive to `Memory.callees` / `Memory.traitImpls`. -/
theorem vcMirWithCallees_narrow_of_batchedCert {cone : List DefPath} {rootBody : CapturedMir}
    {fullCallees narrowCallees : List CapturedMir} {extra₁ extra₂ : List TraitImplEntry}
    {fullExt narrowExt : ExternalSummaryEnv}
    (h_cert : BatchedVcConeNarrowCert cone rootBody fullCallees narrowCallees
      extra₁ extra₂ fullExt narrowExt)
    (contracts : ExternalContractInterp) (fuel : Nat) (s : MachineState)
    (h_callees : s.memory.callees = fullCallees)
    (h_traits : s.memory.traitImpls = extra₁)
    (h_ac : s.memory.activeCallee = none)
    (h_cs : s.memory.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirOutcome.mapMem (Memory.withCalleesAndTraits narrowCallees extra₂) out) ↔ post out)
    (h_contract : ∀ tag req ans,
      contracts tag { req with memory := Memory.withCalleesAndTraits narrowCallees extra₂ req.memory } ans ↔
        contracts tag req ans) :
    vcMirWithCallees contracts fuel rootBody s narrowCallees extra₂ narrowExt cone post ↔
      vcMirWithCallees contracts fuel rootBody s fullCallees extra₁ fullExt cone post := by
  have h_self : MachineState.mapMem (Memory.withCalleesAndTraits fullCallees extra₁) s = s := by
    cases s with
    | mk frame mem =>
      dsimp only [MachineState.mapMem, Memory.withCalleesAndTraits] at h_callees h_traits ⊢
      cases mem
      dsimp only at h_callees h_traits
      subst h_callees h_traits
      rfl
  have h_inv : ClosedInvPoly cone rootBody fullCallees extra₁ s :=
    closedInvPoly_entry h_callees h_traits h_ac h_cs
  have h_reach := coneReach_of_closedInvTrait h_cert.rootInCone h_cert.coneBodiesInCone
    h_cert.traitConeAgree.2.2 fuel s h_inv
  have h_at : TraitAgreesAt cone narrowCallees extra₂ (.running s) := by
    intro s' hs'
    cases hs'
    rw [h_callees, h_traits]
    exact h_cert.toTraitConeAgreeOn
  have h_ext : ∀ dp, coneSummary? cone narrowExt dp = coneSummary? cone fullExt dp := by
    intro dp
    unfold coneSummary?
    by_cases hin : inCone cone dp = true
    · simp only [hin, ↓reduceIte]
      exact (h_cert.extAgree dp (inCone_iff.mp hin)).symm
    · simp only [hin, Bool.false_eq_true, ↓reduceIte]
  unfold vcMirWithCallees
  rw [h_self]
  exact wpMirExecExt_trait_cone_narrow cone rootBody narrowCallees extra₂ contracts post h_post
    h_contract h_ext fuel (.running s) h_reach h_at

/-! #### Computing the Certificate (`collectTraitConeBodies`, `computeBatchedVcNarrowCert`) -/

/-- Direct `.fnDef` call targets of a body's `call` / `tailCall` terminators. -/
def bodyDirectCallTargets (b : CapturedMir) : List DefPath :=
  b.basicBlocks.filterMap (fun blk =>
    match blk.terminator.kind with
    | .call func _ _ _ _ => extractFnDefPath? func
    | .tailCall func _ => extractFnDefPath? func
    | _ => none)

/-- Order-preserving `DefPath` deduplication. -/
def dedupDefPaths (dps : List DefPath) : List DefPath :=
  dps.foldl (fun acc dp => if inCone acc dp then acc else acc ++ [dp]) []

/-- One cone-closure step: add the direct call targets of every cone body and the `implPath` of
every `TraitImplEntry` targeting a cone path. -/
def traitConeStep (fullCallees : List CapturedMir) (allTi : List TraitImplEntry)
    (cone : List DefPath) : List DefPath :=
  dedupDefPaths (cone ++ (coneBodies cone fullCallees).flatMap bodyDirectCallTargets ++
    allTi.filterMap (fun e => if inCone cone e.traitRef.defPath then some e.implPath else none))

/-- `collectTraitConeBodies`: fuel-bounded transitive call + trait-impl closure from `rootBody`
(the result is only a *candidate*; closure is re-checked by `checkBatchedVcConeNarrowCert`). -/
def collectTraitConeBodies (fuel : Nat) (rootBody : CapturedMir) (fullCallees : List CapturedMir)
    (extra : List TraitImplEntry) : List DefPath :=
  let allTi := extra ++ flatMapTraitImpls fullCallees
  (List.range fuel).foldl (fun cone _ => traitConeStep fullCallees allTi cone)
    (dedupDefPaths (bodyDirectCallTargets rootBody))

/-- Canonical certificate data `(cone, mask, narrowExt)`: keep every cone body, hoist all trait
impls, and restrict external summaries to the cone. -/
def computeBatchedVcNarrowCert (fuel : Nat) (rootBody : CapturedMir)
    (fullCallees : List CapturedMir) (extra : List TraitImplEntry) (fullExt : ExternalSummaryEnv) :
    List DefPath × List Bool × ExternalSummaryEnv :=
  let cone := collectTraitConeBodies fuel rootBody fullCallees extra
  (cone, fullCallees.map (fun b => inCone cone b.defPath),
    fullExt.filter (fun s => inCone cone s.defPath))

/-- The canonical mask keeps exactly `coneBodies`. -/
theorem selectByMask_coneMask (cone : List DefPath) :
    ∀ (full : List CapturedMir),
      selectByMask full (full.map (fun b => inCone cone b.defPath)) = coneBodies cone full
  | [] => rfl
  | c :: cs => by
    have ih := selectByMask_coneMask cone cs
    show selectByMask (c :: cs) (inCone cone c.defPath :: cs.map (fun b => inCone cone b.defPath)) =
      List.filter (fun b => inCone cone b.defPath) (c :: cs)
    cases hc : inCone cone c.defPath with
    | true =>
      show c :: selectByMask cs (cs.map (fun b => inCone cone b.defPath)) = _
      rw [ih]
      simp only [List.filter, hc]
      rfl
    | false =>
      show selectByMask cs (cs.map (fun b => inCone cone b.defPath)) = _
      rw [ih]
      simp only [List.filter, hc]
      rfl

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

/-- Initial machine state of `traitCallRootMir` with the full callee table. -/
def protoTraitInitState : MachineState :=
  MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir [] emptyMemory protoFullCallees

/-- Canonical keep-mask (`coneBodies`) of `protoFullCallees` over `protoTraitCone`. -/
def protoTraitMask : List Bool :=
  protoFullCallees.map (fun b => inCone protoTraitCone b.defPath)

/-- The single batched certificate check for `traitCallRootMir`, computed by
`computeBatchedVcNarrowCert` and discharged by ONE `decide +kernel`. -/
theorem protoTraitBatchedCert_check :
    computeBatchedVcNarrowCert 4 traitCallRootMir protoFullCallees [] [] =
      (protoTraitCone, protoTraitMask, []) ∧
    checkBatchedVcConeNarrowCert protoTraitCone traitCallRootMir protoFullCallees protoTraitMask
      [] [] [] = true := by
  decide +kernel

/-- Certificate for `(protoNaiveNarrowCallees, protoHoistedExtra)`, derived entirely from the
Boolean check via `BatchedVcConeNarrowCert.ofCheck`. -/
theorem protoTraitBatchedCert :
    BatchedVcConeNarrowCert protoTraitCone traitCallRootMir
      protoFullCallees protoNaiveNarrowCallees [] protoHoistedExtra [] [] := by
  have h := BatchedVcConeNarrowCert.ofCheck protoTraitBatchedCert_check.2
  rw [show selectByMask protoFullCallees protoTraitMask = protoNaiveNarrowCallees from
    selectByMask_coneMask protoTraitCone protoFullCallees] at h
  exact h

/-- **Canary 2 (`canary_traitDispatch_preserved_under_batchedVcNarrow`)**: under the computed and
kernel-checked certificate, the narrowed execution `(protoNaiveNarrowCallees, protoHoistedExtra)`
returns exactly `31 : u32` (derived from `runMirExecBounded_narrow_of_batchedCert`), and
`wpMirExecSym` is preserved. -/
theorem canary_traitDispatch_preserved_under_batchedVcNarrow :
    ((runMirExecBounded 12 traitCallRootMir
        (.running (MachineState.mapMem
          (Memory.withCalleesAndTraits protoNaiveNarrowCallees protoHoistedExtra)
          protoTraitInitState))).map
      (fun out => match out with | .normal (v, _) => some v | _ => none)) =
      some (some (Value.scalar ⟨31, 4⟩)) ∧
    (wpMirExecSym 12 traitCallRootMir
      (.running (MachineState.mapMem
        (Memory.withCalleesAndTraits protoNaiveNarrowCallees protoHoistedExtra) protoTraitInitState))
      (fun out => match out with | .normal (v, _) => v = Value.scalar ⟨31, 4⟩ | _ => False) ↔
    wpMirExecSym 12 traitCallRootMir (.running protoTraitInitState)
      (fun out => match out with | .normal (v, _) => v = Value.scalar ⟨31, 4⟩ | _ => False)) := by
  refine ⟨?_, ?_⟩
  · rw [runMirExecBounded_narrow_of_batchedCert protoTraitBatchedCert 12 protoTraitInitState
      rfl rfl rfl rfl, Option.map_map]
    have hfun : ((fun out => match out with | .normal (v, _) => some v | _ => none) ∘
        MirOutcome.mapMem (Memory.withCalleesAndTraits protoNaiveNarrowCallees protoHoistedExtra)) =
        (fun out => match out with | .normal (v, _) => some v | _ => none) := by
      funext out
      rcases out with ⟨v, m⟩ | _ | _ <;> rfl
    rw [hfun]
    rfl
  · exact wpMirExecSym_narrow_of_batchedCert protoTraitBatchedCert 12 protoTraitInitState
      rfl rfl rfl rfl
      (fun out => match out with | .normal (v, _) => v = Value.scalar ⟨31, 4⟩ | _ => False)
      (fun out => by rcases out with ⟨v, m⟩ | _ | _ <;> exact Iff.rfl)

/-- Same-shape duplicate shadow of `proto::poly` (same `defPath`, `argCount`, `typeParamCount`,
and block count as `protoPoly`, but returns `8` instead of `7`). -/
def protoPolyShadow : CapturedMir := protoLeaf "proto::poly" 8 1 []

/-- Full table in which `protoPoly` shadows `protoPolyShadow`. -/
def protoShadowFullCallees : List CapturedMir := protoPoly :: protoPolyShadow :: protoFullCallees

/-- Untrusted narrowing dropping the first `proto::poly` (index 0) but keeping the shadowed copy. -/
def protoShadowBadMask : List Bool := [false, true, false, false, false, false, false, true]

/-- **Negative Canary 1 (`canary_duplicateShadow_rejected`)**: exposing a shadowed duplicate of
the *same shape* (which changes the callee body that `findCallee?` returns) is rejected. -/
theorem canary_duplicateShadow_rejected :
    checkBatchedVcConeNarrowCert protoTraitCone traitCallRootMir protoShadowFullCallees
      protoShadowBadMask [] [] [] = false ∧
    findCallee? (selectByMask protoShadowFullCallees protoShadowBadMask) "proto::poly" =
      some protoPolyShadow ∧
    findCallee? protoShadowFullCallees "proto::poly" = some protoPoly := by
  refine ⟨by decide +kernel, rfl, rfl⟩

/-- **Negative Canary 2 (`canary_externalShadowsInternal_rejected`)**: an external summary that
shadows an internal callee violates `UntrustedAdmissible`; a summary injected for a cone path
on the narrowed side only violates summary agreement. -/
theorem canary_externalShadowsInternal_rejected :
    checkBatchedVcConeNarrowCert protoTraitCone traitCallRootMir protoFullCallees protoTraitMask []
      [⟨"proto::poly", 1⟩] [⟨"proto::poly", 1⟩] = false ∧
    checkBatchedVcConeNarrowCert protoTraitCone traitCallRootMir protoFullCallees protoTraitMask []
      [] [⟨"proto::Area::area", 3⟩] = false := by
  decide +kernel

/-- **Negative Canary 3 (`canary_missingTraitImplBody_rejected`)**: omitting the
`TraitImplEntry.implPath` target body (`protoCircleArea`) is rejected, as is keeping a body that
carries a cone-targeting `TraitImplEntry` under the unmasked `checkKeptCarryNoConeTraitImpls`
(where `hoistTraitImpls` would duplicate dispatch records). -/
theorem canary_missingTraitImplBody_rejected :
    checkBatchedVcConeNarrowCert protoTraitCone traitCallRootMir protoFullCallees
      [false, false, true, false, false, false] [] [] [] = false ∧
    checkBatchedVcConeNarrowCert protoTraitCone traitCallRootMir protoFullCallees
      [false, false, true, true, false, true] [] [] [] = false := by
  decide +kernel

/-- Real `rustc-capture`-style impl body (`<impl Area for Circle>::area`) that carries its OWN
`TraitImplEntry` (`protoAreaEntry`) in `c.traitImpls` (`rustc-capture/src/rustc_2026_06_01/mod.rs:1885`). -/
def protoCircleAreaWithTrait : CapturedMir :=
  protoLeaf "proto::<impl Area for Circle>::area" 31 0 [protoAreaEntry]

/-- Callee table in `rustc-capture` layout: the kept `impl` body `protoCircleAreaWithTrait` carries
`protoAreaEntry` directly, with filler callees outside the cone. -/
def protoRustcStyleCallees : List CapturedMir :=
  [protoFillerA, protoPoly, protoFillerB, protoCircleAreaWithTrait]

def protoRustcStyleMask : List Bool :=
  [false, true, false, true]

/-- **Positive Canary (`canary_keptBodyWithTraitImpl_accepted`)**: when a *kept* cone body
(`protoCircleAreaWithTrait`) carries its own `TraitImplEntry` (as in real `rustc-capture`),
the legacy `[adv B1]` `checkKeptCarryNoConeTraitImpls` rejects it (`= false`), whereas
`checkBatchedVcConeNarrowCertMask` + `hoistMaskTraitImpls` accepts it (`= true`) and certifies
narrowing via `BatchedVcConeNarrowCert.ofCheckMask` without duplicating dispatch records! -/
theorem canary_keptBodyWithTraitImpl_accepted :
    checkKeptCarryNoConeTraitImpls protoTraitCone
      (selectByMask protoRustcStyleCallees protoRustcStyleMask) = false ∧
    checkBatchedVcConeNarrowCertMask protoTraitCone traitCallRootMir
      protoRustcStyleCallees protoRustcStyleMask [] [] [] = true ∧
    hoistMaskTraitImpls protoRustcStyleCallees protoRustcStyleMask [] = [] ∧
    BatchedVcConeNarrowCert protoTraitCone traitCallRootMir
      protoRustcStyleCallees (selectByMask protoRustcStyleCallees protoRustcStyleMask)
      [] (hoistMaskTraitImpls protoRustcStyleCallees protoRustcStyleMask []) [] [] :=
  ⟨by decide +kernel, by decide +kernel, rfl,
    BatchedVcConeNarrowCert.ofCheckMask (by decide +kernel)⟩


/-- Root body `_0 = ext::rand() -> bb1; bb1: return` calling an *external* function that is
absent from `Memory.callees` (so `Trusted` semantics emits a `MirCallE` interaction). -/
def protoExtCallRootMir : CapturedMir :=
  { traitCallRootMir with
    defPath := "proto::ext_root"
    basicBlocks := [
      protoCallBlock "ext::rand" [] 1,
      { statements := [], terminator := ⟨.return_, "ret"⟩, isCleanup := false } ] }

def protoExtInitState : MachineState :=
  MirFuelFree.initMachineStateWithMemoryAndCallees protoExtCallRootMir [] emptyMemory []

def protoExtCone : List DefPath := ["ext::rand"]

/-- Contract `7`: `ext::rand` returns `5 : u32` and leaves memory unchanged. -/
def protoExtContracts : ExternalContractInterp := fun tag req ans =>
  tag = 7 ∧ ans = .returned (.scalar ⟨5, 4⟩) req.memory

def protoExtPost (out : MirOutcome) : Prop :=
  match out with
  | .normal (v, _) => v = Value.scalar ⟨5, 4⟩
  | _ => False

/-- First step of `protoExtCallRootMir`: the external `MirCallE` request and its continuation. -/
def protoExtStep : MirStepNode := stepMirState protoExtCallRootMir (.running protoExtInitState)

def protoExtReq : MirCallReq :=
  match protoExtStep with
  | .vis (.inr (.inr (.call req))) _ => req
  | _ => { defPath := "", args := [], memory := emptyMemory }

def protoExtCont : MirCallAns → MirExecState :=
  match protoExtStep with
  | .vis (.inr (.inr (.call _))) k => k
  | _ => fun _ => .faulted .ub

theorem protoExtStep_eq :
    protoExtStep = .vis (.inr (.inr (.call protoExtReq))) protoExtCont := rfl

/-- Final value after answering the external call with `ans`. -/
def protoExtResultAfter (ans : MirCallAns) : Option (Option Value) :=
  (runMirExecBounded 2 protoExtCallRootMir (protoExtCont ans)).map
    (fun out => match out with | .normal (v, _) => some v | _ => none)

/-- **External-contract canary (`canary_externalSummary_vc`)**: the external summary is *used*
by `vcMirWithCallees` (non-vacuity): with the cone summary `ext::rand ↦ 7` the VC
`result = 5` holds, while without any summary (havoc) the same VC is false, witnessed by the
answer `6`. -/
theorem canary_externalSummary_vc :
    protoExtReq.defPath = "ext::rand" ∧
    vcMirWithCallees protoExtContracts 3 protoExtCallRootMir protoExtInitState [] []
      [⟨"ext::rand", 7⟩] protoExtCone protoExtPost ∧
    ¬ vcMirWithCallees protoExtContracts 3 protoExtCallRootMir protoExtInitState [] []
      [] protoExtCone protoExtPost := by
  have h5 : protoExtResultAfter (.returned (.scalar ⟨5, 4⟩) protoExtReq.memory) =
      some (some (Value.scalar ⟨5, 4⟩)) := rfl
  have h6 : protoExtResultAfter (.returned (.scalar ⟨6, 4⟩) protoExtReq.memory) =
      some (some (Value.scalar ⟨6, 4⟩)) := rfl
  have hself : MachineState.mapMem (Memory.withCalleesAndTraits [] []) protoExtInitState =
      protoExtInitState := rfl
  refine ⟨rfl, ?_, ?_⟩
  · unfold vcMirWithCallees
    rw [hself]
    show evalNodeWPExt protoExtContracts protoExtCone [⟨"ext::rand", 7⟩] _ protoExtPost protoExtStep
    rw [protoExtStep_eq]
    show (match coneSummary? protoExtCone [⟨"ext::rand", 7⟩] protoExtReq.defPath with
      | some s => ∀ ans, protoExtContracts s.summaryTag protoExtReq ans →
          wpMirExecExt protoExtContracts protoExtCone [⟨"ext::rand", 7⟩] 2 protoExtCallRootMir
            (protoExtCont ans) protoExtPost
      | none => ∀ ans, wpMirExecExt protoExtContracts protoExtCone [⟨"ext::rand", 7⟩] 2
          protoExtCallRootMir (protoExtCont ans) protoExtPost)
    have hsum : coneSummary? protoExtCone [⟨"ext::rand", 7⟩] protoExtReq.defPath =
        some ⟨"ext::rand", 7⟩ := by decide +kernel
    rw [hsum]
    intro ans ⟨_, hans⟩
    subst hans
    unfold protoExtResultAfter at h5
    obtain ⟨out, hout, hv⟩ := Option.map_eq_some_iff.mp h5
    apply wpMirExecExt_of_run _ _ _ _ _ 2 _ out hout
    rcases out with ⟨v, m⟩ | _ | _
    · exact Option.some.inj hv
    · nomatch hv
    · nomatch hv
  · intro hvc
    unfold vcMirWithCallees at hvc
    rw [hself] at hvc
    change evalNodeWPExt protoExtContracts protoExtCone [] _ protoExtPost protoExtStep at hvc
    rw [protoExtStep_eq] at hvc
    have hnone : coneSummary? protoExtCone [] protoExtReq.defPath = none := by decide +kernel
    change (match coneSummary? protoExtCone [] protoExtReq.defPath with
      | some s => ∀ ans, protoExtContracts s.summaryTag protoExtReq ans →
          wpMirExecExt protoExtContracts protoExtCone [] 2 protoExtCallRootMir (protoExtCont ans) protoExtPost
      | none => ∀ ans, wpMirExecExt protoExtContracts protoExtCone [] 2 protoExtCallRootMir
          (protoExtCont ans) protoExtPost) at hvc
    rw [hnone] at hvc
    have hw := hvc (.returned (.scalar ⟨6, 4⟩) protoExtReq.memory)
    unfold protoExtResultAfter at h6
    obtain ⟨out, hout, hv⟩ := Option.map_eq_some_iff.mp h6
    have hp := post_of_wpMirExecExt_run _ _ _ _ _ 2 _ out hout hw
    rcases out with ⟨v, m⟩ | _ | _
    · have hv' : v = Value.scalar ⟨6, 4⟩ := Option.some.inj hv
      have hp' : v = Value.scalar ⟨5, 4⟩ := hp
      rw [hv'] at hp'
      nomatch hp'
    · nomatch hv
    · nomatch hv

/-- External contract interpretation integrating `@[irreducible] coerceValueAt`: contract `8`
stipulates that the external call returns a value `v` coerced at `.uint .u32` from raw bits `5`
(`coerceValueAt protoLayouts (.uint .u32) (.scalar ⟨5, 4⟩) = some v`) and preserves memory.
Because `coerceValueAt` is `@[irreducible]`, `whnf` will not unfold the layout/modulus logic
until rewritten by `coerceValueAt_u32`. -/
def protoCoercedExtContracts : ExternalContractInterp := fun tag req ans =>
  tag = 8 ∧ ∃ v, coerceValueAt protoLayouts (.uint .u32) (.scalar ⟨5, 4⟩) = some v ∧
    ans = .returned v req.memory

/-- **Coercion-integrated VC canary (`canary_coercedExternalSummary_vc`)**: connects
`@[irreducible] coerceValueAt` directly to `vcMirWithCallees` and `coerceValueAt_u32`. -/
theorem canary_coercedExternalSummary_vc :
    vcMirWithCallees protoCoercedExtContracts 3 protoExtCallRootMir protoExtInitState [] []
      [⟨"ext::rand", 8⟩] protoExtCone protoExtPost := by
  have h5 : protoExtResultAfter (.returned (.scalar ⟨5, 4⟩) protoExtReq.memory) =
      some (some (Value.scalar ⟨5, 4⟩)) := rfl
  have hself : MachineState.mapMem (Memory.withCalleesAndTraits [] []) protoExtInitState =
      protoExtInitState := rfl
  unfold vcMirWithCallees
  rw [hself]
  show evalNodeWPExt protoCoercedExtContracts protoExtCone [⟨"ext::rand", 8⟩] _ protoExtPost protoExtStep
  rw [protoExtStep_eq]
  have hsum : coneSummary? protoExtCone [⟨"ext::rand", 8⟩] protoExtReq.defPath =
      some ⟨"ext::rand", 8⟩ := by decide +kernel
  show (match coneSummary? protoExtCone [⟨"ext::rand", 8⟩] protoExtReq.defPath with
    | some s => ∀ ans, protoCoercedExtContracts s.summaryTag protoExtReq ans →
        wpMirExecExt protoCoercedExtContracts protoExtCone [⟨"ext::rand", 8⟩] 2 protoExtCallRootMir
          (protoExtCont ans) protoExtPost
    | none => ∀ ans, wpMirExecExt protoCoercedExtContracts protoExtCone [⟨"ext::rand", 8⟩] 2
        protoExtCallRootMir (protoExtCont ans) protoExtPost)
  rw [hsum]
  intro ans ⟨_, v, hcoerce, hans⟩
  rw [coerceValueAt_u32] at hcoerce
  injection hcoerce with hv_eq
  have hwrap : wrapScalarBits 5 (scalarModulus 4) = 5 := rfl
  rw [hwrap] at hv_eq
  subst hv_eq hans
  unfold protoExtResultAfter at h5
  obtain ⟨out, hout, hv⟩ := Option.map_eq_some_iff.mp h5
  apply wpMirExecExt_of_run _ _ _ _ _ 2 _ out hout
  rcases out with ⟨v, m⟩ | _ | _
  · exact Option.some.inj hv
  · nomatch hv
  · nomatch hv

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

/-- Per-frame caller-location metadata (`FrameLocMeta`, stacks are listed innermost frame first):
- `defPath`: frame function identity,
- `callSitePos`: span of the call terminator *in this frame's caller* that invoked this frame
  (`none` for an entry frame whose caller is not part of the interpreted stack),
- `isTrackCaller`: whether this frame's function carries `#[track_caller]`,
- `detailPolicy`: `-Zlocation-detail` policy of the crate owning this frame's body, applied to
  spans located inside this frame. -/
structure FrameLocMeta where
  defPath : DefPath
  callSitePos : Option SourceExpansionPos
  isTrackCaller : Bool
  detailPolicy : LocationDetailPolicy := {}
  deriving DecidableEq, Repr

/-- Bottom-up `find_closest_untracked_caller_location` walk (`rustc_const_eval`
`interpret/intrinsics/caller_location.rs`; Miri `caller_location_span`). `pos` is a span inside
the head frame: a `#[track_caller]` frame forwards the walk to its own call site (a span inside
the next frame out, so the *next* frame's redaction policy applies), while the first
non-`#[track_caller]` frame — or a `#[track_caller]` frame with no recorded call site — resolves
`pos` under its own crate's policy. `fallbackPol` redacts a call site lying in a caller outside
the captured stack. -/
def resolveCallerLocationAux (fallbackPol : LocationDetailPolicy) (pos : SourceExpansionPos) :
    List FrameLocMeta → SourceExpansionPos
  | [] => applyLocationDetailPolicy fallbackPol pos
  | f :: rest =>
    if f.isTrackCaller then
      match f.callSitePos with
      | some callerPos => resolveCallerLocationAux f.detailPolicy callerPos rest
      | none => applyLocationDetailPolicy f.detailPolicy pos
    else
      applyLocationDetailPolicy f.detailPolicy pos

/-- A `core::intrinsics::caller_location` call site: the span of the intrinsic call inside the
innermost frame plus the interpreted frame stack (innermost first). -/
structure CallerLocationSite where
  intrinsicPos : SourceExpansionPos
  frames : List FrameLocMeta
  deriving DecidableEq, Repr

/-- Effective (redacted) source position returned by `caller_location` at `site`. -/
def CallerLocationSite.resolve (site : CallerLocationSite) : SourceExpansionPos :=
  resolveCallerLocationAux {} site.intrinsicPos site.frames

/-- Top-down `trackCallerArg` propagation (`Miri/Interpreter/Call.lean:245-275`): pushing a
`#[track_caller]` frame whose call site is `p` replaces the propagated caller location by `p`,
so the location seen through a chain `tcChain` (innermost first) is the call site of its
outermost frame, or the intrinsic span itself for an empty chain. -/
def propagateTrackCallerTopDown (defaultPos : SourceExpansionPos)
    (tcChain : List FrameLocMeta) : SourceExpansionPos :=
  tcChain.foldl (fun pos f => f.callSitePos.getD pos) defaultPos

/-- Bottom-up walk = top-down propagation: across a chain of `#[track_caller]` frames with
recorded call sites, followed by a non-`#[track_caller]` frame `outer`, the walk returns the
outermost call site redacted under `outer`'s policy (the crate owning that span). -/
theorem resolveCallerLocationAux_eq_topDown :
    ∀ (tcChain : List FrameLocMeta) (outer : FrameLocMeta) (rest : List FrameLocMeta)
      (fallbackPol : LocationDetailPolicy) (pos : SourceExpansionPos),
      tcChain.all (fun f => f.isTrackCaller && f.callSitePos.isSome) = true →
      outer.isTrackCaller = false →
      resolveCallerLocationAux fallbackPol pos (tcChain ++ outer :: rest) =
        applyLocationDetailPolicy outer.detailPolicy (propagateTrackCallerTopDown pos tcChain)
  | [], outer, rest, fallbackPol, pos, _, h_out => by
    show resolveCallerLocationAux fallbackPol pos (outer :: rest) = _
    unfold resolveCallerLocationAux
    rw [h_out]
    rfl
  | f :: tcRest, outer, rest, fallbackPol, pos, h_tc, h_out => by
    rw [List.all_cons, Bool.and_eq_true, Bool.and_eq_true] at h_tc
    obtain ⟨⟨h_f, h_some⟩, h_rest⟩ := h_tc
    rw [List.cons_append]
    unfold resolveCallerLocationAux
    rw [h_f]
    cases hc : f.callSitePos with
    | none => rw [hc] at h_some; nomatch h_some
    | some p =>
      simp only [↓reduceIte]
      rw [resolveCallerLocationAux_eq_topDown tcRest outer rest f.detailPolicy p h_rest h_out]
      show applyLocationDetailPolicy outer.detailPolicy (propagateTrackCallerTopDown p tcRest) =
        applyLocationDetailPolicy outer.detailPolicy
          (tcRest.foldl (fun pos f => f.callSitePos.getD pos) (f.callSitePos.getD pos))
      rw [hc]
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

/-- Decode a `core::panic::Location<'static>` root allocation: a single relocation at offset `0`
(`file.ptr`, zero offset), `file.len : usize` at bytes `8..16`, `line : u32` at `16..20`, and
`col : u32` at `20..24`. Returns `(fileAllocId, fileLen, line, col)`. -/
def decodeLocationAlloc (locAlloc : CapturedAllocation) :
    Option (AllocId × Nat × UInt32 × UInt32) :=
  match locAlloc.relocations with
  | [(0, filePtr)] =>
    if filePtr.offsetBytes != 0 then
      none
    else
      match readU64Le? (locAlloc.bytes.drop 8), readU32Le? (locAlloc.bytes.drop 16),
          readU32Le? (locAlloc.bytes.drop 20) with
      | some fileLen, some line, some col => some (filePtr.allocId, fileLen, line, col)
      | _, _, _ => none
  | _ => none

/-- Decode exactly `fileLen` initialized filename bytes from a filename allocation. -/
def decodeFilenameAlloc (fileAlloc : CapturedAllocation) (fileLen : Nat) : Option (List UInt8) :=
  match decodeInitBytes? (fileAlloc.bytes.take fileLen) with
  | some fileBytes => if fileBytes.length == fileLen then some fileBytes else none
  | none => none

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
      match decodeLocationAlloc locAlloc with
      | none => none
      | some (fileId, fileLen, line, col) =>
        match lookupGlobalAlloc globals fileId with
        | none => none
        | some fileAlloc =>
          match decodeFilenameAlloc fileAlloc fileLen with
          | none => none
          | some fileBytes => some (fileBytes, line, col)

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

theorem lookupGlobalAlloc_append_of_absent {G R : List CapturedAllocation} {x : AllocId}
    (h : ∀ a ∈ G, a.allocId ≠ x) : lookupGlobalAlloc (G ++ R) x = lookupGlobalAlloc R x := by
  induction G with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.cons_append, lookupGlobalAlloc]
    rw [nat_beq_ne (h a (List.Mem.head _))]
    exact ih (fun a' hm => h a' (List.Mem.tail _ hm))

theorem lookupGlobalAlloc_snoc_self (globals : List CapturedAllocation) (alloc : CapturedAllocation)
    (h_fresh : ∀ a ∈ globals, a.allocId < alloc.allocId) :
    lookupGlobalAlloc (globals ++ [alloc]) alloc.allocId = some alloc := by
  rw [lookupGlobalAlloc_append_of_absent (fun a ha => Nat.ne_of_lt (h_fresh a ha))]
  simp only [lookupGlobalAlloc, nat_beq_self_raw]

theorem decodeLocationAlloc_mk (locId fileId : AllocId) (fileLen : Nat) (line col : UInt32)
    (h_len : fileLen < 4294967296) :
    decodeLocationAlloc (mkLocationAllocation locId fileId fileLen line col) =
      some (fileId, fileLen, line, col) := by
  unfold decodeLocationAlloc mkLocationAllocation
  dsimp only
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  have hdrop8 :
      ([some (0 : UInt8), some 0, some 0, some 0, some 0, some 0, some 0, some 0] ++
        u64LeBytes fileLen ++ u32LeBytes line.toNat ++ u32LeBytes col.toNat).drop 8 =
      u64LeBytes fileLen ++ (u32LeBytes line.toNat ++ u32LeBytes col.toNat) := rfl
  have hdrop16 :
      ([some (0 : UInt8), some 0, some 0, some 0, some 0, some 0, some 0, some 0] ++
        u64LeBytes fileLen ++ u32LeBytes line.toNat ++ u32LeBytes col.toNat).drop 16 =
      u32LeBytes line.toNat ++ u32LeBytes col.toNat := rfl
  have hdrop20 :
      ([some (0 : UInt8), some 0, some 0, some 0, some 0, some 0, some 0, some 0] ++
        u64LeBytes fileLen ++ u32LeBytes line.toNat ++ u32LeBytes col.toNat).drop 20 =
      u32LeBytes col.toNat ++ [] := by
    simp [List.append_nil]
    rfl
  rw [hdrop8, readU64Le_u64LeBytes h_len, hdrop16, readU32Le_u32LeBytes line,
    hdrop20, readU32Le_u32LeBytes col]

theorem decodeFilenameAlloc_mk (fileId : AllocId) (bs : List UInt8) :
    decodeFilenameAlloc (mkFilenameAllocation fileId bs) bs.length = some bs := by
  unfold decodeFilenameAlloc mkFilenameAllocation
  dsimp only
  have htake : (bs.map Option.some).take bs.length = bs.map Option.some :=
    List.take_of_length_le (by simp)
  rw [htake, decodeInitBytes?_map_some]
  dsimp only
  rw [nat_beq_self]
  rfl

/-- A `Location` root allocation and its filename allocation found in `G` decode to
`(bs, line, col)` through the returned `&'static Location`. -/
theorem readLocationFromGlobals_of_lookups {G : List CapturedAllocation} {locId fileId : AllocId}
    {bs : List UInt8} {line col : UInt32}
    (h_loc : lookupGlobalAlloc G locId =
      some (mkLocationAllocation locId fileId bs.length line col))
    (h_file : lookupGlobalAlloc G fileId = some (mkFilenameAllocation fileId bs))
    (h_len : bs.length < 4294967296) :
    readLocationFromGlobals G { allocId := locId, offsetBytes := 0 } = some (bs, line, col) := by
  unfold readLocationFromGlobals
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [h_loc]
  dsimp only
  rw [decodeLocationAlloc_mk _ _ _ _ _ h_len]
  dsimp only
  rw [h_file]
  dsimp only
  rw [decodeFilenameAlloc_mk]

/-- `Location` reads are stable under appending further global allocations. -/
theorem readLocationFromGlobals_append {G : List CapturedAllocation} (R : List CapturedAllocation)
    {p : ProvenancePtr} {x : List UInt8 × UInt32 × UInt32}
    (h : readLocationFromGlobals G p = some x) : readLocationFromGlobals (G ++ R) p = some x := by
  unfold readLocationFromGlobals at h ⊢
  by_cases hoff : (p.offsetBytes != 0) = true
  · simp only [hoff, ↓reduceIte] at h
    cases h
  · simp only [hoff, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hloc : lookupGlobalAlloc G p.allocId with
    | none =>
      rw [hloc] at h
      nomatch h
    | some la =>
      rw [hloc] at h
      rw [lookupGlobalAlloc_append_left hloc]
      dsimp only at h ⊢
      cases hdec : decodeLocationAlloc la with
      | none =>
        rw [hdec] at h
        nomatch h
      | some q =>
        obtain ⟨fid, flen, line, col⟩ := q
        rw [hdec] at h
        dsimp only at h ⊢
        cases hf : lookupGlobalAlloc G fid with
        | none =>
          rw [hf] at h
          nomatch h
        | some fa =>
          rw [hf] at h
          rw [lookupGlobalAlloc_append_left hf]
          exact h

/-- Demand-time `#[track_caller]` environment (`lean-miri#67` Schema 15), caching allocated
immutable filename `AllocId`s by their (post-redaction) byte content so multiple
`caller_location` calls from the same file share a single filename `CapturedAllocation` in
`Memory.globals`. -/
structure DemandCallerLocationEnv where
  fileCache : List (List UInt8 × AllocId) := []
  deriving DecidableEq, Repr

/-- Look up a cached filename `AllocId` by byte sequence. -/
def lookupFileCache? (fileBytes : List UInt8) : List (List UInt8 × AllocId) → Option AllocId
  | [] => none
  | (bs, id) :: rest => if listByteEq bs fileBytes then some id else lookupFileCache? fileBytes rest

/-- Joint fresh identifier frontier (`max mem.nextAllocId mem.nextTag`): in
`Trusted.Rustc.V2026_06_01.MirSemantics`, stack-reference provenance tags (`ProvenancePtr.tag =
ProvenancePtr.allocId`) are resolved via `lookupBorrow mem.borrows ptr.tag` *before*
`lookupGlobalAlloc mem.globals ptr.allocId`. Drawing demand-time `Location` / filename identifiers
from `max mem.nextAllocId mem.nextTag` and advancing **both** `nextAllocId` and `nextTag` ensures
that no `Location` pointer ever collides with a live or future stack borrow tag! -/
def nextFreshGlobalAndTagId (mem : Memory) : AllocId :=
  max mem.nextAllocId mem.nextTag

/-- Borrow-table-aware `&'static core::panic::Location` reader mirroring `Trusted` pointer
resolution (`Statements.lean:3944`, `Places.lean:9926`): checks `lookupBorrow mem.borrows
locPtr.tag` first (failing if a stack borrow shadows `locPtr.allocId`) and falls back to
`readLocationFromGlobals mem.globals locPtr`. -/
def readLocationBorrowAware (mem : Memory) (locPtr : ProvenancePtr) :
    Option (List UInt8 × UInt32 × UInt32) :=
  match lookupBorrow mem.borrows locPtr.tag with
  | some _ => none
  | none => readLocationFromGlobals mem.globals locPtr

/-- Demand-time `core::intrinsics::caller_location` evaluation (`lean-miri#67` Schema 15):
1. Resolves the effective redacted position of `site` (`CallerLocationSite.resolve`).
2. Reuses the cached filename `AllocId` if the (redacted) bytes were already materialized;
   otherwise allocates a fresh filename `CapturedAllocation`.
3. Allocates a fresh `Location` root `CapturedAllocation` per invocation (lean-miri
   `EvalCallerLocationConstruction.hook`: "never deduplicate same-span invocations") and returns
   the `&'static Location` pointer.
Fresh identifiers are drawn from `nextFreshGlobalAndTagId mem = max mem.nextAllocId mem.nextTag`,
and both `nextAllocId` and `nextTag` are advanced past every allocation made here, so neither
later global allocations nor stack borrow tags can collide with a materialized `Location`. -/
def evalDemandCallerLocation (env : DemandCallerLocationEnv) (site : CallerLocationSite)
    (mem : Memory) : DemandCallerLocationEnv × ProvenancePtr × Memory :=
  let effPos := site.resolve
  let baseId := nextFreshGlobalAndTagId mem
  match lookupFileCache? effPos.fileBytes env.fileCache with
  | some fileAllocId =>
    let locAllocId := baseId
    let locAlloc := mkLocationAllocation locAllocId fileAllocId
      effPos.fileBytes.length effPos.line effPos.column
    (env, { allocId := locAllocId, offsetBytes := 0 },
      { mem with
        nextAllocId := locAllocId + 1
        nextTag := locAllocId + 1
        globals := mem.globals ++ [locAlloc] })
  | none =>
    let fileAllocId := baseId
    let locAllocId := baseId + 1
    let fileAlloc := mkFilenameAllocation fileAllocId effPos.fileBytes
    let locAlloc := mkLocationAllocation locAllocId fileAllocId
      effPos.fileBytes.length effPos.line effPos.column
    ({ fileCache := (effPos.fileBytes, fileAllocId) :: env.fileCache },
      { allocId := locAllocId, offsetBytes := 0 },
      { mem with
        nextAllocId := locAllocId + 1
        nextTag := locAllocId + 1
        globals := mem.globals ++ [fileAlloc, locAlloc] })

/-- Eager pre-materialization baseline (pre-Schema 15): materializes filename + `Location`
allocations for all $S$ candidate call sites into `Memory.globals` before execution begins, even
if the program never panics or invokes `caller_location`. -/
def eagerInitAux (env : DemandCallerLocationEnv) (mem : Memory) :
    List CallerLocationSite → DemandCallerLocationEnv × List ProvenancePtr × Memory
  | [] => (env, [], mem)
  | site :: rest =>
    let r := evalDemandCallerLocation env site mem
    let r' := eagerInitAux r.1 r.2.2 rest
    (r'.1, r.2.1 :: r'.2.1, r'.2.2)

def eagerInitCallerLocations (sites : List CallerLocationSite) (mem₀ : Memory) :
    DemandCallerLocationEnv × List ProvenancePtr × Memory :=
  eagerInitAux {} mem₀ sites

/-! ### Demand-World Invariants -/

/-- Every global allocation identifier is below the next fresh identifier. -/
def GlobalsFresh (mem : Memory) : Prop :=
  ∀ a ∈ mem.globals, a.allocId < mem.nextAllocId

/-- Every stack borrow entry tag is below `mem.nextTag`. -/
def BorrowsFresh (mem : Memory) : Prop :=
  ∀ b ∈ mem.borrows, b.tag < mem.nextTag

/-- Every cached `(bytes, id)` filename entry is materialized in `globals`. -/
def FileCacheCoherent (env : DemandCallerLocationEnv) (globals : List CapturedAllocation) : Prop :=
  ∀ bs id, (bs, id) ∈ env.fileCache →
    lookupGlobalAlloc globals id = some (mkFilenameAllocation id bs)

def DemandLocInv (env : DemandCallerLocationEnv) (mem : Memory) : Prop :=
  GlobalsFresh mem ∧ FileCacheCoherent env mem.globals

theorem lookupBorrow_eq_none_of_lt {borrows : List BorrowEntry} {id : Nat}
    (h : ∀ b ∈ borrows, b.tag < id) : lookupBorrow borrows id = none := by
  induction borrows with
  | nil => rfl
  | cons b rest ih =>
    unfold lookupBorrow
    rw [nat_beq_ne (Nat.ne_of_lt (h b (List.Mem.head _)))]
    exact ih (fun b' hb' => h b' (List.Mem.tail _ hb'))

theorem listByteEq_sound : ∀ {a b : List UInt8}, listByteEq a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | x :: xs, y :: ys, h => by
    unfold listByteEq at h
    cases hb : Nat.beq x.toBitVec.toNat y.toBitVec.toNat with
    | false =>
      rw [hb] at h
      nomatch h
    | true =>
      rw [hb] at h
      have hxy : x = y :=
        UInt8.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true hb))
      rw [hxy, listByteEq_sound h]

theorem lookupFileCache?_sound {bs : List UInt8} {id : AllocId} :
    ∀ {cache : List (List UInt8 × AllocId)}, lookupFileCache? bs cache = some id → (bs, id) ∈ cache
  | [], h => nomatch h
  | (bs', id') :: rest, h => by
    unfold lookupFileCache? at h
    by_cases hb : listByteEq bs' bs = true
    · simp only [hb, ↓reduceIte, Option.some.injEq] at h
      subst h
      rw [listByteEq_sound hb]
      exact List.Mem.head _
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
      exact List.Mem.tail _ (lookupFileCache?_sound h)

/-- **Demand step soundness (`evalDemandCallerLocation_spec`)**: under the invariant, one
`caller_location` evaluation returns a pointer that dereferences to the resolved
`(fileBytes, line, column)`, re-establishes the invariant, and only *appends* to
`Memory.globals`. -/
theorem evalDemandCallerLocation_spec (env : DemandCallerLocationEnv) (site : CallerLocationSite)
    (mem : Memory) (h_inv : DemandLocInv env mem)
    (h_len : site.resolve.fileBytes.length < 4294967296) :
    readLocationFromGlobals (evalDemandCallerLocation env site mem).2.2.globals
        (evalDemandCallerLocation env site mem).2.1 =
      some (site.resolve.fileBytes, site.resolve.line, site.resolve.column) ∧
    DemandLocInv (evalDemandCallerLocation env site mem).1
      (evalDemandCallerLocation env site mem).2.2 ∧
    ∃ extra, (evalDemandCallerLocation env site mem).2.2.globals = mem.globals ++ extra := by
  obtain ⟨h_fresh, h_coh⟩ := h_inv
  have h_lt_base : ∀ a ∈ mem.globals, a.allocId < nextFreshGlobalAndTagId mem :=
    fun a ha => Nat.lt_of_lt_of_le (h_fresh a ha) (Nat.le_max_left _ _)
  have h_abs0 : ∀ a ∈ mem.globals, a.allocId ≠ nextFreshGlobalAndTagId mem :=
    fun a ha => Nat.ne_of_lt (h_lt_base a ha)
  have h_abs1 : ∀ a ∈ mem.globals, a.allocId ≠ nextFreshGlobalAndTagId mem + 1 :=
    fun a ha => Nat.ne_of_lt (Nat.lt_succ_of_lt (h_lt_base a ha))
  unfold evalDemandCallerLocation
  dsimp only
  generalize site.resolve = eff at h_len ⊢
  cases hc : lookupFileCache? eff.fileBytes env.fileCache with
  | some fid =>
    dsimp only
    have h_file : lookupGlobalAlloc mem.globals fid = some (mkFilenameAllocation fid eff.fileBytes) :=
      h_coh _ _ (lookupFileCache?_sound hc)
    refine ⟨?_, ⟨?_, ?_⟩, ⟨_, rfl⟩⟩
    · apply readLocationFromGlobals_of_lookups (fileId := fid) _ _ h_len
      · rw [lookupGlobalAlloc_append_of_absent h_abs0]
        simp only [lookupGlobalAlloc, mkLocationAllocation, nat_beq_self_raw]
      · exact lookupGlobalAlloc_append_left h_file
    · intro a ha
      rcases List.mem_append.mp ha with hG | hL
      · exact Nat.lt_succ_of_lt (h_lt_base a hG)
      · rw [List.mem_singleton] at hL
        subst hL
        exact Nat.lt_succ_self _
    · intro bs id hm
      exact lookupGlobalAlloc_append_left (h_coh bs id hm)
  | none =>
    dsimp only
    refine ⟨?_, ⟨?_, ?_⟩, ⟨_, rfl⟩⟩
    · apply readLocationFromGlobals_of_lookups (fileId := nextFreshGlobalAndTagId mem) _ _ h_len
      · rw [lookupGlobalAlloc_append_of_absent h_abs1]
        simp only [lookupGlobalAlloc, mkLocationAllocation, mkFilenameAllocation,
          nat_beq_self_raw, nat_beq_ne (Nat.ne_of_lt (Nat.lt_succ_self (nextFreshGlobalAndTagId mem)))]
      · rw [lookupGlobalAlloc_append_of_absent h_abs0]
        simp only [lookupGlobalAlloc, mkFilenameAllocation, nat_beq_self_raw]
    · intro a ha
      rcases List.mem_append.mp ha with hG | hL
      · exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt (h_lt_base a hG))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
        rcases hL with rfl | rfl
        · exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)
        · exact Nat.lt_succ_self _
    · intro bs id hm
      rcases List.mem_cons.mp hm with heq | hold
      · cases heq
        rw [lookupGlobalAlloc_append_of_absent h_abs0]
        simp only [lookupGlobalAlloc, mkFilenameAllocation, nat_beq_self_raw]
      · exact lookupGlobalAlloc_append_left (h_coh bs id hold)

/-- **Borrow-table-aware soundness (`evalDemandCallerLocation_borrowAware_spec`)**: when `mem`
satisfies both `DemandLocInv` and `BorrowsFresh`, the returned `Location` pointer has
`lookupBorrow = none` and dereferences through `readLocationBorrowAware` (`lookupBorrow` before
`lookupGlobalAlloc`) to the resolved `(fileBytes, line, column)`, while preserving `BorrowsFresh`. -/
theorem evalDemandCallerLocation_borrowAware_spec (env : DemandCallerLocationEnv)
    (site : CallerLocationSite) (mem : Memory)
    (h_inv : DemandLocInv env mem) (h_bf : BorrowsFresh mem)
    (h_len : site.resolve.fileBytes.length < 4294967296) :
    lookupBorrow (evalDemandCallerLocation env site mem).2.2.borrows
        (evalDemandCallerLocation env site mem).2.1.tag = none ∧
    readLocationBorrowAware (evalDemandCallerLocation env site mem).2.2
        (evalDemandCallerLocation env site mem).2.1 =
      some (site.resolve.fileBytes, site.resolve.line, site.resolve.column) ∧
    BorrowsFresh (evalDemandCallerLocation env site mem).2.2 := by
  have h_spec := (evalDemandCallerLocation_spec env site mem h_inv h_len).1
  have h_lt_base : ∀ b ∈ mem.borrows, b.tag < nextFreshGlobalAndTagId mem :=
    fun b hb => Nat.lt_of_lt_of_le (h_bf b hb) (Nat.le_max_right _ _)
  have h_borrows_eq : (evalDemandCallerLocation env site mem).2.2.borrows = mem.borrows := by
    unfold evalDemandCallerLocation; dsimp only; split <;> rfl
  have h_ptr_ge : nextFreshGlobalAndTagId mem ≤
      (evalDemandCallerLocation env site mem).2.1.tag := by
    unfold evalDemandCallerLocation; dsimp only [ProvenancePtr.tag]
    split
    · exact Nat.le_refl _
    · exact Nat.le_succ _
  have h_nextTag_gt : nextFreshGlobalAndTagId mem <
      (evalDemandCallerLocation env site mem).2.2.nextTag := by
    unfold evalDemandCallerLocation; dsimp only
    split
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)
  have h_none : lookupBorrow (evalDemandCallerLocation env site mem).2.2.borrows
      (evalDemandCallerLocation env site mem).2.1.tag = none := by
    rw [h_borrows_eq]
    exact lookupBorrow_eq_none_of_lt (fun b hb => Nat.lt_of_lt_of_le (h_lt_base b hb) h_ptr_ge)
  refine ⟨h_none, ?_, ?_⟩
  · unfold readLocationBorrowAware
    rw [h_none]
    exact h_spec
  · intro b hb
    rw [h_borrows_eq] at hb
    exact Nat.lt_trans (h_lt_base b hb) h_nextTag_gt

/-! ### Kernel Proof that Pure `evalStmt` Preserves `Memory` & `stepMirFn_extCallInCone` -/

/-- **Pure Statement Memory Frame Theorem (`evalStmt_pure_memory_eq`)**:
Every pure MIR statement (`Anneal.PureMirExec.isPureStatement stmt.kind = true`) evaluated on a
frame-free memory (`s.memory.borrows = []`, `s.memory.activeProtectors = []`) leaves the entire
`Memory` record strictly unchanged (`ns.memory = s.memory`) — hence preserving `Memory.globals`,
`Memory.nextAllocId`, and `Memory.nextTag` without any artificial field overwrite. Proved directly
from `Anneal.PureMirExec.evalStmt_toMachineState_eq_withMem_of_frameFree`. -/
theorem evalStmt_pure_memory_eq {s ns : MachineState} {stmt : Statement}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    (h_pure : Anneal.PureMirExec.isPureStatement stmt.kind = true)
    (h_borrows : s.memory.borrows = [])
    (h_prot : s.memory.activeProtectors = [])
    (h_step : evalStmt s stmt localDecls layouts = .tau (.running ns)) :
    ns.memory = s.memory := by
  have h_eq : s = (Anneal.PureMirExec.PureState.ofMachineState s).toMachineState s.memory := by
    cases s; rfl
  have h_stmt :=
    Anneal.PureMirExec.evalStmt_toMachineState_eq_withMem_of_frameFree
      (Anneal.PureMirExec.PureState.ofMachineState s) s.memory stmt localDecls layouts
      h_pure h_borrows h_prot
  rw [← h_eq, h_step] at h_stmt
  cases h_emp : evalStmt
      ((Anneal.PureMirExec.PureState.ofMachineState s).toMachineState emptyMemory)
      stmt localDecls layouts with
  | ret _ => rw [h_emp] at h_stmt; cases h_stmt
  | tau st' =>
    cases st' with
    | halted _ | faulted _ => rw [h_emp] at h_stmt; cases h_stmt
    | running s' =>
      rw [h_emp] at h_stmt
      dsimp only [Anneal.PureMirExec.MirStepNode.withMem,
        Anneal.PureMirExec.MirExecState.withMem] at h_stmt
      injection h_stmt with h_st
      injection h_st with h_ns
      rw [h_ns]
  | vis e _ =>
    rcases e with _ | _ | _ <;> (rw [h_emp] at h_stmt; cases h_stmt)

/-- Every external call (`MirCallE`) emitted by a `MirStepNode` targets a `DefPath` in `cone`. -/
def NodeExtCallInCone (cone : List DefPath) : MirStepNode → Prop
  | .vis (.inr (.inr (.call req))) _ => req.defPath ∈ cone
  | _ => True

private theorem evalForeignFrameDerefWrite_extCallInCone (cone : List DefPath) (s : MachineState)
    (locals₁ : List LocalSlot) (mem₁ : Memory) (dst : Place) (restProj : List ProjectionElem)
    (val : Value) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    NodeExtCallInCone cone
      (evalForeignFrameDerefWrite s locals₁ mem₁ dst restProj val localDecls layouts) := by
  unfold evalForeignFrameDerefWrite
  split <;> trivial

private theorem evalSetDiscriminantLocal_extCallInCone (cone : List DefPath) (s : MachineState)
    (loc : Local) (variantIdx : Nat) (fields : List Value) :
    NodeExtCallInCone cone (evalSetDiscriminantLocal s loc variantIdx fields) := by
  unfold evalSetDiscriminantLocal
  try dsimp only
  repeat' (first | trivial | split | (dsimp only))

private theorem evalSetDiscriminantDerefWrite_extCallInCone (cone : List DefPath) (s : MachineState)
    (locals₁ : List LocalSlot) (p : Place) (rest : List ProjectionElem) (newVal : Value)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    NodeExtCallInCone cone
      (evalSetDiscriminantDerefWrite s locals₁ p rest newVal localDecls layouts) := by
  unfold evalSetDiscriminantDerefWrite
  try dsimp only
  repeat' (first | trivial | exact evalForeignFrameDerefWrite_extCallInCone .. | split | (dsimp only))

private theorem evalFnEntryRetag_extCallInCone (cone : List DefPath) (s : MachineState)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (place : Place) (ptrVal : ProvenancePtr)
    (sz : Nat) (parentEntry : BorrowEntry) (locals' : List LocalSlot) :
    NodeExtCallInCone cone
      (evalFnEntryRetag s localDecls layouts place ptrVal sz parentEntry locals') := by
  unfold evalFnEntryRetag
  try dsimp only
  repeat' (first | trivial | split | (dsimp only))

private theorem evalNonFnEntryRetag_extCallInCone (cone : List DefPath) (retagKind : RetagKind)
    (s : MachineState) (localDecls : List LocalDecl) (layouts : LayoutTable) (place : Place)
    (ptrVal : ProvenancePtr) (sz : Nat) (parentEntry : BorrowEntry) (locals' : List LocalSlot) :
    NodeExtCallInCone cone
      (evalNonFnEntryRetag retagKind s localDecls layouts place ptrVal sz parentEntry locals') := by
  unfold evalNonFnEntryRetag
  try dsimp only
  repeat' (first | trivial | split | (dsimp only))

private theorem evalCopySingleDirect_extCallInCone (cone : List DefPath) (s : MachineState)
    (src dst : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry) (locals₃ : List LocalSlot) :
    NodeExtCallInCone cone
      (evalCopySingleDirect s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
        locals₃) := by
  unfold evalCopySingleDirect
  try dsimp only
  repeat' (first | trivial | split | (dsimp only))

private theorem commitCopyDstPlaceWrite_extCallInCone (cone : List DefPath) (s : MachineState)
    (dstPlace : Place) (dstTargetLocal : LocalIdx) (dstTag : Nat) (locals₃ : List LocalSlot)
    (newVal : Value) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    NodeExtCallInCone cone
      (commitCopyDstPlaceWrite s dstPlace dstTargetLocal dstTag locals₃ newVal localDecls
        layouts) := by
  unfold commitCopyDstPlaceWrite
  try dsimp only
  repeat' (first | trivial | split | (dsimp only))

private theorem evalCopyUnionBytes_extCallInCone (cone : List DefPath) (s : MachineState)
    (src dst : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (srcUnionOpt dstUnionOpt : Option UnionPlaceInfo) (n : Nat) (locals₃ : List LocalSlot) :
    NodeExtCallInCone cone
      (evalCopyUnionBytes s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
        srcUnionOpt dstUnionOpt n locals₃) := by
  unfold evalCopyUnionBytes
  try dsimp only
  repeat' (first | trivial | exact commitCopyDstPlaceWrite_extCallInCone .. | split | (dsimp only))

private theorem evalCopyNonOverlappingPermOk_extCallInCone (cone : List DefPath) (s : MachineState)
    (src dst : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry) (countBits : Nat)
    (locals₃ : List LocalSlot) :
    NodeExtCallInCone cone
      (Trusted.Rustc.V2026_06_01.MirSemantics.evalCopyNonOverlappingPermOk s src dst localDecls
        layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃) := by
  unfold Trusted.Rustc.V2026_06_01.MirSemantics.evalCopyNonOverlappingPermOk
  try dsimp only
  repeat' (first
    | trivial
    | exact evalCopySingleDirect_extCallInCone ..
    | exact evalCopyUnionBytes_extCallInCone ..
    | exact commitCopyDstPlaceWrite_extCallInCone ..
    | split
    | (dsimp only))

private theorem evalForeignFrameCopySingleDirect_extCallInCone (cone : List DefPath)
    (s : MachineState) (src dst : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry) (countBits : Nat)
    (locals₃ : List LocalSlot) :
    NodeExtCallInCone cone
      (evalForeignFrameCopySingleDirect s src dst localDecls layouts srcPtr dstPtr srcEntry
        dstEntry countBits locals₃) := by
  unfold evalForeignFrameCopySingleDirect
  try dsimp only
  repeat' (first | trivial | split | (dsimp only))

private theorem evalCopyNonOverlappingWithCount_extCallInCone (cone : List DefPath)
    (s : MachineState) (src dst : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcVal dstVal : Value) (countBits : Nat) (locals₃ : List LocalSlot) :
    NodeExtCallInCone cone
      (evalCopyNonOverlappingWithCount s src dst localDecls layouts srcVal dstVal countBits
        locals₃) := by
  unfold evalCopyNonOverlappingWithCount
  try dsimp only
  repeat' (first
    | trivial
    | exact evalCopyNonOverlappingPermOk_extCallInCone ..
    | exact evalForeignFrameCopySingleDirect_extCallInCone ..
    | split
    | (dsimp only))

private theorem evalCopyNonOverlapping_extCallInCone (cone : List DefPath) (s : MachineState)
    (src dst count : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    NodeExtCallInCone cone (evalCopyNonOverlapping s src dst count localDecls layouts) := by
  unfold evalCopyNonOverlapping
  try dsimp only
  repeat' (first
    | trivial
    | exact evalCopyNonOverlappingWithCount_extCallInCone ..
    | split
    | (dsimp only))

/-- **No MIR statement ever emits an external call (`evalStmt_extCallInCone`, `0` `Classical.choice`)**. -/
theorem evalStmt_extCallInCone (cone : List DefPath) (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    NodeExtCallInCone cone (evalStmt s stmt localDecls layouts) := by
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | intrinsic intr =>
    cases intr with
    | assume _ =>
      unfold evalStmt; dsimp only
      repeat' (first | trivial | split | (dsimp only))
    | copyNonOverlapping src dst count =>
      exact evalCopyNonOverlapping_extCallInCone cone s src dst count localDecls layouts
  | _ =>
    unfold evalStmt; dsimp only
    repeat' (first
      | trivial
      | exact evalFnEntryRetag_extCallInCone ..
      | exact evalNonFnEntryRetag_extCallInCone ..
      | exact evalSetDiscriminantLocal_extCallInCone ..
      | exact evalSetDiscriminantDerefWrite_extCallInCone ..
      | exact evalForeignFrameDerefWrite_extCallInCone ..
      | split
      | (dsimp only))

private theorem writeIntrinsicReturn_extCallInCone (cone : List DefPath) (s : MachineState)
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx) (retVal : Value) :
    NodeExtCallInCone cone (writeIntrinsicReturn s locals' destination targetBb retVal) := by
  unfold writeIntrinsicReturn
  try dsimp only
  repeat' (first | trivial | split)

private theorem writeIntrinsicScalarResult_extCallInCone (cone : List DefPath) (s : MachineState)
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx)
    (resOpt : Option ScalarInt) :
    NodeExtCallInCone cone (writeIntrinsicScalarResult s locals' destination targetBb resOpt) := by
  unfold writeIntrinsicScalarResult
  split
  · exact writeIntrinsicReturn_extCallInCone ..
  · trivial

private theorem intrinsicUnresolvedLayoutStep_extCallInCone (cone : List DefPath) (ty : RigidTy) :
    NodeExtCallInCone cone (intrinsicUnresolvedLayoutStep ty) := by
  unfold intrinsicUnresolvedLayoutStep
  split <;> trivial

private theorem intrinsicWidePointeeStep_extCallInCone (cone : List DefPath) (ty : RigidTy) :
    NodeExtCallInCone cone (intrinsicWidePointeeStep ty) := by
  unfold intrinsicWidePointeeStep
  split <;> trivial

private theorem intrinsicMissingPointeeStep_extCallInCone (cone : List DefPath)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable) (argOps : List Operand) :
    NodeExtCallInCone cone (intrinsicMissingPointeeStep bodyLocalDecls bodyLayouts argOps) := by
  unfold intrinsicMissingPointeeStep
  try dsimp only
  repeat' (first | trivial | split | (dsimp only))

private theorem evalNonSelectIntrinsicCall_extCallInCone (cone : List DefPath)
    (kind : RustIntrinsicKind) (s : MachineState) (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable) (argOps : List Operand)
    (argVals : List Value) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) :
    NodeExtCallInCone cone
      (evalNonSelectIntrinsicCall kind s target bodyLocalDecls bodyLayouts argOps argVals
        locals' destination targetBb) := by
  unfold evalNonSelectIntrinsicCall
  cases kind <;> dsimp only <;>
    repeat' (first
      | trivial
      | exact writeIntrinsicReturn_extCallInCone ..
      | exact writeIntrinsicScalarResult_extCallInCone ..
      | exact intrinsicUnresolvedLayoutStep_extCallInCone ..
      | exact intrinsicWidePointeeStep_extCallInCone ..
      | exact intrinsicMissingPointeeStep_extCallInCone ..
      | split)

/-- **Reachable external calls from `evalTerminator` stay in the cone
(`evalTerminator_extCallInCone`)**. -/
theorem evalTerminator_extCallInCone (cone : List DefPath) (s : MachineState)
    (term : Terminator) (cur : CapturedMir)
    (h_safe : TermConeSafeTrait cone s cur term) :
    NodeExtCallInCone cone (evalTerminator s term (some cur)) := by
  rcases term with ⟨kind, span⟩
  cases kind with
  | goto _ | unwindTerminate | unreachable => trivial
  | switchInt _ _ =>
    unfold evalTerminator; dsimp only
    repeat' (first | trivial | split)
  | unwindResume =>
    unfold evalTerminator; dsimp only
    cases unwindFromCallStack s.memory.callStack s.memory <;> trivial
  | return_ =>
    rw [ccEvalReturn_eq]
    unfold ccEvalReturn
    repeat' (first | trivial | split)
  | drop _ _ _ =>
    unfold evalTerminator; dsimp only
    repeat' (first | trivial | split)
  | assert _ _ _ _ =>
    unfold evalTerminator; dsimp only
    repeat' (first | trivial | split)
  | call func argOps destination target unwind =>
    have hq : CallTargetInConeTrait cone s cur func (length argOps) := h_safe
    cases target with
    | some targetBb =>
      unfold evalTerminator; dsimp only
      cases h_res : resolveCallTarget s func (length argOps)
          (bodyLocalDeclsOf (some cur)) cur.layouts with
      | ub | unsupported => trivial
      | ok tgt localsAfterFunc =>
        obtain ⟨h_dp, h_cl⟩ := hq tgt localsAfterFunc h_res
        dsimp only
        cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals cur.layouts
            s.memory.callerLocals (callStack := s.memory.callStack) with
        | ub | unsupported => trivial
        | ok argVals locals' =>
          dsimp only
          cases lookupCallee s.memory.callees cur.layouts tgt.defPath tgt.typeArgs
              s.memory.traitImpls with
          | some calleeBody =>
            dsimp only
            cases checkCalleeTargetCompatible tgt calleeBody (length argVals) <;> trivial
          | none =>
            dsimp only
            cases isDirectExactDivTarget tgt with
            | true => repeat' (first | trivial | exact writeIntrinsicReturn_extCallInCone .. | split)
            | false =>
              cases tgt.isIndirect with
              | true => exact h_dp
              | false =>
                unfold evalDirectRustIntrinsic?
                cases hk : classifyRustIntrinsic? tgt.defPath with
                | none => exact h_dp
                | some k =>
                  rw [hk] at h_cl
                  cases k with
                  | constEvalSelect => nomatch h_cl
                  | _ => exact evalNonSelectIntrinsicCall_extCallInCone ..
    | none =>
      unfold evalTerminator; dsimp only
      cases h_res : resolveCallTarget s func (length argOps)
          (bodyLocalDeclsOf (some cur)) cur.layouts with
      | ub | unsupported => trivial
      | ok tgt localsAfterFunc =>
        obtain ⟨h_dp, _⟩ := hq tgt localsAfterFunc h_res
        dsimp only
        cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals cur.layouts
            s.memory.callerLocals (callStack := s.memory.callStack) with
        | ub | unsupported => trivial
        | ok argVals locals' =>
          dsimp only
          repeat' (first | trivial | exact h_dp | split)
  | tailCall func argOps =>
    have hq : CallTargetInConeTrait cone s cur func (length argOps) := h_safe
    unfold evalTerminator evalTailCallTerminator; dsimp only
    cases h_res : resolveCallTarget s func (length argOps)
        (bodyLocalDeclsOf (some cur)) cur.layouts with
    | ub | unsupported => trivial
    | ok tgt localsAfterFunc =>
      obtain ⟨h_dp, _⟩ := hq tgt localsAfterFunc h_res
      dsimp only
      repeat' (first | trivial | exact h_dp | split)
  | _ => trivial

/-- **Every external call emitted by `stepMirFn` on a cone-safe state targets a `DefPath` in
`cone` (`stepMirFn_extCallInCone`)**, so `coneSummary? cone extEnv req.defPath =
findExternalSummary? extEnv req.defPath`! -/
theorem stepMirFn_extCallInCone (cone : List DefPath) (body : CapturedMir) (s : MachineState)
    (h_safe : StepConeSafeTrait cone body s) :
    NodeExtCallInCone cone (stepMirFn body s) := by
  unfold stepMirFn
  dsimp only
  split
  · trivial
  · cases h_bb : get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx with
    | none => trivial
    | some blk =>
      obtain ⟨_, h_term⟩ := h_safe blk h_bb
      dsimp only
      cases h_st : get? blk.statements s.frame.stmtIdx with
      | some stmt =>
        dsimp only
        exact evalStmt_extCallInCone cone s stmt
          (s.memory.activeCallee.getD body).localDecls (s.memory.activeCallee.getD body).layouts
      | none =>
        dsimp only
        split
        · exact evalTerminator_extCallInCone cone s blk.terminator _ h_term
        · trivial

theorem coneSummary?_eq_of_stepMirFn_extCall {cone : List DefPath} {body : CapturedMir}
    {s : MachineState} {req : MirCallReq} {k : MirCallAns → MirExecState}
    (extEnv : ExternalSummaryEnv)
    (h_safe : StepConeSafeTrait cone body s)
    (h_step : stepMirFn body s = .vis (.inr (.inr (.call req))) k) :
    coneSummary? cone extEnv req.defPath = findExternalSummary? extEnv req.defPath := by
  have h_in : req.defPath ∈ cone := by
    have := stepMirFn_extCallInCone cone body s h_safe
    rw [h_step] at this
    exact this
  unfold coneSummary?
  rw [inCone_iff.mpr h_in]
  rfl

/-! ### Trace Semantics: Plain, Demand-Time, and Eager Worlds -/

/-- Trace step: a normal MIR statement, or a `caller_location` intrinsic invocation at call site
`site` (an index into the program's `CallerLocationSite` table). -/
inductive CallerLocationTraceEvent where
  | normalStep (stmt : Statement)
  | invokeCallerLocation (site : Nat)

/-- Normal statement step shared by all three worlds: commits the frame/borrow transition of
`Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt`; on any pure statement and frame-free memory,
`normalStmtStep_eq_raw_of_pure` proves this is identical to the raw `evalStmt` transition with zero
field overwrites (`evalStmt_pure_memory_eq`). -/
def normalStmtStep (s : MachineState) (stmt : Statement) (localDecls : List LocalDecl)
    (layouts : LayoutTable) : MachineState :=
  match evalStmt s stmt localDecls layouts with
  | .tau (.running ns) =>
    { ns with memory := { ns.memory with globals := s.memory.globals, nextAllocId := s.memory.nextAllocId } }
  | _ => s

theorem normalStmtStep_eq_raw_of_pure (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_pure : Anneal.PureMirExec.isPureStatement stmt.kind = true)
    (h_borrows : s.memory.borrows = [])
    (h_prot : s.memory.activeProtectors = []) :
    normalStmtStep s stmt localDecls layouts =
      (match evalStmt s stmt localDecls layouts with
       | .tau (.running ns) => ns
       | _ => s) := by
  unfold normalStmtStep
  cases h_ev : evalStmt s stmt localDecls layouts with
  | ret _ | vis _ _ => rfl
  | tau st =>
    cases st with
    | halted _ | faulted _ => rfl
    | running ns =>
      have h_mem := evalStmt_pure_memory_eq h_pure h_borrows h_prot h_ev
      rcases ns with ⟨fr, mem⟩
      dsimp only at h_mem ⊢
      rw [h_mem]

theorem normalStmtStep_globals (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    (normalStmtStep s stmt localDecls layouts).memory.globals = s.memory.globals := by
  unfold normalStmtStep
  split <;> rfl

theorem normalStmtStep_nextAllocId (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    (normalStmtStep s stmt localDecls layouts).memory.nextAllocId = s.memory.nextAllocId := by
  unfold normalStmtStep
  split <;> rfl

/-- Plain execution with no `caller_location` machinery at all (invocations are ignored). -/
def runPlainTrace (s : MachineState) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    List CallerLocationTraceEvent → MachineState
  | [] => s
  | .normalStep stmt :: rest => runPlainTrace (normalStmtStep s stmt localDecls layouts) localDecls layouts rest
  | .invokeCallerLocation _ :: rest => runPlainTrace s localDecls layouts rest

/-- Demand-time world (`lean-miri#67`): allocates `Location` globals ONLY when a valid
`.invokeCallerLocation` event occurs, returning one pointer per such event. -/
def runDemandCallerLocationTrace (sites : List CallerLocationSite) (env : DemandCallerLocationEnv)
    (s : MachineState) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    List CallerLocationTraceEvent → DemandCallerLocationEnv × List ProvenancePtr × MachineState
  | [] => (env, [], s)
  | .normalStep stmt :: rest =>
    runDemandCallerLocationTrace sites env (normalStmtStep s stmt localDecls layouts)
      localDecls layouts rest
  | .invokeCallerLocation i :: rest =>
    match sites[i]? with
    | none => runDemandCallerLocationTrace sites env s localDecls layouts rest
    | some site =>
      let r := evalDemandCallerLocation env site s.memory
      let r' := runDemandCallerLocationTrace sites r.1 { s with memory := r.2.2 }
        localDecls layouts rest
      (r'.1, r.2.1 :: r'.2.1, r'.2.2)

/-- Eager world execution after pre-allocation: an invocation returns the pre-materialized
pointer of its call site without allocating. -/
def runEagerCallerLocationTrace (ePtrs : List ProvenancePtr) (s : MachineState)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    List CallerLocationTraceEvent → List ProvenancePtr × MachineState
  | [] => ([], s)
  | .normalStep stmt :: rest =>
    runEagerCallerLocationTrace ePtrs (normalStmtStep s stmt localDecls layouts)
      localDecls layouts rest
  | .invokeCallerLocation i :: rest =>
    match ePtrs[i]? with
    | none => runEagerCallerLocationTrace ePtrs s localDecls layouts rest
    | some p =>
      let r := runEagerCallerLocationTrace ePtrs s localDecls layouts rest
      (p :: r.1, r.2)

/-- Eager world: pre-allocate every call site, then run the trace. -/
def runEagerCallerLocationWorld (sites : List CallerLocationSite) (s : MachineState)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (trace : List CallerLocationTraceEvent) : List ProvenancePtr × MachineState :=
  let init := eagerInitCallerLocations sites s.memory
  runEagerCallerLocationTrace init.2.1 { s with memory := init.2.2 } localDecls layouts trace

/-- Call sites actually invoked (valid indices only) along a trace. -/
def invokedSites (sites : List CallerLocationSite) : List CallerLocationTraceEvent → List CallerLocationSite
  | [] => []
  | .normalStep _ :: rest => invokedSites sites rest
  | .invokeCallerLocation i :: rest =>
    match sites[i]? with
    | none => invokedSites sites rest
    | some site => site :: invokedSites sites rest

/-- Expected dereferenced `(fileBytes, line, column)` of a call site. -/
def expectedLocation (site : CallerLocationSite) : Option (List UInt8 × UInt32 × UInt32) :=
  some (site.resolve.fileBytes, site.resolve.line, site.resolve.column)

/-- Observations made through returned `&'static Location` pointers. -/
def readLocations (globals : List CapturedAllocation) (ptrs : List ProvenancePtr) :
    List (Option (List UInt8 × UInt32 × UInt32)) :=
  ptrs.map (readLocationFromGlobals globals)

/-- All call sites have `usize`-encodable (`< 2^32` in this layout) filename lengths. -/
def SitesFileLenOk (sites : List CallerLocationSite) : Prop :=
  ∀ site ∈ sites, site.resolve.fileBytes.length < 4294967296

/-- Predicate stating that a trace contains zero `.invokeCallerLocation` events. -/
def traceHasNoCallerLocation : List CallerLocationTraceEvent → Bool
  | [] => true
  | .normalStep _ :: rest => traceHasNoCallerLocation rest
  | .invokeCallerLocation _ :: _ => false

theorem demandLocInv_normalStmtStep {env : DemandCallerLocationEnv} {s : MachineState}
    (stmt : Statement) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h : DemandLocInv env s.memory) :
    DemandLocInv env (normalStmtStep s stmt localDecls layouts).memory := by
  unfold DemandLocInv GlobalsFresh FileCacheCoherent at *
  rw [normalStmtStep_globals, normalStmtStep_nextAllocId]
  exact h

/-- Multi-step demand-world soundness: every returned pointer dereferences (in the *final*
globals) to its call site's resolved location; the invariant is preserved and globals only grow. -/
theorem runDemandCallerLocationTrace_spec (sites : List CallerLocationSite)
    (h_sites : SitesFileLenOk sites) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    ∀ (trace : List CallerLocationTraceEvent) (env : DemandCallerLocationEnv) (s : MachineState),
      DemandLocInv env s.memory →
      readLocations (runDemandCallerLocationTrace sites env s localDecls layouts trace).2.2.memory.globals
          (runDemandCallerLocationTrace sites env s localDecls layouts trace).2.1 =
        (invokedSites sites trace).map expectedLocation ∧
      DemandLocInv (runDemandCallerLocationTrace sites env s localDecls layouts trace).1
        (runDemandCallerLocationTrace sites env s localDecls layouts trace).2.2.memory ∧
      ∃ extra, (runDemandCallerLocationTrace sites env s localDecls layouts trace).2.2.memory.globals =
        s.memory.globals ++ extra
  | [], env, s, h_inv => ⟨rfl, h_inv, ⟨[], (List.append_nil _).symm⟩⟩
  | .normalStep stmt :: rest, env, s, h_inv => by
    have ih := runDemandCallerLocationTrace_spec sites h_sites localDecls layouts rest env
      (normalStmtStep s stmt localDecls layouts) (demandLocInv_normalStmtStep stmt localDecls layouts h_inv)
    rw [normalStmtStep_globals] at ih
    exact ih
  | .invokeCallerLocation i :: rest, env, s, h_inv => by
    unfold runDemandCallerLocationTrace invokedSites
    cases hsite : sites[i]? with
    | none =>
      exact runDemandCallerLocationTrace_spec sites h_sites localDecls layouts rest env s h_inv
    | some site =>
      dsimp only
      have h_mem : site ∈ sites := List.mem_of_getElem? hsite
      obtain ⟨h_read, h_inv', ⟨e₁, h_g₁⟩⟩ :=
        evalDemandCallerLocation_spec env site s.memory h_inv (h_sites site h_mem)
      obtain ⟨ih_read, ih_inv, ⟨e₂, h_g₂⟩⟩ :=
        runDemandCallerLocationTrace_spec sites h_sites localDecls layouts rest
          (evalDemandCallerLocation env site s.memory).1
          { s with memory := (evalDemandCallerLocation env site s.memory).2.2 } h_inv'
      refine ⟨?_, ih_inv, ⟨e₁ ++ e₂, ?_⟩⟩
      · show readLocationFromGlobals _ _ :: readLocations _ _ = expectedLocation site :: _
        rw [ih_read, h_g₂, readLocationFromGlobals_append e₂ h_read]
        rfl
      · rw [h_g₂]
        show (evalDemandCallerLocation env site s.memory).2.2.globals ++ e₂ = _
        rw [h_g₁, List.append_assoc]

/-- Eager pre-allocation soundness: one pointer per site, each dereferencing to its resolved
location in the eager globals. -/
theorem eagerInitAux_spec :
    ∀ (sites : List CallerLocationSite) (env : DemandCallerLocationEnv) (mem : Memory),
      DemandLocInv env mem → SitesFileLenOk sites →
      readLocations (eagerInitAux env mem sites).2.2.globals (eagerInitAux env mem sites).2.1 =
          sites.map expectedLocation ∧
        (eagerInitAux env mem sites).2.1.length = sites.length ∧
        DemandLocInv (eagerInitAux env mem sites).1 (eagerInitAux env mem sites).2.2 ∧
        ∃ extra, (eagerInitAux env mem sites).2.2.globals = mem.globals ++ extra
  | [], env, mem, h_inv, _ => ⟨rfl, rfl, h_inv, ⟨[], (List.append_nil _).symm⟩⟩
  | site :: rest, env, mem, h_inv, h_sites => by
    unfold eagerInitAux
    dsimp only
    obtain ⟨h_read, h_inv', ⟨e₁, h_g₁⟩⟩ :=
      evalDemandCallerLocation_spec env site mem h_inv (h_sites site (List.Mem.head _))
    obtain ⟨ih_read, ih_len, ih_inv, ⟨e₂, h_g₂⟩⟩ :=
      eagerInitAux_spec rest (evalDemandCallerLocation env site mem).1
        (evalDemandCallerLocation env site mem).2.2 h_inv'
        (fun st hst => h_sites st (List.Mem.tail _ hst))
    refine ⟨?_, ?_, ih_inv, ⟨e₁ ++ e₂, ?_⟩⟩
    · show readLocationFromGlobals _ _ :: readLocations _ _ = expectedLocation site :: _
      rw [ih_read, h_g₂, readLocationFromGlobals_append e₂ h_read]
      rfl
    · show (eagerInitAux _ _ rest).2.1.length + 1 = rest.length + 1
      rw [ih_len]
    · show (eagerInitAux _ _ rest).2.2.globals = _
      rw [h_g₂, h_g₁, List.append_assoc]

/-- Eager-world execution never allocates: globals stay fixed and every invocation observes its
pre-materialized pointer. -/
theorem runEagerCallerLocationTrace_spec (sites : List CallerLocationSite)
    (ePtrs : List ProvenancePtr) (G : List CapturedAllocation)
    (h_map : readLocations G ePtrs = sites.map expectedLocation)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    ∀ (trace : List CallerLocationTraceEvent) (s : MachineState), s.memory.globals = G →
      readLocations G (runEagerCallerLocationTrace ePtrs s localDecls layouts trace).1 =
          (invokedSites sites trace).map expectedLocation ∧
        (runEagerCallerLocationTrace ePtrs s localDecls layouts trace).2.memory.globals = G
  | [], s, h_g => ⟨rfl, h_g⟩
  | .normalStep stmt :: rest, s, h_g =>
    runEagerCallerLocationTrace_spec sites ePtrs G h_map localDecls layouts rest
      (normalStmtStep s stmt localDecls layouts) (by rw [normalStmtStep_globals]; exact h_g)
  | .invokeCallerLocation i :: rest, s, h_g => by
    have h_idx : (ePtrs[i]?).map (readLocationFromGlobals G) = (sites[i]?).map expectedLocation := by
      have := congrArg (fun l => l[i]?) h_map
      simp only [readLocations, List.getElem?_map] at this
      exact this
    have ih := runEagerCallerLocationTrace_spec sites ePtrs G h_map localDecls layouts rest s h_g
    unfold runEagerCallerLocationTrace invokedSites
    cases hp : ePtrs[i]? with
    | none =>
      rw [hp] at h_idx
      cases hs : sites[i]? with
      | none => exact ih
      | some _ => rw [hs] at h_idx; nomatch h_idx
    | some p =>
      rw [hp] at h_idx
      cases hs : sites[i]? with
      | none => rw [hs] at h_idx; nomatch h_idx
      | some site =>
        rw [hs] at h_idx
        dsimp only
        refine ⟨?_, ih.2⟩
        show readLocationFromGlobals G p :: readLocations G _ = expectedLocation site :: _
        rw [ih.1]
        exact congrArg (· :: _) (Option.some.inj h_idx)

/-- **Observational Bisimulation (`demandCallerLocation_bisim_eager`)**: for EVERY call-site
table (arbitrary `#[track_caller]` forwarding chains and arbitrary per-crate
`LocationDetailPolicy` among all 8 combinations), EVERY trace (panicking or not, with any number
of repeated invocations), and every initial state with fresh globals, the demand-time world and
the eager pre-allocated world observe exactly the same `(fileBytes, line, column)` through every
returned `&'static core::panic::Location`, namely the resolved location of each invoked site. -/
theorem demandCallerLocation_bisim_eager (sites : List CallerLocationSite) (s₀ : MachineState)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (trace : List CallerLocationTraceEvent)
    (h_fresh : GlobalsFresh s₀.memory) (h_sites : SitesFileLenOk sites) :
    readLocations (runDemandCallerLocationTrace sites {} s₀ localDecls layouts trace).2.2.memory.globals
        (runDemandCallerLocationTrace sites {} s₀ localDecls layouts trace).2.1 =
      readLocations (runEagerCallerLocationWorld sites s₀ localDecls layouts trace).2.memory.globals
        (runEagerCallerLocationWorld sites s₀ localDecls layouts trace).1 ∧
    readLocations (runDemandCallerLocationTrace sites {} s₀ localDecls layouts trace).2.2.memory.globals
        (runDemandCallerLocationTrace sites {} s₀ localDecls layouts trace).2.1 =
      (invokedSites sites trace).map expectedLocation := by
  have h_inv₀ : DemandLocInv {} s₀.memory := ⟨h_fresh, fun _ _ h => nomatch h⟩
  have h_d := (runDemandCallerLocationTrace_spec sites h_sites localDecls layouts trace {} s₀ h_inv₀).1
  obtain ⟨h_init, _, _, _⟩ := eagerInitAux_spec sites {} s₀.memory h_inv₀ h_sites
  have h_e := runEagerCallerLocationTrace_spec sites (eagerInitCallerLocations sites s₀.memory).2.1
    (eagerInitCallerLocations sites s₀.memory).2.2.globals h_init localDecls layouts trace
    { s₀ with memory := (eagerInitCallerLocations sites s₀.memory).2.2 } rfl
  refine ⟨?_, h_d⟩
  unfold runEagerCallerLocationWorld
  dsimp only
  rw [h_d, h_e.2, h_e.1]

/-- **Zero-Clutter Theorem (`demandCallerLocation_no_call_zero_allocs`)**: on any trace that does
not invoke `caller_location`, the demand-time world is *identical* (`=`) to plain execution with no
`Location` machinery: same environment, no pointers, same final `MachineState` (hence the same
`Memory.globals` and `nextAllocId` as the initial state). -/
theorem demandCallerLocation_no_call_zero_allocs (sites : List CallerLocationSite)
    (env : DemandCallerLocationEnv) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    ∀ (trace : List CallerLocationTraceEvent) (s : MachineState),
      traceHasNoCallerLocation trace = true →
      runDemandCallerLocationTrace sites env s localDecls layouts trace =
          (env, [], runPlainTrace s localDecls layouts trace) ∧
        (runPlainTrace s localDecls layouts trace).memory.globals = s.memory.globals ∧
        (runPlainTrace s localDecls layouts trace).memory.nextAllocId = s.memory.nextAllocId
  | [], _, _ => ⟨rfl, rfl, rfl⟩
  | .normalStep stmt :: rest, s, h => by
    obtain ⟨h₁, h₂, h₃⟩ := demandCallerLocation_no_call_zero_allocs sites env localDecls layouts
      rest (normalStmtStep s stmt localDecls layouts) h
    refine ⟨h₁, ?_, ?_⟩
    · show (runPlainTrace (normalStmtStep s stmt localDecls layouts) localDecls layouts rest).memory.globals = _
      rw [h₂, normalStmtStep_globals]
    · show (runPlainTrace (normalStmtStep s stmt localDecls layouts) localDecls layouts rest).memory.nextAllocId = _
      rw [h₃, normalStmtStep_nextAllocId]
  | .invokeCallerLocation _ :: _, _, h => nomatch h

/-- Exact eager clutter: pre-allocation adds one `Location` per call site plus one filename
allocation per distinct (redacted) filename (`globals.length = G₀ + S + #files`). -/
theorem eagerInitAux_globals_length :
    ∀ (sites : List CallerLocationSite) (env : DemandCallerLocationEnv) (mem : Memory),
      (eagerInitAux env mem sites).2.2.globals.length + env.fileCache.length =
        mem.globals.length + sites.length + (eagerInitAux env mem sites).1.fileCache.length
  | [], env, mem => by
    show mem.globals.length + env.fileCache.length = mem.globals.length + 0 + env.fileCache.length
    rw [Nat.add_zero]
  | site :: rest, env, mem => by
    have ih := eagerInitAux_globals_length rest (evalDemandCallerLocation env site mem).1
      (evalDemandCallerLocation env site mem).2.2
    show (eagerInitAux _ _ rest).2.2.globals.length + env.fileCache.length =
      mem.globals.length + (rest.length + 1) + (eagerInitAux _ _ rest).1.fileCache.length
    have hstep : (evalDemandCallerLocation env site mem).2.2.globals.length +
        env.fileCache.length =
        mem.globals.length + 1 + (evalDemandCallerLocation env site mem).1.fileCache.length := by
      unfold evalDemandCallerLocation
      dsimp only
      split <;> simp only [List.length_append, List.length_cons, List.length_nil] <;> omega
    omega

/-- Eager world on a non-panicking trace: no observations, yet `Memory.globals` carries
`G₀ + S + #files` pre-materialized allocations for the whole run. -/
theorem eagerCallerLocation_clutter (sites : List CallerLocationSite) (s₀ : MachineState)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (trace : List CallerLocationTraceEvent)
    (h : traceHasNoCallerLocation trace = true) :
    (runEagerCallerLocationWorld sites s₀ localDecls layouts trace).1 = [] ∧
      (runEagerCallerLocationWorld sites s₀ localDecls layouts trace).2.memory.globals.length =
        s₀.memory.globals.length + sites.length +
          (eagerInitCallerLocations sites s₀.memory).1.fileCache.length := by
  have hno : ∀ (ePtrs : List ProvenancePtr) (tr : List CallerLocationTraceEvent) (s : MachineState),
      traceHasNoCallerLocation tr = true →
      (runEagerCallerLocationTrace ePtrs s localDecls layouts tr).1 = [] ∧
        (runEagerCallerLocationTrace ePtrs s localDecls layouts tr).2.memory.globals =
          s.memory.globals := by
    intro ePtrs tr
    induction tr with
    | nil => intro s _; exact ⟨rfl, rfl⟩
    | cons ev rest ih =>
      intro s hev
      cases ev with
      | normalStep stmt =>
        obtain ⟨h₁, h₂⟩ := ih (normalStmtStep s stmt localDecls layouts) hev
        exact ⟨h₁, h₂.trans (normalStmtStep_globals s stmt localDecls layouts)⟩
      | invokeCallerLocation _ => nomatch hev
  obtain ⟨h₁, h₂⟩ := hno (eagerInitCallerLocations sites s₀.memory).2.1 trace
    { s₀ with memory := (eagerInitCallerLocations sites s₀.memory).2.2 } h
  refine ⟨h₁, ?_⟩
  unfold runEagerCallerLocationWorld
  dsimp only
  rw [h₂]
  have := eagerInitAux_globals_length sites {} s₀.memory
  unfold eagerInitCallerLocations
  simpa using this

/-! ### Explicit `AllocId` Renaming (`AllocRenamingRel`) -/

/-- Explicit `AllocId` relocation map (`ren : List (AllocId × AllocId)`), relating demand-time
`AllocId`s to eager-world `AllocId`s (first match wins; unmapped ids are fixed). -/
def relocateAllocId (ren : List (AllocId × AllocId)) (id : AllocId) : AllocId :=
  match ren.find? (fun p => p.1 == id) with
  | some (_, id') => id'
  | none => id

def relocatePtr (ren : List (AllocId × AllocId)) (p : ProvenancePtr) : ProvenancePtr :=
  { p with allocId := relocateAllocId ren p.allocId }

/-- Relocate every `ProvenancePtr.allocId` inside a `Value`. -/
def relocateValue (ren : List (AllocId × AllocId)) : Value → Value
  | .unit => .unit
  | .scalar sc => .scalar sc
  | .ptr p sz => .ptr (relocatePtr ren p) sz
  | .aggregate vIdx fields => .aggregate vIdx (fields.map (relocateValue ren))

/-- Constructive duplicate-free check on `List Nat` (via `natListContains`, `Nat.beq`). -/
def nodupNat : List Nat → Bool
  | [] => true
  | x :: xs => !(natListContains x xs) && nodupNat xs

/-- Injective partial bijection predicate on `ren : List (AllocId × AllocId)`. -/
def AllocRenamingWf (ren : List (AllocId × AllocId)) : Bool :=
  let dom := ren.map Prod.fst
  let cod := ren.map Prod.snd
  nodupNat dom && nodupNat cod

/-- Observational equivalence of two `(globals, locPtr)` pairs. -/
def LocationPtrObsEq (globals₁ : List CapturedAllocation) (ptr₁ : ProvenancePtr)
    (globals₂ : List CapturedAllocation) (ptr₂ : ProvenancePtr) : Prop :=
  readLocationFromGlobals globals₁ ptr₁ = readLocationFromGlobals globals₂ ptr₂

/-- `AllocRenamingRel` between demand-time and eager `Memory` states over returned `Location`
pointers: an injective renaming `ren` maps every demand pointer to its eager counterpart, and the
two dereference to identical `(fileBytes, line, column)`. Injectivity of the *codomain* holds
exactly when no call site is invoked twice: lean-miri allocates a fresh `Location` per
invocation, while the eager world has one per site. -/
structure AllocRenamingRel (ren : List (AllocId × AllocId))
    (memDemand memEager : Memory)
    (demandPtrs eagerPtrs : List ProvenancePtr) : Prop where
  wf : AllocRenamingWf ren = true
  ptrsMapped : eagerPtrs = demandPtrs.map (relocatePtr ren)
  obsAgree :
    ∀ p ∈ demandPtrs,
      LocationPtrObsEq memDemand.globals p memEager.globals (relocatePtr ren p)

/-- Positional renaming from demand-time `Location` ids to eager-world `Location` ids. -/
def renamingOfPtrs (ds es : List ProvenancePtr) : List (AllocId × AllocId) :=
  List.zip (ds.map (·.allocId)) (es.map (·.allocId))

theorem relocateAllocId_cons (a b x : AllocId) (ren : List (AllocId × AllocId)) :
    relocateAllocId ((a, b) :: ren) x = if a == x then b else relocateAllocId ren x := by
  unfold relocateAllocId
  rw [List.find?_cons]
  cases a == x <;> rfl

theorem not_mem_of_natListContains_eq_false {x : Nat} :
    ∀ {xs : List Nat}, natListContains x xs = false → x ∉ xs
  | [], _, hm => nomatch hm
  | y :: ys, h, hm => by
    unfold natListContains at h
    cases hb : Nat.beq x y with
    | true => rw [hb] at h; nomatch h
    | false =>
      rw [hb] at h
      rcases List.mem_cons.mp hm with heq | htl
      · subst heq
        rw [nat_beq_self_raw] at hb
        nomatch hb
      · exact not_mem_of_natListContains_eq_false h htl

theorem renamingOfPtrs_mapped :
    ∀ (ds es : List ProvenancePtr), ds.length = es.length →
      nodupNat (ds.map (·.allocId)) = true →
      (∀ p ∈ ds, p.offsetBytes = 0) → (∀ p ∈ es, p.offsetBytes = 0) →
      es = ds.map (relocatePtr (renamingOfPtrs ds es))
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _ => nomatch h
  | _ :: _, [], h, _, _, _ => nomatch h
  | d :: ds, e :: es, h_len, h_nd, h_offD, h_offE => by
    unfold nodupNat at h_nd
    rw [List.map_cons, Bool.and_eq_true] at h_nd
    have h_notin : d.allocId ∉ ds.map (·.allocId) := by
      apply not_mem_of_natListContains_eq_false
      cases hc : natListContains d.allocId (ds.map (·.allocId)) with
      | false => rfl
      | true => rw [hc] at h_nd; nomatch h_nd.1
    have ih := renamingOfPtrs_mapped ds es (Nat.succ.inj h_len) h_nd.2
      (fun p hp => h_offD p (List.Mem.tail _ hp)) (fun p hp => h_offE p (List.Mem.tail _ hp))
    show e :: es = relocatePtr ((d.allocId, e.allocId) :: renamingOfPtrs ds es) d ::
      ds.map (relocatePtr ((d.allocId, e.allocId) :: renamingOfPtrs ds es))
    have h_head : relocatePtr ((d.allocId, e.allocId) :: renamingOfPtrs ds es) d = e := by
      have hd : d.offsetBytes = 0 := h_offD _ (List.Mem.head _)
      have he : e.offsetBytes = 0 := h_offE _ (List.Mem.head _)
      generalize renamingOfPtrs ds es = ren
      rcases e with ⟨eid, eoff⟩
      rcases d with ⟨did, doff⟩
      dsimp only at hd he
      subst hd
      subst he
      show ({ allocId := relocateAllocId ((did, eid) :: ren) did, offsetBytes := 0 } :
        ProvenancePtr) = ⟨eid, 0⟩
      rw [relocateAllocId_cons, nat_beq_self]
      rfl
    have h_tail : ds.map (relocatePtr ((d.allocId, e.allocId) :: renamingOfPtrs ds es)) =
        ds.map (relocatePtr (renamingOfPtrs ds es)) := by
      apply List.map_congr_left
      intro q hq
      unfold relocatePtr
      have hne : (d.allocId == q.allocId) = false := by
        apply beq_eq_false_iff_ne.mpr
        intro heq
        exact h_notin (heq ▸ List.mem_map_of_mem hq)
      rw [relocateAllocId_cons, hne]
      rfl
    rw [h_head, h_tail, ← ih]

/-- **`AllocRenamingRel` from observational agreement**: whenever the demand and eager pointer
lists are observationally equal (`demandCallerLocation_bisim_eager`), have zero offsets, and the
positional renaming is well-formed (injective — i.e. no call site was invoked twice), they are
related by the explicit renaming `renamingOfPtrs`. -/
theorem allocRenamingRel_of_readLocations {ds es : List ProvenancePtr} {memD memE : Memory}
    (h_obs : readLocations memD.globals ds = readLocations memE.globals es)
    (h_wf : AllocRenamingWf (renamingOfPtrs ds es) = true)
    (h_offD : ∀ p ∈ ds, p.offsetBytes = 0) (h_offE : ∀ p ∈ es, p.offsetBytes = 0) :
    AllocRenamingRel (renamingOfPtrs ds es) memD memE ds es := by
  have h_len : ds.length = es.length := by
    have := congrArg List.length h_obs
    simpa [readLocations] using this
  have h_nd : nodupNat (ds.map (·.allocId)) = true := by
    unfold AllocRenamingWf renamingOfPtrs at h_wf
    rw [Bool.and_eq_true] at h_wf
    have h_fst : (List.zip (ds.map (·.allocId)) (es.map (·.allocId))).map Prod.fst =
        ds.map (·.allocId) :=
      List.map_fst_zip (by simp [h_len])
    rw [← h_fst]
    exact h_wf.1
  have h_map := renamingOfPtrs_mapped ds es h_len h_nd h_offD h_offE
  refine ⟨h_wf, h_map, ?_⟩
  intro p hp
  unfold LocationPtrObsEq
  rw [h_map] at h_obs
  unfold readLocations at h_obs
  rw [List.map_map] at h_obs
  exact (List.map_inj_left.mp h_obs) p hp

/-! ### Concrete `#[track_caller]` Chains Across All 8 `-Zlocation-detail` Policies -/

/-- `"src/lib.rs"` and `"core/opt.rs"` filename bytes. -/
def protoLibRsBytes : List UInt8 := [115, 114, 99, 47, 108, 105, 98, 46, 114, 115]
def protoOptionRsBytes : List UInt8 := [99, 111, 114, 101, 47, 111, 112, 116, 46, 114, 115]

def protoUserCallerPos : SourceExpansionPos := ⟨"src/lib.rs", protoLibRsBytes, 42, 13⟩
def protoUnwrapBodyPos : SourceExpansionPos := ⟨"core/opt.rs", protoOptionRsBytes, 950, 5⟩
def protoUnwrapFailedPos : SourceExpansionPos := ⟨"core/opt.rs", protoOptionRsBytes, 1980, 5⟩
def protoOtherCallPos : SourceExpansionPos := ⟨"src/lib.rs", protoLibRsBytes, 108, 7⟩

/-- `option::unwrap_failed` (`#[track_caller]`), called from `Option::unwrap` at `opt.rs:950:5`. -/
def protoUnwrapFailedFrame (pol : LocationDetailPolicy := {}) : FrameLocMeta :=
  ⟨"core::option::unwrap_failed", some protoUnwrapBodyPos, true, pol⟩

/-- `Option::unwrap` (`#[track_caller]`), called from `user_caller` at `lib.rs:42:13`. -/
def protoUnwrapFrame (pol : LocationDetailPolicy := {}) : FrameLocMeta :=
  ⟨"core::option::Option::unwrap", some protoUserCallerPos, true, pol⟩

/-- Entry frame `my_crate::user_caller` (not `#[track_caller]`, no recorded caller). -/
def protoUserCallerFrame (pol : LocationDetailPolicy := {}) : FrameLocMeta :=
  ⟨"my_crate::user_caller", none, false, pol⟩

/-- `caller_location` invoked directly in `user_caller` at `lib.rs:108:7`. -/
def protoDirectSite (userPol : LocationDetailPolicy := {}) : CallerLocationSite :=
  ⟨protoOtherCallPos, [protoUserCallerFrame userPol]⟩

/-- `caller_location` invoked inside `Option::unwrap` (2-frame forwarding chain). -/
def protoUnwrapSite (corePol userPol : LocationDetailPolicy := {}) : CallerLocationSite :=
  ⟨protoUnwrapBodyPos, [protoUnwrapFrame corePol, protoUserCallerFrame userPol]⟩

/-- `caller_location` invoked inside `unwrap_failed` (3-frame forwarding chain
`user_caller -> unwrap -> unwrap_failed -> caller_location`). -/
def protoPanicSite (corePol userPol : LocationDetailPolicy := {}) : CallerLocationSite :=
  ⟨protoUnwrapFailedPos,
    [protoUnwrapFailedFrame corePol, protoUnwrapFrame corePol, protoUserCallerFrame userPol]⟩

/-- Call-site table; frames of the `core` crate use `corePol`, `user_caller` uses `userPol`. -/
def protoSites (corePol userPol : LocationDetailPolicy) : List CallerLocationSite :=
  [protoDirectSite userPol, protoUnwrapSite corePol userPol, protoPanicSite corePol userPol]

theorem applyLocationDetailPolicy_fileBytes_length_le {pol : LocationDetailPolicy}
    {pos : SourceExpansionPos} {bound : Nat}
    (h_pos : pos.fileBytes.length ≤ bound) (h_red : redactedFileBytes.length ≤ bound) :
    (applyLocationDetailPolicy pol pos).fileBytes.length ≤ bound := by
  unfold applyLocationDetailPolicy
  dsimp only
  split <;> assumption

/-- The resolved filename is either `"<redacted>"` or one of the spans along the walk, so a
uniform byte-length bound on those spans bounds the resolved filename. -/
theorem resolveCallerLocationAux_fileBytes_length_le {bound : Nat}
    (h_red : redactedFileBytes.length ≤ bound) :
    ∀ (frames : List FrameLocMeta) (fallbackPol : LocationDetailPolicy) (pos : SourceExpansionPos),
      pos.fileBytes.length ≤ bound →
      (∀ f ∈ frames, ∀ p, f.callSitePos = some p → p.fileBytes.length ≤ bound) →
      (resolveCallerLocationAux fallbackPol pos frames).fileBytes.length ≤ bound
  | [], _, _, h_pos, _ => applyLocationDetailPolicy_fileBytes_length_le h_pos h_red
  | f :: rest, _, pos, h_pos, h_frames => by
    unfold resolveCallerLocationAux
    split
    · split
      · rename_i p hp
        exact resolveCallerLocationAux_fileBytes_length_le h_red rest f.detailPolicy p
          (h_frames f (List.Mem.head _) p hp)
          (fun g hg q hq => h_frames g (List.Mem.tail _ hg) q hq)
      · exact applyLocationDetailPolicy_fileBytes_length_le h_pos h_red
    · exact applyLocationDetailPolicy_fileBytes_length_le h_pos h_red

theorem protoSites_fileLenOk (corePol userPol : LocationDetailPolicy) :
    SitesFileLenOk (protoSites corePol userPol) := by
  intro site hsite
  apply Nat.lt_of_le_of_lt _ (by decide : 11 < 4294967296)
  apply resolveCallerLocationAux_fileBytes_length_le (by decide)
  · simp only [protoSites, List.mem_cons, List.not_mem_nil, or_false] at hsite
    rcases hsite with rfl | rfl | rfl <;> exact Nat.le_of_ble_eq_true rfl
  · intro f hf p hp
    simp only [protoSites, List.mem_cons, List.not_mem_nil, or_false] at hsite
    rcases hsite with rfl | rfl | rfl <;>
      simp only [protoDirectSite, protoUnwrapSite, protoPanicSite, List.mem_cons,
        List.not_mem_nil, or_false] at hf <;>
      rcases hf with rfl | rfl | rfl <;>
      simp only [protoUnwrapFailedFrame, protoUnwrapFrame, protoUserCallerFrame,
        Option.some.injEq, reduceCtorEq] at hp <;>
      subst hp <;> decide

/-- **Filename Deduplication (`demandCallerLocation_filename_dedup`)**: two `caller_location`
invocations resolving into `"src/lib.rs"` (`42:13` via the 3-frame chain and `108:7` directly)
materialize only **3** `CapturedAllocation`s (1 shared filename at `allocId = 1`, 2 distinct
`Location` roots at `2` and `3`) and advance both `nextAllocId = 4` and `nextTag = 4` past every
materialized id (starting from `max emptyMemory.nextAllocId emptyMemory.nextTag = max 0 1 = 1`). -/
theorem demandCallerLocation_filename_dedup :
    let r₁ := evalDemandCallerLocation {} (protoPanicSite {} {}) emptyMemory
    let r₂ := evalDemandCallerLocation r₁.1 (protoDirectSite {}) r₁.2.2
    r₂.2.2.globals.length = 3 ∧
      r₂.1.fileCache.length = 1 ∧
      r₁.2.1.allocId = 2 ∧
      r₂.2.1.allocId = 3 ∧
      r₂.2.2.nextAllocId = 4 ∧
      r₂.2.2.nextTag = 4 ∧
      readLocationFromGlobals r₂.2.2.globals r₁.2.1 = some (protoLibRsBytes, 42, 13) ∧
      readLocationFromGlobals r₂.2.2.globals r₂.2.1 = some (protoLibRsBytes, 108, 7) := by
  decide +kernel

/-- Per-crate policy ownership: the 3-frame chain resolves to `user_caller`'s span, so
`user_caller`'s crate policy applies even when every `core` frame redacts everything. -/
theorem trackCaller_span_owner_policy :
    (protoPanicSite ⟨false, false, false⟩ {}).resolve = protoUserCallerPos ∧
    (protoPanicSite {} ⟨false, false, false⟩).resolve =
      applyLocationDetailPolicy ⟨false, false, false⟩ protoUserCallerPos := by
  decide +kernel

/-- Non-`#[track_caller]` intermediate frame: the walk stops at the call site inside that
frame rather than forwarding the outer caller's position. -/
theorem trackCaller_stops_at_nonTrackCaller_frame :
    let nonTrackMid : FrameLocMeta := ⟨"my_crate::non_track_helper", some protoOtherCallPos, false, {}⟩
    CallerLocationSite.resolve
        ⟨protoUnwrapFailedPos, [protoUnwrapFailedFrame {}, nonTrackMid, protoUserCallerFrame {}]⟩ =
      protoUnwrapBodyPos := by
  decide +kernel

/-- **Borrow-Tag Disjointness Canary (`canary_demandLocation_borrowTag_disjoint`)**:
When `mem` has a live stack borrow with `tag = 1` (`nextTag = 2`) and `nextAllocId = 0`, a naive
allocator drawing from `nextAllocId` would allocate the filename at `0` and the `Location` struct at
`allocId = 1` (`ptr.tag = 1`), which collides with the live stack borrow (`lookupBorrow [b] 1 = some b`)
because `Trusted` checks `lookupBorrow` before `lookupGlobalAlloc`. Drawing from
`nextFreshGlobalAndTagId mem = max mem.nextAllocId mem.nextTag = 2` allocates at `2` and `3`, which
are disjoint from all live stack borrow tags (`readLocationBorrowAware = some ...`). -/
theorem canary_demandLocation_borrowTag_disjoint :
    let liveBorrow : BorrowEntry :=
      { tag := 1, targetLocal := 2, targetProjection := [], perm := .unique }
    let mem : Memory := { emptyMemory with borrows := [liveBorrow], nextTag := 2, nextAllocId := 0 }
    let r := evalDemandCallerLocation {} (protoDirectSite {}) mem
    (lookupBorrow mem.borrows 1).map (·.tag) = some 1 ∧
    r.2.1.allocId = 3 ∧
    (lookupBorrow r.2.2.borrows r.2.1.tag).isNone = true ∧
    readLocationBorrowAware r.2.2 r.2.1 = some (protoLibRsBytes, 108, 7) := by
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

/-- **Lazy 1-layer overwrite-stripping symbolic write (`mkLazyWrite`, `cl/1023450318`)** over a
fixed-width array whose width `w` is statically known (`symArrayLen arr = w`):
1. Constant-folds out-of-bounds writes with an `O(1)` check against the static width `w`
   (`!(idx < w)`; recomputing `symArrayLen arr` here would walk the whole write spine and make
   every write `O(N)`),
2. Collapses same-value writes onto `.constVec len defVal`,
3. Collapses an **immediately preceding** same-address concrete overwrite `.write inner idx' _`
   when `idx' == idx`, and
4. Stops immediately in `O(1)` when `idx' != idx` without walking the write spine. -/
def mkLazyWrite (w : Nat) (arr : SymArrayTerm) (idx : Nat) (val : Nat) : SymArrayTerm :=
  if !(idx < w) then
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

theorem symArrayLen_mkLazyWrite (w : Nat) (arr : SymArrayTerm) (idx val : Nat) :
    symArrayLen (mkLazyWrite w arr idx val) = symArrayLen arr := by
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

/-- An out-of-bounds write (`symArrayLen arr ≤ idx`) is semantically a no-op. -/
theorem eval_write_oob (env : Nat → Nat → Option Nat) (arr : SymArrayTerm) (idx val i : Nat)
    (hge : symArrayLen arr ≤ idx) :
    evalSymArrayTerm env (.write arr idx val) i = evalSymArrayTerm env arr i := by
  show (if i < symArrayLen arr then
      (if (i == idx) = true then some val else evalSymArrayTerm env arr i) else none) =
    evalSymArrayTerm env arr i
  by_cases hi : i < symArrayLen arr
  · simp only [hi, ↓reduceIte]
    have hne : (i == idx) = false :=
      beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (Nat.lt_of_lt_of_le hi hge))
    rw [hne]
    rfl
  · simp only [hi, ↓reduceIte]
    exact (evalSymArrayTerm_oob env arr i hi).symm

/-- **Exact Semantic Soundness of `mkLazyWrite` (`eval_mkLazyWrite`)**:
For all environments `env`, terms `arr` of static width `w`, write indices `idx`, values `val`,
and read indices `i`, `mkLazyWrite w arr idx val` denotes the exact same array as
`.write arr idx val`. -/
theorem eval_mkLazyWrite (env : Nat → Nat → Option Nat) {w : Nat} (arr : SymArrayTerm)
    (h_w : symArrayLen arr = w) (idx val i : Nat) :
    evalSymArrayTerm env (mkLazyWrite w arr idx val) i =
      evalSymArrayTerm env (.write arr idx val) i := by
  subst h_w
  unfold mkLazyWrite
  split
  · rename_i h_oob
    have hge : symArrayLen arr ≤ idx := Nat.le_of_not_lt (by simpa using h_oob)
    exact (eval_write_oob env arr idx val i hge).symm
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
shadowed writes at `idx`, incurring $\Theta(N^2)$ spine inspections across $N$ distinct-address
writes (`eagerWriteChain_distinctAddrs_steps_quadratic`). -/
def mkEagerWrite (w : Nat) (arr : SymArrayTerm) (idx : Nat) (val : Nat) : SymArrayTerm :=
  if !(idx < w) then
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

/-- **Exact Semantic Soundness of the eager baseline (`eval_mkEagerWrite`)**: `mkEagerWrite`
denotes the same array as `.write arr idx val`, so both strategies are interchangeable and the
benchmark compares equal semantics. -/
theorem eval_mkEagerWrite (env : Nat → Nat → Option Nat) {w : Nat} (arr : SymArrayTerm)
    (h_w : symArrayLen arr = w) (idx val i : Nat) :
    evalSymArrayTerm env (mkEagerWrite w arr idx val) i =
      evalSymArrayTerm env (.write arr idx val) i := by
  subst h_w
  unfold mkEagerWrite
  split
  · rename_i h_oob
    have hge : symArrayLen arr ≤ idx := Nat.le_of_not_lt (by simpa using h_oob)
    exact (eval_write_oob env arr idx val i hge).symm
  · unfold evalSymArrayTerm
    rw [symArrayLen_stripShadowedWrites]
    by_cases hi : i < symArrayLen arr
    · simp only [hi, ↓reduceIte]
      cases h_i : i == idx with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact eval_stripShadowedWrites_ne env arr idx i h_i
    · simp only [hi, ↓reduceIte]

/-- Spine walk of `mkLazyRead` (read-over-write forwarding on `rIdx == idx`, skipping distinct
concrete writes `rIdx != idx`; bounds were already checked once against the static width). -/
def lazyReadSpine : SymArrayTerm → Nat → Option Nat
  | .base _ _, _ => none
  | .constVec _ defVal, _ => some defVal
  | .write inner idx val, rIdx => if rIdx == idx then some val else lazyReadSpine inner rIdx
  | .ite cond t f, rIdx => if cond then lazyReadSpine t rIdx else lazyReadSpine f rIdx

/-- Lazy read-over-write folding (`mkLazyRead`): one `O(1)` bounds check against the static width
`w`, then `lazyReadSpine` (which no longer re-walks the spine via `symArrayLen` at every node). -/
def mkLazyRead (w : Nat) (arr : SymArrayTerm) (rIdx : Nat) : Option Nat :=
  if rIdx < w then lazyReadSpine arr rIdx else none

theorem lazyReadSpine_sound (env : Nat → Nat → Option Nat) :
    ∀ (arr : SymArrayTerm) (rIdx v : Nat),
      rIdx < symArrayLen arr →
      lazyReadSpine arr rIdx = some v →
      evalSymArrayTerm env arr rIdx = some v
  | .base _ _, _, _, _, h => nomatch h
  | .constVec len defVal, rIdx, v, hlt, h => by
    unfold symArrayLen at hlt
    unfold lazyReadSpine at h
    unfold evalSymArrayTerm
    simp only [hlt, ↓reduceIte]
    exact h
  | .write inner idx val, rIdx, v, hlt, h => by
    unfold symArrayLen at hlt
    unfold lazyReadSpine at h
    unfold evalSymArrayTerm
    simp only [hlt, ↓reduceIte]
    cases h_eq : rIdx == idx with
    | true =>
      rw [h_eq] at h
      exact h
    | false =>
      rw [h_eq] at h
      exact lazyReadSpine_sound env inner rIdx v hlt h
  | .ite cond t f, rIdx, v, hlt, h => by
    unfold symArrayLen at hlt
    unfold lazyReadSpine at h
    unfold evalSymArrayTerm
    cases cond with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hlt h ⊢
      exact lazyReadSpine_sound env f rIdx v hlt h
    | true =>
      simp only [↓reduceIte] at hlt h ⊢
      exact lazyReadSpine_sound env t rIdx v hlt h

/-- **Soundness of `mkLazyRead` (`eval_mkLazyRead`)**: whenever `mkLazyRead w arr rIdx = some v`
for a term of static width `w`, `evalSymArrayTerm env arr rIdx = some v` for *every* base
environment `env`! -/
theorem eval_mkLazyRead (env : Nat → Nat → Option Nat) {w : Nat} (arr : SymArrayTerm)
    (h_w : symArrayLen arr = w) (rIdx v : Nat) (h : mkLazyRead w arr rIdx = some v) :
    evalSymArrayTerm env arr rIdx = some v := by
  subst h_w
  unfold mkLazyRead at h
  by_cases hlt : rIdx < symArrayLen arr
  · simp only [hlt, ↓reduceIte] at h
    exact lazyReadSpine_sound env arr rIdx v hlt h
  · simp only [hlt, ↓reduceIte] at h
    nomatch h

/-- Instrumented `lazyReadSpine`: counts the number of spine nodes inspected during a read. -/
def lazyReadSpineCounted : SymArrayTerm → Nat → Option Nat × Nat
  | .base _ _, _ => (none, 1)
  | .constVec _ defVal, _ => (some defVal, 1)
  | .write inner idx val, rIdx =>
    if rIdx == idx then
      (some val, 1)
    else
      let r := lazyReadSpineCounted inner rIdx
      (r.1, r.2 + 1)
  | .ite cond t f, rIdx =>
    if cond then
      let r := lazyReadSpineCounted t rIdx
      (r.1, r.2 + 1)
    else
      let r := lazyReadSpineCounted f rIdx
      (r.1, r.2 + 1)

/-- Instrumented `mkLazyRead`: same result as `mkLazyRead`, plus the exact count of spine nodes
inspected. -/
def mkLazyReadCounted (w : Nat) (arr : SymArrayTerm) (rIdx : Nat) : Option Nat × Nat :=
  if rIdx < w then lazyReadSpineCounted arr rIdx else (none, 0)

theorem lazyReadSpineCounted_fst :
    ∀ (arr : SymArrayTerm) (rIdx : Nat),
      (lazyReadSpineCounted arr rIdx).1 = lazyReadSpine arr rIdx
  | .base _ _, _ => rfl
  | .constVec _ _, _ => rfl
  | .write inner idx val, rIdx => by
    unfold lazyReadSpineCounted lazyReadSpine
    split
    · rfl
    · dsimp only
      rw [lazyReadSpineCounted_fst inner rIdx]
  | .ite cond t f, rIdx => by
    unfold lazyReadSpineCounted lazyReadSpine
    cases cond <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact lazyReadSpineCounted_fst f rIdx
    · exact lazyReadSpineCounted_fst t rIdx

theorem mkLazyReadCounted_fst (w : Nat) (arr : SymArrayTerm) (rIdx : Nat) :
    (mkLazyReadCounted w arr rIdx).1 = mkLazyRead w arr rIdx := by
  unfold mkLazyReadCounted mkLazyRead
  split
  · exact lazyReadSpineCounted_fst arr rIdx
  · rfl

/-- **$O(1)$ Top-Write Forwarding (`mkLazyReadCounted_hit_top`)**: reading the address `idx < w`
of the most recent write `.write inner idx val` resolves in `1` spine inspection without walking
`inner`. -/
theorem mkLazyReadCounted_hit_top {w idx : Nat} (inner : SymArrayTerm) (val : Nat)
    (h : idx < w) :
    mkLazyReadCounted w (.write inner idx val) idx = (some val, 1) := by
  unfold mkLazyReadCounted lazyReadSpineCounted
  split
  · have hself : (idx == idx) = true := nat_beq_self idx
    rw [hself]
    rfl
  · rename_i hnot
    exact False.elim (hnot h)

/-! ### Exact Spine-Inspection Complexity Tied to the Implementations

The step counters below are *instrumented copies* of `mkLazyWrite`, `stripShadowedWrites`, and
`mkEagerWrite` with identical recursion structure; `*_fst` theorems prove they compute exactly the
uninstrumented terms, so the complexity theorems are statements about the real implementations
(not free-standing closed-form recurrences). -/

/-- Number of `.write` nodes on the spine of a `SymArrayTerm`. -/
def writeSpineDepth : SymArrayTerm → Nat
  | .write inner _ _ => writeSpineDepth inner + 1
  | _ => 0

/-- `true` iff no `.write` on the spine of the term targets `idx`. -/
def spineAvoids (idx : Nat) : SymArrayTerm → Bool
  | .write inner idx' _ => (idx' != idx) && spineAvoids idx inner
  | _ => true

/-- Instrumented `mkLazyWrite`: same result, plus the number of term nodes inspected (`0` for an
out-of-bounds write folded by the static-width check, otherwise the single top node examined). -/
def mkLazyWriteCounted (w : Nat) (arr : SymArrayTerm) (idx val : Nat) : SymArrayTerm × Nat :=
  if !(idx < w) then
    (arr, 0)
  else
    match arr with
    | .constVec len defVal =>
      (if val == defVal then .constVec len defVal else .write (.constVec len defVal) idx val, 1)
    | .write inner idx' val' =>
      (if idx' == idx then .write inner idx val else .write (.write inner idx' val') idx val, 1)
    | other => (.write other idx val, 1)

theorem mkLazyWriteCounted_fst (w : Nat) (arr : SymArrayTerm) (idx val : Nat) :
    (mkLazyWriteCounted w arr idx val).1 = mkLazyWrite w arr idx val := by
  unfold mkLazyWriteCounted mkLazyWrite
  split
  · rfl
  · cases arr <;> rfl

theorem mkLazyWriteCounted_snd_of_lt {w idx : Nat} (arr : SymArrayTerm) (val : Nat)
    (h : idx < w) : (mkLazyWriteCounted w arr idx val).2 = 1 := by
  unfold mkLazyWriteCounted
  have hnot : (!decide (idx < w)) = false := by simp [h]
  rw [hnot]
  cases arr <;> rfl

/-- Instrumented `stripShadowedWrites`: identical recursion, counting one inspection per visited
spine node (every `.write` plus the terminal non-`.write` node). -/
def stripShadowedWritesCounted : SymArrayTerm → Nat → SymArrayTerm × Nat
  | .write inner idx' val', idx =>
    let r := stripShadowedWritesCounted inner idx
    (if idx' == idx then r.1 else .write r.1 idx' val', r.2 + 1)
  | other, _ => (other, 1)

theorem stripShadowedWritesCounted_fst :
    ∀ (arr : SymArrayTerm) (idx : Nat),
      (stripShadowedWritesCounted arr idx).1 = stripShadowedWrites arr idx
  | .base _ _, _ => rfl
  | .constVec _ _, _ => rfl
  | .ite _ _ _, _ => rfl
  | .write inner idx' val', idx => by
    unfold stripShadowedWritesCounted stripShadowedWrites
    dsimp only
    rw [stripShadowedWritesCounted_fst inner idx]

theorem stripShadowedWritesCounted_snd :
    ∀ (arr : SymArrayTerm) (idx : Nat),
      (stripShadowedWritesCounted arr idx).2 = writeSpineDepth arr + 1
  | .base _ _, _ => rfl
  | .constVec _ _, _ => rfl
  | .ite _ _ _, _ => rfl
  | .write inner idx' val', idx => by
    unfold stripShadowedWritesCounted writeSpineDepth
    dsimp only
    rw [stripShadowedWritesCounted_snd inner idx]

/-- Instrumented `mkEagerWrite`. -/
def mkEagerWriteCounted (w : Nat) (arr : SymArrayTerm) (idx val : Nat) : SymArrayTerm × Nat :=
  if !(idx < w) then
    (arr, 0)
  else
    let r := stripShadowedWritesCounted arr idx
    (.write r.1 idx val, r.2)

theorem mkEagerWriteCounted_fst (w : Nat) (arr : SymArrayTerm) (idx val : Nat) :
    (mkEagerWriteCounted w arr idx val).1 = mkEagerWrite w arr idx val := by
  unfold mkEagerWriteCounted mkEagerWrite
  split
  · rfl
  · dsimp only
    rw [stripShadowedWritesCounted_fst]

theorem mkEagerWriteCounted_snd_of_lt {w idx : Nat} (arr : SymArrayTerm) (val : Nat)
    (h : idx < w) : (mkEagerWriteCounted w arr idx val).2 = writeSpineDepth arr + 1 := by
  unfold mkEagerWriteCounted
  have hnot : (!decide (idx < w)) = false := by simp [h]
  rw [hnot]
  exact stripShadowedWritesCounted_snd arr idx

theorem mkEagerWrite_of_lt {w idx : Nat} (arr : SymArrayTerm) (val : Nat) (h : idx < w) :
    mkEagerWrite w arr idx val = .write (stripShadowedWrites arr idx) idx val := by
  unfold mkEagerWrite
  have hnot : (!decide (idx < w)) = false := by simp [h]
  rw [hnot]
  rfl

theorem stripShadowedWrites_of_spineAvoids :
    ∀ (arr : SymArrayTerm) (idx : Nat),
      spineAvoids idx arr = true → stripShadowedWrites arr idx = arr
  | .base _ _, _, _ => rfl
  | .constVec _ _, _, _ => rfl
  | .ite _ _ _, _, _ => rfl
  | .write inner idx' val', idx, h => by
    unfold spineAvoids at h
    rw [Bool.and_eq_true] at h
    have hne : (idx' == idx) = false := by
      simpa [bne_iff_ne, beq_eq_false_iff_ne] using h.1
    unfold stripShadowedWrites
    dsimp only
    rw [hne, stripShadowedWrites_of_spineAvoids inner idx h.2]
    rfl

/-- `N` distinct-address writes `a[k] := k + 1` (`k = 0, …, N - 1`) under `mkLazyWrite`. -/
def buildLazyDistinctChain (cap : Nat) : Nat → SymArrayTerm
  | 0 => .constVec cap 0
  | n + 1 => mkLazyWrite cap (buildLazyDistinctChain cap n) n (n + 1)

/-- `N` distinct-address writes `a[k] := k + 1` (`k = 0, …, N - 1`) under `mkEagerWrite`. -/
def buildEagerDistinctChain (cap : Nat) : Nat → SymArrayTerm
  | 0 => .constVec cap 0
  | n + 1 => mkEagerWrite cap (buildEagerDistinctChain cap n) n (n + 1)

/-- Instrumented lazy chain: `(buildLazyDistinctChain cap n, total inspections)`. -/
def lazyDistinctChainCounted (cap : Nat) : Nat → SymArrayTerm × Nat
  | 0 => (.constVec cap 0, 0)
  | n + 1 =>
    let r := lazyDistinctChainCounted cap n
    let w := mkLazyWriteCounted cap r.1 n (n + 1)
    (w.1, r.2 + w.2)

/-- Instrumented eager chain: `(buildEagerDistinctChain cap n, total inspections)`. -/
def eagerDistinctChainCounted (cap : Nat) : Nat → SymArrayTerm × Nat
  | 0 => (.constVec cap 0, 0)
  | n + 1 =>
    let r := eagerDistinctChainCounted cap n
    let w := mkEagerWriteCounted cap r.1 n (n + 1)
    (w.1, r.2 + w.2)

theorem lazyDistinctChainCounted_fst (cap : Nat) :
    ∀ n, (lazyDistinctChainCounted cap n).1 = buildLazyDistinctChain cap n
  | 0 => rfl
  | n + 1 => by
    unfold lazyDistinctChainCounted buildLazyDistinctChain
    dsimp only
    rw [mkLazyWriteCounted_fst, lazyDistinctChainCounted_fst cap n]

theorem eagerDistinctChainCounted_fst (cap : Nat) :
    ∀ n, (eagerDistinctChainCounted cap n).1 = buildEagerDistinctChain cap n
  | 0 => rfl
  | n + 1 => by
    unfold eagerDistinctChainCounted buildEagerDistinctChain
    dsimp only
    rw [mkEagerWriteCounted_fst, eagerDistinctChainCounted_fst cap n]

theorem symArrayLen_buildEagerDistinctChain (cap : Nat) :
    ∀ n, symArrayLen (buildEagerDistinctChain cap n) = cap
  | 0 => rfl
  | n + 1 => by
    unfold buildEagerDistinctChain mkEagerWrite
    split
    · exact symArrayLen_buildEagerDistinctChain cap n
    · show symArrayLen (stripShadowedWrites (buildEagerDistinctChain cap n) n) = cap
      rw [symArrayLen_stripShadowedWrites, symArrayLen_buildEagerDistinctChain cap n]

theorem symArrayLen_buildLazyDistinctChain (cap : Nat) :
    ∀ n, symArrayLen (buildLazyDistinctChain cap n) = cap
  | 0 => rfl
  | n + 1 => by
    unfold buildLazyDistinctChain
    rw [symArrayLen_mkLazyWrite, symArrayLen_buildLazyDistinctChain cap n]

/-- Structure of the eager chain: every in-bounds write appends exactly one new spine node, since
the spine never contains the fresh address. -/
theorem buildEagerDistinctChain_succ {cap : Nat} :
    ∀ {n : Nat}, n < cap →
      buildEagerDistinctChain cap (n + 1) = .write (buildEagerDistinctChain cap n) n (n + 1) ∧
        ∀ m, n + 1 ≤ m → spineAvoids m (buildEagerDistinctChain cap (n + 1)) = true
  | 0, h0 => by
    refine ⟨?_, ?_⟩
    · show mkEagerWrite cap (.constVec cap 0) 0 1 = _
      rw [mkEagerWrite_of_lt _ _ h0]
      rfl
    · intro m hm
      show spineAvoids m (mkEagerWrite cap (.constVec cap 0) 0 1) = true
      rw [mkEagerWrite_of_lt _ _ h0]
      show ((0 != m) && true) = true
      have hne : (0 != m) = true := by simp [bne_iff_ne]; omega
      rw [hne]
      rfl
  | k + 1, hk => by
    obtain ⟨ih_eq, ih_av⟩ := buildEagerDistinctChain_succ (cap := cap) (n := k) (by omega)
    have hav : spineAvoids (k + 1) (buildEagerDistinctChain cap (k + 1)) = true :=
      ih_av (k + 1) (Nat.le_refl _)
    have h_eq : buildEagerDistinctChain cap (k + 1 + 1) =
        .write (buildEagerDistinctChain cap (k + 1)) (k + 1) (k + 1 + 1) := by
      show mkEagerWrite cap (buildEagerDistinctChain cap (k + 1)) (k + 1) (k + 1 + 1) = _
      rw [mkEagerWrite_of_lt _ _ hk,
        stripShadowedWrites_of_spineAvoids _ _ hav]
    refine ⟨h_eq, ?_⟩
    intro m hm
    rw [h_eq]
    show ((k + 1 != m) && spineAvoids m (buildEagerDistinctChain cap (k + 1))) = true
    have hne : (k + 1 != m) = true := by simp [bne_iff_ne]; omega
    rw [hne, ih_av m (by omega)]
    rfl

theorem writeSpineDepth_buildEagerDistinctChain {cap : Nat} :
    ∀ {n : Nat}, n ≤ cap → writeSpineDepth (buildEagerDistinctChain cap n) = n
  | 0, _ => rfl
  | n + 1, h => by
    rw [(buildEagerDistinctChain_succ (cap := cap) (n := n) (by omega)).1]
    show writeSpineDepth (buildEagerDistinctChain cap n) + 1 = n + 1
    rw [writeSpineDepth_buildEagerDistinctChain (by omega)]

/-- Structure of the lazy chain: identical to the eager chain term-for-term. -/
theorem buildLazyDistinctChain_succ {cap : Nat} :
    ∀ {n : Nat}, n < cap →
      buildLazyDistinctChain cap (n + 1) = .write (buildLazyDistinctChain cap n) n (n + 1)
  | 0, h0 => by
    show mkLazyWrite cap (.constVec cap 0) 0 1 = _
    unfold mkLazyWrite
    have hnot : (!decide (0 < cap)) = false := by simp [h0]
    rw [hnot]
    rfl
  | k + 1, hk => by
    have ih := buildLazyDistinctChain_succ (cap := cap) (n := k) (by omega)
    show mkLazyWrite cap (buildLazyDistinctChain cap (k + 1)) (k + 1) (k + 1 + 1) = _
    conv => lhs; rw [ih]
    unfold mkLazyWrite
    have hnot : (!decide (k + 1 < cap)) = false := by simp [hk]
    rw [hnot]
    have hne : (k == k + 1) = false :=
      beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (Nat.lt_succ_self k))
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    rw [← ih]

/-- Lazy and eager distinct-address chains build the *same* symbolic term. -/
theorem buildLazyDistinctChain_eq_eager {cap : Nat} :
    ∀ {n : Nat}, n ≤ cap → buildLazyDistinctChain cap n = buildEagerDistinctChain cap n
  | 0, _ => rfl
  | n + 1, h => by
    rw [buildLazyDistinctChain_succ (by omega),
      (buildEagerDistinctChain_succ (cap := cap) (n := n) (by omega)).1,
      buildLazyDistinctChain_eq_eager (by omega)]

/-- **$O(N)$ Linear Bound for `mkLazyWrite` (`lazyWriteChain_distinctAddrs_steps_eq_N`)**:
$N \le cap$ distinct-address writes through the instrumented `mkLazyWrite` perform exactly $N$
node inspections. -/
theorem lazyWriteChain_distinctAddrs_steps_eq_N {cap : Nat} :
    ∀ {N : Nat}, N ≤ cap → (lazyDistinctChainCounted cap N).2 = N
  | 0, _ => rfl
  | n + 1, h => by
    unfold lazyDistinctChainCounted
    dsimp only
    rw [mkLazyWriteCounted_snd_of_lt _ _ (by omega : n < cap),
      lazyWriteChain_distinctAddrs_steps_eq_N (by omega)]

/-- **$\Theta(N^2)$ Exact Bound for `mkEagerWrite`
(`eagerWriteChain_distinctAddrs_steps_quadratic`)**: $N \le cap$ distinct-address writes through
the instrumented `mkEagerWrite` perform exactly $\frac{N(N+1)}{2}$ spine inspections
(`2 * steps = N * (N + 1)`). -/
theorem eagerWriteChain_distinctAddrs_steps_quadratic {cap : Nat} :
    ∀ {N : Nat}, N ≤ cap → 2 * (eagerDistinctChainCounted cap N).2 = N * (N + 1)
  | 0, _ => rfl
  | n + 1, h => by
    unfold eagerDistinctChainCounted
    dsimp only
    rw [mkEagerWriteCounted_snd_of_lt _ _ (by omega : n < cap), eagerDistinctChainCounted_fst,
      writeSpineDepth_buildEagerDistinctChain (by omega), Nat.left_distrib,
      eagerWriteChain_distinctAddrs_steps_quadratic (by omega)]
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
