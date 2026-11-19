/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Std.Do
import Trusted
import Anneal.MirLiftCore

/-!
# Tree Borrows foreign-subtree pruning and `Std.Do` frame-prep composition

Two results over the trusted operational semantics
`Trusted.Rustc.V2026_06_01.MirSemantics` and the lifting layer
`Anneal.MirLiftCore`. No shadow evaluator is defined: every theorem is stated
against the trusted functions themselves.

## Part 1: root-level foreign-subtree pruning (`lean-miri#87`)

The trusted borrow table is a flat `List BorrowEntry`, and every Tree Borrows
access scans all of it. `BorrowSubtree` / `BorrowForest` present the same
entries as a forest, and the pruned traversals (`pruneForeignRead`,
`pruneHasTreeReadUB`, `pruneForeignWrite`, `pruneForeignWriteSimple`,
`pruneForeignWriteProj`, `pruneHasProtectedWriteConflict`) inspect only the
root of a subtree before deciding to skip the whole subtree:

- an *unrelated root* (`isForeignUnrelatedRoot`) targets another allocation,
  and so does its whole subtree (`SameAllocSubtree`);
- a *foreign no-op root* (`isForeignReadNoopPerm` / `isForeignWriteNoopPerm`)
  whose subtree is foreign to the access is unchanged by the access, and so is
  its whole subtree (`ForeignReadNoopSubtree` / `ForeignWriteNoopSubtree`: the
  `.disabled`-subtree and `.frozen`-subtree invariants).

The `*_equiv_fullScan` theorems prove that each pruned traversal agrees
exactly with the trusted full scan, and
`naive_frozen_root_without_subtree_inv_counterexample` shows that the subtree
invariant cannot be dropped.

## Part 2: `Std.Do` frame-prep composition (`lean-miri#88`)

`FramePrepM` is the `EStateM` monad of trusted fault requests (`MirFailE.I`)
over `MachineState`. The call pipeline of `Terminators.lean` is factored into
the stages `prepResolveAndArgs`, `prepPushCalleeFrame`,
`prepRegisterProtectors`, and `prepTeardownAndWriteback`, each proved to be
exactly the corresponding trusted transition. Their weakest preconditions
(`Std.Do.wp`) compose into `wpFramePrep` against a callee contract
`FramePrepContract`. `wpFramePrep_sound_stepMirFn` connects that composition
to the real `stepMirFn` execution and to `LiftFrame`,
`wpFramePrep_triple_sound` gives the `Std.Do.Triple` for the executable call
pipeline, `wpFramePrep_empty_function` discharges calls to the empty function
once and for all, and `wpFramePrep_seq` / `wpFramePrep_duplicate_prefix`
compose calls sequentially and share a verified prefix between two suffix
specifications.

Every declaration is constructive: its axiom closure is contained in
`[propext, Quot.sound]`.
-/

namespace Anneal.TreeBorrowsPruningAndFrameWp

open Trusted.Effect
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.MirLiftCore

/-! ## Part 1. Root-level foreign-subtree Tree Borrows pruning -/

/-! ### 1.1 Subtree-forest representation -/

/--
A borrow subtree: a `BorrowEntry` together with the subtrees of the borrows
reborrowed from it (Tree Borrows children).
-/
inductive BorrowSubtree : Type where
  /-- Subtree with root entry `root` and child subtrees `children`. -/
  | node (root : BorrowEntry) (children : List BorrowSubtree) : BorrowSubtree

/-- A borrow forest: the subtrees of the root borrows, in table order. -/
abbrev BorrowForest : Type := List BorrowSubtree

/-- Root entry of a subtree. -/
def BorrowSubtree.root : BorrowSubtree → BorrowEntry
  | .node root _ => root

/-- Child subtrees of a subtree. -/
def BorrowSubtree.children : BorrowSubtree → List BorrowSubtree
  | .node _ children => children

mutual
/-- Preorder flattening of a subtree into the trusted flat borrow table. -/
def BorrowSubtree.toList : BorrowSubtree → List BorrowEntry
  | .node root children => root :: BorrowForest.toList children
/-- Preorder flattening of a forest into the trusted flat borrow table. -/
def BorrowForest.toList : List BorrowSubtree → List BorrowEntry
  | [] => []
  | t :: ts => BorrowSubtree.toList t ++ BorrowForest.toList ts
end

mutual
/-- Whether some entry of the subtree has provenance tag `tag`. -/
def BorrowSubtree.containsTag : BorrowSubtree → Nat → Bool
  | .node root children, tag =>
    Nat.beq root.tag tag || BorrowForest.containsTag children tag
/-- Whether some entry of the forest has provenance tag `tag`. -/
def BorrowForest.containsTag : List BorrowSubtree → Nat → Bool
  | [], _ => false
  | t :: ts, tag =>
    BorrowSubtree.containsTag t tag || BorrowForest.containsTag ts tag
end

@[simp] theorem BorrowSubtree.toList_node (root : BorrowEntry)
    (children : List BorrowSubtree) :
    (BorrowSubtree.node root children).toList =
      root :: BorrowForest.toList children := by
  rw [BorrowSubtree.toList]

@[simp] theorem BorrowForest.toList_nil :
    BorrowForest.toList [] = [] := by
  rw [BorrowForest.toList]

@[simp] theorem BorrowForest.toList_cons (t : BorrowSubtree)
    (ts : List BorrowSubtree) :
    BorrowForest.toList (t :: ts) = t.toList ++ BorrowForest.toList ts := by
  rw [BorrowForest.toList]

theorem BorrowSubtree.containsTag_node (root : BorrowEntry)
    (children : List BorrowSubtree) (tag : Nat) :
    (BorrowSubtree.node root children).containsTag tag =
      (Nat.beq root.tag tag || BorrowForest.containsTag children tag) := by
  rw [BorrowSubtree.containsTag]

theorem BorrowForest.containsTag_nil (tag : Nat) :
    BorrowForest.containsTag [] tag = false := by
  rw [BorrowForest.containsTag]

theorem BorrowForest.containsTag_cons (t : BorrowSubtree)
    (ts : List BorrowSubtree) (tag : Nat) :
    BorrowForest.containsTag (t :: ts) tag =
      (t.containsTag tag || BorrowForest.containsTag ts tag) := by
  rw [BorrowForest.containsTag]

/-- Splitting a false disjunction. -/
private theorem or_eq_false_split {a b : Bool} (h : (a || b) = false) :
    a = false ∧ b = false := by
  cases a <;> cases b <;>
    first
      | exact ⟨rfl, rfl⟩
      | exact Bool.noConfusion h

/-- A map that fixes every element of a list fixes the list. -/
private theorem map_eq_self_of_forall {α : Type} (f : α → α) :
    ∀ xs : List α, (∀ x, x ∈ xs → f x = x) → xs.map f = xs
  | [], _ => rfl
  | x :: xs, h => by
    show f x :: xs.map f = x :: xs
    rw [h x (List.mem_cons_self ..),
      map_eq_self_of_forall f xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- A test that fails on every element of a list fails on the list. -/
private theorem any_eq_false_of_forall {α : Type} (p : α → Bool) :
    ∀ xs : List α, (∀ x, x ∈ xs → p x = false) → xs.any p = false
  | [], _ => rfl
  | x :: xs, h => by
    show (p x || xs.any p) = false
    rw [h x (List.mem_cons_self ..),
      any_eq_false_of_forall p xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    rfl

/-- `List.any` distributes over append. -/
private theorem any_append' {α : Type} (p : α → Bool) :
    ∀ xs ys : List α, (xs ++ ys).any p = (xs.any p || ys.any p)
  | [], _ => rfl
  | x :: xs, ys => by
    show (p x || (xs ++ ys).any p) = ((p x || xs.any p) || ys.any p)
    rw [any_append' p xs ys]
    cases p x <;> rfl

/-- `List.map` distributes over append. -/
private theorem map_append' {α β : Type} (f : α → β) :
    ∀ xs ys : List α, (xs ++ ys).map f = xs.map f ++ ys.map f
  | [], _ => rfl
  | x :: xs, ys => by
    show f x :: (xs ++ ys).map f = f x :: (xs.map f ++ ys.map f)
    rw [map_append' f xs ys]

/-- Membership in an append. -/
private theorem mem_append_split {α : Type} {a : α} :
    ∀ {xs ys : List α}, a ∈ xs ++ ys → a ∈ xs ∨ a ∈ ys
  | [], _, h => Or.inr h
  | x :: xs, ys, h => by
    have h' : a ∈ x :: (xs ++ ys) := h
    cases h' with
    | head => exact Or.inl (List.mem_cons_self ..)
    | tail _ ht =>
      cases mem_append_split ht with
      | inl hl => exact Or.inl (List.mem_cons_of_mem _ hl)
      | inr hr => exact Or.inr hr

mutual
/-- No entry of a subtree that does not contain `tag` has tag `tag`. -/
theorem BorrowSubtree.tag_ne_of_not_containsTag {tag : Nat} :
    ∀ (t : BorrowSubtree), t.containsTag tag = false →
      ∀ e, e ∈ t.toList → Nat.beq e.tag tag = false
  | .node root children, h, e, he => by
    rw [BorrowSubtree.containsTag_node] at h
    obtain ⟨hroot, hch⟩ := or_eq_false_split h
    rw [BorrowSubtree.toList_node] at he
    cases he with
    | head => exact hroot
    | tail _ ht =>
      exact BorrowForest.tag_ne_of_not_containsTag children hch e ht
/-- No entry of a forest that does not contain `tag` has tag `tag`. -/
theorem BorrowForest.tag_ne_of_not_containsTag {tag : Nat} :
    ∀ (ts : List BorrowSubtree), BorrowForest.containsTag ts tag = false →
      ∀ e, e ∈ BorrowForest.toList ts → Nat.beq e.tag tag = false
  | [], _, e, he => by
    rw [BorrowForest.toList_nil] at he
    cases he
  | t :: ts, h, e, he => by
    rw [BorrowForest.containsTag_cons] at h
    obtain ⟨ht, hts⟩ := or_eq_false_split h
    rw [BorrowForest.toList_cons] at he
    cases mem_append_split he with
    | inl hl => exact BorrowSubtree.tag_ne_of_not_containsTag t ht e hl
    | inr hr => exact BorrowForest.tag_ne_of_not_containsTag ts hts e hr
end

/-! ### 1.2 Subtree invariants -/

mutual
/--
`P root children` holds at every node `node root children` of the subtree.
-/
def AllSubtrees (P : BorrowEntry → List BorrowSubtree → Prop) :
    BorrowSubtree → Prop
  | .node root children => P root children ∧ AllSubtreesForest P children
/-- `P root children` holds at every node of every subtree of the forest. -/
def AllSubtreesForest (P : BorrowEntry → List BorrowSubtree → Prop) :
    List BorrowSubtree → Prop
  | [] => True
  | t :: ts => AllSubtrees P t ∧ AllSubtreesForest P ts
end

theorem AllSubtrees.node_iff {P : BorrowEntry → List BorrowSubtree → Prop}
    {root : BorrowEntry} {children : List BorrowSubtree} :
    AllSubtrees P (.node root children) ↔
      P root children ∧ AllSubtreesForest P children := by
  rw [AllSubtrees]

theorem AllSubtreesForest.nil_iff
    {P : BorrowEntry → List BorrowSubtree → Prop} :
    AllSubtreesForest P [] ↔ True := by
  rw [AllSubtreesForest]

theorem AllSubtreesForest.cons_iff
    {P : BorrowEntry → List BorrowSubtree → Prop} {t : BorrowSubtree}
    {ts : List BorrowSubtree} :
    AllSubtreesForest P (t :: ts) ↔
      AllSubtrees P t ∧ AllSubtreesForest P ts := by
  rw [AllSubtreesForest]

mutual
/--
Strong monotonicity: a node property derivable from the invariant of the
whole subtree rooted at that node holds at every node.
-/
theorem AllSubtrees.mono_strong
    {P Q : BorrowEntry → List BorrowSubtree → Prop}
    (hPQ : ∀ root children, AllSubtrees P (.node root children) →
      Q root children) :
    ∀ (t : BorrowSubtree), AllSubtrees P t → AllSubtrees Q t
  | .node root children, h => by
    have h' := AllSubtrees.node_iff.mp h
    exact AllSubtrees.node_iff.mpr
      ⟨hPQ root children h, AllSubtreesForest.mono_strong hPQ children h'.2⟩
/-- Forest form of `AllSubtrees.mono_strong`. -/
theorem AllSubtreesForest.mono_strong
    {P Q : BorrowEntry → List BorrowSubtree → Prop}
    (hPQ : ∀ root children, AllSubtrees P (.node root children) →
      Q root children) :
    ∀ (ts : List BorrowSubtree), AllSubtreesForest P ts → AllSubtreesForest Q ts
  | [], _ => AllSubtreesForest.nil_iff.mpr True.intro
  | t :: ts, h => by
    have h' := AllSubtreesForest.cons_iff.mp h
    exact AllSubtreesForest.cons_iff.mpr
      ⟨AllSubtrees.mono_strong hPQ t h'.1,
        AllSubtreesForest.mono_strong hPQ ts h'.2⟩
end

mutual
/-- Conjunction of two node invariants. -/
theorem AllSubtrees.and {P Q : BorrowEntry → List BorrowSubtree → Prop} :
    ∀ (t : BorrowSubtree), AllSubtrees P t → AllSubtrees Q t →
      AllSubtrees (fun root children => P root children ∧ Q root children) t
  | .node root children, hP, hQ => by
    have hP' := AllSubtrees.node_iff.mp hP
    have hQ' := AllSubtrees.node_iff.mp hQ
    exact AllSubtrees.node_iff.mpr
      ⟨⟨hP'.1, hQ'.1⟩, AllSubtreesForest.and children hP'.2 hQ'.2⟩
/-- Forest form of `AllSubtrees.and`. -/
theorem AllSubtreesForest.and {P Q : BorrowEntry → List BorrowSubtree → Prop} :
    ∀ (ts : List BorrowSubtree), AllSubtreesForest P ts →
      AllSubtreesForest Q ts →
      AllSubtreesForest
        (fun root children => P root children ∧ Q root children) ts
  | [], _, _ => AllSubtreesForest.nil_iff.mpr True.intro
  | t :: ts, hP, hQ => by
    have hP' := AllSubtreesForest.cons_iff.mp hP
    have hQ' := AllSubtreesForest.cons_iff.mp hQ
    exact AllSubtreesForest.cons_iff.mpr
      ⟨AllSubtrees.and t hP'.1 hQ'.1, AllSubtreesForest.and ts hP'.2 hQ'.2⟩
end

/--
Structural well-formedness of one node against the flat table `allBorrows`
whose parent pointers define Tree Borrows relatedness
(`isBorrowDescendantOrSelf`):

1. every descendant targets the same allocation `(targetFrameDepth,
   targetLocal)` as the root;
2. a tag outside the subtree is not a descendant-or-self of the root
   (`containsTag = false → ¬ isBorrowDescendantOrSelf`);
3. a tag inside the subtree is a descendant-or-self of the root.
-/
def SameAllocNode (allBorrows : List BorrowEntry) (root : BorrowEntry)
    (children : List BorrowSubtree) : Prop :=
  (∀ e, e ∈ BorrowForest.toList children →
    e.targetFrameDepth = root.targetFrameDepth ∧
      e.targetLocal = root.targetLocal) ∧
  (∀ tag, (BorrowSubtree.node root children).containsTag tag = false →
    isBorrowDescendantOrSelf allBorrows tag root.tag = false) ∧
  (∀ tag, (BorrowSubtree.node root children).containsTag tag = true →
    isBorrowDescendantOrSelf allBorrows tag root.tag = true)

/-- `SameAllocNode` at every node of a subtree. -/
def SameAllocSubtree (allBorrows : List BorrowEntry) (t : BorrowSubtree) :
    Prop :=
  AllSubtrees (SameAllocNode allBorrows) t

/-- `SameAllocNode` at every node of a forest. -/
def SameAllocForest (allBorrows : List BorrowEntry) (ts : List BorrowSubtree) :
    Prop :=
  AllSubtreesForest (SameAllocNode allBorrows) ts

/--
Whether a foreign read leaves permission `perm` unchanged without undefined
behavior, for a node whose protector is active (`isProt = true`) or not.

`.cell`, `.frozen`, and `.disabled` are fixed by every foreign read. An
unprotected reservation is fixed; a protected `.reservedFrz` is fixed only
when already conflicted; a protected `.reservedIM` faults; and `.unique` is
frozen (unprotected) or disabled with undefined behavior (protected).
-/
def isForeignReadNoopPerm (isProt : Bool) : TreeBorrowPerm → Bool
  | .cell => true
  | .frozen => true
  | .disabled => true
  | .reservedFrz conflicted =>
    match isProt with
    | true => conflicted
    | false => true
  | .reservedIM => Bool.not isProt
  | .unique => false

/--
Whether a foreign write leaves permission `perm` unchanged without undefined
behavior, for a node whose protector is active (`isProt = true`) or not.

`.cell` and `.disabled` are fixed by every foreign write; an unprotected
`.reservedIM` is fixed; every other permission is disabled.
-/
def isForeignWriteNoopPerm (isProt : Bool) : TreeBorrowPerm → Bool
  | .cell => true
  | .disabled => true
  | .reservedIM => Bool.not isProt
  | .reservedFrz _ => false
  | .unique => false
  | .frozen => false

/--
Whether `root` targets an allocation other than `(targetFrameDepth,
targetLocal)`: such a root, and by `SameAllocSubtree` its whole subtree, is
unrelated to every access to that allocation.
-/
def isForeignUnrelatedRoot (root : BorrowEntry) (targetLocal : Local)
    (targetFrameDepth : Nat := 0) : Bool :=
  Bool.not
    (Bool.and (Nat.beq root.targetFrameDepth targetFrameDepth)
      (Nat.beq root.targetLocal targetLocal))

/--
Whether an access through `accessTag` is foreign to `root`: a direct access
(`none`) is foreign to every node, and an access through `some tag` is foreign
unless `tag` is a descendant-or-self of the root. This is the single
relatedness query that a pruned traversal makes for a skipped subtree; by
`SameAllocSubtree` an access foreign to the root is foreign to the whole
subtree.
-/
def accessForeignToRoot (allBorrows : List BorrowEntry)
    (accessTag : Option Nat) (root : BorrowEntry) : Bool :=
  match accessTag with
  | none => true
  | some tag => Bool.not (isBorrowDescendantOrSelf allBorrows tag root.tag)

/--
Foreign-read no-op invariant of one node: if the root is a foreign-read no-op
then so is every descendant. For a `.disabled` root this is the
`.disabled`-subtree invariant and for a `.frozen` root the `.frozen`-subtree
invariant of Tree Borrows.
-/
def ForeignReadNoopNode (activeProtectors : List Nat) (root : BorrowEntry)
    (children : List BorrowSubtree) : Prop :=
  isForeignReadNoopPerm (isBorrowProtected activeProtectors root) root.perm =
      true →
    ∀ e, e ∈ BorrowForest.toList children →
      isForeignReadNoopPerm (isBorrowProtected activeProtectors e) e.perm = true

/-- `ForeignReadNoopNode` at every node of a subtree. -/
def ForeignReadNoopSubtree (activeProtectors : List Nat) (t : BorrowSubtree) :
    Prop :=
  AllSubtrees (ForeignReadNoopNode activeProtectors) t

/-- `ForeignReadNoopNode` at every node of a forest. -/
def ForeignReadNoopForest (activeProtectors : List Nat)
    (ts : List BorrowSubtree) : Prop :=
  AllSubtreesForest (ForeignReadNoopNode activeProtectors) ts

/--
Foreign-write no-op invariant of one node: if the root is a foreign-write
no-op then so is every descendant (the `.disabled`-subtree invariant).
-/
def ForeignWriteNoopNode (activeProtectors : List Nat) (root : BorrowEntry)
    (children : List BorrowSubtree) : Prop :=
  isForeignWriteNoopPerm (isBorrowProtected activeProtectors root) root.perm =
      true →
    ∀ e, e ∈ BorrowForest.toList children →
      isForeignWriteNoopPerm (isBorrowProtected activeProtectors e) e.perm =
        true

/-- `ForeignWriteNoopNode` at every node of a subtree. -/
def ForeignWriteNoopSubtree (activeProtectors : List Nat) (t : BorrowSubtree) :
    Prop :=
  AllSubtrees (ForeignWriteNoopNode activeProtectors) t

/-- `ForeignWriteNoopNode` at every node of a forest. -/
def ForeignWriteNoopForest (activeProtectors : List Nat)
    (ts : List BorrowSubtree) : Prop :=
  AllSubtreesForest (ForeignWriteNoopNode activeProtectors) ts

mutual
/--
In a structurally well-formed subtree that does not contain `tag`, `tag` is
not a descendant-or-self of any entry.
-/
theorem SameAllocSubtree.foreign_of_not_containsTag
    {allBorrows : List BorrowEntry} {tag : Nat} :
    ∀ (t : BorrowSubtree), SameAllocSubtree allBorrows t →
      t.containsTag tag = false →
      ∀ e, e ∈ t.toList → isBorrowDescendantOrSelf allBorrows tag e.tag = false
  | .node root children, h, hc, e, he => by
    have h' := AllSubtrees.node_iff.mp h
    rw [BorrowSubtree.toList_node] at he
    cases he with
    | head => exact h'.1.2.1 tag hc
    | tail _ ht =>
      rw [BorrowSubtree.containsTag_node] at hc
      exact SameAllocForest.foreign_of_not_containsTag children h'.2
        (or_eq_false_split hc).2 e ht
/-- Forest form of `SameAllocSubtree.foreign_of_not_containsTag`. -/
theorem SameAllocForest.foreign_of_not_containsTag
    {allBorrows : List BorrowEntry} {tag : Nat} :
    ∀ (ts : List BorrowSubtree), SameAllocForest allBorrows ts →
      BorrowForest.containsTag ts tag = false →
      ∀ e, e ∈ BorrowForest.toList ts →
        isBorrowDescendantOrSelf allBorrows tag e.tag = false
  | [], _, _, e, he => by
    rw [BorrowForest.toList_nil] at he
    cases he
  | t :: ts, h, hc, e, he => by
    have h' := AllSubtreesForest.cons_iff.mp h
    rw [BorrowForest.containsTag_cons] at hc
    obtain ⟨ht, hts⟩ := or_eq_false_split hc
    rw [BorrowForest.toList_cons] at he
    cases mem_append_split he with
    | inl hl =>
      exact SameAllocSubtree.foreign_of_not_containsTag t h'.1 ht e hl
    | inr hr =>
      exact SameAllocForest.foreign_of_not_containsTag ts h'.2 hts e hr
end

/--
In a structurally well-formed subtree, an access tag that is not a
descendant-or-self of the root is not contained in the subtree.
-/
theorem SameAllocSubtree.not_containsTag_of_root_foreign
    {allBorrows : List BorrowEntry} {root : BorrowEntry}
    {children : List BorrowSubtree} {tag : Nat}
    (h : SameAllocSubtree allBorrows (.node root children))
    (hroot : isBorrowDescendantOrSelf allBorrows tag root.tag = false) :
    (BorrowSubtree.node root children).containsTag tag = false := by
  have h' := AllSubtrees.node_iff.mp h
  cases hc : (BorrowSubtree.node root children).containsTag tag with
  | false => rfl
  | true =>
    have hd := h'.1.2.2 tag hc
    rw [hroot] at hd
    exact Bool.noConfusion hd

/--
**Foreignness is inherited by subtrees.** In a structurally well-formed
subtree, an access that is foreign to the root (its tag is not a
descendant-or-self of the root) is foreign to every entry of the subtree.
-/
theorem SameAllocSubtree.foreign_of_root_foreign
    {allBorrows : List BorrowEntry} {root : BorrowEntry}
    {children : List BorrowSubtree} {tag : Nat}
    (h : SameAllocSubtree allBorrows (.node root children))
    (hroot : isBorrowDescendantOrSelf allBorrows tag root.tag = false) :
    ∀ e, e ∈ (BorrowSubtree.node root children).toList →
      isBorrowDescendantOrSelf allBorrows tag e.tag = false :=
  SameAllocSubtree.foreign_of_not_containsTag _ h
    (SameAllocSubtree.not_containsTag_of_root_foreign h hroot)

/--
In a structurally well-formed subtree, an access that is foreign to the root
goes through a tag carried by no entry of the subtree.
-/
theorem SameAllocSubtree.tag_ne_of_root_foreign
    {allBorrows : List BorrowEntry} {root : BorrowEntry}
    {children : List BorrowSubtree} {tag : Nat}
    (h : SameAllocSubtree allBorrows (.node root children))
    (hroot : isBorrowDescendantOrSelf allBorrows tag root.tag = false) :
    ∀ e, e ∈ (BorrowSubtree.node root children).toList →
      Nat.beq e.tag tag = false :=
  BorrowSubtree.tag_ne_of_not_containsTag _
    (SameAllocSubtree.not_containsTag_of_root_foreign h hroot)

/-! ### 1.3 Generic pruned traversals -/

mutual
/--
Pruned map over a subtree: when `skip root` holds the whole subtree is
returned unchanged without visiting `children`; otherwise the root is updated
by `upd` and the children are traversed.
-/
def pruneMapSubtree (skip : BorrowEntry → Bool)
    (upd : BorrowEntry → BorrowEntry) : BorrowSubtree → BorrowSubtree
  | .node root children =>
    match skip root with
    | true => .node root children
    | false => .node (upd root) (pruneMapForest skip upd children)
/-- Pruned map over a forest. -/
def pruneMapForest (skip : BorrowEntry → Bool)
    (upd : BorrowEntry → BorrowEntry) : List BorrowSubtree → List BorrowSubtree
  | [] => []
  | t :: ts => pruneMapSubtree skip upd t :: pruneMapForest skip upd ts
end

mutual
/--
Pruned existential test over a subtree: when `skip root` holds the test is
`false` without visiting `children`; otherwise the root is tested by `test`
and, if that fails, the children are traversed.
-/
def pruneAnySubtree (skip : BorrowEntry → Bool) (test : BorrowEntry → Bool) :
    BorrowSubtree → Bool
  | .node root children =>
    match skip root with
    | true => false
    | false =>
      match test root with
      | true => true
      | false => pruneAnyForest skip test children
/-- Pruned existential test over a forest. -/
def pruneAnyForest (skip : BorrowEntry → Bool) (test : BorrowEntry → Bool) :
    List BorrowSubtree → Bool
  | [] => false
  | t :: ts =>
    match pruneAnySubtree skip test t with
    | true => true
    | false => pruneAnyForest skip test ts
end

/--
**O(1) short-circuit.** A skipped subtree is returned as is, for arbitrary
`children`: the pruned map does not inspect the children of a skipped root.
-/
theorem pruneMapSubtree_skip {skip : BorrowEntry → Bool}
    {upd : BorrowEntry → BorrowEntry} {root : BorrowEntry}
    (children : List BorrowSubtree) (h : skip root = true) :
    pruneMapSubtree skip upd (.node root children) = .node root children := by
  rw [pruneMapSubtree, h]

/-- A visited (not skipped) root is updated and its children traversed. -/
theorem pruneMapSubtree_visit {skip : BorrowEntry → Bool}
    {upd : BorrowEntry → BorrowEntry} {root : BorrowEntry}
    (children : List BorrowSubtree) (h : skip root = false) :
    pruneMapSubtree skip upd (.node root children) =
      .node (upd root) (pruneMapForest skip upd children) := by
  rw [pruneMapSubtree, h]

/--
**O(1) short-circuit.** A skipped subtree tests `false`, for arbitrary
`children`: the pruned test does not inspect the children of a skipped root.
-/
theorem pruneAnySubtree_skip {skip test : BorrowEntry → Bool}
    {root : BorrowEntry} (children : List BorrowSubtree)
    (h : skip root = true) :
    pruneAnySubtree skip test (.node root children) = false := by
  rw [pruneAnySubtree, h]

/-- A visited (not skipped) root is tested before its children. -/
theorem pruneAnySubtree_visit {skip test : BorrowEntry → Bool}
    {root : BorrowEntry} (children : List BorrowSubtree)
    (h : skip root = false) :
    pruneAnySubtree skip test (.node root children) =
      (test root || pruneAnyForest skip test children) := by
  rw [pruneAnySubtree, h]
  cases test root <;> rfl

theorem pruneMapForest_nil (skip : BorrowEntry → Bool)
    (upd : BorrowEntry → BorrowEntry) : pruneMapForest skip upd [] = [] := by
  rw [pruneMapForest]

theorem pruneMapForest_cons (skip : BorrowEntry → Bool)
    (upd : BorrowEntry → BorrowEntry) (t : BorrowSubtree)
    (ts : List BorrowSubtree) :
    pruneMapForest skip upd (t :: ts) =
      pruneMapSubtree skip upd t :: pruneMapForest skip upd ts := by
  rw [pruneMapForest]

theorem pruneAnyForest_nil (skip test : BorrowEntry → Bool) :
    pruneAnyForest skip test [] = false := by
  rw [pruneAnyForest]

theorem pruneAnyForest_cons (skip test : BorrowEntry → Bool) (t : BorrowSubtree)
    (ts : List BorrowSubtree) :
    pruneAnyForest skip test (t :: ts) =
      (pruneAnySubtree skip test t || pruneAnyForest skip test ts) := by
  rw [pruneAnyForest]
  cases pruneAnySubtree skip test t <;> rfl

/--
Soundness condition of a skip decision for a pruned map at one node: a
skipped root and all its descendants are fixed by the update.
-/
def MapSkipSoundNode (skip : BorrowEntry → Bool)
    (upd : BorrowEntry → BorrowEntry) (root : BorrowEntry)
    (children : List BorrowSubtree) : Prop :=
  skip root = true →
    upd root = root ∧ ∀ e, e ∈ BorrowForest.toList children → upd e = e

/--
Soundness condition of a skip decision for a pruned test at one node: the
test fails on a skipped root and on all its descendants.
-/
def AnySkipSoundNode (skip test : BorrowEntry → Bool) (root : BorrowEntry)
    (children : List BorrowSubtree) : Prop :=
  skip root = true →
    test root = false ∧ ∀ e, e ∈ BorrowForest.toList children → test e = false

mutual
/--
A pruned map with sound skips flattens to the full map of the flattened
subtree.
-/
theorem pruneMapSubtree_toList {skip : BorrowEntry → Bool}
    {upd : BorrowEntry → BorrowEntry} :
    ∀ (t : BorrowSubtree), AllSubtrees (MapSkipSoundNode skip upd) t →
      (pruneMapSubtree skip upd t).toList = t.toList.map upd
  | .node root children, h => by
    have h' := AllSubtrees.node_iff.mp h
    cases hs : skip root with
    | true =>
      obtain ⟨hroot, hch⟩ := h'.1 hs
      rw [pruneMapSubtree_skip children hs, BorrowSubtree.toList_node]
      show root :: BorrowForest.toList children =
        upd root :: (BorrowForest.toList children).map upd
      rw [hroot, map_eq_self_of_forall upd _ hch]
    | false =>
      rw [pruneMapSubtree_visit children hs, BorrowSubtree.toList_node,
        BorrowSubtree.toList_node, pruneMapForest_toList children h'.2]
      rfl
/-- Forest form of `pruneMapSubtree_toList`. -/
theorem pruneMapForest_toList {skip : BorrowEntry → Bool}
    {upd : BorrowEntry → BorrowEntry} :
    ∀ (ts : List BorrowSubtree),
      AllSubtreesForest (MapSkipSoundNode skip upd) ts →
      BorrowForest.toList (pruneMapForest skip upd ts) =
        (BorrowForest.toList ts).map upd
  | [], _ => by
    rw [pruneMapForest_nil, BorrowForest.toList_nil]
    rfl
  | t :: ts, h => by
    have h' := AllSubtreesForest.cons_iff.mp h
    rw [pruneMapForest_cons, BorrowForest.toList_cons, BorrowForest.toList_cons,
      pruneMapSubtree_toList t h'.1, pruneMapForest_toList ts h'.2,
      map_append']
end

mutual
/--
A pruned test with sound skips agrees with the full test of the flattened
subtree.
-/
theorem pruneAnySubtree_eq_any {skip test : BorrowEntry → Bool} :
    ∀ (t : BorrowSubtree), AllSubtrees (AnySkipSoundNode skip test) t →
      pruneAnySubtree skip test t = t.toList.any test
  | .node root children, h => by
    have h' := AllSubtrees.node_iff.mp h
    cases hs : skip root with
    | true =>
      obtain ⟨hroot, hch⟩ := h'.1 hs
      rw [pruneAnySubtree_skip children hs, BorrowSubtree.toList_node]
      show false = (test root || (BorrowForest.toList children).any test)
      rw [hroot, any_eq_false_of_forall test _ hch]
      rfl
    | false =>
      rw [pruneAnySubtree_visit children hs, BorrowSubtree.toList_node,
        pruneAnyForest_eq_any children h'.2]
      rfl
/-- Forest form of `pruneAnySubtree_eq_any`. -/
theorem pruneAnyForest_eq_any {skip test : BorrowEntry → Bool} :
    ∀ (ts : List BorrowSubtree),
      AllSubtreesForest (AnySkipSoundNode skip test) ts →
      pruneAnyForest skip test ts = (BorrowForest.toList ts).any test
  | [], _ => by
    rw [pruneAnyForest_nil, BorrowForest.toList_nil]
    rfl
  | t :: ts, h => by
    have h' := AllSubtreesForest.cons_iff.mp h
    rw [pruneAnyForest_cons, BorrowForest.toList_cons,
      pruneAnySubtree_eq_any t h'.1, pruneAnyForest_eq_any ts h'.2,
      any_append']
end

mutual
/--
A pruned map preserves every entry projection that the update preserves, with
no invariant on the subtree.
-/
theorem pruneMapSubtree_map_proj {β : Type} {skip : BorrowEntry → Bool}
    {upd : BorrowEntry → BorrowEntry} (f : BorrowEntry → β)
    (hf : ∀ e, f (upd e) = f e) :
    ∀ (t : BorrowSubtree),
      (pruneMapSubtree skip upd t).toList.map f = t.toList.map f
  | .node root children => by
    cases hs : skip root with
    | true => rw [pruneMapSubtree_skip children hs]
    | false =>
      rw [pruneMapSubtree_visit children hs, BorrowSubtree.toList_node,
        BorrowSubtree.toList_node]
      show f (upd root) ::
          (BorrowForest.toList (pruneMapForest skip upd children)).map f =
        f root :: (BorrowForest.toList children).map f
      rw [hf root, pruneMapForest_map_proj f hf children]
/-- Forest form of `pruneMapSubtree_map_proj`. -/
theorem pruneMapForest_map_proj {β : Type} {skip : BorrowEntry → Bool}
    {upd : BorrowEntry → BorrowEntry} (f : BorrowEntry → β)
    (hf : ∀ e, f (upd e) = f e) :
    ∀ (ts : List BorrowSubtree),
      (BorrowForest.toList (pruneMapForest skip upd ts)).map f =
        (BorrowForest.toList ts).map f
  | [] => by rw [pruneMapForest_nil]
  | t :: ts => by
    rw [pruneMapForest_cons, BorrowForest.toList_cons, BorrowForest.toList_cons,
      map_append', map_append', pruneMapSubtree_map_proj f hf t,
      pruneMapForest_map_proj f hf ts]
end


/-! ### 1.4 Per-node access lemmas -/

/-- A foreign-read no-op permission is fixed by the foreign-read access. -/
theorem foreignRead_noop_transition (perm : TreeBorrowPerm) (isProt : Bool)
    (h : isForeignReadNoopPerm isProt perm = true) :
    treeBorrowNodeAccess .read .foreignAccess perm isProt =
      .transition perm := by
  cases perm with
  | cell => cases isProt <;> rfl
  | frozen => cases isProt <;> rfl
  | disabled => rfl
  | reservedFrz conflicted =>
    cases isProt with
    | false => rfl
    | true =>
      have hc : conflicted = true := h
      rw [hc]
      rfl
  | reservedIM =>
    cases isProt with
    | false => rfl
    | true => exact Bool.noConfusion h
  | unique => exact Bool.noConfusion h

/-- A foreign-write no-op permission is fixed by the foreign-write access. -/
theorem foreignWrite_noop_transition (perm : TreeBorrowPerm) (isProt : Bool)
    (h : isForeignWriteNoopPerm isProt perm = true) :
    treeBorrowNodeAccess .write .foreignAccess perm isProt =
      .transition perm := by
  cases perm with
  | cell => cases isProt <;> rfl
  | disabled => rfl
  | reservedIM =>
    cases isProt with
    | false => rfl
    | true => exact Bool.noConfusion h
  | reservedFrz conflicted => exact Bool.noConfusion h
  | unique => exact Bool.noConfusion h
  | frozen => exact Bool.noConfusion h

/-- A foreign-write no-op under any protection status is one when
unprotected. -/
theorem isForeignWriteNoopPerm_unprotected {isProt : Bool}
    {perm : TreeBorrowPerm}
    (h : isForeignWriteNoopPerm isProt perm = true) :
    isForeignWriteNoopPerm false perm = true := by
  cases perm <;> first
    | rfl
    | exact Bool.noConfusion h

/-- Re-installing the current permission leaves an entry unchanged. -/
theorem applyTreeBorrowTransition_self (entry : BorrowEntry) :
    applyTreeBorrowTransition entry (.transition entry.perm) = entry := by
  cases entry
  rfl

/-- Every tag is a descendant-or-self of itself. -/
theorem isBorrowDescendantOrSelf_self (borrows : List BorrowEntry) (tag : Nat) :
    isBorrowDescendantOrSelf borrows tag tag = true := by
  unfold isBorrowDescendantOrSelf
  cases length borrows with
  | zero => exact Nat.beq_refl tag
  | succ fuel =>
    show (match Nat.beq tag tag with
      | true => true
      | false =>
        match lookupBorrow borrows tag with
        | .some entry =>
          match entry.parentTag with
          | .some pTag => isBorrowDescendantOrSelfAux fuel borrows pTag tag
          | .none => false
        | .none => false) = true
    rw [Nat.beq_refl]

/--
An entry of an unrelated root's allocation is unrelated: if the root does not
target `(targetFrameDepth, targetLocal)` and `entry` targets the root's
allocation, then `entry` does not target `(targetFrameDepth, targetLocal)`.
-/
theorem unrelated_of_unrelated_root {root entry : BorrowEntry}
    {targetLocal : Local} {targetFrameDepth : Nat}
    (hroot : isForeignUnrelatedRoot root targetLocal targetFrameDepth = true)
    (hd : entry.targetFrameDepth = root.targetFrameDepth)
    (hl : entry.targetLocal = root.targetLocal) :
    Bool.and (Nat.beq entry.targetFrameDepth targetFrameDepth)
      (Nat.beq entry.targetLocal targetLocal) = false := by
  rw [hd, hl]
  unfold isForeignUnrelatedRoot at hroot
  cases hb : Bool.and (Nat.beq root.targetFrameDepth targetFrameDepth)
      (Nat.beq root.targetLocal targetLocal) with
  | false => rfl
  | true =>
    rw [hb] at hroot
    exact Bool.noConfusion hroot

/-- A root that is not unrelated targets `(targetFrameDepth, targetLocal)`. -/
theorem related_of_not_unrelated_root {root : BorrowEntry} {targetLocal : Local}
    {targetFrameDepth : Nat}
    (hroot : isForeignUnrelatedRoot root targetLocal targetFrameDepth = false) :
    Bool.and (Nat.beq root.targetFrameDepth targetFrameDepth)
      (Nat.beq root.targetLocal targetLocal) = true := by
  unfold isForeignUnrelatedRoot at hroot
  cases hb : Bool.and (Nat.beq root.targetFrameDepth targetFrameDepth)
      (Nat.beq root.targetLocal targetLocal) with
  | true => rfl
  | false =>
    rw [hb] at hroot
    exact Bool.noConfusion hroot

/-! #### Reads -/

/-- A read leaves an entry of another allocation unchanged. -/
theorem updateBorrowPermOnReadAtProj_unrelated (allBorrows : List BorrowEntry)
    (entry : BorrowEntry) (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem) (readRangeOff readRangeLen : Nat)
    (activeProtectors : List Nat) (targetFrameDepth : Nat)
    (h : Bool.and (Nat.beq entry.targetFrameDepth targetFrameDepth)
      (Nat.beq entry.targetLocal targetLocal) = false) :
    updateBorrowPermOnReadAtProj allBorrows entry targetLocal readerTag readProj
      readRangeOff readRangeLen activeProtectors targetFrameDepth = entry := by
  unfold updateBorrowPermOnReadAtProj
  rw [h]

/--
A read leaves a foreign-read no-op entry unchanged, whether the read is local
or foreign to the entry.
-/
theorem updateBorrowPermOnReadAtProj_noop (allBorrows : List BorrowEntry)
    (entry : BorrowEntry) (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem) (readRangeOff readRangeLen : Nat)
    (activeProtectors : List Nat) (targetFrameDepth : Nat)
    (h : isForeignReadNoopPerm (isBorrowProtected activeProtectors entry)
      entry.perm = true) :
    updateBorrowPermOnReadAtProj allBorrows entry targetLocal readerTag readProj
      readRangeOff readRangeLen activeProtectors targetFrameDepth = entry := by
  unfold updateBorrowPermOnReadAtProj
  split
  · rfl
  · split
    · rfl
    · dsimp only []
      split
      · rfl
      · rw [foreignRead_noop_transition _ _ h]
        exact applyTreeBorrowTransition_self entry

/-- Per-node fast skip: a read never changes a `.disabled` entry. -/
theorem updateBorrowPermOnReadAtProj_disabled (allBorrows : List BorrowEntry)
    (entry : BorrowEntry) (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem) (readRangeOff readRangeLen : Nat)
    (activeProtectors : List Nat) (targetFrameDepth : Nat)
    (h : entry.perm = .disabled) :
    updateBorrowPermOnReadAtProj allBorrows entry targetLocal readerTag readProj
      readRangeOff readRangeLen activeProtectors targetFrameDepth = entry :=
  updateBorrowPermOnReadAtProj_noop allBorrows entry targetLocal readerTag
    readProj readRangeOff readRangeLen activeProtectors targetFrameDepth
    (by rw [h]; rfl)

/-- Per-node fast skip: a read never changes a `.frozen` entry. -/
theorem updateBorrowPermOnReadAtProj_frozen (allBorrows : List BorrowEntry)
    (entry : BorrowEntry) (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem) (readRangeOff readRangeLen : Nat)
    (activeProtectors : List Nat) (targetFrameDepth : Nat)
    (h : entry.perm = .frozen) :
    updateBorrowPermOnReadAtProj allBorrows entry targetLocal readerTag readProj
      readRangeOff readRangeLen activeProtectors targetFrameDepth = entry :=
  updateBorrowPermOnReadAtProj_noop allBorrows entry targetLocal readerTag
    readProj readRangeOff readRangeLen activeProtectors targetFrameDepth
    (by rw [h]; rfl)

/-- A read preserves the protector of every entry. -/
theorem updateBorrowPermOnReadAtProj_protector (allBorrows : List BorrowEntry)
    (entry : BorrowEntry) (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem) (readRangeOff readRangeLen : Nat)
    (activeProtectors : List Nat) (targetFrameDepth : Nat) :
    (updateBorrowPermOnReadAtProj allBorrows entry targetLocal readerTag
      readProj readRangeOff readRangeLen activeProtectors
      targetFrameDepth).protector = entry.protector := by
  unfold updateBorrowPermOnReadAtProj
  split
  · rfl
  · split
    · rfl
    · dsimp only []
      split
      · rfl
      · exact (applyTreeBorrowTransition_fields entry _).2.2.2.2.2.1

/-- A read preserves the tag of every entry. -/
theorem updateBorrowPermOnReadAtProj_tag (allBorrows : List BorrowEntry)
    (entry : BorrowEntry) (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem) (readRangeOff readRangeLen : Nat)
    (activeProtectors : List Nat) (targetFrameDepth : Nat) :
    (updateBorrowPermOnReadAtProj allBorrows entry targetLocal readerTag
      readProj readRangeOff readRangeLen activeProtectors
      targetFrameDepth).tag = entry.tag := by
  unfold updateBorrowPermOnReadAtProj
  split
  · rfl
  · split
    · rfl
    · dsimp only []
      split
      · rfl
      · exact (applyTreeBorrowTransition_fields entry _).1

/-- A read is never undefined behavior at an entry of another allocation. -/
theorem borrowEntryReadUB_unrelated (allBorrows : List BorrowEntry)
    (activeProtectors : List Nat) (entry : BorrowEntry) (targetLocal : Local)
    (readerTag : Option Nat) (readProj : List ProjectionElem)
    (readRangeOff readRangeLen targetFrameDepth : Nat)
    (h : Bool.and (Nat.beq entry.targetFrameDepth targetFrameDepth)
      (Nat.beq entry.targetLocal targetLocal) = false) :
    borrowEntryReadUB allBorrows activeProtectors entry targetLocal readerTag
      readProj readRangeOff readRangeLen targetFrameDepth = false := by
  unfold borrowEntryReadUB
  rw [h]

/--
A read that is foreign to a foreign-read no-op entry is not undefined
behavior at that entry.
-/
theorem borrowEntryReadUB_foreign_noop (allBorrows : List BorrowEntry)
    (activeProtectors : List Nat) (entry : BorrowEntry) (targetLocal : Local)
    (readerTag : Option Nat) (readProj : List ProjectionElem)
    (readRangeOff readRangeLen targetFrameDepth : Nat)
    (hf : ∀ tag, readerTag = some tag →
      isBorrowDescendantOrSelf allBorrows tag entry.tag = false)
    (h : isForeignReadNoopPerm (isBorrowProtected activeProtectors entry)
      entry.perm = true) :
    borrowEntryReadUB allBorrows activeProtectors entry targetLocal readerTag
      readProj readRangeOff readRangeLen targetFrameDepth = false := by
  unfold borrowEntryReadUB
  split
  · rfl
  · split
    · rfl
    · cases readerTag with
      | none =>
        dsimp only []
        rw [foreignRead_noop_transition _ _ h]
        rfl
      | some tag =>
        dsimp only []
        rw [hf tag rfl]
        dsimp only []
        rw [foreignRead_noop_transition _ _ h]
        rfl

/-- The trusted read freeze is the map of its per-entry update. -/
theorem freezeTreeBorrowsOnReadAtProj_eq_map (allBorrows : List BorrowEntry)
    (borrows : List BorrowEntry) (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem) (readRangeOff readRangeLen : Nat)
    (activeProtectors : List Nat) (targetFrameDepth : Nat) :
    freezeTreeBorrowsOnReadAtProj allBorrows borrows targetLocal readerTag
        readProj readRangeOff readRangeLen activeProtectors targetFrameDepth =
      borrows.map fun e =>
        updateBorrowPermOnReadAtProj allBorrows e targetLocal readerTag readProj
          readRangeOff readRangeLen activeProtectors targetFrameDepth := by
  induction borrows with
  | nil => rfl
  | cons e rest ih =>
    show updateBorrowPermOnReadAtProj allBorrows e targetLocal readerTag
        readProj readRangeOff readRangeLen activeProtectors targetFrameDepth ::
      freezeTreeBorrowsOnReadAtProj allBorrows rest targetLocal readerTag
        readProj readRangeOff readRangeLen activeProtectors targetFrameDepth = _
    rw [ih]
    rfl

/-- The trusted read undefined-behavior scan is `List.any` of its per-entry
test. -/
theorem hasTreeReadUB_eq_any (allBorrows : List BorrowEntry)
    (borrows : List BorrowEntry) (activeProtectors : List Nat)
    (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem)
    (readRangeOff readRangeLen targetFrameDepth : Nat) :
    hasTreeReadUB allBorrows borrows activeProtectors targetLocal readerTag
        readProj readRangeOff readRangeLen targetFrameDepth =
      borrows.any fun e =>
        borrowEntryReadUB allBorrows activeProtectors e targetLocal readerTag
          readProj readRangeOff readRangeLen targetFrameDepth := by
  induction borrows with
  | nil => rfl
  | cons e rest ih =>
    show (match borrowEntryReadUB allBorrows activeProtectors e targetLocal
        readerTag readProj readRangeOff readRangeLen targetFrameDepth with
      | true => true
      | false =>
        hasTreeReadUB allBorrows rest activeProtectors targetLocal readerTag
          readProj readRangeOff readRangeLen targetFrameDepth) = _
    rw [ih]
    show _ = (borrowEntryReadUB allBorrows activeProtectors e targetLocal
      readerTag readProj readRangeOff readRangeLen targetFrameDepth ||
        rest.any _)
    cases borrowEntryReadUB allBorrows activeProtectors e targetLocal readerTag
      readProj readRangeOff readRangeLen targetFrameDepth <;> rfl

/-! #### Writes -/

/--
The simple writer relatedness is foreign when the entry's tag is not the
writer tag.
-/
theorem treeBorrowWriterRelatedness_foreign (entry : BorrowEntry)
    (writerTag : Option Nat)
    (hf : ∀ tag, writerTag = some tag → Nat.beq entry.tag tag = false) :
    treeBorrowWriterRelatedness entry writerTag = .foreignAccess := by
  cases writerTag with
  | none => rfl
  | some tag =>
    show (match Nat.beq entry.tag tag with
      | true => TreeBorrowRelatedness.localAccess
      | false => TreeBorrowRelatedness.foreignAccess) = .foreignAccess
    rw [hf tag rfl]

/--
The tree-resolved writer tag of a write that is foreign to `entry` (its tag
is not a descendant-or-self of the entry) differs from the entry's tag.
-/
theorem resolveTreeBorrowWriterTag_foreign (allBorrows : List BorrowEntry)
    (entry : BorrowEntry) (writerTag : Option Nat)
    (hf : ∀ tag, writerTag = some tag →
      isBorrowDescendantOrSelf allBorrows tag entry.tag = false) :
    ∀ tag, resolveTreeBorrowWriterTag allBorrows entry writerTag = some tag →
      Nat.beq entry.tag tag = false := by
  intro tag hres
  cases writerTag with
  | none => cases hres
  | some w =>
    have hw := hf w rfl
    have hres' : (match isBorrowDescendantOrSelf allBorrows w entry.tag with
        | true => some entry.tag
        | false => some w) = some tag := hres
    rw [hw] at hres'
    cases hres'
    cases hb : Nat.beq entry.tag tag with
    | false => rfl
    | true =>
      have heq : entry.tag = tag := Nat.eq_of_beq_eq_true hb
      rw [heq, isBorrowDescendantOrSelf_self] at hw
      exact Bool.noConfusion hw

/-- A projection-sensitive write leaves an entry of another allocation
unchanged. -/
theorem updateBorrowPermAtProj_unrelated (entry : BorrowEntry)
    (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat)
    (h : Bool.and (Nat.beq entry.targetFrameDepth targetFrameDepth)
      (Nat.beq entry.targetLocal targetLocal) = false) :
    updateBorrowPermAtProj entry targetLocal writerTag writeProj writeRangeOff
      writeRangeLen targetFrameDepth = entry := by
  unfold updateBorrowPermAtProj
  rw [h]

/--
A projection-sensitive write through another tag leaves a foreign-write no-op
entry unchanged.
-/
theorem updateBorrowPermAtProj_foreign_noop (entry : BorrowEntry)
    (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat)
    (hf : ∀ tag, writerTag = some tag → Nat.beq entry.tag tag = false)
    (h : isForeignWriteNoopPerm false entry.perm = true) :
    updateBorrowPermAtProj entry targetLocal writerTag writeProj writeRangeOff
      writeRangeLen targetFrameDepth = entry := by
  unfold updateBorrowPermAtProj
  rw [treeBorrowWriterRelatedness_foreign entry writerTag hf]
  split
  · rfl
  · dsimp only []
    split
    · rfl
    · rw [foreignWrite_noop_transition _ _ h]
      exact applyTreeBorrowTransition_self entry

/-- A simple write leaves an entry of another allocation unchanged. -/
theorem updateBorrowPerm_unrelated (entry : BorrowEntry) (targetLocal : Local)
    (writerTag : Option Nat) (targetFrameDepth : Nat)
    (h : Bool.and (Nat.beq entry.targetFrameDepth targetFrameDepth)
      (Nat.beq entry.targetLocal targetLocal) = false) :
    updateBorrowPerm entry targetLocal writerTag targetFrameDepth = entry := by
  unfold updateBorrowPerm
  rw [h]

/-- A simple write through another tag leaves a foreign-write no-op entry
unchanged. -/
theorem updateBorrowPerm_foreign_noop (entry : BorrowEntry)
    (targetLocal : Local) (writerTag : Option Nat) (targetFrameDepth : Nat)
    (hf : ∀ tag, writerTag = some tag → Nat.beq entry.tag tag = false)
    (h : isForeignWriteNoopPerm false entry.perm = true) :
    updateBorrowPerm entry targetLocal writerTag targetFrameDepth = entry := by
  unfold updateBorrowPerm
  rw [treeBorrowWriterRelatedness_foreign entry writerTag hf]
  split
  · rfl
  · rw [foreignWrite_noop_transition _ _ h]
    exact applyTreeBorrowTransition_self entry

/-- A tree write leaves an entry of another allocation unchanged. -/
theorem updateBorrowPermTreeAtProj_unrelated (allBorrows : List BorrowEntry)
    (entry : BorrowEntry) (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat)
    (h : Bool.and (Nat.beq entry.targetFrameDepth targetFrameDepth)
      (Nat.beq entry.targetLocal targetLocal) = false) :
    updateBorrowPermTreeAtProj allBorrows entry targetLocal writerTag writeProj
      writeRangeOff writeRangeLen targetFrameDepth = entry :=
  updateBorrowPermAtProj_unrelated entry targetLocal _ writeProj writeRangeOff
    writeRangeLen targetFrameDepth h

/--
A tree write that is foreign to a foreign-write no-op entry leaves the entry
unchanged.
-/
theorem updateBorrowPermTreeAtProj_foreign_noop (allBorrows : List BorrowEntry)
    (entry : BorrowEntry) (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat)
    (hf : ∀ tag, writerTag = some tag →
      isBorrowDescendantOrSelf allBorrows tag entry.tag = false)
    (h : isForeignWriteNoopPerm false entry.perm = true) :
    updateBorrowPermTreeAtProj allBorrows entry targetLocal writerTag writeProj
      writeRangeOff writeRangeLen targetFrameDepth = entry :=
  updateBorrowPermAtProj_foreign_noop entry targetLocal _ writeProj
    writeRangeOff writeRangeLen targetFrameDepth
    (resolveTreeBorrowWriterTag_foreign allBorrows entry writerTag hf) h

/--
Per-node fast skip: a tree write never changes a `.disabled` entry, whether
the write is local (forbidden child write, entry kept) or foreign.
-/
theorem updateBorrowPermTreeAtProj_disabled (allBorrows : List BorrowEntry)
    (entry : BorrowEntry) (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat)
    (h : entry.perm = .disabled) :
    updateBorrowPermTreeAtProj allBorrows entry targetLocal writerTag writeProj
      writeRangeOff writeRangeLen targetFrameDepth = entry := by
  unfold updateBorrowPermTreeAtProj updateBorrowPermAtProj
  split
  · rfl
  · split
    · rw [h]
      rfl
    · split
      · rfl
      · rw [h]
        show applyTreeBorrowTransition entry (.transition .disabled) = entry
        rw [← h]
        exact applyTreeBorrowTransition_self entry

/--
Per-node fast skip: a tree write never changes a `.cell` entry, whether the
write is local or foreign.
-/
theorem updateBorrowPermTreeAtProj_cell (allBorrows : List BorrowEntry)
    (entry : BorrowEntry) (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat)
    (h : entry.perm = .cell) :
    updateBorrowPermTreeAtProj allBorrows entry targetLocal writerTag writeProj
      writeRangeOff writeRangeLen targetFrameDepth = entry := by
  unfold updateBorrowPermTreeAtProj updateBorrowPermAtProj
  split
  · rfl
  · split
    · rw [h]
      show applyTreeBorrowTransition entry (.transition .cell) = entry
      rw [← h]
      exact applyTreeBorrowTransition_self entry
    · split
      · rfl
      · rw [h]
        show applyTreeBorrowTransition entry (.transition .cell) = entry
        rw [← h]
        exact applyTreeBorrowTransition_self entry

/-- A projection-sensitive write preserves the protector of every entry. -/
theorem updateBorrowPermAtProj_protector (entry : BorrowEntry)
    (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat) :
    (updateBorrowPermAtProj entry targetLocal writerTag writeProj writeRangeOff
      writeRangeLen targetFrameDepth).protector = entry.protector := by
  unfold updateBorrowPermAtProj
  split
  · rfl
  · split
    · exact (applyTreeBorrowTransition_fields entry _).2.2.2.2.2.1
    · split
      · rfl
      · exact (applyTreeBorrowTransition_fields entry _).2.2.2.2.2.1

/-- A projection-sensitive write preserves the tag of every entry. -/
theorem updateBorrowPermAtProj_tag (entry : BorrowEntry)
    (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat) :
    (updateBorrowPermAtProj entry targetLocal writerTag writeProj writeRangeOff
      writeRangeLen targetFrameDepth).tag = entry.tag := by
  unfold updateBorrowPermAtProj
  split
  · rfl
  · split
    · exact (applyTreeBorrowTransition_fields entry _).1
    · split
      · rfl
      · exact (applyTreeBorrowTransition_fields entry _).1

/-- A simple write preserves the protector of every entry. -/
theorem updateBorrowPerm_protector (entry : BorrowEntry) (targetLocal : Local)
    (writerTag : Option Nat) (targetFrameDepth : Nat) :
    (updateBorrowPerm entry targetLocal writerTag targetFrameDepth).protector =
      entry.protector := by
  unfold updateBorrowPerm
  split
  · rfl
  · exact (applyTreeBorrowTransition_fields entry _).2.2.2.2.2.1

/-- The trusted tree write is the map of its per-entry update. -/
theorem invalidateTreeBorrowsAtProj_eq_map (allBorrows : List BorrowEntry)
    (borrows : List BorrowEntry) (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat) :
    invalidateTreeBorrowsAtProj allBorrows borrows targetLocal writerTag
        writeProj writeRangeOff writeRangeLen targetFrameDepth =
      borrows.map fun e =>
        updateBorrowPermTreeAtProj allBorrows e targetLocal writerTag writeProj
          writeRangeOff writeRangeLen targetFrameDepth := by
  induction borrows with
  | nil => rfl
  | cons e rest ih =>
    show updateBorrowPermTreeAtProj allBorrows e targetLocal writerTag writeProj
        writeRangeOff writeRangeLen targetFrameDepth ::
      invalidateTreeBorrowsAtProj allBorrows rest targetLocal writerTag
        writeProj writeRangeOff writeRangeLen targetFrameDepth = _
    rw [ih]
    rfl

/-- The trusted simple write is the map of its per-entry update. -/
theorem invalidateConflictingBorrows_eq_map (borrows : List BorrowEntry)
    (targetLocal : Local) (writerTag : Option Nat) (targetFrameDepth : Nat) :
    invalidateConflictingBorrows borrows targetLocal writerTag
        targetFrameDepth =
      borrows.map fun e =>
        updateBorrowPerm e targetLocal writerTag targetFrameDepth := by
  induction borrows with
  | nil => rfl
  | cons e rest ih =>
    show updateBorrowPerm e targetLocal writerTag targetFrameDepth ::
      invalidateConflictingBorrows rest targetLocal writerTag targetFrameDepth =
        _
    rw [ih]
    rfl

/-- The trusted projection-sensitive write is the map of its per-entry
update. -/
theorem invalidateConflictingBorrowsAtProj_eq_map (borrows : List BorrowEntry)
    (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat) :
    invalidateConflictingBorrowsAtProj borrows targetLocal writerTag writeProj
        writeRangeOff writeRangeLen targetFrameDepth =
      borrows.map fun e =>
        updateBorrowPermAtProj e targetLocal writerTag writeProj writeRangeOff
          writeRangeLen targetFrameDepth := by
  induction borrows with
  | nil => rfl
  | cons e rest ih =>
    show updateBorrowPermAtProj e targetLocal writerTag writeProj writeRangeOff
        writeRangeLen targetFrameDepth ::
      invalidateConflictingBorrowsAtProj rest targetLocal writerTag writeProj
        writeRangeOff writeRangeLen targetFrameDepth = _
    rw [ih]
    rfl

/--
Per-entry test of the trusted protected-write conflict scan
`hasProtectedWriteConflict`.
-/
def protectedWriteConflictAt (activeProtectors : List Nat) (targetLocal : Local)
    (writerTag : Option Nat) (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat) (entry : BorrowEntry) :
    Bool :=
  Bool.and
    (Bool.and (Nat.beq entry.targetFrameDepth targetFrameDepth)
      (Nat.beq entry.targetLocal targetLocal))
    (Bool.and
      (borrowEntryOverlapsWrite entry writeProj writeRangeOff writeRangeLen)
      (Bool.and (isBorrowProtected activeProtectors entry)
        (borrowEntryWriteConflicts entry writerTag)))

/-- The trusted protected-write conflict scan is `List.any` of its per-entry
test. -/
theorem hasProtectedWriteConflict_eq_any (borrows : List BorrowEntry)
    (activeProtectors : List Nat) (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat) :
    hasProtectedWriteConflict borrows activeProtectors targetLocal writerTag
        writeProj writeRangeOff writeRangeLen targetFrameDepth =
      borrows.any
        (protectedWriteConflictAt activeProtectors targetLocal writerTag
          writeProj writeRangeOff writeRangeLen targetFrameDepth) := by
  induction borrows with
  | nil => rfl
  | cons e rest ih =>
    show (match protectedWriteConflictAt activeProtectors targetLocal writerTag
        writeProj writeRangeOff writeRangeLen targetFrameDepth e with
      | true => true
      | false =>
        hasProtectedWriteConflict rest activeProtectors targetLocal writerTag
          writeProj writeRangeOff writeRangeLen targetFrameDepth) = _
    rw [ih]
    show _ = (protectedWriteConflictAt activeProtectors targetLocal writerTag
      writeProj writeRangeOff writeRangeLen targetFrameDepth e || rest.any _)
    cases protectedWriteConflictAt activeProtectors targetLocal writerTag
      writeProj writeRangeOff writeRangeLen targetFrameDepth e <;> rfl

/-- No protected-write conflict arises at an entry of another allocation. -/
theorem protectedWriteConflictAt_unrelated (activeProtectors : List Nat)
    (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat) (entry : BorrowEntry)
    (h : Bool.and (Nat.beq entry.targetFrameDepth targetFrameDepth)
      (Nat.beq entry.targetLocal targetLocal) = false) :
    protectedWriteConflictAt activeProtectors targetLocal writerTag writeProj
      writeRangeOff writeRangeLen targetFrameDepth entry = false := by
  unfold protectedWriteConflictAt
  rw [h]
  rfl

/--
No protected-write conflict arises at a foreign-write no-op entry (at its own
protection status) when the write goes through another tag.
-/
theorem protectedWriteConflictAt_foreign_noop (activeProtectors : List Nat)
    (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat) (entry : BorrowEntry)
    (hf : ∀ tag, writerTag = some tag → Nat.beq entry.tag tag = false)
    (h : isForeignWriteNoopPerm (isBorrowProtected activeProtectors entry)
      entry.perm = true) :
    protectedWriteConflictAt activeProtectors targetLocal writerTag writeProj
      writeRangeOff writeRangeLen targetFrameDepth entry = false := by
  unfold protectedWriteConflictAt
  cases hp : isBorrowProtected activeProtectors entry with
  | false =>
    cases Bool.and (Nat.beq entry.targetFrameDepth targetFrameDepth)
        (Nat.beq entry.targetLocal targetLocal) <;>
      cases borrowEntryOverlapsWrite entry writeProj writeRangeOff
        writeRangeLen <;> rfl
  | true =>
    rw [hp] at h
    have hc : borrowEntryWriteConflicts entry writerTag = false := by
      unfold borrowEntryWriteConflicts
      rw [treeBorrowWriterRelatedness_foreign entry writerTag hf,
        foreignWrite_noop_transition _ _ h]
      rfl
    rw [hc]
    cases Bool.and (Nat.beq entry.targetFrameDepth targetFrameDepth)
        (Nat.beq entry.targetLocal targetLocal) <;>
      cases borrowEntryOverlapsWrite entry writeProj writeRangeOff
        writeRangeLen <;> rfl


/-! ### 1.5 Pruned traversals and exact equivalence with the full scans -/

/-- Left projection of a conjunction of node invariants. -/
theorem AllSubtrees.and_left {P Q : BorrowEntry → List BorrowSubtree → Prop}
    {t : BorrowSubtree}
    (h : AllSubtrees (fun root children => P root children ∧ Q root children)
      t) : AllSubtrees P t :=
  AllSubtrees.mono_strong
    (fun _ _ hh => (AllSubtrees.node_iff.mp hh).1.1) t h

/-- Right projection of a conjunction of node invariants. -/
theorem AllSubtrees.and_right {P Q : BorrowEntry → List BorrowSubtree → Prop}
    {t : BorrowSubtree}
    (h : AllSubtrees (fun root children => P root children ∧ Q root children)
      t) : AllSubtrees Q t :=
  AllSubtrees.mono_strong
    (fun _ _ hh => (AllSubtrees.node_iff.mp hh).1.2) t h

/--
In a structurally well-formed subtree, an access that is foreign to the root
is foreign to every entry, both for tree relatedness (the access tag is not a
descendant-or-self of the entry) and for simple relatedness (the access tag
is not the entry's tag).
-/
theorem SameAllocSubtree.foreign_to_all {allBorrows : List BorrowEntry}
    {root : BorrowEntry} {children : List BorrowSubtree}
    {accessTag : Option Nat}
    (h : SameAllocSubtree allBorrows (.node root children))
    (hf : accessForeignToRoot allBorrows accessTag root = true) :
    ∀ e, e ∈ (BorrowSubtree.node root children).toList →
      ∀ tag, accessTag = some tag →
        isBorrowDescendantOrSelf allBorrows tag e.tag = false ∧
          Nat.beq e.tag tag = false := by
  intro e he tag htag
  rw [htag] at hf
  have hroot : isBorrowDescendantOrSelf allBorrows tag root.tag = false := by
    cases hd : isBorrowDescendantOrSelf allBorrows tag root.tag with
    | false => rfl
    | true =>
      have hf' : Bool.not (isBorrowDescendantOrSelf allBorrows tag root.tag) =
          true := hf
      rw [hd] at hf'
      exact Bool.noConfusion hf'
  exact ⟨SameAllocSubtree.foreign_of_root_foreign h hroot e he,
    SameAllocSubtree.tag_ne_of_root_foreign h hroot e he⟩

/-- Splitting a true conjunction. -/
private theorem and_eq_true_split {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;>
    first
      | exact ⟨rfl, rfl⟩
      | exact Bool.noConfusion h

/--
Root-level skip decision of the read freeze: the root is unrelated, or it is
a foreign-read no-op. A read fixes a no-op entry whether it is local or
foreign to it, so no relatedness query is needed.
-/
def readSkipRoot (activeProtectors : List Nat) (targetLocal : Local)
    (targetFrameDepth : Nat) (root : BorrowEntry) : Bool :=
  isForeignUnrelatedRoot root targetLocal targetFrameDepth ||
    isForeignReadNoopPerm (isBorrowProtected activeProtectors root) root.perm

/--
Root-level skip decision of the read undefined-behavior scan: the root is
unrelated, or the read is foreign to the root and the root is a foreign-read
no-op.
-/
def readUBSkipRoot (allBorrows : List BorrowEntry) (activeProtectors : List Nat)
    (targetLocal : Local) (readerTag : Option Nat) (targetFrameDepth : Nat)
    (root : BorrowEntry) : Bool :=
  isForeignUnrelatedRoot root targetLocal targetFrameDepth ||
    (accessForeignToRoot allBorrows readerTag root &&
      isForeignReadNoopPerm (isBorrowProtected activeProtectors root) root.perm)

/--
Root-level skip decision of the write traversals: the root is unrelated, or
the write is foreign to the root and the root is a foreign-write no-op.
-/
def writeSkipRoot (allBorrows : List BorrowEntry) (activeProtectors : List Nat)
    (targetLocal : Local) (writerTag : Option Nat) (targetFrameDepth : Nat)
    (root : BorrowEntry) : Bool :=
  isForeignUnrelatedRoot root targetLocal targetFrameDepth ||
    (accessForeignToRoot allBorrows writerTag root &&
      isForeignWriteNoopPerm (isBorrowProtected activeProtectors root)
        root.perm)

/--
Pruned read freeze, matching `freezeTreeBorrowsOnReadAtProj`: skips, without
visiting its children, every subtree whose root is unrelated or a
foreign-read no-op.
-/
def pruneForeignRead (allBorrows : List BorrowEntry) (forest : BorrowForest)
    (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem) (readRangeOff : Nat := 0)
    (readRangeLen : Nat := 0) (activeProtectors : List Nat := .nil)
    (targetFrameDepth : Nat := 0) : BorrowForest :=
  pruneMapForest (readSkipRoot activeProtectors targetLocal targetFrameDepth)
    (fun e =>
      updateBorrowPermOnReadAtProj allBorrows e targetLocal readerTag readProj
        readRangeOff readRangeLen activeProtectors targetFrameDepth)
    forest

/--
Pruned read undefined-behavior scan, matching `hasTreeReadUB`: skips, without
visiting its children, every subtree whose root is unrelated, or is a
foreign-read no-op to which the read is foreign.
-/
def pruneHasTreeReadUB (allBorrows : List BorrowEntry) (forest : BorrowForest)
    (activeProtectors : List Nat) (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem) (readRangeOff : Nat := 0)
    (readRangeLen : Nat := 0) (targetFrameDepth : Nat := 0) : Bool :=
  pruneAnyForest
    (readUBSkipRoot allBorrows activeProtectors targetLocal readerTag
      targetFrameDepth)
    (fun e =>
      borrowEntryReadUB allBorrows activeProtectors e targetLocal readerTag
        readProj readRangeOff readRangeLen targetFrameDepth)
    forest

/--
Pruned tree write, matching `invalidateTreeBorrowsAtProj`: skips, without
visiting its children, every subtree whose root is unrelated, or is a
foreign-write no-op to which the write is foreign.
-/
def pruneForeignWrite (allBorrows : List BorrowEntry) (forest : BorrowForest)
    (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem) (writeRangeOff : Nat := 0)
    (writeRangeLen : Nat := 0) (targetFrameDepth : Nat := 0)
    (activeProtectors : List Nat := .nil) : BorrowForest :=
  pruneMapForest
    (writeSkipRoot allBorrows activeProtectors targetLocal writerTag
      targetFrameDepth)
    (fun e =>
      updateBorrowPermTreeAtProj allBorrows e targetLocal writerTag writeProj
        writeRangeOff writeRangeLen targetFrameDepth)
    forest

/--
Pruned simple write, matching `invalidateConflictingBorrows`. The flat table
`allBorrows` is consulted only for the root-level relatedness query.
-/
def pruneForeignWriteSimple (allBorrows : List BorrowEntry)
    (forest : BorrowForest) (targetLocal : Local) (writerTag : Option Nat)
    (targetFrameDepth : Nat := 0) (activeProtectors : List Nat := .nil) :
    BorrowForest :=
  pruneMapForest
    (writeSkipRoot allBorrows activeProtectors targetLocal writerTag
      targetFrameDepth)
    (fun e => updateBorrowPerm e targetLocal writerTag targetFrameDepth)
    forest

/--
Pruned projection-sensitive write, matching
`invalidateConflictingBorrowsAtProj`.
-/
def pruneForeignWriteProj (allBorrows : List BorrowEntry)
    (forest : BorrowForest) (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem) (writeRangeOff : Nat := 0)
    (writeRangeLen : Nat := 0) (targetFrameDepth : Nat := 0)
    (activeProtectors : List Nat := .nil) : BorrowForest :=
  pruneMapForest
    (writeSkipRoot allBorrows activeProtectors targetLocal writerTag
      targetFrameDepth)
    (fun e =>
      updateBorrowPermAtProj e targetLocal writerTag writeProj writeRangeOff
        writeRangeLen targetFrameDepth)
    forest

/--
Pruned protected-write conflict scan, matching `hasProtectedWriteConflict`.
-/
def pruneHasProtectedWriteConflict (allBorrows : List BorrowEntry)
    (forest : BorrowForest) (activeProtectors : List Nat) (targetLocal : Local)
    (writerTag : Option Nat) (writeProj : List ProjectionElem := .nil)
    (writeRangeOff : Nat := 0) (writeRangeLen : Nat := 0)
    (targetFrameDepth : Nat := 0) : Bool :=
  pruneAnyForest
    (writeSkipRoot allBorrows activeProtectors targetLocal writerTag
      targetFrameDepth)
    (protectedWriteConflictAt activeProtectors targetLocal writerTag writeProj
      writeRangeOff writeRangeLen targetFrameDepth)
    forest

/--
Skip soundness of the read freeze at one node, from the structural and
foreign-read no-op invariants of the subtree rooted there.
-/
theorem readSkip_sound {allBorrows : List BorrowEntry}
    {activeProtectors : List Nat} {targetLocal : Local}
    {readerTag : Option Nat} {readProj : List ProjectionElem}
    {readRangeOff readRangeLen targetFrameDepth : Nat} {root : BorrowEntry}
    {children : List BorrowSubtree}
    (h : AllSubtrees
      (fun r c =>
        SameAllocNode allBorrows r c ∧ ForeignReadNoopNode activeProtectors r c)
      (.node root children)) :
    MapSkipSoundNode
      (readSkipRoot activeProtectors targetLocal targetFrameDepth)
      (fun e =>
        updateBorrowPermOnReadAtProj allBorrows e targetLocal readerTag readProj
          readRangeOff readRangeLen activeProtectors targetFrameDepth)
      root children := by
  intro hs
  obtain ⟨hA, hN⟩ := (AllSubtrees.node_iff.mp h).1
  unfold readSkipRoot at hs
  cases hu : isForeignUnrelatedRoot root targetLocal targetFrameDepth with
  | true =>
    refine ⟨updateBorrowPermOnReadAtProj_unrelated _ _ _ _ _ _ _ _ _
      (unrelated_of_unrelated_root hu rfl rfl), fun e he => ?_⟩
    exact updateBorrowPermOnReadAtProj_unrelated _ _ _ _ _ _ _ _ _
      (unrelated_of_unrelated_root hu (hA.1 e he).1 (hA.1 e he).2)
  | false =>
    rw [hu] at hs
    have hn : isForeignReadNoopPerm (isBorrowProtected activeProtectors root)
        root.perm = true := hs
    refine ⟨updateBorrowPermOnReadAtProj_noop _ _ _ _ _ _ _ _ _ hn,
      fun e he => ?_⟩
    exact updateBorrowPermOnReadAtProj_noop _ _ _ _ _ _ _ _ _ (hN hn e he)

/--
**Exact equivalence of the pruned read freeze.** On a structurally
well-formed forest satisfying the foreign-read no-op subtree invariant, the
pruned read freeze flattens to exactly the trusted full scan
`freezeTreeBorrowsOnReadAtProj` of the flattened forest.
-/
theorem pruneForeignRead_equiv_fullScan {allBorrows : List BorrowEntry}
    {forest : BorrowForest} {activeProtectors : List Nat}
    (hAlloc : SameAllocForest allBorrows forest)
    (hNoop : ForeignReadNoopForest activeProtectors forest)
    (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem)
    (readRangeOff readRangeLen targetFrameDepth : Nat) :
    BorrowForest.toList
        (pruneForeignRead allBorrows forest targetLocal readerTag readProj
          readRangeOff readRangeLen activeProtectors targetFrameDepth) =
      freezeTreeBorrowsOnReadAtProj allBorrows (BorrowForest.toList forest)
        targetLocal readerTag readProj readRangeOff readRangeLen
        activeProtectors targetFrameDepth := by
  rw [freezeTreeBorrowsOnReadAtProj_eq_map]
  exact pruneMapForest_toList forest
    (AllSubtreesForest.mono_strong (fun _ _ h => readSkip_sound h) forest
      (AllSubtreesForest.and forest hAlloc hNoop))

/--
Skip soundness of the read undefined-behavior scan at one node.
-/
theorem readUBSkip_sound {allBorrows : List BorrowEntry}
    {activeProtectors : List Nat} {targetLocal : Local}
    {readerTag : Option Nat} {readProj : List ProjectionElem}
    {readRangeOff readRangeLen targetFrameDepth : Nat} {root : BorrowEntry}
    {children : List BorrowSubtree}
    (h : AllSubtrees
      (fun r c =>
        SameAllocNode allBorrows r c ∧ ForeignReadNoopNode activeProtectors r c)
      (.node root children)) :
    AnySkipSoundNode
      (readUBSkipRoot allBorrows activeProtectors targetLocal readerTag
        targetFrameDepth)
      (fun e =>
        borrowEntryReadUB allBorrows activeProtectors e targetLocal readerTag
          readProj readRangeOff readRangeLen targetFrameDepth)
      root children := by
  intro hs
  obtain ⟨hA, hN⟩ := (AllSubtrees.node_iff.mp h).1
  have hSub : SameAllocSubtree allBorrows (.node root children) :=
    AllSubtrees.and_left h
  unfold readUBSkipRoot at hs
  cases hu : isForeignUnrelatedRoot root targetLocal targetFrameDepth with
  | true =>
    refine ⟨borrowEntryReadUB_unrelated _ _ _ _ _ _ _ _ _
      (unrelated_of_unrelated_root hu rfl rfl), fun e he => ?_⟩
    exact borrowEntryReadUB_unrelated _ _ _ _ _ _ _ _ _
      (unrelated_of_unrelated_root hu (hA.1 e he).1 (hA.1 e he).2)
  | false =>
    rw [hu] at hs
    obtain ⟨hf, hn⟩ := and_eq_true_split hs
    have hall := SameAllocSubtree.foreign_to_all hSub hf
    refine ⟨borrowEntryReadUB_foreign_noop _ _ _ _ _ _ _ _ _
      (fun tag htag => (hall root (by
        rw [BorrowSubtree.toList_node]
        exact List.mem_cons_self ..) tag htag).1) hn, fun e he => ?_⟩
    exact borrowEntryReadUB_foreign_noop _ _ _ _ _ _ _ _ _
      (fun tag htag => (hall e (by
        rw [BorrowSubtree.toList_node]
        exact List.mem_cons_of_mem _ he) tag htag).1) (hN hn e he)

/--
**Exact equivalence of the pruned read undefined-behavior scan** with the
trusted full scan `hasTreeReadUB`.
-/
theorem pruneHasTreeReadUB_equiv_fullScan {allBorrows : List BorrowEntry}
    {forest : BorrowForest} {activeProtectors : List Nat}
    (hAlloc : SameAllocForest allBorrows forest)
    (hNoop : ForeignReadNoopForest activeProtectors forest)
    (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem)
    (readRangeOff readRangeLen targetFrameDepth : Nat) :
    pruneHasTreeReadUB allBorrows forest activeProtectors targetLocal readerTag
        readProj readRangeOff readRangeLen targetFrameDepth =
      hasTreeReadUB allBorrows (BorrowForest.toList forest) activeProtectors
        targetLocal readerTag readProj readRangeOff readRangeLen
        targetFrameDepth := by
  rw [hasTreeReadUB_eq_any]
  exact pruneAnyForest_eq_any forest
    (AllSubtreesForest.mono_strong (fun _ _ h => readUBSkip_sound h) forest
      (AllSubtreesForest.and forest hAlloc hNoop))

/--
Common core of write skip soundness: on a skipped subtree, either every entry
is unrelated to the written allocation, or the write is foreign to every
entry (for both relatedness notions) and every entry is a foreign-write no-op
at its own protection status.
-/
theorem writeSkip_cases {allBorrows : List BorrowEntry}
    {activeProtectors : List Nat} {targetLocal : Local}
    {writerTag : Option Nat} {targetFrameDepth : Nat} {root : BorrowEntry}
    {children : List BorrowSubtree}
    (h : AllSubtrees
      (fun r c =>
        SameAllocNode allBorrows r c ∧
          ForeignWriteNoopNode activeProtectors r c)
      (.node root children))
    (hs : writeSkipRoot allBorrows activeProtectors targetLocal writerTag
      targetFrameDepth root = true) :
    ∀ e, e ∈ (BorrowSubtree.node root children).toList →
      Bool.and (Nat.beq e.targetFrameDepth targetFrameDepth)
          (Nat.beq e.targetLocal targetLocal) = false ∨
        ((∀ tag, writerTag = some tag →
            isBorrowDescendantOrSelf allBorrows tag e.tag = false ∧
              Nat.beq e.tag tag = false) ∧
          isForeignWriteNoopPerm (isBorrowProtected activeProtectors e) e.perm =
            true) := by
  intro e he
  obtain ⟨hA, hN⟩ := (AllSubtrees.node_iff.mp h).1
  have hSub : SameAllocSubtree allBorrows (.node root children) :=
    AllSubtrees.and_left h
  have he' : e = root ∨ e ∈ BorrowForest.toList children := by
    rw [BorrowSubtree.toList_node] at he
    cases he with
    | head => exact Or.inl rfl
    | tail _ ht => exact Or.inr ht
  unfold writeSkipRoot at hs
  cases hu : isForeignUnrelatedRoot root targetLocal targetFrameDepth with
  | true =>
    cases he' with
    | inl heq =>
      rw [heq]
      exact Or.inl (unrelated_of_unrelated_root hu rfl rfl)
    | inr hch =>
      exact Or.inl
        (unrelated_of_unrelated_root hu (hA.1 e hch).1 (hA.1 e hch).2)
  | false =>
    rw [hu] at hs
    obtain ⟨hf, hn⟩ := and_eq_true_split hs
    have hall := SameAllocSubtree.foreign_to_all hSub hf
    refine Or.inr ⟨fun tag htag => hall e he tag htag, ?_⟩
    cases he' with
    | inl heq =>
      rw [heq]
      exact hn
    | inr hch => exact hN hn e hch

/-- Skip soundness of the tree write at one node. -/
theorem writeSkip_sound_tree {allBorrows : List BorrowEntry}
    {activeProtectors : List Nat} {targetLocal : Local}
    {writerTag : Option Nat} {writeProj : List ProjectionElem}
    {writeRangeOff writeRangeLen targetFrameDepth : Nat} {root : BorrowEntry}
    {children : List BorrowSubtree}
    (h : AllSubtrees
      (fun r c =>
        SameAllocNode allBorrows r c ∧
          ForeignWriteNoopNode activeProtectors r c)
      (.node root children)) :
    MapSkipSoundNode
      (writeSkipRoot allBorrows activeProtectors targetLocal writerTag
        targetFrameDepth)
      (fun e =>
        updateBorrowPermTreeAtProj allBorrows e targetLocal writerTag writeProj
          writeRangeOff writeRangeLen targetFrameDepth)
      root children := by
  intro hs
  have key : ∀ e, e ∈ (BorrowSubtree.node root children).toList →
      updateBorrowPermTreeAtProj allBorrows e targetLocal writerTag writeProj
        writeRangeOff writeRangeLen targetFrameDepth = e := by
    intro e he
    cases writeSkip_cases h hs e he with
    | inl hu => exact updateBorrowPermTreeAtProj_unrelated _ _ _ _ _ _ _ _ hu
    | inr hfn =>
      exact updateBorrowPermTreeAtProj_foreign_noop _ _ _ _ _ _ _ _
        (fun tag htag => (hfn.1 tag htag).1)
        (isForeignWriteNoopPerm_unprotected hfn.2)
  exact ⟨key root (by
      rw [BorrowSubtree.toList_node]
      exact List.mem_cons_self ..),
    fun e he => key e (by
      rw [BorrowSubtree.toList_node]
      exact List.mem_cons_of_mem _ he)⟩

/-- Skip soundness of the simple write at one node. -/
theorem writeSkip_sound_simple {allBorrows : List BorrowEntry}
    {activeProtectors : List Nat} {targetLocal : Local}
    {writerTag : Option Nat} {targetFrameDepth : Nat} {root : BorrowEntry}
    {children : List BorrowSubtree}
    (h : AllSubtrees
      (fun r c =>
        SameAllocNode allBorrows r c ∧
          ForeignWriteNoopNode activeProtectors r c)
      (.node root children)) :
    MapSkipSoundNode
      (writeSkipRoot allBorrows activeProtectors targetLocal writerTag
        targetFrameDepth)
      (fun e => updateBorrowPerm e targetLocal writerTag targetFrameDepth)
      root children := by
  intro hs
  have key : ∀ e, e ∈ (BorrowSubtree.node root children).toList →
      updateBorrowPerm e targetLocal writerTag targetFrameDepth = e := by
    intro e he
    cases writeSkip_cases h hs e he with
    | inl hu => exact updateBorrowPerm_unrelated _ _ _ _ hu
    | inr hfn =>
      exact updateBorrowPerm_foreign_noop _ _ _ _
        (fun tag htag => (hfn.1 tag htag).2)
        (isForeignWriteNoopPerm_unprotected hfn.2)
  exact ⟨key root (by
      rw [BorrowSubtree.toList_node]
      exact List.mem_cons_self ..),
    fun e he => key e (by
      rw [BorrowSubtree.toList_node]
      exact List.mem_cons_of_mem _ he)⟩

/-- Skip soundness of the projection-sensitive write at one node. -/
theorem writeSkip_sound_proj {allBorrows : List BorrowEntry}
    {activeProtectors : List Nat} {targetLocal : Local}
    {writerTag : Option Nat} {writeProj : List ProjectionElem}
    {writeRangeOff writeRangeLen targetFrameDepth : Nat} {root : BorrowEntry}
    {children : List BorrowSubtree}
    (h : AllSubtrees
      (fun r c =>
        SameAllocNode allBorrows r c ∧
          ForeignWriteNoopNode activeProtectors r c)
      (.node root children)) :
    MapSkipSoundNode
      (writeSkipRoot allBorrows activeProtectors targetLocal writerTag
        targetFrameDepth)
      (fun e =>
        updateBorrowPermAtProj e targetLocal writerTag writeProj writeRangeOff
          writeRangeLen targetFrameDepth)
      root children := by
  intro hs
  have key : ∀ e, e ∈ (BorrowSubtree.node root children).toList →
      updateBorrowPermAtProj e targetLocal writerTag writeProj writeRangeOff
        writeRangeLen targetFrameDepth = e := by
    intro e he
    cases writeSkip_cases h hs e he with
    | inl hu => exact updateBorrowPermAtProj_unrelated _ _ _ _ _ _ _ hu
    | inr hfn =>
      exact updateBorrowPermAtProj_foreign_noop _ _ _ _ _ _ _
        (fun tag htag => (hfn.1 tag htag).2)
        (isForeignWriteNoopPerm_unprotected hfn.2)
  exact ⟨key root (by
      rw [BorrowSubtree.toList_node]
      exact List.mem_cons_self ..),
    fun e he => key e (by
      rw [BorrowSubtree.toList_node]
      exact List.mem_cons_of_mem _ he)⟩

/-- Skip soundness of the protected-write conflict scan at one node. -/
theorem writeSkip_sound_conflict {allBorrows : List BorrowEntry}
    {activeProtectors : List Nat} {targetLocal : Local}
    {writerTag : Option Nat} {writeProj : List ProjectionElem}
    {writeRangeOff writeRangeLen targetFrameDepth : Nat} {root : BorrowEntry}
    {children : List BorrowSubtree}
    (h : AllSubtrees
      (fun r c =>
        SameAllocNode allBorrows r c ∧
          ForeignWriteNoopNode activeProtectors r c)
      (.node root children)) :
    AnySkipSoundNode
      (writeSkipRoot allBorrows activeProtectors targetLocal writerTag
        targetFrameDepth)
      (protectedWriteConflictAt activeProtectors targetLocal writerTag writeProj
        writeRangeOff writeRangeLen targetFrameDepth)
      root children := by
  intro hs
  have key : ∀ e, e ∈ (BorrowSubtree.node root children).toList →
      protectedWriteConflictAt activeProtectors targetLocal writerTag writeProj
        writeRangeOff writeRangeLen targetFrameDepth e = false := by
    intro e he
    cases writeSkip_cases h hs e he with
    | inl hu => exact protectedWriteConflictAt_unrelated _ _ _ _ _ _ _ _ hu
    | inr hfn =>
      exact protectedWriteConflictAt_foreign_noop _ _ _ _ _ _ _ _
        (fun tag htag => (hfn.1 tag htag).2) hfn.2
  exact ⟨key root (by
      rw [BorrowSubtree.toList_node]
      exact List.mem_cons_self ..),
    fun e he => key e (by
      rw [BorrowSubtree.toList_node]
      exact List.mem_cons_of_mem _ he)⟩

/--
**Exact equivalence of the pruned tree write** with the trusted full scan
`invalidateTreeBorrowsAtProj`.
-/
theorem pruneForeignWrite_equiv_fullScan {allBorrows : List BorrowEntry}
    {forest : BorrowForest} {activeProtectors : List Nat}
    (hAlloc : SameAllocForest allBorrows forest)
    (hNoop : ForeignWriteNoopForest activeProtectors forest)
    (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat) :
    BorrowForest.toList
        (pruneForeignWrite allBorrows forest targetLocal writerTag writeProj
          writeRangeOff writeRangeLen targetFrameDepth activeProtectors) =
      invalidateTreeBorrowsAtProj allBorrows (BorrowForest.toList forest)
        targetLocal writerTag writeProj writeRangeOff writeRangeLen
        targetFrameDepth := by
  rw [invalidateTreeBorrowsAtProj_eq_map]
  exact pruneMapForest_toList forest
    (AllSubtreesForest.mono_strong (fun _ _ h => writeSkip_sound_tree h) forest
      (AllSubtreesForest.and forest hAlloc hNoop))

/--
**Exact equivalence of the pruned simple write** with the trusted full scan
`invalidateConflictingBorrows`.
-/
theorem pruneForeignWriteSimple_equiv_fullScan {allBorrows : List BorrowEntry}
    {forest : BorrowForest} {activeProtectors : List Nat}
    (hAlloc : SameAllocForest allBorrows forest)
    (hNoop : ForeignWriteNoopForest activeProtectors forest)
    (targetLocal : Local) (writerTag : Option Nat) (targetFrameDepth : Nat) :
    BorrowForest.toList
        (pruneForeignWriteSimple allBorrows forest targetLocal writerTag
          targetFrameDepth activeProtectors) =
      invalidateConflictingBorrows (BorrowForest.toList forest) targetLocal
        writerTag targetFrameDepth := by
  rw [invalidateConflictingBorrows_eq_map]
  exact pruneMapForest_toList forest
    (AllSubtreesForest.mono_strong (fun _ _ h => writeSkip_sound_simple h)
      forest (AllSubtreesForest.and forest hAlloc hNoop))

/--
**Exact equivalence of the pruned projection-sensitive write** with the
trusted full scan `invalidateConflictingBorrowsAtProj`.
-/
theorem pruneForeignWriteProj_equiv_fullScan {allBorrows : List BorrowEntry}
    {forest : BorrowForest} {activeProtectors : List Nat}
    (hAlloc : SameAllocForest allBorrows forest)
    (hNoop : ForeignWriteNoopForest activeProtectors forest)
    (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat) :
    BorrowForest.toList
        (pruneForeignWriteProj allBorrows forest targetLocal writerTag writeProj
          writeRangeOff writeRangeLen targetFrameDepth activeProtectors) =
      invalidateConflictingBorrowsAtProj (BorrowForest.toList forest)
        targetLocal writerTag writeProj writeRangeOff writeRangeLen
        targetFrameDepth := by
  rw [invalidateConflictingBorrowsAtProj_eq_map]
  exact pruneMapForest_toList forest
    (AllSubtreesForest.mono_strong (fun _ _ h => writeSkip_sound_proj h) forest
      (AllSubtreesForest.and forest hAlloc hNoop))

/--
**Exact equivalence of the pruned protected-write conflict scan** with the
trusted full scan `hasProtectedWriteConflict`.
-/
theorem pruneHasProtectedWriteConflict_equiv_fullScan
    {allBorrows : List BorrowEntry} {forest : BorrowForest}
    {activeProtectors : List Nat}
    (hAlloc : SameAllocForest allBorrows forest)
    (hNoop : ForeignWriteNoopForest activeProtectors forest)
    (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat) :
    pruneHasProtectedWriteConflict allBorrows forest activeProtectors
        targetLocal writerTag writeProj writeRangeOff writeRangeLen
        targetFrameDepth =
      hasProtectedWriteConflict (BorrowForest.toList forest) activeProtectors
        targetLocal writerTag writeProj writeRangeOff writeRangeLen
        targetFrameDepth := by
  rw [hasProtectedWriteConflict_eq_any]
  exact pruneAnyForest_eq_any forest
    (AllSubtreesForest.mono_strong (fun _ _ h => writeSkip_sound_conflict h)
      forest (AllSubtreesForest.and forest hAlloc hNoop))

/--
The pruned read freeze preserves the protector of every entry, on every
forest (no invariant is needed).
-/
theorem pruneForeignRead_preserves_protectors (allBorrows : List BorrowEntry)
    (forest : BorrowForest) (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem)
    (readRangeOff readRangeLen : Nat) (activeProtectors : List Nat)
    (targetFrameDepth : Nat) :
    (BorrowForest.toList
        (pruneForeignRead allBorrows forest targetLocal readerTag readProj
          readRangeOff readRangeLen activeProtectors targetFrameDepth)).map
        BorrowEntry.protector =
      (BorrowForest.toList forest).map BorrowEntry.protector :=
  pruneMapForest_map_proj BorrowEntry.protector
    (fun e => updateBorrowPermOnReadAtProj_protector _ e _ _ _ _ _ _ _) forest

/--
The pruned read freeze preserves the tag of every entry, on every forest.
-/
theorem pruneForeignRead_preserves_tags (allBorrows : List BorrowEntry)
    (forest : BorrowForest) (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem)
    (readRangeOff readRangeLen : Nat) (activeProtectors : List Nat)
    (targetFrameDepth : Nat) :
    (BorrowForest.toList
        (pruneForeignRead allBorrows forest targetLocal readerTag readProj
          readRangeOff readRangeLen activeProtectors targetFrameDepth)).map
        BorrowEntry.tag =
      (BorrowForest.toList forest).map BorrowEntry.tag :=
  pruneMapForest_map_proj BorrowEntry.tag
    (fun e => updateBorrowPermOnReadAtProj_tag _ e _ _ _ _ _ _ _) forest

/--
The pruned tree write preserves the protector of every entry, on every forest
(no invariant is needed).
-/
theorem pruneForeignWrite_preserves_protectors (allBorrows : List BorrowEntry)
    (forest : BorrowForest) (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat)
    (activeProtectors : List Nat) :
    (BorrowForest.toList
        (pruneForeignWrite allBorrows forest targetLocal writerTag writeProj
          writeRangeOff writeRangeLen targetFrameDepth activeProtectors)).map
        BorrowEntry.protector =
      (BorrowForest.toList forest).map BorrowEntry.protector :=
  pruneMapForest_map_proj BorrowEntry.protector
    (fun e => updateBorrowPermAtProj_protector e _ _ _ _ _ _) forest

/--
The pruned tree write preserves the tag of every entry, on every forest.
-/
theorem pruneForeignWrite_preserves_tags (allBorrows : List BorrowEntry)
    (forest : BorrowForest) (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat)
    (activeProtectors : List Nat) :
    (BorrowForest.toList
        (pruneForeignWrite allBorrows forest targetLocal writerTag writeProj
          writeRangeOff writeRangeLen targetFrameDepth activeProtectors)).map
        BorrowEntry.tag =
      (BorrowForest.toList forest).map BorrowEntry.tag :=
  pruneMapForest_map_proj BorrowEntry.tag
    (fun e => updateBorrowPermAtProj_tag e _ _ _ _ _ _) forest

/--
The pruned simple and projection-sensitive writes preserve the protector of
every entry, on every forest.
-/
theorem pruneForeignWriteSimple_preserves_protectors
    (allBorrows : List BorrowEntry) (forest : BorrowForest)
    (targetLocal : Local) (writerTag : Option Nat) (targetFrameDepth : Nat)
    (activeProtectors : List Nat) :
    (BorrowForest.toList
        (pruneForeignWriteSimple allBorrows forest targetLocal writerTag
          targetFrameDepth activeProtectors)).map BorrowEntry.protector =
      (BorrowForest.toList forest).map BorrowEntry.protector :=
  pruneMapForest_map_proj BorrowEntry.protector
    (fun e => updateBorrowPerm_protector e _ _ _) forest

/--
**O(1) short-circuit at an unrelated root.** The pruned read freeze returns a
subtree with an unrelated root as is, for arbitrary children and with no
invariant: it never inspects the children.
-/
theorem pruneForeignRead_skip_unrelated (allBorrows : List BorrowEntry)
    (root : BorrowEntry) (children : List BorrowSubtree) (rest : BorrowForest)
    (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem)
    (readRangeOff readRangeLen : Nat) (activeProtectors : List Nat)
    (targetFrameDepth : Nat)
    (h : isForeignUnrelatedRoot root targetLocal targetFrameDepth = true) :
    pruneForeignRead allBorrows (.node root children :: rest) targetLocal
        readerTag readProj readRangeOff readRangeLen activeProtectors
        targetFrameDepth =
      .node root children ::
        pruneForeignRead allBorrows rest targetLocal readerTag readProj
          readRangeOff readRangeLen activeProtectors targetFrameDepth := by
  unfold pruneForeignRead
  rw [pruneMapForest_cons, pruneMapSubtree_skip children (by
    unfold readSkipRoot
    rw [h]
    rfl)]

/--
**O(1) short-circuit at a foreign no-op root.** The pruned read freeze
returns a subtree whose root is a foreign-read no-op as is, for arbitrary
children: it never inspects the children.
-/
theorem pruneForeignRead_skip_noop (allBorrows : List BorrowEntry)
    (root : BorrowEntry) (children : List BorrowSubtree) (rest : BorrowForest)
    (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem)
    (readRangeOff readRangeLen : Nat) (activeProtectors : List Nat)
    (targetFrameDepth : Nat)
    (h : isForeignReadNoopPerm (isBorrowProtected activeProtectors root)
      root.perm = true) :
    pruneForeignRead allBorrows (.node root children :: rest) targetLocal
        readerTag readProj readRangeOff readRangeLen activeProtectors
        targetFrameDepth =
      .node root children ::
        pruneForeignRead allBorrows rest targetLocal readerTag readProj
          readRangeOff readRangeLen activeProtectors targetFrameDepth := by
  unfold pruneForeignRead
  rw [pruneMapForest_cons, pruneMapSubtree_skip children (by
    unfold readSkipRoot
    rw [h]
    cases isForeignUnrelatedRoot root targetLocal targetFrameDepth <;> rfl)]

/--
**O(1) short-circuit of the write traversals.** A subtree whose root is
skipped (`writeSkipRoot`) is returned as is by the pruned tree write, for
arbitrary children.
-/
theorem pruneForeignWrite_skip (allBorrows : List BorrowEntry)
    (root : BorrowEntry) (children : List BorrowSubtree) (rest : BorrowForest)
    (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat)
    (activeProtectors : List Nat)
    (h : writeSkipRoot allBorrows activeProtectors targetLocal writerTag
      targetFrameDepth root = true) :
    pruneForeignWrite allBorrows (.node root children :: rest) targetLocal
        writerTag writeProj writeRangeOff writeRangeLen targetFrameDepth
        activeProtectors =
      .node root children ::
        pruneForeignWrite allBorrows rest targetLocal writerTag writeProj
          writeRangeOff writeRangeLen targetFrameDepth activeProtectors := by
  unfold pruneForeignWrite
  rw [pruneMapForest_cons, pruneMapSubtree_skip children h]


/-! ### 1.6 `MirLiftCore` integration: erasing unrelated foreign subtrees -/

/-- `invalidateConflictingBorrows` distributes over append. -/
theorem invalidateConflictingBorrows_append (xs ys : List BorrowEntry)
    (targetLocal : Local) (writerTag : Option Nat) (targetFrameDepth : Nat) :
    invalidateConflictingBorrows (xs ++ ys) targetLocal writerTag
        targetFrameDepth =
      invalidateConflictingBorrows xs targetLocal writerTag targetFrameDepth ++
        invalidateConflictingBorrows ys targetLocal writerTag
          targetFrameDepth := by
  rw [invalidateConflictingBorrows_eq_map, invalidateConflictingBorrows_eq_map,
    invalidateConflictingBorrows_eq_map, map_append']

/-- `invalidateConflictingBorrowsAtProj` distributes over append. -/
theorem invalidateConflictingBorrowsAtProj_append (xs ys : List BorrowEntry)
    (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat) :
    invalidateConflictingBorrowsAtProj (xs ++ ys) targetLocal writerTag
        writeProj writeRangeOff writeRangeLen targetFrameDepth =
      invalidateConflictingBorrowsAtProj xs targetLocal writerTag writeProj
          writeRangeOff writeRangeLen targetFrameDepth ++
        invalidateConflictingBorrowsAtProj ys targetLocal writerTag writeProj
          writeRangeOff writeRangeLen targetFrameDepth := by
  rw [invalidateConflictingBorrowsAtProj_eq_map,
    invalidateConflictingBorrowsAtProj_eq_map,
    invalidateConflictingBorrowsAtProj_eq_map, map_append']

/--
A simple write to `(targetFrameDepth, targetLocal)` leaves a borrow table
with no entry of that allocation unchanged.
-/
theorem invalidateConflictingBorrows_unrelated_eq (borrows : List BorrowEntry)
    (targetLocal : Local) (writerTag : Option Nat) (targetFrameDepth : Nat)
    (h : ∀ e, e ∈ borrows →
      Bool.and (Nat.beq e.targetFrameDepth targetFrameDepth)
        (Nat.beq e.targetLocal targetLocal) = false) :
    invalidateConflictingBorrows borrows targetLocal writerTag
        targetFrameDepth = borrows := by
  rw [invalidateConflictingBorrows_eq_map]
  exact map_eq_self_of_forall _ _
    (fun e he => updateBorrowPerm_unrelated e _ _ _ (h e he))

/--
A projection-sensitive write to `(targetFrameDepth, targetLocal)` leaves a
borrow table with no entry of that allocation unchanged.
-/
theorem invalidateConflictingBorrowsAtProj_unrelated_eq
    (borrows : List BorrowEntry) (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat)
    (h : ∀ e, e ∈ borrows →
      Bool.and (Nat.beq e.targetFrameDepth targetFrameDepth)
        (Nat.beq e.targetLocal targetLocal) = false) :
    invalidateConflictingBorrowsAtProj borrows targetLocal writerTag writeProj
        writeRangeOff writeRangeLen targetFrameDepth = borrows := by
  rw [invalidateConflictingBorrowsAtProj_eq_map]
  exact map_eq_self_of_forall _ _
    (fun e he => updateBorrowPermAtProj_unrelated e _ _ _ _ _ _ (h e he))

/--
In a structurally well-formed forest all of whose roots are unrelated to
`(targetFrameDepth, targetLocal)`, no entry targets that allocation. Only the
roots are inspected.
-/
theorem SameAllocForest.unrelated_of_roots {allBorrows : List BorrowEntry}
    {targetLocal : Local} {targetFrameDepth : Nat} :
    ∀ (forest : List BorrowSubtree), SameAllocForest allBorrows forest →
      (∀ t, t ∈ forest →
        isForeignUnrelatedRoot t.root targetLocal targetFrameDepth = true) →
      ∀ e, e ∈ BorrowForest.toList forest →
        Bool.and (Nat.beq e.targetFrameDepth targetFrameDepth)
          (Nat.beq e.targetLocal targetLocal) = false
  | [], _, _, e, he => by
    rw [BorrowForest.toList_nil] at he
    cases he
  | .node root children :: ts, h, hroots, e, he => by
    have h' := AllSubtreesForest.cons_iff.mp h
    have hA := (AllSubtrees.node_iff.mp h'.1).1
    have hu : isForeignUnrelatedRoot root targetLocal targetFrameDepth = true :=
      hroots (.node root children) (List.mem_cons_self ..)
    rw [BorrowForest.toList_cons, BorrowSubtree.toList_node] at he
    cases mem_append_split he with
    | inl hl =>
      cases hl with
      | head => exact unrelated_of_unrelated_root hu rfl rfl
      | tail _ ht =>
        exact unrelated_of_unrelated_root hu (hA.1 e ht).1 (hA.1 e ht).2
    | inr hr =>
      exact SameAllocForest.unrelated_of_roots ts h'.2
        (fun t ht => hroots t (List.mem_cons_of_mem _ ht)) e hr

/--
**Erasure of unrelated foreign subtrees (simple write).** If the borrow table
splits into `touched` entries followed by a structurally well-formed forest
whose roots are all unrelated to the written allocation, a simple write only
processes `touched`: the foreign forest is carried over unchanged after
inspecting only its roots.
-/
theorem invalidateConflictingBorrows_erase_foreign
    {allBorrows : List BorrowEntry} (touched : List BorrowEntry)
    {foreign : BorrowForest} (hAlloc : SameAllocForest allBorrows foreign)
    (targetLocal : Local) (writerTag : Option Nat) (targetFrameDepth : Nat)
    (hroots : ∀ t, t ∈ foreign →
      isForeignUnrelatedRoot t.root targetLocal targetFrameDepth = true) :
    invalidateConflictingBorrows (touched ++ BorrowForest.toList foreign)
        targetLocal writerTag targetFrameDepth =
      invalidateConflictingBorrows touched targetLocal writerTag
          targetFrameDepth ++
        BorrowForest.toList foreign := by
  rw [invalidateConflictingBorrows_append,
    invalidateConflictingBorrows_unrelated_eq (BorrowForest.toList foreign) _ _
      _ (SameAllocForest.unrelated_of_roots foreign hAlloc hroots)]

/--
**Erasure of unrelated foreign subtrees (projection-sensitive write).**
-/
theorem invalidateConflictingBorrowsAtProj_erase_foreign
    {allBorrows : List BorrowEntry} (touched : List BorrowEntry)
    {foreign : BorrowForest} (hAlloc : SameAllocForest allBorrows foreign)
    (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat)
    (hroots : ∀ t, t ∈ foreign →
      isForeignUnrelatedRoot t.root targetLocal targetFrameDepth = true) :
    invalidateConflictingBorrowsAtProj (touched ++ BorrowForest.toList foreign)
        targetLocal writerTag writeProj writeRangeOff writeRangeLen
        targetFrameDepth =
      invalidateConflictingBorrowsAtProj touched targetLocal writerTag writeProj
          writeRangeOff writeRangeLen targetFrameDepth ++
        BorrowForest.toList foreign := by
  rw [invalidateConflictingBorrowsAtProj_append,
    invalidateConflictingBorrowsAtProj_unrelated_eq
      (BorrowForest.toList foreign) _ _ _ _ _ _
      (SameAllocForest.unrelated_of_roots foreign hAlloc hroots)]

/--
Borrow forest after `assignLocalPlace`, computed by the pruned write
traversals: the pruned simple write for an unprojected destination and the
pruned projection-sensitive write for a projected one.
-/
def pruneAssignLocalPlaceBorrows (allBorrows : List BorrowEntry)
    (forest : BorrowForest) (locals : PureEnv) (dst : Place)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) (targetFrameDepth : Nat := 0)
    (activeProtectors : List Nat := .nil) : BorrowForest :=
  match dst.projection with
  | [] =>
    pruneForeignWriteSimple allBorrows forest dst.local_ .none targetFrameDepth
      activeProtectors
  | proj :: rest =>
    pruneForeignWriteProj allBorrows forest dst.local_ .none
      (resolveBorrowWriteLocalProj localDecls layouts locals dst.local_
        (proj :: rest))
      0 0 targetFrameDepth activeProtectors

/--
The borrow table returned by a successful `assignLocalPlace`: the trusted
simple write for an unprojected destination and the trusted
projection-sensitive write for a projected one.
-/
theorem assignLocalPlace_borrows_eq {locals locals' : PureEnv}
    {borrows borrows' : List BorrowEntry} {dst : Place} {val : Value}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {targetFrameDepth : Nat}
    (h : assignLocalPlace locals borrows dst val localDecls layouts
      targetFrameDepth = some (locals', borrows')) :
    borrows' =
      (match dst.projection with
        | [] =>
          invalidateConflictingBorrows borrows dst.local_ .none targetFrameDepth
        | proj :: rest =>
          invalidateConflictingBorrowsAtProj borrows dst.local_ .none
            (resolveBorrowWriteLocalProj localDecls layouts locals dst.local_
              (proj :: rest))
            0 0 targetFrameDepth) := by
  unfold assignLocalPlace at h
  cases hp : dst.projection with
  | nil =>
    rw [hp] at h
    dsimp only [] at h
    repeat' (first | (cases h; done) | split at h)
    all_goals (cases h; rfl)
  | cons proj rest =>
    rw [hp] at h
    cases proj <;> dsimp only [] at h
    all_goals repeat' (first | (cases h; done) | split at h)
    all_goals (cases h; rfl)

/--
**`assignLocalPlace` with a pruned borrow table.** Whenever the
`MirLiftCore` assignment `assignLocalPlace` succeeds on the flattened forest,
the borrow table it returns is the flattening of the pruned write
(`pruneAssignLocalPlaceBorrows`), so lifting proofs may replace the full scan
of `assignLocalPlace` by the pruned traversal.
-/
theorem assignLocalPlace_pruned_borrows {allBorrows : List BorrowEntry}
    {forest : BorrowForest} {activeProtectors : List Nat}
    (hAlloc : SameAllocForest allBorrows forest)
    (hNoop : ForeignWriteNoopForest activeProtectors forest)
    {locals locals' : PureEnv} {borrows' : List BorrowEntry} {dst : Place}
    {val : Value} {localDecls : List LocalDecl} {layouts : LayoutTable}
    {targetFrameDepth : Nat}
    (h : assignLocalPlace locals (BorrowForest.toList forest) dst val
      localDecls layouts targetFrameDepth = some (locals', borrows')) :
    borrows' =
      BorrowForest.toList
        (pruneAssignLocalPlaceBorrows allBorrows forest locals dst localDecls
          layouts targetFrameDepth activeProtectors) := by
  rw [assignLocalPlace_borrows_eq h]
  unfold pruneAssignLocalPlaceBorrows
  cases dst.projection with
  | nil =>
    exact (pruneForeignWriteSimple_equiv_fullScan hAlloc hNoop _ _ _).symm
  | cons proj rest =>
    exact (pruneForeignWriteProj_equiv_fullScan hAlloc hNoop _ _ _ _ _ _).symm

/--
**`assignLocalPlace` erases unrelated foreign subtrees.** If the borrow table
is a structurally well-formed forest whose roots are all unrelated to the
assigned local, a successful `assignLocalPlace` returns the borrow table
unchanged, after inspecting only the roots.
-/
theorem assignLocalPlace_unrelated_forest_borrows
    {allBorrows : List BorrowEntry} {forest : BorrowForest}
    (hAlloc : SameAllocForest allBorrows forest)
    {locals locals' : PureEnv} {borrows' : List BorrowEntry} {dst : Place}
    {val : Value} {localDecls : List LocalDecl} {layouts : LayoutTable}
    {targetFrameDepth : Nat}
    (hroots : ∀ t, t ∈ forest →
      isForeignUnrelatedRoot t.root dst.local_ targetFrameDepth = true)
    (h : assignLocalPlace locals (BorrowForest.toList forest) dst val
      localDecls layouts targetFrameDepth = some (locals', borrows')) :
    borrows' = BorrowForest.toList forest := by
  have hun := SameAllocForest.unrelated_of_roots forest hAlloc hroots
  rw [assignLocalPlace_borrows_eq h]
  cases dst.projection with
  | nil => exact invalidateConflictingBorrows_unrelated_eq _ _ _ _ hun
  | cons proj rest =>
    exact invalidateConflictingBorrowsAtProj_unrelated_eq _ _ _ _ _ _ _ hun

/--
`LiftFrame` only depends on the value of the borrow table: a frame at memory
`mem` follows from the frame at `mem` with its borrow table replaced by an
equal one.
-/
theorem LiftFrame_congr_borrows {body : CapturedMir} {bbIdx : BasicBlockIdx}
    {stmtIdx : Nat} {env : PureEnv} {mem : Memory} {post : Value → Prop}
    {fuel : Nat} {borrows : List BorrowEntry} (hb : mem.borrows = borrows)
    (h : LiftFrame body bbIdx stmtIdx env { mem with borrows := borrows } post
      fuel) :
    LiftFrame body bbIdx stmtIdx env mem post fuel := by
  subst hb
  exact h

/--
**`LiftFrame` congruence for a pruned simple write.** A frame at a memory
whose borrow table is the trusted full scan `invalidateConflictingBorrows` of
a forest follows from the frame at the memory holding the pruned traversal's
result.
-/
theorem LiftFrame_congr_pruned_borrows {allBorrows : List BorrowEntry}
    {forest : BorrowForest} {activeProtectors : List Nat}
    (hAlloc : SameAllocForest allBorrows forest)
    (hNoop : ForeignWriteNoopForest activeProtectors forest)
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv}
    {mem : Memory} {post : Value → Prop} {fuel : Nat} (targetLocal : Local)
    (writerTag : Option Nat) (targetFrameDepth : Nat)
    (hmem : mem.borrows =
      invalidateConflictingBorrows (BorrowForest.toList forest) targetLocal
        writerTag targetFrameDepth)
    (h : LiftFrame body bbIdx stmtIdx env
      { mem with
        borrows :=
          BorrowForest.toList
            (pruneForeignWriteSimple allBorrows forest targetLocal writerTag
              targetFrameDepth activeProtectors) }
      post fuel) :
    LiftFrame body bbIdx stmtIdx env mem post fuel :=
  LiftFrame_congr_borrows
    (hmem.trans
      (pruneForeignWriteSimple_equiv_fullScan hAlloc hNoop _ _ _).symm)
    h

/-- `LiftFrame` congruence for a pruned projection-sensitive write. -/
theorem LiftFrame_congr_pruned_borrows_proj {allBorrows : List BorrowEntry}
    {forest : BorrowForest} {activeProtectors : List Nat}
    (hAlloc : SameAllocForest allBorrows forest)
    (hNoop : ForeignWriteNoopForest activeProtectors forest)
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv}
    {mem : Memory} {post : Value → Prop} {fuel : Nat} (targetLocal : Local)
    (writerTag : Option Nat) (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat)
    (hmem : mem.borrows =
      invalidateConflictingBorrowsAtProj (BorrowForest.toList forest)
        targetLocal writerTag writeProj writeRangeOff writeRangeLen
        targetFrameDepth)
    (h : LiftFrame body bbIdx stmtIdx env
      { mem with
        borrows :=
          BorrowForest.toList
            (pruneForeignWriteProj allBorrows forest targetLocal writerTag
              writeProj writeRangeOff writeRangeLen targetFrameDepth
              activeProtectors) }
      post fuel) :
    LiftFrame body bbIdx stmtIdx env mem post fuel :=
  LiftFrame_congr_borrows
    (hmem.trans
      (pruneForeignWriteProj_equiv_fullScan hAlloc hNoop _ _ _ _ _ _).symm)
    h

/-- `LiftFrame` congruence for a pruned tree write. -/
theorem LiftFrame_congr_pruned_borrows_tree {allBorrows : List BorrowEntry}
    {forest : BorrowForest} {activeProtectors : List Nat}
    (hAlloc : SameAllocForest allBorrows forest)
    (hNoop : ForeignWriteNoopForest activeProtectors forest)
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv}
    {mem : Memory} {post : Value → Prop} {fuel : Nat} (targetLocal : Local)
    (writerTag : Option Nat) (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen targetFrameDepth : Nat)
    (hmem : mem.borrows =
      invalidateTreeBorrowsAtProj allBorrows (BorrowForest.toList forest)
        targetLocal writerTag writeProj writeRangeOff writeRangeLen
        targetFrameDepth)
    (h : LiftFrame body bbIdx stmtIdx env
      { mem with
        borrows :=
          BorrowForest.toList
            (pruneForeignWrite allBorrows forest targetLocal writerTag writeProj
              writeRangeOff writeRangeLen targetFrameDepth activeProtectors) }
      post fuel) :
    LiftFrame body bbIdx stmtIdx env mem post fuel :=
  LiftFrame_congr_borrows
    (hmem.trans
      (pruneForeignWrite_equiv_fullScan hAlloc hNoop _ _ _ _ _ _).symm)
    h

/-- `LiftFrame` congruence for a pruned read freeze. -/
theorem LiftFrame_congr_pruned_borrows_read {allBorrows : List BorrowEntry}
    {forest : BorrowForest} {activeProtectors : List Nat}
    (hAlloc : SameAllocForest allBorrows forest)
    (hNoop : ForeignReadNoopForest activeProtectors forest)
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv}
    {mem : Memory} {post : Value → Prop} {fuel : Nat} (targetLocal : Local)
    (readerTag : Option Nat) (readProj : List ProjectionElem)
    (readRangeOff readRangeLen targetFrameDepth : Nat)
    (hmem : mem.borrows =
      freezeTreeBorrowsOnReadAtProj allBorrows (BorrowForest.toList forest)
        targetLocal readerTag readProj readRangeOff readRangeLen
        activeProtectors targetFrameDepth)
    (h : LiftFrame body bbIdx stmtIdx env
      { mem with
        borrows :=
          BorrowForest.toList
            (pruneForeignRead allBorrows forest targetLocal readerTag readProj
              readRangeOff readRangeLen activeProtectors targetFrameDepth) }
      post fuel) :
    LiftFrame body bbIdx stmtIdx env mem post fuel :=
  LiftFrame_congr_borrows
    (hmem.trans
      (pruneForeignRead_equiv_fullScan hAlloc hNoop _ _ _ _ _ _).symm)
    h

/-! ### 1.7 Tightness: the subtree invariant cannot be dropped -/

/-- A `.frozen` root borrow of local `_0` with tag `1`. -/
def cexFrozenRoot : BorrowEntry :=
  { tag := 1, targetLocal := 0, targetProjection := [], perm := .frozen }

/-- A child of `cexFrozenRoot` with tag `2` and permission `perm`. -/
def cexChild (perm : TreeBorrowPerm) : BorrowEntry :=
  { tag := 2, targetLocal := 0, targetProjection := [], perm := perm,
    parentTag := some 1 }

/-- Flat borrow table of the two-node witness. -/
def cexBorrows (perm : TreeBorrowPerm) : List BorrowEntry :=
  [cexFrozenRoot, cexChild perm]

/--
Two-node witness forest: the `.frozen` root `cexFrozenRoot` with one child of
permission `perm`. With `perm = .unique` it violates the `.frozen`-subtree
invariant; with `perm = .frozen` it satisfies every invariant.
-/
def cexForestOf (perm : TreeBorrowPerm) : BorrowForest :=
  [.node cexFrozenRoot [.node (cexChild perm) []]]

/-- The witness forest flattens to the witness borrow table. -/
theorem cexForestOf_toList (perm : TreeBorrowPerm) :
    BorrowForest.toList (cexForestOf perm) = cexBorrows perm := by
  unfold cexForestOf cexBorrows
  rw [BorrowForest.toList_cons, BorrowSubtree.toList_node,
    BorrowForest.toList_cons, BorrowSubtree.toList_node,
    BorrowForest.toList_nil]
  rfl

/-- `Nat.beq` of distinct numbers is `false`. -/
private theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) :
    Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) h

/-- A tag other than `1` and `2` is absent from the witness borrow table. -/
private theorem cexBorrows_lookup_none (perm : TreeBorrowPerm) (tag : Nat)
    (h1 : tag ≠ 1) (h2 : tag ≠ 2) :
    lookupBorrow (cexBorrows perm) tag = none := by
  show (match Nat.beq 1 tag with
    | true => some cexFrozenRoot
    | false =>
      match Nat.beq 2 tag with
      | true => some (cexChild perm)
      | false => none) = none
  rw [beq_false_of_ne (Ne.symm h1), beq_false_of_ne (Ne.symm h2)]

/-- A tag other than `1` and `2` is a descendant of no other tag in the
witness borrow table. -/
private theorem cexBorrows_desc_false (perm : TreeBorrowPerm) (tag anc : Nat)
    (ha : tag ≠ anc) (h1 : tag ≠ 1) (h2 : tag ≠ 2) :
    isBorrowDescendantOrSelf (cexBorrows perm) tag anc = false := by
  show (match Nat.beq tag anc with
    | true => true
    | false =>
      match lookupBorrow (cexBorrows perm) tag with
      | .some entry =>
        match entry.parentTag with
        | .some pTag =>
          isBorrowDescendantOrSelfAux 1 (cexBorrows perm) pTag anc
        | .none => false
      | .none => false) = false
  rw [beq_false_of_ne ha, cexBorrows_lookup_none perm tag h1 h2]

/-- Tags contained in the witness subtree rooted at the root. -/
private theorem cexRoot_containsTag (perm : TreeBorrowPerm) (tag : Nat) :
    (BorrowSubtree.node cexFrozenRoot [.node (cexChild perm) []]).containsTag
        tag = (Nat.beq 1 tag || Nat.beq 2 tag) := by
  rw [BorrowSubtree.containsTag_node, BorrowForest.containsTag_cons,
    BorrowSubtree.containsTag_node, BorrowForest.containsTag_nil]
  show (Nat.beq 1 tag || (Nat.beq 2 tag || false || false)) =
    (Nat.beq 1 tag || Nat.beq 2 tag)
  cases Nat.beq 1 tag <;> cases Nat.beq 2 tag <;> rfl

/-- Tags contained in the witness subtree rooted at the child. -/
private theorem cexChild_containsTag (perm : TreeBorrowPerm) (tag : Nat) :
    (BorrowSubtree.node (cexChild perm) []).containsTag tag =
      Nat.beq 2 tag := by
  rw [BorrowSubtree.containsTag_node, BorrowForest.containsTag_nil]
  show (Nat.beq 2 tag || false) = Nat.beq 2 tag
  cases Nat.beq 2 tag <;> rfl

/--
The witness forest is structurally well-formed for every child permission:
only the permission-level subtree invariant can fail on it.
-/
theorem cexForestOf_sameAlloc (perm : TreeBorrowPerm) :
    SameAllocForest (cexBorrows perm) (cexForestOf perm) := by
  unfold SameAllocForest cexForestOf
  refine AllSubtreesForest.cons_iff.mpr
    ⟨AllSubtrees.node_iff.mpr ⟨⟨?_, ?_, ?_⟩, AllSubtreesForest.cons_iff.mpr
      ⟨AllSubtrees.node_iff.mpr ⟨⟨?_, ?_, ?_⟩,
        AllSubtreesForest.nil_iff.mpr True.intro⟩,
        AllSubtreesForest.nil_iff.mpr True.intro⟩⟩,
      AllSubtreesForest.nil_iff.mpr True.intro⟩
  · intro e he
    rw [BorrowForest.toList_cons, BorrowSubtree.toList_node,
      BorrowForest.toList_nil] at he
    cases he with
    | head => exact ⟨rfl, rfl⟩
    | tail _ ht => cases ht
  · intro tag hc
    rw [cexRoot_containsTag] at hc
    obtain ⟨hb1, hb2⟩ := or_eq_false_split hc
    have h1 : tag ≠ 1 := fun h => by
      rw [h] at hb1
      exact Bool.noConfusion hb1
    have h2 : tag ≠ 2 := fun h => by
      rw [h] at hb2
      exact Bool.noConfusion hb2
    exact cexBorrows_desc_false perm tag 1 h1 h1 h2
  · intro tag hc
    rw [cexRoot_containsTag] at hc
    cases hb1 : Nat.beq 1 tag with
    | true =>
      have h1 : 1 = tag := Nat.eq_of_beq_eq_true hb1
      rw [← h1]
      rfl
    | false =>
      rw [hb1] at hc
      have hb2 : Nat.beq 2 tag = true := hc
      have h2 : 2 = tag := Nat.eq_of_beq_eq_true hb2
      rw [← h2]
      rfl
  · intro e he
    rw [BorrowForest.toList_nil] at he
    cases he
  · intro tag hc
    rw [cexChild_containsTag] at hc
    have h2 : tag ≠ 2 := fun h => by
      rw [h] at hc
      exact Bool.noConfusion hc
    cases Nat.decEq tag 1 with
    | isTrue h1 =>
      rw [h1]
      rfl
    | isFalse h1 => exact cexBorrows_desc_false perm tag 2 h2 h1 h2
  · intro tag hc
    rw [cexChild_containsTag] at hc
    have h2 : 2 = tag := Nat.eq_of_beq_eq_true hc
    rw [← h2]
    rfl

/-- With a `.frozen` child the witness forest satisfies the foreign-read
no-op subtree invariant. -/
theorem cexForestOf_frozen_readNoop :
    ForeignReadNoopForest [] (cexForestOf .frozen) := by
  unfold ForeignReadNoopForest cexForestOf
  refine AllSubtreesForest.cons_iff.mpr
    ⟨AllSubtrees.node_iff.mpr ⟨?_, AllSubtreesForest.cons_iff.mpr
      ⟨AllSubtrees.node_iff.mpr ⟨?_, AllSubtreesForest.nil_iff.mpr True.intro⟩,
        AllSubtreesForest.nil_iff.mpr True.intro⟩⟩,
      AllSubtreesForest.nil_iff.mpr True.intro⟩
  · intro _ e he
    rw [BorrowForest.toList_cons, BorrowSubtree.toList_node,
      BorrowForest.toList_nil] at he
    cases he with
    | head => rfl
    | tail _ ht => cases ht
  · intro _ e he
    rw [BorrowForest.toList_nil] at he
    cases he

/-- With a `.unique` child the witness forest violates the foreign-read no-op
subtree invariant (the `.frozen`-subtree invariant). -/
theorem cexForestOf_unique_not_readNoop :
    ¬ ForeignReadNoopForest [] (cexForestOf .unique) := by
  intro h
  unfold ForeignReadNoopForest cexForestOf at h
  have hroot := (AllSubtrees.node_iff.mp (AllSubtreesForest.cons_iff.mp h).1).1
  have hchild :
      isForeignReadNoopPerm (isBorrowProtected [] (cexChild .unique))
        (cexChild .unique).perm = true :=
    hroot rfl (cexChild .unique) (by
      rw [BorrowForest.toList_cons, BorrowSubtree.toList_node,
        BorrowForest.toList_nil]
      exact List.mem_cons_self ..)
  exact Bool.noConfusion hchild

/--
**Non-vacuity of the equivalence theorem.** On the witness forest with a
`.frozen` child every hypothesis of `pruneForeignRead_equiv_fullScan` holds,
the pruned traversal skips the whole subtree at its `.frozen` root, and it
agrees with the trusted full scan.
-/
theorem pruneForeignRead_frozen_subtree_agrees :
    BorrowForest.toList
        (pruneForeignRead (cexBorrows .frozen) (cexForestOf .frozen) 0 none
          []) =
      freezeTreeBorrowsOnReadAtProj (cexBorrows .frozen)
        (BorrowForest.toList (cexForestOf .frozen)) 0 none [] ∧
    pruneForeignRead (cexBorrows .frozen) (cexForestOf .frozen) 0 none [] =
      cexForestOf .frozen :=
  ⟨pruneForeignRead_equiv_fullScan (cexForestOf_sameAlloc .frozen)
      cexForestOf_frozen_readNoop 0 none [] 0 0 0,
    pruneForeignRead_skip_noop (cexBorrows .frozen) cexFrozenRoot
      [.node (cexChild .frozen) []] [] 0 none [] 0 0 [] 0 rfl⟩

/--
**Tightness witness.** Skipping the subtree of a `.frozen` root on a foreign
read is unsound without the `.frozen`-subtree invariant. On the structurally
well-formed witness forest whose `.frozen` root has a `.unique` child, the
invariant `ForeignReadNoopForest` fails, the pruned traversal (which skips at
the `.frozen` root) leaves the child `.unique`, and the trusted full scan
`freezeTreeBorrowsOnReadAtProj` freezes it: the two results differ.
-/
theorem naive_frozen_root_without_subtree_inv_counterexample :
    SameAllocForest (cexBorrows .unique) (cexForestOf .unique) ∧
    ¬ ForeignReadNoopForest [] (cexForestOf .unique) ∧
    (BorrowForest.toList
        (pruneForeignRead (cexBorrows .unique) (cexForestOf .unique) 0 none
          [])).map BorrowEntry.perm = [.frozen, .unique] ∧
    (freezeTreeBorrowsOnReadAtProj (cexBorrows .unique)
        (BorrowForest.toList (cexForestOf .unique)) 0 none []).map
        BorrowEntry.perm = [.frozen, .frozen] ∧
    BorrowForest.toList
        (pruneForeignRead (cexBorrows .unique) (cexForestOf .unique) 0 none
          []) ≠
      freezeTreeBorrowsOnReadAtProj (cexBorrows .unique)
        (BorrowForest.toList (cexForestOf .unique)) 0 none [] := by
  have hPruned : (BorrowForest.toList
      (pruneForeignRead (cexBorrows .unique) (cexForestOf .unique) 0 none
        [])).map BorrowEntry.perm = [.frozen, .unique] := by
    have hskip :
        pruneForeignRead (cexBorrows .unique) (cexForestOf .unique) 0 none [] =
          cexForestOf .unique :=
      pruneForeignRead_skip_noop (cexBorrows .unique) cexFrozenRoot
        [.node (cexChild .unique) []] [] 0 none [] 0 0 [] 0 rfl
    rw [hskip, cexForestOf_toList]
    rfl
  have hFull : (freezeTreeBorrowsOnReadAtProj (cexBorrows .unique)
      (BorrowForest.toList (cexForestOf .unique)) 0 none []).map
      BorrowEntry.perm = [.frozen, .frozen] := by
    rw [cexForestOf_toList]
    rfl
  refine ⟨cexForestOf_sameAlloc .unique, cexForestOf_unique_not_readNoop,
    hPruned, hFull, fun h => ?_⟩
  have hp := congrArg (List.map BorrowEntry.perm) h
  rw [hPruned, hFull] at hp
  cases hp


/-! ## Part 2. `Std.Do` frame-prep composition -/

section FramePrep

open Std.Do
open Anneal.PureMirExec
open Anneal.Rustc.V2026_06_01.SymbolicEval

/-! ### 2.1 The frame-prep monad and its weakest preconditions -/

/--
Fault type of frame prep: the request type `MirFailE.I` of the trusted fault
effect `MirFailE = FailE FailureKind`, written in its unfolded form
`FailReq FailureKind` (`framePrepFault_eq_mirFailE`). A fault is
`FailReq.fail kind` for a trusted `FailureKind`.
-/
abbrev FramePrepFault : Type := FailReq FailureKind

/-- `FramePrepFault` is the request type of the trusted fault effect. -/
theorem framePrepFault_eq_mirFailE : FramePrepFault = MirFailE.I := rfl

/--
The frame-prep monad: `EStateM` over the trusted `MachineState`, failing with
a request of the trusted fault effect `MirFailE`. `Std.Do` provides its `WP`
and `WPMonad` instances, with postcondition shape `FramePrepShape`.
-/
abbrev FramePrepM : Type → Type := EStateM FramePrepFault MachineState

/-- Postcondition shape of `FramePrepM`: one exception layer over one state
layer. -/
abbrev FramePrepShape : PostShape :=
  .except FramePrepFault (.arg MachineState .pure)

/--
Total-correctness postcondition of a frame-prep stage: the stage must succeed
with a result and final state satisfying `Q`; every fault is rejected.
-/
def framePost {α : Type} (Q : α → MachineState → Prop) :
    PostCond α FramePrepShape :=
  post⟨fun a s => ⌜Q a s⌝, fun _ _ => ⌜False⌝⟩

/--
The `Std.Do` weakest precondition of a frame-prep program for a
total-correctness postcondition: the program runs successfully to a result
and state satisfying the postcondition.
-/
theorem wp_framePost_iff {α : Type} (x : FramePrepM α)
    (Q : α → MachineState → Prop) (s : MachineState) :
    (wp⟦x⟧ (framePost Q) s).down ↔ ∃ a s', x.run s = .ok a s' ∧ Q a s' := by
  simp only [wp, PredTrans.apply]
  split
  · rename_i a s' heq
    exact ⟨fun hq => ⟨a, s', heq, hq⟩, fun ⟨a', s'', he, hq⟩ => by
      rw [heq] at he
      cases he
      exact hq⟩
  · rename_i e s' heq
    exact ⟨fun hq => False.elim hq, fun ⟨a', s'', he, _⟩ => by
      rw [heq] at he
      cases he⟩

/-- A `Std.Do.Triple` of a frame-prep program, unfolded to states. -/
theorem triple_framePrep_iff {α : Type} (x : FramePrepM α)
    (P : Assertion FramePrepShape) (Q : PostCond α FramePrepShape) :
    Triple x P Q ↔ ∀ s, (P s).down → (wp⟦x⟧ Q s).down :=
  Iff.rfl

/-- Running a bind whose first program succeeds. -/
theorem run_bind_ok {α β : Type} {x : FramePrepM α} {f : α → FramePrepM β}
    {s s₁ : MachineState} {a : α} (hx : x.run s = .ok a s₁) :
    (x >>= f).run s = (f a).run s₁ := by
  rw [EStateM.run_bind, hx]

/-- A successful bind factors through a successful first program. -/
theorem run_bind_ok_inv {α β : Type} {x : FramePrepM α} {f : α → FramePrepM β}
    {s s' : MachineState} {b : β} (h : (x >>= f).run s = .ok b s') :
    ∃ a s₁, x.run s = .ok a s₁ ∧ (f a).run s₁ = .ok b s' := by
  rw [EStateM.run_bind] at h
  cases hx : x.run s with
  | ok a s₁ =>
    rw [hx] at h
    exact ⟨a, s₁, rfl, h⟩
  | error e s₁ =>
    rw [hx] at h
    cases h

/-! ### 2.2 The four stages of the call pipeline -/

/--
Result of resolving a call: the instantiated callee body, the evaluated
argument values, and the caller locals after evaluating the function operand
and the arguments.
-/
structure PreparedCall : Type where
  /-- Instantiated callee body (`lookupCallee`). -/
  calleeBody : CapturedMir
  /-- Evaluated argument values (`evalOperands`). -/
  argVals : List Value
  /-- Caller locals after evaluating the function operand and arguments. -/
  localsAfterArgs : List LocalSlot

/--
Stage 1 (resolve and evaluate arguments): `resolveCallTarget`, `evalOperands`,
`lookupCallee`, and `checkCalleeTargetCompatible`, exactly as in the inline
call arm of the trusted `evalTerminator`. The stage does not change the
machine state. Undefined behavior and unsupported constructs fail with the
trusted fault of the same kind; a callee with no linked body (an intrinsic or
external call, outside frame prep) fails closed with `.unsupported`.
-/
def prepResolveAndArgs (callerBody : CapturedMir) (func : Operand)
    (argOps : List Operand) : FramePrepM PreparedCall := fun s =>
  match
    resolveCallTarget s func (length argOps) callerBody.localDecls
      callerBody.layouts
  with
  | .ub => .error (.fail .ub) s
  | .unsupported => .error (.fail .unsupported) s
  | .ok target localsAfterFunc =>
    match
      evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
        callerBody.layouts s.memory.callerLocals
        (callStack := s.memory.callStack)
    with
    | .ub => .error (.fail .ub) s
    | .unsupported => .error (.fail .unsupported) s
    | .ok argVals locals' =>
      match
        lookupCallee s.memory.callees callerBody.layouts target.defPath
          target.typeArgs s.memory.traitImpls
      with
      | .none => .error (.fail .unsupported) s
      | .some calleeBody =>
        match
          checkCalleeTargetCompatible target calleeBody (length argVals)
        with
        | false => .error (.fail .ub) s
        | true => .ok ⟨calleeBody, argVals, locals'⟩ s

/--
Stage 2 (push the callee frame): the trusted `pushCalleeFrame`, which saves
the caller frame on the call stack and activates the callee.
-/
def prepPushCalleeFrame (callerBody : CapturedMir) (destination : Place)
    (targetBb : BasicBlockIdx) (unwind : UnwindAction) (call : PreparedCall) :
    FramePrepM Unit := fun s =>
  .ok ()
    (pushCalleeFrame s callerBody call.localsAfterArgs destination targetBb
      call.calleeBody call.argVals unwind)

/--
Register one function-entry protector for the borrow `tag`: attach the fresh
protector `nextProtector` to the borrow (`attachBorrowProtector`), push it on
`activeProtectors`, and advance `nextProtector`. This is the memory update of
the trusted function-entry retag (`evalFnEntryRetag`).
-/
def registerProtector (tag : Nat) : FramePrepM Unit := fun s =>
  .ok ()
    { s with
      memory :=
        { s.memory with
          borrows :=
            attachBorrowProtector s.memory.borrows tag s.memory.nextProtector
          activeProtectors :=
            s.memory.nextProtector :: s.memory.activeProtectors
          nextProtector := Nat.add s.memory.nextProtector 1 } }

/--
Stage 3 (register function-entry protectors) for the borrows `tags`, in
order. With no protector to register the stage is `pure ()` (the 0-protector
fast path).
-/
def prepRegisterProtectors : List Nat → FramePrepM Unit
  | [] => pure ()
  | tag :: tags =>
    registerProtector tag >>= fun _ => prepRegisterProtectors tags

/--
Stage 4 (teardown and writeback), exactly as in the `TerminatorKind.return_`
arm of the trusted `evalTerminator` for a non-root frame: read the return
value from `_0`, reject a protector conflict of the frame deallocation
(`hasFrameDeallocProtectorConflict`), disable the frame's borrows
(`disableFrameBorrows`), pop the saved caller frame, restore the caller's
protectors (`restoreCallerProtectors`), and write the return value to the
caller's destination (`writeReturnDestination`), resuming the caller at its
return target. A return from the root frame (empty call stack) is not a frame
teardown and fails closed with `.unsupported`.
-/
def prepTeardownAndWriteback : FramePrepM Unit := fun s =>
  match get? s.frame.locals 0 with
  | .some (.init retVal) =>
    match
      hasFrameDeallocProtectorConflict s.memory.borrows
        s.memory.activeProtectors (length s.memory.callStack)
        (length s.frame.locals)
    with
    | true => .error (.fail .ub) s
    | false =>
      match s.memory.callStack with
      | .nil => .error (.fail .unsupported) s
      | caller :: restStack =>
        match caller.isDiverging with
        | true => .error (.fail .ub) s
        | false =>
          match
            writeReturnDestination caller.frame.locals
              { s.memory with
                borrows :=
                  disableFrameBorrows s.memory.borrows
                    (length s.memory.callStack) (length s.frame.locals)
                callStack := restStack
                activeCallee := .some caller.callerBody
                activeProtectors := restoreCallerProtectors caller }
              caller.destination retVal caller.callerBody.localDecls
              caller.callerBody.layouts
          with
          | .ok updatedCallerLocals mem' =>
            .ok ()
              { frame :=
                  { caller.frame with
                    blockIdx := caller.returnTarget
                    stmtIdx := 0
                    locals := updatedCallerLocals }
                memory := mem' }
          | .ub => .error (.fail .ub) s
          | .unsupported => .error (.fail .unsupported) s
  | _ => .error (.fail .ub) s

/--
Call entry: stages 1 and 2 in sequence, returning the prepared call. This is
one step of the trusted machine (`evalTerminator_call_of_prepCallEntry`).
-/
def prepCallEntry (callerBody : CapturedMir) (func : Operand)
    (argOps : List Operand) (destination : Place) (targetBb : BasicBlockIdx)
    (unwind : UnwindAction) : FramePrepM PreparedCall :=
  prepResolveAndArgs callerBody func argOps >>= fun call =>
    prepPushCalleeFrame callerBody destination targetBb unwind call >>= fun _ =>
      pure call

/-! ### 2.3 Exactness of the stages against the trusted machine -/

/--
A successful stage 1 leaves the state unchanged and records the successful
results of the four trusted functions it runs.
-/
theorem prepResolveAndArgs_ok {callerBody : CapturedMir} {func : Operand}
    {argOps : List Operand} {s s' : MachineState} {call : PreparedCall}
    (h : (prepResolveAndArgs callerBody func argOps).run s = .ok call s') :
    s' = s ∧
    ∃ (target : ResolvedCallTarget) (localsAfterFunc : List LocalSlot),
      resolveCallTarget s func (length argOps) callerBody.localDecls
          callerBody.layouts = .ok target localsAfterFunc ∧
      evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
          callerBody.layouts s.memory.callerLocals
          (callStack := s.memory.callStack) =
        .ok call.argVals call.localsAfterArgs ∧
      lookupCallee s.memory.callees callerBody.layouts target.defPath
          target.typeArgs s.memory.traitImpls = some call.calleeBody ∧
      checkCalleeTargetCompatible target call.calleeBody (length call.argVals) =
        true := by
  unfold prepResolveAndArgs EStateM.run at h
  dsimp only [] at h
  cases hRes : resolveCallTarget s func (length argOps) callerBody.localDecls
      callerBody.layouts with
  | ub =>
    rw [hRes] at h
    cases h
  | unsupported =>
    rw [hRes] at h
    cases h
  | ok target localsAfterFunc =>
    rw [hRes] at h
    dsimp only [] at h
    cases hArgs : evalOperands localsAfterFunc argOps s.memory.borrows
        s.memory.globals callerBody.layouts s.memory.callerLocals
        (callStack := s.memory.callStack) with
    | ub =>
      rw [hArgs] at h
      cases h
    | unsupported =>
      rw [hArgs] at h
      cases h
    | ok argVals locals' =>
      rw [hArgs] at h
      dsimp only [] at h
      cases hLookup : lookupCallee s.memory.callees callerBody.layouts
          target.defPath target.typeArgs s.memory.traitImpls with
      | none =>
        rw [hLookup] at h
        cases h
      | some calleeBody =>
        rw [hLookup] at h
        dsimp only [] at h
        cases hCompat : checkCalleeTargetCompatible target calleeBody
            (length argVals) with
        | false =>
          rw [hCompat] at h
          cases h
        | true =>
          rw [hCompat] at h
          cases h
          exact ⟨rfl, target, localsAfterFunc, rfl, hArgs, hLookup, hCompat⟩

/--
A successful call entry is the trusted `pushCalleeFrame` applied to the
successful results of stage 1.
-/
theorem prepCallEntry_ok {callerBody : CapturedMir} {func : Operand}
    {argOps : List Operand} {destination : Place} {targetBb : BasicBlockIdx}
    {unwind : UnwindAction} {s s₁ : MachineState} {call : PreparedCall}
    (h : (prepCallEntry callerBody func argOps destination targetBb unwind).run
      s = .ok call s₁) :
    s₁ =
        pushCalleeFrame s callerBody call.localsAfterArgs destination targetBb
          call.calleeBody call.argVals unwind ∧
    ∃ (target : ResolvedCallTarget) (localsAfterFunc : List LocalSlot),
      resolveCallTarget s func (length argOps) callerBody.localDecls
          callerBody.layouts = .ok target localsAfterFunc ∧
      evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
          callerBody.layouts s.memory.callerLocals
          (callStack := s.memory.callStack) =
        .ok call.argVals call.localsAfterArgs ∧
      lookupCallee s.memory.callees callerBody.layouts target.defPath
          target.typeArgs s.memory.traitImpls = some call.calleeBody ∧
      checkCalleeTargetCompatible target call.calleeBody (length call.argVals) =
        true := by
  unfold prepCallEntry at h
  obtain ⟨call', s', hx, hrest⟩ := run_bind_ok_inv h
  obtain ⟨hs, hres⟩ := prepResolveAndArgs_ok hx
  have hrest' :
      EStateM.Result.ok (ε := FramePrepFault) call'
          (pushCalleeFrame s' callerBody call'.localsAfterArgs destination
            targetBb call'.calleeBody call'.argVals unwind) =
        .ok call s₁ := hrest
  cases hrest'
  rw [hs]
  exact ⟨rfl, hres⟩

/--
**Call entry is one trusted step.** If call entry succeeds from `s` to `s₁`,
then the trusted `evalTerminator` of the corresponding inline
`TerminatorKind.call` steps from `s` to exactly `s₁`.
-/
theorem evalTerminator_call_of_prepCallEntry {callerBody : CapturedMir}
    {term : Terminator} {func : Operand} {argOps : List Operand}
    {destination : Place} {targetBb : BasicBlockIdx} {unwind : UnwindAction}
    {s s₁ : MachineState} {call : PreparedCall}
    (hKind : term.kind = .call func argOps destination (some targetBb) unwind)
    (h : (prepCallEntry callerBody func argOps destination targetBb unwind).run
      s = .ok call s₁) :
    evalTerminator s term (some callerBody) = MirStepNode.step s₁ := by
  obtain ⟨hs₁, target, localsAfterFunc, hRes, hArgs, hLookup, hCompat⟩ :=
    prepCallEntry_ok h
  cases term with
  | mk kind span =>
    have hKind' : kind = .call func argOps destination (some targetBb) unwind :=
      hKind
    rw [hKind', hs₁]
    unfold evalTerminator
    dsimp only [bodyLocalDeclsOf]
    rw [hRes]
    dsimp only []
    rw [hArgs]
    dsimp only []
    rw [hLookup]
    dsimp only []
    rw [hCompat]

/--
**Teardown and writeback is one trusted step.** If stage 4 succeeds from `s`
to `s'`, then the trusted `evalTerminator` of `TerminatorKind.return_` steps
from `s` to exactly `s'`, and `s'` is the popped caller frame resumed at its
return target with statement index `0`.
-/
theorem prepTeardownAndWriteback_spec {s s' : MachineState}
    (h : prepTeardownAndWriteback.run s = .ok () s') :
    (∀ (span : String) (currentBody : Option CapturedMir),
      evalTerminator s { kind := .return_, span := span } currentBody =
        MirStepNode.step s') ∧
    ∃ (caller : SavedCallerFrame) (restStack : List SavedCallerFrame)
      (updatedCallerLocals : List LocalSlot) (mem' : Memory),
      s.memory.callStack = caller :: restStack ∧
      caller.isDiverging = false ∧
      s' =
        { frame :=
            { blockIdx := caller.returnTarget
              stmtIdx := 0
              locals := updatedCallerLocals }
          memory := mem' } := by
  unfold prepTeardownAndWriteback EStateM.run at h
  dsimp only [] at h
  cases hget : get? s.frame.locals 0 with
  | none =>
    rw [hget] at h
    cases h
  | some slot =>
    rw [hget] at h
    cases slot with
    | dead => cases h
    | uninit => cases h
    | init retVal =>
      dsimp only [] at h
      cases hconf : hasFrameDeallocProtectorConflict s.memory.borrows
          s.memory.activeProtectors (length s.memory.callStack)
          (length s.frame.locals) with
      | true =>
        rw [hconf] at h
        cases h
      | false =>
        rw [hconf] at h
        dsimp only [] at h
        cases hstack : s.memory.callStack with
        | nil =>
          rw [hstack] at h
          cases h
        | cons caller restStack =>
          rw [hstack] at h hconf
          dsimp only [] at h
          cases hdiv : caller.isDiverging with
          | true =>
            rw [hdiv] at h
            cases h
          | false =>
            rw [hdiv] at h
            dsimp only [] at h
            cases hwrite : writeReturnDestination caller.frame.locals
                { s.memory with
                  borrows :=
                    disableFrameBorrows s.memory.borrows
                      (length (caller :: restStack)) (length s.frame.locals)
                  callStack := restStack
                  activeCallee := .some caller.callerBody
                  activeProtectors := restoreCallerProtectors caller }
                caller.destination retVal caller.callerBody.localDecls
                caller.callerBody.layouts with
            | ub =>
              rw [hwrite] at h
              cases h
            | unsupported =>
              rw [hwrite] at h
              cases h
            | ok updatedCallerLocals mem' =>
              rw [hwrite] at h
              cases h
              refine ⟨fun span currentBody => ?_,
                caller, restStack, updatedCallerLocals, mem', rfl, hdiv, rfl⟩
              unfold evalTerminator
              dsimp only []
              rw [hget]
              dsimp only []
              rw [hstack, hconf]
              dsimp only []
              rw [hdiv]
              dsimp only []
              rw [hwrite]

/-- Stage 4 as one trusted step, for any terminator of kind `return_`. -/
theorem evalTerminator_return_of_prepTeardown {s s' : MachineState}
    {term : Terminator} {currentBody : Option CapturedMir}
    (hKind : term.kind = .return_)
    (h : prepTeardownAndWriteback.run s = .ok () s') :
    evalTerminator s term currentBody = MirStepNode.step s' := by
  cases term with
  | mk kind span =>
    have hKind' : kind = .return_ := hKind
    rw [hKind']
    exact (prepTeardownAndWriteback_spec h).1 span currentBody

/-! ### 2.4 Function-entry protector registration (stage 3) -/

/-- The 0-protector fast path: with no protector to register, stage 3 leaves
the state unchanged. -/
theorem prepRegisterProtectors_nil_run (s : MachineState) :
    (prepRegisterProtectors []).run s = .ok () s := rfl

/-- Stage 3 registers the first protector and continues with the rest. -/
theorem prepRegisterProtectors_cons_run (tag : Nat) (tags : List Nat)
    (s : MachineState) :
    (prepRegisterProtectors (tag :: tags)).run s =
      (prepRegisterProtectors tags).run
        { s with
          memory :=
            { s.memory with
              borrows :=
                attachBorrowProtector s.memory.borrows tag
                  s.memory.nextProtector
              activeProtectors :=
                s.memory.nextProtector :: s.memory.activeProtectors
              nextProtector := Nat.add s.memory.nextProtector 1 } } := by
  show (registerProtector tag >>= fun _ => prepRegisterProtectors tags).run s =
    _
  exact run_bind_ok rfl

/--
Stage 3 always succeeds. It preserves the frame, the call stack, and the
active callee, and it registers exactly one fresh protector per tag:
`nextProtector` advances by the number of tags and `activeProtectors` grows by
the number of tags.
-/
theorem prepRegisterProtectors_ok (tags : List Nat) :
    ∀ s : MachineState, ∃ s' : MachineState,
      (prepRegisterProtectors tags).run s = .ok () s' ∧
      s'.frame = s.frame ∧
      s'.memory.callStack = s.memory.callStack ∧
      s'.memory.activeCallee = s.memory.activeCallee ∧
      s'.memory.nextProtector = s.memory.nextProtector + tags.length ∧
      s'.memory.activeProtectors.length =
        s.memory.activeProtectors.length + tags.length := by
  induction tags with
  | nil => exact fun s => ⟨s, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons tag tags ih =>
    intro s
    obtain ⟨s', hrun, hframe, hstack, hcallee, hnext, hlen⟩ :=
      ih { s with
           memory :=
             { s.memory with
               borrows :=
                 attachBorrowProtector s.memory.borrows tag
                   s.memory.nextProtector
               activeProtectors :=
                 s.memory.nextProtector :: s.memory.activeProtectors
               nextProtector := Nat.add s.memory.nextProtector 1 } }
    refine ⟨s', (prepRegisterProtectors_cons_run tag tags s).trans hrun, hframe,
      hstack, hcallee, ?_, ?_⟩
    · rw [hnext]
      show s.memory.nextProtector + 1 + tags.length =
        s.memory.nextProtector + (tags.length + 1)
      rw [Nat.add_assoc, Nat.add_comm 1]
    · rw [hlen]
      show s.memory.activeProtectors.length + 1 + tags.length =
        s.memory.activeProtectors.length + (tags.length + 1)
      rw [Nat.add_assoc, Nat.add_comm 1]

/-- Weakest precondition of the 0-protector fast path. -/
theorem wp_prepRegisterProtectors_nil (Q : Unit → MachineState → Prop)
    (s : MachineState) :
    (wp⟦prepRegisterProtectors []⟧ (framePost Q) s).down ↔ Q () s := by
  rw [wp_framePost_iff]
  constructor
  · intro ⟨a, s', hrun, hq⟩
    have hrun' : EStateM.Result.ok (ε := FramePrepFault) () s = .ok a s' := hrun
    cases hrun'
    exact hq
  · intro hq
    exact ⟨(), s, rfl, hq⟩

/--
**Stage 3 is the trusted function-entry protector registration.** On the
attach-only path of the trusted function-entry retag `evalFnEntryRetag` (the
retagged place has no recorded type), the trusted step advances the statement
with exactly the memory produced by `prepRegisterProtectors` for the retagged
borrow.
-/
theorem evalFnEntryRetag_attachOnly_eq_prepRegisterProtectors
    (s s₁ : MachineState) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (place : Place) (ptrVal : ProvenancePtr) (sz : Nat)
    (parentEntry : BorrowEntry) (locals' : List LocalSlot)
    (hTy : placeTy localDecls layouts place = none)
    (h : (prepRegisterProtectors [ptrVal.tag]).run s = .ok () s₁) :
    evalFnEntryRetag s localDecls layouts place ptrVal sz parentEntry locals' =
      MirStepNode.step (advanceStmt s locals' s₁.memory) := by
  have h' : EStateM.Result.ok (ε := FramePrepFault) ()
      { s with
        memory :=
          { s.memory with
            borrows :=
              attachBorrowProtector s.memory.borrows ptrVal.tag
                s.memory.nextProtector
            activeProtectors :=
              s.memory.nextProtector :: s.memory.activeProtectors
            nextProtector := Nat.add s.memory.nextProtector 1 } } =
      .ok () s₁ := h
  cases h'
  unfold evalFnEntryRetag
  dsimp only []
  rw [hTy]

/-! ### 2.5 Executions of the trusted machine and `LiftFrame` -/

/-- `n` silent steps of the trusted `stepMirFn` lead from `s` to `s'`. -/
inductive StepsTo (body : CapturedMir) :
    MachineState → Nat → MachineState → Prop where
  /-- Zero steps. -/
  | refl (s : MachineState) : StepsTo body s 0 s
  /-- One silent trusted step followed by `n` steps. -/
  | step {s s₁ s' : MachineState} {n : Nat} :
      stepMirFn body s = MirStepNode.step s₁ → StepsTo body s₁ n s' →
      StepsTo body s (n + 1) s'

/-- A single silent trusted step. -/
theorem StepsTo.single {body : CapturedMir} {s s' : MachineState}
    (h : stepMirFn body s = MirStepNode.step s') : StepsTo body s 1 s' :=
  StepsTo.step h (StepsTo.refl s')

/-- Concatenation of executions. -/
theorem StepsTo.trans {body : CapturedMir} {s s₁ s₂ : MachineState} {n m : Nat}
    (h₁ : StepsTo body s n s₁) (h₂ : StepsTo body s₁ m s₂) :
    StepsTo body s (m + n) s₂ := by
  induction h₁ with
  | refl s => exact h₂
  | step hstep _ ih => exact StepsTo.step hstep (ih h₂)

/--
`LiftFrame` at an arbitrary machine state: from `s`, the execution of `body`
returns normally from the root frame within `fuel` steps with a value
satisfying `post`.
-/
def LiftState (body : CapturedMir) (s : MachineState) (post : Value → Prop)
    (fuel : Nat) : Prop :=
  wpMirExecSym fuel body (.running s)
    (mirNormalPost fun retVal _ => post retVal)

/-- `LiftState` at an embedded frame is `LiftFrame`. -/
theorem liftState_iff_liftFrame {body : CapturedMir} {bbIdx : BasicBlockIdx}
    {stmtIdx : Nat} {env : PureEnv} {mem : Memory} {post : Value → Prop}
    {fuel : Nat} :
    LiftState body
        (PureState.toMachineState
          { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)
        post fuel ↔
      LiftFrame body bbIdx stmtIdx env mem post fuel := by
  unfold LiftState LiftFrame
  exact Iff.rfl

/-- One silent trusted step extends `LiftState` by one unit of fuel. -/
theorem LiftState.of_step {body : CapturedMir} {s s' : MachineState}
    {post : Value → Prop} {fuel : Nat}
    (h : stepMirFn body s = MirStepNode.step s')
    (hw : LiftState body s' post fuel) : LiftState body s post (fuel + 1) := by
  unfold LiftState wpMirExecSym
  rw [evalSymNodeTree_eq, stepMirExecSymTree_eval]
  show evalNodeWP _ _ (stepMirFn body s)
  rw [h]
  exact hw

/-- `n` silent trusted steps extend `LiftState` by `n` units of fuel. -/
theorem LiftState.of_stepsTo {body : CapturedMir} {s s' : MachineState}
    {post : Value → Prop} {fuel n : Nat} (h : StepsTo body s n s')
    (hw : LiftState body s' post fuel) : LiftState body s post (fuel + n) := by
  induction h with
  | refl s => exact hw
  | step hstep _ ih => exact LiftState.of_step hstep (ih hw)

/-- Fuel monotonicity of `LiftState`. -/
theorem LiftState.mono {body : CapturedMir} {s : MachineState}
    {post : Value → Prop} {f₁ f₂ : Nat} (hle : f₁ ≤ f₂)
    (h : LiftState body s post f₁) : LiftState body s post f₂ :=
  Anneal.MirFuelFree.wpMirExecSym_mono hle h

/--
**Multi-continuation composition.** Two continuations from the same state,
with postconditions `post₁` and `post₂`, compose into one continuation with
the conjunction of the postconditions (the trusted machine is deterministic
up to its external answers, over which `LiftFrame` quantifies universally).
-/
theorem LiftState.and {body : CapturedMir} {s : MachineState}
    {post₁ post₂ : Value → Prop} {fuel : Nat}
    (h₁ : LiftState body s post₁ fuel) (h₂ : LiftState body s post₂ fuel) :
    LiftState body s (fun v => post₁ v ∧ post₂ v) fuel := by
  have h := Anneal.MirFuelFree.wpMirExecSym_conj h₁ h₂
  exact Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym_mono
    (fun out hout => by
      cases out with
      | normal r =>
        cases r
        exact hout
      | panic => exact hout.1
      | abort => exact hout.1) h

private theorem get?_eq_none_of_eq_length {α : Type} :
    ∀ (xs : List α) (i : Nat), i = length xs → get? xs i = none
  | [], _, rfl => rfl
  | _ :: tl, _, rfl => get?_eq_none_of_eq_length tl (length tl) rfl

private theorem ite_eq_of_true {α : Type} {b : Bool} {t e : α}
    (hb : b = true) : (if b = true then t else e) = t := by
  cases b with
  | true => rfl
  | false => cases hb

/--
At the end of a block of the active body, the trusted `stepMirFn` evaluates
the block's terminator.
-/
theorem stepMirFn_at_terminator {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements) :
    stepMirFn body s = evalTerminator s blk.terminator (some cur) := by
  have hNone : get? blk.statements s.frame.stmtIdx = none :=
    get?_eq_none_of_eq_length blk.statements s.frame.stmtIdx hEnd
  have hBeq : (s.frame.stmtIdx == length blk.statements) = true := by
    rw [hEnd]
    exact decide_eq_true rfl
  unfold stepMirFn
  rw [hCur]
  dsimp only []
  rcases hPhase with hp | hp <;>
    (rw [hp]; dsimp only []; rw [hBb]; dsimp only []; rw [hNone]; dsimp only [];
     exact ite_eq_of_true hBeq)

/-! ### 2.6 Callee contracts and `wpFramePrep` -/

/--
The machine is ready to return `retVal` from the active frame: the active
body is at a `TerminatorKind.return_` terminator, the return place `_0` holds
`retVal`, and deallocating the frame conflicts with no active protector.
-/
def ReturnReady (body : CapturedMir) (s : MachineState) (retVal : Value) :
    Prop :=
  ∃ (cur : CapturedMir) (blk : BasicBlockData),
    s.memory.activeCallee.getD body = cur ∧
    (cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized) ∧
    get? cur.basicBlocks s.frame.blockIdx = some blk ∧
    s.frame.stmtIdx = length blk.statements ∧
    blk.terminator.kind = .return_ ∧
    get? s.frame.locals 0 = some (.init retVal) ∧
    hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
      (length s.memory.callStack) (length s.frame.locals) = false

/--
Contract of a callee, stated on machine states of the trusted semantics of
the root body `body`.

- `Pre` is the precondition on the callee entry state (the state right after
  `pushCalleeFrame`).
- `Post` relates the entry state, the returned value, and the return-ready
  state.
- `steps` is the number of trusted steps the callee takes from an entry
  state.
- `exec` is the step-execution guarantee: from every entry state satisfying
  `Pre`, the trusted machine takes `steps` silent steps to a state that is
  ready to return some `retVal` without a protector conflict
  (`ReturnReady`), whose call stack is the entry call stack (the caller's
  saved frames are preserved), and that satisfies `Post`.
-/
structure FramePrepContract (body : CapturedMir) where
  /-- Precondition on the callee entry state. -/
  Pre : MachineState → Prop
  /-- Postcondition on entry state, returned value, and return-ready state. -/
  Post : MachineState → Value → MachineState → Prop
  /-- Number of trusted steps from an entry state to the return-ready state. -/
  steps : MachineState → Nat
  /-- Step-execution guarantee of the callee body. -/
  exec : ∀ s₀ : MachineState, Pre s₀ →
    ∃ (sRet : MachineState) (retVal : Value),
      StepsTo body s₀ (steps s₀) sRet ∧ ReturnReady body sRet retVal ∧
      sRet.memory.callStack = s₀.memory.callStack ∧ Post s₀ retVal sRet

/--
Weakest precondition of an inline call against a callee contract, composed
from the `Std.Do` weakest preconditions of the frame-prep stages: call entry
(stages 1 and 2) must succeed into a state satisfying the contract's
precondition, and from every return-ready state allowed by the contract's
postcondition, teardown and writeback (stage 4) must succeed into a state
satisfying `Q`.
-/
def wpFramePrep {body : CapturedMir} (C : FramePrepContract body)
    (callerBody : CapturedMir) (func : Operand) (argOps : List Operand)
    (destination : Place) (targetBb : BasicBlockIdx) (unwind : UnwindAction)
    (Q : MachineState → Prop) : Assertion FramePrepShape :=
  wp⟦prepCallEntry callerBody func argOps destination targetBb unwind⟧
    (framePost fun _ s₁ =>
      C.Pre s₁ ∧
      ∀ (sRet : MachineState) (retVal : Value),
        C.Post s₁ retVal sRet → ReturnReady body sRet retVal →
        sRet.memory.callStack = s₁.memory.callStack →
          (wp⟦prepTeardownAndWriteback⟧ (framePost fun _ s' => Q s') sRet).down)

/-- One trusted step, as a frame-prep program: a silent step succeeds, and a
fault or any other transition fails. -/
def prepStep (body : CapturedMir) : FramePrepM Unit := fun s =>
  match stepMirFn body s with
  | .tau (.running s') => .ok () s'
  | .vis (.inl (FailReq.fail kind)) _ => .error (FailReq.fail kind) s
  | _ => .error (FailReq.fail .unsupported) s

/-- `n` trusted steps, as a frame-prep program. -/
def prepSteps (body : CapturedMir) : Nat → FramePrepM Unit
  | 0 => pure ()
  | n + 1 => prepStep body >>= fun _ => prepSteps body n

/-- The callee body, as a frame-prep program: run the trusted machine for the
number of steps prescribed at the entry state. -/
def prepRunCallee (body : CapturedMir) (steps : MachineState → Nat) :
    FramePrepM Unit := fun s =>
  prepSteps body (steps s) s

/--
The whole inline call as one executable frame-prep program: call entry, the
callee body run on the trusted machine, then teardown and writeback.
-/
def framePrepCall (body : CapturedMir) (C : FramePrepContract body)
    (callerBody : CapturedMir) (func : Operand) (argOps : List Operand)
    (destination : Place) (targetBb : BasicBlockIdx) (unwind : UnwindAction) :
    FramePrepM Unit :=
  prepCallEntry callerBody func argOps destination targetBb unwind >>= fun _ =>
    prepRunCallee body C.steps >>= fun _ => prepTeardownAndWriteback

/-- A silent trusted step is a successful `prepStep`. -/
theorem prepStep_ok_of_step {body : CapturedMir} {s s' : MachineState}
    (h : stepMirFn body s = MirStepNode.step s') :
    (prepStep body).run s = .ok () s' := by
  show (match stepMirFn body s with
    | .tau (.running s') => EStateM.Result.ok () s'
    | .vis (.inl (FailReq.fail kind)) _ => .error (FailReq.fail kind) s
    | _ => .error (FailReq.fail .unsupported) s) = .ok () s'
  rw [h]
  rfl

/-- An execution of the trusted machine is a successful run of `prepSteps`. -/
theorem prepSteps_ok_of_stepsTo {body : CapturedMir} {s s' : MachineState}
    {n : Nat} (h : StepsTo body s n s') :
    (prepSteps body n).run s = .ok () s' := by
  induction h with
  | refl s => rfl
  | step hstep _ ih =>
    show (prepStep body >>= fun _ => prepSteps body _).run _ = _
    rw [run_bind_ok (prepStep_ok_of_step hstep)]
    exact ih

/--
Unfolding of `wpFramePrep`: the precondition holds exactly when call entry
succeeds into a state satisfying the contract's precondition from which
every contract-allowed return-ready state tears down successfully into `Q`.
-/
theorem wpFramePrep_iff {body : CapturedMir} (C : FramePrepContract body)
    (callerBody : CapturedMir) (func : Operand) (argOps : List Operand)
    (destination : Place) (targetBb : BasicBlockIdx) (unwind : UnwindAction)
    (Q : MachineState → Prop) (s : MachineState) :
    (wpFramePrep C callerBody func argOps destination targetBb unwind Q
        s).down ↔
      ∃ (call : PreparedCall) (s₁ : MachineState),
        (prepCallEntry callerBody func argOps destination targetBb unwind).run
          s = .ok call s₁ ∧
        C.Pre s₁ ∧
        ∀ (sRet : MachineState) (retVal : Value),
          C.Post s₁ retVal sRet → ReturnReady body sRet retVal →
          sRet.memory.callStack = s₁.memory.callStack →
            ∃ s', prepTeardownAndWriteback.run sRet = .ok () s' ∧ Q s' := by
  unfold wpFramePrep
  rw [wp_framePost_iff]
  constructor
  · intro ⟨call, s₁, hrun, hpre, hrest⟩
    refine ⟨call, s₁, hrun, hpre, fun sRet retVal hpost hrr hstack => ?_⟩
    obtain ⟨_, s', htd, hq⟩ :=
      (wp_framePost_iff _ _ _).mp (hrest sRet retVal hpost hrr hstack)
    exact ⟨s', htd, hq⟩
  · intro ⟨call, s₁, hrun, hpre, hrest⟩
    refine ⟨call, s₁, hrun, hpre, fun sRet retVal hpost hrr hstack => ?_⟩
    obtain ⟨s', htd, hq⟩ := hrest sRet retVal hpost hrr hstack
    exact (wp_framePost_iff _ _ _).mpr ⟨(), s', htd, hq⟩

/--
The trusted execution extracted from `wpFramePrep`: call entry, the callee's
contract execution, and teardown, ending in a state satisfying `Q`.
-/
theorem wpFramePrep_run {body : CapturedMir} (C : FramePrepContract body)
    (callerBody : CapturedMir) (func : Operand) (argOps : List Operand)
    (destination : Place) (targetBb : BasicBlockIdx) (unwind : UnwindAction)
    (Q : MachineState → Prop) (s : MachineState)
    (h : (wpFramePrep C callerBody func argOps destination targetBb unwind Q
      s).down) :
    ∃ (call : PreparedCall) (s₁ sRet : MachineState) (retVal : Value)
      (s' : MachineState),
      (prepCallEntry callerBody func argOps destination targetBb unwind).run s =
        .ok call s₁ ∧
      C.Pre s₁ ∧ StepsTo body s₁ (C.steps s₁) sRet ∧
      ReturnReady body sRet retVal ∧
      sRet.memory.callStack = s₁.memory.callStack ∧ C.Post s₁ retVal sRet ∧
      prepTeardownAndWriteback.run sRet = .ok () s' ∧ Q s' := by
  obtain ⟨call, s₁, hrun, hpre, hrest⟩ :=
    (wpFramePrep_iff C callerBody func argOps destination targetBb unwind Q
      s).mp h
  obtain ⟨sRet, retVal, hsteps, hrr, hstack, hpost⟩ := C.exec s₁ hpre
  obtain ⟨s', htd, hq⟩ := hrest sRet retVal hpost hrr hstack
  exact ⟨call, s₁, sRet, retVal, s', hrun, hpre, hsteps, hrr, hstack, hpost,
    htd, hq⟩

/--
**`Std.Do.Triple` soundness of `wpFramePrep`.** The contract-based weakest
precondition is a valid precondition of the executable call pipeline
`framePrepCall`, whose callee part runs the trusted machine: started in a
state satisfying `wpFramePrep`, the pipeline succeeds in a state satisfying
`Q`.
-/
theorem wpFramePrep_triple_sound {body : CapturedMir}
    (C : FramePrepContract body) (callerBody : CapturedMir) (func : Operand)
    (argOps : List Operand) (destination : Place) (targetBb : BasicBlockIdx)
    (unwind : UnwindAction) (Q : MachineState → Prop) :
    Triple
      (framePrepCall body C callerBody func argOps destination targetBb unwind)
      (wpFramePrep C callerBody func argOps destination targetBb unwind Q)
      (framePost fun _ s' => Q s') := by
  rw [triple_framePrep_iff]
  intro s h
  obtain ⟨call, s₁, sRet, retVal, s', hrun, _, hsteps, _, _, _, htd, hq⟩ :=
    wpFramePrep_run C callerBody func argOps destination targetBb unwind Q s h
  refine (wp_framePost_iff _ _ _).mpr ⟨(), s', ?_, hq⟩
  unfold framePrepCall
  rw [run_bind_ok hrun]
  have hcallee : (prepRunCallee body C.steps).run s₁ = .ok () sRet :=
    prepSteps_ok_of_stepsTo hsteps
  rw [run_bind_ok hcallee]
  exact htd

/--
**Soundness of `wpFramePrep` against the trusted machine.** At a
`TerminatorKind.call` terminator of the active body `cur`, if `wpFramePrep`
holds for a callee contract `C` whose step count is bounded by `n`, and the
continuation at the call's target block `targetBb` is lifted for every state
satisfying `Q`, then the caller frame is lifted: the real `stepMirFn`
execution performs call entry (one step), the callee body (`C.steps` steps),
and frame teardown with protector restoration and return writeback (one
step), and resumes in `LiftFrame` at `targetBb`.
-/
theorem wpFramePrep_sound_stepMirFn {body cur : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv} {mem : Memory}
    {blk : BasicBlockData} {post : Value → Prop} {fuel : Nat}
    (C : FramePrepContract body) {func : Operand} {argOps : List Operand}
    {destination : Place} {targetBb : BasicBlockIdx} {unwind : UnwindAction}
    {Q : MachineState → Prop} (n : Nat)
    (hCur : mem.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks bbIdx = some blk)
    (hEnd : stmtIdx = length blk.statements)
    (hTerm : blk.terminator.kind =
      .call func argOps destination (some targetBb) unwind)
    (hSteps : ∀ s₁, C.Pre s₁ → C.steps s₁ ≤ n)
    (hWp : (wpFramePrep C cur func argOps destination targetBb unwind Q
      (PureState.toMachineState
        { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)).down)
    (hCont : ∀ (env' : PureEnv) (mem' : Memory),
      Q (PureState.toMachineState
        { bb := targetBb, stmtIdx := 0, env := env' } mem') →
      LiftFrame body targetBb 0 env' mem' post fuel) :
    LiftFrame body bbIdx stmtIdx env mem post (fuel + n + 2) := by
  obtain ⟨call, s₁, sRet, retVal, s', hEntry, hPre, hSt, hRR, hStack, _, hTd,
    hQ⟩ := wpFramePrep_run C cur func argOps destination targetBb unwind Q _ hWp
  -- Call entry is one trusted step.
  have hStep₀ :
      stepMirFn body
          (PureState.toMachineState
            { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem) =
        MirStepNode.step s₁ :=
    (stepMirFn_at_terminator (s := PureState.toMachineState
      { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem) hCur hPhase hBb
      hEnd).trans (evalTerminator_call_of_prepCallEntry hTerm hEntry)
  -- Teardown and writeback is one trusted step.
  obtain ⟨curR, blkR, hCurR, hPhaseR, hBbR, hEndR, hKindR, _, _⟩ := hRR
  have hStepR : stepMirFn body sRet = MirStepNode.step s' :=
    (stepMirFn_at_terminator hCurR hPhaseR hBbR hEndR).trans
      (evalTerminator_return_of_prepTeardown hKindR hTd)
  -- The teardown resumes the frame saved by this call, at `targetBb`.
  obtain ⟨caller, restStack, updatedCallerLocals, mem', hcs, _, hs'⟩ :=
    (prepTeardownAndWriteback_spec hTd).2
  have hs₁ := (prepCallEntry_ok hEntry).1
  have hsaved : sRet.memory.callStack =
      (pushCalleeFrame
        (PureState.toMachineState
          { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)
        cur call.localsAfterArgs destination targetBb call.calleeBody
        call.argVals unwind).memory.callStack := by
    rw [hStack, hs₁]
  rw [hcs] at hsaved
  have hcaller : caller.returnTarget = targetBb := by
    injection hsaved with hc _
    rw [hc]
  rw [hcaller] at hs'
  rw [hs'] at hQ hStepR
  have hLift' : LiftState body
      (PureState.toMachineState
        { bb := targetBb, stmtIdx := 0, env := updatedCallerLocals } mem')
      post fuel :=
    liftState_iff_liftFrame.mpr (hCont updatedCallerLocals mem' hQ)
  have hLiftR : LiftState body sRet post (fuel + 1) :=
    LiftState.of_step hStepR hLift'
  have hLift₁ : LiftState body s₁ post (fuel + 1 + C.steps s₁) :=
    LiftState.of_stepsTo hSt hLiftR
  have hLift₀ : LiftState body
      (PureState.toMachineState
        { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)
      post (fuel + 1 + C.steps s₁ + 1) :=
    LiftState.of_step hStep₀ hLift₁
  have hle : fuel + 1 + C.steps s₁ + 1 ≤ fuel + n + 2 := by
    have h2 : fuel + 1 + C.steps s₁ ≤ fuel + 1 + n :=
      Nat.add_le_add_left (hSteps s₁ hPre) (fuel + 1)
    rw [Nat.add_right_comm fuel 1 n] at h2
    exact Nat.succ_le_succ h2
  exact liftState_iff_liftFrame.mp (LiftState.mono hle hLift₀)

/-! ### 2.7 Sequential composition and prefix sharing -/

/--
Sequential composition of weakest preconditions of frame-prep programs: the
`Std.Do` weakest precondition of `x >>= f` for a total-correctness
postcondition is the weakest precondition of `x` for the weakest precondition
of `f`.
-/
theorem wp_framePrep_bind {α β : Type} (x : FramePrepM α)
    (f : α → FramePrepM β) (Q : β → MachineState → Prop) (s : MachineState) :
    (wp⟦x >>= f⟧ (framePost Q) s).down ↔
      (wp⟦x⟧ (framePost fun a s₁ => (wp⟦f a⟧ (framePost Q) s₁).down)
        s).down := by
  rw [wp_framePost_iff, wp_framePost_iff]
  constructor
  · intro ⟨b, s', hrun, hq⟩
    obtain ⟨a, s₁, hx, hf⟩ := run_bind_ok_inv hrun
    exact ⟨a, s₁, hx, (wp_framePost_iff _ _ _).mpr ⟨b, s', hf, hq⟩⟩
  · intro ⟨a, s₁, hx, hf⟩
    obtain ⟨b, s', hf', hq⟩ := (wp_framePost_iff _ _ _).mp hf
    exact ⟨b, s', (run_bind_ok hx).trans hf', hq⟩

/--
**Sequential multi-call composition.** The weakest precondition of a first
call, taken for the weakest precondition of a second call as its continuation
predicate, is a valid `Std.Do.Triple` precondition of the two call pipelines
run in sequence (by `Std.Do.Triple.bind` over `wpFramePrep_triple_sound`).
-/
theorem wpFramePrep_seq {body : CapturedMir} (C₁ C₂ : FramePrepContract body)
    (callerBody₁ callerBody₂ : CapturedMir) (func₁ func₂ : Operand)
    (argOps₁ argOps₂ : List Operand) (destination₁ destination₂ : Place)
    (targetBb₁ targetBb₂ : BasicBlockIdx) (unwind₁ unwind₂ : UnwindAction)
    (Q : MachineState → Prop) :
    Triple
      (framePrepCall body C₁ callerBody₁ func₁ argOps₁ destination₁ targetBb₁
          unwind₁ >>= fun _ =>
        framePrepCall body C₂ callerBody₂ func₂ argOps₂ destination₂ targetBb₂
          unwind₂)
      (wpFramePrep C₁ callerBody₁ func₁ argOps₁ destination₁ targetBb₁ unwind₁
        fun s =>
          (wpFramePrep C₂ callerBody₂ func₂ argOps₂ destination₂ targetBb₂
            unwind₂ Q s).down)
      (framePost fun _ s' => Q s') :=
  Triple.bind _ _
    (wpFramePrep_triple_sound C₁ callerBody₁ func₁ argOps₁ destination₁
      targetBb₁ unwind₁ _)
    (fun _ =>
      (triple_framePrep_iff _ _ _).mpr fun s hs =>
        (triple_framePrep_iff _ _ _).mp
          (wpFramePrep_triple_sound C₂ callerBody₂ func₂ argOps₂ destination₂
            targetBb₂ unwind₂ Q) s hs)

/--
**Prefix sharing.** A shared prefix `pre` (for example a sequence of call
pipelines) that establishes `Mid` is verified once and discharges two
distinct suffix specifications `Post₁` and `Post₂` simultaneously: the
composed program satisfies the conjunction `Post₁ ∧ₚ Post₂`. The suffix
triples are combined by `Std.Do.Triple.and` (conjunctivity of the predicate
transformer, `PredTrans.conjunctive`) and the prefix is composed by
`Std.Do.Triple.bind`.
-/
theorem wpFramePrep_duplicate_prefix {α β : Type} (pre : FramePrepM α)
    (suffix : α → FramePrepM β) {P : Assertion FramePrepShape}
    {Mid : α → Assertion FramePrepShape}
    {Post₁ Post₂ : PostCond β FramePrepShape}
    (hPre : Triple pre P (Mid, (Post₁ ∧ₚ Post₂).2))
    (h₁ : ∀ a, Triple (suffix a) (Mid a) Post₁)
    (h₂ : ∀ a, Triple (suffix a) (Mid a) Post₂) :
    Triple (pre >>= suffix) P (Post₁ ∧ₚ Post₂) :=
  Triple.bind pre suffix hPre fun a =>
    (triple_framePrep_iff _ _ _).mpr fun s hs =>
      (triple_framePrep_iff _ _ _).mp (Triple.and (suffix a) (h₁ a) (h₂ a)) s
        ⟨hs, hs⟩

/--
**Prefix sharing for total-correctness postconditions.** With
total-correctness postconditions `framePost Q₁` and `framePost Q₂`, the
shared prefix yields the single postcondition `Q₁ ∧ Q₂`.
-/
theorem wpFramePrep_duplicate_prefix_post {α β : Type} (pre : FramePrepM α)
    (suffix : α → FramePrepM β) {P : Assertion FramePrepShape}
    {Mid : α → MachineState → Prop} {Q₁ Q₂ : β → MachineState → Prop}
    (hPre : Triple pre P (framePost Mid))
    (h₁ : ∀ a, Triple (suffix a) (fun s => ⌜Mid a s⌝) (framePost Q₁))
    (h₂ : ∀ a, Triple (suffix a) (fun s => ⌜Mid a s⌝) (framePost Q₂)) :
    Triple (pre >>= suffix) P (framePost fun b s => Q₁ b s ∧ Q₂ b s) := by
  rw [triple_framePrep_iff]
  intro s hs
  obtain ⟨a, s₁, hx, hmid⟩ :=
    (wp_framePost_iff _ _ _).mp ((triple_framePrep_iff _ _ _).mp hPre s hs)
  obtain ⟨b, s', hf, hq₁⟩ :=
    (wp_framePost_iff _ _ _).mp ((triple_framePrep_iff _ _ _).mp (h₁ a) s₁ hmid)
  obtain ⟨b', s'', hf', hq₂⟩ :=
    (wp_framePost_iff _ _ _).mp ((triple_framePrep_iff _ _ _).mp (h₂ a) s₁ hmid)
  rw [hf] at hf'
  cases hf'
  exact (wp_framePost_iff _ _ _).mpr
    ⟨b, s', (run_bind_ok hx).trans hf, hq₁, hq₂⟩

/--
**Prefix sharing against the trusted machine.** One call verified once by
`wpFramePrep` for the mid-condition `Mid` discharges two continuations at the
call's target block with distinct postconditions `post₁` and `post₂`
simultaneously: the caller frame is lifted for their conjunction
(`LiftFrame` multi-continuation composition, `LiftState.and`).
-/
theorem wpFramePrep_duplicate_prefix_liftFrame {body cur : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv} {mem : Memory}
    {blk : BasicBlockData} {post₁ post₂ : Value → Prop} {fuel : Nat}
    (C : FramePrepContract body) {func : Operand} {argOps : List Operand}
    {destination : Place} {targetBb : BasicBlockIdx} {unwind : UnwindAction}
    {Mid : MachineState → Prop} (n : Nat)
    (hCur : mem.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks bbIdx = some blk)
    (hEnd : stmtIdx = length blk.statements)
    (hTerm : blk.terminator.kind =
      .call func argOps destination (some targetBb) unwind)
    (hSteps : ∀ s₁, C.Pre s₁ → C.steps s₁ ≤ n)
    (hWp : (wpFramePrep C cur func argOps destination targetBb unwind Mid
      (PureState.toMachineState
        { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)).down)
    (hCont₁ : ∀ (env' : PureEnv) (mem' : Memory),
      Mid (PureState.toMachineState
        { bb := targetBb, stmtIdx := 0, env := env' } mem') →
      LiftFrame body targetBb 0 env' mem' post₁ fuel)
    (hCont₂ : ∀ (env' : PureEnv) (mem' : Memory),
      Mid (PureState.toMachineState
        { bb := targetBb, stmtIdx := 0, env := env' } mem') →
      LiftFrame body targetBb 0 env' mem' post₂ fuel) :
    LiftFrame body bbIdx stmtIdx env mem (fun v => post₁ v ∧ post₂ v)
      (fuel + n + 2) :=
  wpFramePrep_sound_stepMirFn C n hCur hPhase hBb hEnd hTerm hSteps hWp
    fun env' mem' hMid =>
      liftState_iff_liftFrame.mp
        (LiftState.and
          (liftState_iff_liftFrame.mpr (hCont₁ env' mem' hMid))
          (liftState_iff_liftFrame.mpr (hCont₂ env' mem' hMid)))

/-! ### 2.8 Empty functions -/

/-- The unit type `()`, at layout index `0` of `emptyFnLayouts`. -/
def emptyFnUnitTy : Ty := { kind := .tuple [], layoutIdx := 0 }

/-- Layout of the zero-sized unit type. -/
def emptyFnUnitLayout : TypeLayout :=
  { size := { bytes := 0 }
    align := { bytes := 1 }
    backendRepr := .memory
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

/-- Layout table of the empty-function witnesses. -/
def emptyFnLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [emptyFnUnitLayout] }

/--
The empty function `fn f() {}` in `Runtime(PostCleanup)` MIR, where the unit
return place is assigned explicitly: `bb0: { _0 = const (); return; }`.
-/
def emptyFnAssignUnit : CapturedMir where
  defPath := "Anneal::TreeBorrowsPruningAndFrameWp::empty_fn_assign_unit"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls :=
    [{ mutability := .mut, ty := emptyFnUnitTy, debugName := some "_0" }]
  basicBlocks := [
    { statements := [
        { kind := .assign { local_ := 0, projection := [] }
            (.use (.constant { ty := emptyFnUnitTy, val := .zeroSized }))
          span := "unit" }]
      terminator := { kind := .return_, span := "ret" }
      isCleanup := false }]
  fnAbi := {
    args := []
    ret := { layout := emptyFnUnitLayout, mode := .direct }
    conv := .rust
    canUnwind := false }
  layouts := emptyFnLayouts
  allocations := []

/--
The empty function with a direct return and no assignment of the unit return
place: `bb0: { return; }` (the shape left by zero-sized-assignment removal).
The trusted machine initializes `_0` to `.uninit` at call entry and its
`return_` requires an initialized `_0`, so a call to this body is undefined
behavior in the trusted semantics (`emptyFnDirect_entry_ub`).
-/
def emptyFnDirect : CapturedMir where
  defPath := "Anneal::TreeBorrowsPruningAndFrameWp::empty_fn_direct"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls :=
    [{ mutability := .mut, ty := emptyFnUnitTy, debugName := some "_0" }]
  basicBlocks := [
    { statements := []
      terminator := { kind := .return_, span := "ret" }
      isCleanup := false }]
  fnAbi := {
    args := []
    ret := { layout := emptyFnUnitLayout, mode := .direct }
    conv := .rust
    canUnwind := false }
  layouts := emptyFnLayouts
  allocations := []

/--
Entry state of an inline call to `emptyFnAssignUnit` with no active
protector: the callee is active at the start of `bb0` with its single local
`_0` uninitialized.
-/
def EmptyFnEntry (s₀ : MachineState) : Prop :=
  s₀.memory.activeCallee = some emptyFnAssignUnit ∧
  s₀.frame = { blockIdx := 0, stmtIdx := 0, locals := [.uninit] } ∧
  s₀.memory.activeProtectors = []

/--
Return-ready state of `emptyFnAssignUnit` reached from the entry state `s₀`:
`_0` holds `.unit`, and the direct write to `_0` has been applied to the
borrow table by the trusted `invalidateConflictingBorrows`.
-/
def emptyFnReturnState (s₀ : MachineState) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 1, locals := [.init .unit] }
    memory :=
      { s₀.memory with
        borrows :=
          invalidateConflictingBorrows s₀.memory.borrows 0 .none
            (length s₀.memory.callStack) } }

/-- A call entry into `emptyFnAssignUnit` from a protector-free state is an
`EmptyFnEntry`. -/
theorem emptyFnEntry_of_pushCalleeFrame (s : MachineState)
    (callerBody : CapturedMir) (localsAfterArgs : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (argVals : List Value)
    (unwind : UnwindAction) (hProt : s.memory.activeProtectors = []) :
    EmptyFnEntry
      (pushCalleeFrame s callerBody localsAfterArgs destination targetBb
        emptyFnAssignUnit argVals unwind) :=
  ⟨rfl, rfl, hProt⟩

/--
The body of `emptyFnAssignUnit` is one trusted step: from an entry state the
trusted `stepMirFn` executes `_0 = const ()` and reaches the return-ready
state.
-/
theorem emptyFn_step {body : CapturedMir} {s₀ : MachineState}
    (h : EmptyFnEntry s₀) :
    stepMirFn body s₀ = MirStepNode.step (emptyFnReturnState s₀) := by
  obtain ⟨hCallee, hFrame, hProt⟩ := h
  cases s₀ with
  | mk frame memory =>
    have hFrame' :
        frame = { blockIdx := 0, stmtIdx := 0, locals := [.uninit] } := hFrame
    have hCallee' : memory.activeCallee = some emptyFnAssignUnit := hCallee
    have hProt' : memory.activeProtectors = [] := hProt
    rw [hFrame']
    have hCur : memory.activeCallee.getD body = emptyFnAssignUnit := by
      rw [hCallee']
      rfl
    have hStmt :=
      stepMirFn_frame_stmt (body := body) (cur := emptyFnAssignUnit)
        (s := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }
                memory := memory })
        (blk :=
          { statements := [
              { kind := .assign { local_ := 0, projection := [] }
                  (.use (.constant { ty := emptyFnUnitTy, val := .zeroSized }))
                span := "unit" }]
            terminator := { kind := .return_, span := "ret" }
            isCleanup := false })
        (stmt :=
          { kind := .assign { local_ := 0, projection := [] }
              (.use (.constant { ty := emptyFnUnitTy, val := .zeroSized }))
            span := "unit" })
        hCur (Or.inl rfl) rfl rfl
    rw [hStmt]
    exact evalStmt_assign_of_evalRvalue (bbIdx := 0) (stmtIdx := 0)
      (env := [.uninit]) (env₁ := [.uninit]) (env₂ := [.init .unit])
      (mem := memory) (mem₁ := memory) (val := .unit)
      (borrows' :=
        invalidateConflictingBorrows memory.borrows 0 .none
          (length memory.callStack))
      rfl hProt' rfl

/-- With no active protector, deallocating a frame conflicts with nothing. -/
theorem hasFrameDeallocProtectorConflict_nil_protectors
    (borrows : List BorrowEntry) (depth nLocals : Nat) :
    hasFrameDeallocProtectorConflict borrows [] depth nLocals = false := by
  cases borrows <;> rfl

/-- The state reached by the body of `emptyFnAssignUnit` is ready to return
`.unit`. -/
theorem emptyFn_returnReady {body : CapturedMir} {s₀ : MachineState}
    (h : EmptyFnEntry s₀) : ReturnReady body (emptyFnReturnState s₀) .unit := by
  obtain ⟨hCallee, _, hProt⟩ := h
  refine ⟨emptyFnAssignUnit, _, ?_, Or.inl rfl, rfl, rfl, rfl, rfl, ?_⟩
  · show s₀.memory.activeCallee.getD body = emptyFnAssignUnit
    rw [hCallee]
    rfl
  · show hasFrameDeallocProtectorConflict _ s₀.memory.activeProtectors _ _ =
      false
    rw [hProt]
    exact hasFrameDeallocProtectorConflict_nil_protectors _ _ _

/--
**Contract of the empty function, discharged once and for all.** From every
protector-free entry state, `emptyFnAssignUnit` takes exactly one trusted
step to the return-ready state `emptyFnReturnState`, returning `.unit` and
preserving the call stack.
-/
def emptyFnContract (body : CapturedMir) : FramePrepContract body where
  Pre := EmptyFnEntry
  Post := fun s₀ retVal sRet => retVal = .unit ∧ sRet = emptyFnReturnState s₀
  steps := fun _ => 1
  exec := fun s₀ h =>
    ⟨emptyFnReturnState s₀, .unit, StepsTo.single (emptyFn_step h),
      emptyFn_returnReady h, rfl, rfl, rfl⟩

/--
**`wpFramePrep` of the empty function, discharged once and for all.** Against
`emptyFnContract`, the weakest precondition of a call is exactly: call entry
succeeds into a protector-free entry state of `emptyFnAssignUnit`, and
teardown from the explicit return-ready state succeeds into `Q`. No reasoning
about the callee body remains.
-/
theorem wpFramePrep_emptyFn_iff (body callerBody : CapturedMir)
    (func : Operand) (argOps : List Operand) (destination : Place)
    (targetBb : BasicBlockIdx) (unwind : UnwindAction)
    (Q : MachineState → Prop) (s : MachineState) :
    (wpFramePrep (emptyFnContract body) callerBody func argOps destination
        targetBb unwind Q s).down ↔
      ∃ (call : PreparedCall) (s₁ : MachineState),
        (prepCallEntry callerBody func argOps destination targetBb unwind).run
          s = .ok call s₁ ∧
        EmptyFnEntry s₁ ∧
        ∃ s', prepTeardownAndWriteback.run (emptyFnReturnState s₁) = .ok () s' ∧
          Q s' := by
  rw [wpFramePrep_iff]
  constructor
  · intro ⟨call, s₁, hrun, hpre, hrest⟩
    exact ⟨call, s₁, hrun, hpre,
      hrest (emptyFnReturnState s₁) .unit ⟨rfl, rfl⟩ (emptyFn_returnReady hpre)
        rfl⟩
  · intro ⟨call, s₁, hrun, hpre, s', htd, hq⟩
    refine ⟨call, s₁, hrun, hpre, fun sRet retVal hpost _ _ => ?_⟩
    have hsRet : sRet = emptyFnReturnState s₁ := hpost.2
    rw [hsRet]
    exact ⟨s', htd, hq⟩

/--
**A call to an empty function reduces directly to `LiftFrame` at the target
block.** At a `TerminatorKind.call` terminator whose callee resolves to
`emptyFnAssignUnit`, in a protector-free memory, the caller frame is lifted
as soon as the continuation at `targetBb` is lifted in the state `s'`
produced by tearing down the callee's return-ready state. The callee body is
never unfolded: its contract `emptyFnContract` is discharged once and for
all. The whole call costs three trusted steps (entry, `_0 = const ()`, and
return).
-/
theorem wpFramePrep_empty_function {body cur : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv} {mem : Memory}
    {blk : BasicBlockData} {post : Value → Prop} {fuel : Nat} {func : Operand}
    {argOps : List Operand} {destination : Place} {targetBb : BasicBlockIdx}
    {unwind : UnwindAction} {call : PreparedCall} {s₁ s' : MachineState}
    (hCur : mem.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks bbIdx = some blk)
    (hEnd : stmtIdx = length blk.statements)
    (hTerm : blk.terminator.kind =
      .call func argOps destination (some targetBb) unwind)
    (hEntry :
      (prepCallEntry cur func argOps destination targetBb unwind).run
          (PureState.toMachineState
            { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem) =
        .ok call s₁)
    (hCallee : call.calleeBody = emptyFnAssignUnit)
    (hProt : mem.activeProtectors = [])
    (hTd : prepTeardownAndWriteback.run (emptyFnReturnState s₁) = .ok () s')
    (hCont : ∀ (env' : PureEnv) (mem' : Memory),
      s' = PureState.toMachineState
        { bb := targetBb, stmtIdx := 0, env := env' } mem' →
      LiftFrame body targetBb 0 env' mem' post fuel) :
    LiftFrame body bbIdx stmtIdx env mem post (fuel + 3) := by
  have hPre : EmptyFnEntry s₁ := by
    rw [(prepCallEntry_ok hEntry).1, hCallee]
    exact emptyFnEntry_of_pushCalleeFrame _ _ _ _ _ _ _ hProt
  have hWp :
      (wpFramePrep (emptyFnContract body) cur func argOps destination targetBb
        unwind (fun st => st = s')
        (PureState.toMachineState
          { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)).down :=
    (wpFramePrep_emptyFn_iff body cur func argOps destination targetBb unwind
      _ _).mpr ⟨call, s₁, hEntry, hPre, s', hTd, rfl⟩
  exact wpFramePrep_sound_stepMirFn (emptyFnContract body) 1 hCur hPhase hBb
    hEnd hTerm (fun _ _ => Nat.le_refl 1) hWp
    (fun env' mem' hQ => hCont env' mem' hQ.symm)

/--
**The direct-return empty function faults at entry.** With `_0`
uninitialized, the trusted `stepMirFn` at the `return_` terminator of
`emptyFnDirect` is undefined behavior (returning an uninitialized return
place).
-/
theorem emptyFnDirect_entry_ub {body : CapturedMir} {s₀ : MachineState}
    (hCallee : s₀.memory.activeCallee = some emptyFnDirect)
    (hFrame : s₀.frame = { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }) :
    stepMirFn body s₀ = MirStepNode.fail .ub := by
  cases s₀ with
  | mk frame memory =>
    have hFrame' :
        frame = { blockIdx := 0, stmtIdx := 0, locals := [.uninit] } := hFrame
    have hCallee' : memory.activeCallee = some emptyFnDirect := hCallee
    rw [hFrame']
    have hCur : memory.activeCallee.getD body = emptyFnDirect := by
      rw [hCallee']
      rfl
    rw [stepMirFn_at_terminator (cur := emptyFnDirect)
      (s := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }
              memory := memory })
      (blk :=
        { statements := []
          terminator := { kind := .return_, span := "ret" }
          isCleanup := false })
      hCur (Or.inl rfl) rfl rfl]
    rfl

/--
**No contract covers the direct-return empty function.** Because the trusted
machine faults at the entry of `emptyFnDirect`, the precondition of every
`FramePrepContract` is false at such an entry state: the direct-return shape
cannot be given a frame-prep contract, in contrast with `emptyFnAssignUnit`
(`emptyFnContract`).
-/
theorem emptyFnDirect_not_contract_pre {body : CapturedMir}
    (C : FramePrepContract body) {s₀ : MachineState}
    (hCallee : s₀.memory.activeCallee = some emptyFnDirect)
    (hFrame : s₀.frame = { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }) :
    ¬ C.Pre s₀ := by
  intro hPre
  obtain ⟨sRet, retVal, hsteps, hrr, _, _⟩ := C.exec s₀ hPre
  generalize C.steps s₀ = n at hsteps
  cases hsteps with
  | refl =>
    obtain ⟨_, _, _, _, _, _, _, hget, _⟩ := hrr
    rw [hFrame] at hget
    cases hget
  | step hstep _ =>
    rw [emptyFnDirect_entry_ub hCallee hFrame] at hstep
    unfold MirStepNode.fail MirStepNode.step at hstep
    cases hstep

/--
A call that resolves to the direct-return empty function satisfies no
`wpFramePrep`, for any contract and any continuation predicate.
-/
theorem wpFramePrep_empty_function_direct_ub {body : CapturedMir}
    (C : FramePrepContract body) (callerBody : CapturedMir) (func : Operand)
    (argOps : List Operand) (destination : Place) (targetBb : BasicBlockIdx)
    (unwind : UnwindAction) (Q : MachineState → Prop) (s : MachineState)
    (hCallee : ∀ (call : PreparedCall) (s₁ : MachineState),
      (prepCallEntry callerBody func argOps destination targetBb unwind).run s =
        .ok call s₁ → call.calleeBody = emptyFnDirect) :
    ¬ (wpFramePrep C callerBody func argOps destination targetBb unwind Q
      s).down := by
  intro h
  obtain ⟨call, s₁, hrun, hpre, _⟩ :=
    (wpFramePrep_iff C callerBody func argOps destination targetBb unwind Q
      s).mp h
  have hs₁ := (prepCallEntry_ok hrun).1
  rw [hCallee call s₁ hrun] at hs₁
  rw [hs₁] at hpre
  exact emptyFnDirect_not_contract_pre C rfl rfl hpre

/-- A normal return of the root frame discharges `LiftState`. -/
theorem LiftState.of_retNormal {body : CapturedMir} {s : MachineState}
    {post : Value → Prop} {fuel : Nat} {retVal : Value} {mem' : Memory}
    (h : stepMirFn body s = MirStepNode.retNormal retVal mem')
    (hv : post retVal) : LiftState body s post (fuel + 1) := by
  unfold LiftState wpMirExecSym
  rw [evalSymNodeTree_eq, stepMirExecSymTree_eval]
  show evalNodeWP _ _ (stepMirFn body s)
  rw [h]
  exact hv

/-! ### 2.9 Worked instance: calling the empty function on the trusted machine

A closed caller body that calls `emptyFnAssignUnit` and returns unit. The
instance shows that every hypothesis of `wpFramePrep_empty_function` is
satisfied by a real execution of the trusted machine: call entry, teardown,
and the continuation are all computed by the trusted semantics.
-/

/-- Function-item type of `emptyFnAssignUnit`. -/
def emptyFnItemTy : Ty :=
  { kind := .fnDef emptyFnAssignUnit.defPath [], layoutIdx := 0 }

/--
Caller of the empty function:
`bb0: { StorageLive(_1); _1 = empty_fn_assign_unit() -> bb1 }`,
`bb1: { _0 = const (); return; }`.
-/
def emptyFnCaller : CapturedMir where
  defPath := "Anneal::TreeBorrowsPruningAndFrameWp::empty_fn_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [
    { mutability := .mut, ty := emptyFnUnitTy, debugName := some "_0" },
    { mutability := .mut, ty := emptyFnUnitTy, debugName := some "_1" }]
  basicBlocks := [
    { statements := [{ kind := .storageLive 1, span := "live" }]
      terminator := {
        kind := .call (.constant { ty := emptyFnItemTy, val := .zeroSized }) []
          { local_ := 1, projection := [] } (some 1) .continue_
        span := "call" }
      isCleanup := false },
    { statements := [
        { kind := .assign { local_ := 0, projection := [] }
            (.use (.constant { ty := emptyFnUnitTy, val := .zeroSized }))
          span := "unit" }]
      terminator := { kind := .return_, span := "ret" }
      isCleanup := false }]
  fnAbi := {
    args := []
    ret := { layout := emptyFnUnitLayout, mode := .direct }
    conv := .rust
    canUnwind := false }
  layouts := emptyFnLayouts
  allocations := []

/-- Initial memory of `emptyFnCaller` linked against `emptyFnAssignUnit`. -/
def emptyFnCallerMem : Memory :=
  (initMachineStateWithCallees emptyFnCaller [] [emptyFnAssignUnit]).memory

/--
The teardown of the empty callee succeeds on the trusted machine, and the
caller's continuation at `bb1` returns `.unit` from the root frame.
-/
theorem emptyFnCaller_teardown_and_continuation :
    ∃ s' : MachineState,
      prepTeardownAndWriteback.run
          (emptyFnReturnState
            (pushCalleeFrame
              (PureState.toMachineState
                { bb := 0, stmtIdx := 1, env := [.uninit, .uninit] }
                emptyFnCallerMem)
              emptyFnCaller [.uninit, .uninit] { local_ := 1, projection := [] }
              1 emptyFnAssignUnit [] .continue_)) =
        .ok () s' ∧
      LiftState emptyFnCaller s' (fun v => v = .unit) 2 :=
  ⟨_, rfl, LiftState.of_step rfl (LiftState.of_retNormal rfl rfl)⟩

/--
**End-to-end instance of `wpFramePrep_empty_function`.** The caller of the
empty function is lifted from its initial state on the trusted machine: one
step for `StorageLive(_1)`, three steps for the call (by
`wpFramePrep_empty_function`, without unfolding the callee), and two steps
for the continuation.
-/
theorem emptyFnCaller_liftFrame :
    LiftFrame emptyFnCaller 0 0 [.uninit, .dead] emptyFnCallerMem
      (fun v => v = .unit) 6 := by
  obtain ⟨s', hTd, hLift⟩ := emptyFnCaller_teardown_and_continuation
  refine liftState_iff_liftFrame.mp
    (LiftState.of_step
      (s' := PureState.toMachineState
        { bb := 0, stmtIdx := 1, env := [.uninit, .uninit] } emptyFnCallerMem)
      rfl (liftState_iff_liftFrame.mpr ?_))
  exact wpFramePrep_empty_function (body := emptyFnCaller)
    (cur := emptyFnCaller)
    (blk :=
      { statements := [{ kind := .storageLive 1, span := "live" }]
        terminator := {
          kind :=
            .call (.constant { ty := emptyFnItemTy, val := .zeroSized }) []
              { local_ := 1, projection := [] } (some 1) .continue_
          span := "call" }
        isCleanup := false })
    (call := ⟨emptyFnAssignUnit, [], [.uninit, .uninit]⟩)
    rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl hTd
    (fun env' mem' h => liftState_iff_liftFrame.mp (h ▸ hLift))

/-- The initial frame of `emptyFnCaller` is the frame lifted by
`emptyFnCaller_liftFrame`. -/
theorem emptyFnCaller_initPureEnv :
    initPureEnv emptyFnCaller [] = [.uninit, .dead] := rfl

end FramePrep

end Anneal.TreeBorrowsPruningAndFrameWp
