/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Trusted.Rustc.V2026_06_01.MirSemantics.Machine
import Trusted.Rustc.V2026_08_01.MirAst.Rvalues
import Anneal.RefFrame.RangedTree
import MiniRustSpec.Interp

/-!
# `dyn Trait` Unsizing, VTable Dispatch & Dual Correspondence Prototype

**Track P (`PROTOTYPE_NO_MERGE`) spike** for the paired Tier 3 TCB workstream
`ws-tcb-dyn-trait-unsize-and-vtable-dispatch`. Nightly Differential Testing
Campaign #22 found `false_positive_ub` hits where Miri accepts
`&__vt_rec as &dyn __AnnealVtableTrait43543` while
`Trusted.Rustc.V2026_06_01.MirSemantics.evalUnsizeCoercion` only accepts slice
targets. This module prototypes, outside `trusted/`, the semantics the TCB
patch needs:

* **§1** Dialect-neutral existential trait predicates and vtable schema
  (`ProtoTraitPred`, `ProtoVTableSlot`, `ProtoVTableEntry`, `ProtoVTableTable`,
  decidable `wfProtoVTableTable`).
* **§2** Wide-pointer metadata (`ProtoWidePtrMeta`), lossless `Value` codec, and
  `V2026_06_01` / `V2026_08_01` lowering adapters with dialect invariance.
* **§3** `evalUnsizeDynProto` / `evalUnsizeCoercionProto`: a conservative
  extension of `evalUnsizeCoercion` (identical on every non-`dyn` target).
* **§4** `dynSizeOfValProto` / `dynAlignOfValProto`.
* **§5** `evalVirtualCallProto`: argument-initialization gate, vtable and slot
  resolution, receiver narrowing, callee ABI validation, and the Tree Borrows
  receiver protector (in `Memory.activeProtectors` and in
  `Anneal.RefFrame.RangedTree`).
* **§6** `evalWideAddrEqProto` (`core::ptr::addr_eq`) and `evalWidePtrEqProto`.
* **§7** `stepMirFnProto`: `stepMirFn` extended with the prototype rules.
* **§8** Correspondence with `MiniRustSpec.Interp` (`Mach` and `MachTB`).
* **§9** Parametric `lean-miri` authority contract (`LmDynAuthority`,
  `LmDynContract`), instantiated over vendored `Miri.Interpreter.*` by the
  cross-root bridge in `tests/mir/DynTraitUnsizeProtoTests.lean`.

Nothing here is a shadow evaluator for production: the production semantics
will live in `trusted/lean/Trusted/Rustc/{V2026_06_01,V2026_08_01}/`.
-/

namespace Anneal.Prototypes.DynTraitUnsizeProto

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## §1. Dialect-neutral existential trait predicates and vtable schema -/

/-- Associated-type binding `AssocName = TyKey` of an existential projection
predicate (`dyn Iterator<Item = u32>`). -/
structure ProtoAssocBinding : Type where
  assocName : String
  tyKey : String

/-- Existential predicate list of a `dyn` type, independent of any `rustc` MIR
dialect: the principal trait with its generic arguments, the projection
predicates, and the auto traits. `hasUnresolvedExistentialBinder` records an
associated-type binder the capture could not resolve (`charon#1640`);
`supertraitOutlivesOk` records whether the supertrait/projection outlives
obligations were discharged (`zerocopy:reference` `407e0bf7692a`). -/
structure ProtoTraitPred : Type where
  principalTrait? : Option String
  typeArgs : List String := []
  assocBindings : List ProtoAssocBinding := []
  autoTraits : List String := []
  hasUnresolvedExistentialBinder : Bool := false
  supertraitOutlivesOk : Bool := true

/-- Bytes of `s` as naturals (kernel-reducible, as `stringEq`). -/
def strBytes (s : String) : List Nat :=
  s.toByteArray.data.toList.map (fun b => b.toBitVec.toNat)

/-- Equality of natural-number lists. -/
def natListEq : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, b :: bs =>
    match Nat.beq a b with
    | true => natListEq as bs
    | false => false
  | _, _ => false

/-- Lexicographic `≤` on natural-number lists. -/
def natListLe : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    match Nat.blt a b with
    | true => true
    | false =>
      match Nat.blt b a with
      | true => false
      | false => natListLe as bs

/-- Equality of strings by their bytes. -/
def strEq (a b : String) : Bool := natListEq (strBytes a) (strBytes b)

/-- Length-prefixed bytes of a string, so that concatenated keys stay
injective. -/
def encStr (s : String) : List Nat := (strBytes s).length :: strBytes s

/-- Length-prefixed encoding of a list of strings. -/
def encStrs : List String → List Nat
  | [] => [0]
  | s :: rest => 1 :: (encStr s ++ encStrs rest)

/-- Stable key of the principal trait predicate `Trait<Args>`. -/
def traitPredKey (name : String) (args : List String) : List Nat :=
  0 :: (encStr name ++ encStrs args)

/-- Stable key of the projection predicate `Assoc = Ty`. -/
def projPredKey (b : ProtoAssocBinding) : List Nat :=
  1 :: (encStr b.assocName ++ encStr b.tyKey)

/-- Stable keys of the non-auto predicates, in source order. Auto traits are
dropped, as `Miri.Interpreter.VTable.sortedPredicates` filters `autoTrait`. -/
def ProtoTraitPred.nonAutoKeys (p : ProtoTraitPred) : List (List Nat) :=
  (match p.principalTrait? with
   | some t => [traitPredKey t p.typeArgs]
   | none => []) ++ p.assocBindings.map projPredKey

/-- Insert a key into a sorted key list. -/
def insertKey (k : List Nat) : List (List Nat) → List (List Nat)
  | [] => [k]
  | h :: t =>
    match natListLe k h with
    | true => k :: h :: t
    | false => h :: insertKey k t

/-- Insertion sort of keys (`VTable.sortPredicates`). -/
def sortKeys : List (List Nat) → List (List Nat)
  | [] => []
  | h :: t => insertKey h (sortKeys t)

/-- Drop adjacent equal keys; on a sorted list this is `List.eraseDups`. -/
def dedupSorted : List (List Nat) → List (List Nat)
  | [] => []
  | a :: rest =>
    match rest with
    | [] => [a]
    | b :: _ =>
      match natListEq a b with
      | true => dedupSorted rest
      | false => a :: dedupSorted rest

/-- Canonical predicate list: non-auto predicates, sorted and deduplicated. -/
def ProtoTraitPred.canonical (p : ProtoTraitPred) : List (List Nat) :=
  dedupSorted (sortKeys p.nonAutoKeys)

/-- Equality of key lists. -/
def keysEq : List (List Nat) → List (List Nat) → Bool
  | [], [] => true
  | a :: as, b :: bs =>
    match natListEq a b with
    | true => keysEq as bs
    | false => false
  | _, _ => false

/-- Trait-object type equality as the vtable trait check sees it: equal
canonical non-auto predicate lists (`VTable.checkForTypeRead`). Auto traits,
predicate order, and duplicates do not matter. -/
def traitPredEq (a b : ProtoTraitPred) : Bool := keysEq a.canonical b.canonical

/-- Whether a predicate must fail closed: an unresolved existential binder or
undischarged supertrait outlives obligations. -/
def ProtoTraitPred.failsClosed (p : ProtoTraitPred) : Bool :=
  p.hasUnresolvedExistentialBinder || !p.supertraitOutlivesOk

theorem natListEq_refl : ∀ l : List Nat, natListEq l l = true
  | [] => rfl
  | a :: as => by
    show (match Nat.beq a a with | true => natListEq as as | false => false) = true
    rw [Nat.beq_refl]; exact natListEq_refl as

theorem natListEq_eq : ∀ {a b : List Nat}, natListEq a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: as, b :: bs, h => by
    have h' : (match Nat.beq a b with | true => natListEq as bs | false => false) = true := h
    cases hab : Nat.beq a b with
    | false => rw [hab] at h'; cases h'
    | true =>
      rw [hab] at h'
      rw [Nat.eq_of_beq_eq_true hab, natListEq_eq h']

theorem keysEq_refl : ∀ l : List (List Nat), keysEq l l = true
  | [] => rfl
  | a :: as => by
    show (match natListEq a a with | true => keysEq as as | false => false) = true
    rw [natListEq_refl]; exact keysEq_refl as

theorem keysEq_eq : ∀ {a b : List (List Nat)}, keysEq a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: as, b :: bs, h => by
    have h' : (match natListEq a b with | true => keysEq as bs | false => false) = true := h
    cases hab : natListEq a b with
    | false => rw [hab] at h'; cases h'
    | true =>
      rw [hab] at h'
      rw [natListEq_eq hab, keysEq_eq h']

theorem strEq_refl (s : String) : strEq s s = true := natListEq_refl _

/-- `traitPredEq` is reflexive. -/
theorem traitPredEq_refl (p : ProtoTraitPred) : traitPredEq p p = true := keysEq_refl _

/-- `traitPredEq` is symmetric. -/
theorem traitPredEq_symm {a b : ProtoTraitPred} (h : traitPredEq a b = true) :
    traitPredEq b a = true := by
  unfold traitPredEq at h ⊢
  rw [keysEq_eq h]; exact keysEq_refl _

/-- `s` occurs in `xs`. -/
def strMem (s : String) : List String → Bool
  | [] => false
  | x :: xs => strEq x s || strMem s xs

/-- Every auto trait in `dst` is already required by `src` (`dst ⊆ src`):
dropping auto traits on a `dyn` upcast is well typed; adding one is rejected by
`rustc`'s type checker, so such MIR is ill formed (the prototype fails closed
with `.unsupported`, never `.ub`: vendored Miri executes it without UB). -/
def autoTraitsSubset (dst src : List String) : Bool :=
  dst.all (fun a => strMem a src)

theorem natBlt_true_iff (a b : Nat) : Nat.blt a b = true ↔ a < b :=
  ⟨fun h => Nat.le_of_ble_eq_true h, fun h => Nat.ble_eq_true_of_le h⟩

theorem natListLe_refl : ∀ l : List Nat, natListLe l l = true
  | [] => rfl
  | a :: as => by
    show (match Nat.blt a a with
          | true => true
          | false => match Nat.blt a a with | true => false | false => natListLe as as) = true
    have hlt : Nat.blt a a = false := by
      cases h : Nat.blt a a with
      | false => rfl
      | true => exact absurd ((natBlt_true_iff a a).mp h) (Nat.lt_irrefl a)
    rw [hlt]
    exact natListLe_refl as

theorem natListLe_antisymm : ∀ {a b : List Nat},
    natListLe a b = true → natListLe b a = true → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, _, h2 => by cases h2
  | _ :: _, [], h1, _ => by cases h1
  | a :: as, b :: bs, h1, h2 => by
    have h1' : (match Nat.blt a b with
                | true => true
                | false => match Nat.blt b a with | true => false | false => natListLe as bs) = true := h1
    have h2' : (match Nat.blt b a with
                | true => true
                | false => match Nat.blt a b with | true => false | false => natListLe bs as) = true := h2
    cases hab : Nat.blt a b with
    | true =>
      have hba : Nat.blt b a = false := by
        cases h : Nat.blt b a with
        | false => rfl
        | true =>
          exact absurd (Nat.lt_trans ((natBlt_true_iff a b).mp hab) ((natBlt_true_iff b a).mp h))
            (Nat.lt_irrefl a)
      rw [hba, hab] at h2'
      cases h2'
    | false =>
      cases hba : Nat.blt b a with
      | true => rw [hab, hba] at h1'; cases h1'
      | false =>
        rw [hab, hba] at h1' h2'
        have heq : a = b := by
          have h1n : ¬ a < b := fun h => by
            have := (natBlt_true_iff a b).mpr h
            rw [this] at hab; cases hab
          have h2n : ¬ b < a := fun h => by
            have := (natBlt_true_iff b a).mpr h
            rw [this] at hba; cases hba
          omega
        rw [heq, natListLe_antisymm h1' h2']

theorem natListLe_total : ∀ {a b : List Nat}, natListLe a b = false → natListLe b a = true
  | [], _, h => by cases h
  | _ :: _, [], _ => rfl
  | a :: as, b :: bs, h => by
    have h' : (match Nat.blt a b with
               | true => true
               | false => match Nat.blt b a with | true => false | false => natListLe as bs) = false := h
    cases hab : Nat.blt a b with
    | true => rw [hab] at h'; cases h'
    | false =>
      cases hba : Nat.blt b a with
      | true =>
        show (match Nat.blt b a with
              | true => true
              | false => match Nat.blt a b with | true => false | false => natListLe bs as) = true
        rw [hba]
      | false =>
        rw [hab, hba] at h'
        show (match Nat.blt b a with
              | true => true
              | false => match Nat.blt a b with | true => false | false => natListLe bs as) = true
        rw [hba, hab]
        exact natListLe_total h'

theorem natListLe_trans : ∀ {a b c : List Nat},
    natListLe a b = true → natListLe b c = true → natListLe a c = true
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, h1, _ => by cases h1
  | _ :: _, _ :: _, [], _, h2 => by cases h2
  | a :: as, b :: bs, c :: cs, h1, h2 => by
    have h1' : (match Nat.blt a b with
                | true => true
                | false => match Nat.blt b a with | true => false | false => natListLe as bs) = true := h1
    have h2' : (match Nat.blt b c with
                | true => true
                | false => match Nat.blt c b with | true => false | false => natListLe bs cs) = true := h2
    show (match Nat.blt a c with
          | true => true
          | false => match Nat.blt c a with | true => false | false => natListLe as cs) = true
    cases hab : Nat.blt a b with
    | true =>
      cases hbc : Nat.blt b c with
      | true =>
        have hac : Nat.blt a c = true :=
          (natBlt_true_iff a c).mpr
            (Nat.lt_trans ((natBlt_true_iff a b).mp hab) ((natBlt_true_iff b c).mp hbc))
        rw [hac]
      | false =>
        cases hcb : Nat.blt c b with
        | true => rw [hbc, hcb] at h2'; cases h2'
        | false =>
          have hbcEq : b = c := by
            have hn1 : ¬ b < c := fun h => by
              have := (natBlt_true_iff b c).mpr h; rw [this] at hbc; cases hbc
            have hn2 : ¬ c < b := fun h => by
              have := (natBlt_true_iff c b).mpr h; rw [this] at hcb; cases hcb
            omega
          rw [← hbcEq, hab]
    | false =>
      cases hba : Nat.blt b a with
      | true => rw [hab, hba] at h1'; cases h1'
      | false =>
        rw [hab, hba] at h1'
        have habEq : a = b := by
          have hn1 : ¬ a < b := fun h => by
            have := (natBlt_true_iff a b).mpr h; rw [this] at hab; cases hab
          have hn2 : ¬ b < a := fun h => by
            have := (natBlt_true_iff b a).mpr h; rw [this] at hba; cases hba
          omega
        subst habEq
        cases hbc : Nat.blt a c with
        | true => rfl
        | false =>
          cases hcb : Nat.blt c a with
          | true => rw [hbc, hcb] at h2'; cases h2'
          | false =>
            rw [hbc, hcb] at h2'
            exact natListLe_trans h1' h2'

theorem insertKey_comm (x y : List Nat) :
    ∀ l : List (List Nat), insertKey x (insertKey y l) = insertKey y (insertKey x l)
  | [] => by
    simp only [insertKey]
    cases hxy : natListLe x y with
    | true =>
      cases hyx : natListLe y x with
      | true => rw [natListLe_antisymm hxy hyx]
      | false => rfl
    | false =>
      rw [natListLe_total hxy]
  | h :: t => by
    simp only [insertKey]
    cases hxh : natListLe x h with
    | true =>
      cases hyh : natListLe y h with
      | true =>
        simp only [insertKey]
        cases hxy : natListLe x y with
        | true =>
          cases hyx : natListLe y x with
          | true => rw [natListLe_antisymm hxy hyx]
          | false => simp only [hyh]
        | false =>
          rw [natListLe_total hxy]; simp only [hxh]
      | false =>
        have hhy : natListLe h y = true := natListLe_total hyh
        have hxy : natListLe x y = true := natListLe_trans hxh hhy
        have hyx : natListLe y x = false := by
          cases hyx' : natListLe y x with
          | false => rfl
          | true =>
            have : natListLe y h = true := natListLe_trans hyx' hxh
            rw [this] at hyh; cases hyh
        simp only [insertKey, hxh, hyh, hyx]
    | false =>
      cases hyh : natListLe y h with
      | true =>
        have hhx : natListLe h x = true := natListLe_total hxh
        have hxy : natListLe x y = false := by
          cases hxy' : natListLe x y with
          | false => rfl
          | true =>
            have : natListLe x h = true := natListLe_trans hxy' hyh
            rw [this] at hxh; cases hxh
        simp only [insertKey, hxh, hyh, hxy]
      | false =>
        simp only [insertKey, hxh, hyh, insertKey_comm x y t]

theorem dedupSorted_cons_same (x : List Nat) (t : List (List Nat)) :
    dedupSorted (x :: x :: t) = dedupSorted (x :: t) := by
  show (match natListEq x x with | true => dedupSorted (x :: t) | false => x :: dedupSorted (x :: t)) =
    dedupSorted (x :: t)
  rw [natListEq_refl]

theorem dedupSorted_insertKey_dup (x : List Nat) :
    ∀ l : List (List Nat), dedupSorted (insertKey x (insertKey x l)) = dedupSorted (insertKey x l)
  | [] => by
    simp only [insertKey, natListLe_refl]
    exact dedupSorted_cons_same x []
  | h :: t => by
    simp only [insertKey]
    cases hxh : natListLe x h with
    | true =>
      simp only [insertKey, natListLe_refl]
      exact dedupSorted_cons_same x (h :: t)
    | false =>
      simp only [insertKey, hxh]
      have hne : natListEq h x = false := by
        cases heq : natListEq h x with
        | false => rfl
        | true =>
          rw [natListEq_eq heq, natListLe_refl] at hxh
          cases hxh
      cases t with
      | nil =>
        simp only [insertKey, natListLe_refl]
        show (match natListEq h x with | true => dedupSorted [x, x] | false => h :: dedupSorted [x, x]) =
          (match natListEq h x with | true => dedupSorted [x] | false => h :: dedupSorted [x])
        rw [hne, dedupSorted_cons_same x []]
      | cons h' t' =>
        simp only [insertKey]
        cases hxh' : natListLe x h' with
        | true =>
          simp only [insertKey, natListLe_refl]
          show (match natListEq h x with
                | true => dedupSorted (x :: x :: h' :: t')
                | false => h :: dedupSorted (x :: x :: h' :: t')) =
            (match natListEq h x with
             | true => dedupSorted (x :: h' :: t')
             | false => h :: dedupSorted (x :: h' :: t'))
          rw [hne, dedupSorted_cons_same x (h' :: t')]
        | false =>
          simp only [insertKey, hxh']
          show (match natListEq h h' with
                | true => dedupSorted (h' :: insertKey x (insertKey x t'))
                | false => h :: dedupSorted (h' :: insertKey x (insertKey x t'))) =
            (match natListEq h h' with
             | true => dedupSorted (h' :: insertKey x t')
             | false => h :: dedupSorted (h' :: insertKey x t'))
          have ih := dedupSorted_insertKey_dup x (h' :: t')
          simp only [insertKey, hxh'] at ih
          rw [ih]

theorem sortKeys_append_swap (pre suf : List (List Nat)) (a b : List Nat) :
    sortKeys (pre ++ a :: b :: suf) = sortKeys (pre ++ b :: a :: suf) := by
  induction pre with
  | nil => exact insertKey_comm a b (sortKeys suf)
  | cons p ps ih =>
    simp only [List.cons_append, sortKeys]
    rw [ih]

theorem dedupSorted_sortKeys_append_dup (pre suf : List (List Nat)) (a : List Nat) :
    dedupSorted (sortKeys (pre ++ a :: a :: suf)) = dedupSorted (sortKeys (pre ++ a :: suf)) := by
  induction pre with
  | nil => exact dedupSorted_insertKey_dup a (sortKeys suf)
  | cons p ps ih =>
    simp only [List.cons_append, sortKeys]
    have hcomm : ∀ x l, insertKey p (insertKey x l) = insertKey x (insertKey p l) :=
      fun x l => insertKey_comm p x l
    -- Move `p` inside the two copies of `a` by rewriting the suffix? No, recurse on `pre` via `insertKey_comm`!
    -- Even simpler: prove `dedupSorted (insertKey p (insertKey a (insertKey a l))) = dedupSorted (insertKey p (insertKey a l))`.
    have hmove : ∀ l : List (List Nat),
        sortKeys (ps ++ a :: a :: suf) = insertKey a (insertKey a (sortKeys (ps ++ suf))) ∧
        sortKeys (ps ++ a :: suf) = insertKey a (sortKeys (ps ++ suf)) := by
      intro _
      clear ih
      induction ps with
      | nil => exact ⟨rfl, rfl⟩
      | cons q qs ih2 =>
        simp only [List.cons_append, sortKeys, ih2.1, ih2.2]
        exact ⟨by rw [insertKey_comm q a, insertKey_comm q a], insertKey_comm q a _⟩
    have hm := hmove []
    rw [hm.1, hm.2, insertKey_comm p a, insertKey_comm p a]
    exact dedupSorted_insertKey_dup a (insertKey p (sortKeys (ps ++ suf)))

/-- `traitPredEq` is transitive. -/
theorem traitPredEq_trans {a b c : ProtoTraitPred} (h₁ : traitPredEq a b = true)
    (h₂ : traitPredEq b c = true) : traitPredEq a c = true := by
  unfold traitPredEq at h₁ h₂ ⊢
  rw [keysEq_eq h₁]; exact h₂

/-- The trait check ignores auto traits and the fail-closed flags: two
predicates that differ only there are equal. -/
theorem traitPredEq_ignores_autoTraits_and_flags (p : ProtoTraitPred) (autos : List String)
    (unresolved outlives : Bool) :
    traitPredEq
      { p with autoTraits := autos, hasUnresolvedExistentialBinder := unresolved,
               supertraitOutlivesOk := outlives } p = true :=
  traitPredEq_refl p

/-- **Associated-type order invariance (`VTable.sortedPredicates`).** Swapping
any two adjacent associated-type bindings preserves canonical equality. -/
theorem traitPredEq_assocBindings_swap (p : ProtoTraitPred)
    (pre suf : List ProtoAssocBinding) (a b : ProtoAssocBinding) :
    traitPredEq
      { p with assocBindings := pre ++ a :: b :: suf }
      { p with assocBindings := pre ++ b :: a :: suf } = true := by
  unfold traitPredEq ProtoTraitPred.canonical ProtoTraitPred.nonAutoKeys
  dsimp only
  simp only [List.map_append, List.map_cons, ← List.append_assoc]
  rw [sortKeys_append_swap]
  exact keysEq_refl _

/-- **Associated-type deduplication (`VTable.sortedPredicates`).** Duplicating
an associated-type binding preserves canonical equality. -/
theorem traitPredEq_assocBindings_dup (p : ProtoTraitPred)
    (pre suf : List ProtoAssocBinding) (a : ProtoAssocBinding) :
    traitPredEq
      { p with assocBindings := pre ++ a :: a :: suf }
      { p with assocBindings := pre ++ a :: suf } = true := by
  unfold traitPredEq ProtoTraitPred.canonical ProtoTraitPred.nonAutoKeys
  dsimp only
  simp only [List.map_append, List.map_cons, ← List.append_assoc]
  rw [dedupSorted_sortKeys_append_dup]
  exact keysEq_refl _

/-- One entry of a vtable, as `rustc`'s `VtblEntry` and
`Miri.Interpreter.VTableEntry`. -/
inductive ProtoVTableSlot : Type where
  /-- `drop_in_place` glue (`none` when the type needs no drop). -/
  | dropInPlace (dropFn? : Option String)
  | size
  | align
  | vacant
  /-- Concrete monomorphized implementation `DefPath`. -/
  | method (defPath : String)
  /-- Pointer to the vtable of a supertrait, for `dyn Sub -> dyn Super`. -/
  | traitVPtr (superVTableId : Nat)

/-- Slot equality, used for prefix-compatible primary supertrait validation. -/
def slotEq : ProtoVTableSlot → ProtoVTableSlot → Bool
  | .dropInPlace a, .dropInPlace b =>
    (match a, b with
     | some x, some y => strEq x y
     | none, none => true
     | _, _ => false)
  | .size, .size => true
  | .align, .align => true
  | .vacant, .vacant => true
  | .method a, .method b => strEq a b
  | .traitVPtr a, .traitVPtr b => Nat.beq a b
  | _, _ => false

/-- `pre` is a slot-wise prefix of `full`. -/
def slotsPrefix : List ProtoVTableSlot → List ProtoVTableSlot → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => slotEq a b && slotsPrefix as bs

/-- Captured vtable of `concreteTyKey` for the trait object type `traitPred`.
`primarySuperVTable?` optionally records the `vtableId` of the primary (prefix)
supertrait vtable for `dyn Sub -> dyn Super` upcasts without a `.traitVPtr` slot. -/
structure ProtoVTableEntry : Type where
  vtableId : Nat
  vtableAllocId : Nat
  concreteTyKey : String
  traitPred : ProtoTraitPred
  sizeBytes : Nat
  alignBytes : Nat
  isUninhabited : Bool := false
  slots : List ProtoVTableSlot
  primarySuperVTable? : Option Nat := none

/-- Captured vtables of a compilation unit, with the side table mapping the
dialect's `RigidTy.dynamic` key to the full existential predicate list. -/
structure ProtoVTableTable : Type where
  entries : List ProtoVTableEntry
  dynTypes : List (String × ProtoTraitPred) := []

/-- Vtable with identifier `vid`. -/
def lookupVTableById : List ProtoVTableEntry → Nat → Option ProtoVTableEntry
  | [], _ => none
  | e :: rest, vid =>
    match Nat.beq e.vtableId vid with
    | true => some e
    | false => lookupVTableById rest vid

/-- Vtable stored in allocation `allocId`. -/
def lookupVTableByAlloc : List ProtoVTableEntry → Nat → Option ProtoVTableEntry
  | [], _ => none
  | e :: rest, allocId =>
    match Nat.beq e.vtableAllocId allocId with
    | true => some e
    | false => lookupVTableByAlloc rest allocId

/-- Vtable of the concrete type `tyKey` for the trait object type `pred`. -/
def findVTableFor : List ProtoVTableEntry → String → ProtoTraitPred → Option ProtoVTableEntry
  | [], _, _ => none
  | e :: rest, tyKey, pred =>
    match strEq e.concreteTyKey tyKey && traitPredEq e.traitPred pred with
    | true => some e
    | false => findVTableFor rest tyKey pred

/-- Existential predicate list registered for the dialect key `key`. -/
def lookupDynPred : List (String × ProtoTraitPred) → String → Option ProtoTraitPred
  | [], _ => none
  | (k, p) :: rest, key =>
    match strEq k key with
    | true => some p
    | false => lookupDynPred rest key

/-- `n` is a positive power of two (`n &&& (n - 1) == 0`). -/
def isPow2 (n : Nat) : Bool := Nat.blt 0 n && Nat.beq (n &&& (n - 1)) 0

/-- The canonical header `[drop_in_place, size, align]` starts the vtable. -/
def slotsHeaderOk : List ProtoVTableSlot → Bool
  | .dropInPlace _ :: .size :: .align :: _ => true
  | _ => false

/-- Two entries describe the same concrete type with identical layout metadata. -/
def sameConcreteLayout (s e : ProtoVTableEntry) : Bool :=
  strEq s.concreteTyKey e.concreteTyKey && Nat.beq s.sizeBytes e.sizeBytes &&
    Nat.beq s.alignBytes e.alignBytes && (s.isUninhabited == e.isUninhabited)

/-- A slot after the header: a method, a vacant slot, or a non-self supertrait
vtable pointer to a vtable of the same concrete type and layout for a distinct
supertrait predicate. -/
def bodySlotOk (es : List ProtoVTableEntry) (e : ProtoVTableEntry) : ProtoVTableSlot → Bool
  | .method _ => true
  | .vacant => true
  | .traitVPtr sup =>
    !Nat.beq sup e.vtableId &&
      (match lookupVTableById es sup with
       | some s => sameConcreteLayout s e && !traitPredEq s.traitPred e.traitPred
       | none => false)
  | _ => false

/-- Every slot after the header is well formed. -/
def bodySlotsOk (es : List ProtoVTableEntry) (e : ProtoVTableEntry) : List ProtoVTableSlot → Bool
  | [] => true
  | s :: rest => bodySlotOk es e s && bodySlotsOk es e rest

/-- Well-formedness of an optional primary (prefix) supertrait vtable link:
must point to a distinct entry of the same concrete type and layout whose slots
are a prefix of `e.slots`. -/
def primarySuperOk (es : List ProtoVTableEntry) (e : ProtoVTableEntry) : Bool :=
  match e.primarySuperVTable? with
  | none => true
  | some sup =>
    !Nat.beq sup e.vtableId &&
      (match lookupVTableById es sup with
       | some s =>
         sameConcreteLayout s e && !traitPredEq s.traitPred e.traitPred &&
           slotsPrefix s.slots e.slots
       | none => false)

/-- Layout metadata of a vtable entry is valid for a `ptrBytes` target:
`ptrBytes > 0`, `align` is a power of two strictly below `signedHalfModulus ptrBytes`,
`size` is a multiple of `align`, and `size + (align - 1) <= isize::MAX` (Rust
`Layout::from_size_align` invariant; prevents `size = 0, align = 2^100` overflow). -/
def entryLayoutOk (ptrBytes : Nat) (e : ProtoVTableEntry) : Bool :=
  let half := signedHalfModulus ptrBytes
  Nat.blt 0 ptrBytes && isPow2 e.alignBytes && Nat.blt e.alignBytes half &&
    Nat.blt e.sizeBytes half && Nat.blt (e.sizeBytes + (e.alignBytes - 1)) half &&
    Nat.beq (e.sizeBytes % e.alignBytes) 0

/-- Well-formedness of one vtable entry inside the table `es`. -/
def wfProtoVTableEntry (ptrBytes : Nat) (es : List ProtoVTableEntry) (e : ProtoVTableEntry) :
    Bool :=
  entryLayoutOk ptrBytes e && !Nat.beq e.vtableAllocId 0 && slotsHeaderOk e.slots &&
    bodySlotsOk es e (e.slots.drop 3) && primarySuperOk es e

/-- `x` does not occur in `xs`. -/
def natNotIn (x : Nat) : List Nat → Bool
  | [] => true
  | y :: ys => !Nat.beq x y && natNotIn x ys

/-- The naturals in the list are pairwise distinct. -/
def natsUnique : List Nat → Bool
  | [] => true
  | x :: xs => natNotIn x xs && natsUnique xs

/-- Pairwise table consistency: two distinct entries for the same concrete type
must agree on `(sizeBytes, alignBytes, isUninhabited)` and must not duplicate
the same canonical trait predicate. -/
def entryConsistentWith (e : ProtoVTableEntry) : List ProtoVTableEntry → Bool
  | [] => true
  | x :: rest =>
    (match strEq e.concreteTyKey x.concreteTyKey with
     | false => true
     | true => sameConcreteLayout e x && !traitPredEq e.traitPred x.traitPred) &&
      entryConsistentWith e rest

/-- Every pair of distinct entries in `es` is layout-consistent and has distinct
`(concreteTyKey, canonical traitPred)`. -/
def entriesPairwiseOk : List ProtoVTableEntry → Bool
  | [] => true
  | e :: rest => entryConsistentWith e rest && entriesPairwiseOk rest

/-- Every entry of `es'` is well formed inside `es`. -/
def allEntriesWf (ptrBytes : Nat) (es : List ProtoVTableEntry) : List ProtoVTableEntry → Bool
  | [] => true
  | e :: rest => wfProtoVTableEntry ptrBytes es e && allEntriesWf ptrBytes es rest

/-- Decidable well-formedness of a vtable table: every entry is well formed,
vtable identifiers and vtable allocation identifiers are unique, and entries
for the same concrete type agree on layout without duplicating predicates. -/
def wfProtoVTableTable (ptrBytes : Nat) (vt : ProtoVTableTable) : Bool :=
  allEntriesWf ptrBytes vt.entries vt.entries &&
    natsUnique (vt.entries.map (·.vtableId)) &&
    natsUnique (vt.entries.map (·.vtableAllocId)) &&
    entriesPairwiseOk vt.entries

/-- A vtable allocation identifier is disjoint from every allocation range of
`mem` at target pointer width `ptrBytes`: non-null, below `fnPtrAllocBase` and
`stackLocalAddrPageBase ptrBytes` (so its canonical page address `allocId * 65536`
cannot alias null, stack locals, or function pointers on 32-bit or 64-bit targets),
not a global/function/borrow entry, and at or above both `mem.nextAllocId` and
`mem.nextTag`. -/
def vtableAllocDisjoint (ptrBytes : Nat) (mem : Memory) (allocId : Nat) : Bool :=
  !Nat.beq allocId 0 &&
    Nat.blt allocId (stackLocalAddrPageBase ptrBytes) &&
    (match lookupGlobalAlloc mem.globals allocId with | some _ => false | none => true) &&
    (match lookupFnPtr mem.fnPtrs allocId with | some _ => false | none => true) &&
    !isFnPtrAllocId allocId &&
    (match lookupBorrow mem.borrows allocId with | some _ => false | none => true) &&
    Nat.ble mem.nextAllocId allocId &&
    Nat.ble mem.nextTag allocId

/-- Every vtable allocation of the table is disjoint from `mem` at width `ptrBytes`. -/
def vtablesDisjointFrom (ptrBytes : Nat) (mem : Memory) : List ProtoVTableEntry → Bool
  | [] => true
  | e :: rest => vtableAllocDisjoint ptrBytes mem e.vtableAllocId && vtablesDisjointFrom ptrBytes mem rest

/-- Environment gate of every prototype rule: the table is well formed for the
target pointer width and disjoint from the allocations of `mem`. A rule whose
gate fails reports `.unsupported`. -/
def vtableEnvOk (ptrBytes : Nat) (vt : ProtoVTableTable) (mem : Memory) : Bool :=
  wfProtoVTableTable ptrBytes vt && vtablesDisjointFrom ptrBytes mem vt.entries

theorem lookupVTableByAlloc_allocId :
    ∀ {es : List ProtoVTableEntry} {a : Nat} {e : ProtoVTableEntry},
      lookupVTableByAlloc es a = some e → e.vtableAllocId = a
  | [], _, _, h => by cases h
  | x :: rest, a, e, h => by
    have h' : (match Nat.beq x.vtableAllocId a with
               | true => some x
               | false => lookupVTableByAlloc rest a) = some e := h
    cases hx : Nat.beq x.vtableAllocId a with
    | true =>
      rw [hx] at h'
      cases h'
      exact Nat.eq_of_beq_eq_true hx
    | false =>
      rw [hx] at h'
      exact lookupVTableByAlloc_allocId h'

theorem findVTableFor_spec :
    ∀ {es : List ProtoVTableEntry} {k : String} {p : ProtoTraitPred} {e : ProtoVTableEntry},
      findVTableFor es k p = some e →
        strEq e.concreteTyKey k = true ∧ traitPredEq e.traitPred p = true
  | [], _, _, _, h => by cases h
  | x :: rest, k, p, e, h => by
    have h' : (match strEq x.concreteTyKey k && traitPredEq x.traitPred p with
               | true => some x
               | false => findVTableFor rest k p) = some e := h
    cases hx : (strEq x.concreteTyKey k && traitPredEq x.traitPred p) with
    | true =>
      rw [hx] at h'
      cases h'
      cases h1 : strEq x.concreteTyKey k with
      | false => rw [h1] at hx; cases hx
      | true => rw [h1] at hx; exact ⟨rfl, hx⟩
    | false =>
      rw [hx] at h'
      exact findVTableFor_spec h'

/-! ## §2. Wide-pointer metadata, `Value` codec, and dialect lowering -/

/-- Metadata of a pointer: none (thin), a slice length, or a vtable pointer. -/
inductive ProtoWidePtrMeta : Type where
  | thin
  | sliceLen (len : Nat)
  | vtable (vtPtr : ProvenancePtr)

/-- Data word of a pointer: a pointer with provenance, or the address of a
provenance-less raw pointer. -/
inductive ProtoDataWord : Type where
  | prov (p : ProvenancePtr)
  | addr (bits : Nat)

/-- Thin or wide pointer, independent of its `Value` encoding. -/
structure ProtoWidePtr : Type where
  data : ProtoDataWord
  ptrMeta : ProtoWidePtrMeta

/-- `Value` of a data word at pointer width `ptrBytes`. -/
def encodeDataWord (ptrBytes : Nat) : ProtoDataWord → Value
  | .prov p => .ptr p ptrBytes
  | .addr bits => .scalar ⟨bits, ptrBytes⟩

/-- `Trusted` `Value` of a pointer: `.ptr p ptrBytes` or `.scalar addr` when
thin, `.aggregate 0 [data, .scalar len]` for a slice pointer, and
`.aggregate 0 [data, .ptr vtPtr ptrBytes]` for a trait-object pointer. -/
def encodeWidePtr (ptrBytes : Nat) (w : ProtoWidePtr) : Value :=
  match w.ptrMeta with
  | .thin => encodeDataWord ptrBytes w.data
  | .sliceLen len => .aggregate 0 [encodeDataWord ptrBytes w.data, .scalar ⟨len, ptrBytes⟩]
  | .vtable vt => .aggregate 0 [encodeDataWord ptrBytes w.data, .ptr vt ptrBytes]

/-- Data word of a pointer-width `Value`. -/
def decodeDataWord? (ptrBytes : Nat) : Value → Option ProtoDataWord
  | .ptr p sz =>
    match Nat.beq sz ptrBytes with
    | true => some (.prov p)
    | false => none
  | .scalar sc =>
    match Nat.beq sc.sizeBytes ptrBytes with
    | true => some (.addr sc.bits)
    | false => none
  | _ => none

/-- Validated decoding of a pointer `Value`: every word must have width
`ptrBytes`, and a wide pointer is variant `0` with exactly two words. -/
def decodeWidePtr? (ptrBytes : Nat) : Value → Option ProtoWidePtr
  | .aggregate vIdx fields =>
    match Nat.beq vIdx 0, fields with
    | true, [d, .scalar m] =>
      match decodeDataWord? ptrBytes d, Nat.beq m.sizeBytes ptrBytes with
      | some dw, true => some ⟨dw, .sliceLen m.bits⟩
      | _, _ => none
    | true, [d, .ptr vt sz] =>
      match decodeDataWord? ptrBytes d, Nat.beq sz ptrBytes with
      | some dw, true => some ⟨dw, .vtable vt⟩
      | _, _ => none
    | _, _ => none
  | v =>
    match decodeDataWord? ptrBytes v with
    | some dw => some ⟨dw, .thin⟩
    | none => none

theorem decodeDataWord?_encodeDataWord (ptrBytes : Nat) (d : ProtoDataWord) :
    decodeDataWord? ptrBytes (encodeDataWord ptrBytes d) = some d := by
  cases d <;> simp [encodeDataWord, decodeDataWord?, Nat.beq_refl]

theorem encodeDataWord_of_decodeDataWord? {ptrBytes : Nat} {v : Value} {d : ProtoDataWord}
    (h : decodeDataWord? ptrBytes v = some d) : encodeDataWord ptrBytes d = v := by
  cases v with
  | ptr p sz =>
    simp only [decodeDataWord?] at h
    cases hsz : Nat.beq sz ptrBytes with
    | false => rw [hsz] at h; cases h
    | true =>
      rw [hsz] at h; cases h
      rw [← Nat.eq_of_beq_eq_true hsz]; rfl
  | scalar sc =>
    simp only [decodeDataWord?] at h
    cases hsz : Nat.beq sc.sizeBytes ptrBytes with
    | false => rw [hsz] at h; cases h
    | true =>
      rw [hsz] at h; cases h
      cases sc
      rw [← Nat.eq_of_beq_eq_true hsz]; rfl
  | unit => cases h
  | aggregate _ _ => cases h
  | uninit => cases h

/-- **Lossless codec (decode after encode).** -/
theorem decodeWidePtr?_encodeWidePtr (ptrBytes : Nat) (w : ProtoWidePtr) :
    decodeWidePtr? ptrBytes (encodeWidePtr ptrBytes w) = some w := by
  obtain ⟨d, m⟩ := w
  cases m with
  | thin => cases d <;> simp [encodeWidePtr, encodeDataWord, decodeWidePtr?, decodeDataWord?]
  | sliceLen len =>
    cases d <;> simp [encodeWidePtr, encodeDataWord, decodeWidePtr?, decodeDataWord?]
  | vtable vt =>
    cases d <;> simp [encodeWidePtr, encodeDataWord, decodeWidePtr?, decodeDataWord?]

/-- **Validated codec (encode after decode).** A `Value` that decodes is exactly
the encoding of what it decodes to, so no other `Value` shape is accepted. -/
theorem encodeWidePtr_of_decodeWidePtr? {ptrBytes : Nat} {v : Value} {w : ProtoWidePtr}
    (h : decodeWidePtr? ptrBytes v = some w) : encodeWidePtr ptrBytes w = v := by
  cases v with
  | ptr p sz =>
    have hd : decodeDataWord? ptrBytes (.ptr p sz) = some w.data ∧ w.ptrMeta = .thin := by
      simp only [decodeWidePtr?] at h
      cases hdw : decodeDataWord? ptrBytes (.ptr p sz) with
      | none => rw [hdw] at h; cases h
      | some dw => rw [hdw] at h; cases h; exact ⟨rfl, rfl⟩
    obtain ⟨d, m⟩ := w
    cases hd.2
    exact encodeDataWord_of_decodeDataWord? hd.1
  | scalar sc =>
    have hd : decodeDataWord? ptrBytes (.scalar sc) = some w.data ∧ w.ptrMeta = .thin := by
      simp only [decodeWidePtr?] at h
      cases hdw : decodeDataWord? ptrBytes (.scalar sc) with
      | none => rw [hdw] at h; cases h
      | some dw => rw [hdw] at h; cases h; exact ⟨rfl, rfl⟩
    obtain ⟨d, m⟩ := w
    cases hd.2
    exact encodeDataWord_of_decodeDataWord? hd.1
  | unit => simp [decodeWidePtr?, decodeDataWord?] at h
  | uninit => simp [decodeWidePtr?, decodeDataWord?] at h
  | aggregate vIdx fields =>
    simp only [decodeWidePtr?] at h
    cases hv : Nat.beq vIdx 0 with
    | false => rw [hv] at h; cases h
    | true =>
      rw [hv] at h
      cases Nat.eq_of_beq_eq_true hv
      match fields, h with
      | [d, .scalar m], h =>
        simp only at h
        cases hdw : decodeDataWord? ptrBytes d with
        | none => rw [hdw] at h; cases h
        | some dw =>
          rw [hdw] at h
          cases hsz : Nat.beq m.sizeBytes ptrBytes with
          | false => rw [hsz] at h; cases h
          | true =>
            rw [hsz] at h; cases h
            cases m
            simp only [encodeWidePtr]
            rw [encodeDataWord_of_decodeDataWord? hdw, ← Nat.eq_of_beq_eq_true hsz]
      | [d, .ptr vt sz], h =>
        simp only at h
        cases hdw : decodeDataWord? ptrBytes d with
        | none => rw [hdw] at h; cases h
        | some dw =>
          rw [hdw] at h
          cases hsz : Nat.beq sz ptrBytes with
          | false => rw [hsz] at h; cases h
          | true =>
            rw [hsz] at h; cases h
            simp only [encodeWidePtr]
            rw [encodeDataWord_of_decodeDataWord? hdw, ← Nat.eq_of_beq_eq_true hsz]

/-- Reference or raw pointer. -/
inductive ProtoPtrKind : Type where
  | ref
  | raw
  deriving DecidableEq

/-- Pointee class of a pointer type, independent of the MIR dialect. -/
inductive ProtoPointee : Type where
  /-- Sized concrete type with canonical key `tyKey`. -/
  | sized (tyKey : String)
  | slice
  | str
  /-- Trait object whose dialect key (`RigidTy.dynamic` path) is `traitKey`. -/
  | dyn (traitKey : String)
  /-- A pointee the prototype does not classify. -/
  | opaque

/-- Pointer type, independent of the MIR dialect. -/
structure ProtoPtrTy : Type where
  kind : ProtoPtrKind
  isMut : Bool
  pointee : ProtoPointee

/-- Pointer coercion class, independent of the MIR dialect. -/
inductive ProtoCoercion : Type where
  | unsize
  | other
  deriving DecidableEq

namespace V06
open Trusted.Rustc.V2026_06_01.MirAst

/-- Mutability of the `V2026_06_01` dialect. -/
def lowerMut : Mutability → Bool
  | .not => false
  | .mut => true

/-- Canonical key of a sized concrete type (`V2026_06_01`). Types the
prototype does not key report `none`, which makes the rules fail closed. -/
def tyKey? : RigidTy → Option String
  | .adt path [] => some path
  | .bool => some "bool"
  | .char => some "char"
  | .uint .u8 => some "u8"
  | .uint .u16 => some "u16"
  | .uint .u32 => some "u32"
  | .uint .u64 => some "u64"
  | .uint .usize => some "usize"
  | .int .i8 => some "i8"
  | .int .i16 => some "i16"
  | .int .i32 => some "i32"
  | .int .i64 => some "i64"
  | .int .isize => some "isize"
  | .tuple [] => some "()"
  | _ => none

/-- Pointee class (`V2026_06_01`). -/
def lowerPointee : RigidTy → ProtoPointee
  | .slice _ => .slice
  | .str => .str
  | .dynamic traitPath => .dyn traitPath
  | ty =>
    match tyKey? ty with
    | some k => .sized k
    | none => .opaque

/-- Pointer type (`V2026_06_01`): `none` on a non-pointer type. -/
def lowerPtrTy : RigidTy → Option ProtoPtrTy
  | .ref m pointee => some ⟨.ref, lowerMut m, lowerPointee pointee⟩
  | .rawPtr m pointee => some ⟨.raw, lowerMut m, lowerPointee pointee⟩
  | _ => none

/-- Coercion class of a cast kind (`V2026_06_01`): `none` on a cast that is not
a pointer coercion. -/
def lowerCastKind : CastKind → Option ProtoCoercion
  | .pointerCoercion kind =>
    match strEq kind "Unsize" with
    | true => some .unsize
    | false => some .other
  | _ => none

end V06

namespace V08

/-- Mutability of the `V2026_08_01` dialect. -/
def lowerMut : Trusted.Rustc.V2026_08_01.MirAst.Mutability → Bool
  | .not => false
  | .mut => true

/-- Canonical key of a sized concrete type (`V2026_08_01`). -/
def tyKey? : Trusted.Rustc.V2026_08_01.MirAst.RigidTy → Option String
  | .adt path [] => some path
  | .bool => some "bool"
  | .char => some "char"
  | .uint .u8 => some "u8"
  | .uint .u16 => some "u16"
  | .uint .u32 => some "u32"
  | .uint .u64 => some "u64"
  | .uint .usize => some "usize"
  | .int .i8 => some "i8"
  | .int .i16 => some "i16"
  | .int .i32 => some "i32"
  | .int .i64 => some "i64"
  | .int .isize => some "isize"
  | .tuple [] => some "()"
  | _ => none

/-- Pointee class (`V2026_08_01`). -/
def lowerPointee : Trusted.Rustc.V2026_08_01.MirAst.RigidTy → ProtoPointee
  | .slice _ => .slice
  | .str => .str
  | .dynamic traitPath => .dyn traitPath
  | ty =>
    match tyKey? ty with
    | some k => .sized k
    | none => .opaque

/-- Pointer type (`V2026_08_01`): `none` on a non-pointer type. -/
def lowerPtrTy : Trusted.Rustc.V2026_08_01.MirAst.RigidTy → Option ProtoPtrTy
  | .ref m pointee => some ⟨.ref, lowerMut m, lowerPointee pointee⟩
  | .rawPtr m pointee => some ⟨.raw, lowerMut m, lowerPointee pointee⟩
  | _ => none

/-- Coercion class of a cast kind (`V2026_08_01`). -/
def lowerCastKind : Trusted.Rustc.V2026_08_01.MirAst.CastKind → Option ProtoCoercion
  | .pointerCoercion kind =>
    match strEq kind "Unsize" with
    | true => some .unsize
    | false => some .other
  | _ => none

end V08

/-! ### Dialect invariance

`homTy`, `homMut`, and `homCastKind` translate the `V2026_06_01` syntax the
adapters inspect into its `V2026_08_01` homologue. The adapters agree on
homologous inputs, so both dialects lower onto the same neutral types. -/

namespace Hom
open Trusted.Rustc

/-- Homologous mutability. -/
def homMut : V2026_06_01.MirAst.Mutability → V2026_08_01.MirAst.Mutability
  | .not => .not
  | .mut => .mut

/-- Homologous pointee, on the pointee heads the adapters distinguish. A slice
element type is erased to `()` on both sides: the adapters never inspect it. -/
def homPointee? : V2026_06_01.MirAst.RigidTy → Option V2026_08_01.MirAst.RigidTy
  | .adt path [] => some (.adt path [])
  | .bool => some .bool
  | .char => some .char
  | .uint .u8 => some (.uint .u8)
  | .uint .u16 => some (.uint .u16)
  | .uint .u32 => some (.uint .u32)
  | .uint .u64 => some (.uint .u64)
  | .uint .usize => some (.uint .usize)
  | .int .i8 => some (.int .i8)
  | .int .i16 => some (.int .i16)
  | .int .i32 => some (.int .i32)
  | .int .i64 => some (.int .i64)
  | .int .isize => some (.int .isize)
  | .tuple [] => some (.tuple [])
  | .str => some .str
  | .slice _ => some (.slice (.tuple []))
  | .dynamic traitPath => some (.dynamic traitPath)
  | _ => none

/-- Homologous pointer type. -/
def homPtrTy? : V2026_06_01.MirAst.RigidTy → Option V2026_08_01.MirAst.RigidTy
  | .ref m pointee =>
    match homPointee? pointee with
    | some p => some (.ref (homMut m) p)
    | none => none
  | .rawPtr m pointee =>
    match homPointee? pointee with
    | some p => some (.rawPtr (homMut m) p)
    | none => none
  | _ => none

/-- Homologous cast kind (total: the two dialects have the same cast kinds). -/
def homCastKind : V2026_06_01.MirAst.CastKind → V2026_08_01.MirAst.CastKind
  | .pointerExposeProvenance => .pointerExposeProvenance
  | .pointerWithExposedProvenance => .pointerWithExposedProvenance
  | .pointerCoercion k => .pointerCoercion k
  | .intToInt => .intToInt
  | .floatToInt => .floatToInt
  | .floatToFloat => .floatToFloat
  | .intToFloat => .intToFloat
  | .ptrToPtr => .ptrToPtr
  | .fnPtrToPtr => .fnPtrToPtr
  | .transmute => .transmute
  | .subtype => .subtype

theorem lowerMut_hom (m : V2026_06_01.MirAst.Mutability) :
    V08.lowerMut (homMut m) = V06.lowerMut m := by
  cases m <;> rfl

/-- **Dialect invariance of cast-kind lowering** (every cast kind). -/
theorem lowerCastKind_hom (k : V2026_06_01.MirAst.CastKind) :
    V08.lowerCastKind (homCastKind k) = V06.lowerCastKind k := by
  cases k <;> rfl

theorem lowerPointee_hom {t : V2026_06_01.MirAst.RigidTy} {t' : V2026_08_01.MirAst.RigidTy}
    (h : homPointee? t = some t') : V08.lowerPointee t' = V06.lowerPointee t := by
  unfold homPointee? at h
  split at h <;> first | (cases h; rfl) | cases h

/-- **Dialect invariance of pointer-type lowering**: homologous `V2026_06_01`
and `V2026_08_01` pointer types lower onto the same neutral pointer type. -/
theorem lowerPtrTy_hom {t : V2026_06_01.MirAst.RigidTy} {t' : V2026_08_01.MirAst.RigidTy}
    (h : homPtrTy? t = some t') : V08.lowerPtrTy t' = V06.lowerPtrTy t := by
  cases t with
  | ref m pointee =>
    simp only [homPtrTy?] at h
    cases hp : homPointee? pointee with
    | none => rw [hp] at h; cases h
    | some p =>
      rw [hp] at h; cases h
      simp only [V08.lowerPtrTy, V06.lowerPtrTy, lowerMut_hom, lowerPointee_hom hp]
  | rawPtr m pointee =>
    simp only [homPtrTy?] at h
    cases hp : homPointee? pointee with
    | none => rw [hp] at h; cases h
    | some p =>
      rw [hp] at h; cases h
      simp only [V08.lowerPtrTy, V06.lowerPtrTy, lowerMut_hom, lowerPointee_hom hp]
  | _ => simp [homPtrTy?] at h

/-- The homologue exists whenever the `V2026_06_01` adapter classifies the
pointee: the translation is total on the pointees the rules act on. -/
theorem homPointee?_isSome_of_classified (t : V2026_06_01.MirAst.RigidTy)
    (h : (match V06.lowerPointee t with | .opaque => false | _ => true) = true) :
    (homPointee? t).isSome = true := by
  unfold homPointee?
  split <;> first | rfl | skip
  rename_i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  unfold V06.lowerPointee at h
  split at h
  all_goals first
    | exact (h16 _ rfl).elim
    | exact (h15 rfl).elim
    | exact (h17 _ rfl).elim
    | (cases h; done)
    | (exfalso
       rename_i k heq
       unfold V06.tyKey? at heq
       split at heq <;> first | (simp_all; done) | cases heq)

end Hom

/-! ## §3. `dyn Trait` unsizing coercion -/

/-- `targetKind` is a reference or raw pointer to a trait object: its pointer
kind, mutability, and the dialect key of the trait object type. -/
def dynPtrTarget? : RigidTy → Option (ProtoPtrKind × Bool × String)
  | .ref m (.dynamic traitKey) => some (.ref, V06.lowerMut m, traitKey)
  | .rawPtr m (.dynamic traitKey) => some (.raw, V06.lowerMut m, traitKey)
  | _ => none

/-- Pointer-kind compatibility of an unsizing coercion: a reference coerces to
a reference or a raw pointer, a raw pointer only to a raw pointer. -/
def unsizeKindCompatible : ProtoPtrKind → ProtoPtrKind → Bool
  | .ref, _ => true
  | .raw, .raw => true
  | .raw, .ref => false

/-- Mutability compatibility of an unsizing coercion (the neutral form of
`unsizeMutabilityCompatible`): a shared source never coerces to a mutable
target. -/
def unsizeMutCompatible (srcMut dstMut : Bool) : Bool := srcMut || !dstMut

/-- Tree Borrows permission check of a borrow tag for creating a reference
with mutability `dstMut`: `.disabled` never, `.frozen` only when shared. -/
def borrowPermAllows (perm : TreeBorrowPerm) (dstMut : Bool) : Bool :=
  match perm with
  | .disabled => false
  | .frozen => !dstMut
  | _ => true

/-- Byte length of the allocation behind the borrow `b`, and the byte offset
of the borrowed place inside it: the declared size of the target local of the
frame that owns it, and `borrowPlaceByteOffset?`. `none` when the local is
gone, dead, or has no known layout. -/
def borrowAllocExtent?
    (locals : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (b : BorrowEntry) : Option (Nat × Nat) :=
  match readFrameLocalSlot locals mem.callStack mem.callerLocals b.targetFrameDepth b.targetLocal with
  | none => none
  | some .dead => none
  | some _ =>
    match frameLocalDeclsAndLayoutsAtDepth mem.callStack localDecls layouts b.targetFrameDepth with
    | none => none
    | some (decls, lays) =>
      match get? decls b.targetLocal with
      | none => none
      | some decl =>
        match
          tyByteSize decls lays decl.ty,
          borrowPlaceByteOffset? locals mem.callerLocals localDecls layouts b mem.callStack
        with
        | some allocLen, some placeOff => some (allocLen, placeOff)
        | _, _ => none

/-- Normalize a data word to target pointer width `ptrBytes` (wrapping
provenance-less scalar addresses modulo `2^(8 * ptrBytes)`). -/
def wrapDataWord (ptrBytes : Nat) : ProtoDataWord → ProtoDataWord
  | .prov p => .prov p
  | .addr bits => .addr (wrapScalarBits bits (scalarModulus ptrBytes))

/-- Tree Borrows access kind required to validate a reference with mutability `dstMut`. -/
def refAccessKind (dstMut : Bool) : TreeBorrowAccessKind :=
  match dstMut with
  | true => .write
  | false => .read

/-- Safe-reference validity of the data pointer `p` at the layout of the
vtable entry `e` (`check_ptr` on a safe pointer): the address is in-bounds for
`ptrBytes`, non-null, and aligned to a valid power-of-two `alignBytes`; the
concrete type is inhabited; the borrow tag and every strict ancestor permit the
access (or the global allocation is writable and in bounds; or for a zero-sized
type, a non-null aligned dangling pointer `allocId = 0` is valid per
`Places.lean:14620` and MiniRust `check_ptr`). -/
def refDataValid
    (ptrBytes : Nat) (e : ProtoVTableEntry) (dstMut : Bool) (p : ProvenancePtr)
    (locals : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) : Bool :=
  match
    ptrAddress? locals mem.borrows mem.callerLocals localDecls layouts ptrBytes p mem.callStack
  with
  | none => false
  | some addr =>
    match
      isPow2 e.alignBytes && Nat.blt addr (scalarModulus ptrBytes) &&
        !Nat.beq addr 0 && Nat.beq (addr % e.alignBytes) 0 && !e.isUninhabited
    with
    | false => false
    | true =>
      match lookupBorrow mem.borrows p.tag with
      | some b =>
        match
          borrowPermAllows b.perm dstMut && !b.allocDead &&
            !treeBorrowAncestorsChildAccessUB (refAccessKind dstMut) mem.borrows b.parentTag
        with
        | false => false
        | true =>
          match borrowAllocExtent? locals mem localDecls layouts b with
          | some (allocLen, placeOff) =>
            Nat.ble (placeOff + p.offsetBytes + e.sizeBytes) allocLen
          | none => false
      | none =>
        match lookupGlobalAlloc mem.globals p.allocId with
        | some alloc =>
          (match dstMut, alloc.mutability with
           | true, .not => false
           | _, _ => true) &&
            Nat.ble (p.offsetBytes + e.sizeBytes) (length alloc.bytes)
        | none =>
          -- Valid dangling ZST reference (e.g. `NonNull::<()>::dangling()`):
          -- `allocId = 0`, non-null aligned offset, `sizeBytes = 0`.
          Nat.beq e.sizeBytes 0 && Nat.beq p.allocId 0 && !Nat.beq p.offsetBytes 0

/-- Safe-reference validity of a provenance-less address word (valid only for a
zero-sized, inhabited concrete type at a wrapped non-null aligned address). -/
def refAddrValid (ptrBytes : Nat) (e : ProtoVTableEntry) (bits : Nat) : Bool :=
  let wrapped := wrapScalarBits bits (scalarModulus ptrBytes)
  isPow2 e.alignBytes && Nat.beq e.sizeBytes 0 && !Nat.beq wrapped 0 &&
    Nat.beq (wrapped % e.alignBytes) 0 && !e.isUninhabited

/-- Vtable pointer `Value` of the entry `e`. -/
def vtablePtrOf (e : ProtoVTableEntry) : ProvenancePtr :=
  { allocId := e.vtableAllocId, offsetBytes := 0 }

/-- Trait-object pointer `Value` with data word `d` and the vtable of `e`. -/
def mkDynPtr (ptrBytes : Nat) (d : ProtoDataWord) (e : ProtoVTableEntry) : Value :=
  encodeWidePtr ptrBytes ⟨d, .vtable (vtablePtrOf e)⟩

/-- Resolution of a runtime vtable pointer for the trait object type `pred`
(`InvalidVTablePointer` / `InvalidVTableTrait`): the pointer must be the base
of a captured vtable allocation whose trait object type is `pred`. -/
inductive VTableResolution : Type where
  | ok (e : ProtoVTableEntry)
  | invalidPointer
  | invalidTrait

/-- Resolve the vtable pointer `vtPtr` for `pred`. -/
def resolveVTablePtr (vt : ProtoVTableTable) (pred : ProtoTraitPred) (vtPtr : ProvenancePtr) :
    VTableResolution :=
  match Nat.beq vtPtr.offsetBytes 0 with
  | false => .invalidPointer
  | true =>
    match lookupVTableByAlloc vt.entries vtPtr.allocId with
    | none => .invalidPointer
    | some e =>
      match traitPredEq e.traitPred pred with
      | true => .ok e
      | false => .invalidTrait

/-- Supertrait vtable reached from the slots `slots` through a `.traitVPtr`
slot whose vtable has trait object type `dstPred`. -/
def findSupertraitVPtr (es : List ProtoVTableEntry) (dstPred : ProtoTraitPred) :
    List ProtoVTableSlot → Option ProtoVTableEntry
  | [] => none
  | .traitVPtr sup :: rest =>
    match lookupVTableById es sup with
    | some s =>
      match traitPredEq s.traitPred dstPred with
      | true => some s
      | false => findSupertraitVPtr es dstPred rest
    | none => findSupertraitVPtr es dstPred rest
  | _ :: rest => findSupertraitVPtr es dstPred rest

/-- Fuel-bounded walk along `primarySuperVTable?` (prefix-compatible primary
supertrait chain), matching `rustc`'s primary supertrait vtable prefix layout
without permitting arbitrary unrelated 0-method marker traits. -/
def findPrimarySuperVTable (es : List ProtoVTableEntry) (dstPred : ProtoTraitPred) :
    Nat → ProtoVTableEntry → Option ProtoVTableEntry
  | 0, _ => none
  | fuel + 1, cur =>
    match cur.primarySuperVTable? with
    | none => none
    | some supId =>
      match lookupVTableById es supId with
      | none => none
      | some sup =>
        match sameConcreteLayout sup cur && slotsPrefix sup.slots cur.slots with
        | false => none
        | true =>
          match traitPredEq sup.traitPred dstPred with
          | true => some sup
          | false => findPrimarySuperVTable es dstPred fuel sup

/-- Target vtable of the upcast of `e` to `dstPred`: through a `.traitVPtr`
slot, or along the declared primary-supertrait prefix chain
(`Miri.Interpreter.Cast.unsizeIntoPointer:179-205`). Unrelated traits (even
0-method marker traits whose header is a slot prefix) are rejected. -/
def upcastVTable? (es : List ProtoVTableEntry) (e : ProtoVTableEntry) (dstPred : ProtoTraitPred) :
    Option ProtoVTableEntry :=
  match findSupertraitVPtr es dstPred e.slots with
  | some s => some s
  | none => findPrimarySuperVTable es dstPred (length es) e

/-- Unsizing of an evaluated thin pointer `v` to a concrete type `tyKey` into a
pointer to the trait object type `dstPred`.

A raw-to-raw coercion only pairs the data word with the vtable pointer: the
data pointer may be null, dangling, misaligned, or provenance-less. A
coercion from a reference additionally requires safe-reference validity
(`refDataValid` / `refAddrValid`). -/
def unsizeSizedToDyn
    (vt : ProtoVTableTable) (ptrBytes : Nat) (srcKind : ProtoPtrKind) (dstMut : Bool)
    (dstPred : ProtoTraitPred) (tyKey : String) (v : Value)
    (locals : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) : RvalueEvalResult :=
  match findVTableFor vt.entries tyKey dstPred with
  | none => .unsupported
  | some e =>
    match v with
    | .ptr p sz =>
      match Nat.beq sz ptrBytes with
      | false => .ub
      | true =>
        match srcKind with
        | .raw => .ok (mkDynPtr ptrBytes (.prov p) e) locals mem
        | .ref =>
          match refDataValid ptrBytes e dstMut p locals mem localDecls layouts with
          | true => .ok (mkDynPtr ptrBytes (.prov p) e) locals mem
          | false => .ub
    | .scalar sc =>
      match Nat.beq sc.sizeBytes ptrBytes with
      | false => .ub
      | true =>
        let bits := wrapScalarBits sc.bits (scalarModulus ptrBytes)
        match srcKind with
        | .raw => .ok (mkDynPtr ptrBytes (.addr bits) e) locals mem
        | .ref =>
          -- A provenance-less reference is valid only to a zero-sized type.
          match refAddrValid ptrBytes e bits with
          | true => .ok (mkDynPtr ptrBytes (.addr bits) e) locals mem
          | false => .ub
    | _ => .ub

/-- Upcast (or identity coercion) of an evaluated trait-object pointer `v` of
type `srcPred` into a pointer to `dstPred`. The incoming vtable pointer is
validated first (a runtime check: invalid vtable pointers are UB, as in
`Cast.unsizeIntoPointer`'s `vtableType`). Auto-trait fabrication
(`dstPred.autoTraits ⊈ srcPred.autoTraits`) is ill-typed MIR and fails closed
with `.unsupported`. Provenance-less data addresses are wrapped modulo
`2^(8 * ptrBytes)` before safe-reference validity is checked. -/
def unsizeDynToDyn
    (vt : ProtoVTableTable) (ptrBytes : Nat) (srcKind : ProtoPtrKind) (dstMut : Bool)
    (srcPred dstPred : ProtoTraitPred) (v : Value)
    (locals : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) : RvalueEvalResult :=
  match decodeWidePtr? ptrBytes v with
  | some ⟨d, .vtable vtPtr⟩ =>
    match resolveVTablePtr vt srcPred vtPtr with
    | .invalidPointer => .ub
    | .invalidTrait => .ub
    | .ok e =>
      match autoTraitsSubset dstPred.autoTraits srcPred.autoTraits with
      | false => .unsupported
      | true =>
        match (match traitPredEq srcPred dstPred with
               | true => some e
               | false => upcastVTable? vt.entries e dstPred) with
        | none => .unsupported
        | some target =>
          let d' := wrapDataWord ptrBytes d
          match srcKind, d' with
          | .raw, _ => .ok (mkDynPtr ptrBytes d' target) locals mem
          | .ref, .prov p =>
            match refDataValid ptrBytes target dstMut p locals mem localDecls layouts with
            | true => .ok (mkDynPtr ptrBytes (.prov p) target) locals mem
            | false => .ub
          | .ref, .addr bits =>
            match refAddrValid ptrBytes target bits with
            | true => .ok (mkDynPtr ptrBytes (.addr bits) target) locals mem
            | false => .ub
  | _ => .ub

/-- Unsizing of the evaluated operand `v` of pointer type `src` into a
`dstKind` pointer of mutability `dstMut` to the trait object type `dstPred`. -/
def unsizeDynValue
    (vt : ProtoVTableTable) (ptrBytes : Nat) (dstKind : ProtoPtrKind) (dstMut : Bool)
    (dstPred : ProtoTraitPred) (src : ProtoPtrTy) (v : Value)
    (locals : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) : RvalueEvalResult :=
  match unsizeKindCompatible src.kind dstKind && unsizeMutCompatible src.isMut dstMut with
  | false => .ub
  | true =>
    match src.pointee with
    | .sized tyKey =>
      unsizeSizedToDyn vt ptrBytes src.kind dstMut dstPred tyKey v locals mem localDecls layouts
    | .dyn srcKey =>
      match lookupDynPred vt.dynTypes srcKey with
      | none => .unsupported
      | some srcPred =>
        match srcPred.failsClosed with
        | true => .unsupported
        | false =>
          unsizeDynToDyn vt ptrBytes src.kind dstMut srcPred dstPred v locals mem localDecls layouts
    | .slice => .ub
    | .str => .ub
    | .opaque => .unsupported

/-- `CastKind.pointerCoercion "Unsize"` to a `dstKind` pointer of mutability
`dstMut` to the trait object type keyed `traitKey`.

Fail-closed order: the environment gate and the target predicate are checked
before the operand is evaluated, so an unresolved existential binder or an
undischarged outlives obligation is `.unsupported` whatever the operand is. -/
def evalUnsizeDynProto
    (vt : ProtoVTableTable) (dstKind : ProtoPtrKind) (dstMut : Bool) (traitKey : String)
    (locals : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) : RvalueEvalResult :=
  let ptrBytes := layoutPointerBytes layouts
  match lookupDynPred vt.dynTypes traitKey with
  | none => .unsupported
  | some dstPred =>
    match dstPred.failsClosed with
    | true => .unsupported
    | false =>
      match vtableEnvOk ptrBytes vt mem with
      | false => .unsupported
      | true =>
        match
          evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
            mem.callStack
        with
        | .ub => .ub
        | .unsupported => .unsupported
        | .ok v locals' =>
          match operandTy localDecls layouts op with
          | none => .unsupported
          | some srcTy =>
            match V06.lowerPtrTy srcTy.kind with
            | none => .ub
            | some src =>
              unsizeDynValue vt ptrBytes dstKind dstMut dstPred src v locals' mem localDecls
                layouts

/-- **Prototype replacement for `evalUnsizeCoercion`.** A reference or raw
pointer target to a trait object uses `evalUnsizeDynProto`; every other target
is `evalUnsizeCoercion` itself. -/
def evalUnsizeCoercionProto
    (vt : ProtoVTableTable) (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) : RvalueEvalResult :=
  match dynPtrTarget? targetTy.kind with
  | none => evalUnsizeCoercion locals op targetTy mem localDecls layouts
  | some (dstKind, dstMut, traitKey) =>
    evalUnsizeDynProto vt dstKind dstMut traitKey locals op mem localDecls layouts

/-- **Universal conservation.** On every target that is not a pointer to a
trait object, the prototype IS `evalUnsizeCoercion`. -/
theorem evalUnsizeCoercionProto_conservative
    (vt : ProtoVTableTable) (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h : dynPtrTarget? targetTy.kind = none) :
    evalUnsizeCoercionProto vt locals op targetTy mem localDecls layouts =
      evalUnsizeCoercion locals op targetTy mem localDecls layouts := by
  unfold evalUnsizeCoercionProto
  rw [h]

/-- **Universal slice conservation.** For the four slice-pointer targets
`&[T]`, `&mut [T]`, `*const [T]`, `*mut [T]` (every `T`, every vtable table,
operand, and state) the prototype agrees with `evalUnsizeCoercion`. -/
theorem evalUnsizeCoercionProto_slice_conservative
    (vt : ProtoVTableTable) (locals : List LocalSlot) (op : Operand)
    (m : Mutability) (elem : RigidTy) (layoutIdx : LayoutIdx)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalUnsizeCoercionProto vt locals op ⟨.ref m (.slice elem), layoutIdx⟩ mem localDecls
        layouts =
      evalUnsizeCoercion locals op ⟨.ref m (.slice elem), layoutIdx⟩ mem localDecls layouts ∧
    evalUnsizeCoercionProto vt locals op ⟨.rawPtr m (.slice elem), layoutIdx⟩ mem localDecls
        layouts =
      evalUnsizeCoercion locals op ⟨.rawPtr m (.slice elem), layoutIdx⟩ mem localDecls layouts :=
  ⟨rfl, rfl⟩

theorem rawPtrUnsizeArrayToSliceLen?_dyn_target_none
    (srcOpt : Option Ty) (targetTy : Ty) (ptrBytes : Nat)
    (k : ProtoPtrKind × Bool × String) (h : dynPtrTarget? targetTy.kind = some k) :
    rawPtrUnsizeArrayToSliceLen? srcOpt targetTy ptrBytes = none := by
  unfold rawPtrUnsizeArrayToSliceLen?
  split
  · rename_i heq
    rw [heq] at h
    cases h
  · rfl

/-- **Campaign #22 root cause, universally.** On a reference or raw pointer
target to a trait object, `evalUnsizeCoercion` never succeeds: it is `.ub`
unless evaluating the operand is itself `.unsupported`. -/
theorem evalUnsizeCoercion_dyn_target_never_ok
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (k : ProtoPtrKind × Bool × String) (h : dynPtrTarget? targetTy.kind = some k) :
    evalUnsizeCoercion locals op targetTy mem localDecls layouts = .ub ∨
    evalUnsizeCoercion locals op targetTy mem localDecls layouts = .unsupported := by
  obtain ⟨kind, idx⟩ := targetTy
  have hk : (∃ m t, kind = .ref m (.dynamic t)) ∨ (∃ m t, kind = .rawPtr m (.dynamic t)) := by
    simp only at h
    unfold dynPtrTarget? at h
    split at h
    · exact Or.inl ⟨_, _, rfl⟩
    · exact Or.inr ⟨_, _, rfl⟩
    · cases h
  rcases hk with ⟨m, t, rfl⟩ | ⟨m, t, rfl⟩
  all_goals
    unfold evalUnsizeCoercion
    dsimp only
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
    · split
      · exact Or.inl rfl
      · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · rw [rawPtrUnsizeArrayToSliceLen?_dyn_target_none _ _ _ k h]
        exact Or.inl rfl
    · exact Or.inl rfl

/-! ### §3 universal laws -/

/-- **Fail-closed existential boundary (`charon#1640`, `407e0bf7692a`).** When
the target predicate has an unresolved existential binder or undischarged
supertrait outlives obligations, unsizing is `.unsupported` for every operand
and state: never `.ok`, never `.ub`. -/
theorem evalUnsizeDynProto_failsClosed
    (vt : ProtoVTableTable) (dstKind : ProtoPtrKind) (dstMut : Bool) (traitKey : String)
    (locals : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (pred : ProtoTraitPred)
    (hLook : lookupDynPred vt.dynTypes traitKey = some pred)
    (hFail : pred.failsClosed = true) :
    evalUnsizeDynProto vt dstKind dstMut traitKey locals op mem localDecls layouts =
      .unsupported := by
  unfold evalUnsizeDynProto
  simp only [hLook, hFail]

/-- A trait object type with no registered predicate list fails closed. -/
theorem evalUnsizeDynProto_unregistered
    (vt : ProtoVTableTable) (dstKind : ProtoPtrKind) (dstMut : Bool) (traitKey : String)
    (locals : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hLook : lookupDynPred vt.dynTypes traitKey = none) :
    evalUnsizeDynProto vt dstKind dstMut traitKey locals op mem localDecls layouts =
      .unsupported := by
  unfold evalUnsizeDynProto
  simp only [hLook]

/-- A vtable environment that is ill formed, or overlaps the allocations of
`mem`, fails closed. -/
theorem evalUnsizeDynProto_env_gate
    (vt : ProtoVTableTable) (dstKind : ProtoPtrKind) (dstMut : Bool) (traitKey : String)
    (locals : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hEnv : vtableEnvOk (layoutPointerBytes layouts) vt mem = false) :
    evalUnsizeDynProto vt dstKind dstMut traitKey locals op mem localDecls layouts =
      .unsupported := by
  unfold evalUnsizeDynProto
  dsimp only
  split
  · rfl
  · split
    · rfl
    · rw [hEnv]

/-- **Mutability violation.** A shared source (`&T`, `*const T`) never unsizes
to a mutable target (`&mut dyn Trait`, `*mut dyn Trait`). -/
theorem unsizeDynValue_shared_to_mut_ub
    (vt : ProtoVTableTable) (ptrBytes : Nat) (dstKind : ProtoPtrKind)
    (dstPred : ProtoTraitPred) (src : ProtoPtrTy) (v : Value)
    (locals : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (hSrc : src.isMut = false) :
    unsizeDynValue vt ptrBytes dstKind true dstPred src v locals mem localDecls layouts = .ub := by
  unfold unsizeDynValue
  simp [unsizeMutCompatible, hSrc]

/-- **Kind violation.** A raw pointer never unsizes to a reference. -/
theorem unsizeDynValue_raw_to_ref_ub
    (vt : ProtoVTableTable) (ptrBytes : Nat) (dstMut : Bool)
    (dstPred : ProtoTraitPred) (src : ProtoPtrTy) (v : Value)
    (locals : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (hSrc : src.kind = .raw) :
    unsizeDynValue vt ptrBytes .ref dstMut dstPred src v locals mem localDecls layouts = .ub := by
  unfold unsizeDynValue
  simp [unsizeKindCompatible, hSrc]

/-- **Raw side of the raw-versus-reference distinction.** Unsizing a raw
pointer with provenance pairs it with the vtable pointer for EVERY data pointer
`p`: nothing is required of its allocation, offset, alignment, or borrow tag,
and the data pointer is preserved exactly. -/
theorem unsizeSizedToDyn_raw_ptr_unchecked
    (vt : ProtoVTableTable) (ptrBytes : Nat) (dstMut : Bool) (dstPred : ProtoTraitPred)
    (tyKey : String) (p : ProvenancePtr) (locals : List LocalSlot) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (e : ProtoVTableEntry)
    (hFind : findVTableFor vt.entries tyKey dstPred = some e) :
    unsizeSizedToDyn vt ptrBytes .raw dstMut dstPred tyKey (.ptr p ptrBytes) locals mem
        localDecls layouts =
      .ok (.aggregate 0 [.ptr p ptrBytes, .ptr (vtablePtrOf e) ptrBytes]) locals mem := by
  unfold unsizeSizedToDyn
  simp only [hFind, Nat.beq_refl]
  rfl

/-- **Raw side, provenance-less pointers.** Unsizing a provenance-less raw
pointer (any address, including null) pairs its wrapped address with the vtable
pointer. -/
theorem unsizeSizedToDyn_raw_scalar_unchecked
    (vt : ProtoVTableTable) (ptrBytes : Nat) (dstMut : Bool) (dstPred : ProtoTraitPred)
    (tyKey : String) (bits : Nat) (locals : List LocalSlot) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (e : ProtoVTableEntry)
    (hFind : findVTableFor vt.entries tyKey dstPred = some e) :
    unsizeSizedToDyn vt ptrBytes .raw dstMut dstPred tyKey (.scalar ⟨bits, ptrBytes⟩) locals mem
        localDecls layouts =
      .ok (.aggregate 0
            [.scalar ⟨wrapScalarBits bits (scalarModulus ptrBytes), ptrBytes⟩,
             .ptr (vtablePtrOf e) ptrBytes]) locals mem := by
  unfold unsizeSizedToDyn
  simp only [hFind, Nat.beq_refl]
  rfl

/-- **Reference side of the raw-versus-reference distinction.** Unsizing a
reference with provenance succeeds exactly when the data pointer passes
safe-reference validity, and is UB otherwise. -/
theorem unsizeSizedToDyn_ref_ptr_iff_valid
    (vt : ProtoVTableTable) (ptrBytes : Nat) (dstMut : Bool) (dstPred : ProtoTraitPred)
    (tyKey : String) (p : ProvenancePtr) (locals : List LocalSlot) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (e : ProtoVTableEntry)
    (hFind : findVTableFor vt.entries tyKey dstPred = some e) :
    unsizeSizedToDyn vt ptrBytes .ref dstMut dstPred tyKey (.ptr p ptrBytes) locals mem
        localDecls layouts =
      (match refDataValid ptrBytes e dstMut p locals mem localDecls layouts with
       | true => .ok (.aggregate 0 [.ptr p ptrBytes, .ptr (vtablePtrOf e) ptrBytes]) locals mem
       | false => .ub) := by
  unfold unsizeSizedToDyn
  simp only [hFind, Nat.beq_refl]
  rfl

/-- An uncaptured vtable (no entry for the concrete type and trait object
type) is `.unsupported`, never `.ok` and never `.ub`. -/
theorem unsizeSizedToDyn_uncaptured_unsupported
    (vt : ProtoVTableTable) (ptrBytes : Nat) (srcKind : ProtoPtrKind) (dstMut : Bool)
    (dstPred : ProtoTraitPred) (tyKey : String) (v : Value) (locals : List LocalSlot)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hFind : findVTableFor vt.entries tyKey dstPred = none) :
    unsizeSizedToDyn vt ptrBytes srcKind dstMut dstPred tyKey v locals mem localDecls layouts =
      .unsupported := by
  unfold unsizeSizedToDyn
  simp only [hFind]

/-- A `.disabled` borrow tag is never a valid reference. -/
theorem refDataValid_disabled
    (ptrBytes : Nat) (e : ProtoVTableEntry) (dstMut : Bool) (p : ProvenancePtr)
    (locals : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (b : BorrowEntry)
    (hB : lookupBorrow mem.borrows p.tag = some b) (hPerm : b.perm = .disabled) :
    refDataValid ptrBytes e dstMut p locals mem localDecls layouts = false := by
  unfold refDataValid
  split
  · rfl
  · split
    · rfl
    · simp only [hB, borrowPermAllows, hPerm, Bool.false_and]

/-- A `.frozen` borrow tag is never a valid mutable reference. -/
theorem refDataValid_frozen_mut
    (ptrBytes : Nat) (e : ProtoVTableEntry) (p : ProvenancePtr)
    (locals : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (b : BorrowEntry)
    (hB : lookupBorrow mem.borrows p.tag = some b) (hPerm : b.perm = .frozen) :
    refDataValid ptrBytes e true p locals mem localDecls layouts = false := by
  unfold refDataValid
  split
  · rfl
  · split
    · rfl
    · simp only [hB, borrowPermAllows, hPerm, Bool.not_true, Bool.false_and]

/-- A borrow tag whose strict ancestor in the Tree Borrows hierarchy forbids
the access (e.g. a `.disabled` parent tag, or a `.frozen` parent tag for a
mutable reference) is never a valid reference. -/
theorem refDataValid_ancestor_ub
    (ptrBytes : Nat) (e : ProtoVTableEntry) (dstMut : Bool) (p : ProvenancePtr)
    (locals : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (b : BorrowEntry)
    (hB : lookupBorrow mem.borrows p.tag = some b)
    (hAnc : treeBorrowAncestorsChildAccessUB (refAccessKind dstMut) mem.borrows b.parentTag = true) :
    refDataValid ptrBytes e dstMut p locals mem localDecls layouts = false := by
  unfold refDataValid
  split
  · rfl
  · split
    · rfl
    · simp only [hB, hAnc, Bool.not_true, Bool.and_false]

/-- A reference to an uninhabited concrete type is never valid (`kani#5216`). -/
theorem refDataValid_uninhabited
    (ptrBytes : Nat) (e : ProtoVTableEntry) (dstMut : Bool) (p : ProvenancePtr)
    (locals : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (hU : e.isUninhabited = true) :
    refDataValid ptrBytes e dstMut p locals mem localDecls layouts = false := by
  unfold refDataValid
  split
  · rfl
  · simp only [hU, Bool.not_true, Bool.and_false]

/-- A null, out-of-address-space, or misaligned address is never a valid reference. -/
theorem refDataValid_null_or_misaligned
    (ptrBytes : Nat) (e : ProtoVTableEntry) (dstMut : Bool) (p : ProvenancePtr)
    (locals : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (addr : Nat)
    (hAddr : ptrAddress? locals mem.borrows mem.callerLocals localDecls layouts ptrBytes p
      mem.callStack = some addr)
    (hBad : addr = 0 ∨ addr % e.alignBytes ≠ 0 ∨ Nat.blt addr (scalarModulus ptrBytes) = false) :
    refDataValid ptrBytes e dstMut p locals mem localDecls layouts = false := by
  unfold refDataValid
  rw [hAddr]
  have hc :
      (isPow2 e.alignBytes && Nat.blt addr (scalarModulus ptrBytes) &&
        !Nat.beq addr 0 && Nat.beq (addr % e.alignBytes) 0 && !e.isUninhabited) = false := by
    rcases hBad with h0 | hA | hOob
    · subst h0; simp
    · have : Nat.beq (addr % e.alignBytes) 0 = false := by
        cases hb : Nat.beq (addr % e.alignBytes) 0 with
        | false => rfl
        | true => exact absurd (Nat.eq_of_beq_eq_true hb) hA
      rw [this]; simp
    · rw [hOob]; simp
  simp only [hc]

/-- A non-zero-sized pointer (or non-zero `allocId` dangling pointer) with no
borrow entry and no global allocation is never a valid reference. -/
theorem refDataValid_no_allocation
    (ptrBytes : Nat) (e : ProtoVTableEntry) (dstMut : Bool) (p : ProvenancePtr)
    (locals : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (hB : lookupBorrow mem.borrows p.tag = none)
    (hG : lookupGlobalAlloc mem.globals p.allocId = none)
    (hNotZst : Nat.beq e.sizeBytes 0 = false ∨ Nat.beq p.allocId 0 = false) :
    refDataValid ptrBytes e dstMut p locals mem localDecls layouts = false := by
  unfold refDataValid
  split
  · rfl
  · split
    · rfl
    · simp only [hB, hG]
      rcases hNotZst with hSz | hId
      · rw [hSz]; rfl
      · rw [hId]; simp

/-- **Valid dangling ZST reference** (matching `Places.lean:14620` and MiniRust
`check_ptr`): a dangling `allocId = 0` pointer with non-null, in-bounds, aligned
`offsetBytes` to an inhabited zero-sized concrete type passes `refDataValid`. -/
theorem refDataValid_zst_dangling_ptr
    (ptrBytes : Nat) (e : ProtoVTableEntry) (dstMut : Bool) (off : Nat)
    (locals : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (hB : lookupBorrow mem.borrows 0 = none)
    (hG : lookupGlobalAlloc mem.globals 0 = none)
    (hPow : isPow2 e.alignBytes = true)
    (hSz : e.sizeBytes = 0)
    (hInh : e.isUninhabited = false)
    (hNz : Nat.beq off 0 = false)
    (hBound : Nat.blt off (scalarModulus ptrBytes) = true)
    (hAlign : Nat.beq (off % e.alignBytes) 0 = true) :
    refDataValid ptrBytes e dstMut { allocId := 0, offsetBytes := off }
      locals mem localDecls layouts = true := by
  unfold refDataValid
  have hAddr :
      ptrAddress? locals mem.borrows mem.callerLocals localDecls layouts ptrBytes
        { allocId := 0, offsetBytes := off } mem.callStack = some off := by
    simp only [ptrAddress?, ProvenancePtr.tag, hB]
    exact congrArg some (Nat.zero_add off)
  rw [hAddr]
  simp only [hPow, hBound, hNz, hAlign, hInh, hSz, hB, hG, ProvenancePtr.tag, Nat.beq_refl,
    Bool.not_false, Bool.and_true]

/-- An out-of-bounds referent in a global allocation is never a valid
reference. -/
theorem refDataValid_global_out_of_bounds
    (ptrBytes : Nat) (e : ProtoVTableEntry) (dstMut : Bool) (p : ProvenancePtr)
    (locals : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (alloc : CapturedAllocation)
    (hB : lookupBorrow mem.borrows p.tag = none)
    (hG : lookupGlobalAlloc mem.globals p.allocId = some alloc)
    (hOob : Nat.ble (p.offsetBytes + e.sizeBytes) (length alloc.bytes) = false) :
    refDataValid ptrBytes e dstMut p locals mem localDecls layouts = false := by
  unfold refDataValid
  split
  · rfl
  · split
    · rfl
    · simp only [hB, hG, hOob, Bool.and_false]

/-- The vtable pointer of a captured entry resolves to an entry with the same
allocation whenever lookup by allocation finds one for the right trait. -/
theorem resolveVTablePtr_ok_iff
    (vt : ProtoVTableTable) (pred : ProtoTraitPred) (vtPtr : ProvenancePtr)
    (e : ProtoVTableEntry) :
    resolveVTablePtr vt pred vtPtr = .ok e ↔
      (vtPtr.offsetBytes = 0 ∧ lookupVTableByAlloc vt.entries vtPtr.allocId = some e ∧
        traitPredEq e.traitPred pred = true) := by
  unfold resolveVTablePtr
  constructor
  · intro h
    cases hOff : Nat.beq vtPtr.offsetBytes 0 with
    | false => rw [hOff] at h; cases h
    | true =>
      rw [hOff] at h
      cases hL : lookupVTableByAlloc vt.entries vtPtr.allocId with
      | none => rw [hL] at h; cases h
      | some e' =>
        rw [hL] at h
        cases hT : traitPredEq e'.traitPred pred with
        | false => simp [hT] at h
        | true =>
          have h' : VTableResolution.ok e' = VTableResolution.ok e := by
            simpa only [hT] using h
          cases h'
          exact ⟨Nat.eq_of_beq_eq_true hOff, rfl, hT⟩
  · rintro ⟨hOff, hL, hT⟩
    rw [hOff, hL]
    simp only [hT]

/-- A vtable pointer with a non-zero offset is `InvalidVTablePointer`. -/
theorem resolveVTablePtr_offset_invalid
    (vt : ProtoVTableTable) (pred : ProtoTraitPred) (vtPtr : ProvenancePtr)
    (h : Nat.beq vtPtr.offsetBytes 0 = false) :
    resolveVTablePtr vt pred vtPtr = .invalidPointer := by
  unfold resolveVTablePtr
  rw [h]

/-- A pointer into an allocation that is not a captured vtable (null, a data
allocation, a function pointer) is `InvalidVTablePointer`. -/
theorem resolveVTablePtr_unknown_alloc_invalid
    (vt : ProtoVTableTable) (pred : ProtoTraitPred) (vtPtr : ProvenancePtr)
    (h : lookupVTableByAlloc vt.entries vtPtr.allocId = none) :
    resolveVTablePtr vt pred vtPtr = .invalidPointer := by
  unfold resolveVTablePtr
  split
  · rfl
  · rw [h]

/-- A vtable of another trait object type is `InvalidVTableTrait`. -/
theorem resolveVTablePtr_wrong_trait_invalid
    (vt : ProtoVTableTable) (pred : ProtoTraitPred) (vtPtr : ProvenancePtr)
    (e : ProtoVTableEntry)
    (hOff : Nat.beq vtPtr.offsetBytes 0 = true)
    (hL : lookupVTableByAlloc vt.entries vtPtr.allocId = some e)
    (hT : traitPredEq e.traitPred pred = false) :
    resolveVTablePtr vt pred vtPtr = .invalidTrait := by
  unfold resolveVTablePtr
  rw [hOff, hL]
  simp only [hT]

/-- **No arbitrary marker-trait upcast.** If an entry has neither a `.traitVPtr`
slot targeting `dstPred` nor a declared `primarySuperVTable?`, `upcastVTable?`
returns `none` even if an unrelated 0-method marker trait vtable exists whose
header is a slot prefix of `e.slots`. -/
theorem upcastVTable?_rejects_unrelated_marker
    (es : List ProtoVTableEntry) (e : ProtoVTableEntry) (dstPred : ProtoTraitPred)
    (hNoVPtr : findSupertraitVPtr es dstPred e.slots = none)
    (hNoPrim : e.primarySuperVTable? = none) :
    upcastVTable? es e dstPred = none := by
  unfold upcastVTable?
  rw [hNoVPtr]
  cases hLen : length es with
  | zero => rfl
  | succ n => simp only [findPrimarySuperVTable, hNoPrim]

/-- **No auto-trait fabrication, fail closed.** Upcasting or coercing a valid
`dyn srcPred` pointer to `dyn dstPred` when `dstPred` adds an auto trait absent
from `srcPred` (e.g. `&dyn Trait -> &dyn Trait + Send`) is `.unsupported`:
never `.ok` (no fabricated `Send`), never `.ub` (the MIR is ill typed, and
vendored Miri runs it without UB). -/
theorem unsizeDynToDyn_forbids_auto_trait_fabrication
    (vt : ProtoVTableTable) (ptrBytes : Nat) (srcKind : ProtoPtrKind) (dstMut : Bool)
    (srcPred dstPred : ProtoTraitPred) (v : Value) (d : ProtoDataWord) (vtPtr : ProvenancePtr)
    (e : ProtoVTableEntry)
    (locals : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (hDec : decodeWidePtr? ptrBytes v = some ⟨d, .vtable vtPtr⟩)
    (hRes : resolveVTablePtr vt srcPred vtPtr = .ok e)
    (hAuto : autoTraitsSubset dstPred.autoTraits srcPred.autoTraits = false) :
    unsizeDynToDyn vt ptrBytes srcKind dstMut srcPred dstPred v locals mem localDecls layouts =
      .unsupported := by
  unfold unsizeDynToDyn
  simp only [hDec, hRes, hAuto]

theorem wrapScalarBits_zero (m : Nat) : wrapScalarBits 0 m = 0 := by
  unfold wrapScalarBits
  cases Nat.ble m 0
  · rfl
  · exact Nat.zero_mod m

/-- **Wrapped-null rejection on 32-bit/64-bit ZST reference upcast.** A
provenance-less scalar address whose value wraps to `0` modulo `2^(8 * ptrBytes)`
(e.g. `2^32` on 32-bit targets) is UB when coerced as a reference even for a
zero-sized concrete type. -/
theorem unsizeDynToDyn_zst_wrapped_null_ub
    (vt : ProtoVTableTable) (ptrBytes : Nat) (dstMut : Bool)
    (srcPred dstPred : ProtoTraitPred) (bits : Nat) (vtPtr : ProvenancePtr)
    (locals : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (hWrap : wrapScalarBits bits (scalarModulus ptrBytes) = 0) :
    unsizeDynToDyn vt ptrBytes .ref dstMut srcPred dstPred
        (.aggregate 0 [.scalar ⟨bits, ptrBytes⟩, .ptr vtPtr ptrBytes])
        locals mem localDecls layouts = .ub ∨
    unsizeDynToDyn vt ptrBytes .ref dstMut srcPred dstPred
        (.aggregate 0 [.scalar ⟨bits, ptrBytes⟩, .ptr vtPtr ptrBytes])
        locals mem localDecls layouts = .unsupported := by
  unfold unsizeDynToDyn
  have hDec :
      decodeWidePtr? ptrBytes (.aggregate 0 [.scalar ⟨bits, ptrBytes⟩, .ptr vtPtr ptrBytes]) =
        some ⟨.addr bits, .vtable vtPtr⟩ := by
    simp only [decodeWidePtr?, decodeDataWord?, Nat.beq_refl]
  simp only [hDec]
  cases hRes : resolveVTablePtr vt srcPred vtPtr with
  | invalidPointer => exact Or.inl rfl
  | invalidTrait => exact Or.inl rfl
  | ok e =>
    dsimp only
    cases hAuto : autoTraitsSubset dstPred.autoTraits srcPred.autoTraits with
    | false => exact Or.inr rfl
    | true =>
      dsimp only
      cases (match traitPredEq srcPred dstPred with
             | true => some e
             | false => upcastVTable? vt.entries e dstPred) with
      | none => exact Or.inr rfl
      | some target =>
        left
        simp only [wrapDataWord, hWrap, refAddrValid, wrapScalarBits_zero,
          Nat.beq_refl, Bool.not_true, Bool.and_false, Bool.false_and]

/-- **Invalid incoming vtable pointer (`lean-miri#75/#79/#82`, `kani#5216`).**
Upcasting a trait-object pointer whose vtable pointer does not resolve for the
source trait object type is UB, for raw pointers and references alike. -/
theorem unsizeDynToDyn_invalid_vtable_ub
    (vt : ProtoVTableTable) (ptrBytes : Nat) (srcKind : ProtoPtrKind) (dstMut : Bool)
    (srcPred dstPred : ProtoTraitPred) (v : Value) (d : ProtoDataWord) (vtPtr : ProvenancePtr)
    (locals : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (hDec : decodeWidePtr? ptrBytes v = some ⟨d, .vtable vtPtr⟩)
    (hBad : ∀ e, resolveVTablePtr vt srcPred vtPtr ≠ .ok e) :
    unsizeDynToDyn vt ptrBytes srcKind dstMut srcPred dstPred v locals mem localDecls layouts =
      .ub := by
  unfold unsizeDynToDyn
  simp only [hDec]
  cases hR : resolveVTablePtr vt srcPred vtPtr with
  | ok e => exact absurd hR (hBad e)
  | invalidPointer => rfl
  | invalidTrait => rfl

/-- A source that is not a trait-object pointer with a vtable-pointer word (a
thin pointer, or a pair whose metadata is a slice length or a dangling integer)
is UB to upcast. -/
theorem unsizeDynToDyn_non_vtable_meta_ub
    (vt : ProtoVTableTable) (ptrBytes : Nat) (srcKind : ProtoPtrKind) (dstMut : Bool)
    (srcPred dstPred : ProtoTraitPred) (v : Value)
    (locals : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (hDec : ∀ d vtPtr, decodeWidePtr? ptrBytes v ≠ some ⟨d, .vtable vtPtr⟩) :
    unsizeDynToDyn vt ptrBytes srcKind dstMut srcPred dstPred v locals mem localDecls layouts =
      .ub := by
  unfold unsizeDynToDyn
  split
  · rename_i d vtPtr heq
    exact absurd heq (hDec d vtPtr)
  · rfl

/-! ## §4. Vtable-backed dynamic layout (`size_of_val` / `align_of_val`) -/

/-- Result of a prototype rule that returns a plain value. -/
inductive ProtoRes (α : Type) : Type where
  | ok (val : α)
  | ub
  | unsupported

/-- Size and alignment of the value behind a pointer `v` to the trait object
type `pred`, read from the vtable only.

The pointer must decode at width `ptrBytes` with a vtable-pointer word; a thin
pointer, a non-pointer, a slice length or dangling integer in the metadata
word, a non-zero vtable offset, a non-vtable allocation, and a vtable of
another trait are all UB. The data word is never inspected: this is
`size_of_val_raw` on `*const dyn Trait`, which does not dereference the data
pointer. -/
def dynLayoutOfValProto (vt : ProtoVTableTable) (ptrBytes : Nat) (pred : ProtoTraitPred)
    (v : Value) : ProtoRes (Nat × Nat) :=
  match pred.failsClosed with
  | true => .unsupported
  | false =>
    match wfProtoVTableTable ptrBytes vt with
    | false => .unsupported
    | true =>
      match decodeWidePtr? ptrBytes v with
      | some ⟨_, .vtable vtPtr⟩ =>
        match resolveVTablePtr vt pred vtPtr with
        | .ok e =>
          match entryLayoutOk ptrBytes e with
          | true => .ok (e.sizeBytes, e.alignBytes)
          | false => .ub
        | .invalidPointer => .ub
        | .invalidTrait => .ub
      | _ => .ub

/-- `size_of_val` on a pointer to the trait object type `pred`. -/
def dynSizeOfValProto (vt : ProtoVTableTable) (ptrBytes : Nat) (pred : ProtoTraitPred)
    (v : Value) : ProtoRes Nat :=
  match dynLayoutOfValProto vt ptrBytes pred v with
  | .ok (size, _) => .ok size
  | .ub => .ub
  | .unsupported => .unsupported

/-- `align_of_val` on a pointer to the trait object type `pred`. -/
def dynAlignOfValProto (vt : ProtoVTableTable) (ptrBytes : Nat) (pred : ProtoTraitPred)
    (v : Value) : ProtoRes Nat :=
  match dynLayoutOfValProto vt ptrBytes pred v with
  | .ok (_, align) => .ok align
  | .ub => .ub
  | .unsupported => .unsupported

/-- An entry of a well-formed table has a valid layout. -/
theorem allEntriesWf_lookupByAlloc {ptrBytes : Nat} {es : List ProtoVTableEntry} :
    ∀ {es' : List ProtoVTableEntry} {a : Nat} {e : ProtoVTableEntry},
      allEntriesWf ptrBytes es es' = true → lookupVTableByAlloc es' a = some e →
        wfProtoVTableEntry ptrBytes es e = true
  | [], _, _, _, h => by cases h
  | x :: rest, a, e, hWf, h => by
    have hWf' : (wfProtoVTableEntry ptrBytes es x && allEntriesWf ptrBytes es rest) = true := hWf
    have h' : (match Nat.beq x.vtableAllocId a with
               | true => some x
               | false => lookupVTableByAlloc rest a) = some e := h
    cases hx : wfProtoVTableEntry ptrBytes es x with
    | false => rw [hx] at hWf'; cases hWf'
    | true =>
      rw [hx] at hWf'
      cases ha : Nat.beq x.vtableAllocId a with
      | true => rw [ha] at h'; cases h'; exact hx
      | false => rw [ha] at h'; exact allEntriesWf_lookupByAlloc hWf' h'

theorem wfProtoVTableTable_allEntriesWf {ptrBytes : Nat} {vt : ProtoVTableTable}
    (h : wfProtoVTableTable ptrBytes vt = true) :
    allEntriesWf ptrBytes vt.entries vt.entries = true := by
  unfold wfProtoVTableTable at h
  cases hA : allEntriesWf ptrBytes vt.entries vt.entries with
  | true => rfl
  | false => rw [hA] at h; cases h

theorem wfProtoVTableEntry_layoutOk {ptrBytes : Nat} {es : List ProtoVTableEntry}
    {e : ProtoVTableEntry} (h : wfProtoVTableEntry ptrBytes es e = true) :
    entryLayoutOk ptrBytes e = true := by
  unfold wfProtoVTableEntry at h
  cases hL : entryLayoutOk ptrBytes e with
  | true => rfl
  | false => rw [hL] at h; cases h

/-- **Dynamic layout from the vtable.** On a well-formed table, a pointer whose
vtable pointer resolves for `pred` has exactly the size and alignment of the
resolved vtable entry, whatever its data word is. -/
theorem dynLayoutOfValProto_ok
    (vt : ProtoVTableTable) (ptrBytes : Nat) (pred : ProtoTraitPred) (v : Value)
    (d : ProtoDataWord) (vtPtr : ProvenancePtr) (e : ProtoVTableEntry)
    (hPred : pred.failsClosed = false)
    (hWf : wfProtoVTableTable ptrBytes vt = true)
    (hDec : decodeWidePtr? ptrBytes v = some ⟨d, .vtable vtPtr⟩)
    (hRes : resolveVTablePtr vt pred vtPtr = .ok e) :
    dynLayoutOfValProto vt ptrBytes pred v = .ok (e.sizeBytes, e.alignBytes) ∧
    dynSizeOfValProto vt ptrBytes pred v = .ok e.sizeBytes ∧
    dynAlignOfValProto vt ptrBytes pred v = .ok e.alignBytes := by
  have hL : entryLayoutOk ptrBytes e = true :=
    wfProtoVTableEntry_layoutOk
      (allEntriesWf_lookupByAlloc (wfProtoVTableTable_allEntriesWf hWf)
        ((resolveVTablePtr_ok_iff vt pred vtPtr e).mp hRes).2.1)
  have h1 : dynLayoutOfValProto vt ptrBytes pred v = .ok (e.sizeBytes, e.alignBytes) := by
    unfold dynLayoutOfValProto
    simp only [hPred, hWf, hDec, hRes, hL]
  refine ⟨h1, ?_, ?_⟩
  · unfold dynSizeOfValProto; rw [h1]
  · unfold dynAlignOfValProto; rw [h1]

/-- **`size_of_val_raw` does not dereference the data pointer.** The dynamic
layout of a trait-object pointer depends only on its vtable word: any two data
words (valid, null, dangling, misaligned, provenance-less) give the same
result. -/
theorem dynLayoutOfValProto_data_independent
    (vt : ProtoVTableTable) (ptrBytes : Nat) (pred : ProtoTraitPred)
    (d d' : ProtoDataWord) (vtPtr : ProvenancePtr) :
    dynLayoutOfValProto vt ptrBytes pred (encodeWidePtr ptrBytes ⟨d, .vtable vtPtr⟩) =
      dynLayoutOfValProto vt ptrBytes pred (encodeWidePtr ptrBytes ⟨d', .vtable vtPtr⟩) := by
  unfold dynLayoutOfValProto
  simp only [decodeWidePtr?_encodeWidePtr]

/-- Invalid vtable pointer (non-zero offset, non-vtable allocation) or a vtable
of another trait: dynamic layout is UB. -/
theorem dynLayoutOfValProto_invalid_vtable_ub
    (vt : ProtoVTableTable) (ptrBytes : Nat) (pred : ProtoTraitPred) (v : Value)
    (d : ProtoDataWord) (vtPtr : ProvenancePtr)
    (hPred : pred.failsClosed = false)
    (hWf : wfProtoVTableTable ptrBytes vt = true)
    (hDec : decodeWidePtr? ptrBytes v = some ⟨d, .vtable vtPtr⟩)
    (hBad : ∀ e, resolveVTablePtr vt pred vtPtr ≠ .ok e) :
    dynLayoutOfValProto vt ptrBytes pred v = .ub ∧
    dynSizeOfValProto vt ptrBytes pred v = .ub ∧
    dynAlignOfValProto vt ptrBytes pred v = .ub := by
  have h1 : dynLayoutOfValProto vt ptrBytes pred v = .ub := by
    unfold dynLayoutOfValProto
    simp only [hPred, hWf, hDec]
    cases hR : resolveVTablePtr vt pred vtPtr with
    | ok e => exact absurd hR (hBad e)
    | invalidPointer => rfl
    | invalidTrait => rfl
  refine ⟨h1, ?_, ?_⟩
  · unfold dynSizeOfValProto; rw [h1]
  · unfold dynAlignOfValProto; rw [h1]

/-- A value without a vtable-pointer metadata word (a thin pointer, a
non-pointer scalar of the wrong width, `uninit`, or a pair whose metadata is a
slice length or a provenance-less dangling integer): dynamic layout is UB. -/
theorem dynLayoutOfValProto_non_vtable_meta_ub
    (vt : ProtoVTableTable) (ptrBytes : Nat) (pred : ProtoTraitPred) (v : Value)
    (hPred : pred.failsClosed = false)
    (hWf : wfProtoVTableTable ptrBytes vt = true)
    (hDec : ∀ d vtPtr, decodeWidePtr? ptrBytes v ≠ some ⟨d, .vtable vtPtr⟩) :
    dynLayoutOfValProto vt ptrBytes pred v = .ub := by
  unfold dynLayoutOfValProto
  rw [hPred, hWf]
  dsimp only
  split
  · rename_i d vtPtr heq
    exact absurd heq (hDec _ vtPtr)
  · rfl

/-- An unresolved existential binder or undischarged outlives obligation makes
dynamic layout fail closed. -/
theorem dynLayoutOfValProto_failsClosed
    (vt : ProtoVTableTable) (ptrBytes : Nat) (pred : ProtoTraitPred) (v : Value)
    (hPred : pred.failsClosed = true) :
    dynLayoutOfValProto vt ptrBytes pred v = .unsupported := by
  unfold dynLayoutOfValProto
  simp only [hPred]

/-! ## §5. Virtual method dispatch and the Tree Borrows receiver protector -/

/-- A virtual call site (`InstanceKind::Virtual(def_id, idx)`): the trait
object type of the receiver, the vtable slot index, whether the receiver is
a reference (`&dyn Trait`, `&mut dyn Trait`) or a raw pointer / other
`DispatchFromDyn` receiver, and (when a reference) whether it is mutable. -/
structure ProtoVirtualCallSite : Type where
  traitPred : ProtoTraitPred
  slotIdx : Nat
  receiverIsRef : Bool
  receiverIsMut : Bool := false

/-- Outcome of resolving and entering a virtual call. -/
inductive ProtoVirtualCallResult : Type where
  /-- The concrete callee frame is pushed. `protectedTag` is the retagged
  receiver tag carrying the call-frame protector (reference receivers). -/
  | enter (state : MachineState) (callee : CapturedMir) (protectedTag : Option Nat)
  /-- The concrete method body is not linked: an external call request with the
  receiver already narrowed. -/
  | externalCall (defPath : DefPath) (args : List Value) (locals : List LocalSlot)
  | ub
  | unsupported

/-- Unwrap a `DispatchFromDyn` receiver: a trait-object pointer, or a wrapper
aggregate with exactly one field that is not a zero-sized `unit`
(`VirtualCalls.receiverPlace` / `nonOneZstField`). -/
def unwrapDispatchReceiver (ptrBytes : Nat) : Nat → Value → Option ProtoWidePtr
  | 0, _ => none
  | fuel + 1, v =>
    match decodeWidePtr? ptrBytes v with
    | some w => some w
    | none =>
      match v with
      | .aggregate _ fields =>
        match fields.filter (fun f => match f with | .unit => false | _ => true) with
        | [inner] => unwrapDispatchReceiver ptrBytes fuel inner
        | _ => none
      | _ => none

/-- Receiver mutability compatibility between the virtual call site and the
concrete callee's `_1` parameter: an immutable `&dyn Trait` call site cannot
dispatch to a callee expecting `&mut Self`. -/
def virtualCalleeReceiverOk (site : ProtoVirtualCallSite) (callee : CapturedMir) : Bool :=
  match site.receiverIsRef, site.receiverIsMut, get? callee.localDecls 1 with
  | true, false, some { ty := { kind := .ref .mut _, .. }, .. } => false
  | _, _, _ => true

/-- ABI validation of the concrete callee against the call: not an intrinsic
ABI, the same argument count, compatible receiver mutability, and (when the ABI
is captured) a pointer-sized thin receiver. -/
def virtualCalleeAbiOk (ptrBytes : Nat) (site : ProtoVirtualCallSite) (callee : CapturedMir)
    (argCount : Nat) : Bool :=
  !callConvEq callee.fnAbi.conv .rustIntrinsic && Nat.beq callee.argCount argCount &&
    virtualCalleeReceiverOk site callee &&
    (match callee.fnAbi.args with
     | [] => true
     | recvAbi :: _ =>
       Nat.beq (length callee.fnAbi.args) argCount &&
         Nat.beq recvAbi.layout.size.bytes ptrBytes)

/-- Return ABI compatibility: for non-diverging calls, when the destination
type has a known size and the callee ABI is captured, the sizes agree. -/
def virtualRetAbiOk (callerBody callee : CapturedMir) (destination : Place)
    (target : Option BasicBlockIdx := some 0) : Bool :=
  match target with
  | none => true
  | some _ =>
    match callee.fnAbi.args, placeTy callerBody.localDecls callerBody.layouts destination with
    | _ :: _, some dstTy =>
      match tyByteSize callerBody.localDecls callerBody.layouts dstTy with
      | some n => Nat.beq n callee.fnAbi.ret.layout.size.bytes
      | none => true
    | _, _ => true

/-- **Step 4: receiver call-frame protector.** After the callee frame is
pushed, retag the narrowed receiver `_1` with `Trusted`'s own function-entry
retag (`evalFnEntryRetag`): the callee receives a fresh child tag of the
caller's borrow tag, protected by a fresh protector in
`Memory.activeProtectors`. The retag statement index advance is undone, so the
callee still starts at its first statement. A receiver whose tag has no borrow
entry (a global referent) is entered without a protector. -/
def protectVirtualReceiver (s1 : MachineState) (callee : CapturedMir) (p : ProvenancePtr)
    (ptrBytes : Nat) : ProtoVirtualCallResult :=
  match lookupBorrow s1.memory.borrows p.tag with
  | none => .enter s1 callee none
  | some parentEntry =>
    match parentEntry.perm with
    | .disabled => .ub
    | _ =>
      match
        evalFnEntryRetag s1 callee.localDecls callee.layouts { local_ := 1, projection := [] } p
          ptrBytes parentEntry s1.frame.locals
      with
      | .tau (.running s2) =>
        .enter { s2 with frame := { s2.frame with stmtIdx := 0 } } callee
          (match lookupBorrow s2.memory.borrows s1.memory.nextTag with
           | some _ => some s1.memory.nextTag
           | none => none)
      | .vis (.inl (.fail .ub)) _ => .ub
      | _ => .unsupported

/-- Reference-receiver validity check performed before callee dispatch (for
both linked and unlinked callees): enforces `site.receiverIsMut` (rejecting
`.frozen` tags and immutable globals on `&mut dyn Trait` calls) and ZST
validity for provenance-less addresses. -/
def virtualReceiverValid
    (ptrBytes : Nat) (site : ProtoVirtualCallSite) (e : ProtoVTableEntry) (d : ProtoDataWord)
    (locals' : List LocalSlot) (mem : Memory) (callerBody : CapturedMir) : Bool :=
  match site.receiverIsRef, d with
  | false, _ => true
  | true, .prov p =>
    refDataValid ptrBytes e site.receiverIsMut p locals' mem callerBody.localDecls
      callerBody.layouts
  | true, .addr bits => refAddrValid ptrBytes e bits

/-- **`evalVirtualCallProtoOpt`** (supporting both returning `target = some bb`
and diverging `target = none` calls).

1. *Argument initialization gate (`kani#5172`).* The receiver and all
   arguments are evaluated first; a UB operand (dead local, uninitialized read)
   or an evaluated value containing `uninit` is UB before the vtable or the
   callee is looked at.
2. *Vtable and slot resolution.* The receiver must be a trait-object pointer
   whose vtable pointer resolves for the site's trait object type; the slot
   must be a method, otherwise the call is UB ("dyn call trying to call
   something that is not a method").
3. *Receiver validity, narrowing, and ABI validation.* A reference receiver is
   validated with `site.receiverIsMut` (`refDataValid` / `refAddrValid`) BEFORE
   callee lookup, so even unlinked calls fault UB on invalid `&dyn`/`&mut dyn`
   receivers. Argument `0` becomes the thin data word (allocation, offset, and
   tag preserved); linked callees must pass ABI and receiver-mutability checks.
4. *Receiver protector.* A reference receiver is retagged under a fresh
   call-frame protector (`protectVirtualReceiver`). -/
def evalVirtualCallProtoOpt
    (vt : ProtoVTableTable) (site : ProtoVirtualCallSite) (s : MachineState)
    (callerBody : CapturedMir) (argOps : List Operand) (destination : Place)
    (target : Option BasicBlockIdx) (unwind : UnwindAction) : ProtoVirtualCallResult :=
  let layouts := callerBody.layouts
  let ptrBytes := layoutPointerBytes layouts
  match
    evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals layouts
      s.memory.callerLocals (callStack := s.memory.callStack)
  with
  | .ub => .ub
  | .unsupported => .unsupported
  | .ok argVals locals' =>
    match valueListContainsUninit argVals with
    | true => .ub
    | false =>
      match site.traitPred.failsClosed with
      | true => .unsupported
      | false =>
        match vtableEnvOk ptrBytes vt s.memory with
        | false => .unsupported
        | true =>
          match argVals with
          | [] => .ub
          | recv :: rest =>
            match unwrapDispatchReceiver ptrBytes 4 recv with
            | some ⟨d, .vtable vtPtr⟩ =>
              match resolveVTablePtr vt site.traitPred vtPtr with
              | .invalidPointer => .ub
              | .invalidTrait => .ub
              | .ok e =>
                match get? e.slots site.slotIdx with
                | some (.method defPath) =>
                  let d' := wrapDataWord ptrBytes d
                  match virtualReceiverValid ptrBytes site e d' locals' s.memory callerBody with
                  | false => .ub
                  | true =>
                    let thinRecv := encodeDataWord ptrBytes d'
                    match lookupCallee s.memory.callees layouts defPath [] s.memory.traitImpls with
                    | none => .externalCall defPath (thinRecv :: rest) locals'
                    | some callee =>
                      match
                        virtualCalleeAbiOk ptrBytes site callee (length argVals) &&
                          virtualRetAbiOk callerBody callee destination target
                      with
                      | false => .ub
                      | true =>
                        let s1 :=
                          match target with
                          | some bb =>
                            pushCalleeFrame s callerBody locals' destination bb callee
                              (thinRecv :: rest) unwind
                          | none =>
                            pushDivergingCalleeFrame s callerBody locals' destination unwind callee
                              (thinRecv :: rest)
                        match site.receiverIsRef, d' with
                        | true, .prov p => protectVirtualReceiver s1 callee p ptrBytes
                        | _, _ => .enter s1 callee none
                | _ => .ub
            | _ => .ub

/-- **`evalVirtualCallProto`** for returning virtual calls (`target : BasicBlockIdx`). -/
def evalVirtualCallProto
    (vt : ProtoVTableTable) (site : ProtoVirtualCallSite) (s : MachineState)
    (callerBody : CapturedMir) (argOps : List Operand) (destination : Place)
    (target : BasicBlockIdx) (unwind : UnwindAction) : ProtoVirtualCallResult :=
  evalVirtualCallProtoOpt vt site s callerBody argOps destination (some target) unwind

/-- **Uninitialized argument gate (`kani#5172`).** If evaluating the arguments
is UB, the virtual call is UB whatever the vtable table, the site, and the
linked callees are. -/
theorem evalVirtualCallProto_operand_ub
    (vt : ProtoVTableTable) (site : ProtoVirtualCallSite) (s : MachineState)
    (callerBody : CapturedMir) (argOps : List Operand) (destination : Place)
    (target : BasicBlockIdx) (unwind : UnwindAction)
    (hOps : evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals
      callerBody.layouts s.memory.callerLocals (callStack := s.memory.callStack) = .ub) :
    evalVirtualCallProto vt site s callerBody argOps destination target unwind = .ub := by
  unfold evalVirtualCallProto evalVirtualCallProtoOpt
  simp only [hOps]

/-- **Uninitialized argument gate, value form.** If any evaluated argument (the
receiver or a trailing argument) contains `uninit`, the virtual call is UB even
when the trait predicate fails closed, the vtable table is ill formed, or the
callee is not linked. -/
theorem evalVirtualCallProto_uninit_arg_ub
    (vt : ProtoVTableTable) (site : ProtoVirtualCallSite) (s : MachineState)
    (callerBody : CapturedMir) (argOps : List Operand) (destination : Place)
    (target : BasicBlockIdx) (unwind : UnwindAction) (argVals : List Value)
    (locals' : List LocalSlot)
    (hOps : evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals
      callerBody.layouts s.memory.callerLocals (callStack := s.memory.callStack) =
        .ok argVals locals')
    (hUninit : valueListContainsUninit argVals = true) :
    evalVirtualCallProto vt site s callerBody argOps destination target unwind = .ub := by
  unfold evalVirtualCallProto evalVirtualCallProtoOpt
  simp only [hOps, hUninit]

/-- **Fail-closed existential boundary at a call.** With initialized
arguments, a trait predicate with an unresolved existential binder or
undischarged outlives obligations makes the call `.unsupported`. -/
theorem evalVirtualCallProto_failsClosed
    (vt : ProtoVTableTable) (site : ProtoVirtualCallSite) (s : MachineState)
    (callerBody : CapturedMir) (argOps : List Operand) (destination : Place)
    (target : BasicBlockIdx) (unwind : UnwindAction) (argVals : List Value)
    (locals' : List LocalSlot)
    (hOps : evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals
      callerBody.layouts s.memory.callerLocals (callStack := s.memory.callStack) =
        .ok argVals locals')
    (hInit : valueListContainsUninit argVals = false)
    (hFail : site.traitPred.failsClosed = true) :
    evalVirtualCallProto vt site s callerBody argOps destination target unwind =
      .unsupported := by
  unfold evalVirtualCallProto evalVirtualCallProtoOpt
  simp only [hOps, hInit, hFail]

/-- **Non-method slot.** With initialized arguments and a receiver whose vtable
resolves to `e`, a slot index that is out of range or names a header, vacant,
or supertrait slot is UB. -/
theorem evalVirtualCallProto_non_method_slot_ub
    (vt : ProtoVTableTable) (site : ProtoVirtualCallSite) (s : MachineState)
    (callerBody : CapturedMir) (argOps : List Operand) (destination : Place)
    (target : BasicBlockIdx) (unwind : UnwindAction) (recv : Value) (rest : List Value)
    (locals' : List LocalSlot) (d : ProtoDataWord) (vtPtr : ProvenancePtr)
    (e : ProtoVTableEntry)
    (hOps : evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals
      callerBody.layouts s.memory.callerLocals (callStack := s.memory.callStack) =
        .ok (recv :: rest) locals')
    (hInit : valueListContainsUninit (recv :: rest) = false)
    (hFail : site.traitPred.failsClosed = false)
    (hEnv : vtableEnvOk (layoutPointerBytes callerBody.layouts) vt s.memory = true)
    (hRecv : unwrapDispatchReceiver (layoutPointerBytes callerBody.layouts) 4 recv =
      some ⟨d, .vtable vtPtr⟩)
    (hRes : resolveVTablePtr vt site.traitPred vtPtr = .ok e)
    (hSlot : ∀ defPath, get? e.slots site.slotIdx ≠ some (.method defPath)) :
    evalVirtualCallProto vt site s callerBody argOps destination target unwind = .ub := by
  unfold evalVirtualCallProto evalVirtualCallProtoOpt
  simp only [hOps, hInit, hFail, hEnv, hRecv, hRes]

/-- **Invalid vtable pointer at a call.** With initialized arguments, a
receiver whose vtable pointer does not resolve for the site's trait object type
(null, dangling, offset, non-vtable allocation, wrong trait) is UB. -/
theorem evalVirtualCallProto_invalid_vtable_ub
    (vt : ProtoVTableTable) (site : ProtoVirtualCallSite) (s : MachineState)
    (callerBody : CapturedMir) (argOps : List Operand) (destination : Place)
    (target : BasicBlockIdx) (unwind : UnwindAction) (recv : Value) (rest : List Value)
    (locals' : List LocalSlot) (d : ProtoDataWord) (vtPtr : ProvenancePtr)
    (hOps : evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals
      callerBody.layouts s.memory.callerLocals (callStack := s.memory.callStack) =
        .ok (recv :: rest) locals')
    (hInit : valueListContainsUninit (recv :: rest) = false)
    (hFail : site.traitPred.failsClosed = false)
    (hEnv : vtableEnvOk (layoutPointerBytes callerBody.layouts) vt s.memory = true)
    (hRecv : unwrapDispatchReceiver (layoutPointerBytes callerBody.layouts) 4 recv =
      some ⟨d, .vtable vtPtr⟩)
    (hBad : ∀ e, resolveVTablePtr vt site.traitPred vtPtr ≠ .ok e) :
    evalVirtualCallProto vt site s callerBody argOps destination target unwind = .ub := by
  unfold evalVirtualCallProto evalVirtualCallProtoOpt
  simp only [hOps, hInit, hFail, hEnv, hRecv]
  cases hR : resolveVTablePtr vt site.traitPred vtPtr with
  | ok e => exact absurd hR (hBad e)
  | invalidPointer => rfl
  | invalidTrait => rfl

/-- **Reference receiver validity precedes callee lookup.** An invalid
reference receiver (including a `&mut dyn Trait` call on a `.frozen` tag or
immutable global, or any invalid `&dyn Trait`) is UB even when the concrete
callee body is NOT linked (never `.externalCall`). -/
theorem evalVirtualCallProto_invalid_ref_before_callee_ub
    (vt : ProtoVTableTable) (site : ProtoVirtualCallSite) (s : MachineState)
    (callerBody : CapturedMir) (argOps : List Operand) (destination : Place)
    (target : BasicBlockIdx) (unwind : UnwindAction) (recv : Value) (rest : List Value)
    (locals' : List LocalSlot) (d : ProtoDataWord) (vtPtr : ProvenancePtr)
    (e : ProtoVTableEntry) (defPath : String)
    (hOps : evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals
      callerBody.layouts s.memory.callerLocals (callStack := s.memory.callStack) =
        .ok (recv :: rest) locals')
    (hInit : valueListContainsUninit (recv :: rest) = false)
    (hFail : site.traitPred.failsClosed = false)
    (hEnv : vtableEnvOk (layoutPointerBytes callerBody.layouts) vt s.memory = true)
    (hRecv : unwrapDispatchReceiver (layoutPointerBytes callerBody.layouts) 4 recv =
      some ⟨d, .vtable vtPtr⟩)
    (hRes : resolveVTablePtr vt site.traitPred vtPtr = .ok e)
    (hSlot : get? e.slots site.slotIdx = some (.method defPath))
    (hInvalid : virtualReceiverValid (layoutPointerBytes callerBody.layouts) site e
      (wrapDataWord (layoutPointerBytes callerBody.layouts) d) locals' s.memory callerBody =
        false) :
    evalVirtualCallProto vt site s callerBody argOps destination target unwind = .ub := by
  unfold evalVirtualCallProto evalVirtualCallProtoOpt
  simp only [hOps, hInit, hFail, hEnv, hRecv, hRes, hSlot, hInvalid]

/-- **Receiver narrowing.** When a valid receiver's method body is not linked,
the call is an external call whose first argument is the narrowed thin data word
(allocation, offset, and tag preserved; vtable word removed; trailing arguments
unchanged). -/
theorem evalVirtualCallProto_narrows_receiver
    (vt : ProtoVTableTable) (site : ProtoVirtualCallSite) (s : MachineState)
    (callerBody : CapturedMir) (argOps : List Operand) (destination : Place)
    (target : BasicBlockIdx) (unwind : UnwindAction) (recv : Value) (rest : List Value)
    (locals' : List LocalSlot) (d : ProtoDataWord) (vtPtr : ProvenancePtr)
    (e : ProtoVTableEntry) (defPath : String)
    (hOps : evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals
      callerBody.layouts s.memory.callerLocals (callStack := s.memory.callStack) =
        .ok (recv :: rest) locals')
    (hInit : valueListContainsUninit (recv :: rest) = false)
    (hFail : site.traitPred.failsClosed = false)
    (hEnv : vtableEnvOk (layoutPointerBytes callerBody.layouts) vt s.memory = true)
    (hRecv : unwrapDispatchReceiver (layoutPointerBytes callerBody.layouts) 4 recv =
      some ⟨d, .vtable vtPtr⟩)
    (hRes : resolveVTablePtr vt site.traitPred vtPtr = .ok e)
    (hSlot : get? e.slots site.slotIdx = some (.method defPath))
    (hValid : virtualReceiverValid (layoutPointerBytes callerBody.layouts) site e
      (wrapDataWord (layoutPointerBytes callerBody.layouts) d) locals' s.memory callerBody =
        true)
    (hCallee : lookupCallee s.memory.callees callerBody.layouts defPath []
      s.memory.traitImpls = none) :
    evalVirtualCallProto vt site s callerBody argOps destination target unwind =
      .externalCall defPath
        (encodeDataWord (layoutPointerBytes callerBody.layouts)
          (wrapDataWord (layoutPointerBytes callerBody.layouts) d) :: rest) locals' := by
  unfold evalVirtualCallProto evalVirtualCallProtoOpt
  simp only [hOps, hInit, hFail, hEnv, hRecv, hRes, hSlot, hValid, hCallee]

/-! ### Ranged Tree Borrows view of the receiver protector

`protectVirtualReceiver` registers the protector in `Memory.activeProtectors`.
The same event in `Anneal.RefFrame.RangedTree`: the owner of the receiver's
storage is the root, the caller's reference is its child, and the callee's
retagged receiver is the protected grandchild over the receiver's byte range.
-/

open Anneal.RefFrame in
/-- Ranged borrow tree of a virtual receiver before the function-entry retag:
`ownerTag` (the owner of the storage, `Unique`), `parentTag` (the caller's
reference, with permission `parentPerm`), and `childTag` (the callee's
receiver, initially `childPerm`, not yet accessed) over `[off, off + size)`.
`isProtected` selects a reference receiver (protected child) or a raw-pointer
receiver (no protector). -/
def receiverTree (ownerTag parentTag childTag off size : Nat)
    (parentPerm childPerm : TbPermission) (isProtected : Bool) : RangedBorrowTree :=
  { topology := [⟨ownerTag, none⟩, ⟨parentTag, some ownerTag⟩, ⟨childTag, some parentTag⟩]
    protectedTags := match isProtected with | true => [childTag] | false => []
    segments :=
      [⟨off, size,
        [(ownerTag, ⟨.Unique, true⟩), (parentTag, ⟨parentPerm, true⟩),
         (childTag, ⟨childPerm, false⟩)]⟩] }

open Anneal.RefFrame in
/-- Initial permission of the retagged receiver: `Frozen` for `&dyn Trait`,
`ReservedFrz false` for `&mut dyn Trait` (`fnEntryRetagPerm`). -/
def receiverChildPerm (isMut : Bool) : TbPermission :=
  match isMut with
  | false => .Frozen
  | true => .ReservedFrz false

open Anneal.RefFrame in
/-- Function-entry retag of the receiver: the initial reborrow read through the
child tag over the receiver range. -/
def receiverEnter (tree : RangedBorrowTree) (childTag off size : Nat) : RangedAccessResult :=
  performRangedAccess tree off size childTag .Read .VisitChildrenOfAccessed

open Anneal.RefFrame in
/-- A foreign access through `actorTag` (the owner or another alias of the
receiver's backing storage) to `[off, off + size)`. -/
def receiverForeignAccess (tree : RangedBorrowTree) (actorTag off size : Nat)
    (kind : TbAccessKind) : RangedAccessResult :=
  performRangedAccess tree off size actorTag kind .VisitChildrenOfAccessed

open Anneal.RefFrame in
/-- Return of the virtual call: release the receiver protector
(`exitFrameWithProtectors`). -/
def receiverExit (tree : RangedBorrowTree) (childTag : Nat) : ProtectorReleaseResult :=
  exitFrameWithProtectors tree [childTag]

open Anneal.RefFrame in
/-- Code of a transition error: `1` child access forbidden, `2` protected
disabled, `3` protected dealloc. -/
def tbErrCode : TbTransitionError → Nat
  | .ChildAccessForbidden _ => 1
  | .ProtectedDisabled _ => 2
  | .ProtectedDealloc => 3

open Anneal.RefFrame in
/-- Code of a ranged access status: `[0]` completed, `[1]` uncovered or
missing tag, `[2, offset, length, node, error]` transition error, `[3, ..]`
invariant failure. -/
def accessCode : RangedAccessStatus → List Nat
  | .Completed => [0]
  | .UncoveredOrMissingTag => [1]
  | .TransitionError o l t e => [2, o, l, t, tbErrCode e]
  | .InvariantFailure o l t => [3, o, l, t]

open Anneal.RefFrame in
/-- Code of a protector release status: `[0]` released, `[1, tag]` missing
tag, `[2, ..]` access failure, `[3, ..]` invariant failure. -/
def releaseCode : ProtectorReleaseStatus → List Nat
  | .Released => [0]
  | .MissingTag t => [1, t]
  | .AccessFailure o l t e => [2, o, l, t, tbErrCode e]
  | .InvariantFailure o l t => [3, o, l, t]

/-! ## §6. `core::ptr::addr_eq` (`rust#166144`) versus wide `==` -/

/-- Equality of the canonical addresses of two pointer words, as the thin
pointer `BinOp.eq` of `evalRvalue` computes it (`ptrAddressScalar?` /
`resolveWideWordScalar?`, then `evalScalarBinOp .eq`). -/
def thinWordAddrEq (a b : Value) (locals : List LocalSlot) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) : RvalueEvalResult :=
  let ptrBytes := layoutPointerBytes layouts
  match
    resolveWideWordScalar? a locals mem.borrows mem.callerLocals localDecls layouts ptrBytes
      mem.callStack,
    resolveWideWordScalar? b locals mem.borrows mem.callerLocals localDecls layouts ptrBytes
      mem.callStack
  with
  | some x, some y => evalScalarBinOp .eq x y locals mem false
  | _, _ => .unsupported

/-- **`core::ptr::addr_eq(p, q)`.** Compares only the canonical addresses of
the data words; the metadata words (none, a slice length, or a vtable pointer)
are decoded and dropped. A value that is not a pointer (in particular `uninit`
or an aggregate containing `uninit`) is UB. -/
def evalWideAddrEqProto (p q : Value) (locals : List LocalSlot) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) : RvalueEvalResult :=
  let ptrBytes := layoutPointerBytes layouts
  match decodeWidePtr? ptrBytes p, decodeWidePtr? ptrBytes q with
  | some wp, some wq =>
    thinWordAddrEq (encodeDataWord ptrBytes wp.data) (encodeDataWord ptrBytes wq.data)
      locals mem localDecls layouts
  | _, _ => .ub

/-- **Wide pointer `==`.** Compares `(data address, metadata word)` with
`evalWidePtrRelBinOp .eq` on homogeneous wide pointers (both `.vtable` or both
`.sliceLen`); rejects `.uninit`, non-wide pointers, width mismatches, and
heterogeneous metadata kinds (`.sliceLen` vs `.vtable`) with `.ub`, matching
MiniRust `comparePtrM`. -/
def evalWidePtrEqProto (p q : Value) (locals : List LocalSlot) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) : RvalueEvalResult :=
  let ptrBytes := layoutPointerBytes layouts
  match decodeWidePtr? ptrBytes p, decodeWidePtr? ptrBytes q with
  | some ⟨dp, .vtable vp⟩, some ⟨dq, .vtable vq⟩ =>
    evalWidePtrRelBinOp .eq (encodeDataWord ptrBytes dp) (.ptr vp ptrBytes)
      (encodeDataWord ptrBytes dq) (.ptr vq ptrBytes) locals mem localDecls layouts ptrBytes
  | some ⟨dp, .sliceLen lp⟩, some ⟨dq, .sliceLen lq⟩ =>
    evalWidePtrRelBinOp .eq (encodeDataWord ptrBytes dp) (.scalar ⟨lp, ptrBytes⟩)
      (encodeDataWord ptrBytes dq) (.scalar ⟨lq, ptrBytes⟩) locals mem localDecls layouts ptrBytes
  | _, _ => .ub

/-- **`addr_eq` ignores ALL metadata.** For every pair of data words and every
combination of metadata on either side (`.thin`, `.sliceLen n`,
`.vtable vtPtr`), `addr_eq` is the address comparison of the data words. -/
theorem evalWideAddrEqProto_ignores_metadata
    (d₁ d₂ : ProtoDataWord) (m₁ m₂ : ProtoWidePtrMeta) (locals : List LocalSlot)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalWideAddrEqProto
        (encodeWidePtr (layoutPointerBytes layouts) ⟨d₁, m₁⟩)
        (encodeWidePtr (layoutPointerBytes layouts) ⟨d₂, m₂⟩) locals mem localDecls layouts =
      thinWordAddrEq
        (encodeDataWord (layoutPointerBytes layouts) d₁)
        (encodeDataWord (layoutPointerBytes layouts) d₂) locals mem localDecls layouts := by
  unfold evalWideAddrEqProto
  simp only [decodeWidePtr?_encodeWidePtr]

/-- Corollary: changing the metadata of either operand never changes
`addr_eq` (`&rec as &dyn TraitA` vs `&rec as &dyn TraitB`, `&arr[0..2]` vs
`&arr[0..4]`, `&rec as &dyn TraitA` vs `&rec as *const ()`). -/
theorem evalWideAddrEqProto_metadata_invariant
    (d₁ d₂ : ProtoDataWord) (m₁ m₂ m₁' m₂' : ProtoWidePtrMeta) (locals : List LocalSlot)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalWideAddrEqProto
        (encodeWidePtr (layoutPointerBytes layouts) ⟨d₁, m₁⟩)
        (encodeWidePtr (layoutPointerBytes layouts) ⟨d₂, m₂⟩) locals mem localDecls layouts =
      evalWideAddrEqProto
        (encodeWidePtr (layoutPointerBytes layouts) ⟨d₁, m₁'⟩)
        (encodeWidePtr (layoutPointerBytes layouts) ⟨d₂, m₂'⟩) locals mem localDecls layouts := by
  rw [evalWideAddrEqProto_ignores_metadata, evalWideAddrEqProto_ignores_metadata]

/-- `addr_eq` on an operand that is not a pointer value is UB; `uninit` is not
a pointer value at any width. -/
theorem evalWideAddrEqProto_uninit_ub (q : Value) (locals : List LocalSlot)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalWideAddrEqProto .uninit q locals mem localDecls layouts = .ub ∧
    evalWideAddrEqProto q .uninit locals mem localDecls layouts = .ub := by
  constructor
  · rfl
  · unfold evalWideAddrEqProto
    dsimp only
    split
    · rename_i h1 h2; cases h2
    · rfl

/-- Wide `==` on `.uninit` is UB. -/
theorem evalWidePtrEqProto_uninit_ub (q : Value) (locals : List LocalSlot)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalWidePtrEqProto .uninit q locals mem localDecls layouts = .ub ∧
    evalWidePtrEqProto q .uninit locals mem localDecls layouts = .ub := by
  constructor
  · rfl
  · unfold evalWidePtrEqProto
    dsimp only
    split <;> first | rfl | (rename_i h2; cases h2)

/-- Wide `==` rejects heterogeneous wide metadata (slice length vs vtable pointer) with UB. -/
theorem evalWidePtrEqProto_heterogeneous_meta_ub
    (d₁ d₂ : ProtoDataWord) (len : Nat) (vtPtr : ProvenancePtr) (locals : List LocalSlot)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalWidePtrEqProto
        (encodeWidePtr (layoutPointerBytes layouts) ⟨d₁, .sliceLen len⟩)
        (encodeWidePtr (layoutPointerBytes layouts) ⟨d₂, .vtable vtPtr⟩)
        locals mem localDecls layouts = .ub ∧
    evalWidePtrEqProto
        (encodeWidePtr (layoutPointerBytes layouts) ⟨d₁, .vtable vtPtr⟩)
        (encodeWidePtr (layoutPointerBytes layouts) ⟨d₂, .sliceLen len⟩)
        locals mem localDecls layouts = .ub := by
  unfold evalWidePtrEqProto
  simp only [decodeWidePtr?_encodeWidePtr, and_self]

/-- `PtrToPtr` to a thin raw pointer erases the vtable word of a trait-object
pointer with provenance and keeps the data pointer exactly. -/
theorem evalCastPtrToPtr_dyn_to_thin
    (locals locals' : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (a vt : ProvenancePtr)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack =
        .ok (.aggregate 0 [.ptr a (layoutPointerBytes layouts), .ptr vt (layoutPointerBytes layouts)])
          locals')
    (hThin : isThinRawPtrTy targetTy = true) :
    evalCastPtrToPtr locals op targetTy mem localDecls layouts =
      .ok (.ptr a (layoutPointerBytes layouts)) locals' mem := by
  unfold evalCastPtrToPtr
  simp only [hOp, Nat.beq_refl, Bool.and_self, hThin]

/-- `PtrToPtr` to a thin raw pointer erases the vtable word of a provenance-less
trait-object pointer and preserves the wrapped scalar address. -/
theorem evalCastPtrToPtr_dyn_scalar_to_thin
    (locals locals' : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (bits : Nat) (vt : ProvenancePtr)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack =
        .ok (.aggregate 0
              [.scalar ⟨bits, layoutPointerBytes layouts⟩,
               .ptr vt (layoutPointerBytes layouts)])
          locals')
    (hThin : isThinRawPtrTy targetTy = true) :
    evalCastPtrToPtr locals op targetTy mem localDecls layouts =
      .ok (.scalar ⟨wrapScalarBits bits (scalarModulus (layoutPointerBytes layouts)),
                    layoutPointerBytes layouts⟩) locals' mem := by
  unfold evalCastPtrToPtr
  simp only [hOp, Nat.beq_refl, Bool.and_self, hThin]

theorem wrapScalarBits_idem (bits m : Nat) :
    wrapScalarBits (wrapScalarBits bits m) m = wrapScalarBits bits m := by
  unfold wrapScalarBits
  cases h : Nat.ble m bits with
  | false => simp only [h]
  | true =>
    cases m with
    | zero =>
      change (match Nat.ble 0 (bits % 0) with | true => (bits % 0) % 0 | false => bits % 0) = bits % 0
      simp only [Nat.mod_zero, h]
    | succ k =>
      have hlt : bits % (k + 1) < k + 1 := Nat.mod_lt bits (Nat.succ_pos k)
      have hble : Nat.ble (k + 1) (bits % (k + 1)) = false := by
        cases hb : Nat.ble (k + 1) (bits % (k + 1)) with
        | false => rfl
        | true => exact absurd (Nat.le_of_ble_eq_true hb) (Nat.not_le_of_gt hlt)
      change (match Nat.ble (k + 1) (bits % (k + 1)) with
              | true => (bits % (k + 1)) % (k + 1)
              | false => bits % (k + 1)) = bits % (k + 1)
      rw [hble]

theorem evalScalarBinOp_eq_irrel_signed (x y : ScalarInt) (locals : List LocalSlot)
    (mem : Memory) (s₁ s₂ : Bool) :
    evalScalarBinOp .eq x y locals mem s₁ = evalScalarBinOp .eq x y locals mem s₂ :=
  rfl

/-- **`addr_eq` is the MIR fat-to-thin lowering** `(p as *const ()) == (q as
*const ())` across ALL combinations of provenance / provenance-less data words
and ALL metadata variants (`.thin`, `.sliceLen`, `.vtable`). When `lhsOp` /
`rhsOp` evaluate to the wrapped thin data words produced by `evalCastPtrToPtr`,
`evalRvalue (.binaryOp .eq lhsOp rhsOp)` equals `evalWideAddrEqProto` on the
wide (or thin) pointers. -/
theorem evalWideAddrEqProto_eq_thin_binop_eq_all_words
    (locals : List LocalSlot) (lhsOp rhsOp : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (d₁ d₂ : ProtoDataWord) (m₁ m₂ : ProtoWidePtrMeta)
    (hL : evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack =
        .ok (encodeDataWord (layoutPointerBytes layouts)
              (wrapDataWord (layoutPointerBytes layouts) d₁)) locals)
    (hR : evalOperand locals rhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack =
        .ok (encodeDataWord (layoutPointerBytes layouts)
              (wrapDataWord (layoutPointerBytes layouts) d₂)) locals)
    (hRel : isPtrRelationalBinOp .eq localDecls layouts lhsOp rhsOp = true) :
    evalRvalue locals (.binaryOp .eq lhsOp rhsOp) mem localDecls layouts =
      evalWideAddrEqProto
        (encodeWidePtr (layoutPointerBytes layouts) ⟨d₁, m₁⟩)
        (encodeWidePtr (layoutPointerBytes layouts) ⟨d₂, m₂⟩)
        locals mem localDecls layouts := by
  rw [evalWideAddrEqProto_ignores_metadata]
  cases d₁ with
  | prov a =>
    cases d₂ with
    | prov b =>
      simp only [wrapDataWord, encodeDataWord] at hL hR
      simp only [thinWordAddrEq, encodeDataWord, resolveWideWordScalar?, Nat.beq_refl]
      unfold evalRvalue
      simp only [hL, hR, hRel]
      generalize ptrAddressScalar? locals mem.borrows mem.callerLocals localDecls layouts
        (layoutPointerBytes layouts) a (layoutPointerBytes layouts) mem.callStack = x
      generalize ptrAddressScalar? locals mem.borrows mem.callerLocals localDecls layouts
        (layoutPointerBytes layouts) b (layoutPointerBytes layouts) mem.callStack = y
      cases x <;> cases y <;> rfl
    | addr b =>
      simp only [wrapDataWord, encodeDataWord] at hL hR
      simp only [thinWordAddrEq, encodeDataWord, resolveWideWordScalar?, Nat.beq_refl]
      unfold evalRvalue
      simp only [hL, hR, hRel]
      generalize ptrAddressScalar? locals mem.borrows mem.callerLocals localDecls layouts
        (layoutPointerBytes layouts) a (layoutPointerBytes layouts) mem.callStack = x
      cases x <;> rfl
  | addr a =>
    cases d₂ with
    | prov b =>
      simp only [wrapDataWord, encodeDataWord] at hL hR
      simp only [thinWordAddrEq, encodeDataWord, resolveWideWordScalar?, Nat.beq_refl]
      unfold evalRvalue
      simp only [hL, hR, hRel]
      generalize ptrAddressScalar? locals mem.borrows mem.callerLocals localDecls layouts
        (layoutPointerBytes layouts) b (layoutPointerBytes layouts) mem.callStack = y
      cases y <;> rfl
    | addr b =>
      simp only [wrapDataWord, encodeDataWord] at hL hR
      simp only [thinWordAddrEq, encodeDataWord, resolveWideWordScalar?, Nat.beq_refl]
      unfold evalRvalue
      simp only [hL, hR]
      exact evalScalarBinOp_eq_irrel_signed _ _ locals mem _ false

/-- Specialization to two provenance trait-object pointers (`&dyn A` vs `&dyn B`). -/
theorem evalWideAddrEqProto_eq_thin_ptr_binop_eq
    (locals : List LocalSlot) (lhsOp rhsOp : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (a b va vb : ProvenancePtr)
    (hL : evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.ptr a (layoutPointerBytes layouts)) locals)
    (hR : evalOperand locals rhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.ptr b (layoutPointerBytes layouts)) locals)
    (hRel : isPtrRelationalBinOp .eq localDecls layouts lhsOp rhsOp = true) :
    evalRvalue locals (.binaryOp .eq lhsOp rhsOp) mem localDecls layouts =
      evalWideAddrEqProto
        (.aggregate 0 [.ptr a (layoutPointerBytes layouts), .ptr va (layoutPointerBytes layouts)])
        (.aggregate 0 [.ptr b (layoutPointerBytes layouts), .ptr vb (layoutPointerBytes layouts)])
        locals mem localDecls layouts :=
  evalWideAddrEqProto_eq_thin_binop_eq_all_words locals lhsOp rhsOp mem localDecls layouts
    (.prov a) (.prov b) (.vtable va) (.vtable vb) hL hR hRel

/-- The canonical address word of a pointer that has no borrow entry is its
allocation page plus its offset, wrapped to the pointer width. -/
theorem resolveWideWordScalar?_unborrowed
    (p : ProvenancePtr) (ptrBytes : Nat) (locals : List LocalSlot) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hB : lookupBorrow mem.borrows p.tag = none) :
    resolveWideWordScalar? (.ptr p ptrBytes) locals mem.borrows mem.callerLocals localDecls
        layouts ptrBytes mem.callStack =
      some
        { bits := wrapScalarBits (Nat.add (Nat.mul p.allocId 65536) p.offsetBytes)
            (scalarModulus ptrBytes)
          sizeBytes := ptrBytes } := by
  simp only [resolveWideWordScalar?, Nat.beq_refl, ptrAddressScalar?, ptrAddress?, hB]

/-- **Wide `==` compares the metadata word.** Two trait-object pointers with
the same data word whose vtable pointers have different canonical addresses are
unequal under `evalWidePtrEqProto` (`evalWidePtrRelBinOp .eq`), while `addr_eq`
on the same pair ignores the vtables. -/
theorem evalWidePtrEqProto_same_data_distinct_meta
    (d : ProtoDataWord) (va vb : ProvenancePtr) (locals : List LocalSlot) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (x ma mb : ScalarInt)
    (hD : resolveWideWordScalar? (encodeDataWord (layoutPointerBytes layouts) d) locals mem.borrows
      mem.callerLocals localDecls layouts (layoutPointerBytes layouts) mem.callStack = some x)
    (hA : resolveWideWordScalar? (.ptr va (layoutPointerBytes layouts)) locals mem.borrows
      mem.callerLocals localDecls layouts (layoutPointerBytes layouts) mem.callStack = some ma)
    (hB : resolveWideWordScalar? (.ptr vb (layoutPointerBytes layouts)) locals mem.borrows
      mem.callerLocals localDecls layouts (layoutPointerBytes layouts) mem.callStack = some mb)
    (hSz : Nat.beq ma.sizeBytes 0 = false)
    (hSzEq : Nat.beq ma.sizeBytes mb.sizeBytes = true)
    (hNe : Nat.beq ma.bits mb.bits = false) :
    evalWidePtrEqProto
        (encodeWidePtr (layoutPointerBytes layouts) ⟨d, .vtable va⟩)
        (encodeWidePtr (layoutPointerBytes layouts) ⟨d, .vtable vb⟩) locals mem
        localDecls layouts =
      .ok (.scalar (boolToScalar false)) locals mem := by
  simp only [evalWidePtrEqProto, decodeWidePtr?_encodeWidePtr, evalWidePtrRelBinOp,
    hD, hA, hB, Nat.beq_refl, evalScalarBinOp, hSz, hSzEq, hNe]

/-! ## Spine normalization for kernel evaluation

A copy of the spine-normalizing helpers of
`Anneal.Rustc.V2026_06_01.Lower` (`strictMachineState` and friends). That
module cannot be imported here: in the `examples/` Lake package it clashes with
`Trusted` on an auxiliary `eq_def` declaration. Every helper is proved to be
the identity (`strictMachineState_eq`). -/

namespace Strict

@[reducible]
def strictBool : Bool → Option Bool
  | false => .some false
  | true => .some true

theorem strictBool_eq : ∀ (b : Bool), strictBool b = .some b
  | false => rfl
  | true => rfl

@[reducible]
def strictBits : Nat → Nat → Option Nat
  | .zero, n => .some n
  | .succ _, .zero => .some .zero
  | .succ _, .succ .zero => .some (.succ .zero)
  | .succ k, .succ (.succ m) =>
    let n := .succ (.succ m)
    match strictBits k (Nat.div n 2), Nat.beq (Nat.mod n 2) 0 with
    | .some q, true => .some (Nat.mul 2 q)
    | .some q, false => .some (.succ (Nat.mul 2 q))
    | .none, _ => .none

theorem strictBits_eq : ∀ (k n : Nat), strictBits k n = .some n
  | .zero, _ => rfl
  | .succ _, .zero => rfl
  | .succ _, .succ .zero => rfl
  | .succ k, .succ (.succ m) => by
    unfold strictBits
    dsimp only
    rw [strictBits_eq k (Nat.div (.succ (.succ m)) 2)]
    cases hm : Nat.beq (Nat.mod (.succ (.succ m)) 2) 0
    · dsimp only
      have hm' : (.succ (.succ m)) % 2 ≠ 0 := fun hc => by
        change Nat.mod (.succ (.succ m)) 2 = 0 at hc
        rw [hc] at hm
        nomatch hm
      change Option.some (2 * ((m + 2) / 2) + 1) = Option.some (m + 2)
      exact congrArg Option.some (by omega)
    · dsimp only
      have hm' : (.succ (.succ m)) % 2 = 0 := Nat.eq_of_beq_eq_true hm
      change Option.some (2 * ((m + 2) / 2)) = Option.some (m + 2)
      exact congrArg Option.some (by omega)

@[reducible]
def strictOpt {α : Type} : Option α → Option (Option α)
  | .none => .some .none
  | .some x => .some (.some x)

theorem strictOpt_eq {α : Type} : ∀ (o : Option α), strictOpt o = .some o
  | .none => rfl
  | .some _ => rfl

@[reducible]
def strictOptNat : Option Nat → Option (Option Nat)
  | .none => .some .none
  | .some n =>
    match strictBits 32 n with
    | .some n' => .some (.some n')
    | .none => .none

theorem strictOptNat_eq : ∀ (o : Option Nat), strictOptNat o = .some o
  | .none => rfl
  | .some n => by
    unfold strictOptNat
    dsimp only
    rw [strictBits_eq 32 n]

@[reducible]
def strictList {α : Type} : List α → Option (List α)
  | .nil => .some .nil
  | x :: xs =>
    match strictList xs with
    | .some xs' => .some (x :: xs')
    | .none => .none

theorem strictList_eq {α : Type} : ∀ (xs : List α), strictList xs = .some xs
  | .nil => rfl
  | _ :: xs => by
    unfold strictList
    rw [strictList_eq xs]

@[reducible]
def strictPerm : TreeBorrowPerm → Option TreeBorrowPerm
  | .cell => .some .cell
  | .reservedFrz b =>
    match strictBool b with
    | .some b' => .some (.reservedFrz b')
    | .none => .none
  | .reservedIM => .some .reservedIM
  | .unique => .some .unique
  | .frozen => .some .frozen
  | .disabled => .some .disabled

theorem strictPerm_eq : ∀ (p : TreeBorrowPerm), strictPerm p = .some p
  | .cell => rfl
  | .reservedFrz b => by
    unfold strictPerm
    dsimp only
    rw [strictBool_eq b]
  | .reservedIM => rfl
  | .unique => rfl
  | .frozen => rfl
  | .disabled => rfl

@[reducible]
def strictBorrowEntry (e : BorrowEntry) : Option BorrowEntry :=
  match strictBits 32 e.tag, strictBits 16 e.targetLocal, strictList e.targetProjection, strictPerm e.perm with
  | .some tag', .some loc', .some proj', .some perm' =>
    match strictBits 64 e.rangeOffset, strictBits 64 e.rangeLen, strictOptNat e.protector with
    | .some roff', .some rlen', .some prot' =>
      match strictOptNat e.parentTag, strictBits 16 e.targetFrameDepth, strictBool e.allocDead with
      | .some ptag', .some depth', .some dead' =>
        .some
          { tag := tag'
            targetLocal := loc'
            targetProjection := proj'
            perm := perm'
            rangeOffset := roff'
            rangeLen := rlen'
            protector := prot'
            parentTag := ptag'
            targetFrameDepth := depth'
            allocDead := dead' }
      | _, _, _ => .none
    | _, _, _ => .none
  | _, _, _, _ => .none

theorem strictBorrowEntry_eq (e : BorrowEntry) : strictBorrowEntry e = .some e := by
  cases e
  unfold strictBorrowEntry
  dsimp only
  rw [strictBits_eq, strictBits_eq, strictList_eq, strictPerm_eq,
      strictBits_eq, strictBits_eq, strictOptNat_eq, strictOptNat_eq,
      strictBits_eq, strictBool_eq]

@[reducible]
def strictBorrows : List BorrowEntry → Option (List BorrowEntry)
  | .nil => .some .nil
  | e :: rest =>
    match strictBorrowEntry e, strictBorrows rest with
    | .some e', .some rest' => .some (e' :: rest')
    | _, _ => .none

theorem strictBorrows_eq : ∀ (bs : List BorrowEntry), strictBorrows bs = .some bs
  | .nil => rfl
  | e :: rest => by
    unfold strictBorrows
    rw [strictBorrowEntry_eq e, strictBorrows_eq rest]

@[reducible]
def mapStrictList {α : Type} (f : α → Option α) : List α → Option (List α)
  | .nil => .some .nil
  | x :: xs =>
    match f x, mapStrictList f xs with
    | .some x', .some xs' => .some (x' :: xs')
    | _, _ => .none

theorem mapStrictList_eq {α : Type} (f : α → Option α) (hf : ∀ x, f x = .some x) :
    ∀ (xs : List α), mapStrictList f xs = .some xs
  | .nil => rfl
  | x :: xs => by
    unfold mapStrictList
    rw [hf x, mapStrictList_eq f hf xs]

@[reducible]
def strictValue : Nat → Value → Option Value
  | .zero, v => .some v
  | .succ _, .unit => .some .unit
  | .succ _, .uninit => .some .uninit
  | .succ _, .scalar sc =>
    match strictBits 128 sc.bits, strictBits 16 sc.sizeBytes with
    | .some b', .some sz' => .some (.scalar ⟨b', sz'⟩)
    | _, _ => .none
  | .succ _, .ptr p sz =>
    match strictBits 64 p.allocId, strictBits 64 p.offsetBytes, strictBits 16 sz with
    | .some a', .some o', .some sz' => .some (.ptr ⟨a', o'⟩ sz')
    | _, _, _ => .none
  | .succ d, .aggregate v fs =>
    match strictBits 16 v, mapStrictList (strictValue d) fs with
    | .some v', .some fs' => .some (.aggregate v' fs')
    | _, _ => .none

theorem strictValue_eq : ∀ (d : Nat) (v : Value), strictValue d v = .some v
  | .zero, _ => rfl
  | .succ d, v => by
    cases v with
    | unit => rfl
    | uninit => rfl
    | scalar sc =>
      cases sc
      unfold strictValue
      dsimp only
      rw [strictBits_eq, strictBits_eq]
    | ptr p sz =>
      cases p
      unfold strictValue
      dsimp only
      rw [strictBits_eq, strictBits_eq, strictBits_eq]
    | aggregate v fs =>
      unfold strictValue
      rw [strictBits_eq, mapStrictList_eq (strictValue d) (strictValue_eq d) fs]

@[reducible]
def strictSlotsAt (argCount idx : Nat) : List LocalSlot → Option (List LocalSlot)
  | .nil => .some .nil
  | .dead :: rest =>
    match strictSlotsAt argCount (.succ idx) rest with
    | .some rest' => .some (.dead :: rest')
    | .none => .none
  | .uninit :: rest =>
    match strictSlotsAt argCount (.succ idx) rest with
    | .some rest' => .some (.uninit :: rest')
    | .none => .none
  | .init v :: rest =>
    match Bool.and (Nat.ble 1 idx) (Nat.ble idx argCount) with
    | true =>
      match strictSlotsAt argCount (.succ idx) rest with
      | .some rest' => .some (.init v :: rest')
      | .none => .none
    | false =>
      match strictValue 16 v, strictSlotsAt argCount (.succ idx) rest with
      | .some v', .some rest' => .some (.init v' :: rest')
      | _, _ => .none

theorem strictSlotsAt_eq (argCount : Nat) :
    ∀ (idx : Nat) (ls : List LocalSlot), strictSlotsAt argCount idx ls = .some ls
  | _, .nil => rfl
  | idx, slot :: rest => by
    cases slot with
    | dead =>
      unfold strictSlotsAt
      rw [strictSlotsAt_eq argCount (.succ idx) rest]
    | uninit =>
      unfold strictSlotsAt
      rw [strictSlotsAt_eq argCount (.succ idx) rest]
    | init v =>
      unfold strictSlotsAt
      cases Bool.and (Nat.ble 1 idx) (Nat.ble idx argCount) <;> dsimp only
      · rw [strictValue_eq 16 v, strictSlotsAt_eq argCount (.succ idx) rest]
      · rw [strictSlotsAt_eq argCount (.succ idx) rest]

@[reducible]
def strictFrame (argCount : Nat) (f : StackFrame) : Option StackFrame :=
  match strictBits 16 f.blockIdx, strictBits 16 f.stmtIdx, strictSlotsAt argCount 0 f.locals with
  | .some blk, .some idx, .some locs =>
    .some { blockIdx := blk, stmtIdx := idx, locals := locs }
  | _, _, _ => .none

theorem strictFrame_eq (argCount : Nat) (f : StackFrame) :
    strictFrame argCount f = .some f := by
  cases f
  unfold strictFrame
  dsimp only
  rw [strictBits_eq, strictBits_eq, strictSlotsAt_eq]

@[reducible]
def strictMemory (m : Memory) : Option Memory :=
  match strictBits 32 m.nextAllocId, strictList m.globals, strictBorrows m.borrows, strictBits 32 m.nextTag with
  | .some naid, .some glob, .some bor, .some nt =>
    match strictList m.callees, strictList m.traitImpls, strictList m.callStack, strictOpt m.activeCallee with
    | .some cal, .some ti, .some cs, .some ac =>
      match strictList m.activeProtectors, strictBits 32 m.nextProtector, strictSlotsAt 0 0 m.callerLocals with
      | .some ap, .some np, .some cl =>
        match strictList m.fnPtrs, strictList m.exposedAllocIds with
        | .some fp, .some ea =>
          .some
            { nextAllocId := naid, globals := glob, borrows := bor, nextTag := nt,
              callees := cal, traitImpls := ti, callStack := cs, activeCallee := ac,
              activeProtectors := ap, nextProtector := np, callerLocals := cl,
              fnPtrs := fp, exposedAllocIds := ea }
        | _, _ => .none
      | _, _, _ => .none
    | _, _, _, _ => .none
  | _, _, _, _ => .none

theorem strictMemory_eq (m : Memory) : strictMemory m = .some m := by
  cases m
  unfold strictMemory
  dsimp only
  rw [strictBits_eq, strictList_eq, strictBorrows_eq, strictBits_eq,
      strictList_eq, strictList_eq, strictList_eq, strictOpt_eq,
      strictList_eq, strictBits_eq, strictSlotsAt_eq, strictList_eq, strictList_eq]

@[reducible]
def strictMachineState (argCount : Nat) (s : MachineState) : Option MachineState :=
  match strictFrame argCount s.frame, strictMemory s.memory with
  | .some f', .some m' => .some { frame := f', memory := m' }
  | _, _ => .none

theorem strictMachineState_eq (argCount : Nat) (s : MachineState) :
    strictMachineState argCount s = .some s := by
  cases s
  unfold strictMachineState
  dsimp only
  rw [strictFrame_eq, strictMemory_eq]

end Strict

/-! ## §7. `stepMirFn` extended with the prototype rules -/

/-- Captured `dyn` information of a compilation unit: the vtable table and the
slot index of every virtual method (`InstanceKind::Virtual(def_id, idx)`),
keyed by the trait method `DefPath` of the call site. -/
structure ProtoDynProgram : Type where
  vtables : ProtoVTableTable
  virtualMethods : List (String × Nat) := []

/-- Vtable slot index of the trait method `defPath`. -/
def lookupVirtualSlot : List (String × Nat) → String → Option Nat
  | [], _ => none
  | (k, idx) :: rest, defPath =>
    match strEq k defPath with
    | true => some idx
    | false => lookupVirtualSlot rest defPath

/-- Classification of a call terminator. -/
inductive VirtualSiteResolution : Type where
  | notVirtual
  | unsupported
  | site (site : ProtoVirtualCallSite)

/-- Receiver class of a virtual call from the type of its first argument:
`(isRef, isMut)`. A reference `&[mut] dyn Trait` and a `Pin<&[mut] dyn Trait>`
wrapper (whose inner reference Miri retags with a function-entry protector,
`RetagFields`) are reference receivers; a raw pointer is not. Every other
`DispatchFromDyn` receiver (`Box<dyn Trait>`, `Rc<Self>`, unknown types) fails
closed with `none`: classifying it as raw would skip the safe-reference
validity check and the receiver protector. -/
def classifyVirtualReceiver : Option Ty → Option (Bool × Bool)
  | some { kind := .ref m _, .. } => some (true, V06.lowerMut m)
  | some { kind := .rawPtr _ _, .. } => some (false, false)
  | some { kind := .adt path [.ref m _], .. } =>
    match strEq path "core::pin::Pin" with
    | true => some (true, V06.lowerMut m)
    | false => none
  | _ => none

/-- **Receiver classification fails closed.** A wrapper receiver other than
`Pin<&[mut] _>` (for example `Box<dyn Trait>`) and an untyped receiver are never
classified as raw pointers; `Pin<&mut dyn Trait>` is a mutable reference
receiver. -/
theorem classifyVirtualReceiver_fail_closed (path : String) (args : List RigidTy) (idx : Nat)
    (hPin : strEq path "core::pin::Pin" = false) :
    classifyVirtualReceiver (some { kind := .adt path args, layoutIdx := idx }) = none ∧
    classifyVirtualReceiver none = none ∧
    classifyVirtualReceiver
      (some { kind := .adt "core::pin::Pin" [.ref .mut (.dynamic "T")], layoutIdx := idx }) =
        some (true, true) := by
  refine ⟨?_, rfl, ?_⟩
  · unfold classifyVirtualReceiver
    split
    · rename_i h; cases h
    · rename_i h; cases h
    · rename_i path' m _ _ h
      injection h with h1
      injection h1 with h2
      injection h2 with h3 _
      subst h3
      simp only [hPin]
    · rfl
  · unfold classifyVirtualReceiver
    simp only [V06.lowerMut]
    rfl

/-- A call is virtual when its callee is a registered virtual method whose
`Self` type argument is a trait object (`<dyn Trait as Trait>::method`). The
receiver kind and mutability come from the type of the first argument. A
registered virtual method whose predicate list was not captured fails closed;
a callee that is not a registered virtual method is left to `stepMirFn` (which
requests an external call when no body is linked). -/
def virtualCallSite? (prog : ProtoDynProgram) (callerBody : CapturedMir) (func : Operand)
    (argOps : List Operand) : VirtualSiteResolution :=
  match extractCallee? func with
  | some (defPath, .dynamic traitKey :: _) =>
    match lookupVirtualSlot prog.virtualMethods defPath with
    | none => .notVirtual
    | some slotIdx =>
      match lookupDynPred prog.vtables.dynTypes traitKey with
      | none => .unsupported
      | some pred =>
        match argOps with
        | [] => .unsupported
        | recvOp :: _ =>
          match classifyVirtualReceiver (operandTy callerBody.localDecls callerBody.layouts recvOp) with
          | none => .unsupported
          | some (isRef, isMut) =>
            .site
              { traitPred := pred, slotIdx := slotIdx, receiverIsRef := isRef,
                receiverIsMut := isMut }
  | _ => .notVirtual

/-- A borrow entry targets the local `loc` of the frame at depth `depth`. -/
def anyBorrowTargets : List BorrowEntry → Nat → Local → Bool
  | [], _, _ => false
  | b :: rest, depth, loc =>
    (Nat.beq b.targetFrameDepth depth && Nat.beq b.targetLocal loc && !b.allocDead) ||
      anyBorrowTargets rest depth loc

/-- Assignment `place = op as <pointer to dyn> (PointerCoercion(Unsize))`.

Prototype restriction (fail closed): the destination is a whole local that no
live borrow targets, so the assignment needs no borrow invalidation. In the TCB
the rule lives inside `evalRvalue`, and the existing assignment path applies. -/
def stepUnsizeAssignProto (vt : ProtoVTableTable) (s : MachineState) (currentBody : CapturedMir)
    (place : Place) (op : Operand) (targetTy : Ty) : MirStepNode :=
  match place.projection with
  | _ :: _ => MirStepNode.unsupported
  | [] =>
    match anyBorrowTargets s.memory.borrows (length s.memory.callStack) place.local_ with
    | true => MirStepNode.unsupported
    | false =>
      match
        evalUnsizeCoercionProto vt s.frame.locals op targetTy s.memory currentBody.localDecls
          currentBody.layouts
      with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok v locals' mem' =>
        match get? locals' place.local_ with
        | none => MirStepNode.fail .ub
        | some .dead => MirStepNode.fail .ub
        | some _ =>
          match set? locals' place.local_ (.init v) with
          | some locals'' => MirStepNode.step (advanceStmt s locals'' mem')
          | none => MirStepNode.fail .ub

/-- Resume continuation for an external call supporting both returning
(`target = some bb`) and diverging (`target = none`, where returning normally
is UB) call terminators. -/
def resumeExternalCallOpt
    (s : MachineState) (localsAfterArgs : List LocalSlot) (destination : Place)
    (target : Option BasicBlockIdx) (unwind : UnwindAction) (ans : MirCallAns) : MirExecState :=
  match target with
  | some bb => resumeExternalCall s localsAfterArgs destination bb unwind ans
  | none =>
    match ans with
    | .returned _ _ => .faulted .ub
    | _ => resumeExternalCall s localsAfterArgs destination 0 unwind ans

/-- Virtual call terminator (returning or diverging). -/
def stepVirtualCallProtoOpt
    (vt : ProtoVTableTable) (site : ProtoVirtualCallSite) (s : MachineState)
    (currentBody : CapturedMir) (argOps : List Operand) (destination : Place)
    (target : Option BasicBlockIdx) (unwind : UnwindAction) : MirStepNode :=
  match evalVirtualCallProtoOpt vt site s currentBody argOps destination target unwind with
  | .enter s' _ _ => MirStepNode.step s'
  | .externalCall defPath args locals' =>
    MirStepNode.extCall
      { defPath := defPath, typeArgs := [], args := args, memory := s.memory }
      (resumeExternalCallOpt s locals' destination target unwind)
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported

/-- Returning virtual call terminator. -/
def stepVirtualCallProto (vt : ProtoVTableTable) (site : ProtoVirtualCallSite) (s : MachineState)
    (currentBody : CapturedMir) (argOps : List Operand) (destination : Place)
    (target : BasicBlockIdx) (unwind : UnwindAction) : MirStepNode :=
  stepVirtualCallProtoOpt vt site s currentBody argOps destination (some target) unwind

/-- Write `v` to the whole local `dst` and advance to the next statement. The
destination must be a live local that no live borrow targets (prototype
restriction, fail closed). -/
def assignWholeLocalProto (s : MachineState) (locals' : List LocalSlot) (mem' : Memory)
    (dst : Local) (v : Value) : MirStepNode :=
  match anyBorrowTargets mem'.borrows (length mem'.callStack) dst with
  | true => MirStepNode.unsupported
  | false =>
    match get? locals' dst with
    | none => MirStepNode.fail .ub
    | some .dead => MirStepNode.fail .ub
    | some _ =>
      match set? locals' dst (.init v) with
      | some locals'' => MirStepNode.step (advanceStmt s locals'' mem')
      | none => MirStepNode.fail .ub

/-- Classification of `&raw const (*src)` / `&raw mut (*src)` on a trait-object
pointer `src`.

Creating a raw pointer performs no memory access and no retag under Tree
Borrows (Miri does not retag raw pointers; MiniRust's `AddrOf Raw` only
re-wraps the pointer), so the result is the same wide pointer whatever the
permission of the borrow tag is: a `.disabled` or `.frozen` tag is *not* UB
here (it becomes UB at the first access through the raw pointer). The only
rejection is `&raw mut (*r)` with `r : &dyn Trait`, which `rustc` refuses to
compile (E0596): such MIR is ill formed and fails closed with `.unsupported`.
Returns `none` to fall through to `stepMirFn`. -/
def dynRawBorrowProto?
    (ptrBytes : Nat) (mutKind : Mutability) (locals : List LocalSlot)
    (localDecls : List LocalDecl) (srcPlace : Place) : Option (ProtoRes Value) :=
  match srcPlace.projection with
  | [.deref] =>
    match get? locals srcPlace.local_ with
    | some (.init v) =>
      match decodeWidePtr? ptrBytes v with
      | some ⟨_, .vtable _⟩ =>
        match get? localDecls srcPlace.local_ with
        | some { ty := { kind := .ref srcMut (.dynamic _), .. }, .. } =>
          match unsizeMutCompatible (V06.lowerMut srcMut) (V06.lowerMut mutKind) with
          | false => some .unsupported
          | true => some (.ok v)
        | some { ty := { kind := .rawPtr _ (.dynamic _), .. }, .. } => some (.ok v)
        | _ => some .unsupported
      | _ => none
    | _ => none
  | _ => none

/-- **Raw borrows of a `dyn` place perform no Tree Borrows check.** Whatever the
borrow table says (a `.disabled` or `.frozen` tag included), `&raw const (*r)`
of a `&dyn Trait` / `&mut dyn Trait` local `r` holding a trait-object pointer
returns that pointer unchanged. -/
theorem dynRawBorrowProto?_ignores_borrow_state
    (ptrBytes : Nat) (locals : List LocalSlot) (localDecls : List LocalDecl) (r : Local)
    (v : Value) (d : ProtoDataWord) (vtPtr : ProvenancePtr) (decl : LocalDecl)
    (m : Mutability) (traitKey : String)
    (hSlot : get? locals r = some (.init v))
    (hDec : decodeWidePtr? ptrBytes v = some ⟨d, .vtable vtPtr⟩)
    (hDecl : get? localDecls r = some decl)
    (hTy : decl.ty.kind = .ref m (.dynamic traitKey)) :
    dynRawBorrowProto? ptrBytes .not locals localDecls { local_ := r, projection := [.deref] } =
      some (.ok v) := by
  obtain ⟨mu, ⟨kind, idx⟩, dn⟩ := decl
  simp only at hTy
  subst hTy
  unfold dynRawBorrowProto?
  simp only [hSlot, hDec, hDecl]
  cases m <;> rfl

/-- The callee of a call terminator is `core::ptr::addr_eq`. -/
def isAddrEqCallee (func : Operand) : Bool :=
  match extractCalleeDefPath? func with
  | some defPath => strEq defPath "core::ptr::addr_eq"
  | none => false

/-- Detect `core::intrinsics::{size_of_val, align_of_val}` (or `core::mem::*`)
called on a pointer to `.dynamic traitKey`. Returns `some (isAlign, traitKey)`. -/
def dynLayoutIntrinsic?
    (currentBody : CapturedMir) (func : Operand) (argOps : List Operand) :
    Option (Bool × String) :=
  match extractCallee? func with
  | some (defPath, typeArgs) =>
    let isAlign? : Option Bool :=
      match classifyRustIntrinsic? defPath with
      | some .sizeOfVal => some false
      | some .alignOfVal => some true
      | _ =>
        match strEq defPath "core::mem::size_of_val" with
        | true => some false
        | false =>
          match strEq defPath "core::mem::align_of_val" with
          | true => some true
          | false => none
    match isAlign? with
    | none => none
    | some isAlign =>
      let pointee? : Option RigidTy :=
        match typeArgs with
        | t :: _ => some t
        | [] =>
          match argOps with
          | ptrOp :: _ =>
            match operandTy currentBody.localDecls currentBody.layouts ptrOp with
            | some { kind := .rawPtr _ t, .. } => some t
            | some { kind := .ref _ t, .. } => some t
            | _ => none
          | [] => none
      match pointee? with
      | some (.dynamic traitKey) => some (isAlign, traitKey)
      | _ => none
  | none => none

/-- Step `size_of_val` / `align_of_val` on a pointer to `.dynamic traitKey`
using `dynSizeOfValProto` / `dynAlignOfValProto`. -/
def stepDynLayoutIntrinsicProto
    (vt : ProtoVTableTable) (isAlign : Bool) (traitKey : String) (s : MachineState)
    (currentBody : CapturedMir) (argOps : List Operand) (destination : Place)
    (target : BasicBlockIdx) : MirStepNode :=
  let ptrBytes := layoutPointerBytes currentBody.layouts
  match
    evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals currentBody.layouts
      s.memory.callerLocals (callStack := s.memory.callStack)
  with
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported
  | .ok [ptrVal] locals' =>
    match lookupDynPred vt.dynTypes traitKey with
    | none => MirStepNode.unsupported
    | some pred =>
      let res :=
        match isAlign with
        | false => dynSizeOfValProto vt ptrBytes pred ptrVal
        | true => dynAlignOfValProto vt ptrBytes pred ptrVal
      match res with
      | .ok n => writeIntrinsicReturn s locals' destination target (.scalar ⟨n, ptrBytes⟩)
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
  | .ok _ _ => MirStepNode.fail .ub

/-- Call `core::ptr::addr_eq(p, q)`: evaluate both arguments, compare the data
addresses with `evalWideAddrEqProto`, and write the `bool` to the destination
with `writeIntrinsicReturn`. -/
def stepAddrEqProto (s : MachineState) (currentBody : CapturedMir) (argOps : List Operand)
    (destination : Place) (target : BasicBlockIdx) : MirStepNode :=
  match
    evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals currentBody.layouts
      s.memory.callerLocals (callStack := s.memory.callStack)
  with
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported
  | .ok [p, q] locals' =>
    match evalWideAddrEqProto p q locals' s.memory currentBody.localDecls currentBody.layouts with
    | .ok ret _ _ => writeIntrinsicReturn s locals' destination target ret
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
  | .ok _ _ => MirStepNode.fail .ub

/-- **`stepMirFn` with the prototype rules.** An `Unsize` cast to a pointer to
a trait object, a raw borrow of a dereferenced trait-object pointer, a virtual
call (returning or diverging), a `size_of_val`/`align_of_val` intrinsic on a
trait object, and a call to `core::ptr::addr_eq` use the prototype rules; every
other statement and terminator is `stepMirFn`. -/
def stepMirFnProto (prog : ProtoDynProgram) (body : CapturedMir) (s : MachineState) :
    MirStepNode :=
  let currentBody := s.memory.activeCallee.getD body
  match currentBody.phase with
  | .other _ => stepMirFn body s
  | _ =>
    match get? currentBody.basicBlocks s.frame.blockIdx with
    | none => stepMirFn body s
    | some bb =>
      match get? bb.statements s.frame.stmtIdx with
      | some stmt =>
        match stmt.kind with
        | .assign place (.cast (.pointerCoercion kind) op targetTy) =>
          match strEq kind "Unsize", dynPtrTarget? targetTy.kind with
          | true, some _ => stepUnsizeAssignProto prog.vtables s currentBody place op targetTy
          | _, _ => stepMirFn body s
        | .assign place (.rawPtr mutKind srcPlace) =>
          match
            place.projection,
            dynRawBorrowProto? (layoutPointerBytes currentBody.layouts) mutKind s.frame.locals
              currentBody.localDecls srcPlace
          with
          | [], some (.ok v) => assignWholeLocalProto s s.frame.locals s.memory place.local_ v
          | [], some .ub => MirStepNode.fail .ub
          | [], some .unsupported => MirStepNode.unsupported
          | _, _ => stepMirFn body s
        | _ => stepMirFn body s
      | none =>
        match Nat.beq s.frame.stmtIdx (length bb.statements) with
        | false => stepMirFn body s
        | true =>
          match bb.terminator.kind with
          | .call func argOps destination targetOpt unwind =>
            match virtualCallSite? prog currentBody func argOps with
            | .notVirtual =>
              match targetOpt with
              | some target =>
                match isAddrEqCallee func with
                | true => stepAddrEqProto s currentBody argOps destination target
                | false =>
                  match dynLayoutIntrinsic? currentBody func argOps with
                  | some (isAlign, traitKey) =>
                    stepDynLayoutIntrinsicProto prog.vtables isAlign traitKey s currentBody argOps
                      destination target
                  | none => stepMirFn body s
              | none => stepMirFn body s
            | .unsupported => MirStepNode.unsupported
            | .site site =>
              stepVirtualCallProtoOpt prog.vtables site s currentBody argOps destination targetOpt
                unwind
          | _ => stepMirFn body s

/-- Outcome of a bounded run. -/
inductive ProtoRunResult : Type where
  | returned (val : Value) (mem : Memory)
  | panic
  | abort
  | ub
  | unsupported
  | outOfFuel
  | externalCall (defPath : DefPath)

/-! ### Spine normalization for kernel evaluation

The kernel reduces by name: without normalization every step's state is a
closure over the previous one and a bounded run exhausts memory. As
`Anneal.Rustc.V2026_06_01.Lower.stepMirStateStrict`, the runners below rebuild
the state with `Strict.strictMachineState` before each step. It is the
identity (`Strict.strictMachineState_eq`), so the normalized runners equal the
plain ones (`runSteps_eq_plain`, `advanceSteps_eq_plain`). -/

/-- Spine-normalized copy of `s` (equal to `s`). -/
def normState (body : CapturedMir) (s : MachineState) : MachineState :=
  match
    Strict.strictMachineState
      (match s.memory.activeCallee with
       | some callee => callee.argCount
       | none => body.argCount) s
  with
  | some s' => s'
  | none => s

theorem normState_eq (body : CapturedMir) (s : MachineState) : normState body s = s := by
  unfold normState
  rw [Strict.strictMachineState_eq]

/-- One step of a bounded run on an already chosen state. -/
def runStepResult (k : MirExecState → ProtoRunResult) (node : MirStepNode) : ProtoRunResult :=
  match node with
  | .ret (.normal (v, mem)) => .returned v mem
  | .ret .panic => .panic
  | .ret .abort => .abort
  | .tau st' => k st'
  | .vis (.inl (.fail .ub)) _ => .ub
  | .vis (.inl (.fail .unsupported)) _ => .unsupported
  | .vis (.inl (.fail .outOfFuel)) _ => .outOfFuel
  | .vis (.inr (.inl _)) cont => k (cont PUnit.unit)
  | .vis (.inr (.inr (.call req))) _ => .externalCall req.defPath

/-- Verdict of a state that is not running. -/
def haltedResult : MirExecState → ProtoRunResult
  | .halted (.normal (v, mem)) => .returned v mem
  | .halted .panic => .panic
  | .halted .abort => .abort
  | .faulted .ub => .ub
  | .faulted .unsupported => .unsupported
  | .faulted .outOfFuel => .outOfFuel
  | .running _ => .outOfFuel

/-- Bounded run of `step` from `st`, without normalization. Observation events
are skipped; an external call request stops the run. -/
def runStepsPlain (step : MachineState → MirStepNode) : Nat → MirExecState → ProtoRunResult
  | 0, _ => .outOfFuel
  | fuel + 1, .running s => runStepResult (runStepsPlain step fuel) (step s)
  | _ + 1, st => haltedResult st

/-- Bounded run of `step` from `st`, normalizing the state before each step. -/
def runSteps (body : CapturedMir) (step : MachineState → MirStepNode) :
    Nat → MirExecState → ProtoRunResult
  | 0, _ => .outOfFuel
  | fuel + 1, .running s => runStepResult (runSteps body step fuel) (step (normState body s))
  | _ + 1, st => haltedResult st

/-- The normalized runner is the plain runner. -/
theorem runSteps_eq_plain (body : CapturedMir) (step : MachineState → MirStepNode) :
    ∀ (fuel : Nat) (st : MirExecState), runSteps body step fuel st = runStepsPlain step fuel st
  | 0, _ => rfl
  | fuel + 1, .running s => by
    have ih : runSteps body step fuel = runStepsPlain step fuel :=
      funext (runSteps_eq_plain body step fuel)
    show runStepResult (runSteps body step fuel) (step (normState body s)) =
      runStepResult (runStepsPlain step fuel) (step s)
    rw [normState_eq, ih]
  | _ + 1, .halted _ => rfl
  | _ + 1, .faulted _ => rfl

/-- State after `n` steps of `step`, without normalization (observation events
are skipped; `none` when the run stops earlier). -/
def advanceStepsPlain (step : MachineState → MirStepNode) :
    Nat → MachineState → Option MachineState
  | 0, s => some s
  | n + 1, s =>
    match step s with
    | .tau (.running s') => advanceStepsPlain step n s'
    | .vis (.inr (.inl _)) k =>
      match k PUnit.unit with
      | .running s' => advanceStepsPlain step n s'
      | _ => none
    | _ => none

/-- State after `n` steps of `step`, normalizing the state before each step. -/
def advanceSteps (body : CapturedMir) (step : MachineState → MirStepNode) :
    Nat → MachineState → Option MachineState
  | 0, s => some (normState body s)
  | n + 1, s =>
    match step (normState body s) with
    | .tau (.running s') => advanceSteps body step n s'
    | .vis (.inr (.inl _)) k =>
      match k PUnit.unit with
      | .running s' => advanceSteps body step n s'
      | _ => none
    | _ => none

/-- The normalized `advanceSteps` is the plain one. -/
theorem advanceSteps_eq_plain (body : CapturedMir) (step : MachineState → MirStepNode) :
    ∀ (n : Nat) (s : MachineState), advanceSteps body step n s = advanceStepsPlain step n s
  | 0, s => by
    show some (normState body s) = some s
    rw [normState_eq]
  | n + 1, s => by
    have ih : advanceSteps body step n = advanceStepsPlain step n :=
      funext (advanceSteps_eq_plain body step n)
    unfold advanceSteps advanceStepsPlain
    rw [normState_eq, ih]

/-- Bounded run of `body` with the prototype rules. -/
def runMirProto (prog : ProtoDynProgram) (body : CapturedMir) (fuel : Nat)
    (s : MachineState) : ProtoRunResult :=
  runSteps body (stepMirFnProto prog body) fuel (.running s)

/-- Bounded run of `body` with `Trusted`'s `stepMirFn` alone. -/
def runMirTrusted (body : CapturedMir) (fuel : Nat) (s : MachineState) : ProtoRunResult :=
  runSteps body (stepMirFn body) fuel (.running s)

/-- **Stepper conservation.** On a state whose current statement is neither a
pointer-coercion cast assignment nor a raw-borrow assignment, the prototype
stepper IS `stepMirFn`. -/
theorem stepMirFnProto_conservative_stmt
    (prog : ProtoDynProgram) (body : CapturedMir) (s : MachineState)
    (bb : BasicBlockData) (stmt : Statement)
    (hBb : get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx = some bb)
    (hStmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hKind : ∀ place kind op targetTy,
      stmt.kind ≠ .assign place (.cast (.pointerCoercion kind) op targetTy))
    (hRaw : ∀ place m srcPlace, stmt.kind ≠ .assign place (.rawPtr m srcPlace)) :
    stepMirFnProto prog body s = stepMirFn body s := by
  unfold stepMirFnProto
  dsimp only
  split
  · rfl
  · rw [hBb]
    dsimp only
    rw [hStmt]
    dsimp only
    split
    · rename_i place kind op targetTy heq
      exact absurd heq (hKind place kind op targetTy)
    · rename_i place m srcPlace heq
      exact absurd heq (hRaw place m srcPlace)
    · rfl

/-! ## §8. Correspondence with `MiniRustSpec.Interp` (`Mach` and `MachTB`) -/

namespace MR

open MiniRustSpec MiniRustSpec.Interp

/-- Machine layout of the translation into a MiniRust machine over the memory
model `M`: the provenance and base address of an allocation identifier, the
MiniRust trait name of a trait object type, and the MiniRust function name of a
concrete method `DefPath`. -/
structure DynLayout (M : Type) [Gen.Memory M] : Type where
  provOf : Nat → Gen.Memory.Provenance M
  addrOf : Nat → Int
  traitOf : ProtoTraitPred → Nat
  fnOf : String → Nat

variable {M : Type} [Gen.Memory M] [MemoryOps M]

/-- MiniRust thin pointer to offset `off` of the allocation `allocId`. -/
def ptrAt (L : DynLayout M) (allocId off : Nat) : Gen.ThinPointer (Gen.Memory.Provenance M) :=
  { addr := L.addrOf allocId + (off : Int), provenance := some (L.provOf allocId) }

/-- MiniRust vtable pointer of the entry `e`: the base of its allocation. -/
def vtPtr (L : DynLayout M) (e : ProtoVTableEntry) :
    Gen.ThinPointer (Gen.Memory.Provenance M) :=
  ptrAt L e.vtableAllocId 0

/-- MiniRust vtable name of the entry `e`. -/
def vtName (e : ProtoVTableEntry) : Gen.VTableName := ⟨⟨e.vtableId⟩⟩

/-- MiniRust trait name of the trait object type `pred`. -/
def traitName (L : DynLayout M) (pred : ProtoTraitPred) : Gen.TraitName :=
  ⟨⟨L.traitOf pred⟩⟩

/-- Method table of a vtable: the slot index of each `.method` slot names the
trait method. -/
def methodsFrom (L : DynLayout M) : Nat → List ProtoVTableSlot →
    List (Gen.TraitMethodName × Gen.FnName)
  | _, [] => []
  | i, .method defPath :: rest => (⟨⟨i⟩⟩, ⟨⟨L.fnOf defPath⟩⟩) :: methodsFrom L (i + 1) rest
  | i, _ :: rest => methodsFrom L (i + 1) rest

/-- MiniRust `VTable` of the entry `e`. -/
def vtableOf (L : DynLayout M) (e : ProtoVTableEntry) : Gen.VTable :=
  { trait_name := traitName L e.traitPred
    size := ⟨e.sizeBytes⟩
    align := ⟨e.alignBytes⟩
    cells := []
    methods := ⟨methodsFrom L 0 e.slots⟩ }

/-- Deduplicate `prog.traits` by `Gen.TraitName`, keeping the first entry per trait. -/
def dedupTraits {α : Type} : List (Gen.TraitName × α) → List (Gen.TraitName × α)
  | [] => []
  | (tn, tr) :: rest =>
    (tn, tr) :: (dedupTraits rest).filter (fun p => !decide (p.1 = tn))

/-- **Translation.** Install the vtable table into the MiniRust machine `m`:
`vtable_ptrs`, `prog.vtables`, and deduplicated `prog.traits`. -/
def installVTables (L : DynLayout M) (vt : ProtoVTableTable) (m : Gen.Machine M) :
    Gen.Machine M :=
  { m with
    vtable_ptrs := ⟨vt.entries.map (fun e => (vtName e, vtPtr L e))⟩
    prog :=
      { m.prog with
        vtables := ⟨vt.entries.map (fun e => (vtName e, vtableOf L e))⟩
        traits :=
          ⟨dedupTraits
            (vt.entries.map (fun e =>
              (traitName L e.traitPred, ⟨(methodsFrom L 0 e.slots).map Prod.fst⟩)))⟩ } }

theorem find?_map_unique {α β : Type} (f : α → β) (p : β → Bool) (e : α) :
    ∀ (es : List α), e ∈ es → p (f e) = true → (∀ x, x ∈ es → p (f x) = true → x = e) →
      (es.map f).find? p = some (f e)
  | [], hMem, _, _ => by cases hMem
  | x :: xs, hMem, hp, hUniq => by
    simp only [List.map_cons, List.find?_cons]
    cases hx : p (f x) with
    | true =>
      rw [hUniq x (List.mem_cons_self) hx]
    | false =>
      have hMem' : e ∈ xs := by
        rcases List.mem_cons.mp hMem with h | h
        · subst h; rw [hp] at hx; cases hx
        · exact h
      exact find?_map_unique f p e xs hMem' hp
        (fun y hy hpy => hUniq y (List.mem_cons_of_mem _ hy) hpy)

theorem find?_map_none {α β : Type} (f : α → β) (p : β → Bool) :
    ∀ (es : List α), (∀ x, x ∈ es → p (f x) = false) → (es.map f).find? p = none
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.map_cons, List.find?_cons]
    rw [h x List.mem_cons_self]
    exact find?_map_none f p xs (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem natNotIn_map {α : Type} (k : α → Nat) (a : Nat) :
    ∀ (xs : List α), natNotIn a (xs.map k) = true → ∀ y, y ∈ xs → k y ≠ a
  | [], _, y, hy => by cases hy
  | x :: xs, h, y, hy => by
    have h' : (!Nat.beq a (k x) && natNotIn a (xs.map k)) = true := h
    cases hax : Nat.beq a (k x) with
    | true => rw [hax] at h'; cases h'
    | false =>
      rw [hax] at h'
      rcases List.mem_cons.mp hy with rfl | hy'
      · intro heq
        rw [heq, Nat.beq_refl] at hax
        cases hax
      · exact natNotIn_map k a xs h' y hy'

/-- Pairwise-distinct keys: two members with the same key are the same
member. -/
theorem natsUnique_map_inj {α : Type} (k : α → Nat) :
    ∀ (xs : List α), natsUnique (xs.map k) = true → ∀ x y, x ∈ xs → y ∈ xs → k x = k y → x = y
  | [], _, x, _, hx, _, _ => by cases hx
  | z :: zs, h, x, y, hx, hy, hk => by
    have h' : (natNotIn (k z) (zs.map k) && natsUnique (zs.map k)) = true := h
    cases hz : natNotIn (k z) (zs.map k) with
    | false => rw [hz] at h'; cases h'
    | true =>
      rw [hz] at h'
      rcases List.mem_cons.mp hx with rfl | hx'
      · rcases List.mem_cons.mp hy with rfl | hy'
        · rfl
        · exact absurd hk.symm (natNotIn_map k _ zs hz y hy')
      · rcases List.mem_cons.mp hy with rfl | hy'
        · exact absurd hk (natNotIn_map k _ zs hz x hx')
        · exact natsUnique_map_inj k zs h' x y hx' hy' hk

theorem lookupVTableByAlloc_mem :
    ∀ {es : List ProtoVTableEntry} {a : Nat} {e : ProtoVTableEntry},
      lookupVTableByAlloc es a = some e → e ∈ es
  | [], _, _, h => by cases h
  | x :: rest, a, e, h => by
    have h' : (match Nat.beq x.vtableAllocId a with
               | true => some x
               | false => lookupVTableByAlloc rest a) = some e := h
    cases hx : Nat.beq x.vtableAllocId a with
    | true => rw [hx] at h'; cases h'; exact List.mem_cons_self
    | false => rw [hx] at h'; exact List.mem_cons_of_mem _ (lookupVTableByAlloc_mem h')

theorem lookupVTableByAlloc_none :
    ∀ {es : List ProtoVTableEntry} {a : Nat},
      lookupVTableByAlloc es a = none → ∀ x, x ∈ es → x.vtableAllocId ≠ a
  | [], _, _, x, hx => by cases hx
  | z :: rest, a, h, x, hx => by
    have h' : (match Nat.beq z.vtableAllocId a with
               | true => some z
               | false => lookupVTableByAlloc rest a) = none := h
    cases hz : Nat.beq z.vtableAllocId a with
    | true => rw [hz] at h'; cases h'
    | false =>
      rw [hz] at h'
      rcases List.mem_cons.mp hx with rfl | hx'
      · intro heq
        rw [heq, Nat.beq_refl] at hz
        cases hz
      · exact lookupVTableByAlloc_none h' x hx'

/-- Uniqueness facts of a well-formed table. -/
theorem wf_unique {ptrBytes : Nat} {vt : ProtoVTableTable}
    (h : wfProtoVTableTable ptrBytes vt = true) :
    natsUnique (vt.entries.map (·.vtableId)) = true ∧
    natsUnique (vt.entries.map (·.vtableAllocId)) = true := by
  unfold wfProtoVTableTable at h
  cases h1 : allEntriesWf ptrBytes vt.entries vt.entries <;>
  cases h2 : natsUnique (vt.entries.map (·.vtableId)) <;>
  cases h3 : natsUnique (vt.entries.map (·.vtableAllocId)) <;>
  cases h4 : entriesPairwiseOk vt.entries <;>
  simp_all

omit [MemoryOps M] in
/-- Resolution of the vtable name of a table member in `prog.vtables`. -/
theorem mapGet_vtables (L : DynLayout M) (vt : ProtoVTableTable) (e : ProtoVTableEntry)
    (hMem : e ∈ vt.entries) (hIds : natsUnique (vt.entries.map (·.vtableId)) = true) :
    (vt.entries.map (fun e => (vtName e, vtableOf L e))).find?
        (fun x => decide (x.1 = vtName e)) = some (vtName e, vtableOf L e) := by
  refine find?_map_unique (fun e => (vtName e, vtableOf L e)) _ e vt.entries hMem
    (by simp) ?_
  intro x hx hpx
  have hname : vtName x = vtName e := by simpa using hpx
  have hid : x.vtableId = e.vtableId := by
    unfold vtName at hname
    injection hname with h1
    injection h1
  exact natsUnique_map_inj (·.vtableId) vt.entries hIds x e hx hMem hid

/-- **`vtable_from_ptr` succeeds on a captured vtable pointer.** On every
memory model `M` and base machine `m`, with an injective provenance map and a
well-formed table, the base pointer of the allocation of a captured vtable
resolves to exactly the translated `VTable`; `vtable_lookup` agrees. -/
theorem vtableFromPtrM_install_ok (L : DynLayout M) (vt : ProtoVTableTable)
    (m : Gen.Machine M) (ptrBytes a : Nat) (e : ProtoVTableEntry)
    (hProv : ∀ x y, L.provOf x = L.provOf y → x = y)
    (hWf : wfProtoVTableTable ptrBytes vt = true)
    (hLook : lookupVTableByAlloc vt.entries a = some e) :
    vtableFromPtrM (installVTables L vt m) (ptrAt L a 0) = .ok (vtableOf L e) ∧
    vtableLookupM (installVTables L vt m) (ptrAt L a 0) = .ok (vtableOf L e) := by
  obtain ⟨hIds, hAllocs⟩ := wf_unique hWf
  have hMem : e ∈ vt.entries := lookupVTableByAlloc_mem hLook
  have hA : e.vtableAllocId = a := lookupVTableByAlloc_allocId hLook
  have hFind :
      (vt.entries.map (fun e => (vtName e, vtPtr L e))).find?
          (fun x => decide (x.2 = ptrAt L a 0)) = some (vtName e, vtPtr L e) := by
    refine find?_map_unique (fun e => (vtName e, vtPtr L e)) _ e vt.entries hMem
      (by simp [vtPtr, hA]) ?_
    intro x hx hpx
    have hptr : vtPtr L x = ptrAt L a 0 := by simpa using hpx
    have hprov : L.provOf x.vtableAllocId = L.provOf a := by
      unfold vtPtr ptrAt at hptr
      injection hptr with _ h2
      injection h2
    have hid : x.vtableAllocId = e.vtableAllocId := by rw [hA]; exact hProv _ _ hprov
    exact natsUnique_map_inj (·.vtableAllocId) vt.entries hAllocs x e hx hMem hid
  have hGet := mapGet_vtables L vt e hMem hIds
  constructor
  · unfold vtableFromPtrM installVTables
    simp only [hFind, mapIndex, mapGet, hGet, Option.map_some]
    rfl
  · unfold vtableLookupM installVTables
    simp only [hFind, mapIndex, mapGet, hGet, Option.map_some]
    rfl

/-- **`vtable_from_ptr` is UB on every other pointer.** A pointer that is not
the base pointer of a captured vtable allocation throws MiniRust
`ub "invalid pointer for vtable lookup"`. -/
theorem vtableFromPtrM_install_ub (L : DynLayout M) (vt : ProtoVTableTable)
    (m : Gen.Machine M) (ptr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (hNe : ∀ x, x ∈ vt.entries → vtPtr L x ≠ ptr) :
    vtableFromPtrM (installVTables L vt m) ptr = ub "invalid pointer for vtable lookup" := by
  have hFind :
      (vt.entries.map (fun e => (vtName e, vtPtr L e))).find?
          (fun x => decide (x.2 = ptr)) = none :=
    find?_map_none _ _ vt.entries (fun x hx => by simpa using hNe x hx)
  unfold vtableFromPtrM installVTables
  simp only [hFind]

omit [MemoryOps M] in
/-- A pointer with a non-zero offset is never the base pointer of a vtable
allocation (with an injective provenance map). -/
theorem vtPtr_ne_ptrAt_offset (L : DynLayout M) (hProv : ∀ x y, L.provOf x = L.provOf y → x = y)
    (x : ProtoVTableEntry) (a off : Nat) (hOff : off ≠ 0) : vtPtr L x ≠ ptrAt L a off := by
  intro hEq
  unfold vtPtr ptrAt at hEq
  injection hEq with h1 h2
  injection h2 with h2
  have hxa : x.vtableAllocId = a := hProv _ _ h2
  rw [hxa] at h1
  have h0 : ((0 : Nat) : Int) = (off : Int) := Int.add_left_cancel h1
  exact hOff (by exact_mod_cast h0.symm)

/-- Invalid vtable pointers are UB in MiniRust exactly as in the prototype:
the base of an allocation that is not a captured vtable (unknown or data /
function allocation), a non-zero offset into any allocation, and a
provenance-less (dangling integer) pointer. -/
theorem vtableFromPtrM_install_invalid (L : DynLayout M) (vt : ProtoVTableTable)
    (m : Gen.Machine M) (hProv : ∀ x y, L.provOf x = L.provOf y → x = y) :
    (∀ a, lookupVTableByAlloc vt.entries a = none →
      vtableFromPtrM (installVTables L vt m) (ptrAt L a 0) =
        ub "invalid pointer for vtable lookup") ∧
    (∀ a off, off ≠ 0 →
      vtableFromPtrM (installVTables L vt m) (ptrAt L a off) =
        ub "invalid pointer for vtable lookup") ∧
    (∀ addr,
      vtableFromPtrM (installVTables L vt m) { addr := addr, provenance := none } =
        ub "invalid pointer for vtable lookup") := by
  refine ⟨?_, ?_, ?_⟩
  · intro a hNone
    refine vtableFromPtrM_install_ub L vt m _ (fun x hx hEq => ?_)
    have hprov : L.provOf x.vtableAllocId = L.provOf a := by
      unfold vtPtr ptrAt at hEq
      injection hEq with _ h2
      injection h2
    exact lookupVTableByAlloc_none hNone x hx (hProv _ _ hprov)
  · intro a off hOff
    exact vtableFromPtrM_install_ub L vt m _
      (fun x _ => vtPtr_ne_ptrAt_offset L hProv x a off hOff)
  · intro addr
    refine vtableFromPtrM_install_ub L vt m _ (fun x _ hEq => ?_)
    unfold vtPtr ptrAt at hEq
    injection hEq with _ h2
    cases h2

/-- **`compute_size` / `compute_align` equal the prototype's dynamic layout.**
For a captured vtable `e` of a well-formed table, on every memory model:
MiniRust `Machine::compute_size` and `Machine::compute_align` at
`LayoutStrategy::TraitObject` with the vtable pointer of `e` return exactly the
values `dynSizeOfValProto` and `dynAlignOfValProto` return on a trait-object
pointer (any data word) carrying that vtable pointer. -/
theorem computeSizeAlignM_eq_dynLayoutProto (L : DynLayout M) (vt : ProtoVTableTable)
    (m : Gen.Machine M) (ptrBytes : Nat) (e : ProtoVTableEntry) (d : ProtoDataWord)
    (tn : Gen.TraitName)
    (hProv : ∀ x y, L.provOf x = L.provOf y → x = y)
    (hWf : wfProtoVTableTable ptrBytes vt = true)
    (hPred : e.traitPred.failsClosed = false)
    (hLook : lookupVTableByAlloc vt.entries e.vtableAllocId = some e) :
    computeSizeM (installVTables L vt m) (.TraitObject tn)
        (some (.VTablePointer (vtPtr L e))) = .ok ⟨e.sizeBytes⟩ ∧
    computeAlignM (installVTables L vt m) (.TraitObject tn)
        (some (.VTablePointer (vtPtr L e))) = .ok ⟨e.alignBytes⟩ ∧
    dynSizeOfValProto vt ptrBytes e.traitPred (mkDynPtr ptrBytes d e) = .ok e.sizeBytes ∧
    dynAlignOfValProto vt ptrBytes e.traitPred (mkDynPtr ptrBytes d e) = .ok e.alignBytes := by
  have hLk := (vtableFromPtrM_install_ok L vt m ptrBytes e.vtableAllocId e hProv hWf hLook).2
  have hRes : resolveVTablePtr vt e.traitPred (vtablePtrOf e) = .ok e :=
    (resolveVTablePtr_ok_iff vt e.traitPred (vtablePtrOf e) e).mpr
      ⟨rfl, hLook, traitPredEq_refl _⟩
  have hProto := dynLayoutOfValProto_ok vt ptrBytes e.traitPred (mkDynPtr ptrBytes d e) d
    (vtablePtrOf e) e hPred hWf (decodeWidePtr?_encodeWidePtr _ _) hRes
  refine ⟨?_, ?_, hProto.2.1, hProto.2.2⟩
  · unfold computeSizeM
    simp only [LayoutStrategy.compute_size_and_align, vtPtr, hLk, bind, Except.bind, pure,
      Except.pure, vtableOf]
  · unfold computeAlignM
    simp only [LayoutStrategy.compute_size_and_align, vtPtr, hLk, bind, Except.bind, pure,
      Except.pure, vtableOf]

/-- **Universal iff for `vtableFromPtrM`:** on any memory model `M`, well-formed
table `vt`, and injective provenance map `L`, `vtableFromPtrM` resolves
`ptrAt L a off` to `v` if and only if `off = 0` and `lookupVTableByAlloc` finds
an entry `e` with `v = vtableOf L e` (which matches `resolveVTablePtr` up to
the trait-predicate check). -/
theorem vtableFromPtrM_install_iff (L : DynLayout M) (vt : ProtoVTableTable)
    (m : Gen.Machine M) (ptrBytes a off : Nat) (v : Gen.VTable)
    (hProv : ∀ x y, L.provOf x = L.provOf y → x = y)
    (hWf : wfProtoVTableTable ptrBytes vt = true) :
    vtableFromPtrM (installVTables L vt m) (ptrAt L a off) = .ok v ↔
      (off = 0 ∧ ∃ e, lookupVTableByAlloc vt.entries a = some e ∧ v = vtableOf L e) := by
  constructor
  · intro hOk
    cases off with
    | zero =>
      cases hL : lookupVTableByAlloc vt.entries a with
      | none =>
        have hUb := (vtableFromPtrM_install_invalid L vt m hProv).1 a hL
        rw [hUb] at hOk
        cases hOk
      | some e =>
        have hRes := (vtableFromPtrM_install_ok L vt m ptrBytes a e hProv hWf hL).1
        rw [hRes] at hOk
        cases hOk
        exact ⟨rfl, e, rfl, rfl⟩
    | succ k =>
      have hUb := (vtableFromPtrM_install_invalid L vt m hProv).2.1 a (k + 1) (Nat.succ_ne_zero k)
      rw [hUb] at hOk
      cases hOk
  · rintro ⟨rfl, e, hL, rfl⟩
    exact (vtableFromPtrM_install_ok L vt m ptrBytes a e hProv hWf hL).1

/-- **Universal `checkPtrMetadataM` correspondence (valid, trait mismatch,
invalid vtable pointer, non-vtable metadata).** -/
theorem checkPtrMetadataM_install_correspondence (L : DynLayout M) (vt : ProtoVTableTable)
    (m : Gen.Machine M) (ptrBytes a : Nat) (e : ProtoVTableEntry) (tn : Gen.TraitName)
    (hProv : ∀ x y, L.provOf x = L.provOf y → x = y)
    (hWf : wfProtoVTableTable ptrBytes vt = true)
    (hLook : lookupVTableByAlloc vt.entries a = some e)
    (hBounds : inBounds (ptrAt L a 0).addr .Unsigned x86_64.PTR_SIZE = true) :
    checkPtrMetadataM (some (.VTablePointer (ptrAt L a 0))) (.VTablePointer (traitName L e.traitPred))
        (some (vtableFromPtrM (installVTables L vt m))) = .ok () ∧
    (traitName L e.traitPred ≠ tn →
      checkPtrMetadataM (some (.VTablePointer (ptrAt L a 0))) (.VTablePointer tn)
          (some (vtableFromPtrM (installVTables L vt m))) =
        ub "Value::Ptr: invalid vtable in metadata") ∧
    (∀ (off : Nat), off ≠ 0 → inBounds (ptrAt L a off).addr .Unsigned x86_64.PTR_SIZE = true →
      checkPtrMetadataM (some (.VTablePointer (ptrAt L a off))) (.VTablePointer tn)
          (some (vtableFromPtrM (installVTables L vt m))) =
        ub "invalid pointer for vtable lookup") ∧
    checkPtrMetadataM (some (.ElementCount 3)) (.VTablePointer tn)
        (some (vtableFromPtrM (installVTables L vt m))) =
      ub "Value::Ptr: invalid metadata" ∧
    checkPtrMetadataM none (.VTablePointer tn)
        (some (vtableFromPtrM (installVTables L vt m))) =
      ub "Value::Ptr: invalid metadata" := by
  have hVt := (vtableFromPtrM_install_ok L vt m ptrBytes a e hProv hWf hLook).1
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · unfold checkPtrMetadataM
    simp only [hBounds, ensureElseUb, hVt, vtableOf, beq_self_eq_true,
      Bool.not_true, Bool.false_eq_true, ite_false, bind, Except.bind, pure, Except.pure]
  · intro hNe
    have hBeq : (traitName L e.traitPred == tn) = false := by
      cases hb : (traitName L e.traitPred == tn) with
      | false => rfl
      | true => exact absurd (eq_of_beq hb) hNe
    unfold checkPtrMetadataM
    simp only [hBounds, ensureElseUb, ite_true, hVt, vtableOf, hBeq,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, bind, Except.bind, pure, Except.pure]
  · intro off hOff hBOff
    have hUb := (vtableFromPtrM_install_invalid L vt m hProv).2.1 a off hOff
    unfold checkPtrMetadataM
    simp only [hBOff, ensureElseUb, Bool.not_true, Bool.false_eq_true, ite_false,
      hUb, bind, Except.bind, pure, Except.pure, ub]

/-- **Universal MiniRust raw-pointer dyn validity (`checkPtrM` on `PtrType.Raw`).**
Matching `unsizeSizedToDyn_raw_ptr_unchecked` and `unsizeSizedToDyn_raw_scalar_unchecked`,
a raw pointer `*const dyn Trait` with a valid vtable pointer is accepted for
EVERY in-bounds thin data pointer `dataPtr` — even null, unaligned, dangling, or
provenance-less. -/
theorem checkPtrM_raw_dyn_unchecked (L : DynLayout M) (vt : ProtoVTableTable)
    (m : Gen.Machine M) (ptrBytes : Nat) (e : ProtoVTableEntry)
    (dataPtr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (hProv : ∀ x y, L.provOf x = L.provOf y → x = y)
    (hWf : wfProtoVTableTable ptrBytes vt = true)
    (hLook : lookupVTableByAlloc vt.entries e.vtableAllocId = some e)
    (hDataBounds : inBounds dataPtr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hVtBounds : inBounds (vtPtr L e).addr .Unsigned x86_64.PTR_SIZE = true) :
    checkPtrM { thin_pointer := dataPtr, metadata := some (.VTablePointer (vtPtr L e)) }
        (.Raw (.VTablePointer (traitName L e.traitPred)))
        (some (installVTables L vt m)) = .ok () := by
  have hMeta :=
    (checkPtrMetadataM_install_correspondence L vt m ptrBytes e.vtableAllocId e
      (traitName L e.traitPred) hProv hWf hLook hVtBounds).1
  unfold checkPtrM
  simp only [hDataBounds, ensureElseUb, PtrType.meta_kind, Option.map_some,
    vtPtr, hMeta, PtrType.safe_pointee, Bool.not_true, Bool.false_eq_true, ite_false,
    bind, Except.bind, pure, Except.pure]

private theorem inBounds_zero_unsigned_ptr :
    inBounds (0 : Int) .Unsigned x86_64.PTR_SIZE = true := by
  unfold inBounds
  have h1 : decide ((0 : Int) ≤ 0) = true := decide_eq_true (Int.le_refl 0)
  have h2 : decide ((0 : Int) < (2 : Int) ^ Size.bits x86_64.PTR_SIZE) = true :=
    decide_eq_true (Int.pow_pos (by decide : (0 : Int) < 2))
  rw [h1, h2]
  rfl

private theorem ensureElseUb_true (msg : String) : ensureElseUb true msg = .ok () := rfl
private theorem ensureElseUb_false (msg : String) : ensureElseUb false msg = ub msg := rfl
private theorem bind_ok_interp {α β : Type} (x : α) (f : α → Interp β) :
    (Except.ok x >>= f) = f x := rfl
private theorem bind_pure_interp {α β : Type} (x : α) (f : α → Interp β) :
    (pure x >>= f) = f x := rfl
private theorem bind_ub_interp {α β : Type} (msg : String) (f : α → Interp β) :
    (ub msg >>= f) = ub msg := rfl

/-- **Universal MiniRust safe-reference dyn rejections (`checkPtrM` on `PtrType.Ref`).**
On a safe `&dyn Trait` / `&mut dyn Trait` pointer with a valid vtable pointer
and `size <= isize::MAX`, MiniRust rejects null, unaligned, and uninhabited
referents with exact UB messages matching `refDataValid`. -/
theorem checkPtrM_ref_dyn_rejects_invalid (L : DynLayout M) (vt : ProtoVTableTable)
    (m : Gen.Machine M) (ptrBytes : Nat) (e : ProtoVTableEntry)
    (mutbl : LibSpecr.Mutability) (freeze unpin : Bool)
    (hProv : ∀ x y, L.provOf x = L.provOf y → x = y)
    (hWf : wfProtoVTableTable ptrBytes vt = true)
    (hLook : lookupVTableByAlloc vt.entries e.vtableAllocId = some e)
    (hVtBounds : inBounds (vtPtr L e).addr .Unsigned x86_64.PTR_SIZE = true)
    (hSizeSigned : inBounds (e.sizeBytes : Int) .Signed x86_64.PTR_SIZE = true) :
    (∀ (prov : Option (Gen.Memory.Provenance M)),
      checkPtrM
          { thin_pointer := { addr := 0, provenance := prov }
            metadata := some (.VTablePointer (vtPtr L e)) }
          (.Ref mutbl
            { layout := .TraitObject (traitName L e.traitPred), inhabited := true,
              unsafe_cells := .TraitObject, freeze := freeze, unpin := unpin })
          (some (installVTables L vt m)) = ub "Value::Ptr: null safe pointer") ∧
    (∀ (dataPtr : Gen.ThinPointer (Gen.Memory.Provenance M)),
      inBounds dataPtr.addr .Unsigned x86_64.PTR_SIZE = true →
      dataPtr.addr ≠ 0 →
      Align.is_aligned ⟨e.alignBytes⟩ dataPtr.addr = false →
      checkPtrM
          { thin_pointer := dataPtr, metadata := some (.VTablePointer (vtPtr L e)) }
          (.Ref mutbl
            { layout := .TraitObject (traitName L e.traitPred), inhabited := true,
              unsafe_cells := .TraitObject, freeze := freeze, unpin := unpin })
          (some (installVTables L vt m)) = ub "Value::Ptr: unaligned safe pointer") ∧
    (∀ (dataPtr : Gen.ThinPointer (Gen.Memory.Provenance M)),
      inBounds dataPtr.addr .Unsigned x86_64.PTR_SIZE = true →
      dataPtr.addr ≠ 0 →
      Align.is_aligned ⟨e.alignBytes⟩ dataPtr.addr = true →
      checkPtrM
          { thin_pointer := dataPtr, metadata := some (.VTablePointer (vtPtr L e)) }
          (.Ref mutbl
            { layout := .TraitObject (traitName L e.traitPred), inhabited := false,
              unsafe_cells := .TraitObject, freeze := freeze, unpin := unpin })
          (some (installVTables L vt m)) = ub "Value::Ptr: safe pointer to uninhabited type") := by
  have hMeta :=
    (checkPtrMetadataM_install_correspondence L vt m ptrBytes e.vtableAllocId e
      (traitName L e.traitPred) hProv hWf hLook hVtBounds).1
  have hLk := (vtableFromPtrM_install_ok L vt m ptrBytes e.vtableAllocId e hProv hWf hLook).2
  refine ⟨?_, ?_, ?_⟩
  · intro prov
    unfold checkPtrM
    rw [inBounds_zero_unsigned_ptr, ensureElseUb_true, bind_ok_interp]
    dsimp only [PtrType.meta_kind, LayoutStrategy.meta_kind, Option.map_some, vtPtr]
    rw [hMeta, bind_ok_interp]
    dsimp only [PtrType.safe_pointee, LayoutStrategy.compute_size_and_align]
    rw [hLk, bind_ok_interp]
    dsimp only [vtableOf]
    rw [bind_pure_interp]
    dsimp only
    rw [hSizeSigned, ensureElseUb_true, bind_ok_interp, bne_self_eq_false, ensureElseUb_false,
      bind_ub_interp]
  · intro dataPtr hB hNz hUnal
    have hNzB : (dataPtr.addr != 0) = true := bne_iff_ne.mpr hNz
    unfold checkPtrM
    rw [hB, ensureElseUb_true, bind_ok_interp]
    dsimp only [PtrType.meta_kind, LayoutStrategy.meta_kind, Option.map_some, vtPtr]
    rw [hMeta, bind_ok_interp]
    dsimp only [PtrType.safe_pointee, LayoutStrategy.compute_size_and_align]
    rw [hLk, bind_ok_interp]
    dsimp only [vtableOf]
    rw [bind_pure_interp]
    dsimp only
    rw [hSizeSigned, ensureElseUb_true, bind_ok_interp, hNzB, ensureElseUb_true, bind_ok_interp,
      hUnal, ensureElseUb_false, bind_ub_interp]
  · intro dataPtr hB hNz hAl
    have hNzB : (dataPtr.addr != 0) = true := bne_iff_ne.mpr hNz
    unfold checkPtrM
    rw [hB, ensureElseUb_true, bind_ok_interp]
    dsimp only [PtrType.meta_kind, LayoutStrategy.meta_kind, Option.map_some, vtPtr]
    rw [hMeta, bind_ok_interp]
    dsimp only [PtrType.safe_pointee, LayoutStrategy.compute_size_and_align]
    rw [hLk, bind_ok_interp]
    dsimp only [vtableOf]
    rw [bind_pure_interp]
    dsimp only
    rw [hSizeSigned, ensureElseUb_true, bind_ok_interp, hNzB, ensureElseUb_true, bind_ok_interp,
      hAl, ensureElseUb_true, bind_ok_interp, ensureElseUb_false, bind_ub_interp]

omit [MemoryOps M] in
/-- Slot lookup in `methodsFrom` agrees with `get? slots` on every `.method` slot. -/
theorem methodsFrom_find?_method (L : DynLayout M) :
    ∀ (base idx : Nat) (slots : List ProtoVTableSlot) (defPath : String),
      get? slots idx = some (.method defPath) →
      (methodsFrom L base slots).find? (fun p => decide (p.1 = ⟨⟨base + idx⟩⟩)) =
        some (⟨⟨base + idx⟩⟩, ⟨⟨L.fnOf defPath⟩⟩)
  | _, _, [], _, h => by cases h
  | base, 0, .method dp :: rest, defPath, h => by
    cases h
    simp [methodsFrom]
  | base, 0, .dropInPlace _ :: _, _, h => by cases h
  | base, 0, .size :: _, _, h => by cases h
  | base, 0, .align :: _, _, h => by cases h
  | base, 0, .vacant :: _, _, h => by cases h
  | base, 0, .traitVPtr _ :: _, _, h => by cases h
  | base, idx + 1, s :: rest, defPath, h => by
    have hStep : base + (idx + 1) = (base + 1) + idx := by omega
    have ih := methodsFrom_find?_method L (base + 1) idx rest defPath h
    rw [hStep]
    cases s with
    | method dp =>
      simp only [methodsFrom, List.find?_cons]
      have hNe : ¬ (({ _0 := { idx := base } } : Gen.TraitMethodName) = ⟨⟨base + 1 + idx⟩⟩) := by
        intro heq; injection heq with h1; injection h1 with h2; omega
      simp [hNe, ih]
    | dropInPlace _ => exact ih
    | size => exact ih
    | align => exact ih
    | vacant => exact ih
    | traitVPtr _ => exact ih

/-- **Universal `evalUnOpM` correspondence for `.GetMetadata`, `.ComputeSize`,
`.ComputeAlign`, and `.VTableMethodLookup`.** Across every memory model `M`
(including `Mach` and `MachTB`), well-formed table `vt`, and captured vtable `e`:
* `GetMetadata` extracts the vtable pointer `vtPtr L e`;
* `ComputeSize` / `ComputeAlign` return `e.sizeBytes` / `e.alignBytes` (matching
  `dynSizeOfValProto` / `dynAlignOfValProto`);
* `VTableMethodLookup ⟨⟨slotIdx⟩⟩` resolves to `fn_ptrs[L.fnOf defPath]`
  whenever `get? e.slots slotIdx = some (.method defPath)`. -/
theorem evalUnOpM_dyn_correspondence (L : DynLayout M) (vt : ProtoVTableTable)
    (m : Gen.Machine M) (ptrBytes slotIdx : Nat) (e : ProtoVTableEntry) (defPath : String)
    (dataPtr fnThin : Gen.ThinPointer (Gen.Memory.Provenance M)) (ptrTy : Gen.PtrType)
    (hProv : ∀ x y, L.provOf x = L.provOf y → x = y)
    (hWf : wfProtoVTableTable ptrBytes vt = true)
    (hLook : lookupVTableByAlloc vt.entries e.vtableAllocId = some e)
    (hVtBounds : inBounds (vtPtr L e).addr .Unsigned x86_64.PTR_SIZE = true)
    (hMetaKind : PtrType.meta_kind ptrTy = .VTablePointer (traitName L e.traitPred))
    (hSlot : get? e.slots slotIdx = some (.method defPath))
    (hFnPtr : mapGet m.fn_ptrs ⟨⟨L.fnOf defPath⟩⟩ = some fnThin) :
    let m' := installVTables L vt m
    let vtVal : Gen.Value M := .Ptr (ThinPointer.widen (vtPtr L e) none)
    let tn := traitName L e.traitPred
    evalUnOpM .GetMetadata
        (.Ptr { thin_pointer := dataPtr, metadata := some (.VTablePointer (vtPtr L e)) }, .Ptr ptrTy)
        (some m') = .ok (vtVal, .Ptr (.VTablePtr tn)) ∧
    evalUnOpM (.ComputeSize (.TraitObject tn)) (vtVal, .Ptr (.VTablePtr tn)) (some m') =
      .ok (.Int (e.sizeBytes : Int), .Int IntType.usize_ty) ∧
    evalUnOpM (.ComputeAlign (.TraitObject tn)) (vtVal, .Ptr (.VTablePtr tn)) (some m') =
      .ok (.Int (e.alignBytes : Int), .Int IntType.usize_ty) ∧
    evalUnOpM (.VTableMethodLookup ⟨⟨slotIdx⟩⟩) (vtVal, .Ptr (.VTablePtr tn)) (some m') =
      .ok (.Ptr (ThinPointer.widen fnThin none), .Ptr .FnPtr) := by
  intro m' vtVal tn
  have hOk := vtableFromPtrM_install_ok L vt m ptrBytes e.vtableAllocId e hProv hWf hLook
  have hVt : vtableFromPtrM m' (vtPtr L e) = .ok (vtableOf L e) := hOk.1
  have hLk : vtableLookupM m' (vtPtr L e) = .ok (vtableOf L e) := hOk.2
  have hMethod :
      mapIndex (vtableOf L e).methods ⟨⟨slotIdx⟩⟩ "vtable.methods[method]" =
        .ok ⟨⟨L.fnOf defPath⟩⟩ := by
    have hf := methodsFrom_find?_method L 0 slotIdx e.slots defPath hSlot
    simp only [Nat.zero_add] at hf
    unfold mapIndex mapGet vtableOf
    simp only [hf, Option.map_some]
    rfl
  have hFnIdx : mapIndex m'.fn_ptrs ⟨⟨L.fnOf defPath⟩⟩ "self.fn_ptrs[fn_name]" = .ok fnThin := by
    unfold mapIndex m' installVTables
    simp only [hFnPtr]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold evalUnOpM
    dsimp only
    rw [hMetaKind]
    simp only [PointerMetaKind.encode_as_valueM, PointerMetaKind.ty, checkValueM,
      checkPtrM, vtVal, ThinPointer.widen, hVtBounds, ensureElseUb,
      PtrType.meta_kind, checkPtrMetadataM, PtrType.safe_pointee, hVt, vtableOf,
      beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ite_false,
      bind, Except.bind, pure, Except.pure, tn]
  · unfold evalUnOpM
    simp only [Type.meta_kind, PointerMetaKind.decode_valueM, Type.layout, computeSizeM,
      LayoutStrategy.compute_size_and_align, vtVal, ThinPointer.widen, hLk, vtableOf,
      bind, Except.bind, pure, Except.pure]
  · unfold evalUnOpM
    simp only [Type.meta_kind, PointerMetaKind.decode_valueM, Type.layout, computeAlignM,
      LayoutStrategy.compute_size_and_align, vtVal, ThinPointer.widen, hLk, vtableOf,
      bind, Except.bind, pure, Except.pure]
  · unfold evalUnOpM
    simp only [vtVal, ThinPointer.widen, hLk, hMethod, hFnIdx, bind, Except.bind, pure,
      Except.pure]

/-! ### `Mach` (`BasicMemory`) and `MachTB` (`TreeBorrowsMemory`) instances -/

/-- Layout for `Mach`: provenance `(⟨a⟩, ())` and base address `a * 65536`,
the canonical `Trusted` address of an unbacked pointer (`ptrAddress?`). -/
def bmLayout (traitOf : ProtoTraitPred → Nat) (fnOf : String → Nat) : DynLayout BM :=
  { provOf := fun a => (⟨(a : Int)⟩, ()), addrOf := fun a => (a : Int) * 65536,
    traitOf := traitOf, fnOf := fnOf }

/-- Layout for `MachTB`: root provenance `(⟨a⟩, [])` and the same addresses. -/
def tbLayout (traitOf : ProtoTraitPred → Nat) (fnOf : String → Nat) : DynLayout TBM :=
  { provOf := fun a => (⟨(a : Int)⟩, []), addrOf := fun a => (a : Int) * 65536,
    traitOf := traitOf, fnOf := fnOf }

theorem bmLayout_provOf_inj (traitOf : ProtoTraitPred → Nat) (fnOf : String → Nat) :
    ∀ x y, (bmLayout traitOf fnOf).provOf x = (bmLayout traitOf fnOf).provOf y → x = y := by
  intro x y h
  have h1 : ((⟨(x : Int)⟩ : Gen.AllocId), ()) = ((⟨(y : Int)⟩ : Gen.AllocId), ()) := h
  injection h1 with h2 _
  injection h2 with h3
  exact_mod_cast h3

theorem tbLayout_provOf_inj (traitOf : ProtoTraitPred → Nat) (fnOf : String → Nat) :
    ∀ x y, (tbLayout traitOf fnOf).provOf x = (tbLayout traitOf fnOf).provOf y → x = y := by
  intro x y h
  have h1 : ((⟨(x : Int)⟩ : Gen.AllocId), ([] : Gen.Path)) =
      ((⟨(y : Int)⟩ : Gen.AllocId), ([] : Gen.Path)) := h
  injection h1 with h2 _
  injection h2 with h3
  exact_mod_cast h3

/-- Empty MiniRust program. -/
def emptyProgram : Gen.Program :=
  { functions := ⟨[]⟩, start := ⟨⟨0⟩⟩, globals := ⟨[]⟩, traits := ⟨[]⟩, vtables := ⟨[]⟩ }

/-- `Mach` with the given allocations and function pointers and nothing else. -/
def baseMach (allocs : List Gen.Allocation) (fnPtrs : List (Gen.FnName × Ptr) := []) : Mach :=
  { prog := emptyProgram
    mem := { memory := { allocations := allocs, _phantom := {} }, accesses := [] }
    intptrcast := ⟨⟨[]⟩⟩, threads := [], active_thread := 0, synchronized_threads := ⟨[]⟩
    locks := [], global_ptrs := ⟨[]⟩, fn_ptrs := ⟨fnPtrs⟩, vtable_ptrs := ⟨[]⟩
    stdout := ⟨[]⟩, stderr := ⟨[]⟩ }

/-- `MachTB` with the given allocations and function pointers and nothing
else. -/
def baseMachTB (allocs : List (Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra))
    (fnPtrs : List (Gen.FnName × Gen.ThinPointer Gen.TreeBorrowsProvenance) := []) : MachTB :=
  { prog := emptyProgram
    mem :=
      { memory := { params := ⟨true⟩, mem := { allocations := allocs, _phantom := {} } }
        accesses := [] }
    intptrcast := ⟨⟨[]⟩⟩, threads := [], active_thread := 0, synchronized_threads := ⟨[]⟩
    locks := [], global_ptrs := ⟨[]⟩, fn_ptrs := ⟨fnPtrs⟩, vtable_ptrs := ⟨[]⟩
    stdout := ⟨[]⟩, stderr := ⟨[]⟩ }

/-- **`Mach` (`BasicMemory`), monomorphic functions.** The monomorphic
`MiniRustSpec.Interp.vtableFromPtr`, `vtableLookup`, `computeSize`, and
`computeAlign` satisfy the same laws as their polymorphic versions on a `Mach`
with the vtable table installed. -/
theorem mach_install_ok (L : DynLayout BM) (vt : ProtoVTableTable) (m : Mach)
    (ptrBytes a : Nat) (e : ProtoVTableEntry) (tn : Gen.TraitName)
    (hProv : ∀ x y, L.provOf x = L.provOf y → x = y)
    (hWf : wfProtoVTableTable ptrBytes vt = true)
    (hLook : lookupVTableByAlloc vt.entries a = some e) :
    vtableFromPtr (installVTables L vt m) (ptrAt L a 0) = .ok (vtableOf L e) ∧
    vtableLookup (installVTables L vt m) (ptrAt L a 0) = .ok (vtableOf L e) ∧
    computeSize (installVTables L vt m) (.TraitObject tn)
        (some (.VTablePointer (ptrAt L a 0))) = .ok ⟨e.sizeBytes⟩ ∧
    computeAlign (installVTables L vt m) (.TraitObject tn)
        (some (.VTablePointer (ptrAt L a 0))) = .ok ⟨e.alignBytes⟩ := by
  obtain ⟨hIds, hAllocs⟩ := wf_unique hWf
  have hMem : e ∈ vt.entries := lookupVTableByAlloc_mem hLook
  have hA : e.vtableAllocId = a := lookupVTableByAlloc_allocId hLook
  have hFind :
      (vt.entries.map (fun e => (vtName e, vtPtr L e))).find?
          (fun x => decide (x.2 = ptrAt L a 0)) = some (vtName e, vtPtr L e) := by
    refine find?_map_unique (fun e => (vtName e, vtPtr L e)) _ e vt.entries hMem
      (by simp [vtPtr, hA]) ?_
    intro x hx hpx
    have hptr : vtPtr L x = ptrAt L a 0 := by simpa using hpx
    have hprov : L.provOf x.vtableAllocId = L.provOf a := by
      unfold vtPtr ptrAt at hptr
      injection hptr with _ h2
      injection h2
    have hid : x.vtableAllocId = e.vtableAllocId := by rw [hA]; exact hProv _ _ hprov
    exact natsUnique_map_inj (·.vtableAllocId) vt.entries hAllocs x e hx hMem hid
  have hGet := mapGet_vtables L vt e hMem hIds
  have hLk : vtableLookup (installVTables L vt m) (ptrAt L a 0) = .ok (vtableOf L e) := by
    unfold vtableLookup installVTables
    simp only [hFind, mapIndex, mapGet, hGet, Option.map_some]
    rfl
  refine ⟨?_, hLk, ?_, ?_⟩
  · unfold vtableFromPtr installVTables
    simp only [hFind, mapIndex, mapGet, hGet, Option.map_some]
    rfl
  · unfold computeSize
    simp only [LayoutStrategy.compute_size_and_align, hLk, bind, Except.bind, pure,
      Except.pure, vtableOf]
  · unfold computeAlign
    simp only [LayoutStrategy.compute_size_and_align, hLk, bind, Except.bind, pure,
      Except.pure, vtableOf]

/-- **`Mach`, invalid pointers.** The monomorphic `vtableFromPtr` throws
`ub "invalid pointer for vtable lookup"` on a pointer that is not the base
pointer of a captured vtable allocation. -/
theorem mach_install_ub (L : DynLayout BM) (vt : ProtoVTableTable) (m : Mach) (ptr : Ptr)
    (hNe : ∀ x, x ∈ vt.entries → vtPtr L x ≠ ptr) :
    vtableFromPtr (installVTables L vt m) ptr = ub "invalid pointer for vtable lookup" := by
  have hFind :
      (vt.entries.map (fun e => (vtName e, vtPtr L e))).find?
          (fun x => decide (x.2 = ptr)) = none :=
    find?_map_none _ _ vt.entries (fun x hx => by simpa using hNe x hx)
  unfold vtableFromPtr installVTables
  simp only [hFind]

/-- **`Mach` and `MachTB` correspondence.** For a well-formed table and a
captured vtable `e`, on `Mach` and on `MachTB` alike: `vtable_from_ptr` of the
vtable pointer of `e` is the translated `VTable`, and `compute_size` /
`compute_align` at `LayoutStrategy::TraitObject` return the size and alignment
`dynSizeOfValProto` / `dynAlignOfValProto` return. -/
theorem mach_and_machTB_vtable_correspondence
    (traitOf : ProtoTraitPred → Nat) (fnOf : String → Nat) (vt : ProtoVTableTable)
    (ptrBytes : Nat) (e : ProtoVTableEntry) (d : ProtoDataWord) (tn : Gen.TraitName)
    (m : Mach) (mTB : MachTB)
    (hWf : wfProtoVTableTable ptrBytes vt = true)
    (hPred : e.traitPred.failsClosed = false)
    (hLook : lookupVTableByAlloc vt.entries e.vtableAllocId = some e) :
    (vtableFromPtr (installVTables (bmLayout traitOf fnOf) vt m)
        (vtPtr (bmLayout traitOf fnOf) e) = .ok (vtableOf (bmLayout traitOf fnOf) e) ∧
      computeSize (installVTables (bmLayout traitOf fnOf) vt m) (.TraitObject tn)
        (some (.VTablePointer (vtPtr (bmLayout traitOf fnOf) e))) = .ok ⟨e.sizeBytes⟩ ∧
      computeAlign (installVTables (bmLayout traitOf fnOf) vt m) (.TraitObject tn)
        (some (.VTablePointer (vtPtr (bmLayout traitOf fnOf) e))) = .ok ⟨e.alignBytes⟩) ∧
    (vtableFromPtrM (installVTables (tbLayout traitOf fnOf) vt mTB)
        (vtPtr (tbLayout traitOf fnOf) e) = .ok (vtableOf (tbLayout traitOf fnOf) e) ∧
      computeSizeM (installVTables (tbLayout traitOf fnOf) vt mTB) (.TraitObject tn)
        (some (.VTablePointer (vtPtr (tbLayout traitOf fnOf) e))) = .ok ⟨e.sizeBytes⟩ ∧
      computeAlignM (installVTables (tbLayout traitOf fnOf) vt mTB) (.TraitObject tn)
        (some (.VTablePointer (vtPtr (tbLayout traitOf fnOf) e))) = .ok ⟨e.alignBytes⟩) ∧
    dynSizeOfValProto vt ptrBytes e.traitPred (mkDynPtr ptrBytes d e) = .ok e.sizeBytes ∧
    dynAlignOfValProto vt ptrBytes e.traitPred (mkDynPtr ptrBytes d e) = .ok e.alignBytes := by
  have hB := computeSizeAlignM_eq_dynLayoutProto (bmLayout traitOf fnOf) vt m ptrBytes e d tn
    (bmLayout_provOf_inj traitOf fnOf) hWf hPred hLook
  have hT := computeSizeAlignM_eq_dynLayoutProto (tbLayout traitOf fnOf) vt mTB ptrBytes e d tn
    (tbLayout_provOf_inj traitOf fnOf) hWf hPred hLook
  have hFB := (vtableFromPtrM_install_ok (bmLayout traitOf fnOf) vt m ptrBytes e.vtableAllocId e
    (bmLayout_provOf_inj traitOf fnOf) hWf hLook).1
  have hFT := (vtableFromPtrM_install_ok (tbLayout traitOf fnOf) vt mTB ptrBytes e.vtableAllocId e
    (tbLayout_provOf_inj traitOf fnOf) hWf hLook).1
  have hM := mach_install_ok (bmLayout traitOf fnOf) vt m ptrBytes e.vtableAllocId e tn
    (bmLayout_provOf_inj traitOf fnOf) hWf hLook
  exact ⟨⟨hM.1, hM.2.2.1, hM.2.2.2⟩, ⟨hFT, hT.1, hT.2.1⟩, hB.2.2.1, hB.2.2.2⟩

end MR

/-! ## §9. Parametric `lean-miri` authority contract

`lean-miri`'s vendored interpreter (`Miri.Interpreter.{VTable, VTableMachine,
VirtualCalls, DynamicLayout, Cast}`) is only in the `examples/` Lake package,
so this module cannot import it. The contract is therefore parametric: an
`LmDynAuthority` answers `LmQuery`s about a `ProtoVTableTable`, `protoLmRun` is
the prototype's answer computed with the rules of §3-§5, and `LmDynContract`
states their agreement law by law. The cross-root bridge in
`tests/mir/DynTraitUnsizeProtoTests.lean` builds the authority over the
vendored functions and kernel-checks `lmAuthorityCheck` for it. -/

namespace Lm

/-- Pointer of a query or observation: an allocation with an offset, or a
provenance-less integer address. -/
inductive LmPtr : Type where
  | prov (allocId off : Nat)
  | int (addr : Nat)
  deriving DecidableEq

/-- Error class of a `lean-miri` operation. -/
inductive LmErr : Type where
  /-- `undefinedBehavior "InvalidVTablePointer"`. -/
  | invalidVTablePointer
  /-- `undefinedBehavior "InvalidVTableTrait"`. -/
  | invalidVTableTrait
  /-- `undefinedBehavior "dyn call trying to call something that is not a method"`. -/
  | notAMethod
  /-- `undefinedBehavior "InvalidUninitBytes"`. -/
  | uninitBytes
  | otherUb
  | unsupported
  | other
  deriving DecidableEq

/-- Observation of a `lean-miri` operation. -/
inductive LmObs : Type where
  /-- Concrete type of a vtable (`VTable.getPtrVTableTypeRead`). -/
  | tyOk (tyId : Nat)
  /-- Size and alignment in bytes (`VTable.getSizeAndAlignRead`,
  `DynamicLayout.sizeAndAlignFromMeta`). -/
  | sizeAlign (size align : Nat)
  /-- Wide pointer written by `Cast.unsizeIntoPointer`. -/
  | wide (data vt : LmPtr)
  /-- Thin pointer returned by `Cast.ptrToPtr`. -/
  | thin (data : LmPtr)
  /-- Concrete method and narrowed receiver (`VirtualCalls.resolveVirtual`,
  `VTable.getMethod`). -/
  | method (fnId : Nat) (recv : LmPtr)
  | err (e : LmErr)
  deriving DecidableEq

/-- A question about a vtable table. Trait object types are indices into
`ProtoVTableTable.dynTypes`; concrete types are indices into `tyKeys`. -/
inductive LmQuery : Type where
  /-- `VTable.getPtrVTableTypeRead` with an optional expected trait. -/
  | vtableType (vtPtr : LmPtr) (expected? : Option Nat)
  /-- `VTable.getSizeAndAlignRead` at the expected trait. -/
  | sizeAlign (vtPtr : LmPtr) (expected : Nat)
  /-- `DynamicLayout.sizeAndAlignFromMeta` on a `dyn` place with metadata. -/
  | dynLayout (vtPtr : LmPtr) (expected : Nat)
  /-- `Cast.unsizeIntoPointer` from a pointer to a sized type. -/
  | unsize (tyIdx traitIdx : Nat) (data : LmPtr)
  /-- `Cast.unsizeIntoPointer` from a trait-object pointer (upcast). -/
  | upcast (srcTrait dstTrait : Nat) (data vt : LmPtr)
  /-- `Cast.ptrToPtr` from a wide raw pointer to a thin raw pointer. -/
  | ptrToPtr (data ptrMeta : LmPtr)
  /-- `Cast.ptrToPtr` on an uninitialized immediate. -/
  | ptrToPtrUninit
  /-- `VirtualCalls.resolveVirtual` on a raw trait-object receiver. -/
  | virtualCall (traitIdx slot : Nat) (data vt : LmPtr)
  /-- `VirtualCalls.resolveVirtual` on a `DispatchFromDyn` single-non-1ZST
  wrapper struct `((), *const dyn Trait, ())`. -/
  | virtualCallWrapped (traitIdx slot : Nat) (data vt : LmPtr)
  /-- `VTable.getMethod` on a vtable pointer. -/
  | getMethod (traitIdx slot : Nat) (vt : LmPtr)
  deriving DecidableEq

/-- First occurrences of the strings, in order. -/
def strDedup : List String → List String → List String
  | acc, [] => acc.reverse
  | acc, x :: xs =>
    match strMem x acc with
    | true => strDedup acc xs
    | false => strDedup (x :: acc) xs

/-- Index of the first occurrence of `s` (the length when absent). -/
def strIndex (s : String) : List String → Nat
  | [] => 0
  | x :: xs =>
    match strEq x s with
    | true => 0
    | false => strIndex s xs + 1

/-- Concrete type keys of the table, in order of first appearance. -/
def tyKeys (vt : ProtoVTableTable) : List String :=
  strDedup [] (vt.entries.map (·.concreteTyKey))

/-- Method `DefPath`s of a slot list. -/
def slotMethods : List ProtoVTableSlot → List String
  | [] => []
  | .method p :: rest => p :: slotMethods rest
  | _ :: rest => slotMethods rest

/-- Concrete method `DefPath`s of the table, in order of first appearance. -/
def fnKeys (vt : ProtoVTableTable) : List String :=
  strDedup [] (vt.entries.flatMap (fun e => slotMethods e.slots))

/-- Numeric identity of a concrete type key. -/
def tyIdOf (vt : ProtoVTableTable) (key : String) : Nat := strIndex key (tyKeys vt)

/-- Numeric identity of a concrete method. -/
def fnIdOf (vt : ProtoVTableTable) (defPath : String) : Nat := strIndex defPath (fnKeys vt)

/-- Trait object type with index `i`. -/
def nthPred (vt : ProtoVTableTable) (i : Nat) : Option ProtoTraitPred :=
  match get? vt.dynTypes i with
  | some (_, p) => some p
  | none => none

/-- `Trusted` pointer of a query pointer. -/
def dataWordOf : LmPtr → ProtoDataWord
  | .prov a off => .prov { allocId := a, offsetBytes := off }
  | .int addr => .addr addr

/-- Query pointer of a pointer word `Value`. -/
def lmPtrOfWord : Value → Option LmPtr
  | .ptr p _ => some (.prov p.allocId p.offsetBytes)
  | .scalar sc => some (.int sc.bits)
  | _ => none

/-- Observation of a wide pointer `Value`. -/
def obsOfWide : Value → LmObs
  | .aggregate 0 [d, m] =>
    match lmPtrOfWord d, lmPtrOfWord m with
    | some dp, some mp => .wide dp mp
    | _, _ => .err .other
  | _ => .err .other

/-- Error class of a vtable pointer that does not resolve for `pred`. -/
def classifyVtErr (vt : ProtoVTableTable) (pred : ProtoTraitPred) : LmPtr → LmErr
  | .int _ => .invalidVTablePointer
  | .prov a off =>
    match resolveVTablePtr vt pred { allocId := a, offsetBytes := off } with
    | .invalidTrait => .invalidVTableTrait
    | _ => .invalidVTablePointer

/-- Trait-object pointer `Value` with the given data and metadata words. -/
def widePtrValue (data ptrMeta : LmPtr) : Value :=
  .aggregate 0 [encodeDataWord 8 (dataWordOf data), encodeDataWord 8 (dataWordOf ptrMeta)]

/-- Fat-to-thin pointer cast (`PtrToPtr` to a thin raw pointer): the data word
of a decoded pointer; a value that is not a pointer is UB. -/
def fatToThinProto (ptrBytes : Nat) (v : Value) : ProtoRes Value :=
  match decodeWidePtr? ptrBytes v with
  | some w => .ok (encodeDataWord ptrBytes w.data)
  | none => .ub

/-- Caller body of the one-argument virtual call used to answer queries. -/
def queryCallerBody : CapturedMir :=
  { defPath := "lm::query_caller", phase := .runtimePostCleanup, role := .model, argCount := 0,
    localDecls := [], basicBlocks := [],
    fnAbi :=
      { args := []
        ret :=
          { layout :=
              { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := .memory,
                fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }
            mode := .ignore }
        conv := .rust, canUnwind := false },
    layouts := { pointerBits := 64, isLittleEndian := true, entries := [] }, allocations := [] }

/-- Machine state whose only local holds the receiver `recv`. -/
def queryCallState (recv : Value) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.init recv] }, memory := emptyMemory }

/-- Method resolution of `evalVirtualCallProto` on a raw receiver value `recv`
(direct wide pointer or `DispatchFromDyn` single-non-1ZST wrapper) with no
callee linked: the concrete method and the narrowed receiver. -/
def virtualCallObsVal (vt : ProtoVTableTable) (pred : ProtoTraitPred) (slot : Nat)
    (vtp : LmPtr) (recv : Value) : LmObs :=
  match
    evalVirtualCallProto vt { traitPred := pred, slotIdx := slot, receiverIsRef := false }
      (queryCallState recv) queryCallerBody
      [.copy { local_ := 0, projection := [] }] { local_ := 0, projection := [] } 0 .continue_
  with
  | .externalCall defPath (thin :: _) _ =>
    match lmPtrOfWord thin with
    | some recvPtr => .method (fnIdOf vt defPath) recvPtr
    | none => .err .other
  | .externalCall _ [] _ => .err .other
  | .enter _ _ _ => .err .other
  | .unsupported => .err .unsupported
  | .ub =>
    match vtp with
    | .int _ => .err .invalidVTablePointer
    | .prov a off =>
      match resolveVTablePtr vt pred { allocId := a, offsetBytes := off } with
      | .ok _ => .err .notAMethod
      | .invalidPointer => .err .invalidVTablePointer
      | .invalidTrait => .err .invalidVTableTrait

/-- Method resolution of `evalVirtualCallProto` on a direct raw receiver with
no callee linked. -/
def virtualCallObs (vt : ProtoVTableTable) (pred : ProtoTraitPred) (slot : Nat)
    (data vtp : LmPtr) : LmObs :=
  virtualCallObsVal vt pred slot vtp (widePtrValue data vtp)

/-- **The prototype's answer to a query**, computed with the rules of §3-§5
(`resolveVTablePtr`, `dynLayoutOfValProto`, `unsizeSizedToDyn`,
`unsizeDynToDyn`, `fatToThinProto`, `evalVirtualCallProto`). -/
def protoLmRun (vt : ProtoVTableTable) : LmQuery → LmObs
  | .vtableType vtp expected? =>
    match vtp, expected? with
    | .int _, _ => .err .invalidVTablePointer
    | .prov a off, none =>
      match Nat.beq off 0, lookupVTableByAlloc vt.entries a with
      | true, some e => .tyOk (tyIdOf vt e.concreteTyKey)
      | _, _ => .err .invalidVTablePointer
    | .prov a off, some t =>
      match nthPred vt t with
      | none => .err .other
      | some pred =>
        match resolveVTablePtr vt pred { allocId := a, offsetBytes := off } with
        | .ok e => .tyOk (tyIdOf vt e.concreteTyKey)
        | .invalidPointer => .err .invalidVTablePointer
        | .invalidTrait => .err .invalidVTableTrait
  | .sizeAlign vtp t | .dynLayout vtp t =>
    match nthPred vt t with
    | none => .err .other
    | some pred =>
      match dynLayoutOfValProto vt 8 pred (widePtrValue (.int 0) vtp) with
      | .ok (size, align) => .sizeAlign size align
      | .unsupported => .err .unsupported
      | .ub => .err (classifyVtErr vt pred vtp)
  | .unsize tyIdx traitIdx data =>
    match get? (tyKeys vt) tyIdx, nthPred vt traitIdx with
    | some key, some pred =>
      match pred.failsClosed with
      | true => .err .unsupported
      | false =>
        match
          unsizeSizedToDyn vt 8 .raw false pred key (encodeDataWord 8 (dataWordOf data)) []
            emptyMemory [] emptyLayoutTable
        with
        | .ok v _ _ => obsOfWide v
        | .ub => .err .otherUb
        | .unsupported => .err .unsupported
    | _, _ => .err .other
  | .upcast srcTrait dstTrait data vtp =>
    match nthPred vt srcTrait, nthPred vt dstTrait with
    | some srcPred, some dstPred =>
      match
        unsizeDynToDyn vt 8 .raw false srcPred dstPred (widePtrValue data vtp) [] emptyMemory []
          emptyLayoutTable
      with
      | .ok v _ _ => obsOfWide v
      | .ub => .err (classifyVtErr vt srcPred vtp)
      | .unsupported => .err .unsupported
    | _, _ => .err .other
  | .ptrToPtr data ptrMeta =>
    match fatToThinProto 8 (widePtrValue data ptrMeta) with
    | .ok v =>
      match lmPtrOfWord v with
      | some p => .thin p
      | none => .err .other
    | .ub => .err .otherUb
    | .unsupported => .err .unsupported
  | .ptrToPtrUninit =>
    match fatToThinProto 8 .uninit with
    | .ub => .err .uninitBytes
    | _ => .err .other
  | .virtualCall traitIdx slot data vtp =>
    match nthPred vt traitIdx with
    | none => .err .other
    | some pred => virtualCallObs vt pred slot data vtp
  | .virtualCallWrapped traitIdx slot data vtp =>
    match nthPred vt traitIdx with
    | none => .err .other
    | some pred =>
      virtualCallObsVal vt pred slot vtp (.aggregate 0 [.unit, widePtrValue data vtp, .unit])
  | .getMethod traitIdx slot vtp =>
    match nthPred vt traitIdx with
    | none => .err .other
    | some pred => virtualCallObs vt pred slot (.int 0) vtp

/-- An authority answering queries about a vtable table. The genuine instance
runs vendored `Miri.Interpreter.*`. -/
structure LmDynAuthority : Type where
  run : ProtoVTableTable → LmQuery → LmObs

/-- The prototype as an authority. -/
def protoLmAuthority : LmDynAuthority := ⟨protoLmRun⟩

def predA : ProtoTraitPred := { principalTrait? := some "TraitA" }
def predAlt : ProtoTraitPred := { principalTrait? := some "TraitAlt" }
def predSuper : ProtoTraitPred := { principalTrait? := some "Super" }
def predSub : ProtoTraitPred := { principalTrait? := some "Sub" }
def predSub2 : ProtoTraitPred := { principalTrait? := some "Sub2" }
def predMarker : ProtoTraitPred := { principalTrait? := some "Marker" }
def predIterU32 : ProtoTraitPred :=
  { principalTrait? := some "Iter",
    assocBindings := [⟨"Item", "u32"⟩, ⟨"Err", "u8"⟩] }
def predIterU32PermDupAuto : ProtoTraitPred :=
  { principalTrait? := some "Iter",
    assocBindings := [⟨"Err", "u8"⟩, ⟨"Item", "u32"⟩, ⟨"Item", "u32"⟩],
    autoTraits := ["Send", "Sync"] }
def predIterU64 : ProtoTraitPred :=
  { principalTrait? := some "Iter",
    assocBindings := [⟨"Item", "u64"⟩, ⟨"Err", "u8"⟩] }

/-- Vtable table of the correspondence corpus. Entries `0..2` are the
Campaign #22 shape (two concrete types for `TraitA`, one type for two traits);
entry `4` (`dyn Sub`) reaches entry `3` (`dyn Super`) through a `.traitVPtr`
slot; entry `5` (`dyn Sub2`) declares entry `3` as its `primarySuperVTable?`
(prefix-compatible); entry `6` (`dyn Marker`) is an unrelated 0-method marker
trait; entry `7` (`dyn Iter<Item = u32, Err = u8>`) exercises multi-predicate
associated-type sorting and deduplication. -/
def corpusTable : ProtoVTableTable :=
  { entries :=
      [ { vtableId := 0, vtableAllocId := 40000, concreteTyKey := "Receiver", traitPred := predA,
          sizeBytes := 4, alignBytes := 4,
          slots := [.dropInPlace none, .size, .align, .method "rec::eval", .method "rec::tag"] },
        { vtableId := 1, vtableAllocId := 40001, concreteTyKey := "AltReceiver",
          traitPred := predA, sizeBytes := 8, alignBytes := 4,
          slots :=
            [.dropInPlace none, .size, .align, .method "other::eval", .method "other::tag"] },
        { vtableId := 2, vtableAllocId := 40002, concreteTyKey := "Receiver",
          traitPred := predAlt, sizeBytes := 4, alignBytes := 4,
          slots := [.dropInPlace none, .size, .align, .method "rec::alt"] },
        { vtableId := 3, vtableAllocId := 40003, concreteTyKey := "Receiver",
          traitPred := predSuper, sizeBytes := 4, alignBytes := 4,
          slots := [.dropInPlace none, .size, .align, .method "rec::sup"] },
        { vtableId := 4, vtableAllocId := 40004, concreteTyKey := "Receiver",
          traitPred := predSub, sizeBytes := 4, alignBytes := 4,
          slots :=
            [.dropInPlace none, .size, .align, .method "rec::sup", .traitVPtr 3,
             .method "rec::sub", .vacant] },
        { vtableId := 5, vtableAllocId := 40005, concreteTyKey := "Receiver",
          traitPred := predSub2, sizeBytes := 4, alignBytes := 4,
          slots := [.dropInPlace none, .size, .align, .method "rec::sup", .method "rec::sub2"],
          primarySuperVTable? := some 3 },
        { vtableId := 6, vtableAllocId := 40006, concreteTyKey := "Receiver",
          traitPred := predMarker, sizeBytes := 4, alignBytes := 4,
          slots := [.dropInPlace none, .size, .align] },
        { vtableId := 7, vtableAllocId := 40007, concreteTyKey := "Receiver",
          traitPred := predIterU32, sizeBytes := 4, alignBytes := 4,
          slots := [.dropInPlace none, .size, .align, .method "rec::iter_next"] } ],
    dynTypes :=
      [ ("TraitA", predA), ("TraitAlt", predAlt), ("Super", predSuper), ("Sub", predSub),
        ("Sub2", predSub2),
        ("TraitA+Send", { predA with autoTraits := ["Send"] }),
        ("Unresolved", { predA with hasUnresolvedExistentialBinder := true }),
        ("Marker", predMarker),
        ("IterU32", predIterU32),
        ("IterU32PermDupAuto", predIterU32PermDupAuto),
        ("IterU64Mismatch", predIterU64) ] }

/-- Test vectors of the correspondence: every query kind, with valid and
invalid inputs (including multi-predicate associated-type sorting/deduplication
and `DispatchFromDyn` single-non-1ZST wrapper receivers). -/
def lmCorpus : List LmQuery :=
  [ -- vtable type and trait validation (including assoc-type sorting & dedup)
    .vtableType (.prov 40000 0) none,
    .vtableType (.prov 40000 0) (some 0),
    .vtableType (.prov 40001 0) (some 0),
    .vtableType (.prov 40000 0) (some 5),          -- auto traits are ignored
    .vtableType (.prov 40007 0) (some 8),          -- multi-predicate exact match
    .vtableType (.prov 40007 0) (some 9),          -- permuted + duplicated + auto traits
    .vtableType (.prov 40007 0) (some 10),         -- mismatched associated type (`u64` vs `u32`)
    .vtableType (.prov 40002 0) (some 0),          -- `TraitAlt` vtable used as `dyn TraitA`
    .vtableType (.prov 40000 8) (some 0),          -- non-zero offset
    .vtableType (.prov 7 0) (some 0),              -- non-vtable allocation
    .vtableType (.int 4096) (some 0),              -- dangling integer
    .vtableType (.int 0) none,                     -- null
    -- dynamic layout
    .sizeAlign (.prov 40000 0) 0,
    .sizeAlign (.prov 40001 0) 0,
    .sizeAlign (.prov 40002 0) 0,
    .sizeAlign (.prov 40007 0) 9,                  -- permuted/deduped assoc bindings layout
    .sizeAlign (.prov 40007 0) 10,                 -- mismatched assoc binding -> InvalidVTableTrait
    .sizeAlign (.prov 40001 4) 0,
    .sizeAlign (.int 64) 0,
    .dynLayout (.prov 40000 0) 0,
    .dynLayout (.prov 40001 0) 5,
    .dynLayout (.prov 40002 0) 1,
    .dynLayout (.prov 40002 0) 0,
    .dynLayout (.prov 9 0) 0,
    .dynLayout (.int 0) 0,
    -- unsizing from a sized type
    .unsize 0 0 (.prov 3 0),
    .unsize 1 0 (.prov 5 4),
    .unsize 0 1 (.prov 3 0),
    .unsize 0 0 (.int 0),                          -- null raw pointer
    .unsize 0 0 (.int 4097),                       -- misaligned dangling raw pointer
    .unsize 1 1 (.prov 5 0),                       -- no vtable captured
    -- upcasts
    .upcast 3 2 (.prov 3 0) (.prov 40004 0),       -- through `.traitVPtr`
    .upcast 4 2 (.prov 3 0) (.prov 40005 0),       -- primary-supertrait prefix-compatible
    .upcast 3 3 (.prov 3 0) (.prov 40004 0),       -- identity
    .upcast 5 0 (.prov 3 0) (.prov 40000 0),       -- drop auto trait (`TraitA+Send -> TraitA`)
    .upcast 3 2 (.prov 3 0) (.prov 40000 0),       -- wrong-trait vtable
    .upcast 3 2 (.prov 3 0) (.prov 40004 8),       -- offset vtable pointer
    .upcast 3 2 (.prov 3 0) (.int 0),              -- null vtable pointer
    -- fat-to-thin
    .ptrToPtr (.prov 3 0) (.prov 40000 0),
    .ptrToPtr (.prov 5 4) (.prov 40001 0),
    .ptrToPtr (.int 4096) (.prov 40002 0),
    .ptrToPtr (.prov 3 0) (.int 2),
    .ptrToPtrUninit,
    -- virtual calls (direct and `DispatchFromDyn` single-non-1ZST wrapper)
    .virtualCall 0 3 (.prov 3 0) (.prov 40000 0),
    .virtualCall 0 4 (.prov 3 0) (.prov 40000 0),
    .virtualCall 0 3 (.prov 5 4) (.prov 40001 0),  -- receiver with a field offset
    .virtualCall 1 3 (.prov 3 0) (.prov 40002 0),
    .virtualCall 9 3 (.prov 3 0) (.prov 40007 0),  -- call via permuted/deduped assoc pred
    .virtualCallWrapped 0 3 (.prov 5 4) (.prov 40001 0), -- `DispatchFromDyn` wrapper `((), ptr, ())`
    .virtualCallWrapped 0 1 (.prov 3 0) (.prov 40000 0), -- wrapper on header slot -> notAMethod
    .virtualCall 0 0 (.prov 3 0) (.prov 40000 0),  -- `drop_in_place` slot
    .virtualCall 0 1 (.prov 3 0) (.prov 40000 0),  -- `size` slot
    .virtualCall 0 2 (.prov 3 0) (.prov 40000 0),  -- `align` slot
    .virtualCall 3 4 (.prov 3 0) (.prov 40004 0),  -- `.traitVPtr` slot
    .virtualCall 3 6 (.prov 3 0) (.prov 40004 0),  -- vacant slot
    .virtualCall 0 9 (.prov 3 0) (.prov 40000 0),  -- out of range
    .virtualCall 0 3 (.prov 3 0) (.prov 40002 0),  -- wrong trait
    .virtualCall 0 3 (.prov 3 0) (.prov 40000 4),  -- offset vtable pointer
    .virtualCall 0 3 (.prov 3 0) (.int 8),         -- dangling integer vtable pointer
    .getMethod 0 3 (.prov 40001 0),
    .getMethod 0 2 (.prov 40001 0),
    .getMethod 0 3 (.prov 6 0) ]

/-- The authority agrees with the prototype on every test vector. -/
def lmAuthorityCheck (auth : LmDynAuthority) : Bool :=
  lmCorpus.all (fun q => decide (auth.run corpusTable q = protoLmRun corpusTable q))

/-- `Cast.unsizeIntoPointer` pairs the data pointer, unchanged, with the base
pointer of the captured vtable; a null or dangling raw data pointer is paired
the same way, and an uncaptured vtable is unsupported. -/
def unsizeLaw : List (LmQuery × LmObs) :=
  [ (.unsize 0 0 (.prov 3 0), .wide (.prov 3 0) (.prov 40000 0)),
    (.unsize 1 0 (.prov 5 4), .wide (.prov 5 4) (.prov 40001 0)),
    (.unsize 0 1 (.prov 3 0), .wide (.prov 3 0) (.prov 40002 0)),
    (.unsize 0 0 (.int 0), .wide (.int 0) (.prov 40000 0)),
    (.unsize 0 0 (.int 4097), .wide (.int 4097) (.prov 40000 0)),
    (.unsize 1 1 (.prov 5 0), .err .unsupported) ]

/-- A `dyn Sub -> dyn Super` upcast selects the supertrait vtable through the
`.traitVPtr` slot or the primary-supertrait prefix, dropping auto traits and
identity coercions keep the vtable; an invalid incoming vtable pointer is UB. -/
def upcastLaw : List (LmQuery × LmObs) :=
  [ (.upcast 3 2 (.prov 3 0) (.prov 40004 0), .wide (.prov 3 0) (.prov 40003 0)),
    (.upcast 4 2 (.prov 3 0) (.prov 40005 0), .wide (.prov 3 0) (.prov 40003 0)),
    (.upcast 3 3 (.prov 3 0) (.prov 40004 0), .wide (.prov 3 0) (.prov 40004 0)),
    (.upcast 5 0 (.prov 3 0) (.prov 40000 0), .wide (.prov 3 0) (.prov 40000 0)),
    (.upcast 3 2 (.prov 3 0) (.prov 40000 0), .err .invalidVTableTrait),
    (.upcast 3 2 (.prov 3 0) (.prov 40004 8), .err .invalidVTablePointer),
    (.upcast 3 2 (.prov 3 0) (.int 0), .err .invalidVTablePointer) ]

/-- Dynamic size and alignment come from the vtable, through both
`VTable.getSizeAndAlignRead` and `DynamicLayout.sizeAndAlignFromMeta`. -/
def layoutLaw : List (LmQuery × LmObs) :=
  [ (.sizeAlign (.prov 40000 0) 0, .sizeAlign 4 4),
    (.sizeAlign (.prov 40001 0) 0, .sizeAlign 8 4),
    (.sizeAlign (.prov 40007 0) 9, .sizeAlign 4 4),
    (.dynLayout (.prov 40000 0) 0, .sizeAlign 4 4),
    (.dynLayout (.prov 40002 0) 1, .sizeAlign 4 4) ]

/-- The vtable trait check ignores auto traits and sorts/deduplicates
non-auto projection predicates (`VTable.sortedPredicates`):
`dyn TraitA + Send` accepts `dyn TraitA`, and permuted/duplicated associated-type
bindings with auto traits accept `dyn Iter<Item = u32, Err = u8>`. -/
def autoTraitLaw : List (LmQuery × LmObs) :=
  [ (.vtableType (.prov 40000 0) (some 0), .tyOk 0),
    (.vtableType (.prov 40000 0) (some 5), .tyOk 0),
    (.vtableType (.prov 40001 0) (some 0), .tyOk 1),
    (.vtableType (.prov 40007 0) (some 8), .tyOk 0),
    (.vtableType (.prov 40007 0) (some 9), .tyOk 0),
    (.dynLayout (.prov 40001 0) 5, .sizeAlign 8 4) ]

/-- `InvalidVTablePointer`: a dangling integer, null, a non-zero offset, and a
non-vtable allocation. -/
def invalidPointerLaw : List (LmQuery × LmObs) :=
  [ (.vtableType (.int 4096) (some 0), .err .invalidVTablePointer),
    (.vtableType (.int 0) none, .err .invalidVTablePointer),
    (.vtableType (.prov 40000 8) (some 0), .err .invalidVTablePointer),
    (.vtableType (.prov 7 0) (some 0), .err .invalidVTablePointer),
    (.sizeAlign (.int 64) 0, .err .invalidVTablePointer),
    (.sizeAlign (.prov 40001 4) 0, .err .invalidVTablePointer),
    (.dynLayout (.prov 9 0) 0, .err .invalidVTablePointer),
    (.dynLayout (.int 0) 0, .err .invalidVTablePointer),
    (.virtualCall 0 3 (.prov 3 0) (.int 8), .err .invalidVTablePointer),
    (.virtualCall 0 3 (.prov 3 0) (.prov 40000 4), .err .invalidVTablePointer),
    (.getMethod 0 3 (.prov 6 0), .err .invalidVTablePointer) ]

/-- `InvalidVTableTrait`: a vtable of another trait object type or mismatched
associated-type binding. -/
def invalidTraitLaw : List (LmQuery × LmObs) :=
  [ (.vtableType (.prov 40002 0) (some 0), .err .invalidVTableTrait),
    (.vtableType (.prov 40007 0) (some 10), .err .invalidVTableTrait),
    (.sizeAlign (.prov 40002 0) 0, .err .invalidVTableTrait),
    (.sizeAlign (.prov 40007 0) 10, .err .invalidVTableTrait),
    (.dynLayout (.prov 40002 0) 0, .err .invalidVTableTrait),
    (.virtualCall 0 3 (.prov 3 0) (.prov 40002 0), .err .invalidVTableTrait) ]

/-- A virtual call resolves the method slot and narrows the receiver (direct or
inside a `DispatchFromDyn` single-non-1ZST wrapper) to the thin data pointer,
keeping its allocation and offset. -/
def virtualCallLaw : List (LmQuery × LmObs) :=
  [ (.virtualCall 0 3 (.prov 3 0) (.prov 40000 0), .method 0 (.prov 3 0)),
    (.virtualCall 0 4 (.prov 3 0) (.prov 40000 0), .method 1 (.prov 3 0)),
    (.virtualCall 0 3 (.prov 5 4) (.prov 40001 0), .method 2 (.prov 5 4)),
    (.virtualCall 1 3 (.prov 3 0) (.prov 40002 0), .method 4 (.prov 3 0)),
    (.virtualCall 9 3 (.prov 3 0) (.prov 40007 0), .method 8 (.prov 3 0)),
    (.virtualCallWrapped 0 3 (.prov 5 4) (.prov 40001 0), .method 2 (.prov 5 4)),
    (.getMethod 0 3 (.prov 40001 0), .method 2 (.int 0)) ]

/-- A header, supertrait, vacant, or out-of-range slot is UB ("dyn call trying
to call something that is not a method"). -/
def nonMethodSlotLaw : List (LmQuery × LmObs) :=
  [ (.virtualCall 0 0 (.prov 3 0) (.prov 40000 0), .err .notAMethod),
    (.virtualCall 0 1 (.prov 3 0) (.prov 40000 0), .err .notAMethod),
    (.virtualCall 0 2 (.prov 3 0) (.prov 40000 0), .err .notAMethod),
    (.virtualCallWrapped 0 1 (.prov 3 0) (.prov 40000 0), .err .notAMethod),
    (.virtualCall 3 4 (.prov 3 0) (.prov 40004 0), .err .notAMethod),
    (.virtualCall 3 6 (.prov 3 0) (.prov 40004 0), .err .notAMethod),
    (.virtualCall 0 9 (.prov 3 0) (.prov 40000 0), .err .notAMethod),
    (.getMethod 0 2 (.prov 40001 0), .err .notAMethod) ]

/-- The fat-to-thin `PtrToPtr` cast erases the metadata word (a vtable pointer
or a slice length) and keeps the data pointer; an uninitialized immediate is
UB. -/
def ptrToPtrLaw : List (LmQuery × LmObs) :=
  [ (.ptrToPtr (.prov 3 0) (.prov 40000 0), .thin (.prov 3 0)),
    (.ptrToPtr (.prov 5 4) (.prov 40001 0), .thin (.prov 5 4)),
    (.ptrToPtr (.int 4096) (.prov 40002 0), .thin (.int 4096)),
    (.ptrToPtr (.prov 3 0) (.int 2), .thin (.prov 3 0)),
    (.ptrToPtrUninit, .err .uninitBytes) ]

/-- Every vector of a law is a corpus query whose prototype answer is the
stated observation. -/
def lawOk (law : List (LmQuery × LmObs)) : Bool :=
  law.all (fun p => decide (p.1 ∈ lmCorpus) && decide (protoLmRun corpusTable p.1 = p.2))

/-- The authority returns the stated observation on every vector of the law. -/
def LawHolds (auth : LmDynAuthority) (law : List (LmQuery × LmObs)) : Prop :=
  ∀ p, p ∈ law → auth.run corpusTable p.1 = p.2

/-- **`lean-miri` correspondence contract.** Each field is one operational law
of the vendored interpreter, stated on explicit test vectors. -/
structure LmDynContract (auth : LmDynAuthority) : Prop where
  /-- Agreement with the prototype on every test vector. -/
  agreement : ∀ q, q ∈ lmCorpus → auth.run corpusTable q = protoLmRun corpusTable q
  unsize_pairs_data_with_vtable : LawHolds auth unsizeLaw
  upcast_selects_super_vtable : LawHolds auth upcastLaw
  layout_from_vtable : LawHolds auth layoutLaw
  trait_check_ignores_auto_traits : LawHolds auth autoTraitLaw
  invalid_vtable_pointer_ub : LawHolds auth invalidPointerLaw
  invalid_vtable_trait_ub : LawHolds auth invalidTraitLaw
  virtual_call_resolves_and_narrows : LawHolds auth virtualCallLaw
  non_method_slot_ub : LawHolds auth nonMethodSlotLaw
  ptr_to_ptr_erases_metadata : LawHolds auth ptrToPtrLaw

theorem lmAuthorityCheck_agreement {auth : LmDynAuthority} (h : lmAuthorityCheck auth = true) :
    ∀ q, q ∈ lmCorpus → auth.run corpusTable q = protoLmRun corpusTable q := by
  intro q hq
  exact of_decide_eq_true (List.all_eq_true.mp h q hq)

theorem lawHolds_of_agreement {auth : LmDynAuthority}
    (hA : ∀ q, q ∈ lmCorpus → auth.run corpusTable q = protoLmRun corpusTable q)
    (law : List (LmQuery × LmObs)) (hLaw : lawOk law = true) : LawHolds auth law := by
  intro p hp
  have h := List.all_eq_true.mp hLaw p hp
  rw [Bool.and_eq_true] at h
  exact (hA p.1 (of_decide_eq_true h.1)).trans (of_decide_eq_true h.2)

/-- The law vectors are corpus queries with the stated prototype answers
(kernel-evaluated): the laws are not vacuous. -/
theorem lmLaws_ok :
    lawOk unsizeLaw = true ∧ lawOk upcastLaw = true ∧ lawOk layoutLaw = true ∧
    lawOk autoTraitLaw = true ∧ lawOk invalidPointerLaw = true ∧
    lawOk invalidTraitLaw = true ∧ lawOk virtualCallLaw = true ∧
    lawOk nonMethodSlotLaw = true ∧ lawOk ptrToPtrLaw = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **Contract from the kernel-checked certificate.** An authority that passes
`lmAuthorityCheck` satisfies every law of `LmDynContract`. -/
theorem lmDynContractOfCheck (auth : LmDynAuthority) (h : lmAuthorityCheck auth = true) :
    LmDynContract auth :=
  have hA := lmAuthorityCheck_agreement h
  { agreement := hA
    unsize_pairs_data_with_vtable := lawHolds_of_agreement hA _ lmLaws_ok.1
    upcast_selects_super_vtable := lawHolds_of_agreement hA _ lmLaws_ok.2.1
    layout_from_vtable := lawHolds_of_agreement hA _ lmLaws_ok.2.2.1
    trait_check_ignores_auto_traits := lawHolds_of_agreement hA _ lmLaws_ok.2.2.2.1
    invalid_vtable_pointer_ub := lawHolds_of_agreement hA _ lmLaws_ok.2.2.2.2.1
    invalid_vtable_trait_ub := lawHolds_of_agreement hA _ lmLaws_ok.2.2.2.2.2.1
    virtual_call_resolves_and_narrows := lawHolds_of_agreement hA _ lmLaws_ok.2.2.2.2.2.2.1
    non_method_slot_ub := lawHolds_of_agreement hA _ lmLaws_ok.2.2.2.2.2.2.2.1
    ptr_to_ptr_erases_metadata := lawHolds_of_agreement hA _ lmLaws_ok.2.2.2.2.2.2.2.2 }

/-- The prototype passes its own check (the corpus is consistent). -/
theorem protoLmAuthority_check : lmAuthorityCheck protoLmAuthority = true := by
  decide +kernel

/-- **The check is not vacuous.** Authorities that answer every query with one
fixed observation, that drop the vtable trait check, or that return the wide
pointer from the fat-to-thin cast fail it. -/
theorem lmAuthorityCheck_rejects_forgeries :
    lmAuthorityCheck ⟨fun _ _ => .err .unsupported⟩ = false ∧
    lmAuthorityCheck ⟨fun _ _ => .err .invalidVTablePointer⟩ = false ∧
    lmAuthorityCheck
      ⟨fun vt q =>
        match q with
        | .vtableType vtp (some _) => protoLmRun vt (.vtableType vtp none)
        | q => protoLmRun vt q⟩ = false ∧
    lmAuthorityCheck
      ⟨fun vt q =>
        match q with
        | .ptrToPtr data ptrMeta => .wide data ptrMeta
        | q => protoLmRun vt q⟩ = false ∧
    lmAuthorityCheck
      ⟨fun vt q =>
        match q with
        | .virtualCall t slot data vtp => protoLmRun vt (.virtualCall t (slot + 1) data vtp)
        | q => protoLmRun vt q⟩ = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The corpus table is well formed at 8-byte pointers. -/
theorem corpusTable_wf : wfProtoVTableTable 8 corpusTable = true := by decide +kernel

/-! ### Closed MiniRust instance on the correspondence corpus -/

/-- MiniRust trait numbering of the corpus: the index in `dynTypes`. -/
def corpusTraitOf (p : ProtoTraitPred) : Nat :=
  let rec go : List (String × ProtoTraitPred) → Nat
    | [] => 0
    | (_, q) :: rest =>
      match traitPredEq q p with
      | true => 0
      | false => go rest + 1
  go corpusTable.dynTypes

open MiniRustSpec MiniRustSpec.Interp in
/-- **MiniRust side of the corpus, closed.** For every base `Mach` and `MachTB`
and every data word: on the corpus table's `AltReceiver` vtable (`dyn TraitA`,
allocation `40001`), MiniRust `vtable_from_ptr`, `compute_size`, and
`compute_align` (`Mach` monomorphic and `MachTB` polymorphic) return the
translated vtable, `8`, and `4`, and `dynSizeOfValProto` /
`dynAlignOfValProto` return `8` and `4`; `vtable_from_ptr` of a non-zero
offset into that vtable is `ub "invalid pointer for vtable lookup"`. -/
theorem corpus_minirust_instance (m : Mach) (mTB : MachTB) (d : ProtoDataWord) :
    let e : ProtoVTableEntry :=
      { vtableId := 1, vtableAllocId := 40001, concreteTyKey := "AltReceiver",
        traitPred := predA, sizeBytes := 8, alignBytes := 4,
        slots :=
          [.dropInPlace none, .size, .align, .method "other::eval", .method "other::tag"] }
    let L := MR.bmLayout corpusTraitOf (fnIdOf corpusTable)
    let LT := MR.tbLayout corpusTraitOf (fnIdOf corpusTable)
    ((vtableFromPtr (MR.installVTables L corpusTable m) (MR.vtPtr L e) =
        .ok (MR.vtableOf L e) ∧
      computeSize (MR.installVTables L corpusTable m) (.TraitObject ⟨⟨0⟩⟩)
        (some (.VTablePointer (MR.vtPtr L e))) = .ok ⟨8⟩ ∧
      computeAlign (MR.installVTables L corpusTable m) (.TraitObject ⟨⟨0⟩⟩)
        (some (.VTablePointer (MR.vtPtr L e))) = .ok ⟨4⟩) ∧
    (vtableFromPtrM (MR.installVTables LT corpusTable mTB) (MR.vtPtr LT e) =
        .ok (MR.vtableOf LT e) ∧
      computeSizeM (MR.installVTables LT corpusTable mTB) (.TraitObject ⟨⟨0⟩⟩)
        (some (.VTablePointer (MR.vtPtr LT e))) = .ok ⟨8⟩ ∧
      computeAlignM (MR.installVTables LT corpusTable mTB) (.TraitObject ⟨⟨0⟩⟩)
        (some (.VTablePointer (MR.vtPtr LT e))) = .ok ⟨4⟩) ∧
    dynSizeOfValProto corpusTable 8 e.traitPred (mkDynPtr 8 d e) = .ok 8 ∧
    dynAlignOfValProto corpusTable 8 e.traitPred (mkDynPtr 8 d e) = .ok 4) ∧
    vtableFromPtr (MR.installVTables L corpusTable m) (MR.ptrAt L 40001 8) =
      ub "invalid pointer for vtable lookup" := by
  intro e L LT
  refine ⟨MR.mach_and_machTB_vtable_correspondence corpusTraitOf (fnIdOf corpusTable)
    corpusTable 8 e d ⟨⟨0⟩⟩ m mTB corpusTable_wf rfl rfl, ?_⟩
  exact MR.mach_install_ub L corpusTable m _
    (fun x _ => MR.vtPtr_ne_ptrAt_offset L (MR.bmLayout_provOf_inj _ _) x 40001 8 (by decide))

end Lm

/-! ## §10. Prototype capstone -/

/-- **Prototype capstone.** The four laws the TCB patch must preserve:
slice targets are `evalUnsizeCoercion` itself; a fail-closed target predicate
is `.unsupported`; `addr_eq` ignores all metadata; and an uninitialized
virtual-call argument is UB before dispatch. -/
theorem dyn_trait_proto_capstone :
    (∀ (vt : ProtoVTableTable) (locals : List LocalSlot) (op : Operand) (m : Mutability)
        (elem : RigidTy) (idx : LayoutIdx) (mem : Memory) (decls : List LocalDecl)
        (layouts : LayoutTable),
      evalUnsizeCoercionProto vt locals op ⟨.ref m (.slice elem), idx⟩ mem decls layouts =
        evalUnsizeCoercion locals op ⟨.ref m (.slice elem), idx⟩ mem decls layouts) ∧
    (∀ (vt : ProtoVTableTable) (k : ProtoPtrKind) (mt : Bool) (key : String)
        (locals : List LocalSlot) (op : Operand) (mem : Memory) (decls : List LocalDecl)
        (layouts : LayoutTable) (pred : ProtoTraitPred),
      lookupDynPred vt.dynTypes key = some pred → pred.failsClosed = true →
      evalUnsizeDynProto vt k mt key locals op mem decls layouts = .unsupported) ∧
    (∀ (d₁ d₂ : ProtoDataWord) (m₁ m₂ m₁' m₂' : ProtoWidePtrMeta) (locals : List LocalSlot)
        (mem : Memory) (decls : List LocalDecl) (layouts : LayoutTable),
      evalWideAddrEqProto (encodeWidePtr (layoutPointerBytes layouts) ⟨d₁, m₁⟩)
          (encodeWidePtr (layoutPointerBytes layouts) ⟨d₂, m₂⟩) locals mem decls layouts =
        evalWideAddrEqProto (encodeWidePtr (layoutPointerBytes layouts) ⟨d₁, m₁'⟩)
          (encodeWidePtr (layoutPointerBytes layouts) ⟨d₂, m₂'⟩) locals mem decls layouts) ∧
    (∀ (vt : ProtoVTableTable) (site : ProtoVirtualCallSite) (s : MachineState)
        (body : CapturedMir) (argOps : List Operand) (dst : Place) (tgt : BasicBlockIdx)
        (uw : UnwindAction) (vals : List Value) (locals' : List LocalSlot),
      evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals body.layouts
          s.memory.callerLocals (callStack := s.memory.callStack) = .ok vals locals' →
      valueListContainsUninit vals = true →
      evalVirtualCallProto vt site s body argOps dst tgt uw = .ub) :=
  ⟨fun vt locals op m elem idx mem decls layouts =>
      (evalUnsizeCoercionProto_slice_conservative vt locals op m elem idx mem decls layouts).1,
   fun vt k mt key locals op mem decls layouts pred h1 h2 =>
      evalUnsizeDynProto_failsClosed vt k mt key locals op mem decls layouts pred h1 h2,
   evalWideAddrEqProto_metadata_invariant,
   fun vt site s body argOps dst tgt uw vals locals' h1 h2 =>
      evalVirtualCallProto_uninit_arg_ub vt site s body argOps dst tgt uw vals locals' h1 h2⟩

end Anneal.Prototypes.DynTraitUnsizeProto
