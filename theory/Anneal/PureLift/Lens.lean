-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.Nat.Basic

namespace Anneal.PureLift

/-!
# Bidirectional Lenses, Sub-Place Paths, and Value Algebra

Foundational definitions for the `PureLift` functional transformation. Inspired
by prior art in Aeneas (Ho and Protzenko, ICFP 2022), `PureLift` lifts
imperative programs with borrows, nested projections, and structured or
block-based control flow into pure functional computations.

This module defines:
- `EvalOutcome` and `HoldsFnSpec`: total evaluation outcomes where `.fail` maps
  to `False`, preventing vacuous truth on ill-formed borrow plans.
- `Lens` and `LawfulLens`: partial bidirectional lenses with identity and
  composition laws.
- `ValAlgebra`: the language-agnostic value interface supporting aggregate
  field projection, reference-handle encoding, boolean extraction, and
  conditional symbolic value merging.
-/

abbrev LocalId := Nat
abbrev LoanId := Nat
abbrev RegionGroupId := Nat
abbrev BlockId := Nat
abbrev FieldIdx := Nat
abbrev SubPath := List FieldIdx

/-- Fixed-depth call-by-name combinators (`fix4`, `fix8`, `fix16`).
Unlike `Nat.recCompiled` (`Nat.brecOn`) or `List.foldr` (`List.brecOn`), which
reduce the recursion spine in head position before inspecting the target value,
`fix8 step base x` places `step` directly in head position (`step (...) x`).
Consequently, base cases (`.unborrowed`, `.direct`, `.act`, `0`) discard the
recursive continuation `ih` in $O(1)$ `whnf` steps without emitting
compiler-only `_unsafe_rec` declarations. -/
def fix2 {α : Type} (step : α → α) (base : α) : α :=
  step (step base)

def fix4 {α : Type} (step : α → α) (base : α) : α :=
  fix2 step (fix2 step base)

def fix8 {α : Type} (step : α → α) (base : α) : α :=
  fix4 step (fix4 step base)

def fix16 {α : Type} (step : α → α) (base : α) : α :=
  fix8 step (fix8 step base)

/-- Total structural recursion on `Nat` indices via `@Nat.recCompiled`, avoiding
bounded fuel truncation at indices above eight while emitting zero
compiler-only `_unsafe_rec` declarations. -/
def natFold {α : Type} (zero : α) (succ : Nat → α → α) (n : Nat) : α :=
  @Nat.recCompiled (fun _ => α) zero succ n

/-- Total structural recursion on `List` spines via `List.foldr`, passing the
actual remaining list tail to `cons` and avoiding bounded fuel truncation on
lists longer than eight elements while emitting zero compiler-only
`_unsafe_rec` declarations. -/
def listFold {α β : Type} (nil : β) (cons : α → List α → β → β)
    (xs : List α) : β :=
  match
    xs.foldr
      (fun x (acc : List α × β) =>
        match acc with
        | (tail, ih) => (x :: tail, cons x tail ih))
      ([], nil)
  with
  | (_, res) => res

/-- Total evaluation outcome for `PureLift` plan execution.

Any borrow violation, aliasing conflict, unended loan at function return,
out-of-order region group termination, uninitialized spatial cell upon
reabsorption, or insufficient loop fuel evaluates to `.fail`. -/
inductive EvalOutcome (α : Type) where
  | ok (val : α)
  | fail

/-- Specification lifting predicate over `EvalOutcome`.

Mapping `.fail` to `False` guarantees that a proved specification always
witnesses successful evaluation without borrow or safety faults. -/
def HoldsFnSpec {α : Type} (out : EvalOutcome α) (post : α → Prop) : Prop :=
  match out with
  | .ok res => post res
  | .fail => False

theorem holdsFnSpec_not_fail {α : Type} (post : α → Prop) :
    ¬ HoldsFnSpec (.fail : EvalOutcome α) post :=
  fun h => h

/-- Pure functional output of a lifted function: pairs the direct return value
`ret` with the updated final values `mutFinals` of all external mutable-borrow
input parameters in declaration order. -/
structure FuncOut (Val : Type) where
  ret : Val
  mutFinals : List Val

/-- Partial bidirectional lens between an aggregate state `S` and a focused
view `A`. -/
structure Lens (S A : Type) where
  get : S → Option A
  put : S → A → Option S

/-- Well-behavedness laws (`get_put`, `put_get`, `put_put`) for a partial
bidirectional lens. -/
structure LawfulLens (S A : Type) (l : Lens S A) : Prop where
  get_put : ∀ s a, l.get s = some a → l.put s a = some s
  put_get : ∀ s a s', l.put s a = some s' → l.get s' = some a
  put_put : ∀ s a1 a2 s1, l.put s a1 = some s1 → l.put s1 a2 = l.put s a2

/-- Identity lens on `S`. -/
def Lens.id (S : Type) : Lens S S where
  get s := some s
  put _ a := some a

/-- Sequential composition of partial lenses `l1 : Lens S A` and
`l2 : Lens A B`. -/
def Lens.comp {S A B : Type} (l1 : Lens S A) (l2 : Lens A B) : Lens S B where
  get s :=
    match l1.get s with
    | some a => l2.get a
    | none => none
  put s b :=
    match l1.get s with
    | some a =>
      match l2.put a b with
      | some a' => l1.put s a'
      | none => none
    | none => none

theorem Lens.id_lawful (S : Type) : LawfulLens S S (Lens.id S) where
  get_put := by
    intro s a h
    injection h with hEq
    subst hEq
    rfl
  put_get := by
    intro s a s' h
    injection h with hEq
    subst hEq
    rfl
  put_put := by
    intro s a1 a2 s1 h
    injection h with hEq
    subst hEq
    rfl

theorem Lens.comp_lawful {S A B : Type} (l1 : Lens S A) (l2 : Lens A B)
    (h1 : LawfulLens S A l1) (h2 : LawfulLens A B l2) :
    LawfulLens S B (Lens.comp l1 l2) where
  get_put := by
    intro s b hGet
    dsimp [Lens.comp] at hGet
    dsimp [Lens.comp]
    revert hGet
    cases hG1 : l1.get s with
    | none =>
      intro hFalse
      nomatch hFalse
    | some a =>
      dsimp
      intro hG2
      rw [h2.get_put a b hG2]
      dsimp
      exact h1.get_put s a hG1
  put_get := by
    intro s b s' hPut
    dsimp [Lens.comp] at hPut
    dsimp [Lens.comp]
    revert hPut
    cases hG1 : l1.get s with
    | none =>
      intro hFalse
      nomatch hFalse
    | some a =>
      dsimp
      cases hP2 : l2.put a b with
      | none =>
        intro hFalse
        nomatch hFalse
      | some a' =>
        dsimp
        intro hP1
        rw [h1.put_get s a' s' hP1]
        dsimp
        exact h2.put_get a b a' hP2
  put_put := by
    intro s b1 b2 s1 hPut1
    dsimp [Lens.comp] at hPut1
    dsimp [Lens.comp]
    revert hPut1
    cases hG1 : l1.get s with
    | none =>
      intro hFalse
      nomatch hFalse
    | some a =>
      dsimp
      cases hP2 : l2.put a b1 with
      | none =>
        intro hFalse
        nomatch hFalse
      | some a1 =>
        dsimp
        intro hP1
        rw [h1.put_get s a1 s1 hP1]
        dsimp
        rw [h2.put_put a b1 b2 a1 hP2]
        cases l2.put a b2 with
        | none => rfl
        | some a2 =>
          dsimp
          exact h1.put_put s a1 a2 s1 hP1

/-- Language-agnostic value algebra equipping a carrier type `Val` with:
- `defaultVal`: default value for unallocated local slots,
- `asBool`: concrete boolean extraction for branch and loop conditions,
- `zipVal`, `projectBranchVal`, and the three branch-projection laws
  (`projectBranchVal_concrete`, `projectBranchVal_zip_true`,
  `projectBranchVal_zip_false`): symbolic conditional merge at diamond
  control-flow joins and lawful branch-specific value projection,
- `getField`, `setField`, and the three bidirectional field-lens laws
  (`getField_setField`, `setField_getField`, `setField_setField`): aggregate
  child projection and update by index,
- `encodeRef`, `encodeSharedRef`, `decodeRef`, and `remapRefInVal`: first-order
  borrow handle representation and recursive loan-ID renaming inside values,
- `sizeBound`: an upper bound on both the aggregate nesting depth of a value
  and the field count of every aggregate inside it. Branch joins use it as a
  traversal budget when merging aggregates field by field, so no fixed depth or
  width cutoff applies. An underestimate is still sound: the join then falls
  back to `zipVal` for the remaining subvalue. -/
structure ValAlgebra (Val : Type) where
  defaultVal : Val
  asBool : Val → Option Bool
  zipVal : Val → Val → Val → Val
  projectBranchVal : Val → Bool → Val → Val := fun _ _ v => v
  projectBranchVal_concrete :
    ∀ (cond : Val) (b branch : Bool) (v : Val),
      asBool cond = some b → projectBranchVal cond branch v = v
  projectBranchVal_zip_true :
    ∀ (cond vt vf : Val),
      asBool cond = none →
      projectBranchVal cond true (zipVal cond vt vf) = vt
  projectBranchVal_zip_false :
    ∀ (cond vt vf : Val),
      asBool cond = none →
      projectBranchVal cond false (zipVal cond vt vf) = vf
  getField : FieldIdx → Val → Option Val
  setField : FieldIdx → Val → Val → Option Val
  getField_setField :
    ∀ (f : FieldIdx) (s a : Val),
      getField f s = some a → setField f s a = some s
  setField_getField :
    ∀ (f : FieldIdx) (s a s' : Val),
      setField f s a = some s' → getField f s' = some a
  setField_setField :
    ∀ (f : FieldIdx) (s a1 a2 s1 : Val),
      setField f s a1 = some s1 → setField f s1 a2 = setField f s a2
  encodeRef : LoanId → SubPath → Val
  encodeSharedRef : LoanId → SubPath → Val := encodeRef
  decodeRef : Val → Option (LoanId × SubPath)
  remapRefInVal : LoanId → LoanId → Val → Val
  sizeBound : Val → Nat

/-- Single-step field projection lens induced by `alg` at field index `f`. -/
def fieldLens {Val : Type} (alg : ValAlgebra Val) (f : FieldIdx) :
    Lens Val Val where
  get v := alg.getField f v
  put v sub := alg.setField f v sub

/-- Every `alg : ValAlgebra Val` induces a lawful single-step `fieldLens` at
every field index `f : FieldIdx`. -/
theorem fieldLens_lawful {Val : Type} (alg : ValAlgebra Val) (f : FieldIdx) :
    LawfulLens Val Val (fieldLens alg f) where
  get_put := alg.getField_setField f
  put_get := alg.setField_getField f
  put_put := alg.setField_setField f

/-- Read the nested sub-value at `SubPath` inside `v`. -/
def getPath {Val : Type} (alg : ValAlgebra Val) (path : SubPath) (v : Val) :
    Option Val :=
  path.foldr
    (fun f ih v0 =>
      match alg.getField f v0 with
      | some child => ih child
      | none => none)
    (fun v0 => some v0)
    v

/-- Update the nested sub-value at `SubPath` inside `vOld` to `vNew`. -/
def putPath {Val : Type} (alg : ValAlgebra Val) (path : SubPath)
    (vOld vNew : Val) : Option Val :=
  path.foldr
    (fun f ih vO vN =>
      match alg.getField f vO with
      | some childOld =>
        match ih childOld vN with
        | some childNew => alg.setField f vO childNew
        | none => none
      | none => none)
    (fun _ vN => some vN)
    vOld vNew

/-- Bidirectional lens focusing on the nested sub-place at `path`. -/
def subPathLens {Val : Type} (alg : ValAlgebra Val) (path : SubPath) :
    Lens Val Val where
  get v := getPath alg path v
  put v sub := putPath alg path v sub

/-- Every `alg : ValAlgebra Val` induces a lawful `subPathLens alg path` for
every nested projection path `path : SubPath`. -/
theorem subPathLens_lawful {Val : Type} (alg : ValAlgebra Val) :
    ∀ path : SubPath, LawfulLens Val Val (subPathLens alg path)
  | [] => Lens.id_lawful Val
  | f :: ps =>
    Lens.comp_lawful (fieldLens alg f) (subPathLens alg ps)
      (fieldLens_lawful alg f) (subPathLens_lawful alg ps)

/-- Conditional list selector used to merge `mutFinals` across branch joins
without requiring list-length side-conditions. -/
def zipValListBool {Val : Type} (c : Bool) (xs ys : List Val) : List Val :=
  match c with
  | true => xs
  | false => ys

/-- Elementwise conditional list merge for equal-length value lists. -/
def zipValListElem {Val : Type} (zipB : Bool → Val → Val → Val) (c : Bool)
    (xs ys : List Val) : List Val :=
  xs.foldr
    (fun x ih ys0 =>
      match ys0 with
      | [] => []
      | y :: ys' => zipB c x y :: ih ys')
    (fun _ => [])
    ys

/-- Pointwise conditional merge of two `FuncOut Val` results. -/
def zipFuncOut {Val : Type} (zipB : Bool → Val → Val → Val)
    (c : Bool) (t f : FuncOut Val) : FuncOut Val :=
  ⟨zipB c t.ret f.ret, zipValListBool c t.mutFinals f.mutFinals⟩

/-- Unconditional equivalence between `zipFuncOut` and top-level `if c then t
else f`, requiring zero side-conditions on `t.mutFinals` and `f.mutFinals`. -/
theorem zipFuncOut_eq_ite {Val : Type} (zipB : Bool → Val → Val → Val)
    (hTrue : ∀ x y, zipB true x y = x)
    (hFalse : ∀ x y, zipB false x y = y)
    (c : Bool) (t f : FuncOut Val) :
    zipFuncOut zipB c t f = (if c then t else f) := by
  cases t with
  | mk rt mt =>
    cases f with
    | mk rf mf =>
      cases c with
      | true =>
        dsimp [zipFuncOut, zipValListBool]
        rw [hTrue rt rf]
      | false =>
        dsimp [zipFuncOut, zipValListBool]
        rw [hFalse rt rf]

/-!
## Exhaustive Kernel-Checked Tests for `Lens`
-/

/-- Size-indexed tree representation for `LensTestVal`, enforcing in the type
system that every internal node's fuel index equals the exact structural size of
its subtrees plus one. -/
inductive LensTestTree : Nat → Type where
  | atom (n : Nat) : LensTestTree 1
  | branch (fl fr : Nat) (l : LensTestTree fl) (r : LensTestTree fr) :
      LensTestTree (fl + fr + 1)
  | choice (fc ft ff : Nat) (c : LensTestTree fc)
      (vt : LensTestTree ft) (vf : LensTestTree ff) :
      LensTestTree (fc + ft + ff + 1)
  | ref (lid : LoanId) (path : SubPath) : LensTestTree 1

/-- Binary tree test value used to exercise `ValAlgebra`, `getPath`, and
`putPath` at arbitrary nesting depths without `noncomputable` declarations,
fixed depth cutoffs, or forgeable fuel counters. -/
structure LensTestVal where
  fuel : Nat
  tree : LensTestTree fuel

namespace LensTestVal

/-- Atomic scalar leaf constructor. -/
def atom (n : Nat) : LensTestVal :=
  ⟨1, .atom n⟩

/-- Encoded reference leaf constructor. -/
def ref (lid : LoanId) (path : SubPath) : LensTestVal :=
  ⟨1, .ref lid path⟩

/-- Binary aggregate node constructor carrying unforgeable structural fuel
`l.fuel + r.fuel + 1`. -/
def node (l r : LensTestVal) : LensTestVal :=
  ⟨l.fuel + r.fuel + 1, .branch l.fuel r.fuel l.tree r.tree⟩

/-- Symbolic conditional choice node constructor carrying unforgeable structural
fuel `c.fuel + vt.fuel + vf.fuel + 1`. -/
def choice (c vt vf : LensTestVal) : LensTestVal :=
  ⟨c.fuel + vt.fuel + vf.fuel + 1,
   .choice c.fuel vt.fuel vf.fuel c.tree vt.tree vf.tree⟩

end LensTestVal

def remapLensTestVal (oldLid newLid : LoanId)
    (v : LensTestVal) : LensTestVal :=
  natFold
    (fun x => x)
    (fun _ ih x =>
      match x with
      | ⟨_, .atom n⟩ => .atom n
      | ⟨_, .branch fl fr l r⟩ =>
        .node (ih ⟨fl, l⟩) (ih ⟨fr, r⟩)
      | ⟨_, .choice fc ft ff c vt vf⟩ =>
        .choice (ih ⟨fc, c⟩) (ih ⟨ft, vt⟩) (ih ⟨ff, vf⟩)
      | ⟨_, .ref lid path⟩ =>
        if lid == oldLid then .ref newLid path else .ref lid path)
    v.fuel v

def lensTestGetField (f : FieldIdx) (v : LensTestVal) : Option LensTestVal :=
  match f, v with
  | 0, ⟨_, .branch fl _ l _⟩ => some ⟨fl, l⟩
  | 1, ⟨_, .branch _ fr _ r⟩ => some ⟨fr, r⟩
  | _, _ => none

def lensTestSetField (f : FieldIdx) (v sub : LensTestVal) :
    Option LensTestVal :=
  match f, v, sub with
  | 0, ⟨_, .branch _ fr _ r⟩, ⟨fSub, tSub⟩ =>
    some ⟨fSub + fr + 1, .branch fSub fr tSub r⟩
  | 1, ⟨_, .branch fl _ l _⟩, ⟨fSub, tSub⟩ =>
    some ⟨fl + fSub + 1, .branch fl fSub l tSub⟩
  | _, _, _ => none

theorem lensTest_getField_setField (f : FieldIdx) (s a : LensTestVal)
    (hGet : lensTestGetField f s = some a) :
    lensTestSetField f s a = some s := by
  cases f with
  | zero =>
    cases s with
    | mk _ t =>
      cases t with
      | branch fl fr l r =>
        injection hGet with hEq
        subst hEq
        rfl
      | atom _ => nomatch hGet
      | choice _ _ _ _ _ _ => nomatch hGet
      | ref _ _ => nomatch hGet
  | succ f' =>
    cases f' with
    | zero =>
      cases s with
      | mk _ t =>
        cases t with
        | branch fl fr l r =>
          injection hGet with hEq
          subst hEq
          rfl
        | atom _ => nomatch hGet
        | choice _ _ _ _ _ _ => nomatch hGet
        | ref _ _ => nomatch hGet
    | succ _ => nomatch hGet

theorem lensTest_setField_getField (f : FieldIdx) (s a s' : LensTestVal)
    (hPut : lensTestSetField f s a = some s') :
    lensTestGetField f s' = some a := by
  cases f with
  | zero =>
    cases s with
    | mk _ t =>
      cases t with
      | branch fl fr l r =>
        cases a with
        | mk fSub tSub =>
          injection hPut with hEq
          subst hEq
          rfl
      | atom _ => nomatch hPut
      | choice _ _ _ _ _ _ => nomatch hPut
      | ref _ _ => nomatch hPut
  | succ f' =>
    cases f' with
    | zero =>
      cases s with
      | mk _ t =>
        cases t with
        | branch fl fr l r =>
          cases a with
          | mk fSub tSub =>
            injection hPut with hEq
            subst hEq
            rfl
        | atom _ => nomatch hPut
        | choice _ _ _ _ _ _ => nomatch hPut
        | ref _ _ => nomatch hPut
    | succ _ => nomatch hPut

theorem lensTest_setField_setField (f : FieldIdx)
    (s a1 a2 s1 : LensTestVal)
    (hPut1 : lensTestSetField f s a1 = some s1) :
    lensTestSetField f s1 a2 = lensTestSetField f s a2 := by
  cases f with
  | zero =>
    cases s with
    | mk _ t =>
      cases t with
      | branch fl fr l r =>
        cases a1 with
        | mk f1 t1 =>
          cases a2 with
          | mk f2 t2 =>
            injection hPut1 with hEq
            subst hEq
            rfl
      | atom _ => nomatch hPut1
      | choice _ _ _ _ _ _ => nomatch hPut1
      | ref _ _ => nomatch hPut1
  | succ f' =>
    cases f' with
    | zero =>
      cases s with
      | mk _ t =>
        cases t with
        | branch fl fr l r =>
          cases a1 with
          | mk f1 t1 =>
            cases a2 with
            | mk f2 t2 =>
              injection hPut1 with hEq
              subst hEq
              rfl
        | atom _ => nomatch hPut1
        | choice _ _ _ _ _ _ => nomatch hPut1
        | ref _ _ => nomatch hPut1
    | succ _ => nomatch hPut1

def lensTestSubPathEq (xs ys : SubPath) : Bool :=
  xs.foldr
    (fun a ih bs =>
      match bs with
      | [] => false
      | b :: bs' => Nat.beq a b && ih bs')
    (fun bs =>
      match bs with
      | [] => true
      | _ :: _ => false)
    ys

theorem lensTestSubPathEq_refl (xs : SubPath) :
    lensTestSubPathEq xs xs = true := by
  induction xs with
  | nil => rfl
  | cons x xs' ih =>
    change (Nat.beq x x && lensTestSubPathEq xs' xs') = true
    rw [Nat.beq_refl x, ih]
    rfl

def lensTestValEqStep (ih : LensTestVal → LensTestVal → Bool)
    (a b : LensTestVal) : Bool :=
  match a, b with
  | ⟨_, .atom n1⟩, ⟨_, .atom n2⟩ => Nat.beq n1 n2
  | ⟨_, .branch fl1 fr1 l1 r1⟩, ⟨_, .branch fl2 fr2 l2 r2⟩ =>
    ih ⟨fl1, l1⟩ ⟨fl2, l2⟩ && ih ⟨fr1, r1⟩ ⟨fr2, r2⟩
  | ⟨_, .choice fc1 ft1 ff1 c1 vt1 vf1⟩,
    ⟨_, .choice fc2 ft2 ff2 c2 vt2 vf2⟩ =>
    ih ⟨fc1, c1⟩ ⟨fc2, c2⟩ &&
    ih ⟨ft1, vt1⟩ ⟨ft2, vt2⟩ &&
    ih ⟨ff1, vf1⟩ ⟨ff2, vf2⟩
  | ⟨_, .ref lid1 p1⟩, ⟨_, .ref lid2 p2⟩ =>
    Nat.beq lid1 lid2 && lensTestSubPathEq p1 p2
  | _, _ => false

def lensTestValEqFuel (k : Nat) (v1 v2 : LensTestVal) : Bool :=
  natFold
    (fun _ _ => false)
    (fun _ ih a b => lensTestValEqStep ih a b)
    k v1 v2

def lensTestValEq (v1 v2 : LensTestVal) : Bool :=
  lensTestValEqFuel v1.fuel v1 v2

theorem lensTestTree_eq_refl :
    ∀ {f : Nat} (t : LensTestTree f) (k : Nat),
      f ≤ k → lensTestValEqFuel k ⟨f, t⟩ ⟨f, t⟩ = true := by
  intro f t
  induction t with
  | atom n =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ k' =>
      change Nat.beq n n = true
      exact Nat.beq_refl n
  | branch fl fr l r ihl ihr =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ k' =>
      have hSub : fl + fr ≤ k' := Nat.le_of_succ_le_succ hLe
      have hFl : fl ≤ k' := Nat.le_trans (Nat.le_add_right fl fr) hSub
      have hFr : fr ≤ k' := Nat.le_trans (Nat.le_add_left fr fl) hSub
      change
        (lensTestValEqFuel k' ⟨fl, l⟩ ⟨fl, l⟩ &&
         lensTestValEqFuel k' ⟨fr, r⟩ ⟨fr, r⟩) = true
      rw [ihl k' hFl, ihr k' hFr]
      rfl
  | choice fc ft ff c vt vf ihc iht ihf =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ k' =>
      have hSub : fc + ft + ff ≤ k' := Nat.le_of_succ_le_succ hLe
      have hSub12 : fc + ft ≤ k' :=
        Nat.le_trans (Nat.le_add_right (fc + ft) ff) hSub
      have hFc : fc ≤ k' := Nat.le_trans (Nat.le_add_right fc ft) hSub12
      have hFt : ft ≤ k' := Nat.le_trans (Nat.le_add_left ft fc) hSub12
      have hFf : ff ≤ k' := Nat.le_trans (Nat.le_add_left ff (fc + ft)) hSub
      change
        (lensTestValEqFuel k' ⟨fc, c⟩ ⟨fc, c⟩ &&
         lensTestValEqFuel k' ⟨ft, vt⟩ ⟨ft, vt⟩ &&
         lensTestValEqFuel k' ⟨ff, vf⟩ ⟨ff, vf⟩) = true
      rw [ihc k' hFc, iht k' hFt, ihf k' hFf]
      rfl
  | ref lid path =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ k' =>
      change (Nat.beq lid lid && lensTestSubPathEq path path) = true
      rw [Nat.beq_refl lid, lensTestSubPathEq_refl path]
      rfl

theorem lensTestValEq_refl (v : LensTestVal) : lensTestValEq v v = true := by
  cases v with
  | mk f t =>
    exact lensTestTree_eq_refl t f (Nat.le_refl f)

def lensTestAsBool (v : LensTestVal) : Option Bool :=
  match v with
  | ⟨_, .atom n⟩ => some (n != 0)
  | _ => none

def lensTestZipVal (c vt vf : LensTestVal) : LensTestVal :=
  match lensTestAsBool c with
  | some true => vt
  | some false => vf
  | none => .choice c vt vf

def lensTestProjectBranchVal (c : LensTestVal) (branch : Bool)
    (v : LensTestVal) : LensTestVal :=
  match lensTestAsBool c with
  | some _ => v
  | none =>
    natFold
      (fun v0 => v0)
      (fun _ ih v0 =>
        match v0 with
        | ⟨_, .choice fc ft ff cond vt vf⟩ =>
          if lensTestValEq c ⟨fc, cond⟩ then
            if branch then ⟨ft, vt⟩ else ⟨ff, vf⟩
          else
            .choice ⟨fc, cond⟩ (ih ⟨ft, vt⟩) (ih ⟨ff, vf⟩)
        | ⟨_, .branch fl fr l r⟩ =>
          .node (ih ⟨fl, l⟩) (ih ⟨fr, r⟩)
        | other => other)
      v.fuel v

theorem lensTest_projectBranchVal_concrete (cond : LensTestVal)
    (b branch : Bool) (v : LensTestVal)
    (hConcrete : lensTestAsBool cond = some b) :
    lensTestProjectBranchVal cond branch v = v := by
  dsimp [lensTestProjectBranchVal]
  rw [hConcrete]

theorem lensTest_projectBranchVal_zip_true (cond vt vf : LensTestVal)
    (hSym : lensTestAsBool cond = none) :
    lensTestProjectBranchVal cond true (lensTestZipVal cond vt vf) = vt := by
  dsimp [lensTestProjectBranchVal, lensTestZipVal]
  rw [hSym]
  cases cond with
  | mk fc tc =>
    cases vt with
    | mk ft tt =>
      cases vf with
      | mk ff tf =>
        change
          (if lensTestValEq ⟨fc, tc⟩ ⟨fc, tc⟩ then (⟨ft, tt⟩ : LensTestVal)
           else _) = ⟨ft, tt⟩
        rw [lensTestValEq_refl ⟨fc, tc⟩]
        rfl

theorem lensTest_projectBranchVal_zip_false (cond vt vf : LensTestVal)
    (hSym : lensTestAsBool cond = none) :
    lensTestProjectBranchVal cond false (lensTestZipVal cond vt vf) = vf := by
  dsimp [lensTestProjectBranchVal, lensTestZipVal]
  rw [hSym]
  cases cond with
  | mk fc tc =>
    cases vt with
    | mk ft tt =>
      cases vf with
      | mk ff tf =>
        change
          (if lensTestValEq ⟨fc, tc⟩ ⟨fc, tc⟩ then (⟨ff, tf⟩ : LensTestVal)
           else _) = ⟨ff, tf⟩
        rw [lensTestValEq_refl ⟨fc, tc⟩]
        rfl

def lensTestValAlg : ValAlgebra LensTestVal where
  defaultVal := .atom 0
  asBool := lensTestAsBool
  zipVal := lensTestZipVal
  projectBranchVal := lensTestProjectBranchVal
  projectBranchVal_concrete := lensTest_projectBranchVal_concrete
  projectBranchVal_zip_true := lensTest_projectBranchVal_zip_true
  projectBranchVal_zip_false := lensTest_projectBranchVal_zip_false
  getField := lensTestGetField
  setField := lensTestSetField
  getField_setField := lensTest_getField_setField
  setField_getField := lensTest_setField_getField
  setField_setField := lensTest_setField_setField
  encodeRef lid path := .ref lid path
  decodeRef v :=
    match v with
    | ⟨_, .ref lid path⟩ => some (lid, path)
    | _ => none
  remapRefInVal := remapLensTestVal
  sizeBound v := v.fuel

theorem lensTestValAlg_fieldLens_lawful (f : FieldIdx) :
    LawfulLens LensTestVal LensTestVal (fieldLens lensTestValAlg f) :=
  fieldLens_lawful lensTestValAlg f

theorem lensTestValAlg_subPathLens_lawful (path : SubPath) :
    LawfulLens LensTestVal LensTestVal (subPathLens lensTestValAlg path) :=
  subPathLens_lawful lensTestValAlg path

/-- `natFold` is exact at indices well above eight (`n = 9`, `12`, `20`),
never truncating or aliasing. -/
theorem natFold_above_eight_exact :
    natFold 0 (fun _ acc => acc + 1) 9 = 9 ∧
    natFold 0 (fun _ acc => acc + 1) 12 = 12 ∧
    natFold 0 (fun _ acc => acc + 1) 20 = 20 :=
  ⟨rfl, rfl, rfl⟩

/-- `listFold` traverses lists longer than eight elements completely and passes
the exact remaining suffix to `cons`. -/
theorem listFold_above_eight_exact :
    listFold 0 (fun x _ acc => x + acc)
      [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] = 78 ∧
    listFold [] (fun _ tail _ => tail) [1, 2, 3] = [2, 3] :=
  ⟨rfl, rfl⟩

/-- Deep 10-level binary tree value for testing `getPath` and `putPath` beyond
depth 8. -/
def deepLensTestTree (leaf : Nat) : LensTestVal :=
  .node (.node (.node (.node (.node (.node (.node (.node (.node (.node
    (.atom leaf) (.atom 1)) (.atom 2)) (.atom 3)) (.atom 4)) (.atom 5))
    (.atom 6)) (.atom 7)) (.atom 8)) (.atom 9)) (.atom 10)

/-- `getPath` and `putPath` succeed and preserve sibling branches at depth
10. -/
theorem getPath_putPath_depth_ten (x y : Nat) :
    let path10 : SubPath := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    getPath lensTestValAlg path10 (deepLensTestTree x) = some (.atom x) ∧
    putPath lensTestValAlg path10 (deepLensTestTree x) (.atom y) =
      some (deepLensTestTree y) ∧
    getPath lensTestValAlg [1] (deepLensTestTree x) = some (.atom 10) ∧
    getPath lensTestValAlg [0, 0, 0, 2] (deepLensTestTree x) = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `HoldsFnSpec` succeeds on `.ok` and rejects `.fail`. -/
theorem holdsFnSpec_ok_and_fail_tests :
    HoldsFnSpec (.ok (42 : Nat)) (fun n => n = 42) ∧
    ¬ HoldsFnSpec (.fail : EvalOutcome Nat) (fun _ => True) :=
  ⟨rfl, holdsFnSpec_not_fail _⟩

/-- Exhaustive unit tests for `fix2`/`fix4`/`fix8`/`fix16` combinators. -/
theorem fix_combinators_exhaustive_tests :
    fix2 (fun n => n + 1) 0 = 2 ∧
    fix4 (fun n => n + 1) 0 = 4 ∧
    fix8 (fun n => n + 1) 0 = 8 ∧
    fix16 (fun n => n + 1) 0 = 16 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Exhaustive unit tests for `Lens.id`, `Lens.comp`, `Lens.id_lawful`, and
`Lens.comp_lawful`, including `none` propagation when an outer or inner lens
fails. -/
theorem lens_id_and_comp_exhaustive_tests :
    (Lens.id Nat).get 15 = some 15 ∧
    (Lens.id Nat).put 15 20 = some 20 ∧
    (Lens.comp (fieldLens lensTestValAlg 0) (fieldLens lensTestValAlg 1)).get
      (.node (.node (.atom 1) (.atom 2)) (.atom 3)) = some (.atom 2) ∧
    (Lens.comp (fieldLens lensTestValAlg 0) (fieldLens lensTestValAlg 1)).get
      (.node (.atom 1) (.atom 3)) = none ∧
    (Lens.comp (fieldLens lensTestValAlg 0) (fieldLens lensTestValAlg 1)).get
      (.atom 1) = none ∧
    (Lens.comp (fieldLens lensTestValAlg 0) (fieldLens lensTestValAlg 1)).put
      (.node (.node (.atom 1) (.atom 2)) (.atom 3)) (.atom 99) =
      some (.node (.node (.atom 1) (.atom 99)) (.atom 3)) ∧
    (Lens.comp (fieldLens lensTestValAlg 0) (fieldLens lensTestValAlg 1)).put
      (.node (.atom 1) (.atom 3)) (.atom 99) = none ∧
    (Lens.comp (fieldLens lensTestValAlg 0) (fieldLens lensTestValAlg 1)).put
      (.atom 1) (.atom 99) = none ∧
    LawfulLens LensTestVal LensTestVal (Lens.id LensTestVal) ∧
    LawfulLens LensTestVal LensTestVal
      (Lens.comp (fieldLens lensTestValAlg 0) (fieldLens lensTestValAlg 1)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   Lens.id_lawful LensTestVal,
   Lens.comp_lawful
     (fieldLens lensTestValAlg 0)
     (fieldLens lensTestValAlg 1)
     (lensTestValAlg_fieldLens_lawful 0)
     (lensTestValAlg_fieldLens_lawful 1)⟩

/-- Exhaustive unit tests for `zipValListBool`, `zipValListElem`, `zipFuncOut`,
and `zipFuncOut_eq_ite`. -/
theorem zipVal_and_zipFuncOut_exhaustive_tests (c : Bool) :
    let zipB (b : Bool) (x y : Nat) : Nat := if b then x else y
    zipValListBool true [1, 2] [3] = [1, 2] ∧
    zipValListBool false [1, 2] [3] = [3] ∧
    zipValListElem zipB true [10, 20] [30, 40, 50] = [10, 20] ∧
    zipValListElem zipB false [10, 20] [30, 40, 50] = [30, 40] ∧
    zipFuncOut zipB c ⟨1, [10, 20]⟩ ⟨2, [30]⟩ =
      (if c then ⟨1, [10, 20]⟩ else ⟨2, [30]⟩) :=
  ⟨rfl, rfl, rfl, rfl,
   zipFuncOut_eq_ite
     (fun b x y => if b then x else y)
     (fun _ _ => rfl)
     (fun _ _ => rfl)
     c ⟨1, [10, 20]⟩ ⟨2, [30]⟩⟩

/-- Exhaustive negative and boundary tests for `getPath`, `putPath`, `asBool`,
`zipVal`, `projectBranchVal`, `encodeRef`, `decodeRef`, and deep post-update
`remapRefInVal` on `lensTestValAlg`. -/
theorem lensTestValAlg_operations_and_failures_tests :
    getPath lensTestValAlg [0] (.atom 5) = none ∧
    getPath lensTestValAlg [0] (.ref 1 []) = none ∧
    getPath lensTestValAlg [2] (.node (.atom 1) (.atom 2)) = none ∧
    putPath lensTestValAlg [0] (.atom 5) (.atom 6) = none ∧
    putPath lensTestValAlg [0] (.ref 1 []) (.atom 6) = none ∧
    putPath lensTestValAlg [2] (.node (.atom 1) (.atom 2)) (.atom 6) = none ∧
    putPath lensTestValAlg [] (.atom 5) (.atom 9) = some (.atom 9) ∧
    lensTestValAlg.asBool (.atom 1) = some true ∧
    lensTestValAlg.asBool (.atom 0) = some false ∧
    lensTestValAlg.asBool (.node (.atom 1) (.atom 2)) = none ∧
    lensTestValAlg.zipVal (.atom 1) (.atom 10) (.atom 20) = .atom 10 ∧
    lensTestValAlg.zipVal (.atom 0) (.atom 10) (.atom 20) = .atom 20 ∧
    lensTestValAlg.zipVal (.ref 0 []) (.atom 10) (.atom 20) =
      .choice (.ref 0 []) (.atom 10) (.atom 20) ∧
    lensTestValAlg.projectBranchVal (.ref 0 []) true
      (.choice (.ref 0 []) (.atom 10) (.atom 20)) = .atom 10 ∧
    lensTestValAlg.projectBranchVal (.ref 0 []) false
      (.choice (.ref 0 []) (.atom 10) (.atom 20)) = .atom 20 ∧
    lensTestValAlg.decodeRef (lensTestValAlg.encodeRef 7 [0, 1]) =
      some (7, [0, 1]) ∧
    lensTestValAlg.decodeRef (lensTestValAlg.encodeSharedRef 7 [0, 1]) =
      some (7, [0, 1]) ∧
    lensTestValAlg.remapRefInVal 3 9
      (.node (.ref 3 [0]) (.node (.atom 1) (.ref 4 [1]))) =
      .node (.ref 9 [0]) (.node (.atom 1) (.ref 4 [1])) ∧
    (let path10 : SubPath := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
     match putPath lensTestValAlg path10 (deepLensTestTree 0) (.ref 3 [1]) with
     | some deepWithRef =>
       match putPath lensTestValAlg [0] (.node (.atom 0) (.atom 1))
           deepWithRef with
       | some replacedRoot =>
         getPath lensTestValAlg (0 :: path10)
           (lensTestValAlg.remapRefInVal 3 9 replacedRoot) =
           some (.ref 9 [1])
       | none => False
     | none => False) ∧
    lensTestValAlg.decodeRef (.atom 7) = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.PureLift
