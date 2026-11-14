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
- `zipVal` and `projectBranchVal`: symbolic conditional merge at diamond
  control-flow joins and branch-specific value projection,
- `getField` and `setField`: aggregate child projection and update by index,
- `encodeRef`, `encodeSharedRef`, `decodeRef`, and `remapRefInVal`: first-order
  borrow handle representation and recursive loan-ID renaming inside values. -/
structure ValAlgebra (Val : Type) where
  defaultVal : Val
  asBool : Val → Option Bool
  zipVal : Val → Val → Val → Val
  projectBranchVal : Val → Bool → Val → Val := fun _ _ v => v
  getField : FieldIdx → Val → Option Val
  setField : FieldIdx → Val → Val → Option Val
  encodeRef : LoanId → SubPath → Val
  encodeSharedRef : LoanId → SubPath → Val := encodeRef
  decodeRef : Val → Option (LoanId × SubPath)
  remapRefInVal : LoanId → LoanId → Val → Val

/-- Single-step field projection lens induced by `alg` at field index `f`. -/
def fieldLens {Val : Type} (alg : ValAlgebra Val) (f : FieldIdx) :
    Lens Val Val where
  get v := alg.getField f v
  put v sub := alg.setField f v sub

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

/-- If every single-field lens is lawful, then `subPathLens alg path` is lawful
for every nested projection path `path : SubPath`. -/
theorem subPathLens_lawful {Val : Type} (alg : ValAlgebra Val)
    (hField : ∀ f : FieldIdx, LawfulLens Val Val (fieldLens alg f)) :
    ∀ path : SubPath, LawfulLens Val Val (subPathLens alg path)
  | [] => Lens.id_lawful Val
  | f :: ps =>
    Lens.comp_lawful (fieldLens alg f) (subPathLens alg ps)
      (hField f) (subPathLens_lawful alg hField ps)

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

/-- Binary tree test value used to exercise `ValAlgebra`, `getPath`, and
`putPath` at arbitrary nesting depths. -/
inductive LensTestVal where
  | atom (n : Nat)
  | node (l r : LensTestVal)
  | ref (lid : LoanId) (path : SubPath)

noncomputable def remapLensTestVal (oldLid newLid : LoanId)
    (v : LensTestVal) : LensTestVal :=
  @LensTestVal.rec (fun _ => LensTestVal)
    (fun n => .atom n)
    (fun _ _ ihL ihR => .node ihL ihR)
    (fun lid path =>
      if lid == oldLid then .ref newLid path else .ref lid path)
    v

noncomputable def lensTestValAlg : ValAlgebra LensTestVal where
  defaultVal := .atom 0
  asBool v :=
    match v with
    | .atom n => some (n != 0)
    | _ => none
  zipVal c vt vf :=
    match c with
    | .atom n => if n != 0 then vt else vf
    | .ref lid p => .node (.ref lid p) (.node vt vf)
    | _ => vf
  projectBranchVal _ branch v :=
    match v with
    | .node (.ref _ _) (.node vt vf) => if branch then vt else vf
    | _ => v
  getField f v :=
    match f, v with
    | 0, .node l _ => some l
    | 1, .node _ r => some r
    | _, _ => none
  setField f v sub :=
    match f, v with
    | 0, .node _ r => some (.node sub r)
    | 1, .node l _ => some (.node l sub)
    | _, _ => none
  encodeRef lid path := .ref lid path
  decodeRef v :=
    match v with
    | .ref lid path => some (lid, path)
    | _ => none
  remapRefInVal := remapLensTestVal

theorem lensTestValAlg_fieldLens_lawful (f : FieldIdx) :
    LawfulLens LensTestVal LensTestVal (fieldLens lensTestValAlg f) where
  get_put := by
    intro s a hGet
    cases f with
    | zero =>
      cases s with
      | node l r =>
        dsimp [fieldLens, lensTestValAlg] at hGet
        injection hGet with hEq
        subst hEq
        rfl
      | atom _ => nomatch hGet
      | ref _ _ => nomatch hGet
    | succ f' =>
      cases f' with
      | zero =>
        cases s with
        | node l r =>
          dsimp [fieldLens, lensTestValAlg] at hGet
          injection hGet with hEq
          subst hEq
          rfl
        | atom _ => nomatch hGet
        | ref _ _ => nomatch hGet
      | succ _ => nomatch hGet
  put_get := by
    intro s a s' hPut
    cases f with
    | zero =>
      cases s with
      | node l r =>
        dsimp [fieldLens, lensTestValAlg] at hPut
        injection hPut with hEq
        subst hEq
        rfl
      | atom _ => nomatch hPut
      | ref _ _ => nomatch hPut
    | succ f' =>
      cases f' with
      | zero =>
        cases s with
        | node l r =>
          dsimp [fieldLens, lensTestValAlg] at hPut
          injection hPut with hEq
          subst hEq
          rfl
        | atom _ => nomatch hPut
        | ref _ _ => nomatch hPut
      | succ _ => nomatch hPut
  put_put := by
    intro s a1 a2 s1 hPut1
    cases f with
    | zero =>
      cases s with
      | node l r =>
        dsimp [fieldLens, lensTestValAlg] at hPut1
        injection hPut1 with hEq
        subst hEq
        rfl
      | atom _ => nomatch hPut1
      | ref _ _ => nomatch hPut1
    | succ f' =>
      cases f' with
      | zero =>
        cases s with
        | node l r =>
          dsimp [fieldLens, lensTestValAlg] at hPut1
          injection hPut1 with hEq
          subst hEq
          rfl
        | atom _ => nomatch hPut1
        | ref _ _ => nomatch hPut1
      | succ _ => nomatch hPut1

theorem lensTestValAlg_subPathLens_lawful (path : SubPath) :
    LawfulLens LensTestVal LensTestVal (subPathLens lensTestValAlg path) :=
  subPathLens_lawful lensTestValAlg lensTestValAlg_fieldLens_lawful path

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
`zipVal`, `encodeRef`, and `decodeRef` on `lensTestValAlg`. -/
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
      .node (.ref 0 []) (.node (.atom 10) (.atom 20)) ∧
    lensTestValAlg.projectBranchVal (.ref 0 []) true
      (.node (.ref 0 []) (.node (.atom 10) (.atom 20))) = .atom 10 ∧
    lensTestValAlg.projectBranchVal (.ref 0 []) false
      (.node (.ref 0 []) (.node (.atom 10) (.atom 20))) = .atom 20 ∧
    lensTestValAlg.decodeRef (lensTestValAlg.encodeRef 7 [0, 1]) =
      some (7, [0, 1]) ∧
    lensTestValAlg.decodeRef (lensTestValAlg.encodeSharedRef 7 [0, 1]) =
      some (7, [0, 1]) ∧
    lensTestValAlg.remapRefInVal 3 9
      (.node (.ref 3 [0]) (.node (.atom 1) (.ref 4 [1]))) =
      .node (.ref 9 [0]) (.node (.atom 1) (.ref 4 [1])) ∧
    lensTestValAlg.decodeRef (.atom 7) = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl⟩

end Anneal.PureLift
