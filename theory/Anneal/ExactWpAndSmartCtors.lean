/-
Copyright 2026 The Fuchsia Authors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Trusted

/-!
# `Std.Do`-Insulated `ExactWP`, `Bitprism` Smart Constructors, & `veil_frame` Named-Field Framing (`Anneal.ExactWpAndSmartCtors`)

This module provides three foundational verification layers directly over Anneal's unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics` with **ZERO `Std.Do` / `Std.Tactic.Do` imports**
(complete insulation from upstream Lean `Std.WP` churn and `lean4#16728` `Legacy.DoResult*`):

1. **Part A (`Std.Do`-Insulated Exact Two-Continuation WP Algebra)**:
   - `ExactOutcome S E A`: carries updated state `S` on BOTH `.ok (val : A) (state : S)` AND
     `.error (err : E) (state : S)`, preserving partial committed state updates preceding a failed
     check (mirroring `proofs-rs/lean-miri#93`).
   - `AnnealExactWP`, `ExactTriple`, `TreeBorrowsFrameWP`, `ProtectorReleaseWP`: bidirectional `↔`
     weakest-precondition and strongest-postcondition characterization (`exactWP_iff`, `exactWP_bind`,
     `exactWP_foldl`, `exactWP_consequence`, `exactWP_negation_refutation`), fuel-bounded &
     loop-invariant whole-body safety VCs (`ExactBodySafetyVC`), and direct instantiations over
     unmodified `Trusted.Rustc.V2026_06_01.MirSemantics` (`stepMirFn`, `evalStmt`, `evalTerminator`,
     `restoreCallerProtectors`, `disableFrameBorrows`, `hasFrameDeallocProtectorConflict`).
2. **Part B (`Bitprism` cl/1029634110 Kernel-Proved Smart Simplifying Constructors)**:
   - Leaves all raw `Trusted.Rustc.V2026_06_01.MirAst` & `MirSemantics` constructors completely
     untouched (`rfl`/`dsimp only` correspondence proofs unaffected).
   - Smart constructors (`mkAddSmart`, `mkSubSmart`, `mkMulSmart`, `mkBitAndSmart`, `mkBitOrSmart`,
     `mkBitXorSmart`, `mkShlSmart`, `mkShrSmart`, `mkPtrOffsetSmart`, `mkWrappingPtrOffsetSmart`,
     `mkMemWriteFrame`) at BOTH the scalar/pointer algebraic level AND the MIR `Rvalue`/`Operand`/
     frame level, each paired with an exact kernel-proved `*_eq_raw` theorem carrying the exact
     operand-definedness / width / overflow preconditions — plus negative refutations proving UB
     is NEVER unsoundly erased (`0 & dead`, `0 & uninit`, `uninit * 0`, `addUnchecked` overflow).
3. **Part C (`veil#209` `veil_frame` Named-Field Framing over `MirSemantics.Memory` & `StackFrame`)**:
   - Exhaustive enumeration of all 14 fields of `Trusted.Rustc.V2026_06_01.MirSemantics.Memory`
     plus all 3 fields of `StackFrame` (`Memory.ext_allFields`, `MachineState.ext_allFields`).
   - Named-field framing predicates (`AgreeOutsideFields`, `ReadsOnlyFields`, `ModifiesOnlyFields`,
     `DisjointFields`), named combinators (`frame_locals`, `frame_callerLocals`, `frame_borrows`,
     `frame_globals`, `frame_heap`, `frame_callStack`, `frame_protectors`), `exactWP_veil_frame`,
     real `Trusted.MirSemantics` transition framing theorems, and an ergonomic `anneal_veil_frame`
     tactic automatically discharging disjoint named-field preservation goals.
-/

namespace Anneal.ExactWpAndSmartCtors

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

set_option autoImplicit false

/-! ## Part A. `Std.Do`-Insulated Exact Two-Continuation WP Algebra -/

section ExactWPAlgebra

/-- Two-continuation state outcome retaining the updated state `S` on BOTH normal completion
(`.ok`) and error completion (`.error`), so partial committed effects preceding a failed check
are faithfully observed (mirroring `proofs-rs/lean-miri#93` without `Std.Do`). -/
inductive ExactOutcome (S E A : Type) : Type where
  | ok (val : A) (state : S) : ExactOutcome S E A
  | error (err : E) (state : S) : ExactOutcome S E A
  deriving DecidableEq, Repr

/-- State-threading effect producing an `ExactOutcome` from any pre-state `S`. -/
abbrev ExactAction (S E A : Type) : Type := S → ExactOutcome S E A

namespace ExactAction

def pure {S E A : Type} (a : A) : ExactAction S E A := fun s => .ok a s

def throw {S E A : Type} (e : E) : ExactAction S E A := fun s => .error e s

def get {S E : Type} : ExactAction S E S := fun s => .ok s s

def set {S E : Type} (s' : S) : ExactAction S E Unit := fun _ => .ok () s'

def modify {S E : Type} (f : S → S) : ExactAction S E Unit := fun s => .ok () (f s)

def bind {S E A B : Type} (m : ExactAction S E A) (k : A → ExactAction S E B) :
    ExactAction S E B := fun s =>
  match m s with
  | .ok a s' => k a s'
  | .error e s' => .error e s'

def seq {S E A B : Type} (m : ExactAction S E A) (n : ExactAction S E B) : ExactAction S E B :=
  bind m (fun _ => n)

def map {S E A B : Type} (f : A → B) (m : ExactAction S E A) : ExactAction S E B :=
  bind m (fun a => pure (f a))

/-- Lift an `EStateM E S A` into `ExactAction S E A` with zero loss of error-branch state. -/
def ofEStateM {S E A : Type} (m : EStateM E S A) : ExactAction S E A := fun s =>
  match m s with
  | .ok a s' => .ok a s'
  | .error e s' => .error e s'

/-- Inverse conversion back to `EStateM E S A`. -/
def toEStateM {S E A : Type} (m : ExactAction S E A) : EStateM E S A := fun s =>
  match m s with
  | .ok a s' => .ok a s'
  | .error e s' => .error e s'

theorem ofEStateM_toEStateM {S E A : Type} (m : ExactAction S E A) :
    ofEStateM (toEStateM m) = m := by
  funext s
  unfold ofEStateM toEStateM
  cases m s <;> rfl

theorem toEStateM_ofEStateM {S E A : Type} (m : EStateM E S A) :
    toEStateM (ofEStateM m) = m := by
  funext s
  dsimp only [toEStateM, ofEStateM]
  cases m s <;> rfl

/-- Left fold threading committed state across a list and halting immediately on the first error
while retaining the exact state committed by all preceding iterations. -/
def foldl {S E α β : Type} (step : β → α → ExactAction S E β) :
    β → List α → ExactAction S E β
  | acc, [] => pure acc
  | acc, x :: xs => bind (step acc x) (fun acc' => foldl step acc' xs)

end ExactAction

/-- **Exact two-continuation weakest precondition** (completely `Std.Do`-free):
`AnnealExactWP act post onError s` holds iff running `act` from `s` either succeeds with
`.ok a s'` satisfying `post a s'`, or fails with `.error e s'` satisfying `onError e s'`. -/
def AnnealExactWP {S E A : Type} (act : ExactAction S E A)
    (post : A → S → Prop) (onError : E → S → Prop) (s : S) : Prop :=
  match act s with
  | .ok a s' => post a s'
  | .error e s' => onError e s'

/-- Two-continuation Hoare triple over `ExactAction`. -/
def ExactTriple {S E A : Type} (pre : S → Prop) (act : ExactAction S E A)
    (post : A → S → Prop) (onError : E → S → Prop) : Prop :=
  ∀ s, pre s → AnnealExactWP act post onError s

/-- **Bidirectional exactness (`exactWP_iff`)**: `AnnealExactWP` is simultaneously the weakest
precondition and strongest post-characterization of `act` (never a lossy one-way approximation). -/
theorem exactWP_iff {S E A : Type} (act : ExactAction S E A)
    (post : A → S → Prop) (onError : E → S → Prop) (s : S) :
    AnnealExactWP act post onError s ↔
      (∀ a s', act s = .ok a s' → post a s') ∧
      (∀ e s', act s = .error e s' → onError e s') := by
  unfold AnnealExactWP
  cases h : act s with
  | ok a s' =>
    constructor
    · intro hp
      exact ⟨(fun a' s'' hEq => by cases hEq; exact hp), (fun _ _ hEq => by cases hEq)⟩
    · intro ⟨hOk, _⟩
      exact hOk a s' rfl
  | error e s' =>
    constructor
    · intro he
      exact ⟨(fun _ _ hEq => by cases hEq), (fun e' s'' hEq => by cases hEq; exact he)⟩
    · intro ⟨_, hErr⟩
      exact hErr e s' rfl

theorem exactWP_of_eq_ok {S E A : Type} {act : ExactAction S E A}
    {post : A → S → Prop} {onError : E → S → Prop} {s s' : S} {a : A}
    (h : act s = .ok a s') :
    AnnealExactWP act post onError s ↔ post a s' := by
  unfold AnnealExactWP; rw [h]

theorem exactWP_of_eq_error {S E A : Type} {act : ExactAction S E A}
    {post : A → S → Prop} {onError : E → S → Prop} {s s' : S} {e : E}
    (h : act s = .error e s') :
    AnnealExactWP act post onError s ↔ onError e s' := by
  unfold AnnealExactWP; rw [h]

theorem exactTriple_iff {S E A : Type} (pre : S → Prop) (act : ExactAction S E A)
    (post : A → S → Prop) (onError : E → S → Prop) :
    ExactTriple pre act post onError ↔ ∀ s, pre s → AnnealExactWP act post onError s :=
  Iff.rfl

theorem exactWP_self_triple {S E A : Type} (act : ExactAction S E A)
    (post : A → S → Prop) (onError : E → S → Prop) :
    ExactTriple (AnnealExactWP act post onError) act post onError :=
  fun _ h => h

theorem exactWP_pure {S E A : Type} (a : A)
    (post : A → S → Prop) (onError : E → S → Prop) (s : S) :
    AnnealExactWP (ExactAction.pure a) post onError s ↔ post a s :=
  Iff.rfl

theorem exactWP_throw {S E A : Type} (e : E)
    (post : A → S → Prop) (onError : E → S → Prop) (s : S) :
    AnnealExactWP (ExactAction.throw (A := A) e) post onError s ↔ onError e s :=
  Iff.rfl

theorem exactWP_get {S E : Type}
    (post : S → S → Prop) (onError : E → S → Prop) (s : S) :
    AnnealExactWP (ExactAction.get (E := E)) post onError s ↔ post s s :=
  Iff.rfl

theorem exactWP_set {S E : Type} (s' : S)
    (post : Unit → S → Prop) (onError : E → S → Prop) (s : S) :
    AnnealExactWP (ExactAction.set (E := E) s') post onError s ↔ post () s' :=
  Iff.rfl

theorem exactWP_modify {S E : Type} (f : S → S)
    (post : Unit → S → Prop) (onError : E → S → Prop) (s : S) :
    AnnealExactWP (ExactAction.modify (E := E) f) post onError s ↔ post () (f s) :=
  Iff.rfl

/-- Exact monadic sequencing law (`↔`). -/
theorem exactWP_bind {S E A B : Type} (m : ExactAction S E A) (k : A → ExactAction S E B)
    (post : B → S → Prop) (onError : E → S → Prop) (s : S) :
    AnnealExactWP (ExactAction.bind m k) post onError s ↔
      AnnealExactWP m (fun a s' => AnnealExactWP (k a) post onError s') onError s := by
  unfold AnnealExactWP ExactAction.bind
  cases m s <;> rfl

theorem exactWP_seq {S E A B : Type} (m : ExactAction S E A) (n : ExactAction S E B)
    (post : B → S → Prop) (onError : E → S → Prop) (s : S) :
    AnnealExactWP (ExactAction.seq m n) post onError s ↔
      AnnealExactWP m (fun _ s' => AnnealExactWP n post onError s') onError s :=
  exactWP_bind m (fun _ => n) post onError s

theorem exactWP_map {S E A B : Type} (f : A → B) (m : ExactAction S E A)
    (post : B → S → Prop) (onError : E → S → Prop) (s : S) :
    AnnealExactWP (ExactAction.map f m) post onError s ↔
      AnnealExactWP m (fun a s' => post (f a) s') onError s :=
  exactWP_bind m (fun a => ExactAction.pure (f a)) post onError s

theorem exactWP_ite {S E A : Type} (c : Bool) (t f : ExactAction S E A)
    (post : A → S → Prop) (onError : E → S → Prop) (s : S) :
    AnnealExactWP (if c then t else f) post onError s ↔
      (c = true → AnnealExactWP t post onError s) ∧
      (c = false → AnnealExactWP f post onError s) := by
  cases c with
  | true => simp
  | false => simp

theorem exactWP_match_option {S E A B : Type} (o : Option B)
    (onNone : ExactAction S E A) (onSome : B → ExactAction S E A)
    (post : A → S → Prop) (onError : E → S → Prop) (s : S) :
    AnnealExactWP (match o with | none => onNone | some b => onSome b) post onError s ↔
      (o = none → AnnealExactWP onNone post onError s) ∧
      (∀ b, o = some b → AnnealExactWP (onSome b) post onError s) := by
  cases o with
  | none => simp
  | some b => simp

/-- Monotonicity / consequence rule in both success and error continuations. -/
theorem exactWP_consequence {S E A : Type} {act : ExactAction S E A}
    {post₁ post₂ : A → S → Prop} {err₁ err₂ : E → S → Prop} {s : S}
    (hOk : ∀ a s', post₁ a s' → post₂ a s')
    (hErr : ∀ e s', err₁ e s' → err₂ e s')
    (h : AnnealExactWP act post₁ err₁ s) :
    AnnealExactWP act post₂ err₂ s := by
  unfold AnnealExactWP at h ⊢
  cases hAct : act s with
  | ok a s' => rw [hAct] at h; exact hOk a s' h
  | error e s' => rw [hAct] at h; exact hErr e s' h

/-- Pointwise equivalence congruence. -/
theorem exactWP_congr {S E A : Type} {act₁ act₂ : ExactAction S E A}
    {post : A → S → Prop} {onError : E → S → Prop} {s : S}
    (hEq : act₁ s = act₂ s) :
    AnnealExactWP act₁ post onError s ↔ AnnealExactWP act₂ post onError s := by
  unfold AnnealExactWP; rw [hEq]

/-- Exact conjunction distribution (holds in BOTH directions because `act` is deterministic). -/
theorem exactWP_and {S E A : Type} (act : ExactAction S E A)
    (p₁ p₂ : A → S → Prop) (e₁ e₂ : E → S → Prop) (s : S) :
    AnnealExactWP act (fun a s' => p₁ a s' ∧ p₂ a s') (fun e s' => e₁ e s' ∧ e₂ e s') s ↔
      AnnealExactWP act p₁ e₁ s ∧ AnnealExactWP act p₂ e₂ s := by
  unfold AnnealExactWP
  cases act s <;> rfl

/-- Exact disjunction distribution. -/
theorem exactWP_or {S E A : Type} (act : ExactAction S E A)
    (p₁ p₂ : A → S → Prop) (e₁ e₂ : E → S → Prop) (s : S) :
    AnnealExactWP act (fun a s' => p₁ a s' ∨ p₂ a s') (fun e s' => e₁ e s' ∨ e₂ e s') s ↔
      AnnealExactWP act p₁ e₁ s ∨ AnnealExactWP act p₂ e₂ s := by
  unfold AnnealExactWP
  cases act s <;> rfl

/-- Pure safety characterization: setting `onError := fun _ _ => False` holds iff `act s`
succeeds and satisfies `post`. -/
theorem exactWP_false_onError_iff_ok {S E A : Type} (act : ExactAction S E A)
    (post : A → S → Prop) (s : S) :
    AnnealExactWP act post (fun _ _ => False) s ↔
      ∃ a s', act s = .ok a s' ∧ post a s' := by
  unfold AnnealExactWP
  cases h : act s with
  | ok a s' =>
    constructor
    · intro hp; exact ⟨a, s', rfl, hp⟩
    · rintro ⟨_, _, hEq, hp⟩; cases hEq; exact hp
  | error e s' =>
    constructor
    · intro hf; exact False.elim hf
    · rintro ⟨_, _, hEq, _⟩; cases hEq

/-- **Bidirectional UB / error refutation**: failing the pure-safety VC (`¬ AnnealExactWP`)
is logically equivalent to exhibiting an actual `.error e s'` execution outcome! -/
theorem exactWP_negation_refutation {S E A : Type} (act : ExactAction S E A) (s : S) :
    (¬ AnnealExactWP act (fun _ _ => True) (fun _ _ => False) s) ↔
      ∃ e s', act s = .error e s' := by
  unfold AnnealExactWP
  cases h : act s with
  | ok a s' =>
    constructor
    · intro hNot; exact False.elim (hNot trivial)
    · rintro ⟨_, _, hEq⟩; cases hEq
  | error e s' =>
    constructor
    · intro _; exact ⟨e, s', rfl⟩
    · intro _ hf; exact hf

/-- Exact `EStateM` bridge (`↔`). -/
theorem exactWP_ofEStateM {S E A : Type} (m : EStateM E S A)
    (post : A → S → Prop) (onError : E → S → Prop) (s : S) :
    AnnealExactWP (ExactAction.ofEStateM m) post onError s ↔
      match m s with
      | .ok a s' => post a s'
      | .error e s' => onError e s' := by
  unfold AnnealExactWP ExactAction.ofEStateM
  cases m s <;> rfl

/-- Exact recursive weakest precondition for `ExactAction.foldl`. -/
def exactFoldWP {S E α β : Type} (step : β → α → ExactAction S E β)
    (post : β → S → Prop) (onError : E → S → Prop) : β → List α → S → Prop
  | acc, [], s => post acc s
  | acc, x :: xs, s =>
    AnnealExactWP (step acc x) (fun acc' s' => exactFoldWP step post onError acc' xs s') onError s

/-- Exact `↔` law for list folds (`exactWP_foldl`). -/
theorem exactWP_foldl {S E α β : Type} (step : β → α → ExactAction S E β)
    (post : β → S → Prop) (onError : E → S → Prop)
    (acc : β) (xs : List α) (s : S) :
    AnnealExactWP (ExactAction.foldl step acc xs) post onError s ↔
      exactFoldWP step post onError acc xs s := by
  induction xs generalizing acc s with
  | nil => rfl
  | cons x xs ih =>
    rw [ExactAction.foldl, exactWP_bind]
    unfold exactFoldWP
    unfold AnnealExactWP
    cases step acc x s with
    | ok acc' s' => exact ih acc' s'
    | error e s' => rfl

/-- Loop-invariant rule for `ExactAction.foldl`: if `Inv` holds initially and every element
step preserves `Inv` on success while establishing `onError` on failure, then `Inv` holds at
the end of the fold (and `onError` holds on any early abort). -/
theorem exactWP_foldl_invariant {S E α β : Type} (step : β → α → ExactAction S E β)
    (Inv : β → S → Prop) (onError : E → S → Prop)
    (hStep : ∀ acc x s, Inv acc s → AnnealExactWP (step acc x) Inv onError s)
    (acc : β) (xs : List α) (s : S) (hInit : Inv acc s) :
    AnnealExactWP (ExactAction.foldl step acc xs) Inv onError s := by
  rw [exactWP_foldl]
  induction xs generalizing acc s with
  | nil => exact hInit
  | cons x xs ih =>
    unfold exactFoldWP
    exact exactWP_consequence (fun acc' s' hInv => ih acc' s' hInv) (fun _ _ h => h)
      (hStep acc x s hInit)

/-- **Generic `TreeBorrowsFrameWP`**: exact two-continuation weakest precondition for
sequential Tree Borrows segment/location visits (`List Seg`) where each visit updates state `S`
and appends a diagnostic entry `D`, preserving ALL committed updates and visited diagnostics on
BOTH `.ok` and `.error`! -/
def treeBorrowsFrameAction {S E Seg D : Type}
    (visit : Seg → ExactAction S E D) (segs : List Seg) : ExactAction S E (List D) :=
  ExactAction.map List.reverse
    (ExactAction.foldl (fun acc seg => ExactAction.map (fun d => d :: acc) (visit seg)) [] segs)

def TreeBorrowsFrameWP {S E Seg D : Type}
    (visit : Seg → ExactAction S E D) (segs : List Seg)
    (post : List D → S → Prop) (onError : E → S → Prop) (s : S) : Prop :=
  exactFoldWP (fun acc seg => ExactAction.map (fun d => d :: acc) (visit seg))
    (fun acc s' => post acc.reverse s') onError [] segs s

theorem treeBorrowsFrameWP_iff {S E Seg D : Type}
    (visit : Seg → ExactAction S E D) (segs : List Seg)
    (post : List D → S → Prop) (onError : E → S → Prop) (s : S) :
    TreeBorrowsFrameWP visit segs post onError s ↔
      AnnealExactWP (treeBorrowsFrameAction visit segs) post onError s := by
  unfold TreeBorrowsFrameWP treeBorrowsFrameAction
  rw [exactWP_map, exactWP_foldl]

/-- Committed-prefix error guarantee on `TreeBorrowsFrameWP`: if segment `seg₁` succeeds
updating `s₀ ↦ s₁` and segment `seg₂` then fails producing `(e, s₂)` from `s₁`, then the
error continuation receives `(e, s₂)` (NOT the pre-state `s₀`!). -/
theorem treeBorrowsFrameWP_committed_prefix_on_error {S E Seg D : Type}
    (visit : Seg → ExactAction S E D) (seg₁ seg₂ : Seg) (rest : List Seg)
    (s₀ s₁ s₂ : S) (d₁ : D) (e : E)
    (h₁ : visit seg₁ s₀ = .ok d₁ s₁)
    (h₂ : visit seg₂ s₁ = .error e s₂)
    (post : List D → S → Prop) (onError : E → S → Prop) :
    TreeBorrowsFrameWP visit (seg₁ :: seg₂ :: rest) post onError s₀ ↔ onError e s₂ := by
  rw [treeBorrowsFrameWP_iff]
  dsimp only [treeBorrowsFrameAction, ExactAction.map, ExactAction.foldl, ExactAction.bind,
    ExactAction.pure, AnnealExactWP]
  rw [h₁]; dsimp only
  rw [h₂]

/-- **Generic `ProtectorReleaseWP`**: exact two-continuation WP for releasing a list of
protectors (`List P`) via per-protector `releaseOne` (retaining committed prefix updates on
error) followed by final global teardown `endCall`. -/
def protectorReleaseAction {S E P : Type}
    (releaseOne : P → ExactAction S E Unit) (endCall : ExactAction S E Unit)
    (prots : List P) : ExactAction S E Unit :=
  ExactAction.seq
    (ExactAction.foldl (fun _ p => releaseOne p) () prots)
    endCall

def ProtectorReleaseWP {S E P : Type}
    (releaseOne : P → ExactAction S E Unit) (endCall : ExactAction S E Unit)
    (prots : List P) (post : Unit → S → Prop) (onError : E → S → Prop) (s : S) : Prop :=
  exactFoldWP (fun _ p => releaseOne p)
    (fun _ s' => AnnealExactWP endCall post onError s') onError () prots s

theorem protectorReleaseWP_iff {S E P : Type}
    (releaseOne : P → ExactAction S E Unit) (endCall : ExactAction S E Unit)
    (prots : List P) (post : Unit → S → Prop) (onError : E → S → Prop) (s : S) :
    ProtectorReleaseWP releaseOne endCall prots post onError s ↔
      AnnealExactWP (protectorReleaseAction releaseOne endCall prots) post onError s := by
  unfold ProtectorReleaseWP protectorReleaseAction
  rw [exactWP_seq, exactWP_foldl]

/-- Committed-prefix error guarantee for `ProtectorReleaseWP`: when protector `p₁` succeeds
updating `s₀ ↦ s₁` and `p₂` fails with `(e, s₂)`, `endCall` does NOT run and `onError`
observes the committed post-`p₁` failure state `(e, s₂)`. -/
theorem protectorReleaseWP_error_preserves_prefix {S E P : Type}
    (releaseOne : P → ExactAction S E Unit) (endCall : ExactAction S E Unit)
    (p₁ p₂ : P) (rest : List P) (s₀ s₁ s₂ : S) (e : E)
    (h₁ : releaseOne p₁ s₀ = .ok () s₁)
    (h₂ : releaseOne p₂ s₁ = .error e s₂)
    (post : Unit → S → Prop) (onError : E → S → Prop) :
    ProtectorReleaseWP releaseOne endCall (p₁ :: p₂ :: rest) post onError s₀ ↔ onError e s₂ := by
  rw [protectorReleaseWP_iff]
  dsimp only [protectorReleaseAction, ExactAction.seq, ExactAction.foldl, ExactAction.bind,
    AnnealExactWP]
  rw [h₁]; dsimp only
  rw [h₂]

/-! ### Part A.2. Whole-Body `ExactBodySafetyVC` & Unmodified `Trusted.MirSemantics` Instantiations -/

/-- Exact error classification for lifting `Trusted.Rustc.V2026_06_01.MirSemantics` into `ExactAction`. -/
inductive MirStepErr : Type where
  | fail (fk : Trusted.Effect.FailureKind) : MirStepErr
  | extCall : MirStepErr
  | outOfFuel : MirStepErr
  deriving DecidableEq, Repr

/-- Lift one `MirStepNode` from pre-state `s` into `ExactOutcome MachineState MirStepErr (Option MirOutcome)`:
`.ok none s'` means `.running s'`, `.ok (some out) s` means `.halted out` at `s`, and
`.error err s` retains the exact pre-fault `MachineState`. -/
def liftMirStepNode (s : MachineState) :
    MirStepNode → ExactOutcome MachineState MirStepErr (Option MirOutcome)
  | .tau (.running s') => .ok none s'
  | .tau (.halted out) => .ok (some out) s
  | .tau (.faulted fk) => .error (.fail fk) s
  | .ret out => .ok (some out) s
  | .vis (.inl (.fail fk)) _ => .error (.fail fk) s
  | .vis (.inr _) _ => .error .extCall s

/-- Single-step `ExactAction` directly wrapping unmodified `Trusted.MirSemantics.stepMirFn`. -/
def mirStepAction (body : CapturedMir) :
    ExactAction MachineState MirStepErr (Option MirOutcome) :=
  fun s => liftMirStepNode s (stepMirFn body s)

/-- Fuel-bounded multi-step `ExactAction` directly iterating unmodified `stepMirFn`. -/
def mirRunFuelAction (body : CapturedMir) :
    Nat → ExactAction MachineState MirStepErr MirOutcome
  | 0, s => .error .outOfFuel s
  | fuel + 1, s =>
    match mirStepAction body s with
    | .ok none s' => mirRunFuelAction body fuel s'
    | .ok (some out) s' => .ok out s'
    | .error err s' => .error err s'

/-- **Whole-body exact safety VC** (`ExactBodySafetyVC`) for fuel-bounded execution of `body`. -/
def ExactBodySafetyVC (body : CapturedMir) :
    Nat → (MirOutcome → MachineState → Prop) → (MirStepErr → MachineState → Prop) →
      MachineState → Prop
  | 0, _, onError, s => onError .outOfFuel s
  | fuel + 1, post, onError, s =>
    AnnealExactWP (mirStepAction body)
      (fun optOut s' =>
        match optOut with
        | none => ExactBodySafetyVC body fuel post onError s'
        | some out => post out s')
      onError s

/-- Bidirectional exactness of `ExactBodySafetyVC` against `mirRunFuelAction` (`↔`). -/
theorem exactBodySafetyVC_iff (body : CapturedMir) (fuel : Nat)
    (post : MirOutcome → MachineState → Prop) (onError : MirStepErr → MachineState → Prop)
    (s : MachineState) :
    ExactBodySafetyVC body fuel post onError s ↔
      AnnealExactWP (mirRunFuelAction body fuel) post onError s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ n ih =>
    dsimp only [ExactBodySafetyVC, mirRunFuelAction, AnnealExactWP]
    cases mirStepAction body s with
    | ok optOut s' =>
      cases optOut with
      | none => exact ih s'
      | some out => rfl
    | error err s' => rfl

/-- Single-step unfolding law for `ExactBodySafetyVC`. -/
theorem exactBodySafetyVC_step (body : CapturedMir) (fuel : Nat)
    (post : MirOutcome → MachineState → Prop) (onError : MirStepErr → MachineState → Prop)
    (s : MachineState) :
    ExactBodySafetyVC body (fuel + 1) post onError s ↔
      AnnealExactWP (mirStepAction body)
        (fun optOut s' =>
          match optOut with
          | none => ExactBodySafetyVC body fuel post onError s'
          | some out => post out s')
        onError s :=
  Iff.rfl

/-- **Loop-invariant safety VC discharge**: if `Inv` holds at `s` and every single `stepMirFn`
from an `Inv` state preserves `Inv` on `.running`, establishes `post` on `.halted`, and
establishes `onError` on error (with `Inv s → onError .outOfFuel s` at fuel 0), then
`ExactBodySafetyVC body fuel post onError s` holds for EVERY `fuel : Nat`. -/
theorem exactBodySafetyVC_loop_invariant (body : CapturedMir)
    (Inv : MachineState → Prop)
    (post : MirOutcome → MachineState → Prop)
    (onError : MirStepErr → MachineState → Prop)
    (hStep : ∀ s, Inv s →
      AnnealExactWP (mirStepAction body)
        (fun optOut s' => match optOut with | none => Inv s' | some out => post out s')
        onError s)
    (hFuelZero : ∀ s, Inv s → onError .outOfFuel s)
    (fuel : Nat) (s : MachineState) (hInit : Inv s) :
    ExactBodySafetyVC body fuel post onError s := by
  induction fuel generalizing s with
  | zero => exact hFuelZero s hInit
  | succ n ih =>
    unfold ExactBodySafetyVC
    exact exactWP_consequence
      (fun optOut s' hPost => by
        cases optOut with
        | none => exact ih s' hPost
        | some out => exact hPost)
      (fun _ _ hErr => hErr)
      (hStep s hInit)

/-- Single-statement `ExactAction` directly wrapping unmodified `Trusted.MirSemantics.evalStmt`. -/
def evalStmtAction (stmt : Statement) (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    ExactAction MachineState MirStepErr (Option MirOutcome) :=
  fun s => liftMirStepNode s (evalStmt s stmt localDecls layouts)

theorem evalStmtExactWP_nop (span : String) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (post : Option MirOutcome → MachineState → Prop) (onError : MirStepErr → MachineState → Prop)
    (s : MachineState) :
    AnnealExactWP (evalStmtAction { kind := .nop, span := span } localDecls layouts) post onError s ↔
      post none (advanceStmt s s.frame.locals) :=
  Iff.rfl

/-- Single-terminator `ExactAction` directly wrapping unmodified `Trusted.MirSemantics.evalTerminator`. -/
def evalTerminatorAction (term : Terminator) (currentBody : Option CapturedMir := .none) :
    ExactAction MachineState MirStepErr (Option MirOutcome) :=
  fun s => liftMirStepNode s (evalTerminator s term currentBody)

theorem evalTerminatorExactWP_unreachable (span : String) (currentBody : Option CapturedMir)
    (post : Option MirOutcome → MachineState → Prop) (onError : MirStepErr → MachineState → Prop)
    (s : MachineState) :
    AnnealExactWP (evalTerminatorAction { kind := .unreachable, span := span } currentBody)
      post onError s ↔ onError (.fail .ub) s :=
  Iff.rfl

theorem evalTerminatorExactWP_unwindTerminate (span : String) (currentBody : Option CapturedMir)
    (post : Option MirOutcome → MachineState → Prop) (onError : MirStepErr → MachineState → Prop)
    (s : MachineState) :
    AnnealExactWP
      (evalTerminatorAction { kind := .unwindTerminate, span := span } currentBody)
      post onError s ↔ post (some .abort) s :=
  Iff.rfl

/-- Direct `ExactAction` wrapping unmodified `Trusted.MirSemantics.restoreCallerProtectors`. -/
def restoreCallerProtectorsAction (caller : SavedCallerFrame) :
    ExactAction MachineState MirStepErr Unit :=
  ExactAction.modify (fun s =>
    { s with memory := { s.memory with activeProtectors := restoreCallerProtectors caller } })

theorem restoreCallerProtectorsExactWP_iff (caller : SavedCallerFrame)
    (post : Unit → MachineState → Prop) (onError : MirStepErr → MachineState → Prop)
    (s : MachineState) :
    AnnealExactWP (restoreCallerProtectorsAction caller) post onError s ↔
      post () { s with memory := { s.memory with activeProtectors := restoreCallerProtectors caller } } :=
  Iff.rfl

/-- Direct `ExactAction` wrapping unmodified `Trusted.MirSemantics.disableFrameBorrows`. -/
def disableFrameBorrowsAction (depth nLocals : Nat) :
    ExactAction MachineState MirStepErr Unit :=
  ExactAction.modify (fun s =>
    { s with memory := { s.memory with borrows := disableFrameBorrows s.memory.borrows depth nLocals } })

theorem disableFrameBorrowsExactWP_iff (depth nLocals : Nat)
    (post : Unit → MachineState → Prop) (onError : MirStepErr → MachineState → Prop)
    (s : MachineState) :
    AnnealExactWP (disableFrameBorrowsAction depth nLocals) post onError s ↔
      post () { s with memory := { s.memory with borrows := disableFrameBorrows s.memory.borrows depth nLocals } } :=
  Iff.rfl

/-- Direct `ExactAction` combining unmodified `hasFrameDeallocProtectorConflict` with
`disableFrameBorrows`: faults with `.fail .ub` (retaining `s` unmodified) iff a protected
borrow targets the dying frame, and otherwise disables that frame's borrows. -/
def frameDeallocProtectorAction (depth nLocals : Nat) :
    ExactAction MachineState MirStepErr Unit := fun s =>
  if hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors depth nLocals then
    .error (.fail .ub) s
  else
    .ok () { s with memory := { s.memory with borrows := disableFrameBorrows s.memory.borrows depth nLocals } }

theorem frameDeallocProtectorExactWP_iff (depth nLocals : Nat)
    (post : Unit → MachineState → Prop) (onError : MirStepErr → MachineState → Prop)
    (s : MachineState) :
    AnnealExactWP (frameDeallocProtectorAction depth nLocals) post onError s ↔
      (hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors depth nLocals = true →
        onError (.fail .ub) s) ∧
      (hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors depth nLocals = false →
        post () { s with memory := { s.memory with borrows := disableFrameBorrows s.memory.borrows depth nLocals } }) := by
  unfold AnnealExactWP frameDeallocProtectorAction
  cases hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors depth nLocals <;>
    simp

/-! ### Part A.3. Non-Vacuous Concrete Whole-Body `ExactBodySafetyVC` Discharges \& Refutations on
Unmodified `Trusted.MirSemantics.stepMirFn` -/

/-- Zero-sized unit layout for the concrete Part A.3 `CapturedMir` bodies. -/
def exactVcUnitLayout : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }

/-- Single-block unit-returning `CapturedMir` body with statements `stmts` and terminator `term`. -/
def exactVcBody (stmts : List Statement) (term : TerminatorKind) : CapturedMir :=
  { defPath := "ep2::exact_vc", phase := .runtimePostCleanup, role := .subject, argCount := 0,
    localDecls := [{ mutability := .mut, ty := ⟨.tuple [], 0⟩, debugName := none }],
    basicBlocks := [{ statements := stmts, terminator := { kind := term, span := "ep2.rs" },
                      isCleanup := false }],
    fnAbi := { args := [], ret := { layout := exactVcUnitLayout, mode := .direct },
               conv := .rust, canUnwind := true },
    layouts := { pointerBits := 64, isLittleEndian := true, entries := [exactVcUnitLayout] },
    allocations := [] }

/-- `_0 = (); return` -/
def exactVcReturnBody : CapturedMir :=
  exactVcBody [{ kind := .assign { local_ := 0, projection := [] } (.aggregate .tuple []),
                 span := "ep2.rs" }] .return_

/-- `unreachable` -/
def exactVcUnreachableBody : CapturedMir := exactVcBody [] .unreachable

/-- `unwindTerminate` (process abort) -/
def exactVcAbortBody : CapturedMir := exactVcBody [] .unwindTerminate

/-- Boolean classification of a fuel-bounded `mirRunFuelAction` outcome. -/
def exactVcIsNormal : ExactOutcome MachineState MirStepErr MirOutcome → Bool
  | .ok (.normal _) _ => true
  | _ => false

/-- **Concrete non-vacuous whole-body `ExactBodySafetyVC` facts on REAL `stepMirFn` executions**:
1. `_0 = (); return` terminates normally within `4` steps, so `ExactBodySafetyVC` with the
   postcondition "normal return" and an UNSATISFIABLE error continuation (`False`) HOLDS;
2. `unreachable` faults with EXACTLY `.fail .ub` at the pre-state, so the safety VC with an
   unsatisfiable error continuation is REFUTED, while the exact error continuation
   `err = .fail .ub` holds;
3. `unwindTerminate` halts with `.abort` (never `.normal`), so the "normal return" VC is REFUTED. -/
theorem exactBodySafetyVC_concrete_trusted_bodies :
    let s0 := initMachineStateWithCallees exactVcReturnBody [] []
    let u0 := initMachineStateWithCallees exactVcUnreachableBody [] []
    let a0 := initMachineStateWithCallees exactVcAbortBody [] []
    exactVcIsNormal (mirRunFuelAction exactVcReturnBody 4 s0) = true ∧
    ExactBodySafetyVC exactVcReturnBody 4
      (fun out _ => exactVcIsNormal (.ok out s0) = true) (fun _ _ => False) s0 ∧
    mirRunFuelAction exactVcUnreachableBody 2 u0 = .error (.fail .ub) u0 ∧
    ExactBodySafetyVC exactVcUnreachableBody 2 (fun _ _ => True) (fun e _ => e = .fail .ub) u0 ∧
    ¬ ExactBodySafetyVC exactVcUnreachableBody 2 (fun _ _ => True) (fun _ _ => False) u0 ∧
    mirRunFuelAction exactVcAbortBody 2 a0 = .ok .abort a0 ∧
    ¬ ExactBodySafetyVC exactVcAbortBody 2
      (fun out _ => exactVcIsNormal (.ok out a0) = true) (fun _ _ => True) a0 := by
  intro s0 u0 a0
  have hRet : exactVcIsNormal (mirRunFuelAction exactVcReturnBody 4 s0) = true := by decide
  have hUb : mirRunFuelAction exactVcUnreachableBody 2 u0 = .error (.fail .ub) u0 := rfl
  have hAb : mirRunFuelAction exactVcAbortBody 2 a0 = .ok .abort a0 := rfl
  refine ⟨hRet, ?_, hUb, ?_, ?_, hAb, ?_⟩
  · rw [exactBodySafetyVC_iff]
    unfold AnnealExactWP
    revert hRet
    cases mirRunFuelAction exactVcReturnBody 4 s0 with
    | ok out s' =>
      cases out with
      | normal r => intro _; rfl
      | panic => intro h; cases h
      | abort => intro h; cases h
    | error e s' => intro h; cases h
  · rw [exactBodySafetyVC_iff, exactWP_of_eq_error hUb]
  · rw [exactBodySafetyVC_iff, exactWP_of_eq_error hUb]; exact id
  · rw [exactBodySafetyVC_iff, exactWP_of_eq_ok hAb]; intro h; cases h

end ExactWPAlgebra

/-! ## Part B. `Bitprism` (`cl/1029634110`) Kernel-Proved Smart Simplifying Constructors -/

section BitprismSmartCtors

/-! ### B.1. Exact Bitwise & Scalar Arithmetic Identities on Unmodified `Trusted.MirSemantics` -/

private theorem nat_add_eq (a b : Nat) : Nat.add a b = a + b := rfl
private theorem nat_sub_eq (a b : Nat) : Nat.sub a b = a - b := rfl
private theorem nat_mul_eq (a b : Nat) : Nat.mul a b = a * b := rfl
private theorem nat_div_eq (a b : Nat) : Nat.div a b = a / b := rfl
private theorem nat_mod_eq (a b : Nat) : Nat.mod a b = a % b := rfl

private theorem nat_mod_two_mul (a n : Nat) :
    a % (2 * n) = a % 2 + 2 * ((a / 2) % n) := by
  have h1 : a % (2 * n) = (a % (2 * n)) % 2 + 2 * ((a % (2 * n)) / 2) :=
    (Nat.mod_add_div (a % (2 * n)) 2).symm
  have h2 : (a % (2 * n)) % 2 = a % 2 := Nat.mod_mod_of_dvd a ⟨n, rfl⟩
  have h3 : (a % (2 * n)) / 2 = (a / 2) % n := Nat.mod_mul_right_div_self a 2 n
  rw [h2, h3] at h1
  exact h1

theorem scalarPow2_eq_two_pow (k : Nat) : scalarPow2 k = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [scalarPow2, nat_mul_eq, ih, Nat.pow_succ, Nat.mul_comm]

theorem scalarModulus_eq_two_pow (sz : Nat) : scalarModulus sz = 2 ^ (sz * 8) := by
  induction sz with
  | zero => rfl
  | succ k ih =>
    simp only [scalarModulus, nat_mul_eq, ih]
    have hExp : (k + 1) * 8 = k * 8 + 8 := by omega
    rw [hExp, Nat.pow_add]
    have h256 : 2 ^ 8 = 256 := by decide
    rw [h256, Nat.mul_comm]

theorem scalarModulus_pos (sz : Nat) : 0 < scalarModulus sz := by
  rw [scalarModulus_eq_two_pow]
  exact Nat.pow_pos (by decide)

theorem wrapScalarBits_eq_mod (a m : Nat) : wrapScalarBits a m = a % m := by
  unfold wrapScalarBits
  cases h : Nat.ble m a with
  | true => rfl
  | false =>
    have hLt : a < m := by
      have hNotLe : ¬ (m ≤ a) := by
        intro hLe
        have : Nat.ble m a = true := Nat.ble_eq.mpr hLe
        rw [this] at h; cases h
      omega
    exact (Nat.mod_eq_of_lt hLt).symm

theorem wrapScalarBits_of_lt {a m : Nat} (h : a < m) : wrapScalarBits a m = a := by
  rw [wrapScalarBits_eq_mod, Nat.mod_eq_of_lt h]

theorem bitwiseAndBits_zero_right (k a : Nat) : bitwiseAndBits k a 0 = 0 := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    simp only [bitwiseAndBits, nat_add_eq, nat_mul_eq, nat_div_eq, nat_mod_eq,
      Nat.zero_mod, Nat.zero_div, ih (a / 2)]
    have h01 : Nat.beq 0 1 = false := rfl
    simp [h01]

theorem bitwiseAndBits_zero_left (k b : Nat) : bitwiseAndBits k 0 b = 0 := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih =>
    simp only [bitwiseAndBits, nat_add_eq, nat_mul_eq, nat_div_eq, nat_mod_eq,
      Nat.zero_mod, Nat.zero_div, ih (b / 2)]
    have h01 : Nat.beq 0 1 = false := rfl
    simp [h01]

theorem bitwiseAndBits_self (k a : Nat) : bitwiseAndBits k a a = a % 2 ^ k := by
  induction k generalizing a with
  | zero => simp [bitwiseAndBits, Nat.mod_one]
  | succ k ih =>
    simp only [bitwiseAndBits, nat_add_eq, nat_mul_eq, nat_div_eq, nat_mod_eq, ih (a / 2)]
    have hMod2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
    have hPow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hPow, nat_mod_two_mul]
    rcases hMod2 with h0 | h1
    · rw [h0]; rfl
    · rw [h1]; rfl

theorem bitwiseAndBits_allOnes_right (k a : Nat) :
    bitwiseAndBits k a (2 ^ k - 1) = a % 2 ^ k := by
  induction k generalizing a with
  | zero => simp [bitwiseAndBits, Nat.mod_one]
  | succ k ih =>
    have hPos : 0 < 2 ^ k := Nat.pow_pos (by decide)
    have hPow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hOdd : (2 ^ (k + 1) - 1) % 2 = 1 := by omega
    have hDiv : (2 ^ (k + 1) - 1) / 2 = 2 ^ k - 1 := by omega
    simp only [bitwiseAndBits, nat_add_eq, nat_mul_eq, nat_div_eq, nat_mod_eq,
      hOdd, hDiv, ih (a / 2)]
    have hMod2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
    rw [hPow, nat_mod_two_mul]
    rcases hMod2 with h0 | h1
    · rw [h0]; rfl
    · rw [h1]; rfl

theorem bitwiseAndBits_allOnes_left (k b : Nat) :
    bitwiseAndBits k (2 ^ k - 1) b = b % 2 ^ k := by
  induction k generalizing b with
  | zero => simp [bitwiseAndBits, Nat.mod_one]
  | succ k ih =>
    have hPos : 0 < 2 ^ k := Nat.pow_pos (by decide)
    have hPow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hOdd : (2 ^ (k + 1) - 1) % 2 = 1 := by omega
    have hDiv : (2 ^ (k + 1) - 1) / 2 = 2 ^ k - 1 := by omega
    simp only [bitwiseAndBits, nat_add_eq, nat_mul_eq, nat_div_eq, nat_mod_eq,
      hOdd, hDiv, ih (b / 2)]
    have hMod2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
    rw [hPow, nat_mod_two_mul]
    rcases hMod2 with h0 | h1
    · rw [h0]; rfl
    · rw [h1]; rfl

theorem bitwiseOrBits_zero_right (k a : Nat) : bitwiseOrBits k a 0 = a % 2 ^ k := by
  induction k generalizing a with
  | zero => simp [bitwiseOrBits, Nat.mod_one]
  | succ k ih =>
    simp only [bitwiseOrBits, nat_add_eq, nat_mul_eq, nat_div_eq, nat_mod_eq,
      Nat.zero_mod, Nat.zero_div, ih (a / 2)]
    have hMod2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
    have hPow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hPow, nat_mod_two_mul]
    rcases hMod2 with h0 | h1
    · rw [h0]; rfl
    · rw [h1]; rfl

theorem bitwiseOrBits_zero_left (k b : Nat) : bitwiseOrBits k 0 b = b % 2 ^ k := by
  induction k generalizing b with
  | zero => simp [bitwiseOrBits, Nat.mod_one]
  | succ k ih =>
    simp only [bitwiseOrBits, nat_add_eq, nat_mul_eq, nat_div_eq, nat_mod_eq,
      Nat.zero_mod, Nat.zero_div, ih (b / 2)]
    have hMod2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
    have hPow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hPow, nat_mod_two_mul]
    rcases hMod2 with h0 | h1
    · rw [h0]; rfl
    · rw [h1]; rfl

theorem bitwiseOrBits_self (k a : Nat) : bitwiseOrBits k a a = a % 2 ^ k := by
  induction k generalizing a with
  | zero => simp [bitwiseOrBits, Nat.mod_one]
  | succ k ih =>
    simp only [bitwiseOrBits, nat_add_eq, nat_mul_eq, nat_div_eq, nat_mod_eq, ih (a / 2)]
    have hMod2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
    have hPow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hPow, nat_mod_two_mul]
    rcases hMod2 with h0 | h1
    · rw [h0]; rfl
    · rw [h1]; rfl

theorem bitwiseOrBits_allOnes_right (k a : Nat) :
    bitwiseOrBits k a (2 ^ k - 1) = 2 ^ k - 1 := by
  induction k generalizing a with
  | zero => simp [bitwiseOrBits]
  | succ k ih =>
    have hPos : 0 < 2 ^ k := Nat.pow_pos (by decide)
    have hPow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hOdd : (2 ^ (k + 1) - 1) % 2 = 1 := by omega
    have hDiv : (2 ^ (k + 1) - 1) / 2 = 2 ^ k - 1 := by omega
    simp only [bitwiseOrBits, nat_add_eq, nat_mul_eq, nat_div_eq, nat_mod_eq,
      hOdd, hDiv, ih (a / 2)]
    have hMod2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
    rcases hMod2 with h0 | h1
    · rw [h0]; change 1 + 2 * (2 ^ k - 1) = 2 ^ (k + 1) - 1; omega
    · rw [h1]; change 1 + 2 * (2 ^ k - 1) = 2 ^ (k + 1) - 1; omega

theorem bitwiseOrBits_allOnes_left (k b : Nat) :
    bitwiseOrBits k (2 ^ k - 1) b = 2 ^ k - 1 := by
  induction k generalizing b with
  | zero => simp [bitwiseOrBits]
  | succ k ih =>
    have hPos : 0 < 2 ^ k := Nat.pow_pos (by decide)
    have hPow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hOdd : (2 ^ (k + 1) - 1) % 2 = 1 := by omega
    have hDiv : (2 ^ (k + 1) - 1) / 2 = 2 ^ k - 1 := by omega
    simp only [bitwiseOrBits, nat_add_eq, nat_mul_eq, nat_div_eq, nat_mod_eq,
      hOdd, hDiv, ih (b / 2)]
    have hMod2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
    rcases hMod2 with h0 | h1
    · rw [h0]; change 1 + 2 * (2 ^ k - 1) = 2 ^ (k + 1) - 1; omega
    · rw [h1]; change 1 + 2 * (2 ^ k - 1) = 2 ^ (k + 1) - 1; omega

theorem bitwiseXorBits_zero_right (k a : Nat) : bitwiseXorBits k a 0 = a % 2 ^ k := by
  induction k generalizing a with
  | zero => simp [bitwiseXorBits, Nat.mod_one]
  | succ k ih =>
    simp only [bitwiseXorBits, nat_add_eq, nat_mul_eq, nat_div_eq, nat_mod_eq,
      Nat.zero_mod, Nat.zero_div, ih (a / 2)]
    have hMod2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
    have hPow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hPow, nat_mod_two_mul]
    rcases hMod2 with h0 | h1
    · rw [h0]
    · rw [h1]

theorem bitwiseXorBits_zero_left (k b : Nat) : bitwiseXorBits k 0 b = b % 2 ^ k := by
  induction k generalizing b with
  | zero => simp [bitwiseXorBits, Nat.mod_one]
  | succ k ih =>
    simp only [bitwiseXorBits, nat_add_eq, nat_mul_eq, nat_div_eq, nat_mod_eq,
      Nat.zero_mod, Nat.zero_div, ih (b / 2)]
    have hMod2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
    have hPow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hPow, nat_mod_two_mul]
    rcases hMod2 with h0 | h1
    · rw [h0]
    · rw [h1]

theorem bitwiseXorBits_self (k a : Nat) : bitwiseXorBits k a a = 0 := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    simp only [bitwiseXorBits, nat_add_eq, nat_mul_eq, nat_div_eq, nat_mod_eq, ih (a / 2)]
    have hMod2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
    rcases hMod2 with h0 | h1
    · rw [h0]
    · rw [h1]

/-! ### B.2. Level 1 — Scalar & Pointer Semantic Smart Simplifying Constructors (`SmartExpr`) -/

/-- Canonical all-ones mask `2^(8 * sz) - 1` for a scalar of byte width `sz`. -/
def allOnesMask (sz : Nat) : Nat := scalarModulus sz - 1

/-- Pure symbolic scalar expression AST parameterized by byte width `sz`, enabling `O(1)`
algebraic collapse at construction time (`Bitprism` cl/1029634110 pattern) while keeping all raw
`MirAst` / `MirSemantics` constructors completely untouched. -/
inductive SmartScalarExpr (sz : Nat) : Type where
  | const (bits : Nat) : SmartScalarExpr sz
  | var (id : Nat) : SmartScalarExpr sz
  | bin (op : BinOp) (lhs rhs : SmartScalarExpr sz) : SmartScalarExpr sz

private def binOpTag : BinOp → Nat
  | .add => 0 | .addUnchecked => 1 | .addWithOverflow => 2
  | .sub => 3 | .subUnchecked => 4 | .subWithOverflow => 5
  | .mul => 6 | .mulUnchecked => 7 | .mulWithOverflow => 8
  | .div => 9 | .rem => 10
  | .bitXor => 11 | .bitAnd => 12 | .bitOr => 13
  | .shl => 14 | .shlUnchecked => 15
  | .shr => 16 | .shrUnchecked => 17
  | .eq => 18 | .lt => 19 | .le => 20 | .ne => 21 | .ge => 22 | .gt => 23
  | .cmp => 24 | .offset => 25

private theorem binOpTag_inj {a b : BinOp} (h : binOpTag a = binOpTag b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact False.elim (by cases h)

/-- Structural equality predicate on `SmartScalarExpr sz`. -/
def SmartScalarExpr.beq {sz : Nat} : SmartScalarExpr sz → SmartScalarExpr sz → Bool
  | .const a, .const b => a == b
  | .var a, .var b => a == b
  | .bin op1 l1 r1, .bin op2 l2 r2 =>
    (binOpTag op1 == binOpTag op2) && l1.beq l2 && r1.beq r2
  | _, _ => false

instance {sz : Nat} : BEq (SmartScalarExpr sz) where
  beq := SmartScalarExpr.beq

private theorem smartScalarExpr_beq_refl {sz : Nat} (e : SmartScalarExpr sz) :
    e.beq e = true := by
  induction e with
  | const a => exact beq_self_eq_true a
  | var id => exact beq_self_eq_true id
  | bin op l r ihl ihr =>
    simp only [SmartScalarExpr.beq, beq_self_eq_true, ihl, ihr, Bool.and_true]

private theorem smartScalarExpr_eq_of_beq {sz : Nat} :
    ∀ {a b : SmartScalarExpr sz}, a.beq b = true → a = b
  | .const a, .const b, h => congrArg SmartScalarExpr.const (beq_iff_eq.mp h)
  | .var a, .var b, h => congrArg SmartScalarExpr.var (beq_iff_eq.mp h)
  | .bin op1 l1 r1, .bin op2 l2 r2, h => by
    simp only [SmartScalarExpr.beq, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hOp, hL⟩, hR⟩ := h
    rw [binOpTag_inj hOp, smartScalarExpr_eq_of_beq hL, smartScalarExpr_eq_of_beq hR]
  | .const _, .var _, h | .const _, .bin _ _ _, h
  | .var _, .const _, h | .var _, .bin _ _ _, h
  | .bin _ _ _, .const _, h | .bin _ _ _, .var _, h => Bool.noConfusion h

instance {sz : Nat} : LawfulBEq (SmartScalarExpr sz) where
  eq_of_beq := smartScalarExpr_eq_of_beq
  rfl := smartScalarExpr_beq_refl _

/-- Exact denotational evaluator delegating EVERY binary operator directly to unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.evalScalarBinOp` (unsigned mode, canonical `sz`-byte
scalars). -/
def SmartScalarExpr.eval {sz : Nat} (env : Nat → Nat) : SmartScalarExpr sz → Nat
  | .const b => wrapScalarBits b (scalarModulus sz)
  | .var id => wrapScalarBits (env id) (scalarModulus sz)
  | .bin op lhs rhs =>
    match evalScalarBinOp op ⟨lhs.eval env, sz⟩ ⟨rhs.eval env, sz⟩ [] emptyMemory false with
    | .ok (.scalar sc) _ _ => sc.bits
    | _ => 0

/-- Canonical constant smart-constructor helper. -/
def mkConstSmart {sz : Nat} (b : Nat) : SmartScalarExpr sz :=
  .const (wrapScalarBits b (scalarModulus sz))

/-- Smart simplifying constructor for wrapping addition (`BinOp.add`):
constant folds, eliminates `x + 0` and `0 + x` in `O(1)`. -/
def mkAddSmart {sz : Nat} (lhs rhs : SmartScalarExpr sz) : SmartScalarExpr sz :=
  match lhs, rhs with
  | .const a, .const b => mkConstSmart (a + b)
  | .const 0, r => r
  | l, .const 0 => l
  | l, r => .bin .add l r

/-- Smart simplifying constructor for wrapping subtraction (`BinOp.sub`):
constant folds, eliminates `x - 0` and `x - x = 0` in `O(1)`. -/
def mkSubSmart {sz : Nat} (lhs rhs : SmartScalarExpr sz) : SmartScalarExpr sz :=
  if lhs == rhs then .const 0
  else match lhs, rhs with
  | .const a, .const b =>
    let m := scalarModulus sz
    let ca := wrapScalarBits a m
    let cb := wrapScalarBits b m
    if cb ≤ ca then mkConstSmart (ca - cb)
    else mkConstSmart (m + ca - cb)
  | l, .const 0 => l
  | l, r => .bin .sub l r

/-- Smart simplifying constructor for wrapping multiplication (`BinOp.mul`):
constant folds, absorbs `0`, eliminates `1` in `O(1)`. -/
def mkMulSmart {sz : Nat} (lhs rhs : SmartScalarExpr sz) : SmartScalarExpr sz :=
  match lhs, rhs with
  | .const a, .const b => mkConstSmart (a * b)
  | .const 0, _ | _, .const 0 => .const 0
  | .const 1, r => r
  | l, .const 1 => l
  | l, r => .bin .mul l r

/-- Smart simplifying constructor for bitwise AND (`BinOp.bitAnd`):
constant folds, absorbs `0`, eliminates `allOnesMask sz`, collapses `x & x = x`. -/
def mkBitAndSmart {sz : Nat} (lhs rhs : SmartScalarExpr sz) : SmartScalarExpr sz :=
  if lhs == rhs then lhs
  else match lhs with
  | .const a =>
    match rhs with
    | .const b => mkConstSmart (bitwiseAndBits (sz * 8) a b)
    | r =>
      match a with
      | 0 => .const 0
      | a' + 1 => if a' + 1 == allOnesMask sz then r else .bin .bitAnd (.const (a' + 1)) r
  | l =>
    match rhs with
    | .const 0 => .const 0
    | .const (b' + 1) => if b' + 1 == allOnesMask sz then l else .bin .bitAnd l (.const (b' + 1))
    | r => .bin .bitAnd l r

/-- Smart simplifying constructor for bitwise OR (`BinOp.bitOr`):
constant folds, absorbs `allOnesMask sz`, eliminates `0`, collapses `x | x = x`. -/
def mkBitOrSmart {sz : Nat} (lhs rhs : SmartScalarExpr sz) : SmartScalarExpr sz :=
  if lhs == rhs then lhs
  else match lhs with
  | .const a =>
    match rhs with
    | .const b => mkConstSmart (bitwiseOrBits (sz * 8) a b)
    | r =>
      match a with
      | 0 => r
      | a' + 1 =>
        if a' + 1 == allOnesMask sz then .const (allOnesMask sz)
        else .bin .bitOr (.const (a' + 1)) r
  | l =>
    match rhs with
    | .const 0 => l
    | .const (b' + 1) =>
      if b' + 1 == allOnesMask sz then .const (allOnesMask sz)
      else .bin .bitOr l (.const (b' + 1))
    | r => .bin .bitOr l r

/-- Smart simplifying constructor for bitwise XOR (`BinOp.bitXor`):
constant folds, eliminates `0`, collapses `x ^ x = 0`. -/
def mkBitXorSmart {sz : Nat} (lhs rhs : SmartScalarExpr sz) : SmartScalarExpr sz :=
  if lhs == rhs then .const 0
  else match lhs with
  | .const a =>
    match rhs with
    | .const b => mkConstSmart (bitwiseXorBits (sz * 8) a b)
    | r =>
      match a with
      | 0 => r
      | a' + 1 => .bin .bitXor (.const (a' + 1)) r
  | l =>
    match rhs with
    | .const 0 => l
    | r => .bin .bitXor l r

/-- Smart simplifying constructor for masked left shift (`BinOp.shl`):
constant folds, eliminates shift by `0` (or multiple of `sz * 8`), absorbs `0 << k = 0`. -/
def mkShlSmart {sz : Nat} (lhs rhs : SmartScalarExpr sz) : SmartScalarExpr sz :=
  match lhs, rhs with
  | .const a, .const b =>
    if sz == 0 then .bin .shl (.const a) (.const b)
    else mkConstSmart (shiftLeftBits (wrapScalarBits a (scalarModulus sz))
      (wrapScalarBits b (scalarModulus sz) % (sz * 8)) (scalarModulus sz))
  | .const 0, _ => .const 0
  | l, .const b =>
    if sz != 0 && wrapScalarBits b (scalarModulus sz) % (sz * 8) == 0 then l
    else .bin .shl l (.const b)
  | l, r => .bin .shl l r

/-- Smart simplifying constructor for unsigned masked right shift (`BinOp.shr`):
constant folds, eliminates shift by `0` (or multiple of `sz * 8`), absorbs `0 >> k = 0`. -/
def mkShrSmart {sz : Nat} (lhs rhs : SmartScalarExpr sz) : SmartScalarExpr sz :=
  match lhs, rhs with
  | .const a, .const b =>
    if sz == 0 then .bin .shr (.const a) (.const b)
    else mkConstSmart (shiftRightUnsignedBits (wrapScalarBits a (scalarModulus sz))
      (wrapScalarBits b (scalarModulus sz) % (sz * 8)))
  | .const 0, _ => .const 0
  | l, .const b =>
    if sz != 0 && wrapScalarBits b (scalarModulus sz) % (sz * 8) == 0 then l
    else .bin .shr l (.const b)
  | l, r => .bin .shr l r

/-- Canonical-range predicate for a `SmartScalarExpr` evaluation (holds for every expression built
from constants, variables, and the 8 wrapping/bitwise/shift operators). -/
def SmartScalarExpr.evalLt {sz : Nat} (env : Nat → Nat) (e : SmartScalarExpr sz) : Prop :=
  e.eval env < scalarModulus sz

private theorem nat_beq_zero_false {sz : Nat} (hSz : sz ≠ 0) : Nat.beq sz 0 = false := by
  cases sz with
  | zero => exact False.elim (hSz rfl)
  | succ _ => rfl

private theorem eval_bin_eq {sz : Nat} (env : Nat → Nat) (op : BinOp) (l r : SmartScalarExpr sz) :
    (SmartScalarExpr.bin op l r).eval env =
      match evalScalarBinOp op ⟨l.eval env, sz⟩ ⟨r.eval env, sz⟩ [] emptyMemory false with
      | .ok (.scalar sc) _ _ => sc.bits
      | _ => 0 := rfl

private theorem eval_const_eq {sz : Nat} (env : Nat → Nat) (b : Nat) :
    (SmartScalarExpr.const (sz := sz) b).eval env = b % scalarModulus sz :=
  wrapScalarBits_eq_mod b (scalarModulus sz)

/-- Exact equivalence `mkAddSmart_eq_raw` against unmodified `Trusted.MirSemantics.evalScalarBinOp`. -/
theorem mkAddSmart_eq_raw {sz : Nat} (hSz : sz ≠ 0) (env : Nat → Nat)
    (lhs rhs : SmartScalarExpr sz)
    (hL : lhs.evalLt env) (hR : rhs.evalLt env) :
    (mkAddSmart lhs rhs).eval env = (SmartScalarExpr.bin .add lhs rhs).eval env := by
  have hNz := nat_beq_zero_false hSz
  unfold SmartScalarExpr.evalLt at hL hR
  cases lhs with
  | const a =>
    cases rhs with
    | const b =>
      dsimp only [mkAddSmart]
      rw [eval_bin_eq]
      simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_add_eq,
        mkConstSmart, eval_const_eq, wrapScalarBits_eq_mod, Nat.mod_mod]
      rw [Nat.add_mod]
    | var _ | bin _ _ _ =>
      cases a with
      | zero =>
        dsimp only [mkAddSmart]
        rw [eval_bin_eq]
        simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_add_eq,
          eval_const_eq, wrapScalarBits_eq_mod, Nat.zero_mod, Nat.zero_add]
        exact (Nat.mod_eq_of_lt hR).symm
      | succ _ => rfl
  | var _ | bin _ _ _ =>
    cases rhs with
    | const b =>
      cases b with
      | zero =>
        dsimp only [mkAddSmart]
        rw [eval_bin_eq]
        simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_add_eq,
          eval_const_eq, wrapScalarBits_eq_mod, Nat.zero_mod, Nat.add_zero]
        exact (Nat.mod_eq_of_lt hL).symm
      | succ _ => rfl
    | var _ | bin _ _ _ => rfl

/-- Exact equivalence `mkSubSmart_eq_raw` against unmodified `Trusted.MirSemantics.evalScalarBinOp`. -/
theorem mkSubSmart_eq_raw {sz : Nat} (hSz : sz ≠ 0) (env : Nat → Nat)
    (lhs rhs : SmartScalarExpr sz) (hL : lhs.evalLt env) :
    (mkSubSmart lhs rhs).eval env = (SmartScalarExpr.bin .sub lhs rhs).eval env := by
  have hNz := nat_beq_zero_false hSz
  unfold SmartScalarExpr.evalLt at hL
  unfold mkSubSmart
  split
  · rename_i hEq
    have hEq' : lhs = rhs := beq_iff_eq.mp hEq
    subst hEq'
    rw [eval_bin_eq]
    have hBleSelf : Nat.ble (lhs.eval env) (lhs.eval env) = true := Nat.ble_eq.mpr (Nat.le_refl _)
    simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_sub_eq,
      eval_const_eq, hBleSelf, Nat.sub_self, wrapScalarBits_eq_mod, Nat.zero_mod]
  · cases lhs with
    | const a =>
      cases rhs with
      | const b =>
        dsimp only
        rw [eval_bin_eq]
        simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_add_eq, nat_sub_eq]
        by_cases hLe : wrapScalarBits b (scalarModulus sz) ≤ wrapScalarBits a (scalarModulus sz)
        · have hLe' : b % scalarModulus sz ≤ a % scalarModulus sz := by
            simpa only [wrapScalarBits_eq_mod] using hLe
          have hBle : Nat.ble (b % scalarModulus sz) (a % scalarModulus sz) = true :=
            Nat.ble_eq.mpr hLe'
          simp only [mkConstSmart, wrapScalarBits_eq_mod, hLe', ↓reduceIte, eval_const_eq, hBle,
            Nat.mod_mod]
        · have hLe' : ¬ (b % scalarModulus sz ≤ a % scalarModulus sz) := by
            simpa only [wrapScalarBits_eq_mod] using hLe
          have hBle : Nat.ble (b % scalarModulus sz) (a % scalarModulus sz) = false := by
            cases hb : Nat.ble (b % scalarModulus sz) (a % scalarModulus sz) with
            | false => rfl
            | true => exact False.elim (hLe' (Nat.ble_eq.mp hb))
          simp only [mkConstSmart, wrapScalarBits_eq_mod, hLe', ↓reduceIte, eval_const_eq, hBle,
            Nat.mod_mod]
      | var _ | bin _ _ _ => rfl
    | var _ | bin _ _ _ =>
      cases rhs with
      | const b =>
        cases b with
        | zero =>
          dsimp only
          rw [eval_bin_eq]
          have hBle0 : ∀ n, Nat.ble 0 n = true := fun n => Nat.ble_eq.mpr (Nat.zero_le n)
          simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_sub_eq,
            eval_const_eq, Nat.zero_mod, hBle0, Nat.sub_zero, wrapScalarBits_eq_mod]
          exact (Nat.mod_eq_of_lt hL).symm
        | succ _ => rfl
      | var _ | bin _ _ _ => rfl

/-- Exact equivalence `mkMulSmart_eq_raw` against unmodified `Trusted.MirSemantics.evalScalarBinOp`. -/
theorem mkMulSmart_eq_raw {sz : Nat} (hSz : sz ≠ 0) (env : Nat → Nat)
    (lhs rhs : SmartScalarExpr sz)
    (hL : lhs.evalLt env) (hR : rhs.evalLt env) :
    (mkMulSmart lhs rhs).eval env = (SmartScalarExpr.bin .mul lhs rhs).eval env := by
  have hNz := nat_beq_zero_false hSz
  have hModGt1 : 1 < scalarModulus sz := by
    rw [scalarModulus_eq_two_pow]
    cases sz with
    | zero => exact False.elim (hSz rfl)
    | succ k =>
      have : 2 ^ 8 ≤ 2 ^ ((k + 1) * 8) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  unfold SmartScalarExpr.evalLt at hL hR
  cases lhs with
  | const a =>
    cases rhs with
    | const b =>
      dsimp only [mkMulSmart]
      rw [eval_bin_eq]
      simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq,
        mkConstSmart, eval_const_eq, wrapScalarBits_eq_mod, Nat.mod_mod]
      rw [Nat.mul_mod]
    | var _ | bin _ _ _ =>
      cases a with
      | zero =>
        dsimp only [mkMulSmart]
        rw [eval_bin_eq]
        simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq,
          eval_const_eq, wrapScalarBits_eq_mod, Nat.zero_mod, Nat.zero_mul]
      | succ a' =>
        cases a' with
        | zero =>
          dsimp only [mkMulSmart]
          rw [eval_bin_eq]
          simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq,
            eval_const_eq, wrapScalarBits_eq_mod, Nat.mod_eq_of_lt hModGt1, Nat.one_mul]
          exact (Nat.mod_eq_of_lt hR).symm
        | succ _ => rfl
  | var _ | bin _ _ _ =>
    cases rhs with
    | const b =>
      cases b with
      | zero =>
        dsimp only [mkMulSmart]
        rw [eval_bin_eq]
        simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq,
          eval_const_eq, wrapScalarBits_eq_mod, Nat.zero_mod, Nat.mul_zero]
      | succ b' =>
        cases b' with
        | zero =>
          dsimp only [mkMulSmart]
          rw [eval_bin_eq]
          simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq,
            eval_const_eq, wrapScalarBits_eq_mod, Nat.mod_eq_of_lt hModGt1, Nat.mul_one]
          exact (Nat.mod_eq_of_lt hL).symm
        | succ _ => rfl
    | var _ | bin _ _ _ => rfl

private theorem bitwiseAndBits_mod_left (k a b : Nat) :
    bitwiseAndBits k (a % 2 ^ k) b = bitwiseAndBits k a b := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih =>
    have hPow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hMod2 : (a % (2 * 2 ^ k)) % 2 = a % 2 := Nat.mod_mod_of_dvd a ⟨2 ^ k, rfl⟩
    have hDiv2 : (a % (2 * 2 ^ k)) / 2 = (a / 2) % 2 ^ k := Nat.mod_mul_right_div_self a 2 (2 ^ k)
    simp only [bitwiseAndBits, nat_add_eq, nat_mul_eq, nat_div_eq, nat_mod_eq, hPow, hMod2, hDiv2, ih]

private theorem bitwiseAndBits_mod_right (k a b : Nat) :
    bitwiseAndBits k a (b % 2 ^ k) = bitwiseAndBits k a b := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih =>
    have hPow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hMod2 : (b % (2 * 2 ^ k)) % 2 = b % 2 := Nat.mod_mod_of_dvd b ⟨2 ^ k, rfl⟩
    have hDiv2 : (b % (2 * 2 ^ k)) / 2 = (b / 2) % 2 ^ k := Nat.mod_mul_right_div_self b 2 (2 ^ k)
    simp only [bitwiseAndBits, nat_add_eq, nat_mul_eq, nat_div_eq, nat_mod_eq, hPow, hMod2, hDiv2, ih]

private theorem bitwiseOrBits_mod_left (k a b : Nat) :
    bitwiseOrBits k (a % 2 ^ k) b = bitwiseOrBits k a b := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih =>
    have hPow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hMod2 : (a % (2 * 2 ^ k)) % 2 = a % 2 := Nat.mod_mod_of_dvd a ⟨2 ^ k, rfl⟩
    have hDiv2 : (a % (2 * 2 ^ k)) / 2 = (a / 2) % 2 ^ k := Nat.mod_mul_right_div_self a 2 (2 ^ k)
    simp only [bitwiseOrBits, nat_add_eq, nat_mul_eq, nat_div_eq, nat_mod_eq, hPow, hMod2, hDiv2, ih]

private theorem bitwiseOrBits_mod_right (k a b : Nat) :
    bitwiseOrBits k a (b % 2 ^ k) = bitwiseOrBits k a b := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih =>
    have hPow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hMod2 : (b % (2 * 2 ^ k)) % 2 = b % 2 := Nat.mod_mod_of_dvd b ⟨2 ^ k, rfl⟩
    have hDiv2 : (b % (2 * 2 ^ k)) / 2 = (b / 2) % 2 ^ k := Nat.mod_mul_right_div_self b 2 (2 ^ k)
    simp only [bitwiseOrBits, nat_add_eq, nat_mul_eq, nat_div_eq, nat_mod_eq, hPow, hMod2, hDiv2, ih]

private theorem bitwiseXorBits_mod_left (k a b : Nat) :
    bitwiseXorBits k (a % 2 ^ k) b = bitwiseXorBits k a b := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih =>
    have hPow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hMod2 : (a % (2 * 2 ^ k)) % 2 = a % 2 := Nat.mod_mod_of_dvd a ⟨2 ^ k, rfl⟩
    have hDiv2 : (a % (2 * 2 ^ k)) / 2 = (a / 2) % 2 ^ k := Nat.mod_mul_right_div_self a 2 (2 ^ k)
    simp only [bitwiseXorBits, nat_add_eq, nat_mul_eq, nat_div_eq, nat_mod_eq, hPow, hMod2, hDiv2, ih]

private theorem bitwiseXorBits_mod_right (k a b : Nat) :
    bitwiseXorBits k a (b % 2 ^ k) = bitwiseXorBits k a b := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih =>
    have hPow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hMod2 : (b % (2 * 2 ^ k)) % 2 = b % 2 := Nat.mod_mod_of_dvd b ⟨2 ^ k, rfl⟩
    have hDiv2 : (b % (2 * 2 ^ k)) / 2 = (b / 2) % 2 ^ k := Nat.mod_mul_right_div_self b 2 (2 ^ k)
    simp only [bitwiseXorBits, nat_add_eq, nat_mul_eq, nat_div_eq, nat_mod_eq, hPow, hMod2, hDiv2, ih]

private theorem bitwiseAndBits_lt (k a b : Nat) : bitwiseAndBits k a b < 2 ^ k := by
  induction k generalizing a b with
  | zero => simp [bitwiseAndBits]
  | succ k ih =>
    have hPow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hRec := ih (a / 2) (b / 2)
    simp only [bitwiseAndBits, nat_add_eq, nat_mul_eq, nat_div_eq, nat_mod_eq]
    cases Bool.and (Nat.beq (a % 2) 1) (Nat.beq (b % 2) 1) <;> dsimp only <;> omega

private theorem bitwiseOrBits_lt (k a b : Nat) : bitwiseOrBits k a b < 2 ^ k := by
  induction k generalizing a b with
  | zero => simp [bitwiseOrBits]
  | succ k ih =>
    have hPow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hRec := ih (a / 2) (b / 2)
    simp only [bitwiseOrBits, nat_add_eq, nat_mul_eq, nat_div_eq, nat_mod_eq]
    cases Bool.or (Nat.beq (a % 2) 1) (Nat.beq (b % 2) 1) <;> dsimp only <;> omega

private theorem bitwiseXorBits_lt (k a b : Nat) : bitwiseXorBits k a b < 2 ^ k := by
  induction k generalizing a b with
  | zero => simp [bitwiseXorBits]
  | succ k ih =>
    have hPow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hRec := ih (a / 2) (b / 2)
    simp only [bitwiseXorBits, nat_add_eq, nat_mul_eq, nat_div_eq, nat_mod_eq]
    cases Nat.beq (a % 2) (b % 2) <;> dsimp only <;> omega

/-- Exact equivalence `mkBitAndSmart_eq_raw` against unmodified `evalScalarBinOp`. -/
theorem mkBitAndSmart_eq_raw {sz : Nat} (hSz : sz ≠ 0) (env : Nat → Nat)
    (lhs rhs : SmartScalarExpr sz) (hL : lhs.evalLt env) (hR : rhs.evalLt env) :
    (mkBitAndSmart lhs rhs).eval env = (SmartScalarExpr.bin .bitAnd lhs rhs).eval env := by
  have hNz := nat_beq_zero_false hSz
  have hModEq := scalarModulus_eq_two_pow sz
  have hSubLt : 2 ^ (sz * 8) - 1 < 2 ^ (sz * 8) := by
    have : 0 < 2 ^ (sz * 8) := Nat.pow_pos (by decide); omega
  unfold SmartScalarExpr.evalLt at hL hR
  unfold mkBitAndSmart
  split
  · rename_i hEq
    have hEq' : lhs = rhs := beq_iff_eq.mp hEq
    subst hEq'
    rw [eval_bin_eq]
    simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq,
      bitwiseAndBits_self, ← hModEq, Nat.mod_eq_of_lt hL]
  · cases lhs with
    | const a =>
      cases rhs with
      | const b =>
        dsimp only
        rw [eval_bin_eq]
        simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq,
          mkConstSmart, eval_const_eq, wrapScalarBits_eq_mod, hModEq,
          bitwiseAndBits_mod_left, bitwiseAndBits_mod_right,
          Nat.mod_eq_of_lt (bitwiseAndBits_lt (sz * 8) a b)]
      | var _ | bin _ _ _ =>
        cases a with
        | zero =>
          rw [eval_bin_eq]
          simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq,
            eval_const_eq, Nat.zero_mod, bitwiseAndBits_zero_left]
        | succ a' =>
          by_cases hMask : (a' + 1 == allOnesMask sz) = true
          · have hMask' : a' + 1 = allOnesMask sz := beq_iff_eq.mp hMask
            simp only [hMask, ↓reduceIte]
            rw [hMask']
            conv => rhs; rw [eval_bin_eq]
            simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq,
              allOnesMask, eval_const_eq, hModEq, Nat.mod_eq_of_lt hSubLt,
              bitwiseAndBits_allOnes_left]
            rw [← hModEq, Nat.mod_eq_of_lt hR]
          · simp only [hMask, Bool.false_eq_true, ↓reduceIte]
    | var _ | bin _ _ _ =>
      cases rhs with
      | const b =>
        cases b with
        | zero =>
          conv => rhs; rw [eval_bin_eq]
          simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq,
            eval_const_eq, Nat.zero_mod, bitwiseAndBits_zero_right]
        | succ b' =>
          by_cases hMask : (b' + 1 == allOnesMask sz) = true
          · have hMask' : b' + 1 = allOnesMask sz := beq_iff_eq.mp hMask
            simp only [hMask, ↓reduceIte]
            rw [hMask']
            conv => rhs; rw [eval_bin_eq]
            simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq,
              allOnesMask, eval_const_eq, hModEq, Nat.mod_eq_of_lt hSubLt,
              bitwiseAndBits_allOnes_right]
            rw [← hModEq, Nat.mod_eq_of_lt hL]
          · simp only [hMask, Bool.false_eq_true, ↓reduceIte]
      | var _ | bin _ _ _ => rfl

/-- Exact equivalence `mkBitOrSmart_eq_raw` against unmodified `evalScalarBinOp`. -/
theorem mkBitOrSmart_eq_raw {sz : Nat} (hSz : sz ≠ 0) (env : Nat → Nat)
    (lhs rhs : SmartScalarExpr sz) (hL : lhs.evalLt env) (hR : rhs.evalLt env) :
    (mkBitOrSmart lhs rhs).eval env = (SmartScalarExpr.bin .bitOr lhs rhs).eval env := by
  have hNz := nat_beq_zero_false hSz
  have hModEq := scalarModulus_eq_two_pow sz
  have hSubLt : 2 ^ (sz * 8) - 1 < 2 ^ (sz * 8) := by
    have : 0 < 2 ^ (sz * 8) := Nat.pow_pos (by decide); omega
  unfold SmartScalarExpr.evalLt at hL hR
  unfold mkBitOrSmart
  split
  · rename_i hEq
    have hEq' : lhs = rhs := beq_iff_eq.mp hEq
    subst hEq'
    conv => rhs; rw [eval_bin_eq]
    simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq,
      bitwiseOrBits_self, ← hModEq, Nat.mod_eq_of_lt hL]
  · cases lhs with
    | const a =>
      cases rhs with
      | const b =>
        dsimp only
        conv => rhs; rw [eval_bin_eq]
        simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq,
          mkConstSmart, eval_const_eq, wrapScalarBits_eq_mod, hModEq,
          bitwiseOrBits_mod_left, bitwiseOrBits_mod_right,
          Nat.mod_eq_of_lt (bitwiseOrBits_lt (sz * 8) a b)]
      | var _ | bin _ _ _ =>
        cases a with
        | zero =>
          conv => rhs; rw [eval_bin_eq]
          simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq,
            eval_const_eq, Nat.zero_mod, bitwiseOrBits_zero_left, ← hModEq,
            Nat.mod_eq_of_lt hR]
        | succ a' =>
          by_cases hMask : (a' + 1 == allOnesMask sz) = true
          · have hMask' : a' + 1 = allOnesMask sz := beq_iff_eq.mp hMask
            simp only [hMask, ↓reduceIte]
            rw [hMask']
            conv => rhs; rw [eval_bin_eq]
            simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq,
              allOnesMask, eval_const_eq, hModEq, Nat.mod_eq_of_lt hSubLt,
              bitwiseOrBits_allOnes_left]
          · simp only [hMask, Bool.false_eq_true, ↓reduceIte]
    | var _ | bin _ _ _ =>
      cases rhs with
      | const b =>
        cases b with
        | zero =>
          conv => rhs; rw [eval_bin_eq]
          simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq,
            eval_const_eq, Nat.zero_mod, bitwiseOrBits_zero_right, ← hModEq,
            Nat.mod_eq_of_lt hL]
        | succ b' =>
          by_cases hMask : (b' + 1 == allOnesMask sz) = true
          · have hMask' : b' + 1 = allOnesMask sz := beq_iff_eq.mp hMask
            simp only [hMask, ↓reduceIte]
            rw [hMask']
            conv => rhs; rw [eval_bin_eq]
            simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq,
              allOnesMask, eval_const_eq, hModEq, Nat.mod_eq_of_lt hSubLt,
              bitwiseOrBits_allOnes_right]
          · simp only [hMask, Bool.false_eq_true, ↓reduceIte]
      | var _ | bin _ _ _ => rfl

/-- Exact equivalence `mkBitXorSmart_eq_raw` against unmodified `evalScalarBinOp`. -/
theorem mkBitXorSmart_eq_raw {sz : Nat} (hSz : sz ≠ 0) (env : Nat → Nat)
    (lhs rhs : SmartScalarExpr sz) (hL : lhs.evalLt env) (hR : rhs.evalLt env) :
    (mkBitXorSmart lhs rhs).eval env = (SmartScalarExpr.bin .bitXor lhs rhs).eval env := by
  have hNz := nat_beq_zero_false hSz
  have hModEq := scalarModulus_eq_two_pow sz
  unfold SmartScalarExpr.evalLt at hL hR
  unfold mkBitXorSmart
  split
  · rename_i hEq
    have hEq' : lhs = rhs := beq_iff_eq.mp hEq
    subst hEq'
    conv => rhs; rw [eval_bin_eq]
    simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq,
      eval_const_eq, Nat.zero_mod, bitwiseXorBits_self]
  · cases lhs with
    | const a =>
      cases rhs with
      | const b =>
        dsimp only
        conv => rhs; rw [eval_bin_eq]
        simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq,
          mkConstSmart, eval_const_eq, wrapScalarBits_eq_mod, hModEq,
          bitwiseXorBits_mod_left, bitwiseXorBits_mod_right,
          Nat.mod_eq_of_lt (bitwiseXorBits_lt (sz * 8) a b)]
      | var _ | bin _ _ _ =>
        cases a with
        | zero =>
          conv => rhs; rw [eval_bin_eq]
          simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq,
            eval_const_eq, Nat.zero_mod, bitwiseXorBits_zero_left, ← hModEq,
            Nat.mod_eq_of_lt hR]
        | succ _ => rfl
    | var _ | bin _ _ _ =>
      cases rhs with
      | const b =>
        cases b with
        | zero =>
          conv => rhs; rw [eval_bin_eq]
          simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq,
            eval_const_eq, Nat.zero_mod, bitwiseXorBits_zero_right, ← hModEq,
            Nat.mod_eq_of_lt hL]
        | succ _ => rfl
      | var _ | bin _ _ _ => rfl

/-- Exact equivalence `mkShlSmart_eq_raw` against unmodified `evalScalarBinOp`. -/
theorem mkShlSmart_eq_raw {sz : Nat} (hSz : sz ≠ 0) (env : Nat → Nat)
    (lhs rhs : SmartScalarExpr sz) (hL : lhs.evalLt env) :
    (mkShlSmart lhs rhs).eval env = (SmartScalarExpr.bin .shl lhs rhs).eval env := by
  have hNz := nat_beq_zero_false hSz
  have hNe0 : (sz == 0) = false := beq_false_of_ne hSz
  have hBne0 : (sz != 0) = true := bne_iff_ne.mpr hSz
  unfold SmartScalarExpr.evalLt at hL
  cases lhs with
  | const a =>
    cases rhs with
    | const b =>
      dsimp only [mkShlSmart]
      conv => rhs; rw [eval_bin_eq]
      simp only [evalScalarBinOp, hNz, nat_mul_eq, nat_mod_eq,
        mkConstSmart, hNe0, Bool.false_eq_true, ↓reduceIte,
        eval_const_eq, shiftLeftBits, wrapScalarBits_eq_mod, Nat.mod_mod]
    | var _ | bin _ _ _ =>
      cases a with
      | zero =>
        dsimp only [mkShlSmart]
        conv => rhs; rw [eval_bin_eq]
        simp only [evalScalarBinOp, hNz, nat_mul_eq, nat_mod_eq,
          eval_const_eq, shiftLeftBits, wrapScalarBits_eq_mod, Nat.zero_mod, Nat.zero_mul]
      | succ _ => rfl
  | var _ | bin _ _ _ =>
    cases rhs with
    | const b =>
      dsimp only [mkShlSmart]
      simp only [hBne0, Bool.true_and]
      split
      · rename_i hRem0
        have hRem0' : b % scalarModulus sz % (sz * 8) = 0 := by
          simpa only [wrapScalarBits_eq_mod, beq_iff_eq] using hRem0
        conv => rhs; rw [eval_bin_eq]
        simp only [evalScalarBinOp, hNz, nat_mul_eq, nat_mod_eq,
          eval_const_eq, hRem0', shiftLeftBits, scalarPow2, Nat.mul_one, wrapScalarBits_eq_mod]
        exact (Nat.mod_eq_of_lt hL).symm
      · rfl
    | var _ | bin _ _ _ => rfl

/-- Exact equivalence `mkShrSmart_eq_raw` against unmodified `evalScalarBinOp`. -/
theorem mkShrSmart_eq_raw {sz : Nat} (hSz : sz ≠ 0) (env : Nat → Nat)
    (lhs rhs : SmartScalarExpr sz) (hL : lhs.evalLt env) :
    (mkShrSmart lhs rhs).eval env = (SmartScalarExpr.bin .shr lhs rhs).eval env := by
  have hNz := nat_beq_zero_false hSz
  have hNe0 : (sz == 0) = false := beq_false_of_ne hSz
  have hBne0 : (sz != 0) = true := bne_iff_ne.mpr hSz
  unfold SmartScalarExpr.evalLt at hL
  cases lhs with
  | const a =>
    cases rhs with
    | const b =>
      dsimp only [mkShrSmart]
      conv => rhs; rw [eval_bin_eq]
      simp only [evalScalarBinOp, hNz, nat_mul_eq, nat_mod_eq,
        mkConstSmart, hNe0, Bool.false_eq_true, ↓reduceIte,
        eval_const_eq, shiftRightUnsignedBits, nat_div_eq, wrapScalarBits_eq_mod, Nat.mod_mod]
    | var _ | bin _ _ _ =>
      cases a with
      | zero =>
        dsimp only [mkShrSmart]
        conv => rhs; rw [eval_bin_eq]
        simp only [evalScalarBinOp, hNz, nat_mul_eq, nat_mod_eq,
          eval_const_eq, shiftRightUnsignedBits, nat_div_eq,
          wrapScalarBits_eq_mod, Nat.zero_mod, Nat.zero_div]
      | succ _ => rfl
  | var _ | bin _ _ _ =>
    cases rhs with
    | const b =>
      dsimp only [mkShrSmart]
      simp only [hBne0, Bool.true_and]
      split
      · rename_i hRem0
        have hRem0' : b % scalarModulus sz % (sz * 8) = 0 := by
          simpa only [wrapScalarBits_eq_mod, beq_iff_eq] using hRem0
        conv => rhs; rw [eval_bin_eq]
        simp only [evalScalarBinOp, hNz, nat_mul_eq, nat_mod_eq,
          eval_const_eq, hRem0', shiftRightUnsignedBits, scalarPow2, nat_div_eq,
          Nat.div_one, wrapScalarBits_eq_mod]
        exact (Nat.mod_eq_of_lt hL).symm
      · rfl
    | var _ | bin _ _ _ => rfl

/-- Nested `O(1)` smart-constructor collapse witness: `((((x + 0) * 1) | 0) & allOnes) ^ 0 = x`. -/
theorem bitprism_nested_collapse_o1 (x : Nat) :
    mkBitXorSmart
      (mkBitAndSmart
        (mkBitOrSmart
          (mkMulSmart (mkAddSmart (SmartScalarExpr.var (sz := 4) x) (.const 0)) (.const 1))
          (.const 0))
        (.const (allOnesMask 4)))
      (.const 0) = SmartScalarExpr.var (sz := 4) x := rfl

/-! ### B.3. Pointer Offset Smart Simplifying Constructors (`mkPtrOffsetSmart`, `mkWrappingPtrOffsetSmart`) -/

/-- Smart simplifying constructor for in-bounds pointer offset (`evalBinOpOffset`):
collapses zero byte-offset or zero stride to the input pointer directly (when pointer & bound
validity preconditions hold), delegating all non-trivial offsets to unmodified `evalBinOpOffset`. -/
def mkPtrOffsetSmart (ptr : ProvenancePtr) (ptrSz : Nat) (off : ScalarInt)
    (stride : Nat) (boundOpt : Option Nat) : Option ProvenancePtr :=
  if ptrSz == 8 && off.sizeBytes == 8 && (wrapScalarBits off.bits (scalarModulus 8) == 0 || stride == 0) then
    let halfMod := signedHalfModulus 8
    let inBounds := match boundOpt with
      | .none => Bool.not (Nat.ble halfMod ptr.offsetBytes)
      | .some b =>
        Bool.or
          (Bool.and (Nat.beq b 0) (Bool.not (Nat.ble halfMod ptr.offsetBytes)))
          (Bool.and (Bool.not (Nat.ble halfMod b)) (Nat.ble ptr.offsetBytes b))
    if inBounds then some ptr else none
  else
    evalBinOpOffset ptr ptrSz off stride boundOpt 8

/-- Exact equivalence `mkPtrOffsetSmart_eq_raw` against unmodified `Trusted.MirSemantics.evalBinOpOffset`
(note: preserves the exact `inBounds` / `halfMod` checks so OOB zero-offset UB is NEVER erased!). -/
theorem mkPtrOffsetSmart_eq_raw (ptr : ProvenancePtr) (ptrSz : Nat) (off : ScalarInt)
    (stride : Nat) (boundOpt : Option Nat) :
    mkPtrOffsetSmart ptr ptrSz off stride boundOpt =
      evalBinOpOffset ptr ptrSz off stride boundOpt 8 := by
  unfold mkPtrOffsetSmart
  split
  · rename_i hCond
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hCond
    obtain ⟨⟨hPtr8, hOff8⟩, hZero⟩ := hCond
    subst hPtr8
    unfold evalBinOpOffset
    have hOff8' : Nat.beq off.sizeBytes 8 = true := Nat.beq_eq.mpr hOff8
    have hPtr8' : Nat.beq 8 8 = true := rfl
    simp only [hPtr8', hOff8', Bool.and_self]
    have hBle0 : Nat.ble (signedHalfModulus 8) 0 = false := by decide
    have hBleZero : Nat.ble 0 ptr.offsetBytes = true := Nat.ble_eq.mpr (Nat.zero_le _)
    have hBoundsFalse :
        Nat.ble (signedHalfModulus 8) ptr.offsetBytes = true →
        (match boundOpt with
         | none => !true
         | some b => (Nat.beq b 0 && !true) || (!Nat.ble (signedHalfModulus 8) b && Nat.ble ptr.offsetBytes b)) = false := by
      intro hHalf
      cases boundOpt with
      | none => rfl
      | some b =>
        simp only [Bool.not_true, Bool.and_false, Bool.false_or]
        cases hB : Nat.ble (signedHalfModulus 8) b with
        | true => rfl
        | false =>
          have hB1 : b < signedHalfModulus 8 := by
            have hN : ¬ (signedHalfModulus 8 ≤ b) := by
              intro hLe; have := Nat.ble_eq.mpr hLe; rw [this] at hB; cases hB
            omega
          have hP1 : signedHalfModulus 8 ≤ ptr.offsetBytes := Nat.ble_eq.mp hHalf
          have hPB : Nat.ble ptr.offsetBytes b = false := by
            cases hpb : Nat.ble ptr.offsetBytes b with
            | false => rfl
            | true => have := Nat.ble_eq.mp hpb; omega
          simp [hPB]
    rcases hZero with hOff0 | hStr0
    · rw [hOff0]
      have hNeg : isSignedNegative 0 8 = false := by decide
      simp only [hNeg, nat_add_eq, nat_mul_eq, Nat.zero_mul, hBle0, Nat.add_zero]
      cases hHalf : Nat.ble (signedHalfModulus 8) ptr.offsetBytes with
      | false =>
        cases boundOpt with
        | none => rfl
        | some b =>
          simp only [Bool.not_false, Bool.and_true, Nat.beq_refl, Bool.and_self]
          cases (!Nat.ble (signedHalfModulus 8) b && Nat.ble ptr.offsetBytes b) <;>
            cases Nat.beq b 0 <;> rfl
      | true =>
        have hBF := hBoundsFalse hHalf
        simp only [hBF, Bool.false_eq_true, ↓reduceIte]
    · subst hStr0
      cases hNeg : isSignedNegative (wrapScalarBits off.bits (scalarModulus 8)) 8 with
      | false =>
        simp only [nat_add_eq, nat_mul_eq, Nat.mul_zero, hBle0, Nat.add_zero]
        cases hHalf : Nat.ble (signedHalfModulus 8) ptr.offsetBytes with
        | false =>
          cases boundOpt with
          | none => rfl
          | some b =>
            simp only [Bool.not_false, Bool.and_true, Nat.beq_refl, Bool.and_self]
            cases (!Nat.ble (signedHalfModulus 8) b && Nat.ble ptr.offsetBytes b) <;>
              cases Nat.beq b 0 <;> rfl
        | true =>
          have hBF := hBoundsFalse hHalf
          simp only [hBF, Bool.false_eq_true, ↓reduceIte]
      | true =>
        simp only [nat_sub_eq, nat_mul_eq, Nat.mul_zero, hBle0, Bool.not_false,
          hBleZero, Bool.and_self, Nat.sub_zero]
        cases hHalf : Nat.ble (signedHalfModulus 8) ptr.offsetBytes with
        | false =>
          cases boundOpt with
          | none => rfl
          | some b =>
            simp only [Bool.not_false, Bool.and_true, Nat.beq_refl, Bool.and_self]
            cases (!Nat.ble (signedHalfModulus 8) b && Nat.ble ptr.offsetBytes b) <;>
              cases Nat.beq b 0 <;> rfl
        | true =>
          have hBF := hBoundsFalse hHalf
          simp only [hBF, Bool.false_eq_true, ↓reduceIte]
          cases boundOpt with
          | none => rfl
          | some b =>
            simp only [Bool.not_true, Bool.and_false, Bool.false_or]
            have hSub : (!Nat.ble (signedHalfModulus 8) b && Nat.ble ptr.offsetBytes b) = false := by
              simpa [Bool.not_true, Bool.and_false, Bool.false_or] using hBF
            cases hB : Nat.ble (signedHalfModulus 8) b with
            | true => rfl
            | false =>
              simp only [hB, Bool.not_false, Bool.true_and] at hSub ⊢
              simp [hSub]
  · rfl

/-- Smart simplifying constructor for wrapping pointer offset (`evalArithOffset`):
collapses zero offset or zero stride in `O(1)` while wrapping `ptr.offsetBytes` modulo `2^64`. -/
def mkWrappingPtrOffsetSmart (ptr : ProvenancePtr) (ptrSz : Nat) (off : ScalarInt)
    (stride : Nat) : Option ProvenancePtr :=
  if ptrSz == 8 && off.sizeBytes == 8 && (wrapScalarBits off.bits (scalarModulus 8) == 0 || stride == 0) then
    some { ptr with offsetBytes := wrapScalarBits ptr.offsetBytes (scalarModulus 8) }
  else
    evalArithOffset ptr ptrSz off stride

/-- Exact equivalence `mkWrappingPtrOffsetSmart_eq_raw` against unmodified `evalArithOffset`. -/
theorem mkWrappingPtrOffsetSmart_eq_raw (ptr : ProvenancePtr) (ptrSz : Nat) (off : ScalarInt)
    (stride : Nat) :
    mkWrappingPtrOffsetSmart ptr ptrSz off stride = evalArithOffset ptr ptrSz off stride := by
  unfold mkWrappingPtrOffsetSmart
  split
  · rename_i hCond
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hCond
    obtain ⟨⟨hPtr8, hOff8⟩, hZero⟩ := hCond
    subst hPtr8
    unfold evalArithOffset
    have hOff8' : Nat.beq off.sizeBytes 8 = true := Nat.beq_eq.mpr hOff8
    have hPtr8' : Nat.beq 8 8 = true := rfl
    simp only [hPtr8', hOff8', Bool.and_self]
    rcases hZero with hOff0 | hStr0
    · rw [hOff0]
      have hNeg : isSignedNegative 0 8 = false := by decide
      simp [hNeg]
    · subst hStr0
      cases isSignedNegative (wrapScalarBits off.bits (scalarModulus 8)) 8 with
      | false => simp
      | true =>
        simp only [nat_add_eq, nat_sub_eq, nat_mul_eq, Nat.mul_zero, wrapScalarBits_eq_mod,
          Nat.zero_mod, Nat.sub_zero, Nat.add_mod_right]
  · rfl

/-! ### B.4. Level 2 — MIR `Rvalue` Smart Constructors (Strictly UB-Preserving!) -/

/-- Extract a constant `ScalarInt` from a `MirAst.Operand` if syntactically a scalar int constant. -/
def operandConstScalar? : Operand → Option ScalarInt
  | .constant ⟨_, .scalar (.int sc)⟩ => some sc
  | _ => none

/-- Construct a typed constant `Operand` from a `Ty` and `ScalarInt`. -/
def mkConstScalarOp (ty : Ty) (sc : ScalarInt) : Operand :=
  .constant ⟨ty, .scalar (.int sc)⟩

/-- MIR-level `Rvalue` smart simplifying constructors (`Bitprism` cl/1029634110 pattern).
NOTE: Unchecked operations (`addUnchecked`, `subUnchecked`, `mulUnchecked`, `shlUnchecked`,
`shrUnchecked`) are NEVER simplified by these constructors. ANNIHILATOR rewrites (`0 & x`, `x * 0`,
`allOnes | x`), which DROP an operand, fire ONLY when the dropped operand is itself a same-width
scalar CONSTANT, so a dead/uninit local read is NEVER erased (proved UNCONDITIONALLY for every
operand by `mkBitAndSmartRvalue_zero_{left,right}_eq_raw` / `mkMulSmartRvalue_zero_{left,right}_eq_raw`).
IDENTITY rewrites (`x + 0`, `x | 0`, `1 * x`, ...) keep evaluating `x` via `.use x`; their
`*_eq_raw` theorems carry the exact direct-operand / width / canonicity / validity preconditions. -/
def mkAddSmartRvalue (lhs rhs : Operand) : Rvalue :=
  match operandConstScalar? lhs, operandConstScalar? rhs with
  | some ⟨a, sz⟩, some ⟨b, sz'⟩ =>
    if sz != 0 && sz == sz' then
      if a == 0 && b < scalarModulus sz then .use rhs
      else if b == 0 && a < scalarModulus sz then .use lhs
      else .binaryOp .add lhs rhs
    else .binaryOp .add lhs rhs
  | some ⟨0, sz⟩, none => if sz == 0 then .binaryOp .add lhs rhs else .use rhs
  | none, some ⟨0, sz⟩ => if sz == 0 then .binaryOp .add lhs rhs else .use lhs
  | _, _ => .binaryOp .add lhs rhs

def mkSubSmartRvalue (lhs rhs : Operand) : Rvalue :=
  match operandConstScalar? lhs, operandConstScalar? rhs with
  | some ⟨a, sz⟩, some ⟨0, sz'⟩ =>
    if sz != 0 && sz == sz' && a < scalarModulus sz then .use lhs else .binaryOp .sub lhs rhs
  | none, some ⟨0, sz⟩ => if sz == 0 then .binaryOp .sub lhs rhs else .use lhs
  | _, _ => .binaryOp .sub lhs rhs

def mkMulSmartRvalue (resTy : Ty) (lhs rhs : Operand) : Rvalue :=
  match operandConstScalar? lhs, operandConstScalar? rhs with
  -- Constant-constant pair: ALWAYS check `sz != 0 && sz == sz'` first so width-mismatched
  -- constant pairs preserve `.unsupported` and annihilators never drop a non-constant read.
  | some ⟨a, sz⟩, some ⟨b, sz'⟩ =>
    if sz != 0 && sz == sz' then
      if a == 0 || b == 0 then .use (mkConstScalarOp resTy ⟨0, sz⟩)
      else if a == 1 && b < scalarModulus sz then .use rhs
      else if b == 1 && a < scalarModulus sz then .use lhs
      else .binaryOp .mul lhs rhs
    else .binaryOp .mul lhs rhs
  -- `0 * x` / `x * 0` with NON-constant `x`: `x` may read a dead/uninit local (UB) -> keep raw.
  | some ⟨0, _⟩, none => .binaryOp .mul lhs rhs
  | none, some ⟨0, _⟩ => .binaryOp .mul lhs rhs
  -- Identity `1 * x` / `x * 1`: `x` is STILL evaluated (`.use x`), so its UB is preserved.
  | some ⟨1, sz⟩, none => if sz == 0 then .binaryOp .mul lhs rhs else .use rhs
  | none, some ⟨1, sz⟩ => if sz == 0 then .binaryOp .mul lhs rhs else .use lhs
  | _, _ => .binaryOp .mul lhs rhs

def mkBitAndSmartRvalue (resTy : Ty) (lhs rhs : Operand) : Rvalue :=
  match operandConstScalar? lhs, operandConstScalar? rhs with
  -- Constant-constant pair: ALWAYS check `sz != 0 && sz == sz'` first.
  | some ⟨a, sz⟩, some ⟨b, sz'⟩ =>
    if sz != 0 && sz == sz' then
      if a == 0 || b == 0 then .use (mkConstScalarOp resTy ⟨0, sz⟩)
      else if a == allOnesMask sz && b < scalarModulus sz then .use rhs
      else if b == allOnesMask sz && a < scalarModulus sz then .use lhs
      else .binaryOp .bitAnd lhs rhs
    else .binaryOp .bitAnd lhs rhs
  -- `0 & x` / `x & 0` with NON-constant `x`: keep raw so `x`'s dead/uninit-read UB survives.
  | some ⟨0, _⟩, none => .binaryOp .bitAnd lhs rhs
  | none, some ⟨0, _⟩ => .binaryOp .bitAnd lhs rhs
  -- Identity `allOnes & x` / `x & allOnes`: `x` is still evaluated.
  | some ⟨a, sz⟩, none => if sz != 0 && a == allOnesMask sz then .use rhs else .binaryOp .bitAnd lhs rhs
  | none, some ⟨b, sz⟩ => if sz != 0 && b == allOnesMask sz then .use lhs else .binaryOp .bitAnd lhs rhs
  | _, _ => .binaryOp .bitAnd lhs rhs

def mkBitOrSmartRvalue (resTy : Ty) (lhs rhs : Operand) : Rvalue :=
  match operandConstScalar? lhs, operandConstScalar? rhs with
  -- Constant-constant pair FIRST: width-mismatched pairs (e.g. `allOnes_u32 | 0_u8`) ALWAYS stay
  -- raw (preserving `.unsupported`), while same-width `allOnes | c` / `c | allOnes` collapse cleanly.
  | some ⟨a, sz⟩, some ⟨b, sz'⟩ =>
    if sz != 0 && sz == sz' then
      if a == allOnesMask sz || b == allOnesMask sz then
        .use (mkConstScalarOp resTy ⟨allOnesMask sz, sz⟩)
      else if a == 0 && b < scalarModulus sz then .use rhs
      else if b == 0 && a < scalarModulus sz then .use lhs
      else .binaryOp .bitOr lhs rhs
    else .binaryOp .bitOr lhs rhs
  -- Identity `0 | x` / `x | 0` on non-constant `x`: `x` is still evaluated.
  | some ⟨0, sz⟩, none => if sz == 0 then .binaryOp .bitOr lhs rhs else .use rhs
  | none, some ⟨0, sz⟩ => if sz == 0 then .binaryOp .bitOr lhs rhs else .use lhs
  -- `allOnes | x` with NON-constant `x`: keep raw (never erase `x`'s dead/uninit-read UB).
  | _, _ => .binaryOp .bitOr lhs rhs

def mkBitXorSmartRvalue (lhs rhs : Operand) : Rvalue :=
  match operandConstScalar? lhs, operandConstScalar? rhs with
  | some ⟨a, sz⟩, some ⟨b, sz'⟩ =>
    if sz != 0 && sz == sz' then
      if a == 0 && b < scalarModulus sz then .use rhs
      else if b == 0 && a < scalarModulus sz then .use lhs
      else .binaryOp .bitXor lhs rhs
    else .binaryOp .bitXor lhs rhs
  | some ⟨0, sz⟩, none => if sz == 0 then .binaryOp .bitXor lhs rhs else .use rhs
  | none, some ⟨0, sz⟩ => if sz == 0 then .binaryOp .bitXor lhs rhs else .use lhs
  | _, _ => .binaryOp .bitXor lhs rhs

def mkShlSmartRvalue (lhs rhs : Operand) : Rvalue :=
  match operandConstScalar? lhs, operandConstScalar? rhs with
  | some ⟨a, szL⟩, some ⟨0, szR⟩ =>
    if szL != 0 && szR != 0 && a < scalarModulus szL then .use lhs else .binaryOp .shl lhs rhs
  | none, some ⟨0, szR⟩ => if szR == 0 then .binaryOp .shl lhs rhs else .use lhs
  | _, _ => .binaryOp .shl lhs rhs

def mkShrSmartRvalue (lhs rhs : Operand) : Rvalue :=
  match operandConstScalar? lhs, operandConstScalar? rhs with
  | some ⟨a, szL⟩, some ⟨0, szR⟩ =>
    if szL != 0 && szR != 0 && a < scalarModulus szL then .use lhs else .binaryOp .shr lhs rhs
  | none, some ⟨0, szR⟩ => if szR == 0 then .binaryOp .shr lhs rhs else .use lhs
  | _, _ => .binaryOp .shr lhs rhs

/-- Predicate ensuring an `Operand` is a non-dereferencing operand (constant or direct local copy/move)
so `.use op` performs no Tree Borrows deref read-freeze side effect. -/
def isDirectOperand : Operand → Prop
  | .constant _ => True
  | .copy p => p.projection = []
  | .move p => p.projection = []

private theorem evalRvalue_use_direct (locals locals' : List LocalSlot) (op : Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) (sc : ScalarInt)
    (hDirect : isDirectOperand op)
    (hEval : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar sc) locals')
    (hVal : validateLoadedValue layouts localDecls op (.scalar sc) = true) :
    evalRvalue locals (.use op) mem localDecls layouts = .ok (.scalar sc) locals' mem := by
  simp only [evalRvalue, hEval, hVal]
  cases op with
  | constant c => rfl
  | copy p =>
    cases p with
    | mk l proj =>
      simp only [isDirectOperand] at hDirect
      subst hDirect; rfl
  | move p =>
    cases p with
    | mk l proj =>
      simp only [isDirectOperand] at hDirect
      subst hDirect; rfl

/-- Exact UB-preserving soundness for `mkAddSmartRvalue` on unmodified `Trusted.MirSemantics.evalRvalue`:
`x + 0` equals `.use x` when `x` evaluates cleanly to a canonical `sz`-byte scalar (`sz ≠ 0`). -/
theorem mkAddSmartRvalue_zero_right_eq_raw (locals locals' : List LocalSlot)
    (lhs : Operand) (ty0 : Ty) (sz : Nat) (sc : ScalarInt)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hDirect : isDirectOperand lhs)
    (hSz : sz ≠ 0) (hEqSz : sc.sizeBytes = sz)
    (hCanon : sc.bits < scalarModulus sz)
    (hNotConst0 : operandConstScalar? lhs = none)
    (hEval : evalOperand locals lhs mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar sc) locals')
    (hVal : validateLoadedValue layouts localDecls lhs (.scalar sc) = true) :
    evalRvalue locals (mkAddSmartRvalue lhs (mkConstScalarOp ty0 ⟨0, sz⟩)) mem localDecls layouts =
      evalRvalue locals (.binaryOp .add lhs (mkConstScalarOp ty0 ⟨0, sz⟩)) mem localDecls layouts := by
  have hNe0 : (sz == 0) = false := beq_false_of_ne hSz
  have hNz := nat_beq_zero_false hSz
  unfold mkAddSmartRvalue
  rw [hNotConst0]
  simp only [mkConstScalarOp, operandConstScalar?, hNe0, Bool.false_eq_true, ↓reduceIte]
  rw [evalRvalue_use_direct locals locals' lhs mem localDecls layouts sc hDirect hEval hVal]
  have hConstEval : evalOperand locals' (.constant ⟨ty0, .scalar (.int ⟨0, sz⟩)⟩)
      mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar ⟨0, sz⟩) locals' := rfl
  simp only [evalRvalue, hEval, hConstEval]
  cases sc with
  | mk bits sb =>
    simp only at hEqSz hCanon
    subst hEqSz
    simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_add_eq, Nat.add_zero,
      wrapScalarBits_of_lt hCanon]

/-- Inversion: `operandConstScalar? op = some sc` iff `op` is literally a scalar-int constant. -/
theorem operandConstScalar?_eq_some {op : Operand} {sc : ScalarInt}
    (h : operandConstScalar? op = some sc) : ∃ ty, op = .constant ⟨ty, .scalar (.int sc)⟩ := by
  unfold operandConstScalar? at h
  split at h
  · cases h; exact ⟨_, rfl⟩
  · cases h

/-- Raw evaluation of `0 & c` / `c & 0` / `0 * c` / `c * 0` on two same-width (`sz ≠ 0`) scalar
constants on unmodified `Trusted.MirSemantics.evalRvalue`. -/
private theorem const_annihilator_raw_eval (locals : List LocalSlot) (ty0 tyR : Ty) (b sz : Nat)
    (hSz : sz ≠ 0) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalue locals (.binaryOp .bitAnd (mkConstScalarOp ty0 ⟨0, sz⟩) (mkConstScalarOp tyR ⟨b, sz⟩))
        mem localDecls layouts = .ok (.scalar ⟨0, sz⟩) locals mem ∧
    evalRvalue locals (.binaryOp .bitAnd (mkConstScalarOp tyR ⟨b, sz⟩) (mkConstScalarOp ty0 ⟨0, sz⟩))
        mem localDecls layouts = .ok (.scalar ⟨0, sz⟩) locals mem ∧
    evalRvalue locals (.binaryOp .mul (mkConstScalarOp ty0 ⟨0, sz⟩) (mkConstScalarOp tyR ⟨b, sz⟩))
        mem localDecls layouts = .ok (.scalar ⟨0, sz⟩) locals mem ∧
    evalRvalue locals (.binaryOp .mul (mkConstScalarOp tyR ⟨b, sz⟩) (mkConstScalarOp ty0 ⟨0, sz⟩))
        mem localDecls layouts = .ok (.scalar ⟨0, sz⟩) locals mem := by
  have hNz := nat_beq_zero_false hSz
  have h0 : evalOperand locals (.constant ⟨ty0, .scalar (.int ⟨0, sz⟩)⟩)
      mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar ⟨0, sz⟩) locals := rfl
  have hB : evalOperand locals (.constant ⟨tyR, .scalar (.int ⟨b, sz⟩)⟩)
      mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar ⟨b, sz⟩) locals := rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [evalRvalue, mkConstScalarOp, h0, hB, evalScalarBinOp, hNz, Nat.beq_refl,
      bitwiseAndBits_zero_left, bitwiseAndBits_zero_right, nat_mul_eq, Nat.mul_zero, Nat.zero_mul,
      wrapScalarBits_eq_mod, Nat.zero_mod]

/-- Smart `.use (const sc)` evaluation. -/
private theorem use_const_scalar_eval (locals : List LocalSlot) (resTy : Ty) (sc : ScalarInt) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalue locals (.use (.constant ⟨resTy, .scalar (.int sc)⟩)) mem localDecls layouts =
      .ok (.scalar sc) locals mem :=
  evalRvalue_use_direct locals locals (.constant ⟨resTy, .scalar (.int sc)⟩) mem localDecls
    layouts sc trivial rfl rfl

/-- Raw evaluation of `allOnes | c` and `c | allOnes` on two same-width (`sz ≠ 0`) scalar constants. -/
private theorem const_bitOr_allOnes_raw_eval (locals : List LocalSlot) (ty0 tyR : Ty) (b sz : Nat)
    (hSz : sz ≠ 0) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalue locals (.binaryOp .bitOr (mkConstScalarOp ty0 ⟨allOnesMask sz, sz⟩)
        (mkConstScalarOp tyR ⟨b, sz⟩)) mem localDecls layouts =
      .ok (.scalar ⟨allOnesMask sz, sz⟩) locals mem ∧
    evalRvalue locals (.binaryOp .bitOr (mkConstScalarOp tyR ⟨b, sz⟩)
        (mkConstScalarOp ty0 ⟨allOnesMask sz, sz⟩)) mem localDecls layouts =
      .ok (.scalar ⟨allOnesMask sz, sz⟩) locals mem := by
  have hNz := nat_beq_zero_false hSz
  have hA : evalOperand locals (.constant ⟨ty0, .scalar (.int ⟨allOnesMask sz, sz⟩)⟩)
      mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar ⟨allOnesMask sz, sz⟩) locals := rfl
  have hB : evalOperand locals (.constant ⟨tyR, .scalar (.int ⟨b, sz⟩)⟩)
      mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar ⟨b, sz⟩) locals := rfl
  have hMod : scalarModulus sz = 2 ^ (sz * 8) := scalarModulus_eq_two_pow sz
  have hMask : allOnesMask sz = 2 ^ (sz * 8) - 1 := by
    unfold allOnesMask; rw [hMod]
  refine ⟨?_, ?_⟩
  · simp only [evalRvalue, mkConstScalarOp, hA, hB, evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq]
    rw [hMask, bitwiseOrBits_allOnes_left]
  · simp only [evalRvalue, mkConstScalarOp, hA, hB, evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq]
    rw [hMask, bitwiseOrBits_allOnes_right]

/-- **UNCONDITIONAL exact UB-preserving soundness of `mkBitAndSmartRvalue` on `0 & rhs`** on
unmodified `Trusted.MirSemantics.evalRvalue`, for EVERY operand `rhs` (dead / uninit / deref /
constant), EVERY width `sz`, EVERY `locals`, `mem`, `localDecls`, `layouts`. -/
theorem mkBitAndSmartRvalue_zero_left_eq_raw (locals : List LocalSlot) (resTy ty0 : Ty)
    (rhs : Operand) (sz : Nat) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalue locals (mkBitAndSmartRvalue resTy (mkConstScalarOp ty0 ⟨0, sz⟩) rhs) mem localDecls layouts =
      evalRvalue locals (.binaryOp .bitAnd (mkConstScalarOp ty0 ⟨0, sz⟩) rhs) mem localDecls layouts := by
  cases hR : operandConstScalar? rhs with
  | none =>
    unfold mkBitAndSmartRvalue
    rw [hR]
    rfl
  | some sc =>
    obtain ⟨tyR, rfl⟩ := operandConstScalar?_eq_some hR
    obtain ⟨b, sz'⟩ := sc
    by_cases hC : sz ≠ 0 ∧ sz = sz'
    · obtain ⟨hSz, rfl⟩ := hC
      have hSimp : mkBitAndSmartRvalue resTy (mkConstScalarOp ty0 ⟨0, sz⟩)
          (.constant ⟨tyR, .scalar (.int ⟨b, sz⟩)⟩) = .use (mkConstScalarOp resTy ⟨0, sz⟩) := by
        simp [mkBitAndSmartRvalue, mkConstScalarOp, operandConstScalar?, hSz]
      rw [hSimp, mkConstScalarOp, use_const_scalar_eval]
      exact ((const_annihilator_raw_eval locals ty0 tyR b sz hSz mem localDecls layouts).1).symm
    · have hCond : (sz != 0 && sz == sz') = false := by
        cases h : (sz != 0 && sz == sz') with
        | false => rfl
        | true =>
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
          exact absurd h hC
      simp only [mkBitAndSmartRvalue, mkConstScalarOp, operandConstScalar?, hCond,
        Bool.false_eq_true, ↓reduceIte]

/-- **UNCONDITIONAL** `lhs & 0` soundness (symmetric to `mkBitAndSmartRvalue_zero_left_eq_raw`). -/
theorem mkBitAndSmartRvalue_zero_right_eq_raw (locals : List LocalSlot) (resTy ty0 : Ty)
    (lhs : Operand) (sz : Nat) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalue locals (mkBitAndSmartRvalue resTy lhs (mkConstScalarOp ty0 ⟨0, sz⟩)) mem localDecls layouts =
      evalRvalue locals (.binaryOp .bitAnd lhs (mkConstScalarOp ty0 ⟨0, sz⟩)) mem localDecls layouts := by
  cases hL : operandConstScalar? lhs with
  | none =>
    unfold mkBitAndSmartRvalue
    rw [hL]
    rfl
  | some sc =>
    obtain ⟨tyL, rfl⟩ := operandConstScalar?_eq_some hL
    obtain ⟨a, sz'⟩ := sc
    by_cases hC : sz' ≠ 0 ∧ sz' = sz
    · obtain ⟨hSz, rfl⟩ := hC
      have hSimp : mkBitAndSmartRvalue resTy (.constant ⟨tyL, .scalar (.int ⟨a, sz'⟩)⟩)
          (mkConstScalarOp ty0 ⟨0, sz'⟩) = .use (mkConstScalarOp resTy ⟨0, sz'⟩) := by
        simp [mkBitAndSmartRvalue, mkConstScalarOp, operandConstScalar?, hSz]
      rw [hSimp, mkConstScalarOp, use_const_scalar_eval]
      exact ((const_annihilator_raw_eval locals ty0 tyL a sz' hSz mem localDecls layouts).2.1).symm
    · have hCond : (sz' != 0 && sz' == sz) = false := by
        cases h : (sz' != 0 && sz' == sz) with
        | false => rfl
        | true =>
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
          exact absurd h hC
      simp only [mkBitAndSmartRvalue, mkConstScalarOp, operandConstScalar?, hCond,
        Bool.false_eq_true, ↓reduceIte]

/-- **UNCONDITIONAL** `0 * rhs` soundness on unmodified `evalRvalue` for EVERY operand `rhs`. -/
theorem mkMulSmartRvalue_zero_left_eq_raw (locals : List LocalSlot) (resTy ty0 : Ty)
    (rhs : Operand) (sz : Nat) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalue locals (mkMulSmartRvalue resTy (mkConstScalarOp ty0 ⟨0, sz⟩) rhs) mem localDecls layouts =
      evalRvalue locals (.binaryOp .mul (mkConstScalarOp ty0 ⟨0, sz⟩) rhs) mem localDecls layouts := by
  cases hR : operandConstScalar? rhs with
  | none =>
    unfold mkMulSmartRvalue
    rw [hR]
    rfl
  | some sc =>
    obtain ⟨tyR, rfl⟩ := operandConstScalar?_eq_some hR
    obtain ⟨b, sz'⟩ := sc
    by_cases hC : sz ≠ 0 ∧ sz = sz'
    · obtain ⟨hSz, rfl⟩ := hC
      have hSimp : mkMulSmartRvalue resTy (mkConstScalarOp ty0 ⟨0, sz⟩)
          (.constant ⟨tyR, .scalar (.int ⟨b, sz⟩)⟩) = .use (mkConstScalarOp resTy ⟨0, sz⟩) := by
        simp [mkMulSmartRvalue, mkConstScalarOp, operandConstScalar?, hSz]
      rw [hSimp, mkConstScalarOp, use_const_scalar_eval]
      exact ((const_annihilator_raw_eval locals ty0 tyR b sz hSz mem localDecls layouts).2.2.1).symm
    · have hCond : (sz != 0 && sz == sz') = false := by
        cases h : (sz != 0 && sz == sz') with
        | false => rfl
        | true =>
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
          exact absurd h hC
      simp only [mkMulSmartRvalue, mkConstScalarOp, operandConstScalar?, hCond,
        Bool.false_eq_true, ↓reduceIte]

/-- **UNCONDITIONAL** `lhs * 0` soundness on unmodified `evalRvalue` for EVERY operand `lhs`:
`_1 * 0` with `_1` dead/uninit still faults with `.ub`. -/
theorem mkMulSmartRvalue_zero_right_eq_raw (locals : List LocalSlot) (resTy ty0 : Ty)
    (lhs : Operand) (sz : Nat) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalue locals (mkMulSmartRvalue resTy lhs (mkConstScalarOp ty0 ⟨0, sz⟩)) mem localDecls layouts =
      evalRvalue locals (.binaryOp .mul lhs (mkConstScalarOp ty0 ⟨0, sz⟩)) mem localDecls layouts := by
  cases hL : operandConstScalar? lhs with
  | none =>
    unfold mkMulSmartRvalue
    rw [hL]
    rfl
  | some sc =>
    obtain ⟨tyL, rfl⟩ := operandConstScalar?_eq_some hL
    obtain ⟨a, sz'⟩ := sc
    by_cases hC : sz' ≠ 0 ∧ sz' = sz
    · obtain ⟨hSz, rfl⟩ := hC
      have hSimp : mkMulSmartRvalue resTy (.constant ⟨tyL, .scalar (.int ⟨a, sz'⟩)⟩)
          (mkConstScalarOp ty0 ⟨0, sz'⟩) = .use (mkConstScalarOp resTy ⟨0, sz'⟩) := by
        simp [mkMulSmartRvalue, mkConstScalarOp, operandConstScalar?, hSz]
      rw [hSimp, mkConstScalarOp, use_const_scalar_eval]
      exact ((const_annihilator_raw_eval locals ty0 tyL a sz' hSz mem localDecls layouts).2.2.2).symm
    · have hCond : (sz' != 0 && sz' == sz) = false := by
        cases h : (sz' != 0 && sz' == sz) with
        | false => rfl
        | true =>
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
          exact absurd h hC
      simp only [mkMulSmartRvalue, mkConstScalarOp, operandConstScalar?, hCond,
        Bool.false_eq_true, ↓reduceIte]

private theorem allOnesMask_ne_zero_of_succ (k : Nat) : allOnesMask (k + 1) ≠ 0 := by
  unfold allOnesMask
  rw [scalarModulus_eq_two_pow]
  have h1 : 1 ≤ (k + 1) * 8 := by omega
  have hPow : 2 ^ 1 ≤ 2 ^ ((k + 1) * 8) := Nat.pow_le_pow_right (by decide) h1
  omega

/-- **UNCONDITIONAL** `allOnes | rhs` soundness on unmodified `evalRvalue` for EVERY operand `rhs`
(dead/uninit/width-mismatched constant/same-width constant): width-mismatched constant pairs like
`allOnes_u32 | 0_u8` preserve `.unsupported`, non-constant `rhs` preserves dead/uninit `.ub`, and
same-width constants fold cleanly to `.use (const allOnes)`. -/
theorem mkBitOrSmartRvalue_allOnes_left_eq_raw (locals : List LocalSlot) (resTy ty0 : Ty)
    (rhs : Operand) (sz : Nat) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalue locals (mkBitOrSmartRvalue resTy (mkConstScalarOp ty0 ⟨allOnesMask sz, sz⟩) rhs)
        mem localDecls layouts =
      evalRvalue locals (.binaryOp .bitOr (mkConstScalarOp ty0 ⟨allOnesMask sz, sz⟩) rhs)
        mem localDecls layouts := by
  cases hR : operandConstScalar? rhs with
  | none =>
    cases sz with
    | zero =>
      unfold mkBitOrSmartRvalue; rw [hR]; rfl
    | succ k =>
      have hNe := allOnesMask_ne_zero_of_succ k
      unfold mkBitOrSmartRvalue; rw [hR]
      simp only [mkConstScalarOp, operandConstScalar?]
      cases hZ : allOnesMask (k + 1) with
      | zero => exact absurd hZ hNe
      | succ _ => rfl
  | some sc =>
    obtain ⟨tyR, rfl⟩ := operandConstScalar?_eq_some hR
    obtain ⟨b, sz'⟩ := sc
    by_cases hC : sz ≠ 0 ∧ sz = sz'
    · obtain ⟨hSz, rfl⟩ := hC
      have hSimp : mkBitOrSmartRvalue resTy (mkConstScalarOp ty0 ⟨allOnesMask sz, sz⟩)
          (.constant ⟨tyR, .scalar (.int ⟨b, sz⟩)⟩) =
          .use (mkConstScalarOp resTy ⟨allOnesMask sz, sz⟩) := by
        simp [mkBitOrSmartRvalue, mkConstScalarOp, operandConstScalar?, hSz]
      rw [hSimp, mkConstScalarOp, use_const_scalar_eval]
      exact ((const_bitOr_allOnes_raw_eval locals ty0 tyR b sz hSz mem localDecls layouts).1).symm
    · have hCond : (sz != 0 && sz == sz') = false := by
        cases h : (sz != 0 && sz == sz') with
        | false => rfl
        | true =>
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
          exact absurd h hC
      simp only [mkBitOrSmartRvalue, mkConstScalarOp, operandConstScalar?, hCond,
        Bool.false_eq_true, ↓reduceIte]

/-- **UNCONDITIONAL** `lhs | allOnes` soundness (symmetric to `mkBitOrSmartRvalue_allOnes_left_eq_raw`). -/
theorem mkBitOrSmartRvalue_allOnes_right_eq_raw (locals : List LocalSlot) (resTy ty0 : Ty)
    (lhs : Operand) (sz : Nat) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalue locals (mkBitOrSmartRvalue resTy lhs (mkConstScalarOp ty0 ⟨allOnesMask sz, sz⟩))
        mem localDecls layouts =
      evalRvalue locals (.binaryOp .bitOr lhs (mkConstScalarOp ty0 ⟨allOnesMask sz, sz⟩))
        mem localDecls layouts := by
  cases hL : operandConstScalar? lhs with
  | none =>
    cases sz with
    | zero =>
      unfold mkBitOrSmartRvalue; rw [hL]; rfl
    | succ k =>
      have hNe := allOnesMask_ne_zero_of_succ k
      unfold mkBitOrSmartRvalue; rw [hL]
      simp only [mkConstScalarOp, operandConstScalar?]
      cases hZ : allOnesMask (k + 1) with
      | zero => exact absurd hZ hNe
      | succ _ => rfl
  | some sc =>
    obtain ⟨tyL, rfl⟩ := operandConstScalar?_eq_some hL
    obtain ⟨a, sz'⟩ := sc
    by_cases hC : sz' ≠ 0 ∧ sz' = sz
    · obtain ⟨hSz, rfl⟩ := hC
      have hSimp : mkBitOrSmartRvalue resTy (.constant ⟨tyL, .scalar (.int ⟨a, sz'⟩)⟩)
          (mkConstScalarOp ty0 ⟨allOnesMask sz', sz'⟩) =
          .use (mkConstScalarOp resTy ⟨allOnesMask sz', sz'⟩) := by
        simp [mkBitOrSmartRvalue, mkConstScalarOp, operandConstScalar?, hSz]
      rw [hSimp, mkConstScalarOp, use_const_scalar_eval]
      exact ((const_bitOr_allOnes_raw_eval locals ty0 tyL a sz' hSz mem localDecls layouts).2).symm
    · have hCond : (sz' != 0 && sz' == sz) = false := by
        cases h : (sz' != 0 && sz' == sz) with
        | false => rfl
        | true =>
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
          exact absurd h hC
      simp only [mkBitOrSmartRvalue, mkConstScalarOp, operandConstScalar?, hCond,
        Bool.false_eq_true, ↓reduceIte]

/-- Exact UB-preserving soundness for `mkSubSmartRvalue` on `lhs - 0`. -/
theorem mkSubSmartRvalue_zero_right_eq_raw (locals locals' : List LocalSlot)
    (lhs : Operand) (ty0 : Ty) (sz : Nat) (sc : ScalarInt)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hDirect : isDirectOperand lhs)
    (hSz : sz ≠ 0) (hEqSz : sc.sizeBytes = sz)
    (hCanon : sc.bits < scalarModulus sz)
    (hEval : evalOperand locals lhs mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar sc) locals')
    (hVal : validateLoadedValue layouts localDecls lhs (.scalar sc) = true) :
    evalRvalue locals (mkSubSmartRvalue lhs (mkConstScalarOp ty0 ⟨0, sz⟩)) mem localDecls layouts =
      evalRvalue locals (.binaryOp .sub lhs (mkConstScalarOp ty0 ⟨0, sz⟩)) mem localDecls layouts := by
  have hNe0 : (sz == 0) = false := beq_false_of_ne hSz
  have hNz := nat_beq_zero_false hSz
  have hSimp : mkSubSmartRvalue lhs (mkConstScalarOp ty0 ⟨0, sz⟩) = .use lhs := by
    cases hL : operandConstScalar? lhs with
    | none =>
      unfold mkSubSmartRvalue; rw [hL]
      simp only [mkConstScalarOp, operandConstScalar?, hNe0, Bool.false_eq_true, ↓reduceIte]
    | some scL =>
      obtain ⟨tyL, rfl⟩ := operandConstScalar?_eq_some hL
      have hEqSc : scL = sc := by
        have hConst : evalOperand locals (.constant ⟨tyL, .scalar (.int scL)⟩)
            mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
            .ok (.scalar scL) locals := rfl
        rw [hConst] at hEval; cases hEval; rfl
      subst hEqSc
      cases scL with
      | mk bits sb =>
        simp only at hEqSz hCanon
        subst hEqSz
        simp [mkSubSmartRvalue, mkConstScalarOp, operandConstScalar?, hSz, hCanon]
  rw [hSimp, evalRvalue_use_direct locals locals' lhs mem localDecls layouts sc hDirect hEval hVal]
  have hConstEval : evalOperand locals' (.constant ⟨ty0, .scalar (.int ⟨0, sz⟩)⟩)
      mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar ⟨0, sz⟩) locals' := rfl
  simp only [evalRvalue, mkConstScalarOp, hEval, hConstEval]
  cases sc with
  | mk bits sb =>
    simp only at hEqSz hCanon
    subst hEqSz
    have hBle0 : Nat.ble 0 bits = true := rfl
    simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_sub_eq, Nat.sub_zero,
      hBle0, wrapScalarBits_of_lt hCanon]

/-- Exact UB-preserving soundness for `mkBitOrSmartRvalue` on `lhs | 0`. -/
theorem mkBitOrSmartRvalue_zero_right_eq_raw (locals locals' : List LocalSlot)
    (resTy ty0 : Ty) (lhs : Operand) (sz : Nat) (sc : ScalarInt)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hDirect : isDirectOperand lhs)
    (hSz : sz ≠ 0) (hEqSz : sc.sizeBytes = sz)
    (hCanon : sc.bits < scalarModulus sz)
    (hNotConst : operandConstScalar? lhs = none)
    (hEval : evalOperand locals lhs mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar sc) locals')
    (hVal : validateLoadedValue layouts localDecls lhs (.scalar sc) = true) :
    evalRvalue locals (mkBitOrSmartRvalue resTy lhs (mkConstScalarOp ty0 ⟨0, sz⟩)) mem localDecls layouts =
      evalRvalue locals (.binaryOp .bitOr lhs (mkConstScalarOp ty0 ⟨0, sz⟩)) mem localDecls layouts := by
  have hNe0 : (sz == 0) = false := beq_false_of_ne hSz
  have hNz := nat_beq_zero_false hSz
  have hModEq := scalarModulus_eq_two_pow sz
  unfold mkBitOrSmartRvalue
  rw [hNotConst]
  simp only [mkConstScalarOp, operandConstScalar?, hNe0, Bool.false_eq_true, ↓reduceIte]
  rw [evalRvalue_use_direct locals locals' lhs mem localDecls layouts sc hDirect hEval hVal]
  have hRhsConst : evalOperand locals' (.constant ⟨ty0, .scalar (.int ⟨0, sz⟩)⟩)
      mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar ⟨0, sz⟩) locals' := rfl
  simp only [evalRvalue, hEval, hRhsConst]
  cases sc with
  | mk bits sb =>
    simp only at hEqSz hCanon
    subst hEqSz
    simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq, bitwiseOrBits_zero_right, ← hModEq,
      Nat.mod_eq_of_lt hCanon]

/-- Exact UB-preserving soundness for `mkBitXorSmartRvalue` on `lhs ^ 0`. -/
theorem mkBitXorSmartRvalue_zero_right_eq_raw (locals locals' : List LocalSlot)
    (ty0 : Ty) (lhs : Operand) (sz : Nat) (sc : ScalarInt)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hDirect : isDirectOperand lhs)
    (hSz : sz ≠ 0) (hEqSz : sc.sizeBytes = sz)
    (hCanon : sc.bits < scalarModulus sz)
    (hNotConst : operandConstScalar? lhs = none)
    (hEval : evalOperand locals lhs mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar sc) locals')
    (hVal : validateLoadedValue layouts localDecls lhs (.scalar sc) = true) :
    evalRvalue locals (mkBitXorSmartRvalue lhs (mkConstScalarOp ty0 ⟨0, sz⟩)) mem localDecls layouts =
      evalRvalue locals (.binaryOp .bitXor lhs (mkConstScalarOp ty0 ⟨0, sz⟩)) mem localDecls layouts := by
  have hNe0 : (sz == 0) = false := beq_false_of_ne hSz
  have hNz := nat_beq_zero_false hSz
  have hModEq := scalarModulus_eq_two_pow sz
  unfold mkBitXorSmartRvalue
  rw [hNotConst]
  simp only [mkConstScalarOp, operandConstScalar?, hNe0, Bool.false_eq_true, ↓reduceIte]
  rw [evalRvalue_use_direct locals locals' lhs mem localDecls layouts sc hDirect hEval hVal]
  have hRhsConst : evalOperand locals' (.constant ⟨ty0, .scalar (.int ⟨0, sz⟩)⟩)
      mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar ⟨0, sz⟩) locals' := rfl
  simp only [evalRvalue, hEval, hRhsConst]
  cases sc with
  | mk bits sb =>
    simp only at hEqSz hCanon
    subst hEqSz
    simp only [evalScalarBinOp, hNz, Nat.beq_refl, nat_mul_eq, bitwiseXorBits_zero_right, ← hModEq,
      Nat.mod_eq_of_lt hCanon]

/-- Exact UB-preserving soundness for `mkShlSmartRvalue` on `lhs << 0`. -/
theorem mkShlSmartRvalue_zero_right_eq_raw (locals locals' : List LocalSlot)
    (ty0 : Ty) (lhs : Operand) (sz : Nat) (sc : ScalarInt)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hDirect : isDirectOperand lhs)
    (hSz : sz ≠ 0) (hScSz : sc.sizeBytes ≠ 0)
    (hCanon : sc.bits < scalarModulus sc.sizeBytes)
    (hEval : evalOperand locals lhs mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar sc) locals')
    (hVal : validateLoadedValue layouts localDecls lhs (.scalar sc) = true) :
    evalRvalue locals (mkShlSmartRvalue lhs (mkConstScalarOp ty0 ⟨0, sz⟩)) mem localDecls layouts =
      evalRvalue locals (.binaryOp .shl lhs (mkConstScalarOp ty0 ⟨0, sz⟩)) mem localDecls layouts := by
  have hNe0 : (sz == 0) = false := beq_false_of_ne hSz
  have hNzR := nat_beq_zero_false hSz
  have hNzL := nat_beq_zero_false hScSz
  have hSimp : mkShlSmartRvalue lhs (mkConstScalarOp ty0 ⟨0, sz⟩) = .use lhs := by
    cases hL : operandConstScalar? lhs with
    | none =>
      unfold mkShlSmartRvalue; rw [hL]
      simp only [mkConstScalarOp, operandConstScalar?, hNe0, Bool.false_eq_true, ↓reduceIte]
    | some scL =>
      obtain ⟨tyL, rfl⟩ := operandConstScalar?_eq_some hL
      have hEqSc : scL = sc := by
        have hConst : evalOperand locals (.constant ⟨tyL, .scalar (.int scL)⟩)
            mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
            .ok (.scalar scL) locals := rfl
        rw [hConst] at hEval; cases hEval; rfl
      subst hEqSc
      cases scL with
      | mk bits sb =>
        simp only at hScSz hCanon
        simp [mkShlSmartRvalue, mkConstScalarOp, operandConstScalar?, hScSz, hSz, hCanon]
  rw [hSimp, evalRvalue_use_direct locals locals' lhs mem localDecls layouts sc hDirect hEval hVal]
  have hRhsConst : evalOperand locals' (.constant ⟨ty0, .scalar (.int ⟨0, sz⟩)⟩)
      mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar ⟨0, sz⟩) locals' := rfl
  simp only [evalRvalue, mkConstScalarOp, hEval, hRhsConst]
  cases sc with
  | mk bits sb =>
    simp only at hNzL hCanon
    simp only [evalScalarBinOp, hNzL, hNzR, nat_mul_eq, nat_mod_eq, Nat.zero_mod,
      shiftLeftBits, scalarPow2, Nat.mul_one, wrapScalarBits_of_lt hCanon]

/-- Exact UB-preserving soundness for `mkShrSmartRvalue` on unsigned `lhs >> 0`. -/
theorem mkShrSmartRvalue_zero_right_eq_raw (locals locals' : List LocalSlot)
    (ty0 : Ty) (lhs : Operand) (sz : Nat) (sc : ScalarInt)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hDirect : isDirectOperand lhs)
    (hSz : sz ≠ 0) (hScSz : sc.sizeBytes ≠ 0)
    (hUnsigned : operandIsSigned localDecls lhs layouts = false)
    (hCanon : sc.bits < scalarModulus sc.sizeBytes)
    (hEval : evalOperand locals lhs mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar sc) locals')
    (hVal : validateLoadedValue layouts localDecls lhs (.scalar sc) = true) :
    evalRvalue locals (mkShrSmartRvalue lhs (mkConstScalarOp ty0 ⟨0, sz⟩)) mem localDecls layouts =
      evalRvalue locals (.binaryOp .shr lhs (mkConstScalarOp ty0 ⟨0, sz⟩)) mem localDecls layouts := by
  have hNe0 : (sz == 0) = false := beq_false_of_ne hSz
  have hNzR := nat_beq_zero_false hSz
  have hNzL := nat_beq_zero_false hScSz
  have hSimp : mkShrSmartRvalue lhs (mkConstScalarOp ty0 ⟨0, sz⟩) = .use lhs := by
    cases hL : operandConstScalar? lhs with
    | none =>
      unfold mkShrSmartRvalue; rw [hL]
      simp only [mkConstScalarOp, operandConstScalar?, hNe0, Bool.false_eq_true, ↓reduceIte]
    | some scL =>
      obtain ⟨tyL, rfl⟩ := operandConstScalar?_eq_some hL
      have hEqSc : scL = sc := by
        have hConst : evalOperand locals (.constant ⟨tyL, .scalar (.int scL)⟩)
            mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
            .ok (.scalar scL) locals := rfl
        rw [hConst] at hEval; cases hEval; rfl
      subst hEqSc
      cases scL with
      | mk bits sb =>
        simp only at hScSz hCanon
        simp [mkShrSmartRvalue, mkConstScalarOp, operandConstScalar?, hScSz, hSz, hCanon]
  rw [hSimp, evalRvalue_use_direct locals locals' lhs mem localDecls layouts sc hDirect hEval hVal]
  have hRhsConst : evalOperand locals' (.constant ⟨ty0, .scalar (.int ⟨0, sz⟩)⟩)
      mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar ⟨0, sz⟩) locals' := rfl
  simp only [evalRvalue, mkConstScalarOp, hEval, hRhsConst, hUnsigned]
  cases sc with
  | mk bits sb =>
    simp only at hNzL hCanon
    simp only [evalScalarBinOp, hNzL, hNzR, nat_mul_eq, nat_mod_eq, nat_div_eq, Nat.zero_mod,
      shiftRightUnsignedBits, scalarPow2, Nat.div_one, wrapScalarBits_of_lt hCanon]

/-! ### B.4b. Unconditional Universal UB-Preservation Across ALL 8 `mk*SmartRvalue` Constructors -/

private theorem evalScalarBinOp_wrapping_ne_ub {op : BinOp}
    (hSafe : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .bitAnd ∨
      op = .bitOr ∨ op = .bitXor ∨ op = .shl ∨ op = .shr)
    (lhs rhs : ScalarInt) (locals : List LocalSlot) (mem : Memory) (isSigned : Bool) :
    evalScalarBinOp op lhs rhs locals mem isSigned ≠ .ub := by
  intro hUb
  unfold evalScalarBinOp at hUb
  cases hL0 : Nat.beq lhs.sizeBytes 0 with
  | true => rw [hL0] at hUb; cases hUb
  | false =>
    rw [hL0] at hUb; dsimp only at hUb
    rcases hSafe with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · cases hEq : Nat.beq lhs.sizeBytes rhs.sizeBytes <;> rw [hEq] at hUb <;> cases hUb
    · cases hEq : Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rw [hEq] at hUb; cases hUb
      | true =>
        rw [hEq] at hUb; dsimp only at hUb
        cases hLe : Nat.ble rhs.bits lhs.bits <;> rw [hLe] at hUb <;> cases hUb
    · cases hEq : Nat.beq lhs.sizeBytes rhs.sizeBytes <;> rw [hEq] at hUb <;> cases hUb
    · cases hEq : Nat.beq lhs.sizeBytes rhs.sizeBytes <;> rw [hEq] at hUb <;> cases hUb
    · cases hEq : Nat.beq lhs.sizeBytes rhs.sizeBytes <;> rw [hEq] at hUb <;> cases hUb
    · cases hEq : Nat.beq lhs.sizeBytes rhs.sizeBytes <;> rw [hEq] at hUb <;> cases hUb
    · cases hR0 : Nat.beq rhs.sizeBytes 0 <;> rw [hR0] at hUb <;> cases hUb
    · cases hR0 : Nat.beq rhs.sizeBytes 0 <;> rw [hR0] at hUb <;> cases hUb

private theorem isPtrRelationalBinOp_wrapping_false {op : BinOp}
    (hSafe : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .bitAnd ∨
      op = .bitOr ∨ op = .bitXor ∨ op = .shl ∨ op = .shr)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (lhs rhs : Operand) :
    isPtrRelationalBinOp op localDecls layouts lhs rhs = false := by
  rcases hSafe with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem evalWidePtrAggregateRelBinOp_wrapping_unsupported {op : BinOp}
    (hSafe : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .bitAnd ∨
      op = .bitOr ∨ op = .bitXor ∨ op = .shl ∨ op = .shr)
    (lhs : Operand) (lv : Nat) (lf : List Value) (rv : Nat) (rf : List Value)
    (locals : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalWidePtrAggregateRelBinOp op lhs lv lf rv rf locals mem localDecls layouts = .unsupported := by
  unfold evalWidePtrAggregateRelBinOp
  rcases hSafe with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (split <;> rfl)

private theorem evalRvalue_binaryOp_ub_operand {op : BinOp}
    (hSafe : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .bitAnd ∨
      op = .bitOr ∨ op = .bitXor ∨ op = .shl ∨ op = .shr)
    (locals : List LocalSlot) (lhs rhs : Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hUb : evalRvalue locals (.binaryOp op lhs rhs) mem localDecls layouts = .ub) :
    evalOperand locals lhs mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack = .ub ∨
    ∃ v1 locals₁,
      evalOperand locals lhs mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
        .ok v1 locals₁ ∧
      evalOperand locals₁ rhs mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack = .ub := by
  simp only [evalRvalue] at hUb
  cases hL : evalOperand locals lhs mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
  | ub => exact Or.inl rfl
  | unsupported => rw [hL] at hUb; cases hUb
  | ok v1 locals₁ =>
    rw [hL] at hUb; dsimp only at hUb
    cases hR : evalOperand locals₁ rhs mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
    | ub => exact Or.inr ⟨v1, locals₁, rfl, hR⟩
    | unsupported => rw [hR] at hUb; cases hUb
    | ok v2 locals₂ =>
      rw [hR] at hUb; dsimp only at hUb
      have hNotRel := isPtrRelationalBinOp_wrapping_false hSafe localDecls layouts lhs rhs
      have hAgg := evalWidePtrAggregateRelBinOp_wrapping_unsupported hSafe
      cases v1 <;> cases v2 <;>
        rcases hSafe with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (dsimp only at hUb;
         first
         | exact False.elim (evalScalarBinOp_wrapping_ne_ub (by simp) _ _ _ _ _ hUb)
         | (rw [hNotRel] at hUb; cases hUb)
         | (rw [hAgg] at hUb; cases hUb)
         | cases hUb)

private theorem evalRvalue_ub_of_const_lhs {op : BinOp}
    (hSafe : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .bitAnd ∨
      op = .bitOr ∨ op = .bitXor ∨ op = .shl ∨ op = .shr)
    (locals : List LocalSlot) (ty : Ty) (sc : ScalarInt) (rhs : Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hUb : evalRvalue locals (.binaryOp op (.constant ⟨ty, .scalar (.int sc)⟩) rhs) mem localDecls layouts = .ub) :
    evalRvalue locals (.use rhs) mem localDecls layouts = .ub := by
  have hOp := evalRvalue_binaryOp_ub_operand hSafe locals (.constant ⟨ty, .scalar (.int sc)⟩) rhs mem localDecls layouts hUb
  have hConst : evalOperand locals (.constant ⟨ty, .scalar (.int sc)⟩) mem.borrows mem.globals layouts
      mem.callerLocals localDecls mem.callStack = .ok (.scalar sc) locals := rfl
  rcases hOp with hL | ⟨_, _, hL, hR⟩
  · rw [hConst] at hL; cases hL
  · rw [hConst] at hL; cases hL
    simp only [evalRvalue, hR]

private theorem evalRvalue_ub_of_const_rhs {op : BinOp}
    (hSafe : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .bitAnd ∨
      op = .bitOr ∨ op = .bitXor ∨ op = .shl ∨ op = .shr)
    (locals : List LocalSlot) (lhs : Operand) (ty : Ty) (sc : ScalarInt)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hUb : evalRvalue locals (.binaryOp op lhs (.constant ⟨ty, .scalar (.int sc)⟩)) mem localDecls layouts = .ub) :
    evalRvalue locals (.use lhs) mem localDecls layouts = .ub := by
  have hOp := evalRvalue_binaryOp_ub_operand hSafe locals lhs (.constant ⟨ty, .scalar (.int sc)⟩) mem localDecls layouts hUb
  rcases hOp with hL | ⟨_, locals₁, _, hR⟩
  · simp only [evalRvalue, hL]
  · have hConst : evalOperand locals₁ (.constant ⟨ty, .scalar (.int sc)⟩) mem.borrows mem.globals layouts
        mem.callerLocals localDecls mem.callStack = .ok (.scalar sc) locals₁ := rfl
    rw [hConst] at hR; cases hR

private theorem evalRvalue_binaryOp_const_const_ne_ub {op : BinOp}
    (hSafe : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .bitAnd ∨
      op = .bitOr ∨ op = .bitXor ∨ op = .shl ∨ op = .shr)
    (locals : List LocalSlot) (ty1 ty2 : Ty) (sc1 sc2 : ScalarInt)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalue locals (.binaryOp op (.constant ⟨ty1, .scalar (.int sc1)⟩)
      (.constant ⟨ty2, .scalar (.int sc2)⟩)) mem localDecls layouts ≠ .ub := by
  intro hUb
  have hOp := evalRvalue_binaryOp_ub_operand hSafe locals
    (.constant ⟨ty1, .scalar (.int sc1)⟩) (.constant ⟨ty2, .scalar (.int sc2)⟩)
    mem localDecls layouts hUb
  rcases hOp with hL | ⟨_, locals₁, _, hR⟩
  · cases hL
  · cases hR

/-- **UNCONDITIONAL UNIVERSAL UB-PRESERVATION ACROSS ALL 8 `mk*SmartRvalue` CONSTRUCTORS**:
For EVERY `locals`, `resTy`, `lhs`, `rhs`, `mem`, `localDecls`, `layouts`, ZERO hypotheses on
definedness/width/types: if unmodified `Trusted.MirSemantics.evalRvalue` on the raw `.binaryOp`
faults with `.ub`, then `evalRvalue` on the smart-constructed `Rvalue` ALSO faults with `.ub`!
Not one of the 8 `Bitprism` MIR smart constructors can EVER erase UB! -/
theorem mkSmartRvalue_never_erases_ub (locals : List LocalSlot) (resTy : Ty)
    (lhs rhs : Operand) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    (evalRvalue locals (.binaryOp .add lhs rhs) mem localDecls layouts = .ub →
      evalRvalue locals (mkAddSmartRvalue lhs rhs) mem localDecls layouts = .ub) ∧
    (evalRvalue locals (.binaryOp .sub lhs rhs) mem localDecls layouts = .ub →
      evalRvalue locals (mkSubSmartRvalue lhs rhs) mem localDecls layouts = .ub) ∧
    (evalRvalue locals (.binaryOp .mul lhs rhs) mem localDecls layouts = .ub →
      evalRvalue locals (mkMulSmartRvalue resTy lhs rhs) mem localDecls layouts = .ub) ∧
    (evalRvalue locals (.binaryOp .bitAnd lhs rhs) mem localDecls layouts = .ub →
      evalRvalue locals (mkBitAndSmartRvalue resTy lhs rhs) mem localDecls layouts = .ub) ∧
    (evalRvalue locals (.binaryOp .bitOr lhs rhs) mem localDecls layouts = .ub →
      evalRvalue locals (mkBitOrSmartRvalue resTy lhs rhs) mem localDecls layouts = .ub) ∧
    (evalRvalue locals (.binaryOp .bitXor lhs rhs) mem localDecls layouts = .ub →
      evalRvalue locals (mkBitXorSmartRvalue lhs rhs) mem localDecls layouts = .ub) ∧
    (evalRvalue locals (.binaryOp .shl lhs rhs) mem localDecls layouts = .ub →
      evalRvalue locals (mkShlSmartRvalue lhs rhs) mem localDecls layouts = .ub) ∧
    (evalRvalue locals (.binaryOp .shr lhs rhs) mem localDecls layouts = .ub →
      evalRvalue locals (mkShrSmartRvalue lhs rhs) mem localDecls layouts = .ub) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hUb
    cases hL : operandConstScalar? lhs with
    | none =>
      cases hR : operandConstScalar? rhs with
      | none => simp only [mkAddSmartRvalue, hL, hR]; exact hUb
      | some scR =>
        obtain ⟨tyR, rfl⟩ := operandConstScalar?_eq_some hR
        rcases scR with ⟨b, sz⟩
        cases b with
        | zero =>
          simp only [mkAddSmartRvalue, hL, hR]; split
          · exact hUb
          · exact evalRvalue_ub_of_const_rhs (Or.inl rfl) locals lhs tyR ⟨0, sz⟩ mem localDecls layouts hUb
        | succ _ => simp only [mkAddSmartRvalue, hL, hR]; exact hUb
    | some scL =>
      obtain ⟨tyL, rfl⟩ := operandConstScalar?_eq_some hL
      cases hR : operandConstScalar? rhs with
      | some scR =>
        obtain ⟨tyR, rfl⟩ := operandConstScalar?_eq_some hR
        exact False.elim (evalRvalue_binaryOp_const_const_ne_ub (Or.inl rfl) locals tyL tyR scL scR mem localDecls layouts hUb)
      | none =>
        rcases scL with ⟨a, sz⟩
        cases a with
        | zero =>
          simp only [mkAddSmartRvalue, hL, hR]; split
          · exact hUb
          · exact evalRvalue_ub_of_const_lhs (Or.inl rfl) locals tyL ⟨0, sz⟩ rhs mem localDecls layouts hUb
        | succ _ => simp only [mkAddSmartRvalue, hL, hR]; exact hUb
  · intro hUb
    cases hL : operandConstScalar? lhs with
    | none =>
      cases hR : operandConstScalar? rhs with
      | none => simp only [mkSubSmartRvalue, hL, hR]; exact hUb
      | some scR =>
        obtain ⟨tyR, rfl⟩ := operandConstScalar?_eq_some hR
        rcases scR with ⟨b, sz⟩
        cases b with
        | zero =>
          simp only [mkSubSmartRvalue, hL, hR]; split
          · exact hUb
          · exact evalRvalue_ub_of_const_rhs (Or.inr (Or.inl rfl)) locals lhs tyR ⟨0, sz⟩ mem localDecls layouts hUb
        | succ _ => simp only [mkSubSmartRvalue, hL, hR]; exact hUb
    | some scL =>
      obtain ⟨tyL, rfl⟩ := operandConstScalar?_eq_some hL
      cases hR : operandConstScalar? rhs with
      | some scR =>
        obtain ⟨tyR, rfl⟩ := operandConstScalar?_eq_some hR
        exact False.elim (evalRvalue_binaryOp_const_const_ne_ub (Or.inr (Or.inl rfl)) locals tyL tyR scL scR mem localDecls layouts hUb)
      | none => simp only [mkSubSmartRvalue, hL, hR]; exact hUb
  · intro hUb
    cases hL : operandConstScalar? lhs with
    | none =>
      cases hR : operandConstScalar? rhs with
      | none => simp only [mkMulSmartRvalue, hL, hR]; exact hUb
      | some scR =>
        obtain ⟨tyR, rfl⟩ := operandConstScalar?_eq_some hR
        rcases scR with ⟨b, sz⟩
        cases b with
        | zero => simp only [mkMulSmartRvalue, hL, hR]; exact hUb
        | succ b' =>
          cases b' with
          | zero =>
            simp only [mkMulSmartRvalue, hL, hR]; split
            · exact hUb
            · exact evalRvalue_ub_of_const_rhs (by simp) locals lhs tyR ⟨1, sz⟩ mem localDecls layouts hUb
          | succ _ => simp only [mkMulSmartRvalue, hL, hR]; exact hUb
    | some scL =>
      obtain ⟨tyL, rfl⟩ := operandConstScalar?_eq_some hL
      cases hR : operandConstScalar? rhs with
      | some scR =>
        obtain ⟨tyR, rfl⟩ := operandConstScalar?_eq_some hR
        exact False.elim (evalRvalue_binaryOp_const_const_ne_ub (by simp) locals tyL tyR scL scR mem localDecls layouts hUb)
      | none =>
        rcases scL with ⟨a, sz⟩
        cases a with
        | zero => simp only [mkMulSmartRvalue, hL, hR]; exact hUb
        | succ a' =>
          cases a' with
          | zero =>
            simp only [mkMulSmartRvalue, hL, hR]; split
            · exact hUb
            · exact evalRvalue_ub_of_const_lhs (by simp) locals tyL ⟨1, sz⟩ rhs mem localDecls layouts hUb
          | succ _ => simp only [mkMulSmartRvalue, hL, hR]; exact hUb
  · intro hUb
    cases hL : operandConstScalar? lhs with
    | none =>
      cases hR : operandConstScalar? rhs with
      | none => simp only [mkBitAndSmartRvalue, hL, hR]; exact hUb
      | some scR =>
        obtain ⟨tyR, rfl⟩ := operandConstScalar?_eq_some hR
        rcases scR with ⟨b, sz⟩
        cases b with
        | zero => simp only [mkBitAndSmartRvalue, hL, hR]; exact hUb
        | succ b' =>
          simp only [mkBitAndSmartRvalue, hL, hR]; split
          · exact evalRvalue_ub_of_const_rhs (by simp) locals lhs tyR ⟨b' + 1, sz⟩ mem localDecls layouts hUb
          · exact hUb
    | some scL =>
      obtain ⟨tyL, rfl⟩ := operandConstScalar?_eq_some hL
      cases hR : operandConstScalar? rhs with
      | some scR =>
        obtain ⟨tyR, rfl⟩ := operandConstScalar?_eq_some hR
        exact False.elim (evalRvalue_binaryOp_const_const_ne_ub (by simp) locals tyL tyR scL scR mem localDecls layouts hUb)
      | none =>
        rcases scL with ⟨a, sz⟩
        cases a with
        | zero => simp only [mkBitAndSmartRvalue, hL, hR]; exact hUb
        | succ a' =>
          simp only [mkBitAndSmartRvalue, hL, hR]; split
          · exact evalRvalue_ub_of_const_lhs (by simp) locals tyL ⟨a' + 1, sz⟩ rhs mem localDecls layouts hUb
          · exact hUb
  · intro hUb
    cases hL : operandConstScalar? lhs with
    | none =>
      cases hR : operandConstScalar? rhs with
      | none => simp only [mkBitOrSmartRvalue, hL, hR]; exact hUb
      | some scR =>
        obtain ⟨tyR, rfl⟩ := operandConstScalar?_eq_some hR
        rcases scR with ⟨b, sz⟩
        cases b with
        | zero =>
          simp only [mkBitOrSmartRvalue, hL, hR]; split
          · exact hUb
          · exact evalRvalue_ub_of_const_rhs (by simp) locals lhs tyR ⟨0, sz⟩ mem localDecls layouts hUb
        | succ _ => simp only [mkBitOrSmartRvalue, hL, hR]; exact hUb
    | some scL =>
      obtain ⟨tyL, rfl⟩ := operandConstScalar?_eq_some hL
      cases hR : operandConstScalar? rhs with
      | some scR =>
        obtain ⟨tyR, rfl⟩ := operandConstScalar?_eq_some hR
        exact False.elim (evalRvalue_binaryOp_const_const_ne_ub (by simp) locals tyL tyR scL scR mem localDecls layouts hUb)
      | none =>
        rcases scL with ⟨a, sz⟩
        cases a with
        | zero =>
          simp only [mkBitOrSmartRvalue, hL, hR]; split
          · exact hUb
          · exact evalRvalue_ub_of_const_lhs (by simp) locals tyL ⟨0, sz⟩ rhs mem localDecls layouts hUb
        | succ _ => simp only [mkBitOrSmartRvalue, hL, hR]; exact hUb
  · intro hUb
    cases hL : operandConstScalar? lhs with
    | none =>
      cases hR : operandConstScalar? rhs with
      | none => simp only [mkBitXorSmartRvalue, hL, hR]; exact hUb
      | some scR =>
        obtain ⟨tyR, rfl⟩ := operandConstScalar?_eq_some hR
        rcases scR with ⟨b, sz⟩
        cases b with
        | zero =>
          simp only [mkBitXorSmartRvalue, hL, hR]; split
          · exact hUb
          · exact evalRvalue_ub_of_const_rhs (by simp) locals lhs tyR ⟨0, sz⟩ mem localDecls layouts hUb
        | succ _ => simp only [mkBitXorSmartRvalue, hL, hR]; exact hUb
    | some scL =>
      obtain ⟨tyL, rfl⟩ := operandConstScalar?_eq_some hL
      cases hR : operandConstScalar? rhs with
      | some scR =>
        obtain ⟨tyR, rfl⟩ := operandConstScalar?_eq_some hR
        exact False.elim (evalRvalue_binaryOp_const_const_ne_ub (by simp) locals tyL tyR scL scR mem localDecls layouts hUb)
      | none =>
        rcases scL with ⟨a, sz⟩
        cases a with
        | zero =>
          simp only [mkBitXorSmartRvalue, hL, hR]; split
          · exact hUb
          · exact evalRvalue_ub_of_const_lhs (by simp) locals tyL ⟨0, sz⟩ rhs mem localDecls layouts hUb
        | succ _ => simp only [mkBitXorSmartRvalue, hL, hR]; exact hUb
  · intro hUb
    cases hL : operandConstScalar? lhs with
    | none =>
      cases hR : operandConstScalar? rhs with
      | none => simp only [mkShlSmartRvalue, hL, hR]; exact hUb
      | some scR =>
        obtain ⟨tyR, rfl⟩ := operandConstScalar?_eq_some hR
        rcases scR with ⟨b, sz⟩
        cases b with
        | zero =>
          simp only [mkShlSmartRvalue, hL, hR]; split
          · exact hUb
          · exact evalRvalue_ub_of_const_rhs (by simp) locals lhs tyR ⟨0, sz⟩ mem localDecls layouts hUb
        | succ _ => simp only [mkShlSmartRvalue, hL, hR]; exact hUb
    | some scL =>
      obtain ⟨tyL, rfl⟩ := operandConstScalar?_eq_some hL
      cases hR : operandConstScalar? rhs with
      | some scR =>
        obtain ⟨tyR, rfl⟩ := operandConstScalar?_eq_some hR
        exact False.elim (evalRvalue_binaryOp_const_const_ne_ub (by simp) locals tyL tyR scL scR mem localDecls layouts hUb)
      | none => simp only [mkShlSmartRvalue, hL, hR]; exact hUb
  · intro hUb
    cases hL : operandConstScalar? lhs with
    | none =>
      cases hR : operandConstScalar? rhs with
      | none => simp only [mkShrSmartRvalue, hL, hR]; exact hUb
      | some scR =>
        obtain ⟨tyR, rfl⟩ := operandConstScalar?_eq_some hR
        rcases scR with ⟨b, sz⟩
        cases b with
        | zero =>
          simp only [mkShrSmartRvalue, hL, hR]; split
          · exact hUb
          · exact evalRvalue_ub_of_const_rhs (by simp) locals lhs tyR ⟨0, sz⟩ mem localDecls layouts hUb
        | succ _ => simp only [mkShrSmartRvalue, hL, hR]; exact hUb
    | some scL =>
      obtain ⟨tyL, rfl⟩ := operandConstScalar?_eq_some hL
      cases hR : operandConstScalar? rhs with
      | some scR =>
        obtain ⟨tyR, rfl⟩ := operandConstScalar?_eq_some hR
        exact False.elim (evalRvalue_binaryOp_const_const_ne_ub (by simp) locals tyL tyR scL scR mem localDecls layouts hUb)
      | none => simp only [mkShrSmartRvalue, hL, hR]; exact hUb

/-! ### B.5. Negative Non-Erasure Refutation Theorems (Proving Preconditions Are Essential!) -/

/-- Canonical `u32` constant operand helper for negative UB-preservation witnesses. -/
def cU32Ty : Ty := ⟨.uint .u32, 0⟩
def cU8Ty : Ty := ⟨.uint .u8, 0⟩

/-- **Non-erasure witness #1 (`0 & dead`)**: reading a `.dead` local in `0 & _1` faults with `.ub`
on unmodified `Trusted.MirSemantics.evalRvalue`, and the `Bitprism` smart constructor PRESERVES that
UB (it refuses to drop the non-constant operand), whereas the NAIVE annihilator rewrite
`.use (const 0)` would unsoundly succeed with `.ok (.scalar ⟨0, 4⟩)`. -/
theorem bitAnd_zero_dead_local_preserves_ub :
    let locals : List LocalSlot := [.uninit, .dead]
    let rawRv := Rvalue.binaryOp .bitAnd (mkConstScalarOp cU32Ty ⟨0, 4⟩) (.copy ⟨1, []⟩)
    let simpRv := mkBitAndSmartRvalue cU32Ty (mkConstScalarOp cU32Ty ⟨0, 4⟩) (.copy ⟨1, []⟩)
    let naiveRv := Rvalue.use (mkConstScalarOp cU32Ty ⟨0, 4⟩)
    evalRvalue locals rawRv = .ub ∧
    evalRvalue locals simpRv = .ub ∧
    evalRvalue locals naiveRv = .ok (.scalar ⟨0, 4⟩) locals emptyMemory ∧
    evalRvalue locals simpRv ≠ evalRvalue locals naiveRv := by
  refine ⟨rfl, rfl, rfl, fun h => by cases h⟩

/-- **Non-erasure witness #2 (`0 & uninit`)**: the smart constructor preserves the `.ub` of reading
an `.uninit` local, unlike the naive `.use (const 0)` rewrite. -/
theorem bitAnd_zero_uninit_local_preserves_ub :
    let locals : List LocalSlot := [.uninit, .uninit]
    let rawRv := Rvalue.binaryOp .bitAnd (mkConstScalarOp cU32Ty ⟨0, 4⟩) (.copy ⟨1, []⟩)
    let simpRv := mkBitAndSmartRvalue cU32Ty (mkConstScalarOp cU32Ty ⟨0, 4⟩) (.copy ⟨1, []⟩)
    let naiveRv := Rvalue.use (mkConstScalarOp cU32Ty ⟨0, 4⟩)
    evalRvalue locals rawRv = .ub ∧
    evalRvalue locals simpRv = .ub ∧
    evalRvalue locals naiveRv = .ok (.scalar ⟨0, 4⟩) locals emptyMemory ∧
    evalRvalue locals simpRv ≠ evalRvalue locals naiveRv := by
  refine ⟨rfl, rfl, rfl, fun h => by cases h⟩

/-- **Non-erasure witness #3 (`uninit * 0`)**: the smart constructor preserves the `.ub` of
multiplying an `.uninit` local by `0`, unlike the naive `.use (const 0)` rewrite. -/
theorem mul_zero_uninit_local_preserves_ub :
    let locals : List LocalSlot := [.uninit, .uninit]
    let rawRv := Rvalue.binaryOp .mul (.copy ⟨1, []⟩) (mkConstScalarOp cU32Ty ⟨0, 4⟩)
    let simpRv := mkMulSmartRvalue cU32Ty (.copy ⟨1, []⟩) (mkConstScalarOp cU32Ty ⟨0, 4⟩)
    let naiveRv := Rvalue.use (mkConstScalarOp cU32Ty ⟨0, 4⟩)
    evalRvalue locals rawRv = .ub ∧
    evalRvalue locals simpRv = .ub ∧
    evalRvalue locals naiveRv = .ok (.scalar ⟨0, 4⟩) locals emptyMemory ∧
    evalRvalue locals simpRv ≠ evalRvalue locals naiveRv := by
  refine ⟨rfl, rfl, rfl, fun h => by cases h⟩

/-- **Non-erasure witness #4 (`allOnes | uninit`)**: `mkBitOrSmartRvalue` preserves the `.ub` of
OR-ing `u32::MAX` with an `.uninit` local, unlike the naive `.use (const allOnes)` rewrite. -/
theorem bitOr_allOnes_uninit_local_preserves_ub :
    let locals : List LocalSlot := [.uninit, .uninit]
    let allOnes := mkConstScalarOp cU32Ty ⟨allOnesMask 4, 4⟩
    let rawRv := Rvalue.binaryOp .bitOr allOnes (.copy ⟨1, []⟩)
    let simpRv := mkBitOrSmartRvalue cU32Ty allOnes (.copy ⟨1, []⟩)
    let naiveRv := Rvalue.use allOnes
    evalRvalue locals rawRv = .ub ∧
    evalRvalue locals simpRv = .ub ∧
    evalRvalue locals naiveRv = .ok (.scalar ⟨allOnesMask 4, 4⟩) locals emptyMemory ∧
    evalRvalue locals simpRv ≠ evalRvalue locals naiveRv := by
  refine ⟨rfl, rfl, rfl, fun h => by cases h⟩

/-- **Identity-arm precondition necessity witness**: proves explicitly why `hEqSz` (width agreement)
and `hCanon` (canonicity `< scalarModulus sz`) are strictly necessary on single-sided identity
rewrites (`x + 0`) over untyped `MirAst.Operand`s:
1. Width mismatch: `_1 + 0_u32` where `_1` holds `5_u8` returns `.unsupported` on raw `.binaryOp`,
   whereas `.use _1` returns `.ok (5_u8)`.
2. Non-canonical bits: `_1 + 0_u8` where `_1` holds unwrapped `256_u8` returns `.ok (0_u8)` on raw
   `.binaryOp`, whereas `.use _1` returns `.ok (256_u8)`.
(Note that UB is still NEVER erased: `mkSmartRvalue_never_erases_ub` holds unconditionally!) -/
theorem bitprism_identity_preconditions_necessary :
    let locsMismatch : List LocalSlot := [.uninit, .init (.scalar ⟨5, 1⟩)]
    let locsNonCanon : List LocalSlot := [.uninit, .init (.scalar ⟨256, 1⟩)]
    evalRvalue locsMismatch (.binaryOp .add (.copy ⟨1, []⟩) (mkConstScalarOp cU32Ty ⟨0, 4⟩)) =
      .unsupported ∧
    evalRvalue locsMismatch (mkAddSmartRvalue (.copy ⟨1, []⟩) (mkConstScalarOp cU32Ty ⟨0, 4⟩)) =
      .ok (.scalar ⟨5, 1⟩) locsMismatch emptyMemory ∧
    evalRvalue locsNonCanon (.binaryOp .add (.copy ⟨1, []⟩) (mkConstScalarOp cU8Ty ⟨0, 1⟩)) =
      .ok (.scalar ⟨0, 1⟩) locsNonCanon emptyMemory ∧
    evalRvalue locsNonCanon (mkAddSmartRvalue (.copy ⟨1, []⟩) (mkConstScalarOp cU8Ty ⟨0, 1⟩)) =
      .ok (.scalar ⟨256, 1⟩) locsNonCanon emptyMemory := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- **Forward `.ok` refinement for `mkAddSmartRvalue` on `lhs + 0`**: whenever raw
`evalRvalue locals (.binaryOp .add lhs (const ⟨0, sz⟩))` succeeds with `.ok v locals' mem`
(automatically witnessing `sz ≠ 0` and width match `sc.sizeBytes = sz`!), if `lhs` is direct,
validated, and canonical (`< scalarModulus sz`), then `mkAddSmartRvalue` produces the EXACT same
`.ok v locals' mem`! -/
theorem mkAddSmartRvalue_ok_of_raw_ok (locals locals' : List LocalSlot)
    (lhs : Operand) (ty0 : Ty) (sz : Nat) (v : Value) (mem mem' : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hDirect : isDirectOperand lhs)
    (hRaw : evalRvalue locals (.binaryOp .add lhs (mkConstScalarOp ty0 ⟨0, sz⟩)) mem localDecls layouts =
      .ok v locals' mem')
    (hVal : validateLoadedValue layouts localDecls lhs v = true)
    (hLhsCanon : ∀ scL, evalOperand locals lhs mem.borrows mem.globals layouts mem.callerLocals
      localDecls mem.callStack = .ok (.scalar scL) locals' → scL.bits < scalarModulus sz) :
    evalRvalue locals (mkAddSmartRvalue lhs (mkConstScalarOp ty0 ⟨0, sz⟩)) mem localDecls layouts =
      .ok v locals' mem' := by
  have hRaw' := hRaw
  simp only [evalRvalue, mkConstScalarOp] at hRaw'
  cases hL : evalOperand locals lhs mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
  | ub => rw [hL] at hRaw'; cases hRaw'
  | unsupported => rw [hL] at hRaw'; cases hRaw'
  | ok lv locs₁ =>
    rw [hL] at hRaw'; dsimp only at hRaw'
    have hRConst : evalOperand locs₁ (.constant ⟨ty0, .scalar (.int ⟨0, sz⟩)⟩) mem.borrows mem.globals
        layouts mem.callerLocals localDecls mem.callStack = .ok (.scalar ⟨0, sz⟩) locs₁ := rfl
    rw [hRConst] at hRaw'; dsimp only at hRaw'
    cases lv with
    | scalar sc =>
      dsimp only at hRaw'
      unfold evalScalarBinOp at hRaw'
      cases hSz0 : Nat.beq sc.sizeBytes 0 with
      | true => rw [hSz0] at hRaw'; cases hRaw'
      | false =>
        rw [hSz0] at hRaw'; dsimp only at hRaw'
        cases hEqSz : Nat.beq sc.sizeBytes sz with
        | false => rw [hEqSz] at hRaw'; cases hRaw'
        | true =>
          rw [hEqSz] at hRaw'; dsimp only at hRaw'
          have hSzEq : sc.sizeBytes = sz := Nat.eq_of_beq_eq_true hEqSz
          have hSzNe : sz ≠ 0 := by
            intro h0; subst h0; rw [hSzEq] at hSz0; cases hSz0
          cases hRaw'
          have hScCanon : sc.bits < scalarModulus sz := hLhsCanon sc hL
          have hWrap : wrapScalarBits (Nat.add sc.bits 0) (scalarModulus sc.sizeBytes) = sc.bits := by
            rw [hSzEq, nat_add_eq, Nat.add_zero, wrapScalarBits_of_lt hScCanon]
          have hEqVal : Value.scalar ⟨wrapScalarBits (Nat.add sc.bits 0) (scalarModulus sc.sizeBytes), sc.sizeBytes⟩ =
              Value.scalar sc := by
            cases sc; simp only at hWrap; rw [hWrap]
          rw [hEqVal] at hVal ⊢
          cases hC : operandConstScalar? lhs with
          | none =>
            have hNe0 : (sz == 0) = false := beq_false_of_ne hSzNe
            have hSimp : mkAddSmartRvalue lhs (mkConstScalarOp ty0 ⟨0, sz⟩) = .use lhs := by
              unfold mkAddSmartRvalue; rw [hC]
              simp only [mkConstScalarOp, operandConstScalar?, hNe0, Bool.false_eq_true, ↓reduceIte]
            rw [hSimp]
            exact evalRvalue_use_direct locals locals' lhs mem localDecls layouts sc hDirect hL hVal
          | some sc0 =>
            obtain ⟨tyL, rfl⟩ := operandConstScalar?_eq_some hC
            have hConstL : evalOperand locals (.constant ⟨tyL, .scalar (.int sc0)⟩) mem.borrows mem.globals
                layouts mem.callerLocals localDecls mem.callStack = .ok (.scalar sc0) locals := rfl
            rw [hConstL] at hL; cases hL
            rcases sc with ⟨a, sb⟩
            simp only at hSzEq hScCanon
            subst hSzEq
            by_cases hA0 : a = 0
            · subst hA0
              have hZeroLt : 0 < scalarModulus sb := by
                rw [scalarModulus_eq_two_pow]; exact Nat.pow_pos (by decide)
              have hSimp : mkAddSmartRvalue (.constant ⟨tyL, .scalar (.int ⟨0, sb⟩)⟩)
                  (mkConstScalarOp ty0 ⟨0, sb⟩) = .use (mkConstScalarOp ty0 ⟨0, sb⟩) := by
                simp [mkAddSmartRvalue, mkConstScalarOp, operandConstScalar?, hSzNe, hZeroLt]
              rw [hSimp, mkConstScalarOp]
              exact use_const_scalar_eval locals ty0 ⟨0, sb⟩ mem localDecls layouts
            · have hSimp : mkAddSmartRvalue (.constant ⟨tyL, .scalar (.int ⟨a, sb⟩)⟩)
                  (mkConstScalarOp ty0 ⟨0, sb⟩) = .use (.constant ⟨tyL, .scalar (.int ⟨a, sb⟩)⟩) := by
                simp [mkAddSmartRvalue, mkConstScalarOp, operandConstScalar?, hSzNe, hA0, hScCanon]
              rw [hSimp]
              exact use_const_scalar_eval locals tyL ⟨a, sb⟩ mem localDecls layouts
    | _ => cases hRaw'

/-- **Width-mismatch & non-canonical constant-pair preservation**: width-mismatched constant pairs
(`allOnes_u32 | 0_u8`, `0_u32 + 5_u8`, `1_u32 * 5_u8`, `allOnes_u32 & 5_u8`) preserve `.unsupported`
in ALL smart constructors (never turning `.unsupported` into `.ok`), while `0_u8 + 256_u8` preserves
wrapping (`0` rather than unwrapped `256`). -/
theorem bitprism_const_width_mismatch_preserves_unsupported :
    evalRvalue [] (mkBitOrSmartRvalue cU32Ty (mkConstScalarOp cU32Ty ⟨allOnesMask 4, 4⟩)
        (mkConstScalarOp cU8Ty ⟨0, 1⟩)) = .unsupported ∧
    evalRvalue [] (mkAddSmartRvalue (mkConstScalarOp cU32Ty ⟨0, 4⟩)
        (mkConstScalarOp cU8Ty ⟨5, 1⟩)) = .unsupported ∧
    evalRvalue [] (mkMulSmartRvalue cU32Ty (mkConstScalarOp cU32Ty ⟨1, 4⟩)
        (mkConstScalarOp cU8Ty ⟨5, 1⟩)) = .unsupported ∧
    evalRvalue [] (mkBitAndSmartRvalue cU32Ty (mkConstScalarOp cU32Ty ⟨allOnesMask 4, 4⟩)
        (mkConstScalarOp cU8Ty ⟨5, 1⟩)) = .unsupported ∧
    evalRvalue [] (mkAddSmartRvalue (mkConstScalarOp cU8Ty ⟨0, 1⟩)
        (mkConstScalarOp cU8Ty ⟨256, 1⟩)) = .ok (.scalar ⟨0, 1⟩) [] emptyMemory := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Annihilator still fires on genuine constants**: `0 & 7`, `7 * 0`, and `allOnes | 7` on
same-width `u32` constants collapse to `.use (const ...)`, agreeing exactly with raw evaluation. -/
theorem bitprism_const_annihilators_fire :
    mkBitAndSmartRvalue cU32Ty (mkConstScalarOp cU32Ty ⟨0, 4⟩) (mkConstScalarOp cU32Ty ⟨7, 4⟩) =
      .use (mkConstScalarOp cU32Ty ⟨0, 4⟩) ∧
    mkMulSmartRvalue cU32Ty (mkConstScalarOp cU32Ty ⟨7, 4⟩) (mkConstScalarOp cU32Ty ⟨0, 4⟩) =
      .use (mkConstScalarOp cU32Ty ⟨0, 4⟩) ∧
    mkBitOrSmartRvalue cU32Ty (mkConstScalarOp cU32Ty ⟨allOnesMask 4, 4⟩)
        (mkConstScalarOp cU32Ty ⟨7, 4⟩) =
      .use (mkConstScalarOp cU32Ty ⟨allOnesMask 4, 4⟩) ∧
    mkBitAndSmartRvalue cU32Ty (mkConstScalarOp cU32Ty ⟨0, 4⟩) (.copy ⟨1, []⟩) =
      .binaryOp .bitAnd (mkConstScalarOp cU32Ty ⟨0, 4⟩) (.copy ⟨1, []⟩) ∧
    evalRvalue [] (mkBitAndSmartRvalue cU32Ty (mkConstScalarOp cU32Ty ⟨0, 4⟩)
        (mkConstScalarOp cU32Ty ⟨7, 4⟩)) =
      evalRvalue [] (.binaryOp .bitAnd (mkConstScalarOp cU32Ty ⟨0, 4⟩)
        (mkConstScalarOp cU32Ty ⟨7, 4⟩)) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Negative refutation #4 (`addUnchecked` overflow vs wrapping `add`)**:
`u8::MAX + 1` faults with `.ub` under `.addUnchecked` whereas wrapping `.add` produces `0` —
confirming checked/unchecked overflow modes can NEVER be conflated by smart constructors! -/
theorem addUnchecked_overflow_preserves_ub :
    let lhs := mkConstScalarOp cU8Ty ⟨255, 1⟩
    let rhs := mkConstScalarOp cU8Ty ⟨1, 1⟩
    evalRvalue [] (.binaryOp .addUnchecked lhs rhs) = .ub ∧
    evalRvalue [] (.binaryOp .add lhs rhs) = .ok (.scalar ⟨0, 1⟩) [] emptyMemory ∧
    evalRvalue [] (.binaryOp .addUnchecked lhs rhs) ≠ evalRvalue [] (.binaryOp .add lhs rhs) := by
  refine ⟨rfl, rfl, fun h => by cases h⟩

/-! ### B.6. Level 3 — Frame-Level Coalescing Smart Constructor (`mkMemWriteFrame`) -/

/-- A frame-local write operation targeting local slot `localIdx` with value `val`. -/
structure MemWriteOp : Type where
  localIdx : Nat
  val : Value

/-- Apply a single local write to `locals`, failing `.none` if the slot is out of bounds or `.dead`
(exact mirror of `Trusted.MirSemantics.evalStmt`'s `.assign` direct-local check). -/
def applyOneMemWrite (w : MemWriteOp) (locals : List LocalSlot) : Option (List LocalSlot) :=
  match get? locals w.localIdx with
  | .some .dead => none
  | .some _ => set? locals w.localIdx (.init w.val)
  | .none => none

/-- Apply a list of local writes in sequence. -/
def applyMemWrites : List MemWriteOp → List LocalSlot → Option (List LocalSlot)
  | [], locals => some locals
  | w :: ws, locals =>
    match applyOneMemWrite w locals with
    | some locals' => applyMemWrites ws locals'
    | none => none

/-- Insert a later write `(localIdx, val)` into an already-coalesced frame write list:
overwrites any earlier write to the SAME slot (`last-write-wins`) while commuting across
DISJOINT slots in sorted order (`O(n)` canonical frame representation). -/
def insertCoalesceWrite (w : MemWriteOp) : List MemWriteOp → List MemWriteOp
  | [] => [w]
  | u :: rest =>
    if w.localIdx == u.localIdx then w :: rest
    else if w.localIdx < u.localIdx then w :: u :: rest
    else u :: insertCoalesceWrite w rest

/-- **Coalescing smart constructor `mkMemWriteFrame`**: folds a sequence of local writes into a
canonical deduplicated sorted frame write list (coalescing consecutive or non-adjacent writes to
the same slot and commuting writes to disjoint slots). -/
def mkMemWriteFrame (writes : List MemWriteOp) : List MemWriteOp :=
  writes.foldl (fun acc w => insertCoalesceWrite w acc) []

/-- Slot-liveness predicate: `locals` has a non-`.dead` slot at `idx`. -/
def SlotLive (locals : List LocalSlot) (idx : Nat) : Prop :=
  ∃ slot, get? locals idx = .some slot ∧ slot ≠ .dead

private theorem get_set_same (locals : List LocalSlot) (idx : Nat) (v : LocalSlot)
    (h : ∃ s, get? locals idx = .some s) :
    ∃ locals', set? locals idx v = .some locals' ∧ get? locals' idx = .some v ∧
      (∀ j, j ≠ idx → get? locals' j = get? locals j) := by
  obtain ⟨s, hs⟩ := h
  have hLt : idx < locals.length := by
    unfold get? at hs
    by_cases hL : idx < locals.length
    · exact hL
    · simp [List.getElem?_eq_none (Nat.le_of_not_lt hL)] at hs
  refine ⟨locals.set idx v, ?_, ?_, ?_⟩
  · simp [set?, hLt]
  · simp [get?, hLt]
  · intro j hj
    simp [get?, List.getElem?_set_ne (Ne.symm hj)]

private theorem set_set_same (locals : List LocalSlot) (idx : Nat) (v₁ v₂ : LocalSlot) :
    (match set? locals idx v₁ with | .some l₁ => set? l₁ idx v₂ | .none => .none) =
      set? locals idx v₂ := by
  unfold set?
  by_cases hLt : idx < locals.length
  · simp [hLt, List.length_set, List.set_set]
  · simp [hLt]

private theorem list_set_comm {α : Type} (xs : List α) (i j : Nat) (v₁ v₂ : α) (hNe : i ≠ j) :
    (xs.set i v₁).set j v₂ = (xs.set j v₂).set i v₁ := by
  induction xs generalizing i j with
  | nil => rfl
  | cons hd tl ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact False.elim (hNe rfl)
      | succ m => rfl
    | succ k =>
      cases j with
      | zero => rfl
      | succ m =>
        simp only [List.set_cons_succ]
        exact congrArg (List.cons hd) (ih k m (fun h => hNe (congrArg Nat.succ h)))

private theorem set_set_comm (locals : List LocalSlot) (i j : Nat) (v₁ v₂ : LocalSlot)
    (hNe : i ≠ j) :
    (match set? locals i v₁ with | .some l₁ => set? l₁ j v₂ | .none => .none) =
      (match set? locals j v₂ with | .some l₂ => set? l₂ i v₁ | .none => .none) := by
  unfold set?
  by_cases hi : i < locals.length <;> by_cases hj : j < locals.length
  · simp [hi, hj, List.length_set, list_set_comm locals i j v₁ v₂ hNe]
  · simp [hi, hj, List.length_set]
  · simp [hi, hj, List.length_set]
  · simp [hi, hj]

private theorem applyOneMemWrite_preserves_live (w : MemWriteOp) (locals locals' : List LocalSlot)
    (hOk : applyOneMemWrite w locals = some locals') (idx : Nat) (hLive : SlotLive locals idx) :
    SlotLive locals' idx := by
  unfold applyOneMemWrite at hOk
  cases hG : get? locals w.localIdx with
  | none => rw [hG] at hOk; cases hOk
  | some s =>
    cases s with
    | dead => rw [hG] at hOk; cases hOk
    | _ =>
      rw [hG] at hOk
      obtain ⟨l', hSet, hSame, hOther⟩ := get_set_same locals w.localIdx (.init w.val) ⟨_, hG⟩
      rw [hSet] at hOk
      cases hOk
      by_cases hEq : idx = w.localIdx
      · subst hEq; exact ⟨.init w.val, hSame, fun h => by cases h⟩
      · obtain ⟨sl, hsl, hne⟩ := hLive
        exact ⟨sl, (hOther idx hEq).trans hsl, hne⟩

private theorem applyOneMemWrite_of_live (w : MemWriteOp) (locals : List LocalSlot)
    (hLive : SlotLive locals w.localIdx) :
    ∃ locals', applyOneMemWrite w locals = some locals' ∧
      set? locals w.localIdx (.init w.val) = .some locals' := by
  obtain ⟨sl, hsl, hne⟩ := hLive
  obtain ⟨l', hSet, _, _⟩ := get_set_same locals w.localIdx (.init w.val) ⟨sl, hsl⟩
  refine ⟨l', ?_, hSet⟩
  unfold applyOneMemWrite
  rw [hsl]
  cases sl with
  | dead => exact False.elim (hne rfl)
  | uninit => exact hSet
  | init _ => exact hSet

private theorem applyOneMemWrite_same_overwrite (w₁ w₂ : MemWriteOp) (locals : List LocalSlot)
    (hSame : w₁.localIdx = w₂.localIdx) (hLive : SlotLive locals w₂.localIdx) :
    applyMemWrites [w₁, w₂] locals = applyOneMemWrite w₂ locals := by
  cases w₁ with | mk i₁ v₁ =>
  cases w₂ with | mk i₂ v₂ =>
  simp only at hSame; subst hSame
  obtain ⟨l₁, h1, hSet1⟩ := applyOneMemWrite_of_live ⟨i₁, v₁⟩ locals hLive
  have hLive1 := applyOneMemWrite_preserves_live ⟨i₁, v₁⟩ locals l₁ h1 i₁ hLive
  obtain ⟨l₂, h2, hSet2⟩ := applyOneMemWrite_of_live ⟨i₁, v₂⟩ l₁ hLive1
  obtain ⟨lDirect, hDirect, hSetDirect⟩ := applyOneMemWrite_of_live ⟨i₁, v₂⟩ locals hLive
  have hOver := set_set_same locals i₁ (.init v₁) (.init v₂)
  dsimp only at hSet1 hSet2 hSetDirect
  rw [hSet1] at hOver
  dsimp only at hOver
  rw [hSet2, hSetDirect] at hOver
  cases hOver
  simp only [applyMemWrites, h1, h2, hDirect]

private theorem applyOneMemWrite_comm_disjoint (w₁ w₂ : MemWriteOp) (locals : List LocalSlot)
    (hNe : w₁.localIdx ≠ w₂.localIdx)
    (hL1 : SlotLive locals w₁.localIdx) (hL2 : SlotLive locals w₂.localIdx) :
    applyMemWrites [w₁, w₂] locals = applyMemWrites [w₂, w₁] locals := by
  obtain ⟨l₁, h1, hSet1⟩ := applyOneMemWrite_of_live w₁ locals hL1
  have hL2' := applyOneMemWrite_preserves_live w₁ locals l₁ h1 w₂.localIdx hL2
  obtain ⟨l₁₂, h12, hSet12⟩ := applyOneMemWrite_of_live w₂ l₁ hL2'
  obtain ⟨l₂, h2, hSet2⟩ := applyOneMemWrite_of_live w₂ locals hL2
  have hL1' := applyOneMemWrite_preserves_live w₂ locals l₂ h2 w₁.localIdx hL1
  obtain ⟨l₂₁, h21, hSet21⟩ := applyOneMemWrite_of_live w₁ l₂ hL1'
  have hComm := set_set_comm locals w₁.localIdx w₂.localIdx (.init w₁.val) (.init w₂.val) hNe
  rw [hSet1, hSet2] at hComm
  dsimp only at hComm
  rw [hSet12, hSet21] at hComm
  cases hComm
  simp only [applyMemWrites, h1, h12, h2, h21]

private theorem applyMemWrites_append (ws₁ ws₂ : List MemWriteOp) (locals : List LocalSlot) :
    applyMemWrites (ws₁ ++ ws₂) locals =
      match applyMemWrites ws₁ locals with
      | some locals' => applyMemWrites ws₂ locals'
      | none => none := by
  induction ws₁ generalizing locals with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.cons_append, applyMemWrites]
    cases applyOneMemWrite w locals with
    | none => rfl
    | some locals' => exact ih locals'

private theorem applyMemWrites_preserves_live (ws : List MemWriteOp)
    (locals locals' : List LocalSlot) (h : applyMemWrites ws locals = some locals')
    (idx : Nat) (hLive : SlotLive locals idx) : SlotLive locals' idx := by
  induction ws generalizing locals with
  | nil => cases h; exact hLive
  | cons w ws ih =>
    simp only [applyMemWrites] at h
    cases h1 : applyOneMemWrite w locals with
    | none => rw [h1] at h; cases h
    | some l₁ =>
      rw [h1] at h
      exact ih l₁ h (applyOneMemWrite_preserves_live w locals l₁ h1 idx hLive)

/-- Strict ascending local-index invariant for a coalesced frame write list (every slot index
appears at most once, in strict ascending order). -/
def StrictlySortedWrites : List MemWriteOp → Prop
  | [] => True
  | u :: rest => (∀ x ∈ rest, u.localIdx < x.localIdx) ∧ StrictlySortedWrites rest

private theorem mem_insertCoalesceWrite (w x : MemWriteOp) (acc : List MemWriteOp) :
    x ∈ insertCoalesceWrite w acc → x = w ∨ x ∈ acc := by
  induction acc with
  | nil =>
    intro h; simp only [insertCoalesceWrite, List.mem_singleton] at h; exact .inl h
  | cons u rest ih =>
    unfold insertCoalesceWrite
    split
    · intro h
      rcases List.mem_cons.mp h with rfl | hRest
      · exact .inl rfl
      · exact .inr (List.mem_cons_of_mem _ hRest)
    · split
      · intro h
        rcases List.mem_cons.mp h with rfl | hRest
        · exact .inl rfl
        · exact .inr hRest
      · intro h
        rcases List.mem_cons.mp h with rfl | hRec
        · exact .inr (List.mem_cons_self ..)
        · rcases ih hRec with rfl | hRest
          · exact .inl rfl
          · exact .inr (List.mem_cons_of_mem _ hRest)

private theorem strictlySorted_insertCoalesceWrite (w : MemWriteOp) (acc : List MemWriteOp)
    (hSort : StrictlySortedWrites acc) :
    StrictlySortedWrites (insertCoalesceWrite w acc) := by
  induction acc with
  | nil => exact ⟨(fun _ h => by cases h), trivial⟩
  | cons u rest ih =>
    obtain ⟨hHeadLt, hRestSort⟩ := hSort
    unfold insertCoalesceWrite
    split
    · rename_i hEq
      have hEq' : w.localIdx = u.localIdx := beq_iff_eq.mp hEq
      exact ⟨fun x hx => by rw [hEq']; exact hHeadLt x hx, hRestSort⟩
    · split
      · rename_i _ hLt
        refine ⟨?_, hHeadLt, hRestSort⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hR
        · exact hLt
        · exact Nat.lt_trans hLt (hHeadLt x hR)
      · rename_i hNe hNotLt
        have hNe' : w.localIdx ≠ u.localIdx := fun h => by
          have : (w.localIdx == u.localIdx) = true := beq_iff_eq.mpr h
          exact hNe this
        have hULtW : u.localIdx < w.localIdx := by omega
        refine ⟨?_, ih hRestSort⟩
        intro x hx
        rcases mem_insertCoalesceWrite w x rest hx with rfl | hR
        · exact hULtW
        · exact hHeadLt x hR

private theorem applyMemWrites_comm_head_disjoint (w : MemWriteOp) (rest : List MemWriteOp)
    (locals : List LocalSlot)
    (hDisj : ∀ x ∈ rest, w.localIdx ≠ x.localIdx)
    (hRestLive : ∀ x ∈ rest, SlotLive locals x.localIdx)
    (hWLive : SlotLive locals w.localIdx) :
    applyMemWrites (w :: rest) locals = applyMemWrites (rest ++ [w]) locals := by
  induction rest generalizing locals with
  | nil => rfl
  | cons u tl ih =>
    have hNe : w.localIdx ≠ u.localIdx := hDisj u (List.mem_cons_self ..)
    have hULive : SlotLive locals u.localIdx := hRestLive u (List.mem_cons_self ..)
    have hTlDisj : ∀ x ∈ tl, w.localIdx ≠ x.localIdx :=
      fun x hx => hDisj x (List.mem_cons_of_mem _ hx)
    have hComm2 := applyOneMemWrite_comm_disjoint w u locals hNe hWLive hULive
    have hRewrite1 : applyMemWrites (w :: u :: tl) locals = applyMemWrites (u :: w :: tl) locals := by
      have hA : applyMemWrites ([w, u] ++ tl) locals = applyMemWrites (w :: u :: tl) locals := rfl
      have hB : applyMemWrites ([u, w] ++ tl) locals = applyMemWrites (u :: w :: tl) locals := rfl
      rw [← hA, ← hB, applyMemWrites_append, applyMemWrites_append, hComm2]
    rw [hRewrite1]
    simp only [List.cons_append, applyMemWrites]
    obtain ⟨l₁, h1, _⟩ := applyOneMemWrite_of_live u locals hULive
    rw [h1]
    have hTlLive' : ∀ x ∈ tl, SlotLive l₁ x.localIdx :=
      fun x hx => applyOneMemWrite_preserves_live u locals l₁ h1 x.localIdx
        (hRestLive x (List.mem_cons_of_mem _ hx))
    have hWLive' := applyOneMemWrite_preserves_live u locals l₁ h1 w.localIdx hWLive
    exact ih l₁ hTlDisj hTlLive' hWLive'

private theorem insertCoalesceWrite_eq_append (w : MemWriteOp) (acc : List MemWriteOp)
    (locals : List LocalSlot)
    (hSort : StrictlySortedWrites acc)
    (hAccLive : ∀ u ∈ acc, SlotLive locals u.localIdx)
    (hWLive : SlotLive locals w.localIdx) :
    applyMemWrites (insertCoalesceWrite w acc) locals =
      applyMemWrites (acc ++ [w]) locals := by
  induction acc generalizing locals with
  | nil => rfl
  | cons u rest ih =>
    obtain ⟨hHeadLt, hRestSort⟩ := hSort
    have hULive : SlotLive locals u.localIdx := hAccLive u (List.mem_cons_self ..)
    have hRestLive : ∀ x ∈ rest, SlotLive locals x.localIdx :=
      fun x hx => hAccLive x (List.mem_cons_of_mem _ hx)
    unfold insertCoalesceWrite
    split
    · rename_i hSame
      have hSame' : w.localIdx = u.localIdx := beq_iff_eq.mp hSame
      have hDisjRest : ∀ x ∈ rest, w.localIdx ≠ x.localIdx := fun x hx => by
        have := hHeadLt x hx; omega
      obtain ⟨lU, hU, _⟩ := applyOneMemWrite_of_live u locals hULive
      have hRestLiveU : ∀ x ∈ rest, SlotLive lU x.localIdx :=
        fun x hx => applyOneMemWrite_preserves_live u locals lU hU x.localIdx (hRestLive x hx)
      have hWLiveU := applyOneMemWrite_preserves_live u locals lU hU w.localIdx hWLive
      have hCommBack : applyMemWrites (rest ++ [w]) lU = applyMemWrites (w :: rest) lU :=
        (applyMemWrites_comm_head_disjoint w rest lU hDisjRest hRestLiveU hWLiveU).symm
      have hRhs : applyMemWrites ((u :: rest) ++ [w]) locals = applyMemWrites ([u, w] ++ rest) locals := by
        simp only [List.cons_append, applyMemWrites, hU]
        exact hCommBack
      rw [hRhs, applyMemWrites_append, applyOneMemWrite_same_overwrite u w locals hSame'.symm hWLive]
      rfl
    · split
      · rename_i _ hLt
        have hDisjAll : ∀ x ∈ u :: rest, w.localIdx ≠ x.localIdx := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hR
          · omega
          · have := hHeadLt x hR; omega
        exact applyMemWrites_comm_head_disjoint w (u :: rest) locals hDisjAll hAccLive hWLive
      · simp only [List.cons_append, applyMemWrites]
        obtain ⟨lU, hU, _⟩ := applyOneMemWrite_of_live u locals hULive
        rw [hU]
        have hRestLiveU : ∀ x ∈ rest, SlotLive lU x.localIdx :=
          fun x hx => applyOneMemWrite_preserves_live u locals lU hU x.localIdx (hRestLive x hx)
        have hWLiveU := applyOneMemWrite_preserves_live u locals lU hU w.localIdx hWLive
        exact ih lU hRestSort hRestLiveU hWLiveU

/-- **Exact equivalence `mkMemWriteFrame_eq_raw`** for coalescing `mkMemWriteFrame`:
for any write sequence whose targeted local slots are all live (in-bounds & non-`.dead`),
applying the coalesced canonical write frame produces the EXACT same `List LocalSlot` as
applying the raw write sequence! -/
theorem mkMemWriteFrame_eq_raw (writes : List MemWriteOp) (locals : List LocalSlot)
    (hLive : ∀ w ∈ writes, SlotLive locals w.localIdx) :
    applyMemWrites (mkMemWriteFrame writes) locals = applyMemWrites writes locals := by
  have hFold : ∀ (acc : List MemWriteOp) (ws : List MemWriteOp),
      StrictlySortedWrites acc →
      (∀ u ∈ acc, SlotLive locals u.localIdx) →
      (∀ w ∈ ws, SlotLive locals w.localIdx) →
      applyMemWrites (ws.foldl (fun a w => insertCoalesceWrite w a) acc) locals =
        applyMemWrites (acc ++ ws) locals := by
    intro acc ws
    induction ws generalizing acc with
    | nil =>
      intro _ _ _
      simp only [List.foldl_nil, List.append_nil]
    | cons w ws ih =>
      intro hSort hAccL hWsL
      have hWL : SlotLive locals w.localIdx := hWsL w (List.mem_cons_self ..)
      have hRestL : ∀ x ∈ ws, SlotLive locals x.localIdx :=
        fun x hx => hWsL x (List.mem_cons_of_mem _ hx)
      have hAcc'L : ∀ u ∈ insertCoalesceWrite w acc, SlotLive locals u.localIdx := by
        intro u hu
        rcases mem_insertCoalesceWrite w u acc hu with rfl | hIn
        · exact hWL
        · exact hAccL u hIn
      simp only [List.foldl_cons]
      rw [ih (insertCoalesceWrite w acc) (strictlySorted_insertCoalesceWrite w acc hSort) hAcc'L hRestL]
      rw [applyMemWrites_append, insertCoalesceWrite_eq_append w acc locals hSort hAccL hWL]
      rw [← applyMemWrites_append, List.append_assoc]
      rfl
  exact hFold [] writes trivial (fun _ h => by cases h) hLive

/-- **Negative dead-slot non-erasure witness for `mkMemWriteFrame`**: writing to a `.dead` slot
still fails `.none` even after coalescing two writes to the same dead slot (liveness is never
dropped). -/
theorem mkMemWriteFrame_dead_slot_preserves_failure :
    let locals : List LocalSlot := [.uninit, .dead]
    let ws : List MemWriteOp := [⟨1, .scalar ⟨10, 4⟩⟩, ⟨1, .scalar ⟨20, 4⟩⟩]
    mkMemWriteFrame ws = [⟨1, .scalar ⟨20, 4⟩⟩] ∧
    applyMemWrites ws locals = none ∧
    applyMemWrites (mkMemWriteFrame ws) locals = none :=
  ⟨rfl, rfl, rfl⟩

end BitprismSmartCtors

/-! ## Part C. `veil#209` `veil_frame` Named-Field Framing over `MirSemantics.Memory` & `StackFrame` -/

section VeilFrame

/-- Exhaustive enumeration of ALL 14 fields of `Trusted.Rustc.V2026_06_01.MirSemantics.Memory`. -/
inductive MemoryField : Type where
  | nextAllocId
  | globals
  | borrows
  | nextTag
  | callees
  | traitImpls
  | callStack
  | activeCallee
  | activeProtectors
  | nextProtector
  | callerLocals
  | fnPtrs
  | exposedAllocIds
  | rootUnwindCeiling
  deriving DecidableEq, Repr

/-- Complete list of all 14 `MemoryField` constructors. -/
def allMemoryFields : List MemoryField :=
  [.nextAllocId, .globals, .borrows, .nextTag, .callees, .traitImpls, .callStack,
   .activeCallee, .activeProtectors, .nextProtector, .callerLocals, .fnPtrs,
   .exposedAllocIds, .rootUnwindCeiling]

theorem allMemoryFields_length : allMemoryFields.length = 14 := rfl

theorem mem_allMemoryFields (f : MemoryField) : f ∈ allMemoryFields := by
  cases f <;> simp [allMemoryFields]

/-- Exhaustive enumeration of ALL 17 fields of `MachineState` (`3` `StackFrame` fields + `14`
`Memory` fields). -/
inductive StateField : Type where
  | frameBlockIdx
  | frameStmtIdx
  | frameLocals
  | mem (f : MemoryField)
  deriving DecidableEq, Repr

/-- Exact field-agreement relation on `Memory`. -/
def MemFieldAgree : MemoryField → Memory → Memory → Prop
  | .nextAllocId, m₁, m₂ => m₁.nextAllocId = m₂.nextAllocId
  | .globals, m₁, m₂ => m₁.globals = m₂.globals
  | .borrows, m₁, m₂ => m₁.borrows = m₂.borrows
  | .nextTag, m₁, m₂ => m₁.nextTag = m₂.nextTag
  | .callees, m₁, m₂ => m₁.callees = m₂.callees
  | .traitImpls, m₁, m₂ => m₁.traitImpls = m₂.traitImpls
  | .callStack, m₁, m₂ => m₁.callStack = m₂.callStack
  | .activeCallee, m₁, m₂ => m₁.activeCallee = m₂.activeCallee
  | .activeProtectors, m₁, m₂ => m₁.activeProtectors = m₂.activeProtectors
  | .nextProtector, m₁, m₂ => m₁.nextProtector = m₂.nextProtector
  | .callerLocals, m₁, m₂ => m₁.callerLocals = m₂.callerLocals
  | .fnPtrs, m₁, m₂ => m₁.fnPtrs = m₂.fnPtrs
  | .exposedAllocIds, m₁, m₂ => m₁.exposedAllocIds = m₂.exposedAllocIds
  | .rootUnwindCeiling, m₁, m₂ => m₁.rootUnwindCeiling = m₂.rootUnwindCeiling

/-- Exhaustiveness extensionality theorem for `MemoryField`: agreeing on all 14 named fields
implies `m₁ = m₂` (proving zero fields of `MirSemantics.Memory` were omitted!). -/
theorem Memory.ext_allFields (m₁ m₂ : Memory) (h : ∀ f : MemoryField, MemFieldAgree f m₁ m₂) :
    m₁ = m₂ := by
  cases m₁; cases m₂
  have h1 := h .nextAllocId
  have h2 := h .globals
  have h3 := h .borrows
  have h4 := h .nextTag
  have h5 := h .callees
  have h6 := h .traitImpls
  have h7 := h .callStack
  have h8 := h .activeCallee
  have h9 := h .activeProtectors
  have h10 := h .nextProtector
  have h11 := h .callerLocals
  have h12 := h .fnPtrs
  have h13 := h .exposedAllocIds
  have h14 := h .rootUnwindCeiling
  simp only [MemFieldAgree] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  subst h1; subst h2; subst h3; subst h4; subst h5; subst h6; subst h7
  subst h8; subst h9; subst h10; subst h11; subst h12; subst h13; subst h14
  rfl

/-- Exact field-agreement relation on `MachineState`. -/
def StateFieldAgree : StateField → MachineState → MachineState → Prop
  | .frameBlockIdx, s₁, s₂ => s₁.frame.blockIdx = s₂.frame.blockIdx
  | .frameStmtIdx, s₁, s₂ => s₁.frame.stmtIdx = s₂.frame.stmtIdx
  | .frameLocals, s₁, s₂ => s₁.frame.locals = s₂.frame.locals
  | .mem f, s₁, s₂ => MemFieldAgree f s₁.memory s₂.memory

theorem StateFieldAgree.refl (f : StateField) (s : MachineState) : StateFieldAgree f s s := by
  cases f with
  | frameBlockIdx | frameStmtIdx | frameLocals => rfl
  | mem mf => cases mf <;> rfl

theorem StateFieldAgree.trans {f : StateField} {s₁ s₂ s₃ : MachineState}
    (h₁₂ : StateFieldAgree f s₁ s₂) (h₂₃ : StateFieldAgree f s₂ s₃) :
    StateFieldAgree f s₁ s₃ := by
  cases f with
  | frameBlockIdx | frameStmtIdx | frameLocals => exact Eq.trans h₁₂ h₂₃
  | mem mf => cases mf <;> exact Eq.trans h₁₂ h₂₃

/-- Exhaustiveness extensionality theorem for `StateField` over `MachineState`. -/
theorem MachineState.ext_allFields (s₁ s₂ : MachineState)
    (h : ∀ f : StateField, StateFieldAgree f s₁ s₂) : s₁ = s₂ := by
  cases s₁ with | mk fr₁ m₁ =>
  cases s₂ with | mk fr₂ m₂ =>
  cases fr₁; cases fr₂
  have hb := h .frameBlockIdx
  have hs := h .frameStmtIdx
  have hl := h .frameLocals
  simp only [StateFieldAgree] at hb hs hl
  subst hb; subst hs; subst hl
  have hm := Memory.ext_allFields m₁ m₂ (fun f => h (.mem f))
  subst hm
  rfl

/-- `s₁` and `s₂` agree on EVERY `StateField` outside the modified set `W`. -/
def AgreeOutsideFields (W : List StateField) (s₁ s₂ : MachineState) : Prop :=
  ∀ f, f ∉ W → StateFieldAgree f s₁ s₂

theorem AgreeOutsideFields.refl (W : List StateField) (s : MachineState) :
    AgreeOutsideFields W s s :=
  fun f _ => StateFieldAgree.refl f s

theorem AgreeOutsideFields.mono {W₁ W₂ : List StateField} {s₁ s₂ : MachineState}
    (hSub : ∀ f, f ∈ W₁ → f ∈ W₂) (h : AgreeOutsideFields W₁ s₁ s₂) :
    AgreeOutsideFields W₂ s₁ s₂ :=
  fun f hNotW2 => h f (fun hInW1 => hNotW2 (hSub f hInW1))

theorem AgreeOutsideFields.trans_union {W₁ W₂ : List StateField} {s₁ s₂ s₃ : MachineState}
    (h₁₂ : AgreeOutsideFields W₁ s₁ s₂) (h₂₃ : AgreeOutsideFields W₂ s₂ s₃) :
    AgreeOutsideFields (W₁ ++ W₂) s₁ s₃ := by
  intro f hNot
  have h1 : f ∉ W₁ := fun h => hNot (List.mem_append_left W₂ h)
  have h2 : f ∉ W₂ := fun h => hNot (List.mem_append_right W₁ h)
  exact StateFieldAgree.trans (h₁₂ f h1) (h₂₃ f h2)

/-- Predicate `Inv` depends ONLY on the named fields in `R` (`veil#209` read-set abstraction). -/
def ReadsOnlyFields (R : List StateField) (Inv : MachineState → Prop) : Prop :=
  ∀ s₁ s₂, (∀ f ∈ R, StateFieldAgree f s₁ s₂) → Inv s₁ → Inv s₂

/-- Action `act` modifies ONLY fields in `W` on BOTH its `.ok` and `.error` outcomes! -/
def ModifiesOnlyFields {E A : Type} (W : List StateField)
    (act : ExactAction MachineState E A) : Prop :=
  ∀ s, match act s with
    | .ok _ s' => AgreeOutsideFields W s s'
    | .error _ s' => AgreeOutsideFields W s s'

/-- Disjointness of a read-field set `R` and write-field set `W`. -/
def DisjointFields (R W : List StateField) : Prop :=
  ∀ f, f ∈ R → f ∉ W

/-- Decidable kernel-checkable disjointness check between read set `R` and write set `W`. -/
def disjointFieldsBool (R W : List StateField) : Bool :=
  R.all (fun f => !W.contains f)

theorem disjointFieldsBool_sound {R W : List StateField} (h : disjointFieldsBool R W = true) :
    DisjointFields R W := by
  intro f hfR hfW
  unfold disjointFieldsBool at h
  have hAll := List.all_eq_true.mp h f hfR
  have hCont : W.contains f = true := List.elem_eq_true_of_mem hfW
  rw [hCont] at hAll
  cases hAll

theorem disjointFieldsBool_iff (R W : List StateField) :
    disjointFieldsBool R W = true ↔ DisjointFields R W := by
  constructor
  · exact disjointFieldsBool_sound
  · intro hDisj
    unfold disjointFieldsBool
    apply List.all_eq_true.mpr
    intro f hfR
    cases hC : W.contains f with
    | false => rfl
    | true => exact False.elim (hDisj f hfR (List.mem_of_elem_eq_true hC))

/-- Composition of `ModifiesOnlyFields` across `ExactAction.bind`. -/
theorem modifiesOnlyFields_bind {E A B : Type} {W₁ W₂ : List StateField}
    {m : ExactAction MachineState E A} {k : A → ExactAction MachineState E B}
    (hM : ModifiesOnlyFields W₁ m) (hK : ∀ a, ModifiesOnlyFields W₂ (k a)) :
    ModifiesOnlyFields (W₁ ++ W₂) (ExactAction.bind m k) := by
  intro s
  unfold ExactAction.bind
  have h1 := hM s
  cases hm : m s with
  | error e s' =>
    rw [hm] at h1
    exact AgreeOutsideFields.mono (fun f hf => List.mem_append_left W₂ hf) h1
  | ok a s' =>
    rw [hm] at h1
    dsimp only
    have h2 := hK a s'
    cases hk : k a s' with
    | ok b s'' =>
      rw [hk] at h2
      exact AgreeOutsideFields.trans_union h1 h2
    | error e s'' =>
      rw [hk] at h2
      exact AgreeOutsideFields.trans_union h1 h2

theorem modifiesOnlyFields_seq {E A B : Type} {W₁ W₂ : List StateField}
    {m : ExactAction MachineState E A} {n : ExactAction MachineState E B}
    (hM : ModifiesOnlyFields W₁ m) (hN : ModifiesOnlyFields W₂ n) :
    ModifiesOnlyFields (W₁ ++ W₂) (ExactAction.seq m n) :=
  modifiesOnlyFields_bind hM (fun _ => hN)

/-- **Master `veil#209` `exactWP_veil_frame` rule**:
if `act` modifies only fields in `W`, invariant `Inv` reads only fields in `R`, and `R` is
disjoint from `W`, then `Inv` is automatically carried from the pre-state into BOTH the `.ok`
and `.error` continuations of `AnnealExactWP`! -/
theorem exactWP_veil_frame {E A : Type} {W R : List StateField}
    {act : ExactAction MachineState E A} {Inv : MachineState → Prop}
    {post : A → MachineState → Prop} {onError : E → MachineState → Prop} {s : MachineState}
    (hMod : ModifiesOnlyFields W act)
    (hRead : ReadsOnlyFields R Inv)
    (hDisj : DisjointFields R W)
    (hInv : Inv s)
    (hWp : AnnealExactWP act post onError s) :
    AnnealExactWP act (fun a s' => post a s' ∧ Inv s') (fun e s' => onError e s' ∧ Inv s') s := by
  unfold AnnealExactWP at hWp ⊢
  have hAgree := hMod s
  cases hAct : act s with
  | ok a s' =>
    rw [hAct] at hWp hAgree
    exact ⟨hWp, hRead s s' (fun f hfR => hAgree f (hDisj f hfR)) hInv⟩
  | error e s' =>
    rw [hAct] at hWp hAgree
    exact ⟨hWp, hRead s s' (fun f hfR => hAgree f (hDisj f hfR)) hInv⟩

/-- Direct preservation corollary of `exactWP_veil_frame` (discharges invariant preservation goals
directly via `disjointFieldsBool R W = true`). -/
theorem veil_frame_preserves {E A : Type} {W R : List StateField}
    {act : ExactAction MachineState E A} {Inv : MachineState → Prop} {s : MachineState}
    (hMod : ModifiesOnlyFields W act)
    (hRead : ReadsOnlyFields R Inv)
    (hDisj : disjointFieldsBool R W = true)
    (hInv : Inv s) :
    AnnealExactWP act (fun _ s' => Inv s') (fun _ s' => Inv s') s := by
  have hTriv : AnnealExactWP act (fun _ _ => True) (fun _ _ => True) s := by
    unfold AnnealExactWP; cases act s <;> trivial
  exact exactWP_consequence (fun _ _ h => h.2) (fun _ _ h => h.2)
    (exactWP_veil_frame hMod hRead (disjointFieldsBool_sound hDisj) hInv hTriv)

/-! ### C.1. Named Field-Framing Combinators -/

/-- Lift a predicate on active frame `locals` into a `MachineState` invariant with automatic
`ReadsOnlyFields [.frameLocals]` proof. -/
def frame_locals (P : List LocalSlot → Prop) : MachineState → Prop := fun s => P s.frame.locals

theorem frame_locals_readsOnly (P : List LocalSlot → Prop) :
    ReadsOnlyFields [.frameLocals] (frame_locals P) := by
  intro s₁ s₂ hAgree hP
  have hEq : s₁.frame.locals = s₂.frame.locals := hAgree .frameLocals (List.mem_cons_self ..)
  unfold frame_locals at hP ⊢; rw [← hEq]; exact hP

/-- Lift a predicate on `memory.callerLocals` (`ReadsOnlyFields [.mem .callerLocals]`). -/
def frame_callerLocals (P : List LocalSlot → Prop) : MachineState → Prop :=
  fun s => P s.memory.callerLocals

theorem frame_callerLocals_readsOnly (P : List LocalSlot → Prop) :
    ReadsOnlyFields [.mem .callerLocals] (frame_callerLocals P) := by
  intro s₁ s₂ hAgree hP
  have hEq : s₁.memory.callerLocals = s₂.memory.callerLocals :=
    hAgree (.mem .callerLocals) (List.mem_cons_self ..)
  unfold frame_callerLocals at hP ⊢; rw [← hEq]; exact hP

/-- Lift a predicate on `memory.borrows` (`ReadsOnlyFields [.mem .borrows]`). -/
def frame_borrows (P : List BorrowEntry → Prop) : MachineState → Prop :=
  fun s => P s.memory.borrows

theorem frame_borrows_readsOnly (P : List BorrowEntry → Prop) :
    ReadsOnlyFields [.mem .borrows] (frame_borrows P) := by
  intro s₁ s₂ hAgree hP
  have hEq : s₁.memory.borrows = s₂.memory.borrows :=
    hAgree (.mem .borrows) (List.mem_cons_self ..)
  unfold frame_borrows at hP ⊢; rw [← hEq]; exact hP

/-- Lift a predicate on `memory.globals` (`ReadsOnlyFields [.mem .globals]`). -/
def frame_globals (P : List CapturedAllocation → Prop) : MachineState → Prop :=
  fun s => P s.memory.globals

theorem frame_globals_readsOnly (P : List CapturedAllocation → Prop) :
    ReadsOnlyFields [.mem .globals] (frame_globals P) := by
  intro s₁ s₂ hAgree hP
  have hEq : s₁.memory.globals = s₂.memory.globals :=
    hAgree (.mem .globals) (List.mem_cons_self ..)
  unfold frame_globals at hP ⊢; rw [← hEq]; exact hP

/-- Lift a predicate on heap allocation state `(nextAllocId, globals)`
(`ReadsOnlyFields [.mem .nextAllocId, .mem .globals]`). -/
def frame_heap (P : AllocId → List CapturedAllocation → Prop) : MachineState → Prop :=
  fun s => P s.memory.nextAllocId s.memory.globals

theorem frame_heap_readsOnly (P : AllocId → List CapturedAllocation → Prop) :
    ReadsOnlyFields [.mem .nextAllocId, .mem .globals] (frame_heap P) := by
  intro s₁ s₂ hAgree hP
  have h1 : s₁.memory.nextAllocId = s₂.memory.nextAllocId :=
    hAgree (.mem .nextAllocId) (by simp)
  have h2 : s₁.memory.globals = s₂.memory.globals :=
    hAgree (.mem .globals) (by simp)
  unfold frame_heap at hP ⊢; rw [← h1, ← h2]; exact hP

/-- Lift a predicate on `memory.callStack` (`ReadsOnlyFields [.mem .callStack]`). -/
def frame_callStack (P : List SavedCallerFrame → Prop) : MachineState → Prop :=
  fun s => P s.memory.callStack

theorem frame_callStack_readsOnly (P : List SavedCallerFrame → Prop) :
    ReadsOnlyFields [.mem .callStack] (frame_callStack P) := by
  intro s₁ s₂ hAgree hP
  have hEq : s₁.memory.callStack = s₂.memory.callStack :=
    hAgree (.mem .callStack) (List.mem_cons_self ..)
  unfold frame_callStack at hP ⊢; rw [← hEq]; exact hP

/-- Lift a predicate on protector state `(activeProtectors, nextProtector)`
(`ReadsOnlyFields [.mem .activeProtectors, .mem .nextProtector]`). -/
def frame_protectors (P : List Nat → Nat → Prop) : MachineState → Prop :=
  fun s => P s.memory.activeProtectors s.memory.nextProtector

theorem frame_protectors_readsOnly (P : List Nat → Nat → Prop) :
    ReadsOnlyFields [.mem .activeProtectors, .mem .nextProtector] (frame_protectors P) := by
  intro s₁ s₂ hAgree hP
  have h1 : s₁.memory.activeProtectors = s₂.memory.activeProtectors :=
    hAgree (.mem .activeProtectors) (by simp)
  have h2 : s₁.memory.nextProtector = s₂.memory.nextProtector :=
    hAgree (.mem .nextProtector) (by simp)
  unfold frame_protectors at hP ⊢; rw [← h1, ← h2]; exact hP

/-- Conjunction combinator for `ReadsOnlyFields`. -/
theorem readsOnlyFields_and {R₁ R₂ : List StateField} {P Q : MachineState → Prop}
    (hP : ReadsOnlyFields R₁ P) (hQ : ReadsOnlyFields R₂ Q) :
    ReadsOnlyFields (R₁ ++ R₂) (fun s => P s ∧ Q s) := by
  intro s₁ s₂ hAgree ⟨hp, hq⟩
  exact ⟨hP s₁ s₂ (fun f hf => hAgree f (List.mem_append_left R₂ hf)) hp,
         hQ s₁ s₂ (fun f hf => hAgree f (List.mem_append_right R₁ hf)) hq⟩

/-! ### C.2. Real Unmodified `Trusted.MirSemantics` Transition Framing Theorems -/

/-- `StatementKind.nop` modifies ONLY `[.frameStmtIdx]`. -/
theorem nop_modifiesOnlyFields (span : String) (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    ModifiesOnlyFields [.frameStmtIdx]
      (evalStmtAction { kind := .nop, span := span } localDecls layouts) := by
  intro s
  unfold evalStmtAction evalStmt liftMirStepNode advanceStmt
  intro f hf
  cases f with
  | frameStmtIdx => exact False.elim (hf (List.mem_cons_self ..))
  | frameBlockIdx | frameLocals => rfl
  | mem mf => cases mf <;> rfl

/-- `restoreCallerProtectorsAction` modifies ONLY `[.mem .activeProtectors]`. -/
theorem restoreCallerProtectors_modifiesOnlyFields (caller : SavedCallerFrame) :
    ModifiesOnlyFields [.mem .activeProtectors] (restoreCallerProtectorsAction caller) := by
  intro s
  unfold restoreCallerProtectorsAction ExactAction.modify
  intro f hf
  cases f with
  | frameBlockIdx | frameStmtIdx | frameLocals => rfl
  | mem mf =>
    cases mf with
    | activeProtectors => exact False.elim (hf (List.mem_cons_self ..))
    | _ => rfl

/-- `disableFrameBorrowsAction` modifies ONLY `[.mem .borrows]`. -/
theorem disableFrameBorrows_modifiesOnlyFields (depth nLocals : Nat) :
    ModifiesOnlyFields [.mem .borrows] (disableFrameBorrowsAction depth nLocals) := by
  intro s
  unfold disableFrameBorrowsAction ExactAction.modify
  intro f hf
  cases f with
  | frameBlockIdx | frameStmtIdx | frameLocals => rfl
  | mem mf =>
    cases mf with
    | borrows => exact False.elim (hf (List.mem_cons_self ..))
    | _ => rfl

/-- `frameDeallocProtectorAction` modifies ONLY `[.mem .borrows]` (on BOTH `.ok` and `.error`). -/
theorem frameDeallocProtector_modifiesOnlyFields (depth nLocals : Nat) :
    ModifiesOnlyFields [.mem .borrows] (frameDeallocProtectorAction depth nLocals) := by
  intro s
  unfold frameDeallocProtectorAction
  cases hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors depth nLocals with
  | true => exact AgreeOutsideFields.refl _ s
  | false =>
    intro f hf
    cases f with
    | frameBlockIdx | frameStmtIdx | frameLocals => rfl
    | mem mf =>
      cases mf with
      | borrows => exact False.elim (hf (List.mem_cons_self ..))
      | _ => rfl

/-- Assigning a pure constant scalar into a direct local (`dst.projection = []`) via unmodified
`Trusted.MirSemantics.evalStmt` modifies ONLY `[.frameStmtIdx, .frameLocals, .mem .borrows]`! -/
theorem assign_const_local_modifiesOnlyFields (dstLoc : Local) (ty : Ty) (sc : ScalarInt)
    (span : String) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    ModifiesOnlyFields [.frameStmtIdx, .frameLocals, .mem .borrows]
      (evalStmtAction { kind := .assign ⟨dstLoc, []⟩ (.use (mkConstScalarOp ty sc)), span := span }
        localDecls layouts) := by
  intro s
  have hEvalRv :
      evalRvalue s.frame.locals (.use (mkConstScalarOp ty sc)) s.memory localDecls layouts =
        .ok (.scalar sc) s.frame.locals s.memory := rfl
  unfold evalStmtAction evalStmt
  dsimp only
  rw [hEvalRv]
  dsimp only
  cases get? s.frame.locals dstLoc with
  | none =>
    simp only [liftMirStepNode]
    exact AgreeOutsideFields.refl _ s
  | some slot =>
    cases slot with
    | dead =>
      simp only [liftMirStepNode]
      exact AgreeOutsideFields.refl _ s
    | uninit | init _ =>
      cases set? s.frame.locals dstLoc (.init (.scalar sc)) with
      | none =>
        simp only [liftMirStepNode]
        exact AgreeOutsideFields.refl _ s
      | some locals₂ =>
        cases hProt : s.memory.activeProtectors with
        | nil =>
          simp only [liftMirStepNode, MirStepNode.step]
          intro f hf
          cases f with
          | frameBlockIdx => rfl
          | frameStmtIdx => exact False.elim (hf (by simp))
          | frameLocals => exact False.elim (hf (by simp))
          | mem mf =>
            cases mf with
            | borrows => exact False.elim (hf (by simp))
            | activeProtectors => exact hProt
            | _ => rfl
        | cons ph pt =>
          cases hConf : hasProtectedWriteConflict s.memory.borrows (ph :: pt) dstLoc .none .nil 0 0
              (length s.memory.callStack) with
          | true =>
            simp only [hConf, liftMirStepNode, MirStepNode.fail]
            exact AgreeOutsideFields.refl _ s
          | false =>
            simp only [hConf, liftMirStepNode, MirStepNode.step]
            intro f hf
            cases f with
            | frameBlockIdx => rfl
            | frameStmtIdx => exact False.elim (hf (by simp))
            | frameLocals => exact False.elim (hf (by simp))
            | mem mf =>
              cases mf with
              | borrows => exact False.elim (hf (by simp))
              | activeProtectors => exact hProt
              | _ => rfl

/-- `TerminatorKind.unreachable` and `TerminatorKind.unwindTerminate` modify ZERO fields (`[]`). -/
theorem unreachable_modifiesOnlyFields (span : String) (currentBody : Option CapturedMir) :
    ModifiesOnlyFields []
      (evalTerminatorAction { kind := .unreachable, span := span } currentBody) :=
  fun s => AgreeOutsideFields.refl [] s

theorem unwindTerminate_modifiesOnlyFields (span : String) (currentBody : Option CapturedMir) :
    ModifiesOnlyFields []
      (evalTerminatorAction { kind := .unwindTerminate, span := span } currentBody) :=
  fun s => AgreeOutsideFields.refl [] s

/-! ### C.3. Ergonomic `anneal_veil_frame` Tactic / Macro -/

/-- Automatically discharge named-field `AnnealExactWP` preservation goals (`veil#209` style)
using `veil_frame_preserves` / `exactWP_veil_frame`, resolving `ReadsOnlyFields` for standard
named framing combinators (`frame_locals`, `frame_callerLocals`, `frame_borrows`, `frame_globals`,
`frame_heap`, `frame_callStack`, `frame_protectors`, and conjunctions), `ModifiesOnlyFields`
(including `modifiesOnlyFields_bind` / `modifiesOnlyFields_seq`), and `disjointFieldsBool = true`
by `decide`! -/
macro "anneal_veil_frame" : tactic =>
  `(tactic| (
    first
    | (apply veil_frame_preserves
       · first | assumption | apply modifiesOnlyFields_seq <;> assumption | apply modifiesOnlyFields_bind <;> assumption
       · repeat (first
           | apply readsOnlyFields_and
           | apply frame_locals_readsOnly
           | apply frame_callerLocals_readsOnly
           | apply frame_borrows_readsOnly
           | apply frame_globals_readsOnly
           | apply frame_heap_readsOnly
           | apply frame_callStack_readsOnly
           | apply frame_protectors_readsOnly
           | assumption)
       · decide
       · assumption)
    | (apply exactWP_veil_frame
       · first | assumption | apply modifiesOnlyFields_seq <;> assumption | apply modifiesOnlyFields_bind <;> assumption
       · repeat (first
           | apply readsOnlyFields_and
           | apply frame_locals_readsOnly
           | apply frame_callerLocals_readsOnly
           | apply frame_borrows_readsOnly
           | apply frame_globals_readsOnly
           | apply frame_heap_readsOnly
           | apply frame_callStack_readsOnly
           | apply frame_protectors_readsOnly
           | assumption)
       · exact disjointFieldsBool_sound (by decide)
       · assumption
       · assumption)))

/-- End-to-end demonstration of `anneal_veil_frame` discharging multi-step preservation of
`(globals, callerLocals, callStack)` across `assign_const_local ; restoreCallerProtectors ;
disableFrameBorrows` in ONE tactic call! -/
theorem anneal_veil_frame_multistep_demo (dstLoc : Local) (ty : Ty) (sc : ScalarInt)
    (caller : SavedCallerFrame) (depth nLocals : Nat)
    (Pglob : List CapturedAllocation → Prop) (Pcall : List SavedCallerFrame → Prop)
    (s : MachineState) (hInv : frame_globals Pglob s ∧ frame_callStack Pcall s) :
    let act :=
      ExactAction.seq
        (evalStmtAction { kind := .assign ⟨dstLoc, []⟩ (.use (mkConstScalarOp ty sc)), span := "demo" })
        (ExactAction.seq (restoreCallerProtectorsAction caller) (disableFrameBorrowsAction depth nLocals))
    AnnealExactWP act (fun _ s' => frame_globals Pglob s' ∧ frame_callStack Pcall s')
      (fun _ s' => frame_globals Pglob s' ∧ frame_callStack Pcall s') s := by
  have hMod1 := assign_const_local_modifiesOnlyFields dstLoc ty sc "demo" .nil emptyLayoutTable
  have hMod2 := restoreCallerProtectors_modifiesOnlyFields caller
  have hMod3 := disableFrameBorrows_modifiesOnlyFields depth nLocals
  have hMod23 := modifiesOnlyFields_seq hMod2 hMod3
  have hMod := modifiesOnlyFields_seq hMod1 hMod23
  anneal_veil_frame

end VeilFrame

/-! ## Part D. Episode 2 Core Capstone & Silent Import / Axiom / Bridge-Reality Audit -/

/-- **Episode 2 Core Capstone (`Anneal.ExactWpAndSmartCtors`)**: bundles Part A (`Std.Do`-free
`ExactWP`, `TreeBorrowsFrameWP`, `ProtectorReleaseWP`, `ExactBodySafetyVC`), Part B (`Bitprism`
smart constructors + negative UB non-erasure refutations + coalescing `mkMemWriteFrame`), and
Part C (`veil_frame` 14-field `Memory` framing + `anneal_veil_frame` tactic). -/
theorem ep2_exact_wp_smart_ctors_and_veil_frame_capstone :
    (type_of% @exactWP_iff) ∧
    (type_of% @exactWP_bind) ∧
    (type_of% @exactWP_foldl) ∧
    (type_of% @exactWP_negation_refutation) ∧
    (type_of% @treeBorrowsFrameWP_committed_prefix_on_error) ∧
    (type_of% @protectorReleaseWP_error_preserves_prefix) ∧
    (type_of% @exactBodySafetyVC_iff) ∧
    (type_of% @exactBodySafetyVC_loop_invariant) ∧
    (type_of% @exactBodySafetyVC_concrete_trusted_bodies) ∧
    (type_of% @frameDeallocProtectorExactWP_iff) ∧
    (type_of% @mkAddSmart_eq_raw) ∧
    (type_of% @mkSubSmart_eq_raw) ∧
    (type_of% @mkMulSmart_eq_raw) ∧
    (type_of% @mkBitAndSmart_eq_raw) ∧
    (type_of% @mkBitOrSmart_eq_raw) ∧
    (type_of% @mkBitXorSmart_eq_raw) ∧
    (type_of% @mkShlSmart_eq_raw) ∧
    (type_of% @mkShrSmart_eq_raw) ∧
    (type_of% @mkPtrOffsetSmart_eq_raw) ∧
    (type_of% @mkWrappingPtrOffsetSmart_eq_raw) ∧
    (type_of% @bitprism_nested_collapse_o1) ∧
    (type_of% @mkAddSmartRvalue_zero_right_eq_raw) ∧
    (type_of% @mkSubSmartRvalue_zero_right_eq_raw) ∧
    (type_of% @mkBitAndSmartRvalue_zero_left_eq_raw) ∧
    (type_of% @mkBitAndSmartRvalue_zero_right_eq_raw) ∧
    (type_of% @mkMulSmartRvalue_zero_left_eq_raw) ∧
    (type_of% @mkMulSmartRvalue_zero_right_eq_raw) ∧
    (type_of% @mkBitOrSmartRvalue_allOnes_left_eq_raw) ∧
    (type_of% @mkBitOrSmartRvalue_allOnes_right_eq_raw) ∧
    (type_of% @mkSmartRvalue_never_erases_ub) ∧
    (type_of% @bitprism_const_annihilators_fire) ∧
    (type_of% @bitprism_const_width_mismatch_preserves_unsupported) ∧
    (type_of% @bitprism_identity_preconditions_necessary) ∧
    (type_of% @mkAddSmartRvalue_ok_of_raw_ok) ∧
    (type_of% @bitAnd_zero_dead_local_preserves_ub) ∧
    (type_of% @bitAnd_zero_uninit_local_preserves_ub) ∧
    (type_of% @mul_zero_uninit_local_preserves_ub) ∧
    (type_of% @bitOr_allOnes_uninit_local_preserves_ub) ∧
    (type_of% @addUnchecked_overflow_preserves_ub) ∧
    (type_of% @mkMemWriteFrame_eq_raw) ∧
    (type_of% @mkMemWriteFrame_dead_slot_preserves_failure) ∧
    (type_of% @Memory.ext_allFields) ∧
    (type_of% @MachineState.ext_allFields) ∧
    (type_of% @exactWP_veil_frame) ∧
    (type_of% @anneal_veil_frame_multistep_demo) :=
  ⟨@exactWP_iff, @exactWP_bind, @exactWP_foldl, @exactWP_negation_refutation,
   @treeBorrowsFrameWP_committed_prefix_on_error, @protectorReleaseWP_error_preserves_prefix,
   @exactBodySafetyVC_iff, @exactBodySafetyVC_loop_invariant,
   @exactBodySafetyVC_concrete_trusted_bodies, @frameDeallocProtectorExactWP_iff,
   @mkAddSmart_eq_raw, @mkSubSmart_eq_raw, @mkMulSmart_eq_raw, @mkBitAndSmart_eq_raw,
   @mkBitOrSmart_eq_raw, @mkBitXorSmart_eq_raw, @mkShlSmart_eq_raw, @mkShrSmart_eq_raw,
   @mkPtrOffsetSmart_eq_raw, @mkWrappingPtrOffsetSmart_eq_raw, @bitprism_nested_collapse_o1,
   @mkAddSmartRvalue_zero_right_eq_raw, @mkSubSmartRvalue_zero_right_eq_raw,
   @mkBitAndSmartRvalue_zero_left_eq_raw, @mkBitAndSmartRvalue_zero_right_eq_raw,
   @mkMulSmartRvalue_zero_left_eq_raw, @mkMulSmartRvalue_zero_right_eq_raw,
   @mkBitOrSmartRvalue_allOnes_left_eq_raw, @mkBitOrSmartRvalue_allOnes_right_eq_raw,
   @mkSmartRvalue_never_erases_ub, @bitprism_const_annihilators_fire,
   @bitprism_const_width_mismatch_preserves_unsupported,
   @bitprism_identity_preconditions_necessary, @mkAddSmartRvalue_ok_of_raw_ok,
   @bitAnd_zero_dead_local_preserves_ub, @bitAnd_zero_uninit_local_preserves_ub,
   @mul_zero_uninit_local_preserves_ub, @bitOr_allOnes_uninit_local_preserves_ub,
   @addUnchecked_overflow_preserves_ub, @mkMemWriteFrame_eq_raw,
   @mkMemWriteFrame_dead_slot_preserves_failure, @Memory.ext_allFields,
   @MachineState.ext_allFields, @exactWP_veil_frame, @anneal_veil_frame_multistep_demo⟩

/-!
Note on import minimality & kernel audits:
`Anneal.ExactWpAndSmartCtors` imports ONLY `Trusted` (which itself imports only `Init`), ensuring
zero direct OR transitive imports of `Std.Do`, `Std.Tactic.Do`, `Std.WP`, `Lean`, `Miri`,
`LeanMiriSpec`, or `MiniRustSpec`. Full cross-root transitive import isolation, bridge-reality
reachability, choice-free core WP verification, and standard-3-axiom audits over every declaration
in this module are enforced by `tests/mir/CrossFramePanicAndExactWpTests.lean` and
`anneal-lsp audit-preview`.
-/

end Anneal.ExactWpAndSmartCtors

