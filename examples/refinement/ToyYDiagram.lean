import Anneal.Refinement

/-!
Concrete toy languages, transformations, and program proofs illustrating the
Layer 1A refinement primitives (`LE`, `Semantics`, `Spec`, `GuardedRefines`,
`Partial`, `Language`, `Compiles`, `Abstracts`) and the end-to-end Y-diagram
theorems (`anneal_is_correct` and `verify_on_through_passes`).
-/

namespace Anneal.Examples.ToyYDiagram

open Trusted.Refinement
open Anneal.Refinement

/-- Execution outcomes of a toy expression. -/
inductive Outcome where
  | ok (value : Nat)
  | abort
  | ub
  deriving DecidableEq, Repr

/-- A toy behavior is the set of outcomes a program may produce. -/
abbrev ToyBehavior := BehaviorSet Outcome

def Outcome.isUB : Outcome → Prop
  | .ub => True
  | _ => False

/-- Undefined-behavior freedom as an ordinary downward-closed `Spec`. -/
def ToyNoUB : Spec ToyBehavior :=
  BehaviorSet.forbidSpec Outcome.isUB

/-- Functional specification requiring every outcome to be `.ok expected`. -/
def ReturnsValue (expected : Nat) : Spec ToyBehavior :=
  BehaviorSet.allSpec (fun o => o = .ok expected)

def detFour : ToyBehavior := (· = .ok 4)
def nondetFourFive : ToyBehavior := fun o => o = .ok 4 ∨ o = .ok 5
def withUB : ToyBehavior := fun o => o = .ok 4 ∨ o = .ok 5 ∨ o = .ub

theorem detFour_refines_nondet : detFour ≤ nondetFourFive :=
  fun _ h => .inl h

theorem nondet_refines_withUB : nondetFourFive ≤ withUB :=
  fun _ => fun | .inl h => .inl h | .inr h => .inr (.inl h)

theorem detFour_refines_withUB : detFour ≤ withUB :=
  calc detFour
    _ ≤ nondetFourFive := detFour_refines_nondet
    _ ≤ withUB         := nondet_refines_withUB

theorem noUB_nondetFourFive : ToyNoUB.holds nondetFourFive := by
  rintro _ (rfl | rfl) h_ub <;> exact h_ub

theorem noUB_detFour_by_downward_closure : ToyNoUB.holds detFour :=
  ToyNoUB.downward_closed detFour_refines_nondet noUB_nondetFourFive

/-- Toy IR with nondeterminism and unchecked/checked division. -/
inductive ToyMir where
  | lit (n : Nat)
  | add (left right : ToyMir)
  | divUnchecked (num den : Nat)
  | divChecked (num den : Nat)
  | both (left right : ToyMir)

/-- Evaluate `ToyMir` to its set of possible outcomes. -/
def evalMir : ToyMir → ToyBehavior
  | .lit n => (· = .ok n)
  | .add l r => fun o =>
      (∃ v₁ v₂, evalMir l (.ok v₁) ∧ evalMir r (.ok v₂) ∧ o = .ok (v₁ + v₂)) ∨
      (evalMir l .abort ∧ o = .abort) ∨
      (evalMir r .abort ∧ o = .abort) ∨
      (evalMir l .ub ∧ o = .ub) ∨
      (evalMir r .ub ∧ o = .ub)
  | .divUnchecked num den => fun o =>
      if den = 0 then o = .ub else o = .ok (num / den)
  | .divChecked num den => fun o =>
      if den = 0 then o = .abort else o = .ok (num / den)
  | .both l r => fun o => evalMir l o ∨ evalMir r o

def ToyMirSem : Semantics ToyMir ToyBehavior := evalMir

/-- Toy target machine where division is a total hardware operation (`x / 0 = 0`). -/
inductive ToyTarget where
  | lit (n : Nat)
  | add (left right : ToyTarget)
  | hwDiv (num den : Nat)
  | checkedDiv (num den : Nat)

def evalTarget : ToyTarget → ToyBehavior
  | .lit n => (· = .ok n)
  | .add l r => fun o =>
      (∃ v₁ v₂, evalTarget l (.ok v₁) ∧ evalTarget r (.ok v₂) ∧ o = .ok (v₁ + v₂)) ∨
      (evalTarget l .abort ∧ o = .abort) ∨
      (evalTarget r .abort ∧ o = .abort)
  | .hwDiv num den => (· = .ok (num / den))
  | .checkedDiv num den => fun o =>
      if den = 0 then o = .abort else o = .ok (num / den)

def ToyTargetSem : Semantics ToyTarget ToyBehavior := evalTarget

/-- Compile `ToyMir` to `ToyTarget` by picking `l` in `both l r` and `hwDiv`. -/
def compileLeft : ToyMir → ToyTarget
  | .lit n => .lit n
  | .add l r => .add (compileLeft l) (compileLeft r)
  | .divUnchecked num den => .hwDiv num den
  | .divChecked num den => .checkedDiv num den
  | .both l _ => compileLeft l

theorem compileLeft_refines_of_noUB (p : ToyMir)
    (h_noUB : ToyNoUB.holds (ToyMirSem p)) :
    ToyTargetSem (compileLeft p) ≤ ToyMirSem p := by
  induction p with
  | lit _ => exact fun _ h => h
  | add l r ihl ihr =>
    have hl : ToyNoUB.holds (ToyMirSem l) := by
      rintro (_ | _ | _) ho hub
      · exact hub
      · exact hub
      · exact h_noUB (.inr (.inr (.inr (.inl ⟨ho, rfl⟩)))) trivial
    have hr : ToyNoUB.holds (ToyMirSem r) := by
      rintro (_ | _ | _) ho hub
      · exact hub
      · exact hub
      · exact h_noUB (.inr (.inr (.inr (.inr ⟨ho, rfl⟩)))) trivial
    rintro o (⟨v₁, v₂, hv₁, hv₂, heq⟩ | hab | hab)
    · exact .inl ⟨v₁, v₂, ihl hl _ hv₁, ihr hr _ hv₂, heq⟩
    · exact .inr (.inl ⟨ihl hl _ hab.1, hab.2⟩)
    · exact .inr (.inr (.inl ⟨ihr hr _ hab.1, hab.2⟩))
  | divUnchecked num den =>
    intro o ho
    by_cases h0 : den = 0
    · exact False.elim (@h_noUB .ub (by simp [ToyMirSem, evalMir, h0]) trivial)
    · simpa [ToyMirSem, evalMir, compileLeft, evalTarget, ToyTargetSem, h0] using ho
  | divChecked _ _ => exact fun _ h => h
  | both l _ ihl _ =>
    exact fun _ ho => .inl (ihl (fun _ h hub => h_noUB (.inl h) hub) _ ho)

theorem compileLeft_is_compilerPass (p : ToyMir) :
    CompilerPass ToyMirSem ToyTargetSem ToyNoUB id p (compileLeft p) :=
  compileLeft_refines_of_noUB p

/-- Without `ToyNoUB`, `compileLeft` does not refine `ToyMirSem` on `10 / 0`. -/
theorem compileLeft_not_unconditional :
    ¬ (ToyTargetSem (compileLeft (.divUnchecked 10 0)) ≤
        ToyMirSem (.divUnchecked 10 0)) := by
  intro h_ref
  have h_mir := h_ref (.ok 0) rfl
  simp [ToyMirSem, evalMir] at h_mir

/-- Verifier normalization pass `p ↦ both p p`. -/
def verifNormalize (p : ToyMir) : ToyMir := .both p p

theorem verifNormalize_is_verifierPass (p : ToyMir) :
    VerifierPass ToyMirSem ToyMirSem ToyNoUB id p (verifNormalize p) :=
  fun _ _ ho => .inl ho

/-- Bug-finder pass exploring only the left branch of `both l r`. -/
def exploreLeft : ToyMir → ToyMir
  | .both l _ => exploreLeft l
  | p => p

theorem exploreLeft_is_bugFinderPass (p : ToyMir) :
    BugFinderPass ToyMirSem ToyMirSem id p (exploreLeft p) := by
  induction p with
  | both _ _ ihl _ => exact fun _ _ ho => .inl (ihl trivial _ ho)
  | _ => exact fun _ _ ho => ho

def Outcome.ubToAbort : Outcome → Outcome
  | .ok v => .ok v
  | .abort | .ub => .abort

def ubToAbortBehavior : ToyBehavior → ToyBehavior :=
  BehaviorSet.map Outcome.ubToAbort

theorem ubToAbortBehavior_noUB (b : ToyBehavior) :
    ToyNoUB.holds (ubToAbortBehavior b) := by
  rintro _ ⟨(_ | _ | _), _, rfl⟩ hub <;> exact hub

/-- Sanitizer pass rewriting `divUnchecked` to `divChecked`. -/
def sanitizeDiv : ToyMir → ToyMir
  | .lit n => .lit n
  | .add l r => .add (sanitizeDiv l) (sanitizeDiv r)
  | .divUnchecked num den | .divChecked num den => .divChecked num den
  | .both l r => .both (sanitizeDiv l) (sanitizeDiv r)

theorem sanitizeDiv_refines (p : ToyMir) :
    ToyMirSem (sanitizeDiv p) ≤ ubToAbortBehavior (ToyMirSem p) := by
  induction p with
  | lit n => intro o ho; exact ⟨.ok n, rfl, ho.symm⟩
  | add l r ihl ihr =>
    rintro o (⟨v₁, v₂, hv₁, hv₂, rfl⟩ | ⟨hab, rfl⟩ | ⟨hab, rfl⟩ | ⟨hub, _⟩ | ⟨hub, _⟩)
    · rcases ihl _ hv₁ with ⟨(_ | _ | _), hx₁, heq₁⟩ <;> cases heq₁
      rcases ihr _ hv₂ with ⟨(_ | _ | _), hx₂, heq₂⟩ <;> cases heq₂
      exact ⟨.ok (v₁ + v₂), .inl ⟨v₁, v₂, hx₁, hx₂, rfl⟩, rfl⟩
    · rcases ihl _ hab with ⟨(_ | _ | _), hx₁, heq₁⟩ <;> cases heq₁
      · exact ⟨.abort, .inr (.inl ⟨hx₁, rfl⟩), rfl⟩
      · exact ⟨.ub, .inr (.inr (.inr (.inl ⟨hx₁, rfl⟩))), rfl⟩
    · rcases ihr _ hab with ⟨(_ | _ | _), hx₂, heq₂⟩ <;> cases heq₂
      · exact ⟨.abort, .inr (.inr (.inl ⟨hx₂, rfl⟩)), rfl⟩
      · exact ⟨.ub, .inr (.inr (.inr (.inr ⟨hx₂, rfl⟩))), rfl⟩
    · rcases ihl _ hub with ⟨(_ | _ | _), _, heq⟩ <;> cases heq
    · rcases ihr _ hub with ⟨(_ | _ | _), _, heq⟩ <;> cases heq
  | divUnchecked num den =>
    intro o ho; by_cases h0 : den = 0
    · simp [ToyMirSem, evalMir, sanitizeDiv, h0] at ho
      exact ⟨.ub, by simp [ToyMirSem, evalMir, h0], ho.symm⟩
    · simp [ToyMirSem, evalMir, sanitizeDiv, h0] at ho
      exact ⟨.ok (num / den), by simp [ToyMirSem, evalMir, h0], ho.symm⟩
  | divChecked num den =>
    intro o ho; by_cases h0 : den = 0
    · simp [ToyMirSem, evalMir, sanitizeDiv, h0] at ho
      exact ⟨.abort, by simp [ToyMirSem, evalMir, h0], ho.symm⟩
    · simp [ToyMirSem, evalMir, sanitizeDiv, h0] at ho
      exact ⟨.ok (num / den), by simp [ToyMirSem, evalMir, h0], ho.symm⟩
  | both _ _ ihl ihr =>
    rintro o (hl | hr)
    · rcases ihl _ hl with ⟨x, hx, heq⟩; exact ⟨x, .inl hx, heq⟩
    · rcases ihr _ hr with ⟨x, hx, heq⟩; exact ⟨x, .inr hx, heq⟩

theorem sanitizeDiv_is_sanitizerPass (p : ToyMir) :
    SanitizerPass ToyMirSem ToyMirSem ubToAbortBehavior p (sanitizeDiv p) :=
  fun _ => sanitizeDiv_refines p

theorem sanitizeDiv_always_noUB (p : ToyMir) :
    ToyNoUB.holds (ToyMirSem (sanitizeDiv p)) :=
  SanitizerPass.unconditional_safety (sanitizeDiv_is_sanitizerPass p)
    ToyNoUB (ubToAbortBehavior_noUB (ToyMirSem p))

/-! ## End-to-End Program Verification via `anneal_is_correct` -/

def exampleProg : ToyMir :=
  .both (.divUnchecked 12 3) (.add (.lit 2) (.lit 2))

theorem exampleProg_verif_returns_four :
    (ReturnsValue 4).holds (ToyMirSem (verifNormalize exampleProg)) := by
  have reduce_branch : ∀ {o}, ToyMirSem exampleProg o → o = .ok 4 := by
    rintro o (hdiv | ⟨v₁, v₂, hv₁, hv₂, rfl⟩ | ⟨hab, _⟩ | ⟨hab, _⟩ | ⟨hub, _⟩ | ⟨hub, _⟩)
    · exact hdiv
    · cases hv₁; cases hv₂; rfl
    · cases hab
    · cases hab
    · cases hub
    · cases hub
  rintro o (h | h) <;> exact reduce_branch h

theorem exampleProg_verif_noUB :
    ToyNoUB.holds (ToyMirSem (verifNormalize exampleProg)) := by
  intro o ho hub
  rw [exampleProg_verif_returns_four ho] at hub
  exact hub

theorem exampleProg_compiled_returns_four :
    (ReturnsValue 4).holds (ToyTargetSem (compileLeft exampleProg)) :=
  anneal_is_correct
    ToyMirSem ToyMirSem ToyTargetSem ToyNoUB ToyNoUB
    some compileLeft id monotone_id compileLeft_is_compilerPass
    exampleProg exampleProg (verifNormalize exampleProg) id rfl
    (verifNormalize_is_verifierPass exampleProg) (fun _ h => h)
    exampleProg_verif_noUB (ReturnsValue 4) exampleProg_verif_returns_four

/-! ## Per-Query `Partial` Refinement via `Language`, `Compiles`, and `Abstracts` -/

abbrev DivQuery : Type := Nat × Nat

inductive ToyQueryMir where
  | div
  | safeDiv
  | both (left right : ToyQueryMir)

def evalQueryMir : ToyQueryMir → DivQuery → Partial (BehaviorSet Nat)
  | .div, q => ⟨q.2 ≠ 0, fun _ out => out = q.1 / q.2⟩
  | .safeDiv, q => Partial.pure (· = q.1 / q.2)
  | .both l r, q =>
    ⟨(evalQueryMir l q).defined ∧ (evalQueryMir r q).defined,
     fun h out => (evalQueryMir l q).val h.1 out ∨ (evalQueryMir r q).val h.2 out⟩

def ToyMirLang : Language where
  Prog := ToyQueryMir
  Query := DivQuery
  Out := Nat
  sem := evalQueryMir

inductive ToyQueryTarget where
  | hwDiv

def evalQueryTarget : ToyQueryTarget → DivQuery → Partial (BehaviorSet Nat)
  | .hwDiv, q => Partial.pure (· = q.1 / q.2)

def ToyTargetLang : Language where
  Prog := ToyQueryTarget
  Query := DivQuery
  Out := Nat
  sem := evalQueryTarget

theorem div_defined_iff (x y : Nat) :
    (ToyMirLang.sem .div (x, y)).defined ↔ y ≠ 0 := Iff.rfl

theorem div_zero_equiv_ub (x : Nat) :
    ToyMirLang.sem .div (x, 0) = Partial.ub :=
  Partial.ext ⟨fun h => h rfl, False.elim⟩ (fun h => False.elim (h rfl))

def compileQueryLeft : ToyQueryMir → ToyQueryTarget
  | .div | .safeDiv => .hwDiv
  | .both l _ => compileQueryLeft l

theorem compileQueryLeft_compiles (p : ToyQueryMir) :
    Compiles ToyMirLang ToyTargetLang id p (compileQueryLeft p) := by
  induction p with
  | div | safeDiv => exact fun _ _ => ⟨trivial, fun _ h => h⟩
  | both l _ ihl _ =>
    intro q ⟨hl, _⟩
    rcases ihl q hl with ⟨hd, hr⟩
    exact ⟨hd, fun _ h => .inl (hr _ h)⟩

def verifQueryNormalize (p : ToyQueryMir) : ToyQueryMir := .both p p

theorem verifQueryNormalize_abstracts (p : ToyQueryMir) :
    Abstracts ToyMirLang ToyMirLang id (verifQueryNormalize p) p :=
  fun _ ⟨hd, _⟩ => ⟨hd, fun _ h => .inl h⟩

def divContract : ToyMirLang.Behavior :=
  ToyMirLang.ContractSpec (fun q => q.2 ≠ 0) (fun _ => True) (fun q out => out = q.1 / q.2)

theorem verifQueryNormalize_div_refines_contract :
    ToyMirLang.sem (verifQueryNormalize .div) ≤ divContract :=
  fun _ h => ⟨⟨h, h⟩, fun _ ho _ => ho.elim id id⟩

theorem div_verified_on_nonzero :
    ToyMirLang.sem .div ≤ ToyMirLang.WellFormedOn (fun q => q.2 ≠ 0) ∧
    ToyTargetLang.sem (compileQueryLeft .div) ≤ divContract :=
  verify_on_through_passes
    (L_src := ToyMirLang) (L_v := ToyMirLang) (L_tgt := ToyTargetLang)
    monotone_id monotone_id
    (compileQueryLeft_compiles .div)
    (verifQueryNormalize_abstracts .div)
    verifQueryNormalize_div_refines_contract
    (Language.contractSpec_refines_wellFormedOn (L := ToyMirLang)
      (fun q => q.2 ≠ 0) (fun _ => True) (fun q out => out = q.1 / q.2))

end Anneal.Examples.ToyYDiagram
