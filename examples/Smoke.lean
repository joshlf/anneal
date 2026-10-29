-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Anneal

/-!
# Worked Examples: Literature Encodings and UB Refinements

This module demonstrates how `Trusted.Language` (`Query → Partial (Out → Prop)`)
and `Trusted.SmallStepMachine` (`Trusted.Refinement`, `Trusted.StepResult`)
model a wide range of verification and compilation paradigms within a single
refinement preorder (`≤`):

1. **Structural Non-Vacuity (`unitMachine`):** Constructive prefix existence at
   every finite step budget via `non_vacuity_at_every_depth`.
2. **Literature Models as Special Cases of `Language`:**
   - **2.1 Hoare Logic / Dijkstra Weakest Preconditions (`wp`) & Fiat `ProgOk`
     (`HoareExamples`):** Proves the exact order-isomorphism between
     `State → Partial (State → Prop)` and monotone conjunctive predicate
     transformers `wp`, and demonstrates the separation of safety
     preconditions (`.defined`) from functional preconditions (`.val`) on a
     safe `binary_search` specification vs. an `unsafe` indexing specification.
   - **2.2 Aeneas `DWP` (Total Correctness) vs. `DWLP` (Partial Correctness)
     (`AeneasExamples`):** Instantiates `Language` twice over the same monadic
     evaluator—placing divergence in `.defined` for `DWP` and in `Out` for
     `DWLP`—and proves that a safe infinite loop satisfies `DWLP`
     well-formedness
     while refuting `DWP` well-formedness.
   - **2.3 Alive2 Per-Input State Refinement (`Alive2Examples`):** Separates
     input-level `UB` (`defined = False`, top element) from LLVM `poison` (a
     defined outcome in `Out` that compiles to any concrete value).
   - **2.4 Iris / `iris-lean` Step-Indexed `NotStuck` Adequacy
     (`IrisExamples`):**
     Models step-indexed `NotStuck` adequacy as `IrisLang.sem p ≤
     IrisLang.WellFormed`.
   - **2.5 CompCert `program_behavior` and `behavior_improves`
     (`CompCertExamples`):**
     Indexes `.defined` by finite external I/O trace prefixes `tr : List Event`
     so that `goesWrong tr` makes `(sem p tr).defined = False`, allowing a
     compiler to replace `goesWrong tr` with any behavior extending `tr` while
     preserving all prefixes that cannot go wrong.
3. **Language Without a Single Deterministic Sequence of Execution States
   (`TrueConcurrencyExamples`):** Models a partial-order causal event-structure
   language with no step counter or sequential machine state, encoding
   concurrent conflict freedom in `.defined` (see also `AnnealTests.AxiomaticMP`
   in `tests/Smoke.lean` for a two-thread C++20/Rust happens-before weak-memory
   litmus test).
4. **Non-Time-Traveling UB Preserving Well-Defined Prefixes
   (`PrefixPreservationExamples`):** Shows that when a program emits an
   externally observable effect at step `1` and triggers UB at step `2`, every
   valid compilation (`Compiles`) must preserve the well-defined `1`-step prefix
   while remaining unconstrained from step `2` onward.
5. **Selective Time-Traveling UB (`SelectiveTimeTravelExamples`):** Models two
   forms of UB (`UBA` and `UBB`) and two observable behaviors (`BA` and `BB`)
   where `UBA` can time-travel over `BA` but not `BB`, while `UBB` can
   time-travel over `BB` but not `BA`.
6. **Library Conditionality (`LibraryConditionality`):**
   Demonstrates how `VerificationResultOn` and `VerificationResult` verify both
   safe library functions with conditional functional guarantees (where a
   specification's `.defined` may be `False` outside its functional domain, or
   even unsatisfiable as in `x > 0 && x < 0`, without weakening baseline
   `WellFormed`) and `unsafe` library functions whose baseline safety is
   conditional on a caller `# Safety` precondition `pre`.
-/

namespace AnnealExamples

open Trusted
open Anneal

/-!
## 1. Minimal Small-Step Machine and Structural Non-Vacuity
-/

/-- Trivial one-state small-step machine that terminates immediately with
    `()`. -/
def unitMachine : SmallStepMachine Unit Unit Unit Unit where
  initState _ _ := True
  step _ _ r := r = .terminated (.normal ())

theorem unitMachine_total : TotalStep unitMachine :=
  fun _ _ => ⟨.terminated (.normal ()), rfl⟩

theorem unitMachine_inhabited : InhabitedDemonic unitMachine := by
  intro _ _ _ _ h
  cases h

theorem unitMachine_non_vacuous (n : Nat) :
    ∃ out : ExecOut Unit Unit,
      ReachesPrefix unitMachine () () n () out.trace out.outcome ∧
      out.outcome ≠ .stuck := by
  cases non_vacuity_at_every_depth unitMachine_total unitMachine_inhabited () () True.intro n with
  | intro out hout =>
    exact ⟨out, hout.2.1, hout.2.2⟩

/-!
## 2. Literature Models and Specification Separation

### 2.1 Hoare Logic / Predicate Transformers (`wp`) (`HoareExamples`)
-/
namespace HoareExamples

/-- A state-transition language with `Query := State` (initial state) and
    `Out := State` (final state). -/
abbrev HoareLang (State : Type) (Prog : Type)
    (semFn : Prog → State → Partial (State → Prop)) : Language where
  Prog := Prog
  Query := State
  Out := State
  sem := semFn

/-- Map a partial state behavior `b : State → Partial (State → Prop)` to its
    Dijkstra weakest-precondition predicate transformer
    `toWP b s Post := ∃ h : (b s).defined, ∀ s', (b s).val h s' → Post s'`. -/
def toWP {State : Type} (b : State → Partial (State → Prop))
    (s : State) (Post : State → Prop) : Prop :=
  ∃ h : (b s).defined, ∀ s', (b s).val h s' → Post s'

/-- Recover a partial state behavior from a predicate transformer `wp`. -/
def ofWP {State : Type} (wp : State → (State → Prop) → Prop) :
    State → Partial (State → Prop) :=
  fun s => {
    defined := wp s (fun _ => True)
    val := fun _ s' => ∀ Post : State → Prop, wp s Post → Post s'
  }

/-- **Refinement / Weakest-Precondition Isomorphism:**
    In `State → Partial (State → Prop)`, `b₁ ≤ b₂` holds if and only if for
    every initial state `s` and postcondition `Post`, `toWP b₂ s Post` implies
    `toWP b₁ s Post` (contravariant `wp` implication). -/
theorem le_iff_wp_imp {State : Type}
    (b₁ b₂ : State → Partial (State → Prop)) :
    b₁ ≤ b₂ ↔ ∀ (s : State) (Post : State → Prop), toWP b₂ s Post → toWP b₁ s Post := by
  constructor
  · intro hle s Post ⟨hdef₂, hpost₂⟩
    cases hle s hdef₂ with
    | intro hdef₁ hsub =>
      exact ⟨hdef₁, fun s' hs' => hpost₂ s' (hsub s' hs')⟩
  · intro hwp s hdef₂
    have htrue : toWP b₂ s (fun _ => True) := ⟨hdef₂, fun _ _ => True.intro⟩
    cases hwp s (fun _ => True) htrue with
    | intro hdef₁ _ =>
      refine ⟨hdef₁, ?_⟩
      intro s' hs'
      have hpost₂ : toWP b₂ s ((b₂ s).val hdef₂) := ⟨hdef₂, fun _ h => h⟩
      cases hwp s ((b₂ s).val hdef₂) hpost₂ with
      | intro _ hsub =>
        exact hsub s' hs'

/-- Input to a safe `binary_search` function: a flag recording whether the
    input slice is sorted. -/
structure SearchInput where
  sorted : Bool

/-- Output of `binary_search`: whether the returned `Option usize` is a valid
    lookup result for a sorted slice. -/
structure SearchOutput where
  correctForSorted : Bool

/-- Trivial language wrapper for `binary_search` specifications. -/
abbrev SearchLang : Language where
  Prog := Unit
  Query := SearchInput
  Out := SearchOutput
  sem _ q := Partial.pure (fun out => q.sorted = true → out.correctForSorted = true)

/-- **Correct Safe Specification (`binary_search`):**
    Because `binary_search` is a safe Rust function, `.defined` is `True` for
    all inputs (sorted or unsorted) via `SearchLang.Spec`, while the sortedness
    requirement `q.sorted = true` guards the functional postcondition inside
    `.val`. -/
def binarySearchSpec : SearchLang.Behavior :=
  SearchLang.Spec (fun q out => q.sorted = true → out.correctForSorted = true)

/-- `binarySearchSpec` refines `SearchLang.WellFormed`: it guarantees UB-freedom
    across all well-typed inputs, including unsorted slices. -/
theorem binarySearchSpec_wf :
    binarySearchSpec ≤ SearchLang.WellFormed :=
  spec_le_wellFormed _

/-- **Misplaced Precondition (Anti-Pattern):**
    If a specification author mistakenly places `q.sorted = true` into
    `.defined` (`SearchLang.SpecOn`) instead of `.val`, the specification
    allows UB on unsorted slices. -/
def misplacedBinarySearchSpec : SearchLang.Behavior :=
  SearchLang.SpecOn (fun q => q.sorted = true)
    (fun _ out => out.correctForSorted = true)

/-- Placing `q.sorted = true` into `.defined` causes
    `misplacedBinarySearchSpec ≤ SearchLang.WellFormed` to fail on unsorted
    inputs (`{ sorted := false }`), mechanically catching any functional
    precondition that would weaken baseline safe-function UB-freedom. -/
theorem misplacedBinarySearchSpec_not_wf :
    ¬ (misplacedBinarySearchSpec ≤ SearchLang.WellFormed) :=
  not_specOn_le_wellFormed_of_not_pre (q := { sorted := false })
    (by intro h; cases h)

/-- For an `unsafe` function with an explicit caller `# Safety` precondition
    (here `q.sorted = true`), `.defined` records that safety precondition and
    refines `SearchLang.WellFormedOn (fun q => q.sorted = true)`. -/
theorem unsafeSpec_wfOn :
    misplacedBinarySearchSpec ≤ SearchLang.WellFormedOn (fun q => q.sorted = true) :=
  specOn_le_wellFormedOn _ _

end HoareExamples

/-!
### 2.2 Aeneas `DWP` vs. `DWLP` (`AeneasExamples`)
-/
namespace AeneasExamples

/-- Outcome of an Aeneas-style fuel/monadic evaluation: normal return (`ok`),
    nontermination (`diverge`), or assertion/UB failure (`fail`). -/
inductive AeneasRes (Val : Type) where
  | ok (v : Val)
  | diverge
  | fail

/-- Toy Aeneas program returning an `AeneasRes Nat` from an input `Nat`. -/
abbrev AeneasProg := Nat → AeneasRes Nat

/-- **Aeneas Total Correctness (`DWP`):**
    Both `.fail` and `.diverge` make `defined = False`, so `WellFormed` requires
    both safety and termination. -/
abbrev AeneasTotalLang : Language where
  Prog := AeneasProg
  Query := Nat
  Out := Nat
  sem p x := {
    defined := p x ≠ .fail ∧ p x ≠ .diverge
    val := fun _ v => p x = .ok v
  }

/-- **Aeneas Partial Correctness (`DWLP`):**
    Only `.fail` makes `defined = False`; divergence is represented as `none`
    in `Out = Option Nat`, so `WellFormed` requires safety without requiring
    termination. -/
abbrev AeneasPartialLang : Language where
  Prog := AeneasProg
  Query := Nat
  Out := Option Nat
  sem p x := {
    defined := p x ≠ .fail
    val := fun _ out =>
      match out with
      | some v => p x = .ok v
      | none => p x = .diverge
  }

/-- A safe diverging program (`loop {}`). -/
def loopProg : AeneasProg :=
  fun _ => .diverge

/-- `loopProg` is well-formed in `AeneasPartialLang` (`DWLP`): it never
    fails. -/
theorem loopProg_partial_wf :
    AeneasPartialLang.sem loopProg ≤ AeneasPartialLang.WellFormed := by
  refine (le_wellFormed_iff _).mpr ?_
  intro x hfail
  cases hfail

/-- `loopProg` is *not* well-formed in `AeneasTotalLang` (`DWP`), because total
    correctness forbids divergence in `.defined`. -/
theorem loopProg_not_total_wf :
    ¬ (AeneasTotalLang.sem loopProg ≤ AeneasTotalLang.WellFormed) := by
  intro hwf
  have hdef := (le_wellFormed_iff _).mp hwf (0 : Nat)
  exact hdef.2 rfl

end AeneasExamples

/-!
### 2.3 Alive2 Per-Input State Refinement (`poison` vs. `UB`) (`Alive2Examples`)
-/
namespace Alive2Examples

/-- Alive2 value domain: either a concrete integer `val n` or deferred
    `poison`. -/
inductive AliveVal where
  | val (n : Nat)
  | poison

/-- Alive2 expression evaluation result on an input `x : Nat`: either immediate
    `ub` or a defined `AliveVal`. -/
inductive AliveEval where
  | ub
  | defined (v : AliveVal)

/-- In Alive2, `poison` in a source program may be refined by a target program
    either to `poison` or to any concrete value `val n`. -/
def AliveAllows (srcVal : AliveVal) (tgtVal : AliveVal) : Prop :=
  match srcVal with
  | .poison => True
  | .val n => tgtVal = .val n

/-- Alive2 language: immediate `ub` makes `.defined = False` (top element),
    while `defined v` allows any target `AliveVal` satisfying `AliveAllows
    v`. -/
abbrev AliveLang : Language where
  Prog := Nat → AliveEval
  Query := Nat
  Out := AliveVal
  sem p x := {
    defined := p x ≠ .ub
    val := fun _ out =>
      ∃ v, p x = .defined v ∧ AliveAllows v out
  }

/-- Source expression that produces `poison` when `x = 0` and `val x`
    otherwise. -/
def poisonOnZeroProg : Nat → AliveEval
  | 0 => .defined .poison
  | x + 1 => .defined (.val (x + 1))

/-- Target expression that freezes `poison` at `x = 0` to `val 0`. -/
def freezeZeroProg : Nat → AliveEval
  | 0 => .defined (.val 0)
  | x + 1 => .defined (.val (x + 1))

/-- Buggy target expression that triggers immediate `ub` at `x = 0`. -/
def ubOnZeroProg : Nat → AliveEval
  | 0 => .ub
  | x + 1 => .defined (.val (x + 1))

/-- Freezing `poison` to a concrete value `val 0` is a valid Alive2 compilation
    (`Compiles AliveLang AliveLang id poisonOnZeroProg freezeZeroProg`). -/
theorem alive_freeze_compiles_poison :
    Compiles AliveLang AliveLang id poisonOnZeroProg freezeZeroProg := by
  intro (x : Nat) _
  cases x with
  | zero =>
    dsimp [AliveLang, poisonOnZeroProg, freezeZeroProg]
    refine ⟨(by intro h; cases h), ?_⟩
    intro out ⟨v, hv, hallows⟩
    injection hv with hv'
    subst hv'
    exact ⟨.poison, rfl, True.intro⟩
  | succ n =>
    dsimp [AliveLang, poisonOnZeroProg, freezeZeroProg]
    refine ⟨(by intro h; cases h), ?_⟩
    intro out ⟨v, hv, hallows⟩
    injection hv with hv'
    subst hv'
    exact ⟨.val (n + 1), rfl, hallows⟩

/-- Turning a `poison`-producing input (`x = 0`) into immediate `ub` is rejected
    by `Compiles`, because `poisonOnZeroProg` has `.defined = True` at `x =
    0`. -/
theorem alive_ub_does_not_compile_poison :
    ¬ Compiles AliveLang AliveLang id poisonOnZeroProg ubOnZeroProg := by
  intro hcomp
  have hpDef : (AliveLang.sem poisonOnZeroProg (0 : Nat)).defined := by
    intro h; cases h
  cases hcomp (0 : Nat) hpDef with
  | intro hdef _ =>
    exact hdef rfl

end Alive2Examples

/-!
### 2.4 Iris / `iris-lean` Step-Indexed `NotStuck` Adequacy (`IrisExamples`)
-/
namespace IrisExamples

/-- Configuration of an Iris operational semantics: either an expression state
    `expr s` or a terminal value `ret v`. -/
inductive IrisConfig (State Val : Type) where
  | expr (s : State)
  | ret (v : Val)

/-- An Iris transition system parameterized by a single-step relation `step`. -/
structure IrisSystem (State Val : Type) where
  step : State → IrisConfig State Val → Prop

/-- A configuration `c` is `NotStuck` in `sys` when it is either a terminal
    value `ret v` or an expression state `expr s` that can take at least one
    step. -/
def NotStuck {State Val : Type} (sys : IrisSystem State Val) :
    IrisConfig State Val → Prop
  | .ret _ => True
  | .expr s => ∃ c', sys.step s c'

/-- `StepsN sys n c₁ c₂` holds when `c₁` reaches `c₂` in `n` steps of `sys`. -/
inductive StepsN {State Val : Type} (sys : IrisSystem State Val) :
    Nat → IrisConfig State Val → IrisConfig State Val → Prop where
  | zero (c : IrisConfig State Val) :
      StepsN sys 0 c c
  | succ (n : Nat) (s : State) (c' c'' : IrisConfig State Val) :
      sys.step s c' →
      StepsN sys n c' c'' →
      StepsN sys (n + 1) (.expr s) c''

/-- Iris step-indexed language (`Query := State × Nat`, `Out := IrisConfig State
    Val`):
    - `defined`: every configuration `c'` reachable in `n` steps from `s`
      satisfies `NotStuck`.
    - `val`: the set of configurations reachable in `n` steps from `s`. -/
abbrev IrisLang (State Val : Type) : Language where
  Prog := IrisSystem State Val
  Query := State × Nat
  Out := IrisConfig State Val
  sem sys q := {
    defined := ∀ c', StepsN sys q.2 (.expr q.1) c' → NotStuck sys c'
    val := fun _ c' => StepsN sys q.2 (.expr q.1) c'
  }

/-- **Iris Adequacy as `WellFormed` Refinement:**
    `IrisLang.sem sys ≤ IrisLang.WellFormed` is equivalent to Iris's
    step-indexed
    adequacy statement (`∀ s n c', StepsN sys n (.expr s) c' → NotStuck sys
    c'`). -/
theorem iris_adequacy_iff_le_wellFormed {State Val : Type}
    (sys : IrisSystem State Val) :
    (IrisLang State Val).sem sys ≤ (IrisLang State Val).WellFormed ↔
      ∀ (s : State) (n : Nat) (c' : IrisConfig State Val),
        StepsN sys n (.expr s) c' → NotStuck sys c' := by
  constructor
  · intro hwf s n c' hsteps
    exact (le_wellFormed_iff _).mp hwf (s, n) c' hsteps
  · intro hadq
    refine (le_wellFormed_iff _).mpr ?_
    intro ⟨s, n⟩ c' hsteps
    exact hadq s n c' hsteps

end IrisExamples

/-!
### 2.5 CompCert `program_behavior` and `behavior_improves` (`CompCertExamples`)
-/
namespace CompCertExamples

/-- Whole-program execution behaviors in CompCert (`Event` = external I/O
    syscalls/volatiles, `Ret` = exit code):
    - `terminates tr r`: emits finite trace `tr` and halts with `r`.
    - `diverges tr`: emits finite trace `tr` and loops silently forever.
    - `goesWrong tr`: emits finite trace `tr` and then triggers Undefined
      Behavior. -/
inductive WholeProgBehavior (Event Ret : Type) where
  | terminates (trace : List Event) (ret : Ret)
  | diverges (trace : List Event)
  | goesWrong (trace : List Event)

/-- Extract the external I/O trace of a `WholeProgBehavior`. -/
def WholeProgBehavior.trace {Event Ret : Type} :
    WholeProgBehavior Event Ret → List Event
  | .terminates tr _ => tr
  | .diverges tr => tr
  | .goesWrong tr => tr

/-- Prefix relation on external event lists (`tr₁` is a prefix of `tr₂`). -/
def IsTracePrefix {Event : Type} (tr₁ tr₂ : List Event) : Prop :=
  ∃ suffix, tr₁ ++ suffix = tr₂

/-- CompCert language (`Query := List Event` external I/O trace prefix,
    `Out := WholeProgBehavior Event Ret`):
    - At query prefix `tr`, `(sem p tr).defined` holds when no execution of `p`
      goes wrong with a trace prefix `tr₀` of `tr` (`IsTracePrefix tr₀ tr`).
    - `(sem p tr).val` records all executions of `p` compatible with `tr`.

    Under this encoding, if `p` can produce `goesWrong tr₀`, then for `tr₀` and
    every extension `tr₀ ++ suffix`, `(sem p tr).defined` is `False`, so any
    target program `t` refines `p` at `tr₀ ++ suffix` (CompCert's
    `behavior_improves`), while for any trace prefix `tr` that cannot go wrong,
    `t` must preserve `p`'s behaviors. -/
abbrev CompCertLang (Event Ret : Type) : Language where
  Prog := WholeProgBehavior Event Ret → Prop
  Query := List Event
  Out := WholeProgBehavior Event Ret
  sem p tr := {
    defined := ∀ tr₀, IsTracePrefix tr₀ tr → ¬ p (.goesWrong tr₀)
    val := fun _ b => p b ∧ IsTracePrefix tr b.trace
  }

/-- At any trace prefix `tr` where source program `src` can go wrong
    (`src (.goesWrong tr)`), `CompCertLang.sem src tr` has `defined = False`, so
    *any* target behavior `tgt` refines `src` at `tr` (`behavior_improves`). -/
theorem compcert_goesWrong_prefix_improves {Event Ret : Type}
    (src tgt : WholeProgBehavior Event Ret → Prop)
    (tr : List Event)
    (hwrong : src (.goesWrong tr)) :
    (CompCertLang Event Ret).sem tgt tr ≤ (CompCertLang Event Ret).sem src tr := by
  intro hdef
  have hpre : IsTracePrefix tr tr := ⟨[], List.append_nil tr⟩
  exact False.elim (hdef tr hpre hwrong)

/-- At any trace prefix `tr` where `src` is defined (cannot go wrong on any
    prefix of `tr`), any compiled target `tgt` satisfying `Compiles` must also
    be free of `goesWrong` on prefixes of `tr` and its behaviors extending `tr`
    must be a subset of `src`'s behaviors. -/
theorem compcert_safe_prefix_preserved {Event Ret : Type}
    {src tgt : WholeProgBehavior Event Ret → Prop}
    (hcomp : Compiles (CompCertLang Event Ret) (CompCertLang Event Ret) id src tgt)
    {tr : List Event}
    (hdef_src : ((CompCertLang Event Ret).sem src tr).defined) :
    ((CompCertLang Event Ret).sem tgt tr).defined ∧
    (∀ b, tgt b → IsTracePrefix tr b.trace → src b) := by
  cases hcomp tr hdef_src with
  | intro hdef_tgt hsub =>
    refine ⟨hdef_tgt, ?_⟩
    intro b htgt hpre
    exact (hsub b ⟨htgt, hpre⟩).1

end CompCertExamples

/-!
## 3. Non-Sequential Event-Structure Language (`TrueConcurrencyExamples`)

Not every language executes via a single deterministic sequence of global
states. In true-concurrency event structures and axiomatic weak-memory models
(such as `AnnealTests.AxiomaticMP` in `tests/Smoke.lean`), a program's execution
is a partial order of events with no step counter or sequential state machine.
-/
namespace TrueConcurrencyExamples

/-- Two concurrent events accessing a shared resource (`writeA` and `writeB`),
    plus a join barrier `done`. -/
inductive ConcurrentEvent where
  | writeA
  | writeB
  | done

/-- A true-concurrency program specifies a causal partial order (`Preorder`) on
    `ConcurrentEvent`. -/
structure EventStructureProg where
  causal : ConcurrentEvent → ConcurrentEvent → Prop
  causal_refl : ∀ e, causal e e
  causal_trans : ∀ {a b c}, causal a b → causal b c → causal a c

/-- Scope `ConcurrentEvent` to a program `p : EventStructureProg` so that events
    carry a `Trusted.Preorder` ordered by `p.causal`. -/
structure ScopedConcurrentEvent (p : EventStructureProg) where
  event : ConcurrentEvent

instance instPreorderScopedConcurrentEvent (p : EventStructureProg) :
    Preorder (ScopedConcurrentEvent p) where
  le a b := p.causal a.event b.event
  le_refl a := p.causal_refl a.event
  le_trans hab hbc := p.causal_trans hab hbc

/-- Final value observed at the shared resource after both writes complete. -/
inductive ResourceOutcome where
  | valA
  | valB

/-- True-concurrency language (`Query := Unit`, `Out := ResourceOutcome`) with
    no sequential state machine:
    - `defined`: the conflicting writes `writeA` and `writeB` are causally
      ordered (`writeA ≤ writeB` or `writeB ≤ writeA`), ruling out an
      unsynchronized data race.
    - `val`: `valB` is observed if `writeA` causally precedes `writeB`, and
      `valA` is observed if `writeB` causally precedes `writeA`. -/
abbrev TrueConcurrencyLang : Language where
  Prog := EventStructureProg
  Query := Unit
  Out := ResourceOutcome
  sem p _ := {
    defined :=
      ((⟨.writeA⟩ : ScopedConcurrentEvent p) ≤ ⟨.writeB⟩) ∨
      ((⟨.writeB⟩ : ScopedConcurrentEvent p) ≤ ⟨.writeA⟩)
    val := fun _ out =>
      match out with
      | .valB => (⟨.writeA⟩ : ScopedConcurrentEvent p) ≤ ⟨.writeB⟩
      | .valA => (⟨.writeB⟩ : ScopedConcurrentEvent p) ≤ ⟨.writeA⟩
  }

/-- Unsynchronized parallel program where `writeA` and `writeB` have only
    reflexive causal edges (`writeA` and `writeB` are concurrent). -/
def unsyncedParallelProg : EventStructureProg where
  causal a b := a = b
  causal_refl _ := rfl
  causal_trans h₁ h₂ := Eq.trans h₁ h₂

/-- Synchronized program where `writeA` causally precedes `writeB` and
    `done`. -/
def syncedSequentialOrder : ConcurrentEvent → ConcurrentEvent → Prop
  | .writeA, _ => True
  | .writeB, .writeB => True
  | .writeB, .done => True
  | .done, .done => True
  | _, _ => False

theorem syncedSequentialOrder_trans {a b c : ConcurrentEvent}
    (hab : syncedSequentialOrder a b) (hbc : syncedSequentialOrder b c) :
    syncedSequentialOrder a c := by
  cases a with
  | writeA => exact True.intro
  | writeB =>
    cases b with
    | writeA => cases hab
    | writeB => exact hbc
    | done =>
      cases c with
      | writeA => cases hbc
      | writeB => cases hbc
      | done => exact True.intro
  | done =>
    cases b with
    | writeA => cases hab
    | writeB => cases hab
    | done => exact hbc

def syncedParallelProg : EventStructureProg where
  causal := syncedSequentialOrder
  causal_refl e := by cases e <;> exact True.intro
  causal_trans := syncedSequentialOrder_trans

/-- `syncedParallelProg` is well-formed (race-free) in `TrueConcurrencyLang`. -/
theorem syncedParallelProg_wf :
    TrueConcurrencyLang.sem syncedParallelProg ≤ TrueConcurrencyLang.WellFormed := by
  refine (le_wellFormed_iff _).mpr ?_
  intro _
  exact Or.inl True.intro

/-- `unsyncedParallelProg` violates `TrueConcurrencyLang.WellFormed` because
    `writeA` and `writeB` are causally unordered (data race). -/
theorem unsyncedParallelProg_not_wf :
    ¬ (TrueConcurrencyLang.sem unsyncedParallelProg ≤ TrueConcurrencyLang.WellFormed) := by
  intro hwf
  have hdef := (le_wellFormed_iff _).mp hwf ()
  cases hdef with
  | inl h => cases h
  | inr h => cases h

end TrueConcurrencyExamples

/-!
## 4. Non-Time-Traveling UB (`PrefixPreservationExamples`)

In a language whose UB cannot time-travel over externally observable effects, if
a program emits an observable output at step `1` and triggers UB at step `2`,
its behavior at step `1` is well-defined (`defined = True`) and **must** be
preserved by any valid compiler (`Compiles`), even though step `2` has
`defined = False`.
-/
namespace PrefixPreservationExamples

/-- Observable external I/O event (`output n`). -/
inductive ObsEvent where
  | output (n : Nat)

/-- Simple instruction sequence: emit an observable output, trigger UB, or
    return a final value. -/
inductive PrefixInstr where
  | emit (n : Nat)
  | triggerUb
  | ret (v : Nat)

/-- Machine state holding the remaining instruction list. -/
structure PrefixState where
  code : List PrefixInstr

/-- Small-step machine executing `PrefixInstr` programs one instruction per
    step, emitting `Option ObsEvent` observations. -/
def PrefixIOMachine : SmallStepMachine (List PrefixInstr) PrefixState (Option ObsEvent) Nat where
  initState prog s := s.code = prog
  step _ s r :=
    match s.code with
    | [] => r = .terminated (.normal 0)
    | .emit n :: rest => r = .step (some (.output n)) { code := rest }
    | .triggerUb :: _ => r = .failed .ub
    | .ret v :: _ => r = .terminated (.normal v)

/-- Package `PrefixIOMachine` as a Layer 1A `Language`. -/
abbrev PrefixIOLang : Language :=
  PrefixIOMachine.toLanguage

/-- Source program that emits `ObsEvent.output 42` at step `1` and then triggers
    UB at step `2`. -/
def emitThenUbProg : List PrefixInstr :=
  [.emit 42, .triggerUb]

/-- Initial state for `emitThenUbProg`. -/
def emitThenUbInit : PrefixState :=
  { code := emitThenUbProg }

/-- At step budget `1`, `emitThenUbProg` is **well-defined** (`defined = True`):
    its 1-step execution emits `some (ObsEvent.output 42)` and is in `.running`
    (safe) state before reaching `.triggerUb`. -/
theorem emitThenUb_step1_defined :
    (PrefixIOLang.sem emitThenUbProg { init := emitThenUbInit, steps := 1 }).defined := by
  intro _ tr out hreach
  have hstep :
      PrefixIOMachine.step emitThenUbProg emitThenUbInit
        (.step (some (.output 42)) { code := [.triggerUb] }) :=
    rfl
  cases hreach with
  | step _ _ s' obs tr' _ h1 h2 =>
    cases h2 with
    | zero => exact True.intro
  | choice _ _ _ _ _ _ _ h1 _ _ => cases h1
  | emptyChoice _ _ _ _ h1 _ => cases h1
  | terminated _ _ _ h1 => cases h1
  | failed _ _ _ h1 => cases h1
  | noStep _ _ hnostep =>
    exact False.elim (hnostep ⟨_, hstep⟩)

/-- **Compiler Prefix Preservation Before Non-Time-Traveling UB:**
    Any target program `tgt` that validly compiles `emitThenUbProg`
    (`Compiles PrefixIOLang PrefixIOLang id emitThenUbProg tgt`) **must** be
    defined at step `1` on `emitThenUbInit` and every `1`-step execution of
    `tgt`
    from `emitThenUbInit` **must** emit the exact observable trace
    `[some (ObsEvent.output 42)]` with outcome `.running`. -/
theorem compiler_preserves_well_defined_prefix_before_ub
    {tgt : List PrefixInstr}
    (hcomp : Compiles PrefixIOLang PrefixIOLang id emitThenUbProg tgt) :
    let q₁ : ExecQuery PrefixState := { init := emitThenUbInit, steps := 1 }
    (PrefixIOLang.sem tgt q₁).defined ∧
    (∀ tr oc,
      tgt = emitThenUbInit.code →
      ReachesPrefix PrefixIOMachine tgt emitThenUbInit 1 emitThenUbInit tr oc →
      tr = [some (.output 42)] ∧ oc = .running) := by
  let q₁ : ExecQuery PrefixState := { init := emitThenUbInit, steps := 1 }
  cases hcomp q₁ emitThenUb_step1_defined with
  | intro hdef_tgt hsub =>
    refine ⟨hdef_tgt, ?_⟩
    intro tr oc hinit_tgt hreach_tgt
    have hsrc :
        (PrefixIOLang.sem emitThenUbProg q₁).val emitThenUb_step1_defined
          { trace := tr, outcome := oc } :=
      hsub { trace := tr, outcome := oc } ⟨hinit_tgt.symm, hreach_tgt⟩
    have hreach_src :
        ReachesPrefix PrefixIOMachine emitThenUbProg emitThenUbInit 1
          emitThenUbInit tr oc :=
      hsrc.2
    cases hreach_src with
    | step _ _ s' obs tr' _ h1 h2 =>
      have h1' : StepResult.step obs s' =
          StepResult.step (State := PrefixState) (Obs := Option ObsEvent) (Val := Nat)
            (some (.output 42)) { code := [.triggerUb] } := h1
      injection h1' with hobs hs'
      subst hobs hs'
      cases h2 with
      | zero => exact ⟨rfl, rfl⟩
    | choice _ _ _ _ _ _ _ h1 _ _ => cases h1
    | emptyChoice _ _ _ _ h1 _ => cases h1
    | terminated _ _ _ h1 => cases h1
    | failed _ _ _ h1 => cases h1
    | noStep _ _ hnostep =>
      exact False.elim (hnostep ⟨_, rfl⟩)

/-- At step budget `2` (when `.triggerUb` executes), `emitThenUbProg` is
    **undefined** (`defined = False`), so a compiler is unconstrained from step
    `2` onward. -/
theorem emitThenUb_step2_not_defined :
    ¬ (PrefixIOLang.sem emitThenUbProg { init := emitThenUbInit, steps := 2 }).defined := by
  intro hdef
  let s1 : PrefixState := { code := [.triggerUb] }
  have hstep1 :
      PrefixIOMachine.step emitThenUbProg emitThenUbInit
        (.step (some (.output 42)) s1) := rfl
  have hstep2 :
      PrefixIOMachine.step emitThenUbProg s1 (.failed .ub) := rfl
  have hreach1 :
      ReachesPrefix PrefixIOMachine emitThenUbProg emitThenUbInit 1
        s1 [] (.failed .ub) :=
    ReachesPrefix.failed 0 s1 .ub hstep2
  have hreach2 :
      ReachesPrefix PrefixIOMachine emitThenUbProg emitThenUbInit 2
        emitThenUbInit [some (.output 42)] (.failed .ub) :=
    ReachesPrefix.step 1 emitThenUbInit s1
      (some (.output 42)) [] (.failed .ub) hstep1 hreach1
  exact hdef rfl [some (.output 42)] (.failed .ub) hreach2

end PrefixPreservationExamples

/-!
## 5. Selective Time-Traveling UB (`SelectiveTimeTravelExamples`)

Consider a language with two externally observable behaviors (`BA` and `BB`) and
two forms of Undefined Behavior (`UBA` and `UBB`):
- `UBA` **can** time-travel over `BA`, but **cannot** time-travel over `BB`.
- `UBB` **can** time-travel over `BB`, but **cannot** time-travel over `BA`.

We model this directly in `Language` by defining `(SelectiveTTLang.sem p
k).defined`
at prefix length `k : Nat` so that a later UB event `ub` invalidates prefix `k`
if and only if every observable behavior emitted in prefix `k` is one that `ub`
can time-travel over (`canTimeTravelOver ub obs`). Whenever prefix `k` contains
an observation `obs` that blocks `ub` (`¬ canTimeTravelOver ub obs`), prefix `k`
remains well-defined (`defined = True`) and every valid compiler (`Compiles`)
must preserve it.
-/
namespace SelectiveTimeTravelExamples

/-- Two externally observable behaviors `BA` and `BB`. -/
inductive ObsKind where
  | BA
  | BB

/-- Two forms of Undefined Behavior `UBA` and `UBB`. -/
inductive UBKind where
  | UBA
  | UBB

/-- Time-travel capability matrix:
    - `UBA` can time-travel over `BA`, but not `BB`.
    - `UBB` can time-travel over `BB`, but not `BA`. -/
def canTimeTravelOver : UBKind → ObsKind → Prop
  | .UBA, .BA => True
  | .UBA, .BB => False
  | .UBB, .BB => True
  | .UBB, .BA => False

/-- A two-step program that emits `firstObs` at step `1` (or `none` if silent)
    and optionally triggers `laterUb` at step `2`. -/
structure SelectiveProg where
  firstObs : Option ObsKind
  laterUb : Option UBKind

/-- Observable trace prefix of length `k` (`0` or `1+` steps). -/
def prefixTrace (p : SelectiveProg) (k : Nat) : List ObsKind :=
  match k with
  | 0 => []
  | _ + 1 =>
    match p.firstObs with
    | some obs => [obs]
    | none => []

/-- Whether a prefix of length `k` is well-defined (`defined : Prop`):
    - At `k = 0`: always defined.
    - At `k = 1`: defined unless `laterUb = some ub` can time-travel over the
      observation emitted at step `1` (`canTimeTravelOver ub obs`).
    - At `k ≥ 2`: defined iff `laterUb = none` (since `laterUb` triggers at step
      `2`). -/
def prefixDefined (p : SelectiveProg) : Nat → Prop
  | 0 => True
  | 1 =>
    match p.laterUb with
    | none => True
    | some ub =>
      match p.firstObs with
      | none => False
      | some obs => ¬ canTimeTravelOver ub obs
  | _ + 2 => p.laterUb = none

/-- Selective time-traveling language (`Query := Nat` step budget,
    `Out := List ObsKind` emitted observation trace). -/
abbrev SelectiveTTLang : Language where
  Prog := SelectiveProg
  Query := Nat
  Out := List ObsKind
  sem p k := {
    defined := prefixDefined p k
    val := fun _ tr => tr = prefixTrace p k
  }

/-- Program 1: emits `BA` at step `1`, then triggers `UBA` at step `2`. -/
def prog_BA_then_UBA : SelectiveProg where
  firstObs := some .BA
  laterUb := some .UBA

/-- Program 2: emits `BB` at step `1`, then triggers `UBA` at step `2`. -/
def prog_BB_then_UBA : SelectiveProg where
  firstObs := some .BB
  laterUb := some .UBA

/-- Program 3: emits `BB` at step `1`, then triggers `UBB` at step `2`. -/
def prog_BB_then_UBB : SelectiveProg where
  firstObs := some .BB
  laterUb := some .UBB

/-- Program 4: emits `BA` at step `1`, then triggers `UBB` at step `2`. -/
def prog_BA_then_UBB : SelectiveProg where
  firstObs := some .BA
  laterUb := some .UBB

/-- A silent target program that emits no observations and never triggers UB. -/
def silentProg : SelectiveProg where
  firstObs := none
  laterUb := none

/-- **Case 1 (`BA` followed by `UBA`):**
    Because `UBA` can time-travel over `BA`, the step-`1` prefix of
    `prog_BA_then_UBA` is undefined (`¬ defined`), and a compiler may validly
    compile `prog_BA_then_UBA` to `silentProg` (eliding `BA` completely). -/
theorem uba_time_travels_over_ba :
    ¬ (SelectiveTTLang.sem prog_BA_then_UBA (1 : Nat)).defined ∧
    Compiles SelectiveTTLang SelectiveTTLang id prog_BA_then_UBA silentProg := by
  refine ⟨fun h => h True.intro, ?_⟩
  intro (k : Nat) hdef
  cases k with
  | zero =>
    exact ⟨True.intro, fun _ htr => htr⟩
  | succ m =>
    cases m with
    | zero =>
      exact False.elim (hdef True.intro)
    | succ n =>
      cases hdef

/-- **Case 2 (`BB` followed by `UBA`):**
    Because `UBA` *cannot* time-travel over `BB`, the step-`1` prefix of
    `prog_BB_then_UBA` is well-defined (`defined`), every valid compilation
    `Compiles SelectiveTTLang SelectiveTTLang id prog_BB_then_UBA tgt` must emit
    `[.BB]` at step `1`, and `silentProg` is rejected. -/
theorem uba_blocked_by_bb :
    (SelectiveTTLang.sem prog_BB_then_UBA (1 : Nat)).defined ∧
    (∀ tgt : SelectiveProg,
      Compiles SelectiveTTLang SelectiveTTLang id prog_BB_then_UBA tgt →
      prefixTrace tgt 1 = [.BB]) ∧
    ¬ Compiles SelectiveTTLang SelectiveTTLang id prog_BB_then_UBA silentProg := by
  have hdef1 : (SelectiveTTLang.sem prog_BB_then_UBA (1 : Nat)).defined :=
    fun h => h
  refine ⟨hdef1, ?_, ?_⟩
  · intro tgt hcomp
    cases hcomp (1 : Nat) hdef1 with
    | intro _ hsub =>
      exact hsub (prefixTrace tgt 1) rfl
  · intro hcomp
    cases hcomp (1 : Nat) hdef1 with
    | intro _ hsub =>
      have hbad : ([] : List ObsKind) = [.BB] := hsub [] rfl
      cases hbad

/-- **Case 3 (`BB` followed by `UBB`):**
    Because `UBB` can time-travel over `BB`, the step-`1` prefix of
    `prog_BB_then_UBB` is undefined (`¬ defined`), and a compiler may validly
    compile `prog_BB_then_UBB` to `silentProg` (eliding `BB` completely). -/
theorem ubb_time_travels_over_bb :
    ¬ (SelectiveTTLang.sem prog_BB_then_UBB (1 : Nat)).defined ∧
    Compiles SelectiveTTLang SelectiveTTLang id prog_BB_then_UBB silentProg := by
  refine ⟨fun h => h True.intro, ?_⟩
  intro (k : Nat) hdef
  cases k with
  | zero =>
    exact ⟨True.intro, fun _ htr => htr⟩
  | succ m =>
    cases m with
    | zero =>
      exact False.elim (hdef True.intro)
    | succ n =>
      cases hdef

/-- **Case 4 (`BA` followed by `UBB`):**
    Because `UBB` *cannot* time-travel over `BA`, the step-`1` prefix of
    `prog_BA_then_UBB` is well-defined (`defined`), every valid compilation
    `Compiles SelectiveTTLang SelectiveTTLang id prog_BA_then_UBB tgt` must emit
    `[.BA]` at step `1`, and `silentProg` is rejected. -/
theorem ubb_blocked_by_ba :
    (SelectiveTTLang.sem prog_BA_then_UBB (1 : Nat)).defined ∧
    (∀ tgt : SelectiveProg,
      Compiles SelectiveTTLang SelectiveTTLang id prog_BA_then_UBB tgt →
      prefixTrace tgt 1 = [.BA]) ∧
    ¬ Compiles SelectiveTTLang SelectiveTTLang id prog_BA_then_UBB silentProg := by
  have hdef1 : (SelectiveTTLang.sem prog_BA_then_UBB (1 : Nat)).defined :=
    fun h => h
  refine ⟨hdef1, ?_, ?_⟩
  · intro tgt hcomp
    cases hcomp (1 : Nat) hdef1 with
    | intro _ hsub =>
      exact hsub (prefixTrace tgt 1) rfl
  · intro hcomp
    cases hcomp (1 : Nat) hdef1 with
    | intro _ hsub =>
      have hbad : ([] : List ObsKind) = [.BA] := hsub [] rfl
      cases hbad

end SelectiveTimeTravelExamples

/-!
## 6. Library Conditionality: Safe vs. `unsafe` APIs (`LibraryConditionality`)

A verification result for a library is conditional
on its calling context (`pre`) and separates baseline UB-freedom from additional
functional guarantees (`specs`):
- Because `VerificationResultOn C policy assumptions prog pre specs` requires
  `C.Verified prog` on every element of the non-empty list
  `L_src.WellFormedOn pre :: specs`, baseline UB-freedom on `pre`
  (`C.Verified prog (L_src.WellFormedOn pre)`) is always proved first.
- Each additional specification `spec ∈ specs` may restrict its domain via
  `(spec q).defined` (leaving `(spec q).defined = False`, i.e. `Partial.ub`,
  outside that domain). Even if a user writes an unsatisfiable functional
  precondition (such as `x > 0 && x < 0`, where
  `spec = fun _ => Partial.ub`), that only makes the additional guarantee
  `C.Verified prog spec` vacuously true (`ub_top`) without weakening the
  mandatory baseline `C.Verified prog (L_src.WellFormedOn pre)` obligation.
-/
namespace LibraryConditionality

/-- Division query pairing numerator `n` and divisor `d`. -/
structure DivQuery where
  n : Nat
  d : Nat

/-- Library language whose programs are query-indexed partial behaviors over
    `DivQuery` returning `Nat`. -/
abbrev LibLang : Language where
  Prog := DivQuery → Partial (Nat → Prop)
  Query := DivQuery
  Out := Nat
  sem p := p

/-- Identity compiler on `LibLang`. -/
def LibIdCompiler : Compiler LibLang LibLang where
  compile p := p
  π b := b

/-- Trivial assumption type for `LibraryConditionality`. -/
inductive LibAssumption where
  | compilerSound (p : LibLang.Prog)

instance instTrustedAssumptionLib : TrustedAssumption LibAssumption where
  meaning
    | .compilerSound p => LibIdCompiler.SoundOn p

/-- Trust policy allowing `LibAssumption.compilerSound`. -/
def libPolicy : TrustPolicy LibAssumption where
  isAllowed
    | .compilerSound _ => True

/-- Safe library function `safeDivOrZero`: well-defined for all `(n, d)`
    (`defined := True`), returning `n / d` (which evaluates to `0` in `Nat` when
    `d = 0`). -/
def safeDivOrZero : LibLang.Prog :=
  LibLang.Spec (fun q out => out = q.n / q.d)

/-- Conditional functional specification asserting `out = q.n / q.d` when
    `q.d > 0`, and leaving `defined := False` (`Partial.ub`) when `q.d = 0`. -/
def divExactWhenPosSpec : LibLang.Behavior :=
  LibLang.SpecOn (fun q => q.d > 0) (fun q out => out = q.n / q.d)

/-- Vacuous functional specification with an unsatisfiable precondition
    (`requires(x > 0 && x < 0)`), which evaluates to
    `Partial.ub` (`defined := False`) at every query. -/
def vacuousSpec : LibLang.Behavior :=
  fun _ => Partial.ub

/-- **Safe Library Verification (`VerificationResult`):**
    `safeDivOrZero` satisfies `VerificationResult` with additional
    specifications `[divExactWhenPosSpec, vacuousSpec]`. Even though
    `divExactWhenPosSpec` is undefined at `d = 0` and `vacuousSpec` is undefined
    everywhere, `VerificationResult` still proves `LibLang.WellFormed` across
    **all** queries (including `d = 0`) because `LibLang.WellFormed` is the head
    of `LibLang.WellFormed :: [divExactWhenPosSpec, vacuousSpec]`. -/
theorem safeDiv_verified :
    VerificationResult LibIdCompiler libPolicy [] safeDivOrZero
      [divExactWhenPosSpec, vacuousSpec] := by
  refine ⟨True.intro, ?_⟩
  intro _
  have hcomp : LibIdCompiler.SoundOn safeDivOrZero :=
    ⟨monotone_id, Preorder.le_refl _⟩
  have hwf : LibLang.sem safeDivOrZero ≤ LibLang.WellFormed :=
    spec_le_wellFormed _
  have hpos : LibLang.sem safeDivOrZero ≤ divExactWhenPosSpec :=
    fun _ _ => ⟨True.intro, fun _ hout => hout⟩
  have hvac : LibLang.sem safeDivOrZero ≤ vacuousSpec :=
    fun _ => ub_top _
  exact ⟨
    Compiler.SoundOn.verify hcomp hwf,
    Compiler.SoundOn.verify hcomp hpos,
    Compiler.SoundOn.verify hcomp hvac,
    True.intro
  ⟩

/-- `unsafe` library function `unsafeDiv`: exhibits Undefined Behavior when
    `q.d = 0` (`defined := q.d > 0`). -/
def unsafeDiv : LibLang.Prog :=
  LibLang.SpecOn (fun q => q.d > 0) (fun q out => out = q.n / q.d)

/-- **`unsafe` Library Verification (`VerificationResultOn`):**
    Under the caller `# Safety` precondition `pre := fun q => q.d > 0`,
    `unsafeDiv` satisfies `VerificationResultOn` for both its baseline
    conditional safety obligation `LibLang.WellFormedOn (fun q => q.d > 0)` and
    `divExactWhenPosSpec`. -/
theorem unsafeDiv_verifiedOn :
    VerificationResultOn LibIdCompiler libPolicy [] unsafeDiv
      (fun q => q.d > 0) [divExactWhenPosSpec] := by
  refine ⟨True.intro, ?_⟩
  intro _
  have hcomp : LibIdCompiler.SoundOn unsafeDiv :=
    ⟨monotone_id, Preorder.le_refl _⟩
  exact Compiler.Verified.with_wellFormedOn
    (Compiler.SoundOn.verify hcomp (Preorder.le_refl _))
    (specOn_le_wellFormedOn _ _)
    monotone_id

/-- `unsafeDiv` cannot be verified as an unconditionally safe function
    (`LibLang.WellFormed`), because it is undefined at `d = 0`. -/
theorem unsafeDiv_not_unconditionally_wf :
    ¬ (LibLang.sem unsafeDiv ≤ LibLang.WellFormed) :=
  not_specOn_le_wellFormed_of_not_pre (q := { n := 1, d := 0 }) (Nat.lt_irrefl 0)

end LibraryConditionality

end AnnealExamples
