-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted
import Anneal.Refinement
import Anneal.StepResult
import Anneal.MirLemmas

/-!
# Plan-Guided Shallow Functional Translation (`Anneal.FunctionalTranslation`)

This module implements an Aeneas-inspired functional translation from
`Trusted.MirBody` (`MirLang`) to pure Lean functional behaviors (`FuncLang`)
within the Layer 1A / Layer 1B refinement framework (`Trusted.Refinement`,
`Trusted.StepResult`):

1. **Result Domain (`AeneasRes`) and `FuncLang` Abstraction (`π_func`):**
   `AeneasRes Val` distinguishes normal functional return (`.ok v`) from
   translation or assertion failure (`.fail`). In `FuncLang`, `.fail` maps to
   `defined := False` (`Partial.ub`, the top element of `Partial`).
   Consequently,
   any invalid, mismatched, or fuel-exhausted translation plan step refines
   `.fail` unconditionally (`ub_top`), while downstream `WellFormed` /
   `Spec` obligations (`defined := True`) automatically reject `.fail` on every
   reachable execution path (`not_ub_le_pure`).
2. **Unified `LoanEntry` over `OwnerId` with Executable Backward Lenses:**
   Active mutable borrows (`&mut usize` parameters and branch-joined mutable
   reborrows `let r = if cond { &mut *x } else { &mut *y }`) are represented by
   `LoanEntry` values storing their frozen parent `owners : List OwnerId`,
   current symbolic value `curVal : SymVal`, and executable backward lens
   `back : SymVal → List SymVal`.
3. **Spine-Preserving Plan-Guided Shallow Evaluator (`evalSymState`, `evalSym`)
   and Universal Hint-Independent Soundness (`evalSym_sound`):**
   `TransPlan` guides symbolic evaluation directly over `MirBody` without an
   intermediate `StructuredMir` syntax-tree semantics. Pushing conditional
   choices inside `.usize`/`.bool` payloads (`zipSymVal`, `zipAeneasRes`)
   preserves the outer constructor spine so `translatePure (computePlan body)
   body`
   reduces on symbolic inputs by kernel `rfl` (the First Futamura Projection).
   `evalSym_sound` proves **once** by structural induction on `plan : TransPlan`
   that `Abstracts FuncLang MirLang π_func (evalSym plan body) body` holds for
   **every** `plan : TransPlan` and **every** `body : MirBody`.
4. **Untrusted Heuristic Planner (`computePlan`) and End-to-End Rust Proofs:**
   Because `evalSym_sound` quantifies over all `plan : TransPlan`, the CFG and
   NLL loan-termination heuristic `computePlan : MirBody → TransPlan` carries
   zero proof obligations (`translate_sound`). We use `translate` and
   `translate_sound` to verify non-trivial properties of real Rust functions
   with branching, comparisons, mutable references, conditional reborrowing,
   and in-place mutation (`max_assign` and `update_min`).
-/

namespace Anneal.FunctionalTranslation

class Preorder (B : Type u) extends LE B where
  le_refl : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

/-- Implication (`P → Q`) equips `Prop` with a refinement preorder in which
    stronger propositions refine weaker ones. -/
instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

/-- Pointwise lifting (`∀ a, f a ≤ g a`) equips function spaces `A → B` with a
    refinement preorder whenever the codomain `B` is a `Preorder`.

    Together with `instPreorderProp`, this automatically equips outcome
    predicates `Out → Prop` with subset inclusion (`∀ o, P o → Q o`) and
    query-indexed behaviors `Query → Partial (Out → Prop)` with pointwise
    query refinement. -/
instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

/-- A partially defined value of type `B`, constructively representing
    $B \cup \{\mathsf{UB}\}$:
    - `defined : Prop` records whether the behavior is well-defined (free of
      Undefined Behavior).
    - `val : defined → B` yields the underlying value in `B` whenever `defined`
      holds. When `defined` is `False`, `val` is uniquely inhabited by
      `False.elim`, representing the top element `Partial.ub`. -/
structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

/-- Embed a unconditionally defined value `b : B` into `Partial B`
    (`defined := True`). -/
def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

/-- The undefined element ($\mathsf{UB}$) of `Partial B` (`defined := False`),
    which acts as the top element under `instPreorderPartial`. -/
def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

/-- Map a function `f : B₁ → B₂` over the defined payload of a `Partial B₁`,
    preserving `.defined`. -/
def Partial.map {B₁ : Type u} {B₂ : Type v} (f : B₁ → B₂) (p : Partial B₁) :
    Partial B₂ where
  defined := p.defined
  val h := f (p.val h)

/-- Refinement preorder on `Partial B`: `p₁ ≤ p₂` holds when, whenever `p₂` is
    defined (`h₂ : p₂.defined`), `p₁` is also defined (`h₁ : p₁.defined`) and
    its value refines `p₂`'s value (`p₁.val h₁ ≤ p₂.val h₂`).

    When `p₂` is undefined (`p₂.defined = False`), `p₁ ≤ p₂` holds vacuously,
    making `Partial.ub` the top element of `Partial B`. -/
instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

/-- Order-preserving mapping between behavior preorders.

    When a behavior mapping `π : B₁ → B₂` is monotone, refining a behavior or
    specification in `B₁` (`x ≤ y`) preserves refinement of its mapped behavior
    in `B₂` (`π x ≤ π y`). -/
def Monotone {B₁ : Type u} {B₂ : Type v} [Preorder B₁] [Preorder B₂]
    (π : B₁ → B₂) : Prop :=
  ∀ ⦃x y : B₁⦄, x ≤ y → π x ≤ π y

/-- The canonical domain of query-indexed partial behaviors over `Query` and
    `Out` (`Query → Partial (Out → Prop)`), ordered pointwise by
    `instPreorderFun`, `instPreorderPartial`, and `instPreorderProp`. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- A language bundling a program type `Prog`, a query domain `Query` (such as
    initial states, inputs, step budgets, or external trace prefixes), an
    outcome domain `Out`, and a semantic function
    `sem : Prog → Behavior Query Out`. -/
structure Language where
  Prog : Type
  Query : Type
  Out : Type
  sem : Prog → Behavior Query Out

/-- The behavior domain of a `Language` (`Behavior L.Query L.Out`). -/
abbrev Language.Behavior (L : Language) : Type :=
  Anneal.FunctionalTranslation.Behavior L.Query L.Out

/-- Query-indexed specification on `L` with domain precondition
    `pre : L.Query → Prop` and outcome postcondition
    `post : L.Query → L.Out → Prop`: requires the program to be defined at
    every query `q` satisfying `pre q` (`defined := pre q`) and restricts its
    outcomes at `q` to `post q` (`val := fun _ => post q`).

    By `instPreorderPartial`, `b ≤ L.SpecOn pre post` unfolds to
    `∀ q, pre q → ∃ h : (b q).defined, ∀ out, (b q).val h out → post q out`.
    Outside `pre` (`¬ pre q`), `(L.SpecOn pre post q).defined` is `False`
    (`Partial.ub`), leaving `b q` unconstrained. -/
def Language.SpecOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => {
    defined := pre q
    val := fun _ => post q
  }

/-- Unconditional specification on `L` (`L.SpecOn (fun _ => True) post`),
    definitionally equal to `fun q => Partial.pure (post q)`: requires the
    program to be defined at every query `q : L.Query` and its outcomes at `q`
    to satisfy `post q`. -/
abbrev Language.Spec (L : Language)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

/-- Conditional well-formedness specification on `L` under query precondition
    `pre : L.Query → Prop` (`L.SpecOn pre (fun _ _ => True)`): requires the
    program to be defined (`defined = True`) at every query `q` satisfying
    `pre q`, while permitting any normal outcome (`post := fun _ _ => True`).

    By `instPreorderPartial`, `L.sem s ≤ L.WellFormedOn pre` unfolds to
    `∀ q, pre q → (L.sem s q).defined`. Used as the baseline UB-freedom
    obligation when baseline safety is conditional on `pre`—such as declared
    input/environmental conditions for a binary (whole program), or permitted
    calling contexts and `# Safety` preconditions for a library API. -/
abbrev Language.WellFormedOn (L : Language) (pre : L.Query → Prop) : L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

/-- Unconditional well-formedness specification on `L`
    (`L.WellFormedOn (fun _ => True)`): requires the program to be defined at
    every query `q : L.Query` (`∀ q, (L.sem s q).defined`). Used as the
    mandatory baseline UB-freedom obligation for binaries and safe library APIs
    whose valid initial states or caller inputs are already scoped by `L.Query`
    or `L.sem`. -/
abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

/-- Compilation (refinement) pass from `L_src` to `L_tgt`: target program `t`
    refines the mapped source behavior `π_c (L_src.sem s)`.

    Because `L_tgt.Behavior` is ordered by `instPreorderPartial`, this single
    inequality enforces that at every target query `q` where
    `π_c (L_src.sem s)` is defined, `t` is also defined and its outcomes refine
    `s`'s outcomes, while leaving `t` unconstrained at queries where `s`
    exhibits UB (`defined = False`). -/
abbrev Compiles (L_src L_tgt : Language)
    (π_c : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ π_c (L_src.sem s)

/-- Verification (abstraction) pass from `L_src` to verifier language `L_v`:
    source program `s` refines the mapped verifier behavior `π_v (L_v.sem v)`.

    At every source query `q` where `π_v (L_v.sem v)` is defined, `s` is forced
    to be defined (reflecting UB-freedom backwards from `v` to `s`) and its
    outcomes are covered by `v`'s outcomes. -/
abbrev Abstracts (L_v L_src : Language)
    (π_v : L_v.Behavior → L_src.Behavior)
    (v : L_v.Prog) (s : L_src.Prog) : Prop :=
  L_src.sem s ≤ π_v (L_v.sem v)

/-- A compiler lowering programs from `L_src` to `L_tgt` with behavior mapping
    `π : L_src.Behavior → L_tgt.Behavior`. -/
structure Compiler (L_src L_tgt : Language) where
  compile : L_src.Prog → L_tgt.Prog
  π : L_src.Behavior → L_tgt.Behavior

/-- Soundness of compiler `C` on an individual source program `s`: `C.π` is
    monotone and `s` compiles to `C.compile s`
    (`Compiles L_src L_tgt C.π s (C.compile s)`). -/
def Compiler.SoundOn {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) : Prop :=
  Monotone C.π ∧ Compiles L_src L_tgt C.π s (C.compile s)

/-- End-to-end verification obligation for source program `s` and specification
    `spec` under compiler `C`:
    1. `s` satisfies `spec` in `L_src` (`L_src.sem s ≤ spec`),
    2. `s` compiles to `C.compile s` under `C.π`
       (`Compiles L_src L_tgt C.π s (C.compile s)`), and
    3. `C.compile s` satisfies `C.π spec`
       (`L_tgt.sem (C.compile s) ≤ C.π spec`). -/
def Compiler.Verified {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) (spec : L_src.Behavior) : Prop :=
  L_src.sem s ≤ spec ∧
  Compiles L_src L_tgt C.π s (C.compile s) ∧
  L_tgt.sem (C.compile s) ≤ C.π spec

/-- An assumption recorded in a verification unit's Trusted Computing Base,
    equipped with its intrinsic semantic meaning as a `Prop`. -/
class TrustedAssumption (A : Type) where
  meaning : A → Prop

/-- A policy governing which trusted assumptions of type `A` are permitted. -/
structure TrustPolicy (A : Type) [TrustedAssumption A] where
  isAllowed : A → Prop

/-- Conjunction of a list of propositions. -/
def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

/-- Top-level verification envelope for a source program `prog : L_src.Prog`,
    safety precondition `pre : L_src.Query → Prop`, and additional
    specifications `specs : List L_src.Behavior` under compiler
    `C : Compiler L_src L_tgt`:
    1. Every assumption in `assumptions` is permitted by `policy`
       (`AllHold (assumptions.map policy.isAllowed)`).
    2. Assuming the semantic meaning of every assumption in `assumptions` holds
       (`AllHold (assumptions.map TrustedAssumption.meaning)`), `prog` satisfies
       `C.Verified prog` for the non-empty specification list
       `L_src.WellFormedOn pre :: specs`—proving baseline UB-freedom on `pre`
       (`C.Verified prog (L_src.WellFormedOn pre)`) alongside every additional
       specification `spec ∈ specs`. -/
def VerificationResultOn
    {L_src L_tgt : Language}
    {A : Type} [TrustedAssumption A]
    (C : Compiler L_src L_tgt)
    (policy : TrustPolicy A)
    (assumptions : List A)
    (prog : L_src.Prog)
    (pre : L_src.Query → Prop)
    (specs : List L_src.Behavior) : Prop :=
  AllHold (assumptions.map policy.isAllowed) ∧
  (AllHold (assumptions.map TrustedAssumption.meaning) →
    AllHold ((L_src.WellFormedOn pre :: specs).map (C.Verified prog)))

/-- Top-level verification envelope for a source program `prog : L_src.Prog`
    whose baseline UB-freedom obligation holds across all `L_src.Query`
    (`pre := fun _ => True`, so `L_src.WellFormedOn pre` is `L_src.WellFormed`),
    together with additional specifications `specs : List L_src.Behavior` under
    compiler `C : Compiler L_src L_tgt`. -/
abbrev VerificationResult
    {L_src L_tgt : Language}
    {A : Type} [TrustedAssumption A]
    (C : Compiler L_src L_tgt)
    (policy : TrustPolicy A)
    (assumptions : List A)
    (prog : L_src.Prog)
    (specs : List L_src.Behavior := []) : Prop :=
  VerificationResultOn C policy assumptions prog (fun _ => True) specs



/-- Quantifier polarity for nondeterministic choices in a small-step semantics.

    - `demonic`: runtime, allocator, or scheduler nondeterminism; a
      specification must hold across all branches.
    - `angelic`: existential witness choice. -/
inductive ChoiceKind where
  | demonic
  | angelic

/-- Distinguishes normal return from panic/unwind completion. -/
inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind

/-- Distinguishes language-level Undefined Behavior (`ub`) from explicit
    specification or assertion violations (`contractViolation`). -/
inductive FailureKind where
  | ub
  | contractViolation

/-- Outcome of a single transition step in a small-step interaction tree. -/
inductive StepResult (State Obs Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (kind : ChoiceKind) (branches : State → Prop)
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)

/-- Outcome recorded at the end of a finite execution prefix. -/
inductive PrefixOutcome (Val : Type) where
  | running
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)
  | stuck

/-- A prefix outcome is safe when it neither triggers a failure (`ub` or
    `contractViolation`) nor gets stuck in an unstepped state. -/
def PrefixOutcome.isSafe : PrefixOutcome Val → Prop
  | .running => True
  | .terminated _ => True
  | .failed _ => False
  | .stuck => False

/-- Input query to a finite-prefix small-step execution (`Query` in
    `Language`): the initial machine state `init` and the step budget
    `steps`. -/
structure ExecQuery (State : Type) where
  init : State
  steps : Nat

/-- Observable output of a finite-prefix small-step execution (`Out` in
    `Language`): the accumulated observation trace `trace` and the terminal or
    intermediate `PrefixOutcome` `outcome`. -/
structure ExecOut (Obs Val : Type) where
  trace : List Obs
  outcome : PrefixOutcome Val

/-- Small-step operational semantics parameterized by programs `Prog`, machine
    states `State`, step observations `Obs`, and return values `Val`. -/
structure SmallStepMachine (Prog State Obs Val : Type) where
  initState : Prog → State → Prop
  step : Prog → State → StepResult State Obs Val → Prop

/-- Inductive reachability of a finite execution prefix from current state `s`
    given initial state `init` and remaining step budget `fuel`.

    - At `fuel = 0`, the prefix finishes immediately in `.running`.
    - If `M.step p s` has no outgoing transition (`¬ ∃ r, M.step p s r`) or a
      choice node has no enabled branch (`¬ ∃ s', branches s'`), the machine
      records `.stuck` so unmodeled states or empty choices cannot silently
      vanish into an empty prefix set. -/
inductive ReachesPrefix (M : SmallStepMachine Prog State Obs Val) (p : Prog)
    (init : State) : Nat → State → List Obs → PrefixOutcome Val → Prop where
  | zero (s : State) :
      ReachesPrefix M p init 0 s [] .running
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs) (out : PrefixOutcome Val) :
      M.step p s (.step obs s') →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s (obs :: tr) out
  | choice (n : Nat) (kind : ChoiceKind) (s s' : State) (branches : State → Prop)
      (tr : List Obs) (out : PrefixOutcome Val) :
      M.step p s (.choice kind branches) →
      branches s' →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s tr out
  | emptyChoice (n : Nat) (kind : ChoiceKind) (s : State) (branches : State → Prop) :
      M.step p s (.choice kind branches) →
      (¬ ∃ s', branches s') →
      ReachesPrefix M p init (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : TerminationKind Val) :
      M.step p s (.terminated term) →
      ReachesPrefix M p init (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) (err : FailureKind) :
      M.step p s (.failed err) →
      ReachesPrefix M p init (n + 1) s [] (.failed err)
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, M.step p s r) →
      ReachesPrefix M p init (n + 1) s [] .stuck

/-- Induced query-indexed partial behavior of program `p` in machine `M`:
    - `defined`: if `q.init` is a valid initial state (`M.initState p q.init`),
      then every prefix of length `q.steps` reachable from `q.init` has a safe
      outcome (`out.isSafe`).
    - `val`: the predicate of all `ExecOut Obs Val` reachable from `q.init` in
      `q.steps` steps. -/
def BehaviorOf (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    ExecQuery State → Partial (ExecOut Obs Val → Prop) :=
  fun q => {
    defined :=
      M.initState p q.init →
        ∀ tr out,
          ReachesPrefix M p q.init q.steps q.init tr out →
          out.isSafe
    val := fun _ out =>
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome
  }

/-- Package a `SmallStepMachine` as a Layer 1A `Language` with
    `Query := ExecQuery State`, `Out := ExecOut Obs Val`, and
    `sem := BehaviorOf M`. -/
def SmallStepMachine.toLanguage (M : SmallStepMachine Prog State Obs Val) :
    Language where
  Prog := Prog
  Query := ExecQuery State
  Out := ExecOut Obs Val
  sem := BehaviorOf M



/-- Index of a MIR local variable or temporary (`_0`, `_1`, ...).

    Corresponds to `rustc_middle::mir::Local` indexing into `Body::local_decls`,
    where local `0` (`_0`) is the return place, `1 ..= arg_count` (`_1`, ...)
    are caller-initialized function arguments, and higher indices are
    user-declared variables and temporaries:

    > "The first local is the return value pointer, followed by `arg_count`
    > locals for the function arguments, followed by any user-declared
    > variables and temporaries."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L235-L240 -/
structure LocalId where
  index : Nat

/-- Index of a basic block (`bb0`, `bb1`, ...) within a MIR body.

    Corresponds to `rustc_middle::mir::BasicBlock` indexing into
    `Body::basic_blocks`:

    > "A list of basic blocks. References to basic block use a newtyped index
    > type [`BasicBlock`] that indexes into this vector."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L207-L209 -/
structure BlockId where
  index : Nat

/-- Atomic memory ordering for atomic load operations.

    Corresponds to `core::sync::atomic::Ordering` variants valid on atomic
    loads (`Ordering::Relaxed` and `Ordering::Acquire`):

    > "Memory orderings specify the way atomic operations synchronize memory.
    > In its weakest [`Ordering::Relaxed`], only the memory directly touched by
    > the operation is synchronized."
    >
    > "No ordering constraints, only atomic operations. Corresponds to
    > [`memory_order_relaxed`] in C++20."
    >
    > "When coupled with a load, if the loaded value was written by a store
    > operation with [`Release`] (or stronger) ordering, then all subsequent
    > operations become ordered after that store."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L450-L503 -/
inductive AtomicOrdering where
  | relaxed
  | acquire

/-- Minimal MIR type grammar (`usize`, `bool`, `()`, `&Atomic<usize>`,
    `&usize`, `&mut usize`, and `Ordering`).

    - `MirTy.usize` models Rust's pointer-sized unsigned integer type `usize`:

      > "The `usize` type is an unsigned integer type with the same number of
      > bits as the platform's pointer type. It can represent every memory
      > address in the process."

    - `MirTy.bool` models Rust's boolean type `bool` (`true` and `false`):

      > "The boolean type, `bool`, represents a value, which could only be
      > either `true` or `false`."

    - `MirTy.refAtomicUsize` models a shared reference `&AtomicUsize`
      (`&core::sync::atomic::Atomic<usize>`) to an atomic `usize` object:

      > "The end result is *almost* equivalent to saying that creating a
      > *shared reference* to one of the Rust atomic types corresponds to
      > creating an `atomic_ref` in C++, with the `atomic_ref` being destroyed
      > when the lifetime of the shared reference ends."

    - `MirTy.refSharedUsize` models an immutable shared reference `&usize`:

      > "Shared references (`&T`) point to memory which is owned by some other
      > value. When a shared reference to a value is created, it prevents
      > direct mutation of the value."

    - `MirTy.refMutUsize` models an exclusive mutable reference `&mut usize`:

      > "Mutable references (`&mut T`), also called exclusive references, allow
      > mutating the value they point to."

    - `MirTy.tupleUsizeBool` models the `(usize, bool)` tuple returned by
      checked arithmetic operations (`AddWithOverflow`, `SubWithOverflow`,
      `MulWithOverflow`).

    - `MirTy.atomicOrdering` models `core::sync::atomic::Ordering`.

    Sources:
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/types/numeric.md#L37-L38
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/types/boolean.md#L6-L7
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/types/tuple.md#L6-L10
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/types/pointer.md#L12-L38
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L36-L42
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L466-L527 -/
inductive MirTy where
  | usize
  | bool
  | unit
  | tupleUsizeBool
  | refAtomicUsize
  | refSharedUsize
  | refMutUsize
  | atomicOrdering

/-- Initialized runtime scalar or pair value (`usize`, `bool`, `()`,
    `(usize, bool)`, `&AtomicUsize` location, `&usize` location, `&mut usize`
    location, or `Ordering`).

    In Rust, scalar values and references must be initialized and valid when
    produced; uninitialized locals are represented in `MirState` by
    `Option.none` rather than a `MirVal` constructor:

    > "The Rust compiler assumes that all values produced during program
    > execution are "valid", and producing an invalid value is hence immediate
    > UB."
    >
    > "* An integer (`i*`/`u*`), floating point value (`f*`), or raw pointer
    > must be initialized, i.e., must not be obtained from uninitialized
    > memory."
    >
    > "* A `bool` must be initialized and have the value `0` (`false`) or `1`
    > (`true`)."
    >
    > "* A reference or [`Box<T>`] must be aligned and non-null, it cannot be
    > [dangling], and it must point to a valid value"

    Sources:
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/behavior-considered-undefined.md#L114-L147
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L466-L527 -/
inductive MirVal where
  | usize (bits : Nat)
  | bool (b : Bool)
  | unit
  | tupleUsizeBool (val : Nat) (overflow : Bool)
  | atomicLoc (loc : Nat)
  | refSharedLoc (loc : Nat)
  | refMutLoc (loc : Nat)
  | ordering (ord : AtomicOrdering)

/-- MIR operand evaluated to produce a value in an `Rvalue` or terminator.

    Corresponds to `rustc_middle::mir::Operand` (`Copy`, `Move`, `Constant`)
    specialized to unprojected local places (`Place { local, projection: [] }`):

    > "Creates a value by loading the given place.
    >
    > Before drop elaboration, the type of the place must be `Copy`. After drop
    > elaboration there is no such requirement."
    >
    > "Creates a value by performing loading the place, just like the `Copy`
    > operand.
    >
    > This *may* additionally overwrite the place with `uninit` bytes,
    > depending on how we decide in [UCG#188]. You should not emit MIR that may
    > attempt a subsequent second load of this place without first
    > re-initializing it."
    >
    > "Constants are already semantically values, and remain unchanged."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L1282-L1310 -/
inductive Operand where
  | copy (src : LocalId)
  | move (src : LocalId)
  | constVal (val : MirVal)

/-- Binary comparison and bitwise operators in `Rvalue.binaryOp`.

    Corresponds to `rustc_middle::mir::BinOp` comparison and bitwise variants
    (`Lt`, `Le`, `Eq`, `Ne`, `Gt`, `Ge`, `BitAnd`, `BitOr`, `BitXor`):

    > "The `<` operator (less than)"
    > "The `<=` operator (less than or equal to)"
    > "The `==` operator (equality)"
    > "The `!=` operator (not equal to)"
    > "The `>=` operator (greater than or equal to)"
    > "The `>` operator (greater than)"
    > "The `^` operator (bitwise xor)"
    > "The `&` operator (bitwise and)"
    > "The `|` operator (bitwise or)"

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L1409-L1443 -/
inductive BinOp where
  | lt
  | le
  | eq
  | ne
  | gt
  | ge
  | bitAnd
  | bitOr
  | bitXor

/-- Checked binary arithmetic operators in `Rvalue.checkedBinaryOp` producing a
    `(usize, bool)` pair (`MirVal.tupleUsizeBool`).

    Corresponds to `rustc_middle::mir::BinOp` checked arithmetic variants
    (`AddWithOverflow`, `SubWithOverflow`, `MulWithOverflow`):

    > "The `+` operator (addition) with overflow check"
    > "The `-` operator (subtraction) with overflow check"
    > "The `*` operator (multiplication) with overflow check"

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L1409-L1443 -/
inductive CheckedBinOp where
  | add
  | sub
  | mul

/-- Right-hand side value computation of a MIR assignment statement.

    Corresponds to `rustc_middle::mir::Rvalue` (`Use`, `Use(Copy(*src))`
    dereference load, `BinaryOp`, checked arithmetic `BinaryOp`, and tuple
    field projection loads `_src.0` / `_src.1`):

    > "Yields the operand unchanged, except for a potential retag."
    >
    > "Dereference a pointer or reference."
    >
    > "Applies the binary operation to the two operands, producing a value of
    > the appropriate result type."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L975-L1005
    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L1342-L1370 -/
inductive Rvalue where
  | use (op : Operand)
  | deref (src : LocalId)
  | binaryOp (op : BinOp) (lhs : Operand) (rhs : Operand)
  | checkedBinaryOp (op : CheckedBinOp) (lhs : Operand) (rhs : Operand)
  | proj0 (src : LocalId)
  | proj1 (src : LocalId)

/-- Sequential statement inside a MIR basic block.

    Corresponds to `rustc_middle::mir::StatementKind` (`Assign` to a local place
    or dereferenced place `(*dst) = op`, `StorageLive`, `StorageDead`, and
    no-op statements):

    > "Assign statements roughly correspond to an assignment in Rust proper
    > (`x = ...`) except without the possibility of dropping the previous value
    > (that must be done separately, if at all). The *exact* way this works is
    > undecided. It probably does something like evaluating the LHS to a place,
    > then the RHS to a value, and then storing the value to the place."
    >
    > "`StorageLive` and `StorageDead` statements mark the live range of a
    > local."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L305-L385 -/
inductive Stmt where
  | assign (dst : LocalId) (rv : Rvalue)
  | assignDeref (dst : LocalId) (op : Operand)
  | storageLive (loc : LocalId)
  | storageDead (loc : LocalId)
  | nop

/-- Pure 2-argument `usize` callee in `Terminator.callPure2`. -/
inductive PureCallee2 where
  | addBounded
  | absDiff

/-- Control-flow transfer at the end of a MIR basic block.

    Corresponds to `rustc_middle::mir::TerminatorKind` (`Return`, `Goto`,
    `Unreachable`, `Call` specialized to `Atomic::<usize>::load` or pure
    crate-local callees, and `SwitchInt` on boolean discriminants
    `[0: falseTarget, otherwise: trueTarget]`):

    > "Block has one successor; we continue execution there."
    >
    > "Switches based on the computed value.
    >
    > First, evaluates the `discr` operand. The type of this operand must be a
    > signed or unsigned integer, `char`, or `bool`, and must match the given
    > type. Then, if the list of switch targets contains the computed value,
    > continues execution at the associated basic block. Otherwise, continues
    > execution at the "otherwise" basic block."
    >
    > "Returns from the function.
    >
    > Like function calls, the exact semantics of returns in Rust are unclear.
    > Returning very likely at least assigns the value currently in the return
    > place (`_0`) to the place specified in the associated `Call` terminator
    > in the calling function, as if assigned via `dest = move _0`."
    >
    > "Indicates a terminator that can never be reached.
    >
    > Executing this terminator is UB."
    >
    > "Roughly speaking, evaluates the `func` operand and the arguments, and
    > starts execution of the referred to function. The operand types must
    > match the argument types of the function. The return place type must
    > match the return type."
    >
    > "Loads a value from the atomic integer. `load` takes an [`Ordering`]
    > argument which describes the memory ordering of this operation. Possible
    > values are [`SeqCst`], [`Acquire`] and [`Relaxed`]."

    Sources:
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L683-L808
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L2891-L2917 -/
inductive Terminator where
  | return_
  | goto (target : BlockId)
  | unreachable
  | callAtomicLoad (dst : LocalId) (ptr : Operand) (ord : Operand) (target : BlockId)
  | callPure2 (dst : LocalId) (callee : PureCallee2) (arg1 : Operand) (arg2 : Operand) (target : BlockId)
  | switchInt (discr : Operand) (falseTarget : BlockId) (trueTarget : BlockId)
  | assertNotOverflow (tupleLocal : LocalId) (target : BlockId)

/-- Basic block consisting of sequential statements and a single terminator.

    Corresponds to `rustc_middle::mir::BasicBlockData` in `Body::basic_blocks`.

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L207-L209 -/
structure BasicBlock where
  stmts : List Stmt
  terminator : Terminator

/-- Lowered `Runtime(PostCleanup)` MIR body of a single function.

    Corresponds to `rustc_middle::mir::Body`, recording the parameter types
    (`arg_count` arguments starting at local `1`), the return type (`_0`), the
    total number of locals, and the control-flow graph of basic blocks:

    > "The lowered representation of a single function."
    >
    > "Starting at local 1, `arg_count` locals will be provided by the caller
    > and can be assumed to be initialized."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L204-L251 -/
structure MirBody where
  argTys : List MirTy
  retTy : MirTy
  localCount : Nat
  blocks : List BasicBlock



/-- Modification-order timestamp for a memory location.

    In C++20 / Rust operational timestamp semantics, each memory location has a
    totally ordered modification order indexed by `Timestamp`:

    > "Rust atomics currently follow the same rules as [C++20 atomics][cpp],
    > specifically the rules from the [`intro.races`][cpp-intro.races] section,
    > without the "consume" memory ordering."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L27-L28 -/
abbrev Timestamp := Nat

/-- Thread or message coherence view mapping each memory location identifier to
    the latest modification-order timestamp observed at that location.

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L56-L58 -/
abbrev View := Nat → Timestamp

/-- Pointwise partial order (`v₁ ≤ v₂`) on coherence views: `v₁` is at or
    behind `v₂` when every location's timestamp in `v₁` is `≤` its timestamp in
    `v₂`. -/
instance instPreorderView : Preorder View where
  le v₁ v₂ := ∀ loc, v₁ loc ≤ v₂ loc
  le_refl _ _ := Nat.le_refl _
  le_trans h₁ h₂ loc := Nat.le_trans (h₁ loc) (h₂ loc)

/-- Initial bottom view assigning timestamp `0` to every location. -/
def View.bot : View :=
  fun _ => 0

/-- Advance view `v` at location `loc` to at least timestamp `ts`. -/
def View.bump (v : View) (loc : Nat) (ts : Timestamp) : View :=
  fun l => if l == loc then max (v l) ts else v l

/-- Pointwise join (least upper bound) of two coherence views `v₁` and `v₂`.

    Used when an `Acquire` load synchronizes with a prior `Release` store and
    incorporates the message's release view into the reading thread's view:

    > "When coupled with a load, if the loaded value was written by a store
    > operation with [`Release`] (or stronger) ordering, then all subsequent
    > operations become ordered after that store. In particular, all subsequent
    > loads will see data written before the store."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L489-L492 -/
def View.join (v₁ v₂ : View) : View :=
  fun loc => max (v₁ loc) (v₂ loc)

/-- A store event in the modification order of an atomic `usize` location,
    recording the target location `loc`, its modification-order timestamp `ts`,
    the stored `usize` payload `bits`, and the release view `relView` attached
    to the store.

    Corresponds to a modification of an atomic object in `core::sync::atomic`:

    > "When the C++ standard talks about "the value of an atomic object", this
    > refers to the result of doing an atomic load (via the operations provided
    > in this module). A "modification of an atomic object" refers to an atomic
    > store."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L31-L34 -/
structure AtomicMsg where
  loc : Nat
  ts : Timestamp
  bits : Nat
  relView : View

/-- Operational memory state combining the active thread's coherence view
    (`curView`), the modification-order history of atomic locations
    (`atomicMsgs`), and the deterministic non-atomic memory store (`naVal`,
    `naWriteTs`, `naReadTs`).

    Separating non-atomic locations from the atomic message history reflects
    Rust's data-race rule (`r[undefined.race]`): non-atomic accesses cannot race
    without triggering immediate UB, whereas atomic accesses choose
    nondeterministically among modification-order messages consistent with
    `curView`:

    > "The most important aspect of this model is that *data races* are
    > undefined behavior. A data race is defined as conflicting
    > non-synchronized accesses where at least one of the accesses is
    > non-atomic. Here, accesses are *conflicting* if they affect overlapping
    > regions of memory and at least one of them is a write."

    Sources:
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/behavior-considered-undefined.md#L15-L16
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L44-L49 -/
structure MemState where
  curView : View
  atomicMsgs : List AtomicMsg
  naVal : Nat → Option MirVal
  naWriteTs : Nat → Timestamp
  naReadTs : Nat → Timestamp

/-- Empty initial memory state with bottom views and no allocated locations. -/
def MemState.empty : MemState where
  curView := View.bot
  atomicMsgs := []
  naVal := fun _ => none
  naWriteTs := fun _ => 0
  naReadTs := fun _ => 0

/-- Deterministic non-atomic read at `loc`.

    Returns `some (v, m')` if `loc` holds an initialized value `v` and its last
    non-atomic write timestamp `m.naWriteTs loc` is visible in `m.curView loc`
    (no unsynchronized concurrent write); returns `none` on uninitialized access
    or data race (`r[undefined.race]`, `r[undefined.invalid]`).

    Sources:
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/behavior-considered-undefined.md#L15-L16
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L44-L49 -/
def MemState.readNA (m : MemState) (loc : Nat) : Option (MirVal × MemState) :=
  if decide (m.naWriteTs loc ≤ m.curView loc) then
    match m.naVal loc with
    | some v =>
      some (v, { m with
        naReadTs := View.bump m.naReadTs loc (m.curView loc) })
    | none => none
  else
    none

/-- Deterministic non-atomic write of `v` at `loc`.

    Returns `some m'` if both the last write (`m.naWriteTs loc`) and last read
    (`m.naReadTs loc`) at `loc` are visible in `m.curView loc` (no
    unsynchronized conflicting access); returns `none` on a data race
    (`r[undefined.race]`).

    Sources:
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/behavior-considered-undefined.md#L15-L16
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L44-L49 -/
def MemState.writeNA (m : MemState) (loc : Nat) (v : MirVal) : Option MemState :=
  if decide (m.naWriteTs loc ≤ m.curView loc) && decide (m.naReadTs loc ≤ m.curView loc) then
    let nextTs := m.curView loc + 1
    some { m with
      curView := View.bump m.curView loc nextTs
      naVal := fun l => if l == loc then some v else m.naVal l
      naWriteTs := View.bump m.naWriteTs loc nextTs
      naReadTs := View.bump m.naReadTs loc nextTs }
  else
    none

/-- Modification-order messages at atomic location `loc` that are visible to the
    active thread under read-read / write-read coherence (`m.curView loc ≤
    msg.ts`).

    In C++20 / Rust relaxed and acquire loads, a thread cannot observe a
    modification-order message older than the timestamp already recorded in its
    coherence view for `loc`:

    > "In its weakest [`Ordering::Relaxed`], only the memory directly touched
    > by the operation is synchronized."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L451-L452 -/
def MemState.visibleAtomicMsgs (m : MemState) (loc : Nat) : List AtomicMsg :=
  m.atomicMsgs.filter fun msg =>
    msg.loc == loc && decide (m.curView loc ≤ msg.ts)

/-- Update `MemState` after an atomic load with ordering `ord` observes message
    `msg`:
    - `AtomicOrdering.relaxed`: bumps `curView` at `msg.loc` to `msg.ts`.
    - `AtomicOrdering.acquire`: bumps `curView` at `msg.loc` to `msg.ts` and
      joins `curView` with `msg.relView`.

    Sources:
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L466-L503
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L3990-L4001 -/
def MemState.applyAtomicLoad (m : MemState) (ord : AtomicOrdering) (msg : AtomicMsg) : MemState :=
  let bumped := View.bump m.curView msg.loc msg.ts
  match ord with
  | .relaxed => { m with curView := bumped }
  | .acquire => { m with curView := View.join bumped msg.relView }



/-- Instantaneous execution state of a `MirBody`, recording the contents of
    each local slot (`none` when uninitialized or deallocated, `some v` when
    holding an initialized `MirVal`), the operational memory state `mem`
    (`Trusted/Memory.lean`), the active basic block index, and the statement
    index within that basic block. -/
structure MirState where
  locals : Nat → Option MirVal
  mem : MemState
  block : Nat
  stmtIdx : Nat

/-- Update local slot `target` in a local store `locals`. -/
def updateLocal (locals : Nat → Option MirVal) (target : Nat)
    (val : Option MirVal) : Nat → Option MirVal :=
  fun i => if i == target then val else locals i

/-- Dynamic type-validity relation matching an initialized `MirVal` against a
    `MirTy` in memory state `m`.

    Corresponds to Rust's value validity requirement that every produced scalar
    value or reference be initialized, non-dangling, and match its static type
    (`r[undefined.invalid]`, `r[undefined.validity.reference-box]`):

    > "The Rust compiler assumes that all values produced during program
    > execution are "valid", and producing an invalid value is hence immediate
    > UB."
    >
    > "* A reference or [`Box<T>`] must be aligned and non-null, it cannot be
    > [dangling], and it must point to a valid value"

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/behavior-considered-undefined.md#L114-L147 -/
def MirVal.hasTy (m : MemState) (v : MirVal) (ty : MirTy) : Prop :=
  match v, ty with
  | .usize _, .usize => True
  | .bool _, .bool => True
  | .unit, .unit => True
  | .tupleUsizeBool _ _, .tupleUsizeBool => True
  | .atomicLoc loc, .refAtomicUsize => m.visibleAtomicMsgs loc ≠ []
  | .refSharedLoc loc, .refSharedUsize =>
    ∃ n, m.naVal loc = some (.usize n) ∧
      m.naWriteTs loc ≤ m.curView loc
  | .refMutLoc loc, .refMutUsize =>
    ∃ n, m.naVal loc = some (.usize n) ∧
      m.naWriteTs loc ≤ m.curView loc ∧
      m.naReadTs loc ≤ m.curView loc
  | .ordering _, .atomicOrdering => True
  | _, _ => False

/-- Parameter validity at argument index `k` (`1 ..= argTys.length`), combining
    value validity (`MirVal.hasTy`) with Rust's reference aliasing rules
    (`r[undefined.alias]`: a `&mut usize` parameter cannot alias any preceding
    `&mut usize` or `&usize` parameter, and a `&usize` parameter cannot alias
    any preceding `&mut usize` parameter, while `&usize` parameters may alias
    each other):

    > "* Breaking the [pointer aliasing rules]. `Box<T>`, `&mut T`, and `&T`
    > follow LLVM's scoped `noalias` model, except if the `&T` contains an
    > [`UnsafeCell<U>`]. This means references and boxes cannot be dangling
    > while they are live, and mutable references and boxes cannot be aliased"

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/behavior-considered-undefined.md#L48-L52 -/
def argValidAt (m : MemState) (locals : Nat → Option MirVal) (k : Nat)
    (v : MirVal) (ty : MirTy) : Prop :=
  match ty with
  | .refMutUsize =>
    v.hasTy m .refMutUsize ∧
      ∀ loc i, v = .refMutLoc loc → 1 ≤ i → i < k →
        locals i ≠ some (.refMutLoc loc) ∧ locals i ≠ some (.refSharedLoc loc)
  | .refSharedUsize =>
    v.hasTy m .refSharedUsize ∧
      ∀ loc i, v = .refSharedLoc loc → 1 ≤ i → i < k →
        locals i ≠ some (.refMutLoc loc)
  | _ => v.hasTy m ty

/-- Entry initialization condition for function arguments and non-argument
    locals.

    Starting at local `1` at function entry, each parameter type in `argTys`
    holds an initialized `MirVal` matching its `MirTy` in `m`, while remaining
    locals start uninitialized (`none`):

    > "Starting at local 1, `arg_count` locals will be provided by the caller
    > and can be assumed to be initialized."
    >
    > "At any point during the execution of a function, each local is either
    > allocated or unallocated. Except as noted below, all locals except
    > function parameters are initially unallocated."

    Sources:
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L245-L249
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L366-L368 -/
def argsMatchLocals (m : MemState) (argTys : List MirTy)
    (locals : Nat → Option MirVal) : Prop :=
  argTys.foldr
    (fun ty rest k => (∃ v, locals k = some v ∧ argValidAt m locals k v ty) ∧ rest (k + 1))
    (fun k => ∀ j, k ≤ j → locals j = none)
    1

/-- Entry state predicate for a `MirBody`: execution starts at basic block `0`,
    statement `0`, with the return place `_0` uninitialized and argument locals
    `1 ..= argTys.length` initialized to type-valid values in `s.mem`.

    Corresponds to function body entry in the Rust Reference and `rustc` MIR:

    > "The body block of a function is conceptually wrapped in another block
    > that first binds the argument patterns and then `return`s the value of
    > the function's body."

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/items/functions.md#L114-L116 -/
def initMirState (body : MirBody) (s : MirState) : Prop :=
  s.block = 0 ∧
  s.stmtIdx = 0 ∧
  s.locals 0 = none ∧
  argsMatchLocals s.mem body.argTys s.locals

/-- Evaluate a MIR `Operand` against a local store `locals`, returning the
    produced `MirVal` and the updated local store (`Operand.copy` preserves the
    source local; `Operand.move` deinitializes it; reading an uninitialized
    local returns `none` for immediate UB):

    > "* Producing an [invalid value][invalid-values]. "Producing" a value
    > happens any time a value is assigned to or read from a place, passed to a
    > function/primitive operation or returned from a function/primitive
    > operation."
    >
    > "If the type of that value implements [`Copy`], then the value will be
    > copied."
    >
    > "After moving out of a place expression that evaluates to a local
    > variable, the location is deinitialized and cannot be read from again
    > until it is reinitialized."

    Sources:
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/behavior-considered-undefined.md#L54-L55
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/expressions.md#L199-L215 -/
def evalOperand (locals : Nat → Option MirVal) (op : Operand) :
    Option (MirVal × (Nat → Option MirVal)) :=
  match op with
  | .copy src =>
    match locals src.index with
    | some v => some (v, locals)
    | none => none
  | .move src =>
    match locals src.index with
    | some v => some (v, updateLocal locals src.index none)
    | none => none
  | .constVal v =>
    some (v, locals)

/-- Evaluate a binary comparison or bitwise operator on two `MirVal.usize`
    values, returning `some (.bool b)` for comparisons or `some (.usize n)` for
    bitwise operations on `.usize` inputs, and `none` on type mismatch
    (`r[undefined.invalid]`).

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L1409-L1443 -/
def evalBinOp (op : BinOp) (v1 v2 : MirVal) : Option MirVal :=
  match v1, v2 with
  | .usize n1, .usize n2 =>
    match op with
    | .lt => some (.bool (decide (n1 < n2)))
    | .le => some (.bool (decide (n1 ≤ n2)))
    | .eq => some (.bool (decide (n1 = n2)))
    | .ne => some (.bool (decide (n1 ≠ n2)))
    | .gt => some (.bool (decide (n2 < n1)))
    | .ge => some (.bool (decide (n2 ≤ n1)))
    | .bitAnd => some (.usize (Nat.land n1 n2))
    | .bitOr => some (.usize (Nat.lor n1 n2))
    | .bitXor => some (.usize (Nat.xor n1 n2))
  | _, _ => none

/-- Maximum representable 64-bit `usize` value (`usize::MAX = 2^64 - 1`).

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/types/numeric.md#L37-L38 -/
def usizeMax : Nat := 18446744073709551615

/-- Evaluate a checked binary arithmetic operator (`AddWithOverflow`,
    `SubWithOverflow`, `MulWithOverflow`) on two `MirVal.usize` values,
    returning `some (.tupleUsizeBool val overflow)` on `.usize` inputs and
    `none` on type mismatch.

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L1409-L1443 -/
def evalCheckedBinOp (op : CheckedBinOp) (v1 v2 : MirVal) : Option MirVal :=
  match v1, v2 with
  | .usize n1, .usize n2 =>
    match op with
    | .add => some (.tupleUsizeBool (n1 + n2) (decide (usizeMax < n1 + n2)))
    | .sub => some (.tupleUsizeBool (n1 - n2) (decide (n1 < n2)))
    | .mul => some (.tupleUsizeBool (n1 * n2) (decide (usizeMax < n1 * n2)))
  | _, _ => none

/-- Single-step operational evaluation of a MIR statement.

    Models `Operand::Copy`, `Operand::Move`, `Rvalue::Use`, dereference reads
    `copy (*src)`, `Rvalue::BinaryOp`, `StatementKind::Assign` (to a local or
    dereferenced place `(*dst) = op`), `StatementKind::StorageLive`,
    `StatementKind::StorageDead`, and `StatementKind::Nop`.

    Sources:
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L305-L385
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L975-L1005 -/
def evalMirStmt (s : MirState) (stmt : Stmt) : StepResult MirState Unit MirVal :=
  match stmt with
  | .assign dst (.use op) =>
    match evalOperand s.locals op with
    | some (v, locals') =>
      .step () { s with
        locals := updateLocal locals' dst.index (some v)
        stmtIdx := s.stmtIdx + 1
      }
    | none => .failed .ub
  | .assign dst (.deref src) =>
    match s.locals src.index with
    | some (.refMutLoc loc) | some (.refSharedLoc loc) =>
      match s.mem.readNA loc with
      | some (v, mem') =>
        .step () { s with
          locals := updateLocal s.locals dst.index (some v)
          mem := mem'
          stmtIdx := s.stmtIdx + 1
        }
      | none => .failed .ub
    | _ => .failed .ub
  | .assign dst (.binaryOp op lhs rhs) =>
    match evalOperand s.locals lhs with
    | none => .failed .ub
    | some (v1, locals1) =>
      match evalOperand locals1 rhs with
      | none => .failed .ub
      | some (v2, locals2) =>
        match evalBinOp op v1 v2 with
        | some res =>
          .step () { s with
            locals := updateLocal locals2 dst.index (some res)
            stmtIdx := s.stmtIdx + 1
          }
        | none => .failed .ub
  | .assign dst (.checkedBinaryOp op lhs rhs) =>
    match evalOperand s.locals lhs with
    | none => .failed .ub
    | some (v1, locals1) =>
      match evalOperand locals1 rhs with
      | none => .failed .ub
      | some (v2, locals2) =>
        match evalCheckedBinOp op v1 v2 with
        | some res =>
          .step () { s with
            locals := updateLocal locals2 dst.index (some res)
            stmtIdx := s.stmtIdx + 1
          }
        | none => .failed .ub
  | .assign dst (.proj0 src) =>
    match s.locals src.index with
    | some (.tupleUsizeBool val _) =>
      .step () { s with
        locals := updateLocal s.locals dst.index (some (.usize val))
        stmtIdx := s.stmtIdx + 1
      }
    | _ => .failed .ub
  | .assign dst (.proj1 src) =>
    match s.locals src.index with
    | some (.tupleUsizeBool _ ov) =>
      .step () { s with
        locals := updateLocal s.locals dst.index (some (.bool ov))
        stmtIdx := s.stmtIdx + 1
      }
    | _ => .failed .ub
  | .assignDeref dst op =>
    match evalOperand s.locals op with
    | none => .failed .ub
    | some (v, locals1) =>
      match locals1 dst.index with
      | some (.refMutLoc loc) =>
        match s.mem.writeNA loc v with
        | some mem' =>
          .step () { s with
            locals := locals1
            mem := mem'
            stmtIdx := s.stmtIdx + 1
          }
        | none => .failed .ub
      | _ => .failed .ub
  | .storageLive loc =>
    .step () { s with
      locals := updateLocal s.locals loc.index none
      stmtIdx := s.stmtIdx + 1
    }
  | .storageDead loc =>
    .step () { s with
      locals := updateLocal s.locals loc.index none
      stmtIdx := s.stmtIdx + 1
    }
  | .nop =>
    .step () { s with stmtIdx := s.stmtIdx + 1 }

/-- Evaluate a pure 2-argument `usize` callee (`add_bounded` or `abs_diff`)
    according to its verified functional contract.

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L766-L808 -/
def evalPureCallee2 (callee : PureCallee2) (v1 v2 : MirVal) : Option MirVal :=
  match v1, v2 with
  | .usize x0, .usize y0 =>
    match callee with
    | .addBounded =>
      some (.usize (if decide (x0 ≤ 1000) && decide (y0 ≤ 1000) then x0 + y0 else 0))
    | .absDiff =>
      some (.usize (if decide (y0 ≤ x0) then x0 - y0 else y0 - x0))
  | _, _ => none

/-- Single-step operational evaluation of a MIR basic-block terminator.

    Models `TerminatorKind::Return`, `TerminatorKind::Goto`,
    `TerminatorKind::Unreachable`, `TerminatorKind::Call` specialized to
    `Atomic::<usize>::load`, and `TerminatorKind::SwitchInt` on boolean
    discriminants:
    - `Terminator.return_` reads the return place `_0` (`s.locals 0`) and
      completes with `.terminated (.normal retVal)` if initialized, or triggers
      `.failed .ub` if `_0` is uninitialized (`r[undefined.invalid]`).
    - `Terminator.goto target` transfers control to statement `0` of
      `target.index`.
    - `Terminator.unreachable` triggers immediate `.failed .ub`.
    - `Terminator.callAtomicLoad dst ptrOp ordOp target` evaluates `ptrOp` and
      `ordOp` left-to-right (`syntax.rs#L783-L784`) and performs an atomic load
      on `s.mem` (`atomic.rs#L2891-L2917`, `#L3990-L4001`): if `loc` has
      visible modification-order messages `head :: tail` (`s.mem.curView loc ≤
      msg.ts`),
      it emits a demonic choice (`.choice .demonic`) over every visible message
      `msg ∈ head :: tail`, storing `MirVal.usize msg.bits` into `dst` and
      advancing `s.mem` via `s.mem.applyAtomicLoad ord msg`.
    - `Terminator.switchInt discr falseTarget trueTarget` evaluates `discr` to a
      `MirVal.bool b` and jumps to `falseTarget` when `b = false` (`0`) or
      `trueTarget` when `b = true` (`otherwise`).

    > "Block has one successor; we continue execution there."
    >
    > "Returning very likely at least assigns the value currently in the return
    > place (`_0`) to the place specified in the associated `Call` terminator
    > in the calling function, as if assigned via `dest = move _0`."
    >
    > "Indicates a terminator that can never be reached.
    >
    > Executing this terminator is UB."
    >
    > "The evaluation order is currently "first compute destination place, then
    > `func` operand, then the arguments in left-to-right order"."

    Sources:
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L684-L808
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L2891-L2917
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L3990-L4001 -/
def evalMirTerminator (s : MirState) (term : Terminator) :
    StepResult MirState Unit MirVal :=
  match term with
  | .return_ =>
    match s.locals 0 with
    | some retVal => .terminated (.normal retVal)
    | none => .failed .ub
  | .goto target =>
    .step () { s with block := target.index, stmtIdx := 0 }
  | .unreachable =>
    .failed .ub
  | .callAtomicLoad dst ptrOp ordOp target =>
    match evalOperand s.locals ptrOp with
    | none => .failed .ub
    | some (ptrVal, locals1) =>
      match evalOperand locals1 ordOp with
      | none => .failed .ub
      | some (ordVal, locals2) =>
        match ptrVal, ordVal with
        | .atomicLoc loc, .ordering ord =>
          match s.mem.visibleAtomicMsgs loc with
          | [] => .failed .ub
          | head :: tail =>
            .choice .demonic (fun s' =>
              ∃ msg, msg ∈ (head :: tail) ∧
                s' = {
                  locals := updateLocal locals2 dst.index (some (.usize msg.bits))
                  mem := s.mem.applyAtomicLoad ord msg
                  block := target.index
                  stmtIdx := 0
                })
        | _, _ => .failed .ub
  | .callPure2 dst callee arg1 arg2 target =>
    match evalOperand s.locals arg1 with
    | none => .failed .ub
    | some (v1, locals1) =>
      match evalOperand locals1 arg2 with
      | none => .failed .ub
      | some (v2, locals2) =>
        match evalPureCallee2 callee v1 v2 with
        | some res =>
          .step () { s with
            locals := updateLocal locals2 dst.index (some res)
            block := target.index
            stmtIdx := 0
          }
        | none => .failed .ub
  | .switchInt discr falseTarget trueTarget =>
    match evalOperand s.locals discr with
    | some (.bool false, locals') =>
      .step () { s with
        locals := locals'
        block := falseTarget.index
        stmtIdx := 0
      }
    | some (.bool true, locals') =>
      .step () { s with
        locals := locals'
        block := trueTarget.index
        stmtIdx := 0
      }
    | _ => .failed .ub
  | .assertNotOverflow tupleLocal target =>
    match s.locals tupleLocal.index with
    | some (.tupleUsizeBool _ false) =>
      .step () { s with
        block := target.index
        stmtIdx := 0
      }
    | some (.tupleUsizeBool _ true) =>
      .failed .contractViolation
    | _ => .failed .ub

/-- Single-step transition function of a `MirBody`: executes the statement at
    `s.stmtIdx` in block `s.block`, or the block's terminator once all
    statements in `s.block` have completed. Jumping to an out-of-bounds basic
    block index triggers `.failed .ub`. -/
def evalMirStep (body : MirBody) (s : MirState) :
    StepResult MirState Unit MirVal :=
  match body.blocks[s.block]? with
  | none => .failed .ub
  | some bb =>
    match bb.stmts[s.stmtIdx]? with
    | some stmt => evalMirStmt s stmt
    | none => evalMirTerminator s bb.terminator

/-- Small-step operational machine for `MirBody`. -/
def MirMachine : SmallStepMachine MirBody MirState Unit MirVal where
  initState := initMirState
  step body s r := r = evalMirStep body s

/-- Operational language of Rust MIR (`MirMachine.toLanguage`). -/
def MirLang : Language :=
  MirMachine.toLanguage

/-- Operational behavior of a `MirBody`: the query-indexed partial behavior
    (`ExecQuery MirState → Partial (ExecOut Unit MirVal → Prop)`) induced by
    `MirMachine`. -/
abbrev MirSem (body : MirBody) : MirLang.Behavior :=
  MirLang.sem body

/-- Postcondition specification for a safe function asserting that:
    - `defined := True`: every finite execution prefix is free of UB and stuck
      states (`MirLang.WellFormed`), and
    - `val`: any normal return value equals the initial value of argument local
      `argLocal` (`1` for the first parameter `_1`). -/
def EnsuresEqArg (argLocal : Nat) : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      q.init.locals argLocal = some ret)

/-- Postcondition specification for a safe atomic load from `&AtomicUsize`
    argument `argLocal` (`1` for the first parameter `_1`):
    - `defined := True`: every finite execution prefix is free of UB and stuck
      states (`MirLang.WellFormed`), and
    - `val`: any normal return value `ret` equals `MirVal.usize msg.bits` for
      some modification-order message `msg` at `argLocal`'s atomic location that
      was visible in `q.init.mem`. -/
def EnsuresAtomicLoad (argLocal : Nat) : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      ∃ loc msg,
        q.init.locals argLocal = some (.atomicLoc loc) ∧
        msg ∈ q.init.mem.visibleAtomicMsgs loc ∧
        ret = .usize msg.bits)

/-- Postcondition specification for `pub fn max_assign(x: &mut usize, y: usize)
    -> usize`:
    - `defined := True`: every finite execution prefix is free of UB and stuck
      states (`MirLang.WellFormed`), and
    - `val`: for any initial state where `_1` points to non-atomic location
      `loc` holding `.usize x0` and `_2` holds `.usize y0`, any normal return
      value `ret` equals `.usize (if decide (x0 < y0) then y0 else x0)`. -/
def EnsuresMaxAssign : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret loc x0 y0,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.refMutLoc loc) →
      q.init.mem.naVal loc = some (.usize x0) →
      q.init.locals 2 = some (.usize y0) →
      ret = .usize (if decide (x0 < y0) then y0 else x0))

/-- Postcondition specification for
    `pub fn update_min(x: &mut usize, y: &mut usize, v: usize) -> usize`:
    - `defined := True`: every finite execution prefix is free of UB and stuck
      states (`MirLang.WellFormed`), and
    - `val`: for any initial state where `_1` points to non-atomic location
      `locX` holding `.usize x0`, `_2` points to non-atomic location `locY`
      holding `.usize y0`, and `_3` holds `.usize v0`, any normal return value
      `ret` (which reads `*x` after mutating the conditionally borrowed minimum
      reference `r = if *x <= *y { &mut *x } else { &mut *y }` to `v`) equals
      `.usize (if decide (x0 ≤ y0) then v0 else x0)`. -/
def EnsuresUpdateMin : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret locX locY x0 y0 v0,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.refMutLoc locX) →
      q.init.mem.naVal locX = some (.usize x0) →
      q.init.locals 2 = some (.refMutLoc locY) →
      q.init.mem.naVal locY = some (.usize y0) →
      q.init.locals 3 = some (.usize v0) →
      ret = .usize (if decide (x0 ≤ y0) then v0 else x0))

/-- Postcondition specification for
    `pub fn clamp_assign(x: &mut usize, lo: usize, hi: usize) -> usize`:
    - `defined := True`: every finite execution prefix is free of UB and stuck
      states (`MirLang.WellFormed`), and
    - `val`: for any initial state where `_1` points to non-atomic location
      `loc` holding `.usize x0`, `_2` holds `.usize lo`, and `_3` holds
      `.usize hi`, any normal return value `ret` equals
      `.usize (if decide (x0 < lo) then lo else if decide (hi < x0) then hi else
      x0)`. -/
def EnsuresClampAssign : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret loc x0 lo hi,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.refMutLoc loc) →
      q.init.mem.naVal loc = some (.usize x0) →
      q.init.locals 2 = some (.usize lo) →
      q.init.locals 3 = some (.usize hi) →
      ret = .usize (if decide (x0 < lo) then lo else if decide (hi < x0) then hi else x0))

/-- Postcondition specification for
    `pub fn is_aligned_mask(addr: usize, mask: usize) -> bool`:
    - `defined := True`: every finite execution prefix is free of UB and stuck
      states (`MirLang.WellFormed`), and
    - `val`: for any initial state where `_1` holds `.usize addr` and `_2`
      holds `.usize mask`, any normal return value `ret` equals
      `.bool (decide (Nat.land addr mask = 0))`. -/
def EnsuresIsAlignedMask : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret addr mask,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.usize addr) →
      q.init.locals 2 = some (.usize mask) →
      ret = .bool (decide (Nat.land addr mask = 0)))

/-- Postcondition specification for
    `pub fn shared_max(x: &usize, y: &usize) -> usize`:
    - `defined := True`: every finite execution prefix is free of UB and stuck
      states (`MirLang.WellFormed`), including when `x` and `y` alias the same
      memory location (`locX = locY`), and
    - `val`: for any initial state where `_1` points to shared location `locX`
      holding `.usize x0` and `_2` points to shared location `locY` holding
      `.usize y0`, any normal return value `ret` equals
      `.usize (if decide (x0 < y0) then y0 else x0)`. -/
def EnsuresSharedMax : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret locX locY x0 y0,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.refSharedLoc locX) →
      q.init.mem.naVal locX = some (.usize x0) →
      q.init.locals 2 = some (.refSharedLoc locY) →
      q.init.mem.naVal locY = some (.usize y0) →
      ret = .usize (if decide (x0 < y0) then y0 else x0))

/-- Postcondition specification for
    `pub fn max_assign_shared(dst: &mut usize, src: &usize) -> usize`:
    - `defined := True`: every finite execution prefix is free of UB and stuck
      states (`MirLang.WellFormed`), and
    - `val`: for any initial state where `_1` points to mutable location
      `locDst`
      holding `.usize d0` and `_2` points to shared location `locSrc` holding
      `.usize s0`, any normal return value `ret` equals
      `.usize (if decide (d0 < s0) then s0 else d0)`. -/
def EnsuresMaxAssignShared : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret locDst locSrc d0 s0,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.refMutLoc locDst) →
      q.init.mem.naVal locDst = some (.usize d0) →
      q.init.locals 2 = some (.refSharedLoc locSrc) →
      q.init.mem.naVal locSrc = some (.usize s0) →
      ret = .usize (if decide (d0 < s0) then s0 else d0))

/-- Postcondition specification for
    `pub fn sort_pair(x: &mut usize, y: &mut usize) -> usize`:
    - `defined := True`: every finite execution prefix is free of UB and stuck
      states (`MirLang.WellFormed`), and
    - `val`: for any initial state where `_1` points to `locX` holding
      `.usize x0` and `_2` points to `locY` holding `.usize y0`, any normal
      return value `ret` equals `.usize (if decide (y0 < x0) then y0 else
      x0)`. -/
def EnsuresSortPair : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret locX locY x0 y0,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.refMutLoc locX) →
      q.init.mem.naVal locX = some (.usize x0) →
      q.init.locals 2 = some (.refMutLoc locY) →
      q.init.mem.naVal locY = some (.usize y0) →
      ret = .usize (if decide (y0 < x0) then y0 else x0))

/-- Postcondition specification for
    `pub fn two_phase_reborrow(x: &mut usize, y: &mut usize, a: usize, b: usize)
    -> usize`:
    - `defined := True`: every finite execution prefix is free of UB and stuck
      states (`MirLang.WellFormed`), and
    - `val`: for any initial state where `_1` points to `locX` holding
      `.usize x0`, `_2` points to `locY` holding `.usize y0`, `_3 = some (.usize
      a)`,
      and `_4 = some (.usize b)`, any normal return value `ret` equals
      `.usize (if decide ((if decide (x0 ≤ y0) then a else x0) ≤ (if decide (x0
      ≤ y0) then y0 else a)) then (if decide (x0 ≤ y0) then a else x0) else
      b)`. -/
def EnsuresTwoPhaseReborrow : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret locX locY x0 y0 a b,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.refMutLoc locX) →
      q.init.mem.naVal locX = some (.usize x0) →
      q.init.locals 2 = some (.refMutLoc locY) →
      q.init.mem.naVal locY = some (.usize y0) →
      q.init.locals 3 = some (.usize a) →
      q.init.locals 4 = some (.usize b) →
      ret = .usize
        (if decide ((if decide (x0 ≤ y0) then a else x0) ≤ (if decide (x0 ≤ y0) then y0 else a))
         then (if decide (x0 ≤ y0) then a else x0)
         else b))

/-- Postcondition specification for
    `pub fn add_bounded(x: usize, y: usize) -> usize`:
    - `defined := True`: every finite execution prefix is free of UB, stuck
      states, and overflow assertion failures (`MirLang.WellFormed`), and
    - `val`: for any initial state where `_1 = some (.usize x0)` and
      `_2 = some (.usize y0)`, any normal return value `ret` equals
      `.usize (if decide (x0 ≤ 1000) && decide (y0 ≤ 1000) then x0 + y0 else
      0)`. -/
def EnsuresAddBounded : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret x0 y0,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.usize x0) →
      q.init.locals 2 = some (.usize y0) →
      ret = .usize (if decide (x0 ≤ 1000) && decide (y0 ≤ 1000) then x0 + y0 else 0))

/-- Postcondition specification for
    `pub fn abs_diff(x: usize, y: usize) -> usize`:
    - `defined := True`: every finite execution prefix is free of UB, stuck
      states, and underflow assertion failures (`MirLang.WellFormed`), and
    - `val`: for any initial state where `_1 = some (.usize x0)` and
      `_2 = some (.usize y0)`, any normal return value `ret` equals
      `.usize (if decide (y0 ≤ x0) then x0 - y0 else y0 - x0)`. -/
def EnsuresAbsDiff : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret x0 y0,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.usize x0) →
      q.init.locals 2 = some (.usize y0) →
      ret = .usize (if decide (y0 ≤ x0) then x0 - y0 else y0 - x0))

/-- Postcondition specification for
    `pub fn choose_mut<'a>(b: bool, x: &'a mut usize, y: &'a mut usize) -> &'a
    mut usize`:
    - `defined := True`: every finite execution prefix is free of UB and stuck
      states (`MirLang.WellFormed`), and
    - `val`: for any initial state where `_1 = some (.bool b)`, `_2` points to
      `locX` (`some (.refMutLoc locX)`), and `_3` points to `locY`
      (`some (.refMutLoc locY)`), any normal return value `ret` equals
      `.refMutLoc (if b then locX else locY)`. -/
def EnsuresChooseMut : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret b locX locY,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.bool b) →
      q.init.locals 2 = some (.refMutLoc locX) →
      q.init.locals 3 = some (.refMutLoc locY) →
      ret = .refMutLoc (if b then locX else locY))

/-- Postcondition specification for
    `pub fn count_up(n: usize) -> usize`:
    - `defined := True`: every finite execution prefix is free of UB, stuck
      states, and overflow assertion failures (`MirLang.WellFormed`), and
    - `val`: for any initial state where `_1 = some (.usize n0)`, any normal
      return value `ret` equals
      `.usize (if decide (n0 ≤ 1000) then n0 else 1000)`. -/
def EnsuresCountUp : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret n0,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.usize n0) →
      ret = .usize (if decide (n0 ≤ 1000) then n0 else 1000))

/-- Postcondition specification for
    `pub fn double_bounded(x: usize) -> usize { add_bounded(x, x) }`:
    - `defined := True`: every finite execution prefix is free of UB, stuck
      states, and overflow assertion failures (`MirLang.WellFormed`), and
    - `val`: for any initial state where `_1 = some (.usize x0)`, any normal
      return value `ret` equals
      `.usize (if decide (x0 ≤ 1000) && decide (x0 ≤ 1000) then x0 + x0 else
      0)`. -/
def EnsuresDoubleBounded : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret x0,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.usize x0) →
      ret = .usize (if decide (x0 ≤ 1000) && decide (x0 ≤ 1000) then x0 + x0 else 0))

/-- Abstract type of compiled target artifacts produced by `rustc`. -/
structure TargetArtifact where
  private mk ::
  unit : Unit

/-- Abstract `rustc` lowering from a `MirBody` to a `TargetArtifact`. Declared
    `opaque` so that proofs cannot unfold target compilation and must instead
    invoke the audited `TCBItem.rustcLowering` assumption. -/
def rustc : MirBody → TargetArtifact := fun _ => { unit := () }

/-- Abstract operational behavior of a compiled `TargetArtifact`. -/
def TargetSem :
    TargetArtifact → ExecQuery MirState → Partial (ExecOut Unit MirVal → Prop) :=
  fun _ _ => Partial.ub

/-- Target language of compiled `TargetArtifact`s. -/
def TargetLang : Language where
  Prog := TargetArtifact
  Query := ExecQuery MirState
  Out := ExecOut Unit MirVal
  sem := TargetSem

/-- Abstract compiler behavior mapping from MIR behaviors to target
    behaviors. -/
def π_c : MirLang.Behavior → TargetLang.Behavior :=
  fun b => b

/-- `rustc` compiler lowering from `MirLang` to `TargetLang` under `π_c`. -/
def RustcCompiler : Compiler MirLang TargetLang where
  compile := rustc
  π := π_c

/-- Audited assumption category in a crate's Trusted Computing Base. -/
inductive TCBItem where
  /-- Standard compiler lowering assumption for a function: `RustcCompiler` is
      sound on `body` (`RustcCompiler.SoundOn body`). -/
  | rustcLowering (fnName : String) (body : MirBody)
  /-- Explicit user-supplied axiom assumption (`#[anneal::axiom]`). -/
  | userAxiom (name : String) (prop : Prop)

/-- Semantic meaning of each Rust `TCBItem` as a `TrustedAssumption`. -/
instance instTrustedAssumptionTCBItem : TrustedAssumption TCBItem where
  meaning
    | .rustcLowering _ body => RustcCompiler.SoundOn body
    | .userAxiom _ prop => prop

/-- Default trust policy: standard `rustc` lowering assumptions are permitted;
    unapproved user axioms are rejected. -/
def defaultTrustPolicy : TrustPolicy TCBItem where
  isAllowed
    | .rustcLowering _ _ => True
    | .userAxiom _ _ => False

/-- Captured MIR function pairing its identifier (`name`), lowered `MirBody`
    (`prog`), caller safety precondition (`pre`, defaulting to `fun _ => True`
    for safe functions), and additional specifications (`specs`, defaulting to
    `[]`). -/
structure CapturedFn where
  name : String
  prog : MirBody
  pre : ExecQuery MirState → Prop := fun _ => True
  specs : List MirLang.Behavior := []

/-- Captured Rust crate bundling its functions and TCB audit log. -/
structure Crate where
  functions : List CapturedFn
  tcb : List TCBItem

/-- Top-level theorem required of every verified Rust crate:
    1. The crate contains at least one captured function (`c.functions ≠ []`).
    2. Every captured function `fn ∈ c.functions` satisfies
       `VerificationResultOn RustcCompiler defaultTrustPolicy c.tcb fn.prog
       fn.pre fn.specs`
       —proving that `c.tcb` complies with `defaultTrustPolicy` and, assuming
       the meaning of every item in `c.tcb`, proving
       `RustcCompiler.Verified fn.prog` on the non-empty specification list
       `MirLang.WellFormedOn fn.pre :: fn.specs`. -/
def CrateTheorem (c : Crate) : Prop :=
  c.functions ≠ [] ∧
  AllHold (c.functions.map (fun fn =>
    VerificationResultOn RustcCompiler defaultTrustPolicy c.tcb fn.prog fn.pre fn.specs))


/-- Identity mapping on any behavior domain is monotone. -/
theorem monotone_id {B : Type u} [Preorder B] : Monotone (fun b : B => b) :=
  fun _ _ h => h

/-- Composition of two monotone mappings is monotone. -/
theorem monotone_comp {A : Type u} {B : Type v} {C : Type w}
    [Preorder A] [Preorder B] [Preorder C]
    {g : B → C} {f : A → B}
    (hg : Monotone g) (hf : Monotone f) :
    Monotone (fun a => g (f a)) :=
  fun _ _ h => hg (hf h)

/-- Lifting a monotone map `f : B₁ → B₂` via `Partial.map` yields a monotone
    map `Partial B₁ → Partial B₂`. -/
theorem Partial.monotone_map {B₁ : Type u} {B₂ : Type v}
    [Preorder B₁] [Preorder B₂]
    {f : B₁ → B₂} (hf : Monotone f) :
    Monotone (Partial.map f) := by
  intro p₁ p₂ hp hdef₂
  cases hp hdef₂ with
  | intro hdef₁ hle =>
    exact ⟨hdef₁, hf hle⟩

/-- `Partial.ub` (`defined := False`) is the top element of `Partial B`: every
    partial value `p : Partial B` refines `Partial.ub`. -/
theorem ub_top {B : Type u} [Preorder B] (p : Partial B) :
    p ≤ Partial.ub :=
  fun h => False.elim h

/-- `Partial.ub` refines a partial value `p : Partial B` if and only if `p` is
    undefined (`¬ p.defined`). -/
theorem ub_le_iff {B : Type u} [Preorder B] (p : Partial B) :
    Partial.ub ≤ p ↔ ¬ p.defined :=
  ⟨fun h hdef => (h hdef).1, fun hnot hdef => False.elim (hnot hdef)⟩

/-- On unconditionally defined values (`Partial.pure`), the `Partial B`
    refinement preorder coincides with the underlying preorder on `B`. -/
theorem pure_le_pure_iff {B : Type u} [Preorder B] (b₁ b₂ : B) :
    Partial.pure b₁ ≤ Partial.pure b₂ ↔ b₁ ≤ b₂ := by
  constructor
  · intro h
    cases h True.intro with
    | intro _ hle => exact hle
  · intro hle _
    exact ⟨True.intro, hle⟩

/-- Undefined behavior (`Partial.ub`) never refines a defined specification
    (`Partial.pure b`). -/
theorem not_ub_le_pure {B : Type u} [Preorder B] (b : B) :
    ¬ ((@Partial.ub B) ≤ Partial.pure b) :=
  fun h => (ub_le_iff (Partial.pure b)).mp h True.intro

/-- Refining `L.SpecOn pre post` is equivalent to being defined and satisfying
    `post q` at every query `q` where `pre q` holds. -/
theorem le_specOn_iff {L : Language} (b : L.Behavior)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    b ≤ L.SpecOn pre post ↔
      ∀ q, pre q → ∃ h : (b q).defined, ∀ out, (b q).val h out → post q out :=
  ⟨fun h => h, fun h => h⟩

/-- Refining `L.WellFormedOn pre` is equivalent to being defined at every query
    `q` satisfying `pre q`. -/
theorem le_wellFormedOn_iff {L : Language} (b : L.Behavior)
    (pre : L.Query → Prop) :
    b ≤ L.WellFormedOn pre ↔ ∀ q, pre q → (b q).defined := by
  constructor
  · intro h q hpre
    exact (h q hpre).1
  · intro h q hpre
    exact ⟨h q hpre, fun _ _ => True.intro⟩

/-- Refining `L.WellFormed` is equivalent to being defined at every query
    `q : L.Query`. -/
theorem le_wellFormed_iff {L : Language} (b : L.Behavior) :
    b ≤ L.WellFormed ↔ ∀ q, (b q).defined := by
  constructor
  · intro h q
    exact (le_wellFormedOn_iff b (fun _ => True)).mp h q True.intro
  · intro h
    exact (le_wellFormedOn_iff b (fun _ => True)).mpr (fun q _ => h q)

/-- Unconditional well-formedness (`L.WellFormed`) refines conditional
    well-formedness (`L.WellFormedOn pre`) for any precondition `pre`. -/
theorem wellFormed_le_wellFormedOn {L : Language} (pre : L.Query → Prop) :
    L.WellFormed ≤ L.WellFormedOn pre :=
  fun _ _ => ⟨True.intro, fun _ _ => True.intro⟩

/-- Every conditional specification `L.SpecOn pre post` refines baseline
    conditional well-formedness `L.WellFormedOn pre` on the same precondition
    `pre`. -/
theorem specOn_le_wellFormedOn {L : Language}
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    L.SpecOn pre post ≤ L.WellFormedOn pre :=
  fun _ hpre => ⟨hpre, fun _ _ => True.intro⟩

/-- Every unconditional specification `L.Spec post` refines `L.WellFormed`. -/
theorem spec_le_wellFormed {L : Language} (post : L.Query → L.Out → Prop) :
    L.Spec post ≤ L.WellFormed :=
  specOn_le_wellFormedOn (fun _ => True) post

/-- Any specification built from `Partial.pure` at every query (`L.Spec post`)
    refines `L.WellFormed`. -/
theorem pure_le_wellFormed {L : Language} (post : L.Query → L.Out → Prop) :
    (fun q => Partial.pure (post q)) ≤ L.WellFormed :=
  spec_le_wellFormed post

/-- If `pre q` fails at any query `q`, `L.SpecOn pre post` does not refine
    unconditional `L.WellFormed`: placing a functional precondition in
    `.defined` (`pre`) weakens definedness outside `pre` and is rejected as a
    standalone safe-function specification. -/
theorem not_specOn_le_wellFormed_of_not_pre {L : Language}
    {pre : L.Query → Prop} {post : L.Query → L.Out → Prop}
    {q : L.Query} (hnot : ¬ pre q) :
    ¬ (L.SpecOn pre post ≤ L.WellFormed) :=
  fun hwf => hnot ((le_wellFormed_iff (L.SpecOn pre post)).mp hwf q)

/-- Transitive composition of two pass refinements (`Compiles` or `Abstracts`).

    Because `Partial` internalizes definedness into the refinement preorder
    `≤`, composing `b₃ ≤ π₁ b₂` and `b₂ ≤ π₂ b₁` under a monotone mapping `π₁`
    requires only `Preorder.le_trans` and `Monotone`. -/
theorem pass_trans
    {B₁ : Type u} {B₂ : Type v} {B₃ : Type w}
    [Preorder B₁] [Preorder B₂] [Preorder B₃]
    {π₂ : B₁ → B₂} {π₁ : B₂ → B₃}
    (h_mono₁ : Monotone π₁)
    {b₁ : B₁} {b₂ : B₂} {b₃ : B₃}
    (h₂₃ : b₃ ≤ π₁ b₂)
    (h₁₂ : b₂ ≤ π₂ b₁) :
    b₃ ≤ π₁ (π₂ b₁) :=
  Preorder.le_trans h₂₃ (h_mono₁ h₁₂)

/-- Pipeline-ordered composition of two compilation passes: if `p₁` compiles to
    `p₂` under `π₁` (`Compiles L₁ L₂ π₁ p₁ p₂`), `p₂` compiles to `p₃` under
    `π₂` (`Compiles L₂ L₃ π₂ p₂ p₃`), and `π₂` is monotone, then `p₁` compiles
    to `p₃` under `fun b => π₂ (π₁ b)`. -/
theorem Compiles.comp
    {L₁ L₂ L₃ : Language}
    {π₁ : L₁.Behavior → L₂.Behavior} {π₂ : L₂.Behavior → L₃.Behavior}
    {p₁ : L₁.Prog} {p₂ : L₂.Prog} {p₃ : L₃.Prog}
    (h₁₂ : Compiles L₁ L₂ π₁ p₁ p₂)
    (h₂₃ : Compiles L₂ L₃ π₂ p₂ p₃)
    (h_mono₂ : Monotone π₂) :
    Compiles L₁ L₃ (fun b => π₂ (π₁ b)) p₁ p₃ :=
  pass_trans h_mono₂ h₂₃ h₁₂

/-- Pipeline-ordered composition of two verification abstraction passes: if `s`
    is abstracted by `v₁` under `π₁` (`Abstracts L₁ L_src π₁ v₁ s`), `v₁` is
    abstracted by `v₂` under `π₂` (`Abstracts L₂ L₁ π₂ v₂ v₁`), and `π₁` is
    monotone, then `s` is abstracted by `v₂` under `fun b => π₁ (π₂ b)`. -/
theorem Abstracts.comp
    {L₂ L₁ L_src : Language}
    {π₂ : L₂.Behavior → L₁.Behavior} {π₁ : L₁.Behavior → L_src.Behavior}
    {v₂ : L₂.Prog} {v₁ : L₁.Prog} {s : L_src.Prog}
    (h₁ : Abstracts L₁ L_src π₁ v₁ s)
    (h₂ : Abstracts L₂ L₁ π₂ v₂ v₁)
    (h_mono₁ : Monotone π₁) :
    Abstracts L₂ L_src (fun b => π₁ (π₂ b)) v₂ s :=
  pass_trans h_mono₁ h₁ h₂

/-- Discharge `C.Verified s spec` directly from compiler soundness on `s`
    (`C.SoundOn s`) and a source-level refinement proof (`L_src.sem s ≤
    spec`). -/
theorem Compiler.SoundOn.verify
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {spec : L_src.Behavior}
    (h_comp : C.SoundOn s)
    (h_src : L_src.sem s ≤ spec) :
    C.Verified s spec :=
  ⟨h_src, h_comp.2, Preorder.le_trans h_comp.2 (h_comp.1 h_src)⟩

/-- Y-diagram bridge theorem: discharges `C.Verified s (π_v spec)` from:
    1. A proof on the verifier's model (`L_v.sem v ≤ spec`),
    2. An `Abstracts` pass relating `v` and `s` under `π_v`
       (`L_src.sem s ≤ π_v (L_v.sem v)`),
    3. Monotonicity of the verifier behavior mapping (`Monotone π_v`), and
    4. Compiler soundness on `s` (`C.SoundOn s`). -/
theorem verify_through_passes
    {L_v L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {π_v : L_v.Behavior → L_src.Behavior} {spec : L_v.Behavior}
    {v : L_v.Prog} {s : L_src.Prog}
    (h_proof : L_v.sem v ≤ spec)
    (h_abs : Abstracts L_v L_src π_v v s)
    (h_mono_v : Monotone π_v)
    (h_comp : C.SoundOn s) :
    C.Verified s (π_v spec) :=
  Compiler.SoundOn.verify h_comp (Preorder.le_trans h_abs (h_mono_v h_proof))

/-- Monotonicity of `Compiler.Verified` in the specification argument: if `s`
    satisfies `C.Verified s spec₁`, `spec₁ ≤ spec₂`, and `C.π` is monotone, then
    `s` also satisfies `C.Verified s spec₂`.

    In particular, proving `C.Verified s spec` for any specification `spec` that
    refines `L_src.WellFormedOn pre` immediately yields the baseline safety
    obligation `C.Verified s (L_src.WellFormedOn pre)`. -/
theorem Compiler.Verified.mono
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {spec₁ spec₂ : L_src.Behavior}
    (h_ver : C.Verified s spec₁)
    (h_le : spec₁ ≤ spec₂)
    (h_mono : Monotone C.π) :
    C.Verified s spec₂ :=
  ⟨Preorder.le_trans h_ver.1 h_le,
   h_ver.2.1,
   Preorder.le_trans h_ver.2.2 (h_mono h_le)⟩

/-- Combine a proof of `C.Verified s spec` with `spec ≤ L_src.WellFormedOn pre`
    to discharge `AllHold ((L_src.WellFormedOn pre :: [spec]).map (C.Verified
    s))`
    in `VerificationResultOn`. -/
theorem Compiler.Verified.with_wellFormedOn
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {pre : L_src.Query → Prop} {spec : L_src.Behavior}
    (h_ver : C.Verified s spec)
    (h_wf : spec ≤ L_src.WellFormedOn pre)
    (h_mono : Monotone C.π) :
    AllHold ((L_src.WellFormedOn pre :: [spec]).map (C.Verified s)) :=
  ⟨Compiler.Verified.mono h_ver h_wf h_mono, h_ver, True.intro⟩


/-- Every state of program `p` has at least one step outcome. -/
def TotalStep (M : SmallStepMachine Prog State Obs Val) : Prop :=
  ∀ (p : Prog) (s : State), ∃ r, M.step p s r

/-- Every reachable choice node has at least one enabled branch, preventing an
    empty choice predicate from collapsing `ReachesPrefix`. -/
def InhabitedDemonic (M : SmallStepMachine Prog State Obs Val) : Prop :=
  ∀ (p : Prog) (s : State) (kind : ChoiceKind) (branches : State → Prop),
    M.step p s (.choice kind branches) → ∃ s', branches s'

/-- Constructive prefix existence at every step budget `n : Nat` from any
    starting state `s`. -/
theorem exists_reaches_prefix
    {M : SmallStepMachine Prog State Obs Val}
    (h_tot : TotalStep M)
    (h_dem : InhabitedDemonic M)
    (p : Prog) (init : State) (n : Nat) :
    ∀ (s : State),
      ∃ tr out, ReachesPrefix M p init n s tr out ∧ out ≠ .stuck := by
  induction n with
  | zero =>
    intro s
    exact ⟨[], .running, ReachesPrefix.zero s, by intro h; cases h⟩
  | succ k ih =>
    intro s
    cases h_tot p s with
    | intro r hstep =>
      cases r with
      | step obs s' =>
        cases ih s' with
        | intro tr hrest =>
          cases hrest with
          | intro out hpair =>
            exact ⟨obs :: tr, out,
              ReachesPrefix.step k s s' obs tr out hstep hpair.1,
              hpair.2⟩
      | choice kind branches =>
        cases h_dem p s kind branches hstep with
        | intro s' hbranch =>
          cases ih s' with
          | intro tr hrest =>
            cases hrest with
            | intro out hpair =>
              exact ⟨tr, out,
                ReachesPrefix.choice k kind s s' branches tr out hstep hbranch hpair.1,
                hpair.2⟩
      | terminated term =>
        exact ⟨[], .terminated term,
          ReachesPrefix.terminated k s term hstep,
          by intro h; cases h⟩
      | failed err =>
        exact ⟨[], .failed err,
          ReachesPrefix.failed k s err hstep,
          by intro h; cases h⟩

/-- Structural non-vacuity at every finite step depth `n : Nat`:
    given `TotalStep M`, `InhabitedDemonic M`, and an initial state `init` of
    `p`, there exists a reachable execution output `out : ExecOut Obs Val` at
    query `⟨init, n⟩` whose outcome is not `.stuck`. -/
theorem non_vacuity_at_every_depth
    {M : SmallStepMachine Prog State Obs Val}
    (h_tot : TotalStep M)
    (h_dem : InhabitedDemonic M)
    (p : Prog) (init : State)
    (h_init : M.initState p init)
    (n : Nat) :
    ∃ out : ExecOut Obs Val,
      M.initState p init ∧
      ReachesPrefix M p init n init out.trace out.outcome ∧
      out.outcome ≠ .stuck := by
  cases exists_reaches_prefix h_tot h_dem p init n init with
  | intro tr hrest =>
    cases hrest with
    | intro oc hpair =>
      refine ⟨{ trace := tr, outcome := oc }, ?_⟩
      exact ⟨h_init, hpair.1, hpair.2⟩

/-- Refining `(M.toLanguage).WellFormed` unfolds to `out.isSafe` across every
    initial state `init`, step budget `steps`, trace `tr`, and outcome `out`. -/
theorem behaviorOf_le_wellFormed_iff
    {M : SmallStepMachine Prog State Obs Val} {p : Prog} :
    BehaviorOf M p ≤ (M.toLanguage).WellFormed ↔
      ∀ init steps tr out,
        M.initState p init →
        ReachesPrefix M p init steps init tr out →
        out.isSafe := by
  constructor
  · intro h init steps tr out hinit hreach
    have hdef := (le_wellFormed_iff (L := M.toLanguage) (BehaviorOf M p)).mp h
      { init := init, steps := steps }
    exact hdef hinit tr out hreach
  · intro h
    refine (le_wellFormed_iff (L := M.toLanguage) (BehaviorOf M p)).mpr ?_
    intro q hinit tr out hreach
    exact h q.init q.steps tr out hinit hreach

/-- Bridge lemma for establishing `BehaviorOf M p ≤ (M.toLanguage).SpecOn pre
    Post`:
    it suffices to show that at every query `q` satisfying `pre q`, every
    reachable prefix `(q, out)` has a safe outcome (`out.outcome.isSafe`) and
    satisfies the functional postcondition `Post q out`. -/
theorem behaviorOf_le_specOn
    {M : SmallStepMachine Prog State Obs Val} {p : Prog}
    {pre : ExecQuery State → Prop}
    {Post : ExecQuery State → ExecOut Obs Val → Prop}
    (h : ∀ (q : ExecQuery State) (out : ExecOut Obs Val),
      pre q →
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome →
      out.outcome.isSafe ∧ Post q out) :
    BehaviorOf M p ≤ (M.toLanguage).SpecOn pre Post := by
  intro q hpre
  refine ⟨fun hinit tr oc hreach => (h q ⟨tr, oc⟩ hpre ⟨hinit, hreach⟩).1, ?_⟩
  intro out hval
  exact (h q out hpre hval).2

/-- Bridge lemma for establishing `BehaviorOf M p ≤ (M.toLanguage).Spec Post`:
    it suffices to show that every reachable prefix `(q, out)` has a safe
    outcome (`out.outcome.isSafe`) and satisfies the functional postcondition
    `Post q out`. -/
theorem behaviorOf_le_spec
    {M : SmallStepMachine Prog State Obs Val} {p : Prog}
    {Post : ExecQuery State → ExecOut Obs Val → Prop}
    (h : ∀ (q : ExecQuery State) (out : ExecOut Obs Val),
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome →
      out.outcome.isSafe ∧ Post q out) :
    BehaviorOf M p ≤ (M.toLanguage).Spec Post :=
  behaviorOf_le_specOn (fun q out _ hpfx => h q out hpfx)

/-- Bridge lemma for establishing `BehaviorOf M p ≤ (fun q => Partial.pure (Post
    q))`:
    specialization of `behaviorOf_le_spec` (since `M.toLanguage.Spec Post` is
    definitionally `fun q => Partial.pure (Post q)`). -/
theorem behaviorOf_le_pure
    {M : SmallStepMachine Prog State Obs Val} {p : Prog}
    {Post : ExecQuery State → ExecOut Obs Val → Prop}
    (h : ∀ (q : ExecQuery State) (out : ExecOut Obs Val),
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome →
      out.outcome.isSafe ∧ Post q out) :
    BehaviorOf M p ≤ (fun q => Partial.pure (Post q)) :=
  behaviorOf_le_spec h


/-!
## 1. View Partial Order and Non-Atomic Ownership Helpers (`OwnLoc`)
-/

/-- When `a ≤ b`, `max a b = b`. -/
theorem nat_max_eq_right {a b : Nat} (h : a ≤ b) : max a b = b :=
  Anneal.nat_max_eq_right h

/-- When `¬ a ≤ b`, `max a b = a`. -/
theorem nat_max_eq_left {a b : Nat} (h : ¬ a ≤ b) : max a b = a :=
  Anneal.nat_max_eq_left h

/-- Left upper-bound property of `max` on `Nat` (`a ≤ max a b`). -/
theorem nat_le_max_left (a b : Nat) : a ≤ max a b :=
  if h : a ≤ b then by
    rw [nat_max_eq_right h]
    exact h
  else by
    rw [nat_max_eq_left h]
    exact Nat.le_refl a

/-- Right upper-bound property of `max` on `Nat` (`b ≤ max a b`). -/
theorem nat_le_max_right (a b : Nat) : b ≤ max a b :=
  if h : a ≤ b then by
    rw [nat_max_eq_right h]
    exact Nat.le_refl b
  else by
    rw [nat_max_eq_left h]
    exact Nat.le_of_not_le h

/-- Bumping a coherence view at `(loc, ts)` is inflationary in `Preorder View`
    (`v ≤ View.bump v loc ts`). -/
theorem View.le_bump (v : View) (loc : Nat) (ts : Timestamp) :
    v ≤ View.bump v loc ts := by
  intro l
  unfold View.bump
  cases l == loc with
  | false => exact Nat.le_refl _
  | true => exact nat_le_max_left (v l) ts

/-- Left upper-bound property of `View.join` in `Preorder View`
    (`v₁ ≤ View.join v₁ v₂`). -/
theorem View.le_join_left (v₁ v₂ : View) :
    v₁ ≤ View.join v₁ v₂ :=
  fun l => nat_le_max_left (v₁ l) (v₂ l)

/-- Right upper-bound property of `View.join` in `Preorder View`
    (`v₂ ≤ View.join v₁ v₂`). -/
theorem View.le_join_right (v₁ v₂ : View) :
    v₂ ≤ View.join v₁ v₂ :=
  fun l => nat_le_max_right (v₁ l) (v₂ l)

/-- Any atomic load (`.relaxed` or `.acquire`) monotonically advances the
    active thread's coherence view in `Preorder View`
    (`m.curView ≤ (m.applyAtomicLoad ord msg).curView`). -/
theorem applyAtomicLoad_curView_mono (m : MemState) (ord : AtomicOrdering) (msg : AtomicMsg) :
    m.curView ≤ (m.applyAtomicLoad ord msg).curView := by
  cases ord with
  | relaxed =>
    exact View.le_bump m.curView msg.loc msg.ts
  | acquire =>
    exact Preorder.le_trans
      (View.le_bump m.curView msg.loc msg.ts)
      (View.le_join_left (View.bump m.curView msg.loc msg.ts) msg.relView)

/-- Single-threaded / lock-synchronized non-atomic ownership predicate:
    non-atomic location `loc` holds initialized value `v`, and its last write
    and read timestamps are both visible in the active thread's `curView`. -/
def OwnLoc (m : MemState) (loc : Nat) (v : MirVal) : Prop :=
  m.naVal loc = some v ∧
  m.naWriteTs loc ≤ m.curView loc ∧
  m.naReadTs loc ≤ m.curView loc

/-- Read-only shared non-atomic ownership predicate (`&usize`):
    non-atomic location `loc` holds initialized value `v`, and its last write
    timestamp is visible in the active thread's `curView` (permitting arbitrary
    aliasing reads at `loc`). -/
def ReadOwnLoc (m : MemState) (loc : Nat) (v : MirVal) : Prop :=
  m.naVal loc = some v ∧
  m.naWriteTs loc ≤ m.curView loc

/-- Under `ReadOwnLoc m loc v`, a non-atomic read at `loc` is completely
    deterministic, never triggers a data-race failure, and returns `v`. -/
theorem ReadOwnLoc.readNA_eq {m : MemState} {loc : Nat} {v : MirVal}
    (hRead : ReadOwnLoc m loc v) :
    m.readNA loc =
      some (v, { m with naReadTs := View.bump m.naReadTs loc (m.curView loc) }) := by
  unfold MemState.readNA
  have hdec : decide (m.naWriteTs loc ≤ m.curView loc) = true :=
    decide_eq_true hRead.2
  rw [hdec, hRead.1]
  rfl

/-- Performing a non-atomic read at `loc` preserves `ReadOwnLoc` at every
    shared location `loc'` (both `loc' = loc` and `loc' ≠ loc`). -/
theorem ReadOwnLoc.readNA_preserves {m : MemState} {loc loc' : Nat} {v' : MirVal}
    (hRead' : ReadOwnLoc m loc' v') :
    ReadOwnLoc { m with naReadTs := View.bump m.naReadTs loc (m.curView loc) } loc' v' :=
  hRead'

/-- Under `OwnLoc m loc v`, a non-atomic read at `loc` is completely
    deterministic, never triggers a data-race failure, and returns `v`. -/
theorem OwnLoc.readNA_eq {m : MemState} {loc : Nat} {v : MirVal}
    (hOwn : OwnLoc m loc v) :
    m.readNA loc =
      some (v, { m with naReadTs := View.bump m.naReadTs loc (m.curView loc) }) :=
  ReadOwnLoc.readNA_eq ⟨hOwn.1, hOwn.2.1⟩

/-- Performing a non-atomic read at `loc` preserves `OwnLoc` at every owned
    location `loc'` (both `loc' = loc` and `loc' ≠ loc`). -/
theorem OwnLoc.readNA_preserves {m : MemState} {loc loc' : Nat} {v' : MirVal}
    (hOwn' : OwnLoc m loc' v') :
    OwnLoc { m with naReadTs := View.bump m.naReadTs loc (m.curView loc) } loc' v' := by
  refine ⟨hOwn'.1, hOwn'.2.1, ?_⟩
  dsimp [View.bump]
  cases hbeq : (loc' == loc) with
  | false => exact hOwn'.2.2
  | true =>
    have heq : loc' = loc := of_decide_eq_true hbeq
    subst heq
    rw [nat_max_eq_right hOwn'.2.2]
    exact Nat.le_refl _

/-- Memory state resulting from a successful non-atomic write `m.writeNA loc
    v`. -/
def afterWriteNA (m : MemState) (loc : Nat) (v : MirVal) : MemState :=
  let nextTs := m.curView loc + 1
  { m with
    curView := View.bump m.curView loc nextTs
    naVal := fun l => if l == loc then some v else m.naVal l
    naWriteTs := View.bump m.naWriteTs loc nextTs
    naReadTs := View.bump m.naReadTs loc nextTs }

/-- Under `OwnLoc m loc v`, a non-atomic write `m.writeNA loc vNew` succeeds
    deterministically without data-race failure and produces
    `afterWriteNA m loc vNew`. -/
theorem OwnLoc.writeNA_eq {m : MemState} {loc : Nat} {v : MirVal}
    (hOwn : OwnLoc m loc v) (vNew : MirVal) :
    m.writeNA loc vNew = some (afterWriteNA m loc vNew) := by
  unfold MemState.writeNA afterWriteNA
  have hw : decide (m.naWriteTs loc ≤ m.curView loc) = true :=
    decide_eq_true hOwn.2.1
  have hr : decide (m.naReadTs loc ≤ m.curView loc) = true :=
    decide_eq_true hOwn.2.2
  rw [hw, hr]
  rfl

/-- After writing `vNew` to an owned location `loc`, `OwnLoc` holds at `loc`
    with the updated value `vNew`. -/
theorem OwnLoc.afterWriteNA_self {m : MemState} {loc : Nat} {v : MirVal}
    (hOwn : OwnLoc m loc v) (vNew : MirVal) :
    OwnLoc (afterWriteNA m loc vNew) loc vNew := by
  have hbeq : (loc == loc) = true := decide_eq_true rfl
  have hcur : max (m.curView loc) (m.curView loc + 1) = m.curView loc + 1 :=
    nat_max_eq_right (Nat.le_succ (m.curView loc))
  have hw : max (m.naWriteTs loc) (m.curView loc + 1) = m.curView loc + 1 :=
    nat_max_eq_right (Nat.le_trans hOwn.2.1 (Nat.le_succ (m.curView loc)))
  have hr : max (m.naReadTs loc) (m.curView loc + 1) = m.curView loc + 1 :=
    nat_max_eq_right (Nat.le_trans hOwn.2.2 (Nat.le_succ (m.curView loc)))
  unfold OwnLoc afterWriteNA View.bump
  dsimp
  rw [hbeq, hcur, hw, hr]
  exact ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩

/-- Writing `vNew` to `loc` preserves `OwnLoc` at every other location
    `loc' ≠ loc`. -/
theorem OwnLoc.afterWriteNA_other {m : MemState} {loc loc' : Nat} {v' : MirVal}
    (hne : loc' ≠ loc) (hOwn' : OwnLoc m loc' v') (vNew : MirVal) :
    OwnLoc (afterWriteNA m loc vNew) loc' v' := by
  have hbeq : (loc' == loc) = false := decide_eq_false hne
  unfold OwnLoc afterWriteNA View.bump
  dsimp
  rw [hbeq]
  exact hOwn'

/-- Writing `vNew` to `loc` preserves `ReadOwnLoc` at every other location
    `loc' ≠ loc`. -/
theorem ReadOwnLoc.afterWriteNA_other {m : MemState} {loc loc' : Nat} {v' : MirVal}
    (hne : loc' ≠ loc) (hRead' : ReadOwnLoc m loc' v') (vNew : MirVal) :
    ReadOwnLoc (afterWriteNA m loc vNew) loc' v' := by
  have hbeq : (loc' == loc) = false := decide_eq_false hne
  unfold ReadOwnLoc afterWriteNA View.bump
  dsimp
  rw [hbeq]
  exact hRead'

/-- `OwnLoc` is preserved whenever the thread's coherence view advances in
    `Preorder View` (`m.curView ≤ v'`) without concurrent modification to
    `loc`. -/
theorem OwnLoc.mono_view {m : MemState} {loc : Nat} {v : MirVal} {v' : View}
    (hOwn : OwnLoc m loc v) (hle : m.curView ≤ v') :
    OwnLoc { m with curView := v' } loc v :=
  ⟨hOwn.1, Nat.le_trans hOwn.2.1 (hle loc), Nat.le_trans hOwn.2.2 (hle loc)⟩

/-- Any atomic load preserves `OwnLoc` on non-atomic locations. -/
theorem OwnLoc.preserved_by_atomic_load {m : MemState} {loc : Nat} {v : MirVal}
    (ord : AtomicOrdering) (msg : AtomicMsg) (hOwn : OwnLoc m loc v) :
    OwnLoc (m.applyAtomicLoad ord msg) loc v := by
  have hmono := applyAtomicLoad_curView_mono m ord msg
  cases ord with
  | relaxed => exact OwnLoc.mono_view hOwn hmono
  | acquire => exact OwnLoc.mono_view hOwn hmono

/-- Release-Acquire ownership transfer (e.g., across a `Mutex` unlock/lock): if
    a `Release` message `msg` captured a view `msg.relView` that dominates
    `loc`'s non-atomic write/read timestamps, performing an `Acquire` load of
    `msg` establishes `OwnLoc` in the acquiring thread. -/
theorem OwnLoc.transfer_acquire {m : MemState} {loc : Nat} {v : MirVal}
    (msg : AtomicMsg)
    (hVal : m.naVal loc = some v)
    (hWrite : m.naWriteTs loc ≤ msg.relView loc)
    (hRead : m.naReadTs loc ≤ msg.relView loc) :
    OwnLoc (m.applyAtomicLoad .acquire msg) loc v := by
  have hjoin := View.le_join_right (View.bump m.curView msg.loc msg.ts) msg.relView loc
  exact ⟨hVal, Nat.le_trans hWrite hjoin, Nat.le_trans hRead hjoin⟩

/-!
## 2. Structural Non-Vacuity (`TotalStep` and `InhabitedDemonic`)
-/

/-- `MirMachine` is total: every `(body, s)` pair steps to `evalMirStep body
    s`. -/
theorem mirMachine_total : TotalStep MirMachine :=
  fun body s => ⟨evalMirStep body s, rfl⟩

theorem evalMirStmt_not_choice (s : MirState) (stmt : Stmt)
    (kind : ChoiceKind) (branches : MirState → Prop) :
    StepResult.choice kind branches ≠ evalMirStmt s stmt := by
  cases stmt with
  | assign dst rv =>
    cases rv with
    | use op =>
      dsimp [evalMirStmt]
      cases evalOperand s.locals op with
      | none => intro h; cases h
      | some p => intro h; cases h
    | deref src =>
      dsimp [evalMirStmt]
      cases s.locals src.index with
      | none => intro h; cases h
      | some v =>
        cases v with
        | refMutLoc loc | refSharedLoc loc =>
          dsimp
          cases s.mem.readNA loc with
          | none => intro h; cases h
          | some p => intro h; cases h
        | usize _ | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | ordering _ =>
          intro h; cases h
    | binaryOp op lhs rhs =>
      dsimp [evalMirStmt]
      cases evalOperand s.locals lhs with
      | none => intro h; cases h
      | some p1 =>
        cases p1 with
        | mk v1 locals1 =>
          dsimp
          cases evalOperand locals1 rhs with
          | none => intro h; cases h
          | some p2 =>
            cases p2 with
            | mk v2 locals2 =>
              dsimp
              cases evalBinOp op v1 v2 with
              | none => intro h; cases h
              | some res => intro h; cases h
    | checkedBinaryOp op lhs rhs =>
      dsimp [evalMirStmt]
      cases evalOperand s.locals lhs with
      | none => intro h; cases h
      | some p1 =>
        cases p1 with
        | mk v1 locals1 =>
          dsimp
          cases evalOperand locals1 rhs with
          | none => intro h; cases h
          | some p2 =>
            cases p2 with
            | mk v2 locals2 =>
              dsimp
              cases evalCheckedBinOp op v1 v2 with
              | none => intro h; cases h
              | some res => intro h; cases h
    | proj0 src =>
      dsimp [evalMirStmt]
      cases s.locals src.index with
      | none => intro h; cases h
      | some v =>
        cases v <;> intro h <;> cases h
    | proj1 src =>
      dsimp [evalMirStmt]
      cases s.locals src.index with
      | none => intro h; cases h
      | some v =>
        cases v <;> intro h <;> cases h
  | assignDeref dst op =>
    dsimp [evalMirStmt]
    cases evalOperand s.locals op with
    | none => intro h; cases h
    | some p1 =>
      cases p1 with
      | mk v locals1 =>
        dsimp
        cases locals1 dst.index with
        | none => intro h; cases h
        | some dv =>
          cases dv with
          | refMutLoc loc =>
            dsimp
            cases s.mem.writeNA loc v with
            | none => intro h; cases h
            | some m' => intro h; cases h
          | usize _ | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | ordering _ =>
            intro h; cases h
  | storageLive loc => intro h; cases h
  | storageDead loc => intro h; cases h
  | nop => intro h; cases h

theorem evalMirTerminator_choice_inhabited (s : MirState) (term : Terminator)
    (kind : ChoiceKind) (branches : MirState → Prop) :
    StepResult.choice kind branches = evalMirTerminator s term →
    ∃ s', branches s' := by
  cases term with
  | return_ =>
    dsimp [evalMirTerminator]
    cases s.locals 0 with
    | none => intro h; cases h
    | some v => intro h; cases h
  | goto target => intro h; cases h
  | unreachable => intro h; cases h
  | callPure2 dst callee arg1 arg2 target =>
    dsimp [evalMirTerminator]
    cases evalOperand s.locals arg1 with
    | none => intro h; cases h
    | some p1 =>
      cases p1 with
      | mk v1 locals1 =>
        dsimp
        cases evalOperand locals1 arg2 with
        | none => intro h; cases h
        | some p2 =>
          cases p2 with
          | mk v2 locals2 =>
            dsimp
            cases evalPureCallee2 callee v1 v2 with
            | none => intro h; cases h
            | some res => intro h; cases h
  | switchInt discr falseTarget trueTarget =>
    dsimp [evalMirTerminator]
    cases evalOperand s.locals discr with
    | none => intro h; cases h
    | some p =>
      cases p with
      | mk v locals' =>
        cases v with
        | bool b =>
          cases b with
          | false => intro h; cases h
          | true => intro h; cases h
        | usize _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ =>
          intro h; cases h
  | assertNotOverflow tupleLocal target =>
    dsimp [evalMirTerminator]
    cases s.locals tupleLocal.index with
    | none => intro h; cases h
    | some v =>
      cases v with
      | tupleUsizeBool _ ov =>
        cases ov <;> intro h <;> cases h
      | usize _ | bool _ | unit | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ =>
        intro h; cases h
  | callAtomicLoad dst ptrOp ordOp target =>
    dsimp [evalMirTerminator]
    cases evalOperand s.locals ptrOp with
    | none => intro h; cases h
    | some p1 =>
      cases p1 with
      | mk ptrVal locals1 =>
        dsimp
        cases evalOperand locals1 ordOp with
        | none => intro h; cases h
        | some p2 =>
          cases p2 with
          | mk ordVal locals2 =>
            dsimp
            cases ptrVal with
            | usize _ => intro h; cases h
            | bool _ => intro h; cases h
            | unit => intro h; cases h
            | tupleUsizeBool _ _ => intro h; cases h
            | refSharedLoc _ => intro h; cases h
            | refMutLoc _ => intro h; cases h
            | ordering _ => intro h; cases h
            | atomicLoc loc =>
              cases ordVal with
              | usize _ => intro h; cases h
              | bool _ => intro h; cases h
              | unit => intro h; cases h
              | tupleUsizeBool _ _ => intro h; cases h
              | atomicLoc _ => intro h; cases h
              | refSharedLoc _ => intro h; cases h
              | refMutLoc _ => intro h; cases h
              | ordering ord =>
                dsimp
                cases s.mem.visibleAtomicMsgs loc with
                | nil => intro h; cases h
                | cons head tail =>
                  intro h
                  injection h with _ hbranches
                  subst hbranches
                  refine ⟨{
                    locals := updateLocal locals2 dst.index (some (.usize head.bits))
                    mem := s.mem.applyAtomicLoad ord head
                    block := target.index
                    stmtIdx := 0
                  }, ?_⟩
                  exact ⟨head, List.Mem.head tail, rfl⟩

/-- `MirMachine` has no empty choice nodes: whenever `evalMirStep` emits
    `.choice`, `visibleAtomicMsgs` is of the form `head :: tail`, so `head`
    provides an inhabited transition branch. -/
theorem mirMachine_inhabited : InhabitedDemonic MirMachine := by
  intro body s kind branches hstep
  have h : StepResult.choice kind branches = evalMirStep body s := hstep
  dsimp [evalMirStep] at h
  revert h
  cases body.blocks[s.block]? with
  | none => intro h; cases h
  | some bb =>
    intro h
    dsimp at h
    revert h
    cases bb.stmts[s.stmtIdx]? with
    | none =>
      intro h
      exact evalMirTerminator_choice_inhabited s bb.terminator kind branches h
    | some stmt =>
      intro h
      exact False.elim (evalMirStmt_not_choice s stmt kind branches h)

/-!
## 3. Verification Lemmas for `pub fn id` and `pub fn load_relaxed`
-/

/-- Postcondition `EnsuresEqArg argLocal` refines `MirLang.WellFormed`. -/
theorem ensuresEqArg_le_wellFormed (argLocal : Nat) :
    EnsuresEqArg argLocal ≤ MirLang.WellFormed :=
  spec_le_wellFormed _

/-- Postcondition `EnsuresAtomicLoad argLocal` refines `MirLang.WellFormed`. -/
theorem ensuresAtomicLoad_le_wellFormed (argLocal : Nat) :
    EnsuresAtomicLoad argLocal ≤ MirLang.WellFormed :=
  spec_le_wellFormed _

/-- Canonical `Runtime(PostCleanup)` MIR body for `pub fn id(x: usize) -> usize
    { x }`
    using `Operand.copy`:
    ```text
    bb0: {
        _0 = copy _1;
        return;
    }
    ``` -/
def idCopyBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.assign ⟨0⟩ (.use (.copy ⟨1⟩))]
      terminator := .return_ }
  ]

/-- Canonical `Runtime(PostCleanup)` MIR body for `pub fn id(x: usize) -> usize
    { x }`
    using `Operand.move`:
    ```text
    bb0: {
        _0 = move _1;
        return;
    }
    ``` -/
def idMoveBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.assign ⟨0⟩ (.use (.move ⟨1⟩))]
      terminator := .return_ }
  ]

/-- `idCopyBody` satisfies `EnsuresEqArg 1`: every reachable prefix is safe and
    any normal return value equals the initial value of `_1`. -/
theorem idCopyBody_satisfies_ensures :
    MirSem idCopyBody ≤ EnsuresEqArg 1 := by
  refine behaviorOf_le_pure (M := MirMachine) ?_
  intro q out hpfx
  cases q with
  | mk init steps =>
  cases out with
  | mk trace outcome =>
    have hinit := hpfx.1
    have hreach := hpfx.2
    have hb : init.block = 0 := hinit.1
    have hs : init.stmtIdx = 0 := hinit.2.1
    have harg : ∃ v, init.locals 1 = some v ∧ v.hasTy init.mem .usize :=
      hinit.2.2.2.1
    cases harg with
    | intro v hv =>
      have hv1 : init.locals 1 = some v := hv.1
      have hstep0 :
          evalMirStep idCopyBody init =
            StepResult.step () { init with
              locals := updateLocal init.locals 0 (some v)
              block := 0
              stmtIdx := 1
            } := by
        unfold evalMirStep idCopyBody
        rw [hb, hs]
        change (match evalOperand init.locals (.copy ⟨1⟩) with
          | some (v, locals') => StepResult.step (State := MirState) (Obs := Unit) (Val := MirVal) () { init with
              locals := updateLocal locals' 0 (some v)
              stmtIdx := init.stmtIdx + 1
            }
          | none => StepResult.failed FailureKind.ub) = _
        dsimp [evalOperand]
        rw [hv1, hb, hs]
      cases hreach with
      | zero =>
        exact ⟨True.intro, fun _ h => by cases h⟩
      | step n _ s' obs tr out h1 h2 =>
        have h1' : StepResult.step obs s' = evalMirStep idCopyBody init := h1
        rw [hstep0] at h1'
        injection h1' with _ hs'
        subst hs'
        have hstep1 :
            evalMirStep idCopyBody { init with
              locals := updateLocal init.locals 0 (some v)
              block := 0
              stmtIdx := 1
            } = StepResult.terminated (TerminationKind.normal v) := by
          rfl
        cases h2 with
        | zero =>
          exact ⟨True.intro, fun _ h => by cases h⟩
        | step _ _ _ _ _ _ hstep_bad _ =>
          have hbad : _ = evalMirStep idCopyBody _ := hstep_bad
          rw [hstep1] at hbad
          cases hbad
        | choice _ _ _ _ _ _ _ hstep_bad _ _ =>
          have hbad : _ = evalMirStep idCopyBody _ := hstep_bad
          rw [hstep1] at hbad
          cases hbad
        | emptyChoice _ _ _ _ hstep_bad _ =>
          have hbad : _ = evalMirStep idCopyBody _ := hstep_bad
          rw [hstep1] at hbad
          cases hbad
        | terminated _ _ term hterm =>
          have hterm' : StepResult.terminated term = evalMirStep idCopyBody _ := hterm
          rw [hstep1] at hterm'
          injection hterm' with hterm_eq
          subst hterm_eq
          refine ⟨True.intro, ?_⟩
          intro ret hret
          injection hret with hterm_ret
          injection hterm_ret with hret_eq
          subst hret_eq
          exact hv1
        | failed _ _ err hfail =>
          have hbad : _ = evalMirStep idCopyBody _ := hfail
          rw [hstep1] at hbad
          cases hbad
        | noStep _ _ hnostep =>
          exact False.elim (hnostep ⟨_, hstep1.symm⟩)
      | choice _ _ _ _ _ _ _ h1 _ _ =>
        have h1' : _ = evalMirStep idCopyBody init := h1
        rw [hstep0] at h1'
        cases h1'
      | emptyChoice _ _ _ _ h1 _ =>
        have h1' : _ = evalMirStep idCopyBody init := h1
        rw [hstep0] at h1'
        cases h1'
      | terminated _ _ _ h1 =>
        have h1' : _ = evalMirStep idCopyBody init := h1
        rw [hstep0] at h1'
        cases h1'
      | failed _ _ _ h1 =>
        have h1' : _ = evalMirStep idCopyBody init := h1
        rw [hstep0] at h1'
        cases h1'
      | noStep _ _ hnostep =>
        exact False.elim (hnostep ⟨_, hstep0.symm⟩)

/-- `idCopyBody` satisfies baseline `MirLang.WellFormed`. -/
theorem idCopyBody_satisfies_wellFormed :
    MirSem idCopyBody ≤ MirLang.WellFormed :=
  Preorder.le_trans idCopyBody_satisfies_ensures (ensuresEqArg_le_wellFormed 1)

/-- `idMoveBody` satisfies `EnsuresEqArg 1`: every reachable prefix is safe and
    any normal return value equals the initial value of `_1`. -/
theorem idMoveBody_satisfies_ensures :
    MirSem idMoveBody ≤ EnsuresEqArg 1 := by
  refine behaviorOf_le_pure (M := MirMachine) ?_
  intro q out hpfx
  cases q with
  | mk init steps =>
  cases out with
  | mk trace outcome =>
    have hinit := hpfx.1
    have hreach := hpfx.2
    have hb : init.block = 0 := hinit.1
    have hs : init.stmtIdx = 0 := hinit.2.1
    have harg : ∃ v, init.locals 1 = some v ∧ v.hasTy init.mem .usize :=
      hinit.2.2.2.1
    cases harg with
    | intro v hv =>
      have hv1 : init.locals 1 = some v := hv.1
      have hstep0 :
          evalMirStep idMoveBody init =
            StepResult.step () { init with
              locals := updateLocal (updateLocal init.locals 1 none) 0 (some v)
              block := 0
              stmtIdx := 1
            } := by
        unfold evalMirStep idMoveBody
        rw [hb, hs]
        change (match evalOperand init.locals (.move ⟨1⟩) with
          | some (v, locals') => StepResult.step (State := MirState) (Obs := Unit) (Val := MirVal) () { init with
              locals := updateLocal locals' 0 (some v)
              stmtIdx := init.stmtIdx + 1
            }
          | none => StepResult.failed FailureKind.ub) = _
        dsimp [evalOperand]
        rw [hv1, hb, hs]
      cases hreach with
      | zero =>
        exact ⟨True.intro, fun _ h => by cases h⟩
      | step n _ s' obs tr out h1 h2 =>
        have h1' : StepResult.step obs s' = evalMirStep idMoveBody init := h1
        rw [hstep0] at h1'
        injection h1' with _ hs'
        subst hs'
        have hstep1 :
            evalMirStep idMoveBody { init with
              locals := updateLocal (updateLocal init.locals 1 none) 0 (some v)
              block := 0
              stmtIdx := 1
            } = StepResult.terminated (TerminationKind.normal v) := by
          rfl
        cases h2 with
        | zero =>
          exact ⟨True.intro, fun _ h => by cases h⟩
        | step _ _ _ _ _ _ hstep_bad _ =>
          have hbad : _ = evalMirStep idMoveBody _ := hstep_bad
          rw [hstep1] at hbad
          cases hbad
        | choice _ _ _ _ _ _ _ hstep_bad _ _ =>
          have hbad : _ = evalMirStep idMoveBody _ := hstep_bad
          rw [hstep1] at hbad
          cases hbad
        | emptyChoice _ _ _ _ hstep_bad _ =>
          have hbad : _ = evalMirStep idMoveBody _ := hstep_bad
          rw [hstep1] at hbad
          cases hbad
        | terminated _ _ term hterm =>
          have hterm' : StepResult.terminated term = evalMirStep idMoveBody _ := hterm
          rw [hstep1] at hterm'
          injection hterm' with hterm_eq
          subst hterm_eq
          refine ⟨True.intro, ?_⟩
          intro ret hret
          injection hret with hterm_ret
          injection hterm_ret with hret_eq
          subst hret_eq
          exact hv1
        | failed _ _ err hfail =>
          have hbad : _ = evalMirStep idMoveBody _ := hfail
          rw [hstep1] at hbad
          cases hbad
        | noStep _ _ hnostep =>
          exact False.elim (hnostep ⟨_, hstep1.symm⟩)
      | choice _ _ _ _ _ _ _ h1 _ _ =>
        have h1' : _ = evalMirStep idMoveBody init := h1
        rw [hstep0] at h1'
        cases h1'
      | emptyChoice _ _ _ _ h1 _ =>
        have h1' : _ = evalMirStep idMoveBody init := h1
        rw [hstep0] at h1'
        cases h1'
      | terminated _ _ _ h1 =>
        have h1' : _ = evalMirStep idMoveBody init := h1
        rw [hstep0] at h1'
        cases h1'
      | failed _ _ _ h1 =>
        have h1' : _ = evalMirStep idMoveBody init := h1
        rw [hstep0] at h1'
        cases h1'
      | noStep _ _ hnostep =>
        exact False.elim (hnostep ⟨_, hstep0.symm⟩)

/-- `idMoveBody` satisfies baseline `MirLang.WellFormed`. -/
theorem idMoveBody_satisfies_wellFormed :
    MirSem idMoveBody ≤ MirLang.WellFormed :=
  Preorder.le_trans idMoveBody_satisfies_ensures (ensuresEqArg_le_wellFormed 1)

/-- Canonical `Runtime(PostCleanup)` MIR body for
    `pub fn load_relaxed(a: &AtomicUsize) -> usize { a.load(Ordering::Relaxed)
    }`:
    ```text
    bb0: {
        _2 = std::sync::atomic::Ordering::Relaxed;
        _0 = Atomic::<usize>::load(copy _1, move _2) -> [return: bb1, unwind continue];
    }
    bb1: {
        return;
    }
    ``` -/
def loadRelaxedBody : MirBody where
  argTys := [.refAtomicUsize]
  retTy := .usize
  localCount := 3
  blocks := [
    { stmts := [.assign ⟨2⟩ (.use (.constVal (.ordering .relaxed)))]
      terminator := .callAtomicLoad ⟨0⟩ (.copy ⟨1⟩) (.move ⟨2⟩) ⟨1⟩ },
    { stmts := []
      terminator := .return_ }
  ]

/-- `loadRelaxedBody` satisfies `EnsuresAtomicLoad 1`: every reachable prefix
    is safe (including across the demonic weak-memory choice in `bb0`), and any
    normal return value equals `MirVal.usize msg.bits` for some visible message
    `msg ∈ init.mem.visibleAtomicMsgs loc` at `_1`'s atomic location. -/
theorem loadRelaxedBody_satisfies_ensures :
    MirSem loadRelaxedBody ≤ EnsuresAtomicLoad 1 := by
  refine behaviorOf_le_pure (M := MirMachine) ?_
  intro q out hpfx
  cases q with
  | mk init steps =>
  cases out with
  | mk trace outcome =>
    have hinit := hpfx.1
    have hreach := hpfx.2
    have hb : init.block = 0 := hinit.1
    have hs : init.stmtIdx = 0 := hinit.2.1
    have harg : ∃ v, init.locals 1 = some v ∧ v.hasTy init.mem .refAtomicUsize :=
      hinit.2.2.2.1
    cases harg with
    | intro v hv =>
      have hv1 : init.locals 1 = some v := hv.1
      have hty : v.hasTy init.mem .refAtomicUsize := hv.2
      cases v with
      | usize _ => cases hty
      | bool _ => cases hty
      | unit => cases hty
      | tupleUsizeBool _ _ => cases hty
      | refSharedLoc _ => cases hty
      | refMutLoc _ => cases hty
      | ordering _ => cases hty
      | atomicLoc loc =>
        have hvis : init.mem.visibleAtomicMsgs loc ≠ [] := hty
        let s1 : MirState := { init with
          locals := updateLocal init.locals 2 (some (.ordering .relaxed))
          block := 0
          stmtIdx := 1
        }
        have hstep0 : evalMirStep loadRelaxedBody init = StepResult.step () s1 := by
          unfold evalMirStep loadRelaxedBody
          rw [hb, hs]
          change (StepResult.step (State := MirState) (Obs := Unit) (Val := MirVal) () { init with
            locals := updateLocal init.locals 2 (some (.ordering .relaxed))
            stmtIdx := init.stmtIdx + 1
          }) = StepResult.step () s1
          unfold s1
          rw [hb, hs]
        cases hreach with
        | zero =>
          exact ⟨True.intro, fun _ h => by cases h⟩
        | step n _ s1' obs tr out h1 h2 =>
          have h1' : StepResult.step obs s1' = evalMirStep loadRelaxedBody init := h1
          rw [hstep0] at h1'
          injection h1' with _ hs1'
          subst hs1'
          cases hlist : init.mem.visibleAtomicMsgs loc with
          | nil =>
            exact False.elim (hvis hlist)
          | cons head tail =>
            let localsAfterMove := updateLocal (updateLocal init.locals 2 (some (.ordering .relaxed))) 2 none
            let branches : MirState → Prop := fun s' =>
              ∃ msg, msg ∈ (head :: tail) ∧
                s' = {
                  locals := updateLocal localsAfterMove 0 (some (.usize msg.bits))
                  mem := init.mem.applyAtomicLoad .relaxed msg
                  block := 1
                  stmtIdx := 0
                }
            have hptr : evalOperand s1.locals (.copy ⟨1⟩) = some (.atomicLoc loc, s1.locals) := by
              unfold evalOperand s1 updateLocal
              change (match init.locals 1 with | some v => some (v, _) | none => none) = _
              rw [hv1]
            have hstep1 : evalMirStep loadRelaxedBody s1 = StepResult.choice .demonic branches := by
              unfold evalMirStep loadRelaxedBody
              change evalMirTerminator s1 (.callAtomicLoad ⟨0⟩ (.copy ⟨1⟩) (.move ⟨2⟩) ⟨1⟩) = _
              dsimp only [evalMirTerminator]
              rw [hptr]
              change (match init.mem.visibleAtomicMsgs loc with
                | [] => StepResult.failed FailureKind.ub
                | head' :: tail' =>
                  StepResult.choice (State := MirState) (Obs := Unit) (Val := MirVal) .demonic (fun s' =>
                    ∃ msg, msg ∈ (head' :: tail') ∧
                      s' = {
                        locals := updateLocal localsAfterMove 0 (some (.usize msg.bits))
                        mem := init.mem.applyAtomicLoad .relaxed msg
                        block := 1
                        stmtIdx := 0
                      })) = StepResult.choice .demonic branches
              rw [hlist]
            cases h2 with
            | zero =>
              exact ⟨True.intro, fun _ h => by cases h⟩
            | step _ _ _ _ _ _ hbad _ =>
              have hbad' : _ = evalMirStep loadRelaxedBody s1 := hbad
              rw [hstep1] at hbad'
              cases hbad'
            | choice m kind _ s2 brs tr2 out2 hch hbr h3 =>
              have hch' : StepResult.choice kind brs = evalMirStep loadRelaxedBody s1 := hch
              rw [hstep1] at hch'
              injection hch' with _ hbrs
              subst hbrs
              cases hbr with
              | intro msg hmsg =>
                have hmem : msg ∈ head :: tail := hmsg.1
                have hs2 : s2 = {
                    locals := updateLocal localsAfterMove 0 (some (.usize msg.bits))
                    mem := init.mem.applyAtomicLoad .relaxed msg
                    block := 1
                    stmtIdx := 0
                  } := hmsg.2
                subst hs2
                have hstep2 :
                    evalMirStep loadRelaxedBody {
                      locals := updateLocal localsAfterMove 0 (some (.usize msg.bits))
                      mem := init.mem.applyAtomicLoad .relaxed msg
                      block := 1
                      stmtIdx := 0
                    } = StepResult.terminated (TerminationKind.normal (.usize msg.bits)) := by
                  rfl
                cases h3 with
                | zero =>
                  exact ⟨True.intro, fun _ h => by cases h⟩
                | step _ _ _ _ _ _ hbad _ =>
                  have hbad' : _ = evalMirStep loadRelaxedBody _ := hbad
                  rw [hstep2] at hbad'
                  cases hbad'
                | choice _ _ _ _ _ _ _ hbad _ _ =>
                  have hbad' : _ = evalMirStep loadRelaxedBody _ := hbad
                  rw [hstep2] at hbad'
                  cases hbad'
                | emptyChoice _ _ _ _ hbad _ =>
                  have hbad' : _ = evalMirStep loadRelaxedBody _ := hbad
                  rw [hstep2] at hbad'
                  cases hbad'
                | terminated _ _ term hterm =>
                  have hterm' : StepResult.terminated term = evalMirStep loadRelaxedBody _ := hterm
                  rw [hstep2] at hterm'
                  injection hterm' with hterm_eq
                  subst hterm_eq
                  refine ⟨True.intro, ?_⟩
                  intro ret hret
                  injection hret with hterm_ret
                  injection hterm_ret with hret_eq
                  subst hret_eq
                  refine ⟨loc, msg, hv1, ?_, rfl⟩
                  rw [hlist]
                  exact hmem
                | failed _ _ _ hbad =>
                  have hbad' : _ = evalMirStep loadRelaxedBody _ := hbad
                  rw [hstep2] at hbad'
                  cases hbad'
                | noStep _ _ hnostep =>
                  exact False.elim (hnostep ⟨_, hstep2.symm⟩)
            | emptyChoice _ kind _ brs hch hempty =>
              have hch' : StepResult.choice kind brs = evalMirStep loadRelaxedBody s1 := hch
              rw [hstep1] at hch'
              injection hch' with _ hbrs
              subst hbrs
              exact False.elim (hempty ⟨_, ⟨head, List.Mem.head tail, rfl⟩⟩)
            | terminated _ _ _ hbad =>
              have hbad' : _ = evalMirStep loadRelaxedBody s1 := hbad
              rw [hstep1] at hbad'
              cases hbad'
            | failed _ _ _ hbad =>
              have hbad' : _ = evalMirStep loadRelaxedBody s1 := hbad
              rw [hstep1] at hbad'
              cases hbad'
            | noStep _ _ hnostep =>
              exact False.elim (hnostep ⟨_, hstep1.symm⟩)
        | choice _ _ _ _ _ _ _ h1 _ _ =>
          have h1' : _ = evalMirStep loadRelaxedBody init := h1
          rw [hstep0] at h1'
          cases h1'
        | emptyChoice _ _ _ _ h1 _ =>
          have h1' : _ = evalMirStep loadRelaxedBody init := h1
          rw [hstep0] at h1'
          cases h1'
        | terminated _ _ _ h1 =>
          have h1' : _ = evalMirStep loadRelaxedBody init := h1
          rw [hstep0] at h1'
          cases h1'
        | failed _ _ _ h1 =>
          have h1' : _ = evalMirStep loadRelaxedBody init := h1
          rw [hstep0] at h1'
          cases h1'
        | noStep _ _ hnostep =>
          exact False.elim (hnostep ⟨_, hstep0.symm⟩)

/-- `loadRelaxedBody` satisfies baseline `MirLang.WellFormed`. -/
theorem loadRelaxedBody_satisfies_wellFormed :
    MirSem loadRelaxedBody ≤ MirLang.WellFormed :=
  Preorder.le_trans loadRelaxedBody_satisfies_ensures (ensuresAtomicLoad_le_wellFormed 1)

/-- Generic single-function `CrateTheorem` discharge for an unannotated safe
    function (`specs := []`) via `Compiler.SoundOn.verify`: given
    `h_wf : MirSem body ≤ MirLang.WellFormed`, proves `CrateTheorem` for the
    single-function crate containing `(fnName, body)` with TCB entry
    `TCBItem.rustcLowering fnName body`. -/
theorem verify_single_fn_wf_crate
    (fnName : String) (body : MirBody)
    (h_wf : MirSem body ≤ MirLang.WellFormed) :
    CrateTheorem {
      functions := [{ name := fnName, prog := body, specs := [] }]
      tcb := [TCBItem.rustcLowering fnName body]
    } := by
  refine ⟨(by intro h; cases h), ⟨⟨True.intro, True.intro⟩, ?_⟩, True.intro⟩
  intro hAssumptions
  exact ⟨Compiler.SoundOn.verify hAssumptions.1 h_wf, True.intro⟩

/-- Generic single-function `CrateTheorem` discharge via
    `Compiler.SoundOn.verify`
    and `Compiler.Verified.with_wellFormedOn`: given a proof
    `h_proof : MirSem body ≤ spec` and `h_spec_wf : spec ≤ MirLang.WellFormed`,
    proves `CrateTheorem` for the single-function crate containing
    `(fnName, body, [spec])` with TCB entry `TCBItem.rustcLowering fnName
    body`. -/
theorem verify_single_fn_crate
    (fnName : String) (body : MirBody)
    (spec : MirLang.Behavior)
    (h_proof : MirSem body ≤ spec)
    (h_spec_wf : spec ≤ MirLang.WellFormed) :
    CrateTheorem {
      functions := [{ name := fnName, prog := body, specs := [spec] }]
      tcb := [TCBItem.rustcLowering fnName body]
    } := by
  refine ⟨(by intro h; cases h), ⟨⟨True.intro, True.intro⟩, ?_⟩, True.intro⟩
  intro hAssumptions
  exact Compiler.Verified.with_wellFormedOn
    (Compiler.SoundOn.verify hAssumptions.1 h_proof)
    h_spec_wf hAssumptions.1.1

/-- Ready-to-apply `CrateTheorem` witness for `pub fn id` (`Operand.copy`,
    `specs := [EnsuresEqArg 1]`). -/
theorem prove_id_copy_ensures_crate (fnName : String) :
    CrateTheorem {
      functions := [{ name := fnName, prog := idCopyBody, specs := [EnsuresEqArg 1] }]
      tcb := [TCBItem.rustcLowering fnName idCopyBody]
    } :=
  verify_single_fn_crate fnName idCopyBody (EnsuresEqArg 1)
    idCopyBody_satisfies_ensures (ensuresEqArg_le_wellFormed 1)

/-- Ready-to-apply `CrateTheorem` witness for unannotated `pub fn id`
    (`Operand.copy`, `specs := []`). -/
theorem prove_id_copy_wf_crate (fnName : String) :
    CrateTheorem {
      functions := [{ name := fnName, prog := idCopyBody, specs := [] }]
      tcb := [TCBItem.rustcLowering fnName idCopyBody]
    } :=
  verify_single_fn_wf_crate fnName idCopyBody idCopyBody_satisfies_wellFormed

/-- Ready-to-apply `CrateTheorem` witness for `pub fn id` (`Operand.move`,
    `specs := [EnsuresEqArg 1]`). -/
theorem prove_id_move_ensures_crate (fnName : String) :
    CrateTheorem {
      functions := [{ name := fnName, prog := idMoveBody, specs := [EnsuresEqArg 1] }]
      tcb := [TCBItem.rustcLowering fnName idMoveBody]
    } :=
  verify_single_fn_crate fnName idMoveBody (EnsuresEqArg 1)
    idMoveBody_satisfies_ensures (ensuresEqArg_le_wellFormed 1)

/-- Ready-to-apply `CrateTheorem` witness for unannotated `pub fn id`
    (`Operand.move`, `specs := []`). -/
theorem prove_id_move_wf_crate (fnName : String) :
    CrateTheorem {
      functions := [{ name := fnName, prog := idMoveBody, specs := [] }]
      tcb := [TCBItem.rustcLowering fnName idMoveBody]
    } :=
  verify_single_fn_wf_crate fnName idMoveBody idMoveBody_satisfies_wellFormed

/-- Ready-to-apply `CrateTheorem` witness for `pub fn load_relaxed`
    (`specs := [EnsuresAtomicLoad 1]`). -/
theorem prove_load_relaxed_ensures_crate (fnName : String) :
    CrateTheorem {
      functions := [{ name := fnName, prog := loadRelaxedBody, specs := [EnsuresAtomicLoad 1] }]
      tcb := [TCBItem.rustcLowering fnName loadRelaxedBody]
    } :=
  verify_single_fn_crate fnName loadRelaxedBody (EnsuresAtomicLoad 1)
    loadRelaxedBody_satisfies_ensures (ensuresAtomicLoad_le_wellFormed 1)

/-- Ready-to-apply `CrateTheorem` witness for unannotated `pub fn load_relaxed`
    (`specs := []`). -/
theorem prove_load_relaxed_wf_crate (fnName : String) :
    CrateTheorem {
      functions := [{ name := fnName, prog := loadRelaxedBody, specs := [] }]
      tcb := [TCBItem.rustcLowering fnName loadRelaxedBody]
    } :=
  verify_single_fn_wf_crate fnName loadRelaxedBody loadRelaxedBody_satisfies_wellFormed

/-!
## 4. Positive and Negative Rust Adequacy Canaries
-/

/-- Pure infinite loop MIR body (`bb0: { goto -> bb0; }`). -/
def loopBody : MirBody where
  argTys := []
  retTy := .unit
  localCount := 1
  blocks := [{ stmts := [], terminator := .goto ⟨0⟩ }]

theorem loopBody_reaches_running (init : MirState) (n : Nat) :
    ∀ (s : MirState) (tr : List Unit) (out : PrefixOutcome MirVal),
      s.block = 0 → s.stmtIdx = 0 →
      ReachesPrefix MirMachine loopBody init n s tr out →
      out = PrefixOutcome.running := by
  induction n with
  | zero =>
    intro s tr out _ _ hreach
    cases hreach with
    | zero => rfl
  | succ k ih =>
    intro s tr out hb hs hreach
    have hstep0 : evalMirStep loopBody s = StepResult.step () { s with block := 0, stmtIdx := 0 } := by
      unfold evalMirStep loopBody
      rw [hb, hs]
      rfl
    cases hreach with
    | step _ _ s' obs tr' _ h1 h2 =>
      have h1' : StepResult.step obs s' = evalMirStep loopBody s := h1
      rw [hstep0] at h1'
      injection h1' with _ hs'
      subst hs'
      exact ih { s with block := 0, stmtIdx := 0 } tr' out rfl rfl h2
    | choice _ _ _ _ _ _ _ h1 _ _ =>
      have h1' : _ = evalMirStep loopBody s := h1
      rw [hstep0] at h1'
      cases h1'
    | emptyChoice _ _ _ _ h1 _ =>
      have h1' : _ = evalMirStep loopBody s := h1
      rw [hstep0] at h1'
      cases h1'
    | terminated _ _ _ h1 =>
      have h1' : _ = evalMirStep loopBody s := h1
      rw [hstep0] at h1'
      cases h1'
    | failed _ _ _ h1 =>
      have h1' : _ = evalMirStep loopBody s := h1
      rw [hstep0] at h1'
      cases h1'
    | noStep _ _ hnostep =>
      exact False.elim (hnostep ⟨_, hstep0.symm⟩)

/-- Positive adequacy canary: a pure infinite loop (`loop {}`)
    never triggers `.failed` or `.stuck` at any prefix depth and therefore
    satisfies `MirLang.WellFormed`. -/
theorem canary_safe_infinite_loop :
    MirSem loopBody ≤ MirLang.WellFormed := by
  refine (behaviorOf_le_wellFormed_iff (M := MirMachine)).mpr ?_
  intro init steps tr out hinit hreach
  have hout := loopBody_reaches_running init steps init tr out
    hinit.1 hinit.2.1 hreach
  rw [hout]
  exact True.intro

/-- MIR body that returns immediately without initializing `_0`. -/
def uninitReturnBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 1
  blocks := [{ stmts := [], terminator := .return_ }]

/-- Negative adequacy canary: returning an uninitialized `_0`
    triggers `.failed .ub` at step `1` and therefore refutes
    `MirLang.WellFormed`. -/
theorem canary_uninit_return_violates_wellFormed :
    ¬ (MirSem uninitReturnBody ≤ MirLang.WellFormed) := by
  intro hWF
  let s0 : MirState := {
    locals := fun _ => none
    mem := MemState.empty
    block := 0
    stmtIdx := 0
  }
  have hinit : initMirState uninitReturnBody s0 :=
    ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
  have hfail : ReachesPrefix MirMachine uninitReturnBody s0 1 s0 [] (PrefixOutcome.failed FailureKind.ub) :=
    ReachesPrefix.failed 0 s0 FailureKind.ub rfl
  exact (behaviorOf_le_wellFormed_iff (M := MirMachine)).mp hWF s0 1 [] (.failed .ub) hinit hfail

/-- MIR body for `pub fn id(x: usize) -> usize { 0 }` (assigns constant `0` to
    `_0` instead of `x`). -/
def wrongReturnZeroBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.assign ⟨0⟩ (.use (.constVal (.usize 0)))]
      terminator := .return_ }
  ]

/-- Negative adequacy canary: returning constant `0` instead of `_1`
    violates `EnsuresEqArg 1` when `_1 = MirVal.usize 1`. -/
theorem canary_wrong_id_violates_ensures :
    ¬ (MirSem wrongReturnZeroBody ≤ EnsuresEqArg 1) := by
  intro hEns
  let locals0 : Nat → Option MirVal :=
    updateLocal (fun _ => none) 1 (some (.usize 1))
  let s0 : MirState := {
    locals := locals0
    mem := MemState.empty
    block := 0
    stmtIdx := 0
  }
  let s1 : MirState := {
    locals := updateLocal locals0 0 (some (.usize 0))
    mem := MemState.empty
    block := 0
    stmtIdx := 1
  }
  have hrest : ∀ j, 2 ≤ j → locals0 j = none := by
    intro j hj
    cases j with
    | zero => cases hj
    | succ k =>
      cases k with
      | zero =>
        cases hj with
        | step hle => cases hle
      | succ m => rfl
  have hinit : initMirState wrongReturnZeroBody s0 :=
    ⟨rfl, rfl, rfl, ⟨⟨MirVal.usize 1, rfl, True.intro⟩, hrest⟩⟩
  have hreach1 : ReachesPrefix MirMachine wrongReturnZeroBody s0 1 s1 []
      (PrefixOutcome.terminated (TerminationKind.normal (MirVal.usize 0))) :=
    ReachesPrefix.terminated 0 s1 (TerminationKind.normal (MirVal.usize 0)) rfl
  have hreach2 : ReachesPrefix MirMachine wrongReturnZeroBody s0 2 s0 [()]
      (PrefixOutcome.terminated (TerminationKind.normal (MirVal.usize 0))) :=
    ReachesPrefix.step 1 s0 s1 () []
      (PrefixOutcome.terminated (TerminationKind.normal (MirVal.usize 0))) rfl hreach1
  let q : ExecQuery MirState := { init := s0, steps := 2 }
  let out : ExecOut Unit MirVal := {
    trace := [()]
    outcome := PrefixOutcome.terminated (TerminationKind.normal (MirVal.usize 0))
  }
  cases hEns q True.intro with
  | intro hdef hval =>
    have hpfx : (MirSem wrongReturnZeroBody q).val hdef out := ⟨hinit, hreach2⟩
    have hpost := hval out hpfx (MirVal.usize 0) rfl
    have h1 : q.init.locals 1 = some (MirVal.usize 1) := rfl
    rw [h1] at hpost
    injection hpost with hval'
    injection hval' with hnum
    cases hnum

/-- MIR body that accepts `_1 : &AtomicUsize` (`MirTy.refAtomicUsize`) and
    returns constant `0` instead of loading from `_1`. -/
def wrongAtomicReturnZeroBody : MirBody where
  argTys := [.refAtomicUsize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.assign ⟨0⟩ (.use (.constVal (.usize 0)))]
      terminator := .return_ }
  ]

/-- Negative adequacy canary for weak-memory atomic loads: returning constant
    `0`
    without reading `_1` violates `EnsuresAtomicLoad 1` when location `0`'s only
    visible modification-order message has `bits = 1`. -/
theorem canary_wrong_atomic_load_violates_ensures :
    ¬ (MirSem wrongAtomicReturnZeroBody ≤ EnsuresAtomicLoad 1) := by
  intro hEns
  let msg0 : AtomicMsg := { loc := 0, ts := 0, bits := 1, relView := View.bot }
  let mem0 : MemState := { MemState.empty with atomicMsgs := [msg0] }
  let locals0 : Nat → Option MirVal :=
    updateLocal (fun _ => none) 1 (some (.atomicLoc 0))
  let s0 : MirState := {
    locals := locals0
    mem := mem0
    block := 0
    stmtIdx := 0
  }
  let s1 : MirState := {
    locals := updateLocal locals0 0 (some (.usize 0))
    mem := mem0
    block := 0
    stmtIdx := 1
  }
  have hrest : ∀ j, 2 ≤ j → locals0 j = none := by
    intro j hj
    cases j with
    | zero => cases hj
    | succ k =>
      cases k with
      | zero =>
        cases hj with
        | step hle => cases hle
      | succ m => rfl
  have hvis : mem0.visibleAtomicMsgs 0 ≠ [] := by
    intro hnil
    cases hnil
  have hinit : initMirState wrongAtomicReturnZeroBody s0 :=
    ⟨rfl, rfl, rfl, ⟨⟨MirVal.atomicLoc 0, rfl, hvis⟩, hrest⟩⟩
  have hreach1 : ReachesPrefix MirMachine wrongAtomicReturnZeroBody s0 1 s1 []
      (PrefixOutcome.terminated (TerminationKind.normal (MirVal.usize 0))) :=
    ReachesPrefix.terminated 0 s1 (TerminationKind.normal (MirVal.usize 0)) rfl
  have hreach2 : ReachesPrefix MirMachine wrongAtomicReturnZeroBody s0 2 s0 [()]
      (PrefixOutcome.terminated (TerminationKind.normal (MirVal.usize 0))) :=
    ReachesPrefix.step 1 s0 s1 () []
      (PrefixOutcome.terminated (TerminationKind.normal (MirVal.usize 0))) rfl hreach1
  let q : ExecQuery MirState := { init := s0, steps := 2 }
  let out : ExecOut Unit MirVal := {
    trace := [()]
    outcome := PrefixOutcome.terminated (TerminationKind.normal (MirVal.usize 0))
  }
  cases hEns q True.intro with
  | intro hdef hval =>
    have hpfx : (MirSem wrongAtomicReturnZeroBody q).val hdef out := ⟨hinit, hreach2⟩
    have hpost := hval out hpfx (MirVal.usize 0) rfl
    cases hpost with
    | intro loc hpost2 =>
      cases hpost2 with
      | intro msg hprops =>
        have hloc : q.init.locals 1 = some (MirVal.atomicLoc 0) := rfl
        have hloc_eq := hprops.1
        rw [hloc] at hloc_eq
        injection hloc_eq with hval'
        injection hval' with hloc0
        subst hloc0
        have hmem : msg ∈ [msg0] := hprops.2.1
        cases hmem with
        | head =>
          have hret := hprops.2.2
          injection hret with hbits
          cases hbits
        | tail _ htail =>
          cases htail



/-!
## 1. Functional Result Domain (`AeneasRes`), `FuncLang`, and `π_func`
-/

/-- Result of plan-guided symbolic evaluation:
    - `.ok v`: normal return with value `v`,
    - `.inapplicable`: initial `MirState` does not satisfy the function's entry
      precondition (`initMirState`), mapped to the vacuous partial behavior
      `{ defined := True, val := fun _ _ => False }`,
    - `.fail`: translation or assertion failure, mapped to `Partial.ub`
      (`{ defined := False, val := fun _ _ => True }`). -/
inductive AeneasRes (Val : Type) where
  | ok (v : Val)
  | inapplicable
  | fail

/-- Pure functional target language for the Aeneas-inspired translation.
    - `Prog`: a function `MirState → AeneasRes MirVal` mapping the initial
      state of a call to `.ok ret` or `.fail`.
    - `Query`: the initial `MirState` (big-step, with no step-budget index).
    - `Out`: the returned `MirVal`.
    - `sem`: `.fail` makes `defined := False` (`Partial.ub`); `.ok v` yields
      the singleton outcome predicate `fun r => r = v`. -/
def FuncLang : Language where
  Prog := MirState → AeneasRes MirVal
  Query := MirState
  Out := MirVal
  sem p init := {
    defined := p init ≠ .fail
    val := fun _ v => p init = .ok v
  }

/-- Behavior mapping `π_func : FuncLang.Behavior → MirLang.Behavior` lifting a
    big-step functional behavior `b : MirState → Partial (MirVal → Prop)` to
    small-step prefix behaviors `ExecQuery MirState → Partial (ExecOut Unit
    MirVal → Prop)`
    via `Partial.map`. -/
def π_func (b : FuncLang.Behavior) : MirLang.Behavior :=
  fun q =>
    Partial.map
      (fun (post : MirVal → Prop) (out : ExecOut Unit MirVal) =>
        out.outcome.isSafe ∧
        ∀ ret, out.outcome = .terminated (.normal ret) → post ret)
      (b q.init)

/-- `π_func` is monotone with respect to `Preorder` (`≤`). -/
theorem monotone_π_func : Monotone π_func :=
  fun _ _ hb q =>
    Partial.monotone_map
      (by intro _ _ hle out ⟨hsafe, hret⟩; exact ⟨hsafe, fun r hr => hle r (hret r hr)⟩)
      (hb q.init)

/-- Any unconditional functional specification `FuncLang.Spec Post` maps under
    `π_func` to a behavior that refines the corresponding `MirLang.Spec`. -/
theorem π_func_spec_le (Post : MirState → MirVal → Prop) :
    π_func (FuncLang.Spec Post) ≤
      MirLang.Spec (fun q out =>
        ∀ ret, out.outcome = .terminated (.normal ret) → Post q.init ret) :=
  fun _ _ => ⟨True.intro, fun _ hout => hout.2⟩

/-!
## 2. Small-Step Prefix Simulation Helpers (`SafeAndReturns`)
-/

/-- From current machine state `s`, every finite execution prefix of `body` is
    safe (`out.isSafe`) and any normal termination returns `v`. -/
def SafeAndReturns (body : MirBody) (s : MirState) (v : MirVal) : Prop :=
  ∀ (init : MirState) (steps : Nat) (tr : List Unit) (out : PrefixOutcome MirVal),
    ReachesPrefix MirMachine body init steps s tr out →
    out.isSafe ∧ (∀ ret, out = .terminated (.normal ret) → ret = v)

/-- Deterministic single-step lifting for `SafeAndReturns`: if `s` steps
    deterministically to `s'` and `SafeAndReturns body s' v` holds, then
    `SafeAndReturns body s v` holds. -/
theorem SafeAndReturns.of_step {body : MirBody} {s s' : MirState} {v : MirVal}
    (hstep : evalMirStep body s = .step () s')
    (hnext : SafeAndReturns body s' v) :
    SafeAndReturns body s v := by
  intro init steps tr out hreach
  cases hreach with
  | zero =>
    exact ⟨True.intro, fun _ h => by cases h⟩
  | step n _ s'' obs tr' out h1 h2 =>
    have h1' : StepResult.step obs s'' = evalMirStep body s := h1
    rw [hstep] at h1'
    injection h1' with _ hs''
    subst hs''
    exact hnext init n tr' out h2
  | choice _ _ _ _ _ _ _ h1 _ _ =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | emptyChoice _ _ _ _ h1 _ =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | terminated _ _ _ h1 =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | failed _ _ _ h1 =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | noStep _ _ hnostep =>
    exact False.elim (hnostep ⟨_, hstep.symm⟩)

/-- Terminal lifting for `SafeAndReturns`: if `s` terminates normally with `v`
    in one step, then `SafeAndReturns body s v` holds. -/
theorem SafeAndReturns.of_terminated {body : MirBody} {s : MirState} {v : MirVal}
    (hterm : evalMirStep body s = .terminated (.normal v)) :
    SafeAndReturns body s v := by
  intro init steps tr out hreach
  cases hreach with
  | zero =>
    exact ⟨True.intro, fun _ h => by cases h⟩
  | step _ _ _ _ _ _ h1 _ =>
    have h1' : _ = evalMirStep body s := h1
    rw [hterm] at h1'; cases h1'
  | choice _ _ _ _ _ _ _ h1 _ _ =>
    have h1' : _ = evalMirStep body s := h1
    rw [hterm] at h1'; cases h1'
  | emptyChoice _ _ _ _ h1 _ =>
    have h1' : _ = evalMirStep body s := h1
    rw [hterm] at h1'; cases h1'
  | terminated _ _ term h1 =>
    have h1' : StepResult.terminated term = evalMirStep body s := h1
    rw [hterm] at h1'
    injection h1' with hterm_eq
    subst hterm_eq
    refine ⟨True.intro, ?_⟩
    intro ret hret
    injection hret with hterm_ret
    injection hterm_ret with hret_eq
    exact hret_eq.symm
  | failed _ _ _ h1 =>
    have h1' : _ = evalMirStep body s := h1
    rw [hterm] at h1'; cases h1'
  | noStep _ _ hnostep =>
    exact False.elim (hnostep ⟨_, hterm.symm⟩)

/-!
## 3. Symbolic Values (`SymVal`), Loans (`LoanEntry`), and `TransPlan`
-/

/-- Symbolic values in the functional translation: scalar values (`.usize`,
    `.bool`, `.unit`, `.tupleUsizeBool`), immutable shared reference values
    (`.refShared n`), and active mutable borrow tokens (`.borrow loanId`). -/
inductive SymVal where
  | usize (n : Nat)
  | bool (b : Bool)
  | unit
  | tupleUsizeBool (val : Nat) (overflow : Bool)
  | refShared (n : Nat)
  | borrow (loanId : Nat)

/-- Convert a scalar `SymVal` to its runtime `MirVal` (`none` for `.refShared`
    and `.borrow`). -/
def SymVal.toScalarMirVal : SymVal → Option MirVal
  | .usize n => some (.usize n)
  | .bool b => some (.bool b)
  | .unit => some .unit
  | .tupleUsizeBool val ov => some (.tupleUsizeBool val ov)
  | .refShared _ => none
  | .borrow _ => none

/-- Spine-preserving conditional merge on `SymVal`: pushes `if b then ... else
    ...`
    inside `.usize`, `.bool`, `.tupleUsizeBool`, and `.refShared` payloads so
    the
    outer `SymVal` constructor tag remains exposed for subsequent pattern
    matching
    (`toScalarMirVal`, dereference reads) during `rfl` reduction on symbolic
    inputs. -/
def zipSymVal (b : Bool) (tVal fVal : SymVal) : SymVal :=
  match tVal, fVal with
  | .usize nt, .usize nf => .usize (if b then nt else nf)
  | .bool bt, .bool bf => .bool (if b then bt else bf)
  | .unit, .unit => .unit
  | .tupleUsizeBool vt ovt, .tupleUsizeBool vf ovf =>
    .tupleUsizeBool (if b then vt else vf) (if b then ovt else ovf)
  | .refShared nt, .refShared nf => .refShared (if b then nt else nf)
  | _, _ => if b then tVal else fVal

theorem zipSymVal_eq_ite (b : Bool) (tVal fVal : SymVal) :
    zipSymVal b tVal fVal = (if b then tVal else fVal) := by
  cases b <;> cases tVal <;> cases fVal <;> rfl

/-- Spine-preserving conditional merge on `AeneasRes MirVal`: pushes
    `if b then ... else ...` inside `.ok (.usize ...)` and `.ok (.bool ...)`. -/
def zipAeneasRes (b : Bool) (tRes fRes : AeneasRes MirVal) : AeneasRes MirVal :=
  match tRes, fRes with
  | .ok (.usize nt), .ok (.usize nf) => .ok (.usize (if b then nt else nf))
  | .ok (.bool bt), .ok (.bool bf) => .ok (.bool (if b then bt else bf))
  | .ok .unit, .ok .unit => .ok .unit
  | _, _ => if b then tRes else fRes

theorem zipAeneasRes_eq_ite (b : Bool) (tRes fRes : AeneasRes MirVal) :
    zipAeneasRes b tRes fRes = (if b then tRes else fRes) := by
  cases b <;> cases tRes with
  | inapplicable => rfl
  | fail => rfl
  | ok vt =>
    cases vt <;> cases fRes with
    | inapplicable => rfl
    | fail => rfl
    | ok vf => cases vf <;> rfl

/-- Identifier of an underlying owner frozen by an active mutable loan:
    either a local variable slot (`OwnerId.local`) or a parent loan
    (`OwnerId.loan`) in a reborrow or branch-joined borrow. -/
inductive OwnerId where
  | local (id : Nat)
  | loan (id : Nat)

/-- Unified loan entry in `SymState.loans` representing a root parameter borrow
    (`&mut x`) or a branch-joined mutable borrow
    (`if cond { &mut *x } else { &mut *y }`):
    - `owners`: parent `OwnerId`s frozen while this loan is active,
    - `curVal`: current symbolic value of the borrowed referent,
    - `frozen`: whether this loan is currently frozen by a child borrow or
      retired,
    - `active`: whether this loan is currently live (not yet ended by
      `endLoan`),
    - `back`: executable backward lens `SymVal → List SymVal` mapping the final
      value of this loan at `endLoan` to the updated values written back to
      each owner in `owners`. -/
structure LoanEntry where
  owners : List OwnerId
  curVal : SymVal
  frozen : Bool
  active : Bool
  back : SymVal → List SymVal

/-- Symbolic execution state during plan-guided shallow evaluation. -/
structure SymState where
  locals : Nat → Option SymVal
  loans : Nat → Option LoanEntry
  nextLoan : Nat
  hasActiveJoin : Bool
  block : Nat
  stmtIdx : Nat

/-- Update local slot `target` in a symbolic local store `locals`. -/
def updateSymLocal (locals : Nat → Option SymVal) (target : Nat)
    (val : Option SymVal) : Nat → Option SymVal :=
  fun i => if i == target then val else locals i

/-- Update loan slot `target` in a symbolic loan store `loans`. -/
def updateLoan (loans : Nat → Option LoanEntry) (target : Nat)
    (val : Option LoanEntry) : Nat → Option LoanEntry :=
  fun i => if i == target then val else loans i

/-- Positional translation plan guiding `evalSymState` over a `MirBody`.
    - `ret`: execute `Terminator.return_` at the end of the current block.
    - `step next`: execute one statement or `Terminator.goto`, then continue
      with `next`.
    - `endLoan loanId next`: end active loan `loanId`, propagating
      `entry.back entry.curVal` to `entry.owners` and unfreezing them, then
      continue with `next`.
    - `branch falsePlan truePlan`: evaluate `Terminator.switchInt` and merge
      the `falsePlan` and `truePlan` results via `zipAeneasRes`.
    - `joinBorrow dstLocal falseSrcLocal trueSrcLocal joinBlock joinedLoanId
      afterJoin`:
      execute a diamond conditional reborrow (`if cond { dst = copy trueSrc }
      else { dst = copy falseSrc }`)
      joining at `joinBlock` by allocating a fresh `LoanEntry` at `joinedLoanId`
      with `owners := [.loan falseLid, .loan trueLid]` and a spine-preserving
      backward lens `back`, then continue once with `afterJoin`.
    - `fail`: abort translation on the current path (`.fail`). -/
inductive TransPlan where
  | ret
  | step (next : TransPlan)
  | endLoan (loanId : Nat) (next : TransPlan)
  | branch (falsePlan : TransPlan) (truePlan : TransPlan)
  | joinBorrow
      (dstLocal : Nat)
      (falseSrcLocal : Nat)
      (trueSrcLocal : Nat)
      (joinBlock : Nat)
      (joinedLoanId : Nat)
      (afterJoin : TransPlan)
  | fail

/-!
## 4. Symbolic Step Primitives and Plan-Guided Evaluator (`evalSymState`)
-/

/-- Convert a constant `MirVal` operand into a scalar `SymVal`. -/
def evalSymConst : MirVal → Option SymVal
  | .usize n => some (.usize n)
  | .bool b => some (.bool b)
  | .unit => some .unit
  | _ => none

/-- Evaluate a MIR `Operand` in a symbolic local store `locals`. -/
def evalSymOperand (locals : Nat → Option SymVal) (op : Operand) :
    Option (SymVal × (Nat → Option SymVal)) :=
  match op with
  | .copy src =>
    match locals src.index with
    | some sv => some (sv, locals)
    | none => none
  | .move src =>
    match locals src.index with
    | some sv => some (sv, updateSymLocal locals src.index none)
    | none => none
  | .constVal mv =>
    match evalSymConst mv with
    | some sv => some (sv, locals)
    | none => none

/-- Evaluate a binary comparison or bitwise operator on two symbolic `SymVal`
    operands. -/
def evalSymBinOp (op : BinOp) (v1 v2 : SymVal) : Option SymVal :=
  match v1, v2 with
  | .usize n1, .usize n2 =>
    match op with
    | .lt => some (.bool (decide (n1 < n2)))
    | .le => some (.bool (decide (n1 ≤ n2)))
    | .eq => some (.bool (decide (n1 = n2)))
    | .ne => some (.bool (decide (n1 ≠ n2)))
    | .gt => some (.bool (decide (n2 < n1)))
    | .ge => some (.bool (decide (n2 ≤ n1)))
    | .bitAnd => some (.usize (Nat.land n1 n2))
    | .bitOr => some (.usize (Nat.lor n1 n2))
    | .bitXor => some (.usize (Nat.xor n1 n2))
  | _, _ => none

/-- Evaluate a checked binary arithmetic operator on two symbolic `SymVal`
    operands. -/
def evalSymCheckedBinOp (op : CheckedBinOp) (v1 v2 : SymVal) : Option SymVal :=
  match v1, v2 with
  | .usize n1, .usize n2 =>
    match op with
    | .add => some (.tupleUsizeBool (n1 + n2) (decide (usizeMax < n1 + n2)))
    | .sub => some (.tupleUsizeBool (n1 - n2) (decide (n1 < n2)))
    | .mul => some (.tupleUsizeBool (n1 * n2) (decide (usizeMax < n1 * n2)))
  | _, _ => none

/-- Evaluate a pure 2-argument `usize` callee (`PureCallee2`) on two symbolic
    `SymVal` operands. -/
def evalSymPureCallee2 (callee : PureCallee2) (v1 v2 : SymVal) : Option SymVal :=
  match v1, v2 with
  | .usize x0, .usize y0 =>
    match callee with
    | .addBounded =>
      some (.usize (if decide (x0 ≤ 1000) && decide (y0 ≤ 1000) then x0 + y0 else 0))
    | .absDiff =>
      some (.usize (if decide (y0 ≤ x0) then x0 - y0 else y0 - x0))
  | _, _ => none

/-- Symbolic evaluation of a single MIR `Stmt`. -/
def evalSymStmt (sym : SymState) (stmt : Stmt) : Option SymState :=
  match stmt with
  | .assign dst (.use op) =>
    match evalSymOperand sym.locals op with
    | some (sv, locals') =>
      some { sym with
        locals := updateSymLocal locals' dst.index (some sv)
        stmtIdx := sym.stmtIdx + 1
      }
    | none => none
  | .assign dst (.deref src) =>
    match sym.locals src.index with
    | some (.refShared n) =>
      some { sym with
        locals := updateSymLocal sym.locals dst.index (some (.usize n))
        stmtIdx := sym.stmtIdx + 1
      }
    | some (.borrow lid) =>
      match sym.loans lid with
      | some entry =>
        if entry.active && !entry.frozen then
          some { sym with
            locals := updateSymLocal sym.locals dst.index (some entry.curVal)
            stmtIdx := sym.stmtIdx + 1
          }
        else
          none
      | none => none
    | _ => none
  | .assign dst (.proj0 src) =>
    match sym.locals src.index with
    | some (.tupleUsizeBool val _) =>
      some { sym with
        locals := updateSymLocal sym.locals dst.index (some (.usize val))
        stmtIdx := sym.stmtIdx + 1
      }
    | _ => none
  | .assign dst (.proj1 src) =>
    match sym.locals src.index with
    | some (.tupleUsizeBool _ ov) =>
      some { sym with
        locals := updateSymLocal sym.locals dst.index (some (.bool ov))
        stmtIdx := sym.stmtIdx + 1
      }
    | _ => none
  | .assign dst (.binaryOp op lhs rhs) =>
    match evalSymOperand sym.locals lhs with
    | none => none
    | some (v1, locals1) =>
      match evalSymOperand locals1 rhs with
      | none => none
      | some (v2, locals2) =>
        match evalSymBinOp op v1 v2 with
        | some res =>
          some { sym with
            locals := updateSymLocal locals2 dst.index (some res)
            stmtIdx := sym.stmtIdx + 1
          }
        | none => none
  | .assign dst (.checkedBinaryOp op lhs rhs) =>
    match evalSymOperand sym.locals lhs with
    | none => none
    | some (v1, locals1) =>
      match evalSymOperand locals1 rhs with
      | none => none
      | some (v2, locals2) =>
        match evalSymCheckedBinOp op v1 v2 with
        | some res =>
          some { sym with
            locals := updateSymLocal locals2 dst.index (some res)
            stmtIdx := sym.stmtIdx + 1
          }
        | none => none
  | .assignDeref dst op =>
    match evalSymOperand sym.locals op with
    | none => none
    | some (sv, locals1) =>
      match sv.toScalarMirVal, locals1 dst.index with
      | some _, some (.borrow lid) =>
        match sym.loans lid with
        | some entry =>
          if entry.active && !entry.frozen then
            some { sym with
              locals := locals1
              loans := updateLoan sym.loans lid (some { entry with curVal := sv })
              stmtIdx := sym.stmtIdx + 1
            }
          else
            none
        | none => none
      | _, _ => none
  | .storageLive loc =>
    some { sym with
      locals := updateSymLocal sym.locals loc.index none
      stmtIdx := sym.stmtIdx + 1
    }
  | .storageDead loc =>
    some { sym with
      locals := updateSymLocal sym.locals loc.index none
      stmtIdx := sym.stmtIdx + 1
    }
  | .nop =>
    some { sym with stmtIdx := sym.stmtIdx + 1 }

/-- Execute one sequential statement, `Terminator.goto`, or
    `Terminator.assertNotOverflow` step in `sym`, returning `(overflow, sym')`
    where `overflow = false` for statements and `goto`, and `overflow = ov` for
    `assertNotOverflow` on `.tupleUsizeBool _ ov`. -/
def evalSymStep (body : MirBody) (sym : SymState) : Option (Bool × SymState) :=
  match body.blocks[sym.block]? with
  | none => none
  | some bb =>
    match bb.stmts[sym.stmtIdx]? with
    | some stmt =>
      match evalSymStmt sym stmt with
      | some sym' => some (false, sym')
      | none => none
    | none =>
      match bb.terminator with
      | .goto target => some (false, { sym with block := target.index, stmtIdx := 0 })
      | .assertNotOverflow tupleLocal target =>
        match sym.locals tupleLocal.index with
        | some (.tupleUsizeBool _ ov) =>
          some (ov, { sym with block := target.index, stmtIdx := 0 })
        | _ => none
      | .callPure2 dst callee arg1 arg2 target =>
        match evalSymOperand sym.locals arg1 with
        | none => none
        | some (v1, locals1) =>
          match evalSymOperand locals1 arg2 with
          | none => none
          | some (v2, locals2) =>
            match evalSymPureCallee2 callee v1 v2 with
            | some res =>
              some (false, {
                sym with
                locals := updateSymLocal locals2 dst.index (some res)
                block := target.index
                stmtIdx := 0
              })
            | none => none
      | _ => none

/-- Execute `Terminator.return_` at the end of the current block, returning the
    scalar `MirVal` in `_0`. -/
def evalReturn (body : MirBody) (sym : SymState) : Option MirVal :=
  match body.blocks[sym.block]? with
  | none => none
  | some bb =>
    match bb.stmts[sym.stmtIdx]?, bb.terminator with
    | none, .return_ =>
      match sym.locals 0 with
      | some sv => sv.toScalarMirVal
      | none => none
    | _, _ => none

/-- Evaluate a `Terminator.switchInt` discriminant at the end of the current
    block, returning the boolean condition and the successor states for the
    `false` and `true` targets. -/
def evalBranchStep (body : MirBody) (sym : SymState) :
    Option (Bool × SymState × SymState) :=
  match body.blocks[sym.block]? with
  | none => none
  | some bb =>
    match bb.stmts[sym.stmtIdx]?, bb.terminator with
    | none, .switchInt discr falseTarget trueTarget =>
      match evalSymOperand sym.locals discr with
      | some (.bool cond, locals') =>
        let symFalse := { sym with locals := locals', block := falseTarget.index, stmtIdx := 0 }
        let symTrue := { sym with locals := locals', block := trueTarget.index, stmtIdx := 0 }
        some (cond, symFalse, symTrue)
      | _ => none
    | _, _ => none

/-- End an active joined loan `lid`, applying `entry.back entry.curVal` to
    update and unfreeze its parent loans `[.loan falseLid, .loan trueLid]`. -/
def evalEndLoan (sym : SymState) (lid : Nat) : Option SymState :=
  match sym.loans lid with
  | some entry =>
    if entry.active && !entry.frozen then
      match entry.owners, entry.back entry.curVal with
      | [.loan falseLid, .loan trueLid], [vFalse, vTrue] =>
        match sym.loans falseLid, sym.loans trueLid with
        | some falseEntry, some trueEntry =>
          let loans1 := updateLoan sym.loans lid (some { entry with active := false, frozen := true })
          let loans2 := updateLoan loans1 falseLid (some { falseEntry with curVal := vFalse, frozen := false })
          let loans3 := updateLoan loans2 trueLid (some { trueEntry with curVal := vTrue, frozen := false })
          some { sym with loans := loans3, hasActiveJoin := false }
        | _, _ => none
      | _, _ => none
    else
      none
  | none => none

/-- Check whether a basic block `bb` is a single-statement borrow-copy arm
    `_dst = copy _src; goto -> bbJoin;`, returning `some (dst.index, src.index,
    join.index)`. -/
def matchBorrowArm (bb : BasicBlock) : Option (Nat × Nat × Nat) :=
  match bb.stmts with
  | [s] =>
    match s with
    | .assign dst (.use (.copy src)) =>
      match bb.terminator with
      | .goto joinBlk => some (dst.index, src.index, joinBlk.index)
      | _ => none
    | _ => none
  | _ => none

/-- Execute a diamond conditional reborrow (`switchInt` whose `falseTarget`
    assigns `dst = copy falseSrc; goto joinBlock` and whose `trueTarget`
    assigns `dst = copy trueSrc; goto joinBlock`), allocating a fresh
    `LoanEntry` at `joinedLid` with `owners := [.loan falseLid, .loan trueLid]`
    and a backward lens `back`. -/
def evalJoinBorrow (body : MirBody) (sym : SymState)
    (dstLocal falseSrc trueSrc joinBlock joinedLid : Nat) : Option SymState :=
  if sym.hasActiveJoin then
    none
  else
    match body.blocks[sym.block]? with
    | none => none
    | some bb =>
      match bb.stmts[sym.stmtIdx]?, bb.terminator with
      | none, .switchInt discr falseTarget trueTarget =>
        match evalSymOperand sym.locals discr with
        | some (.bool cond, localsAfterDiscr) =>
          match body.blocks[falseTarget.index]?, body.blocks[trueTarget.index]? with
          | some bbFalse, some bbTrue =>
            match matchBorrowArm bbFalse, matchBorrowArm bbTrue with
            | some (dstF, srcF, joinF), some (dstT, srcT, joinT) =>
              if dstF == dstLocal && dstT == dstLocal &&
                 srcF == falseSrc && srcT == trueSrc &&
                 joinF == joinBlock && joinT == joinBlock then
                match localsAfterDiscr falseSrc, localsAfterDiscr trueSrc with
                | some (.borrow falseLid), some (.borrow trueLid) =>
                  if !(falseLid == trueLid) && !(falseLid == joinedLid) && !(trueLid == joinedLid) then
                    match sym.loans falseLid, sym.loans trueLid, sym.loans joinedLid with
                    | some falseEntry, some trueEntry, none =>
                      if falseEntry.active && !falseEntry.frozen &&
                         trueEntry.active && !trueEntry.frozen then
                        let joinedEntry : LoanEntry := {
                          owners := [.loan falseLid, .loan trueLid]
                          curVal := zipSymVal cond trueEntry.curVal falseEntry.curVal
                          frozen := false
                          active := true
                          back := fun newVal => [
                            zipSymVal cond falseEntry.curVal newVal,
                            zipSymVal cond newVal trueEntry.curVal
                          ]
                        }
                        let loans1 := updateLoan sym.loans falseLid (some { falseEntry with frozen := true })
                        let loans2 := updateLoan loans1 trueLid (some { trueEntry with frozen := true })
                        let loans3 := updateLoan loans2 joinedLid (some joinedEntry)
                        some {
                          locals := updateSymLocal localsAfterDiscr dstLocal (some (.borrow joinedLid))
                          loans := loans3
                          nextLoan := joinedLid + 1
                          hasActiveJoin := true
                          block := joinBlock
                          stmtIdx := 0
                        }
                      else
                        none
                    | _, _, _ => none
                  else
                    none
                | _, _ => none
              else
                none
            | _, _ => none
          | _, _ => none
        | _ => none
      | _, _ => none

/-- Plan-guided shallow symbolic evaluator over `SymState`.
    Compiled via structural recursion on `plan : TransPlan`. -/
noncomputable def evalSymState (plan : TransPlan) (body : MirBody) (sym : SymState) : AeneasRes MirVal :=
  match plan with
  | .ret =>
    match evalReturn body sym with
    | some mv => .ok mv
    | none => .fail
  | .step next =>
    match evalSymStep body sym with
    | some (ov, sym') =>
      if ov then .fail else evalSymState next body sym'
    | none => .fail
  | .endLoan lid next =>
    match evalEndLoan sym lid with
    | some sym' => evalSymState next body sym'
    | none => .fail
  | .branch falsePlan truePlan =>
    match evalBranchStep body sym with
    | some (cond, symFalse, symTrue) =>
      zipAeneasRes cond
        (evalSymState truePlan body symTrue)
        (evalSymState falsePlan body symFalse)
    | none => .fail
  | .joinBorrow dstLocal falseSrc trueSrc joinBlock joinedLid afterJoin =>
    match evalJoinBorrow body sym dstLocal falseSrc trueSrc joinBlock joinedLid with
    | some symJoined => evalSymState afterJoin body symJoined
    | none => .fail
  | .fail => .fail

/-!
## 5. Pure Input Construction (`translatePure`) and Extraction (`evalSym`)
-/

/-- Pure argument value passed to a translated Rust function: either a scalar
    (`usize`, `bool`, `unit`), the referent value of an immutable `&usize`
    parameter (`refShared n`), or the initial referent value of a `&mut usize`
    parameter (`refMut n`). -/
inductive SymArg where
  | usize (n : Nat)
  | bool (b : Bool)
  | unit
  | refShared (n : Nat)
  | refMut (n : Nat)

/-- Empty symbolic local store (`fun _ => none`). -/
def emptySymLocals : Nat → Option SymVal := fun _ => none

/-- Empty symbolic loan store (`fun _ => none`). -/
def emptySymLoans : Nat → Option LoanEntry := fun _ => none

/-- Root `LoanEntry` for an input `&mut usize` parameter holding initial value
    `n`. -/
def rootLoanEntry (n : Nat) : LoanEntry where
  owners := []
  curVal := .usize n
  frozen := false
  active := true
  back := fun _ => []

/-- Populate symbolic parameter locals `idx ..` and root loans from a list of
    pure `SymArg` inputs. -/
noncomputable def buildPureSymStateAux (idx : Nat) : List SymArg →
    (Nat → Option SymVal) × (Nat → Option LoanEntry) × Nat
  | [] => (emptySymLocals, emptySymLoans, idx)
  | arg :: rest =>
    let (locals, loans, nextIdx) := buildPureSymStateAux (idx + 1) rest
    match arg with
    | .usize n => (updateSymLocal locals idx (some (.usize n)), loans, nextIdx)
    | .bool b => (updateSymLocal locals idx (some (.bool b)), loans, nextIdx)
    | .unit => (updateSymLocal locals idx (some .unit), loans, nextIdx)
    | .refShared n => (updateSymLocal locals idx (some (.refShared n)), loans, nextIdx)
    | .refMut n =>
      (updateSymLocal locals idx (some (.borrow idx)),
       updateLoan loans idx (some (rootLoanEntry n)),
       nextIdx)

/-- Build the initial `SymState` at `(block := 0, stmtIdx := 0)` for a list of
    pure `SymArg` function arguments. -/
noncomputable def buildPureSymState (args : List SymArg) : SymState :=
  let (locals, loans, nextLoan) := buildPureSymStateAux 1 args
  { locals := locals
    loans := loans
    nextLoan := nextLoan
    hasActiveJoin := false
    block := 0
    stmtIdx := 0 }

/-- Pure shallow functional evaluator taking a `TransPlan`, `MirBody`, and pure
    argument list `List SymArg`. Specializes on symbolic inputs via `rfl`. -/
noncomputable def translatePure (plan : TransPlan) (body : MirBody) (args : List SymArg) :
    AeneasRes MirVal :=
  evalSymState plan body (buildPureSymState args)

/-- Computable check that no parameter slot `1 ≤ i < k` in `locals` holds
    `.refMutLoc loc` or `.refSharedLoc loc`. -/
noncomputable def noAliasBefore (locals : Nat → Option MirVal) (loc : Nat) : Nat → Bool
  | 0 => true
  | 1 => true
  | j + 2 =>
    (match locals (j + 1) with
     | some (.refMutLoc loc') => !(loc' == loc)
     | some (.refSharedLoc loc') => !(loc' == loc)
     | _ => true) &&
    noAliasBefore locals loc (j + 1)

/-- Computable check that no parameter slot `1 ≤ i < k` in `locals` holds
    `.refMutLoc loc`. -/
noncomputable def noMutAliasBefore (locals : Nat → Option MirVal) (loc : Nat) : Nat → Bool
  | 0 => true
  | 1 => true
  | j + 2 =>
    (match locals (j + 1) with
     | some (.refMutLoc loc') => !(loc' == loc)
     | _ => true) &&
    noMutAliasBefore locals loc (j + 1)

/-- Extract the pure `List SymArg` argument vector from a concrete `MirState`
    according to `argTys`, checking parameter type validity, `OwnLoc` /
    `ReadOwnLoc`
    ownership, and `&mut` non-aliasing (`noAliasBefore`, `noMutAliasBefore`). -/
noncomputable def extractSymArgsAux (idx : Nat) : List MirTy → MirState → Option (List SymArg)
  | [], _ => some []
  | ty :: restTys, init =>
    match ty, init.locals idx with
    | .usize, some (.usize n) =>
      match extractSymArgsAux (idx + 1) restTys init with
      | some restArgs => some (.usize n :: restArgs)
      | none => none
    | .bool, some (.bool b) =>
      match extractSymArgsAux (idx + 1) restTys init with
      | some restArgs => some (.bool b :: restArgs)
      | none => none
    | .unit, some .unit =>
      match extractSymArgsAux (idx + 1) restTys init with
      | some restArgs => some (.unit :: restArgs)
      | none => none
    | .refSharedUsize, some (.refSharedLoc loc) =>
      if noMutAliasBefore init.locals loc idx &&
         decide (init.mem.naWriteTs loc ≤ init.mem.curView loc) then
        match init.mem.naVal loc with
        | some (.usize n) =>
          match extractSymArgsAux (idx + 1) restTys init with
          | some restArgs => some (.refShared n :: restArgs)
          | none => none
        | _ => none
      else
        none
    | .refMutUsize, some (.refMutLoc loc) =>
      if noAliasBefore init.locals loc idx &&
         decide (init.mem.naWriteTs loc ≤ init.mem.curView loc) &&
         decide (init.mem.naReadTs loc ≤ init.mem.curView loc) then
        match init.mem.naVal loc with
        | some (.usize n) =>
          match extractSymArgsAux (idx + 1) restTys init with
          | some restArgs => some (.refMut n :: restArgs)
          | none => none
        | _ => none
      else
        none
    | _, _ => none

/-- Check whether a `MirTy` parameter type is supported by pure functional
    translation (`.usize`, `.bool`, `.unit`, `.refSharedUsize`,
    `.refMutUsize`). -/
def isSupportedArgTy : MirTy → Bool
  | .usize => true
  | .bool => true
  | .unit => true
  | .refSharedUsize => true
  | .refMutUsize => true
  | .tupleUsizeBool => false
  | .refAtomicUsize => false
  | .atomicOrdering => false

/-- Check whether every parameter type in `argTys` is supported by pure
    functional translation. -/
noncomputable def allSupportedArgTys (tys : List MirTy) : Bool :=
  tys.all isSupportedArgTy

/-- Extract the pure `List SymArg` inputs at function entry (`block == 0`,
    `stmtIdx == 0`). -/
noncomputable def extractSymArgs (argTys : List MirTy) (init : MirState) : Option (List SymArg) :=
  if init.block == 0 && init.stmtIdx == 0 then
    extractSymArgsAux 1 argTys init
  else
    none

/-- Plan-guided functional evaluator `evalSym : TransPlan → MirBody →
    FuncLang.Prog`
    lifting `translatePure` to `MirState` via `extractSymArgs`:
    - If `body.argTys` contains an unsupported type (`allSupportedArgTys =
      false`),
      returns `.fail`.
    - Otherwise, if `extractSymArgs body.argTys init = some args`, returns
      `translatePure plan body args`.
    - If `extractSymArgs body.argTys init = none`, `init` lies outside
      `initMirState body`, so returns `.inapplicable` (matching the vacuous
      initial-state guard in `MirMachine`). -/
noncomputable def evalSym (plan : TransPlan) (body : MirBody) (init : MirState) : AeneasRes MirVal :=
  if allSupportedArgTys body.argTys then
    match extractSymArgs body.argTys init with
    | some args => translatePure plan body args
    | none => .inapplicable
  else
    .fail

/-!
## 6. Relational Simulation Invariant (`StateRel`) and Helper Soundness Lemmas
-/

/-- Value correspondence between a symbolic `SymVal` and a concrete `MirVal`
    under concrete loan-location map `loanLoc : Nat → Option Nat` and
    shared-reference relation `sharedLoc : Nat → Nat → Prop`. -/
def ValRel (loanLoc : Nat → Option Nat) (sharedLoc : Nat → Nat → Prop)
    (sv : SymVal) (mv : MirVal) : Prop :=
  match sv with
  | .usize n => mv = .usize n
  | .bool b => mv = .bool b
  | .unit => mv = .unit
  | .tupleUsizeBool val ov => mv = .tupleUsizeBool val ov
  | .refShared n => ∃ loc, sharedLoc loc n ∧ mv = .refSharedLoc loc
  | .borrow lid => ∃ loc, loanLoc lid = some loc ∧ mv = .refMutLoc loc

theorem ValRel.of_toScalarMirVal (loanLoc : Nat → Option Nat)
    (sharedLoc : Nat → Nat → Prop)
    {sv : SymVal} {mv : MirVal} (h : sv.toScalarMirVal = some mv) :
    ValRel loanLoc sharedLoc sv mv := by
  cases sv with
  | usize n => injection h with heq; exact heq.symm
  | bool b => injection h with heq; exact heq.symm
  | unit => injection h with heq; exact heq.symm
  | tupleUsizeBool val ov => injection h with heq; exact heq.symm
  | refShared _ => cases h
  | borrow _ => cases h

theorem ValRel.toScalarMirVal_eq {loanLoc : Nat → Option Nat}
    {sharedLoc : Nat → Nat → Prop}
    {sv : SymVal} {mv mv' : MirVal}
    (hRel : ValRel loanLoc sharedLoc sv mv)
    (hScalar : sv.toScalarMirVal = some mv') :
    mv = mv' := by
  cases sv with
  | usize n =>
    injection hScalar with h1
    exact Eq.trans hRel h1
  | bool b =>
    injection hScalar with h1
    exact Eq.trans hRel h1
  | unit =>
    injection hScalar with h1
    exact Eq.trans hRel h1
  | tupleUsizeBool val ov =>
    injection hScalar with h1
    exact Eq.trans hRel h1
  | refShared _ => cases hScalar
  | borrow _ => cases hScalar

theorem SymVal.not_borrow_of_toScalarMirVal {sv : SymVal} {mv : MirVal}
    (hScalar : sv.toScalarMirVal = some mv) (lid : Nat) :
    sv = .borrow lid → False := by
  intro heq
  subst heq
  cases hScalar

/-- Local store correspondence between `sym.locals` and `conc.locals`. -/
def LocalRel (loanLoc : Nat → Option Nat) (sharedLoc : Nat → Nat → Prop)
    (symLocals : Nat → Option SymVal) (concLocals : Nat → Option MirVal) : Prop :=
  ∀ i sv, symLocals i = some sv → ∃ mv, concLocals i = some mv ∧ ValRel loanLoc sharedLoc sv mv

theorem LocalRel.update_some {loanLoc : Nat → Option Nat} {sharedLoc : Nat → Nat → Prop}
    {symLocals : Nat → Option SymVal} {concLocals : Nat → Option MirVal}
    (hRel : LocalRel loanLoc sharedLoc symLocals concLocals)
    (dst : Nat) {sv : SymVal} {mv : MirVal} (hVal : ValRel loanLoc sharedLoc sv mv) :
    LocalRel loanLoc sharedLoc (updateSymLocal symLocals dst (some sv))
      (updateLocal concLocals dst (some mv)) := by
  intro i sv' hlookup
  unfold updateSymLocal at hlookup
  unfold updateLocal
  cases h : (i == dst) with
  | false =>
    rw [h] at hlookup
    exact hRel i sv' hlookup
  | true =>
    rw [h] at hlookup
    injection hlookup with heq
    subst heq
    exact ⟨mv, rfl, hVal⟩

theorem LocalRel.update_none {loanLoc : Nat → Option Nat} {sharedLoc : Nat → Nat → Prop}
    {symLocals : Nat → Option SymVal} {concLocals : Nat → Option MirVal}
    (hRel : LocalRel loanLoc sharedLoc symLocals concLocals) (dst : Nat) :
    LocalRel loanLoc sharedLoc (updateSymLocal symLocals dst none)
      (updateLocal concLocals dst none) := by
  intro i sv' hlookup
  unfold updateSymLocal at hlookup
  unfold updateLocal
  cases h : (i == dst) with
  | false =>
    rw [h] at hlookup
    exact hRel i sv' hlookup
  | true =>
    rw [h] at hlookup
    cases hlookup

/-- Soundness of symbolic operand evaluation (`evalSymOperand`). -/
theorem evalSymOperand_sound {loanLoc : Nat → Option Nat} {sharedLoc : Nat → Nat → Prop}
    {symLocals symLocals' : Nat → Option SymVal}
    {concLocals : Nat → Option MirVal}
    {op : Operand} {sv : SymVal}
    (hRel : LocalRel loanLoc sharedLoc symLocals concLocals)
    (hEval : evalSymOperand symLocals op = some (sv, symLocals')) :
    ∃ mv concLocals',
      evalOperand concLocals op = some (mv, concLocals') ∧
      ValRel loanLoc sharedLoc sv mv ∧
      LocalRel loanLoc sharedLoc symLocals' concLocals' := by
  cases op with
  | copy src =>
    dsimp [evalSymOperand] at hEval
    cases hsrc : symLocals src.index with
    | none => rw [hsrc] at hEval; cases hEval
    | some sv0 =>
      rw [hsrc] at hEval
      injection hEval with hpair
      injection hpair with hsv hloc
      subst hsv hloc
      cases hRel src.index sv0 hsrc with
      | intro mv hmv =>
        refine ⟨mv, concLocals, ?_, hmv.2, hRel⟩
        dsimp [evalOperand]
        rw [hmv.1]
  | move src =>
    dsimp [evalSymOperand] at hEval
    cases hsrc : symLocals src.index with
    | none => rw [hsrc] at hEval; cases hEval
    | some sv0 =>
      rw [hsrc] at hEval
      injection hEval with hpair
      injection hpair with hsv hloc
      subst hsv hloc
      cases hRel src.index sv0 hsrc with
      | intro mv hmv =>
        refine ⟨mv, updateLocal concLocals src.index none, ?_, hmv.2,
          LocalRel.update_none hRel src.index⟩
        dsimp [evalOperand]
        rw [hmv.1]
  | constVal mv0 =>
    dsimp [evalSymOperand] at hEval
    cases mv0 with
    | usize n =>
      injection hEval with hpair
      injection hpair with hsv hloc
      subst hsv hloc
      exact ⟨.usize n, concLocals, rfl, rfl, hRel⟩
    | bool b =>
      injection hEval with hpair
      injection hpair with hsv hloc
      subst hsv hloc
      exact ⟨.bool b, concLocals, rfl, rfl, hRel⟩
    | unit =>
      injection hEval with hpair
      injection hpair with hsv hloc
      subst hsv hloc
      exact ⟨.unit, concLocals, rfl, rfl, hRel⟩
    | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ =>
      cases hEval

theorem evalSymOperand_borrows {locals locals' : Nat → Option SymVal}
    {loans : Nat → Option LoanEntry} {op : Operand} {sv : SymVal}
    (hBorrows : ∀ i lid, locals i = some (.borrow lid) → ∃ e, loans lid = some e)
    (hEval : evalSymOperand locals op = some (sv, locals')) :
    (∀ lid, sv = .borrow lid → ∃ e, loans lid = some e) ∧
    (∀ i lid, locals' i = some (.borrow lid) → ∃ e, loans lid = some e) := by
  cases op with
  | copy src =>
    dsimp [evalSymOperand] at hEval
    cases hsrc : locals src.index with
    | none => rw [hsrc] at hEval; cases hEval
    | some sv0 =>
      rw [hsrc] at hEval
      injection hEval with hpair
      injection hpair with hsv hloc
      subst hsv hloc
      refine ⟨fun lid heq => ?_, hBorrows⟩
      subst heq
      exact hBorrows src.index lid hsrc
  | move src =>
    dsimp [evalSymOperand] at hEval
    cases hsrc : locals src.index with
    | none => rw [hsrc] at hEval; cases hEval
    | some sv0 =>
      rw [hsrc] at hEval
      injection hEval with hpair
      injection hpair with hsv hloc
      subst hsv hloc
      refine ⟨fun lid heq => ?_, ?_⟩
      · subst heq
        exact hBorrows src.index lid hsrc
      · intro i lid hlookup
        unfold updateSymLocal at hlookup
        cases h : (i == src.index) with
        | false =>
          rw [h] at hlookup
          exact hBorrows i lid hlookup
        | true =>
          rw [h] at hlookup
          cases hlookup
  | constVal mv0 =>
    dsimp [evalSymOperand] at hEval
    cases mv0 with
    | usize n =>
      injection hEval with hpair
      injection hpair with hsv hloc
      subst hsv hloc
      exact ⟨(by intro _ h; cases h), hBorrows⟩
    | bool b =>
      injection hEval with hpair
      injection hpair with hsv hloc
      subst hsv hloc
      exact ⟨(by intro _ h; cases h), hBorrows⟩
    | unit =>
      injection hEval with hpair
      injection hpair with hsv hloc
      subst hsv hloc
      exact ⟨(by intro _ h; cases h), hBorrows⟩
    | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ =>
      cases hEval

theorem localBorrows_update_some {locals : Nat → Option SymVal}
    {loans : Nat → Option LoanEntry} (dst : Nat) {sv : SymVal}
    (hBorrows : ∀ i lid, locals i = some (.borrow lid) → ∃ e, loans lid = some e)
    (hSv : ∀ lid, sv = .borrow lid → ∃ e, loans lid = some e) :
    ∀ i lid, updateSymLocal locals dst (some sv) i = some (.borrow lid) →
      ∃ e, loans lid = some e := by
  intro i lid hlookup
  unfold updateSymLocal at hlookup
  cases h : (i == dst) with
  | false =>
    rw [h] at hlookup
    exact hBorrows i lid hlookup
  | true =>
    rw [h] at hlookup
    injection hlookup with heq
    exact hSv lid heq

theorem localBorrows_update_none {locals : Nat → Option SymVal}
    {loans : Nat → Option LoanEntry} (dst : Nat)
    (hBorrows : ∀ i lid, locals i = some (.borrow lid) → ∃ e, loans lid = some e) :
    ∀ i lid, updateSymLocal locals dst none i = some (.borrow lid) →
      ∃ e, loans lid = some e := by
  intro i lid hlookup
  unfold updateSymLocal at hlookup
  cases h : (i == dst) with
  | false =>
    rw [h] at hlookup
    exact hBorrows i lid hlookup
  | true =>
    rw [h] at hlookup
    cases hlookup

theorem loans_some_updateLoan {loans : Nat → Option LoanEntry}
    (k : Nat) (e' : LoanEntry) {lid : Nat}
    (h : ∃ e, loans lid = some e) :
    ∃ e, updateLoan loans k (some e') lid = some e := by
  unfold updateLoan
  cases lid == k with
  | false => exact h
  | true => exact ⟨e', rfl⟩

/-- Soundness of symbolic binary comparison and bitwise evaluation
    (`evalSymBinOp`). -/
theorem evalSymBinOp_sound {loanLoc : Nat → Option Nat} {sharedLoc : Nat → Nat → Prop}
    {op : BinOp} {sv1 sv2 res : SymVal} {mv1 mv2 : MirVal}
    (hVal1 : ValRel loanLoc sharedLoc sv1 mv1)
    (hVal2 : ValRel loanLoc sharedLoc sv2 mv2)
    (hBin : evalSymBinOp op sv1 sv2 = some res) :
    ∃ mres, evalBinOp op mv1 mv2 = some mres ∧ ValRel loanLoc sharedLoc res mres := by
  cases sv1 with
  | bool _ | unit | tupleUsizeBool _ _ | refShared _ | borrow _ => cases hBin
  | usize n1 =>
    cases sv2 with
    | bool _ | unit | tupleUsizeBool _ _ | refShared _ | borrow _ => cases hBin
    | usize n2 =>
      subst hVal1 hVal2
      cases op with
      | lt =>
        injection hBin with hres
        subst hres
        exact ⟨.bool (decide (n1 < n2)), rfl, rfl⟩
      | le =>
        injection hBin with hres
        subst hres
        exact ⟨.bool (decide (n1 ≤ n2)), rfl, rfl⟩
      | eq =>
        injection hBin with hres
        subst hres
        exact ⟨.bool (decide (n1 = n2)), rfl, rfl⟩
      | ne =>
        injection hBin with hres
        subst hres
        exact ⟨.bool (decide (n1 ≠ n2)), rfl, rfl⟩
      | gt =>
        injection hBin with hres
        subst hres
        exact ⟨.bool (decide (n2 < n1)), rfl, rfl⟩
      | ge =>
        injection hBin with hres
        subst hres
        exact ⟨.bool (decide (n2 ≤ n1)), rfl, rfl⟩
      | bitAnd =>
        injection hBin with hres
        subst hres
        exact ⟨.usize (Nat.land n1 n2), rfl, rfl⟩
      | bitOr =>
        injection hBin with hres
        subst hres
        exact ⟨.usize (Nat.lor n1 n2), rfl, rfl⟩
      | bitXor =>
        injection hBin with hres
        subst hres
        exact ⟨.usize (Nat.xor n1 n2), rfl, rfl⟩

/-- Soundness of symbolic checked binary arithmetic evaluation
    (`evalSymCheckedBinOp`). -/
theorem evalSymCheckedBinOp_sound {loanLoc : Nat → Option Nat} {sharedLoc : Nat → Nat → Prop}
    {op : CheckedBinOp} {sv1 sv2 res : SymVal} {mv1 mv2 : MirVal}
    (hVal1 : ValRel loanLoc sharedLoc sv1 mv1)
    (hVal2 : ValRel loanLoc sharedLoc sv2 mv2)
    (hBin : evalSymCheckedBinOp op sv1 sv2 = some res) :
    ∃ mres, evalCheckedBinOp op mv1 mv2 = some mres ∧ ValRel loanLoc sharedLoc res mres := by
  cases sv1 with
  | bool _ | unit | tupleUsizeBool _ _ | refShared _ | borrow _ => cases hBin
  | usize n1 =>
    cases sv2 with
    | bool _ | unit | tupleUsizeBool _ _ | refShared _ | borrow _ => cases hBin
    | usize n2 =>
      subst hVal1 hVal2
      cases op with
      | add =>
        injection hBin with hres
        subst hres
        exact ⟨.tupleUsizeBool (n1 + n2) (decide (usizeMax < n1 + n2)), rfl, rfl⟩
      | sub =>
        injection hBin with hres
        subst hres
        exact ⟨.tupleUsizeBool (n1 - n2) (decide (n1 < n2)), rfl, rfl⟩
      | mul =>
        injection hBin with hres
        subst hres
        exact ⟨.tupleUsizeBool (n1 * n2) (decide (usizeMax < n1 * n2)), rfl, rfl⟩

theorem evalSymPureCallee2_sound {loanLoc : Nat → Option Nat} {sharedLoc : Nat → Nat → Prop}
    {callee : PureCallee2} {v1 v2 res : SymVal} {mv1 mv2 : MirVal}
    (hVal1 : ValRel loanLoc sharedLoc v1 mv1)
    (hVal2 : ValRel loanLoc sharedLoc v2 mv2)
    (hCall : evalSymPureCallee2 callee v1 v2 = some res) :
    ∃ mres,
      evalPureCallee2 callee mv1 mv2 = some mres ∧
      ValRel loanLoc sharedLoc res mres := by
  cases v1 with
  | bool _ | unit | tupleUsizeBool _ _ | refShared _ | borrow _ => cases hCall
  | usize x0 =>
    cases v2 with
    | bool _ | unit | tupleUsizeBool _ _ | refShared _ | borrow _ => cases hCall
    | usize y0 =>
      subst hVal1 hVal2
      cases callee with
      | addBounded =>
        injection hCall with hres
        subst hres
        exact ⟨.usize (if decide (x0 ≤ 1000) && decide (y0 ≤ 1000) then x0 + y0 else 0), rfl, rfl⟩
      | absDiff =>
        injection hCall with hres
        subst hres
        exact ⟨.usize (if decide (y0 ≤ x0) then x0 - y0 else y0 - x0), rfl, rfl⟩

/-- Invariant for an active joined loan `lid` (`entry.owners = [.loan falseLid,
    .loan trueLid]`):
    1. `falseLid ≠ trueLid`, `falseLid ≠ lid`, and `trueLid ≠ lid`,
    2. `loans falseLid` and `loans trueLid` are present, frozen, and have
      `owners = []`,
    3. `loanLoc falseLid = some locFalse`, `loanLoc trueLid = some locTrue`, and
      `locFalse ≠ locTrue`,
    4. At the inactive branch's location (`locTrue` when `loc = locFalse`, or
      `locFalse` when `loc = locTrue`), `OwnLoc mem` holds with the inactive
      parent's original value (`mvTrueOrig` or `mvFalseOrig`),
    5. Every other active unfrozen loan `otherLid ≠ lid` has a location
      `locOther` distinct from both `locFalse` and `locTrue`, and has
      `otherEntry.owners = []`,
    6. Applying `entry.back v` to any scalar `v` (`v.toScalarMirVal = some mv`)
      yields `[vFalse, vTrue]` matching `(mv, mvTrueOrig)` when `loc = locFalse`
      and `(mvFalseOrig, mv)` when `loc = locTrue`. -/
def JoinInv (loanLoc : Nat → Option Nat)
    (loans : Nat → Option LoanEntry) (mem : MemState)
    (lid : Nat) (entry : LoanEntry) (falseLid trueLid : Nat) : Prop :=
  ∃ (loc locFalse locTrue : Nat) (falseEntry trueEntry : LoanEntry)
    (mvFalseOrig mvTrueOrig : MirVal),
    falseLid ≠ trueLid ∧
    falseLid ≠ lid ∧
    trueLid ≠ lid ∧
    loanLoc lid = some loc ∧
    loanLoc falseLid = some locFalse ∧
    loanLoc trueLid = some locTrue ∧
    locFalse ≠ locTrue ∧
    loans falseLid = some falseEntry ∧
    loans trueLid = some trueEntry ∧
    falseEntry.frozen = true ∧
    trueEntry.frozen = true ∧
    falseEntry.owners = [] ∧
    trueEntry.owners = [] ∧
    ((loc = locFalse ∧ OwnLoc mem locTrue mvTrueOrig) ∨
     (loc = locTrue ∧ OwnLoc mem locFalse mvFalseOrig)) ∧
    (∀ otherLid otherEntry,
      otherLid ≠ lid →
      loans otherLid = some otherEntry →
      otherEntry.active = true →
      otherEntry.frozen = false →
      otherEntry.owners = [] ∧
      ∀ locOther, loanLoc otherLid = some locOther →
        locOther ≠ locFalse ∧ locOther ≠ locTrue) ∧
    (∀ v mv, v.toScalarMirVal = some mv →
      ∃ vFalse vTrue mvFalse mvTrue,
        entry.back v = [vFalse, vTrue] ∧
        vFalse.toScalarMirVal = some mvFalse ∧
        vTrue.toScalarMirVal = some mvTrue ∧
        (loc = locFalse → mvFalse = mv ∧ mvTrue = mvTrueOrig) ∧
        (loc = locTrue → mvFalse = mvFalseOrig ∧ mvTrue = mv))

/-- Loan and memory correspondence between `sym` and `conc.mem`:
    1. Every active unfrozen loan `lid` holds a scalar `curVal` (`mv`) and owns
      its concrete location `loc` in `conc.mem` (`OwnLoc conc.mem loc mv`),
      and either has `entry.owners = []` or satisfies `JoinInv`.
    2. Distinct active unfrozen loans map to distinct concrete locations in
      `conc.mem`.
    3. When `sym.hasActiveJoin = false`, every active unfrozen loan is a root
      loan (`entry.owners = []`).
    4. Every shared reference location `loc` in `sharedLoc loc n` satisfies
      `ReadOwnLoc conc.mem loc (.usize n)` and is disjoint from every mutable
      loan location in `loanLoc`. -/
structure LoanRel (loanLoc : Nat → Option Nat) (sharedLoc : Nat → Nat → Prop)
    (loans : Nat → Option LoanEntry) (hasActiveJoin : Bool) (mem : MemState) : Prop where
  activeOwn :
    ∀ lid entry,
      loans lid = some entry →
      entry.active = true →
      entry.frozen = false →
      (∃ loc mv,
        loanLoc lid = some loc ∧
        entry.curVal.toScalarMirVal = some mv ∧
        OwnLoc mem loc mv) ∧
      (entry.owners = [] ∨
       ∃ falseLid trueLid,
         entry.owners = [.loan falseLid, .loan trueLid] ∧
         JoinInv loanLoc loans mem lid entry falseLid trueLid)
  disjointActive :
    ∀ lid₁ lid₂ e₁ e₂ loc₁ loc₂,
      lid₁ ≠ lid₂ →
      loans lid₁ = some e₁ → e₁.active = true → e₁.frozen = false →
      loans lid₂ = some e₂ → e₂.active = true → e₂.frozen = false →
      loanLoc lid₁ = some loc₁ →
      loanLoc lid₂ = some loc₂ →
      loc₁ ≠ loc₂
  noJoinOwners :
    hasActiveJoin = false →
      ∀ lid entry,
        loans lid = some entry →
        entry.active = true →
        entry.frozen = false →
        entry.owners = []
  sharedOwn :
    ∀ loc n, sharedLoc loc n → ReadOwnLoc mem loc (.usize n)
  disjointShared :
    ∀ lid locMut locShared n,
      loanLoc lid = some locMut →
      sharedLoc locShared n →
      locMut ≠ locShared

/-- Full simulation relation linking a symbolic state `sym : SymState` and a
    concrete state `conc : MirState` under loan-location map `loanLoc` and
    shared-reference relation `sharedLoc`. -/
structure StateRel (loanLoc : Nat → Option Nat) (sharedLoc : Nat → Nat → Prop)
    (sym : SymState) (conc : MirState) : Prop where
  block_eq : conc.block = sym.block
  stmtIdx_eq : conc.stmtIdx = sym.stmtIdx
  localBorrows : ∀ i lid, sym.locals i = some (.borrow lid) → ∃ e, sym.loans lid = some e
  localRel : LocalRel loanLoc sharedLoc sym.locals conc.locals
  loanRel : LoanRel loanLoc sharedLoc sym.loans sym.hasActiveJoin conc.mem


/-!
## 7. Soundness of Transition Primitives and Universal `evalSym_sound`
-/

theorem JoinInv.of_ownLoc_mono {loanLoc : Nat → Option Nat}
    {loans : Nat → Option LoanEntry} {mem mem' : MemState}
    {lid : Nat} {entry : LoanEntry} {falseLid trueLid : Nat}
    (hMono : ∀ l v, OwnLoc mem l v → OwnLoc mem' l v)
    (hJoin : JoinInv loanLoc loans mem lid entry falseLid trueLid) :
    JoinInv loanLoc loans mem' lid entry falseLid trueLid := by
  have ⟨loc, locFalse, locTrue, falseEntry, trueEntry,
    mvFalseOrig, mvTrueOrig, hneFT, hneFL, hneTL, hloc, hlocF, hlocT,
    hneLoc, hloansF, hloansT, hfrozenF, hfrozenT, hownF, hownT, hbranch,
    hother, hback⟩ := hJoin
  refine ⟨loc, locFalse, locTrue, falseEntry, trueEntry, mvFalseOrig, mvTrueOrig,
    hneFT, hneFL, hneTL, hloc, hlocF, hlocT, hneLoc, hloansF, hloansT,
    hfrozenF, hfrozenT, hownF, hownT, ?_, hother, hback⟩
  cases hbranch with
  | inl h => exact Or.inl ⟨h.1, hMono locTrue mvTrueOrig h.2⟩
  | inr h => exact Or.inr ⟨h.1, hMono locFalse mvFalseOrig h.2⟩

theorem LoanRel.of_readNA {loanLoc : Nat → Option Nat} {sharedLoc : Nat → Nat → Prop}
    {loans : Nat → Option LoanEntry} {hasActiveJoin : Bool} {mem : MemState}
    (locRead : Nat)
    (hLoan : LoanRel loanLoc sharedLoc loans hasActiveJoin mem) :
    LoanRel loanLoc sharedLoc loans hasActiveJoin
      { mem with naReadTs := View.bump mem.naReadTs locRead (mem.curView locRead) } where
  activeOwn lid entry hlookup hact hfrz := by
    have ⟨⟨loc, mv, hloc, hsc, hown⟩, hkind⟩ :=
      hLoan.activeOwn lid entry hlookup hact hfrz
    refine ⟨⟨loc, mv, hloc, hsc, OwnLoc.readNA_preserves hown⟩, ?_⟩
    cases hkind with
    | inl hroot => exact Or.inl hroot
    | inr hjoin =>
      have ⟨falseLid, trueLid, howners, hinv⟩ := hjoin
      exact Or.inr ⟨falseLid, trueLid, howners,
        JoinInv.of_ownLoc_mono (fun _ _ h => OwnLoc.readNA_preserves h) hinv⟩
  disjointActive := hLoan.disjointActive
  noJoinOwners := hLoan.noJoinOwners
  sharedOwn loc n hsh := ReadOwnLoc.readNA_preserves (hLoan.sharedOwn loc n hsh)
  disjointShared := hLoan.disjointShared

theorem LoanRel.update_curVal {loanLoc : Nat → Option Nat} {sharedLoc : Nat → Nat → Prop}
    {loans : Nat → Option LoanEntry} {hasActiveJoin : Bool} {mem : MemState}
    {lid loc : Nat} {entry : LoanEntry} {mvOld mvNew : MirVal} {sv : SymVal}
    (hLoan : LoanRel loanLoc sharedLoc loans hasActiveJoin mem)
    (hlookup : loans lid = some entry)
    (hact : entry.active = true)
    (hfrz : entry.frozen = false)
    (hloc : loanLoc lid = some loc)
    (hOwnOld : OwnLoc mem loc mvOld)
    (hScalarNew : sv.toScalarMirVal = some mvNew) :
    LoanRel loanLoc sharedLoc (updateLoan loans lid (some { entry with curVal := sv }))
      hasActiveJoin (afterWriteNA mem loc mvNew) where
  activeOwn lid' entry' hlookup' hact' hfrz' := by
    unfold updateLoan at hlookup'
    cases hbeq : (lid' == lid) with
    | true =>
      rw [hbeq] at hlookup'
      injection hlookup' with heq'
      have hlid_eq : lid' = lid := of_decide_eq_true hbeq
      subst hlid_eq heq'
      refine ⟨⟨loc, mvNew, hloc, hScalarNew, OwnLoc.afterWriteNA_self hOwnOld mvNew⟩, ?_⟩
      have ⟨_, hkind⟩ := hLoan.activeOwn lid' entry hlookup hact hfrz
      cases hkind with
      | inl hroot => exact Or.inl hroot
      | inr hjoin =>
        have ⟨falseLid, trueLid, howners, hinv⟩ := hjoin
        refine Or.inr ⟨falseLid, trueLid, howners, ?_⟩
        have ⟨loc0, locFalse, locTrue, falseEntry, trueEntry,
          mvFalseOrig, mvTrueOrig, hneFT, hneFL, hneTL, hloc0, hlocF, hlocT,
          hneLoc, hloansF, hloansT, hfrozenF, hfrozenT, hownF, hownT, hbranch,
          hother, hback⟩ := hinv
        have hloc0_eq : loc0 = loc := by
          rw [hloc0] at hloc
          injection hloc
        have hbeqF : (falseLid == lid') = false := decide_eq_false hneFL
        have hbeqT : (trueLid == lid') = false := decide_eq_false hneTL
        refine ⟨loc0, locFalse, locTrue, falseEntry, trueEntry,
          mvFalseOrig, mvTrueOrig, hneFT, hneFL, hneTL, hloc0, hlocF, hlocT,
          hneLoc, ?_, ?_, hfrozenF, hfrozenT, hownF, hownT, ?_, ?_, hback⟩
        · unfold updateLoan; rw [hbeqF]; exact hloansF
        · unfold updateLoan; rw [hbeqT]; exact hloansT
        · cases hbranch with
          | inl h =>
            have hneT : locTrue ≠ loc := by
              intro heq; exact hneLoc (Eq.trans (Eq.trans h.1.symm hloc0_eq) heq.symm)
            exact Or.inl ⟨h.1, OwnLoc.afterWriteNA_other hneT h.2 mvNew⟩
          | inr h =>
            have hneF : locFalse ≠ loc := by
              intro heq; exact hneLoc (Eq.trans (Eq.trans heq hloc0_eq.symm) h.1)
            exact Or.inr ⟨h.1, OwnLoc.afterWriteNA_other hneF h.2 mvNew⟩
        · intro otherLid otherEntry hneOther hotherLookup hotherAct hotherFrz
          unfold updateLoan at hotherLookup
          have hbeqO : (otherLid == lid') = false := decide_eq_false hneOther
          rw [hbeqO] at hotherLookup
          exact hother otherLid otherEntry hneOther hotherLookup hotherAct hotherFrz
    | false =>
      rw [hbeq] at hlookup'
      have hne : lid' ≠ lid := of_decide_eq_false hbeq
      have ⟨⟨loc', mv', hloc', hsc', hown'⟩, hkind'⟩ :=
        hLoan.activeOwn lid' entry' hlookup' hact' hfrz'
      have hneLoc' : loc' ≠ loc :=
        hLoan.disjointActive lid' lid entry' entry loc' loc
          hne hlookup' hact' hfrz' hlookup hact hfrz hloc' hloc
      refine ⟨⟨loc', mv', hloc', hsc', OwnLoc.afterWriteNA_other hneLoc' hown' mvNew⟩, ?_⟩
      cases hkind' with
      | inl hroot => exact Or.inl hroot
      | inr hjoin =>
        have ⟨falseLid, trueLid, howners, hinv⟩ := hjoin
        refine Or.inr ⟨falseLid, trueLid, howners, ?_⟩
        have ⟨loc0, locFalse, locTrue, falseEntry, trueEntry,
          mvFalseOrig, mvTrueOrig, hneFT, hneFL, hneTL, hloc0, hlocF, hlocT,
          hneLoc, hloansF, hloansT, hfrozenF, hfrozenT, hownF, hownT, hbranch,
          hother, hback⟩ := hinv
        have hneFL_lid : falseLid ≠ lid := by
          intro heq; subst heq
          rw [hlookup] at hloansF
          injection hloansF with heF
          subst heF
          rw [hfrz] at hfrozenF
          cases hfrozenF
        have hneTL_lid : trueLid ≠ lid := by
          intro heq; subst heq
          rw [hlookup] at hloansT
          injection hloansT with heT
          subst heT
          rw [hfrz] at hfrozenT
          cases hfrozenT
        have hbeqF : (falseLid == lid) = false := decide_eq_false hneFL_lid
        have hbeqT : (trueLid == lid) = false := decide_eq_false hneTL_lid
        have hother_lid := hother lid entry hne.symm hlookup hact hfrz
        have hloc_disj := hother_lid.2 loc hloc
        refine ⟨loc0, locFalse, locTrue, falseEntry, trueEntry,
          mvFalseOrig, mvTrueOrig, hneFT, hneFL, hneTL, hloc0, hlocF, hlocT,
          hneLoc, ?_, ?_, hfrozenF, hfrozenT, hownF, hownT, ?_, ?_, hback⟩
        · unfold updateLoan; rw [hbeqF]; exact hloansF
        · unfold updateLoan; rw [hbeqT]; exact hloansT
        · cases hbranch with
          | inl h =>
            exact Or.inl ⟨h.1, OwnLoc.afterWriteNA_other hloc_disj.2.symm h.2 mvNew⟩
          | inr h =>
            exact Or.inr ⟨h.1, OwnLoc.afterWriteNA_other hloc_disj.1.symm h.2 mvNew⟩
        · intro otherLid otherEntry hneOther hotherLookup hotherAct hotherFrz
          unfold updateLoan at hotherLookup
          cases hbeqO : (otherLid == lid) with
          | false =>
            rw [hbeqO] at hotherLookup
            exact hother otherLid otherEntry hneOther hotherLookup hotherAct hotherFrz
          | true =>
            rw [hbeqO] at hotherLookup
            injection hotherLookup with heqO
            have hO_eq : otherLid = lid := of_decide_eq_true hbeqO
            subst hO_eq heqO
            exact hother_lid
  disjointActive lid₁ lid₂ e₁ e₂ loc₁ loc₂ hne h1 ha1 hf1 h2 ha2 hf2 hloc1 hloc2 := by
    unfold updateLoan at h1 h2
    cases hb1 : (lid₁ == lid) with
    | true =>
      rw [hb1] at h1
      injection h1 with he1
      have h1_eq : lid₁ = lid := of_decide_eq_true hb1
      subst h1_eq he1
      have hb2 : (lid₂ == lid₁) = false := decide_eq_false hne.symm
      rw [hb2] at h2
      exact hLoan.disjointActive lid₁ lid₂ entry e₂ loc₁ loc₂
        hne hlookup hact hfrz h2 ha2 hf2 hloc1 hloc2
    | false =>
      rw [hb1] at h1
      cases hb2 : (lid₂ == lid) with
      | true =>
        rw [hb2] at h2
        injection h2 with he2
        have h2_eq : lid₂ = lid := of_decide_eq_true hb2
        subst h2_eq he2
        exact hLoan.disjointActive lid₁ lid₂ e₁ entry loc₁ loc₂
          hne h1 ha1 hf1 hlookup hact hfrz hloc1 hloc2
      | false =>
        rw [hb2] at h2
        exact hLoan.disjointActive lid₁ lid₂ e₁ e₂ loc₁ loc₂
          hne h1 ha1 hf1 h2 ha2 hf2 hloc1 hloc2
  noJoinOwners hno lid' entry' hlookup' hact' hfrz' := by
    unfold updateLoan at hlookup'
    cases hbeq : (lid' == lid) with
    | true =>
      rw [hbeq] at hlookup'
      injection hlookup' with heq'
      have hlid_eq : lid' = lid := of_decide_eq_true hbeq
      subst hlid_eq heq'
      exact hLoan.noJoinOwners hno lid' entry hlookup hact hfrz
    | false =>
      rw [hbeq] at hlookup'
      exact hLoan.noJoinOwners hno lid' entry' hlookup' hact' hfrz'
  sharedOwn locShared n hsh :=
    ReadOwnLoc.afterWriteNA_other
      (hLoan.disjointShared lid loc locShared n hloc hsh).symm
      (hLoan.sharedOwn locShared n hsh)
      mvNew
  disjointShared := hLoan.disjointShared

/-- Soundness of `evalReturn`. -/
theorem evalReturn_sound {loanLoc : Nat → Option Nat} {sharedLoc : Nat → Nat → Prop}
    {body : MirBody} {sym : SymState} {conc : MirState} {mv : MirVal}
    (hState : StateRel loanLoc sharedLoc sym conc)
    (hRet : evalReturn body sym = some mv) :
    SafeAndReturns body conc mv := by
  unfold evalReturn at hRet
  cases hbb : body.blocks[sym.block]? with
  | none => rw [hbb] at hRet; cases hRet
  | some bb =>
    rw [hbb] at hRet
    dsimp at hRet
    cases hstmt : bb.stmts[sym.stmtIdx]? with
    | some _ => rw [hstmt] at hRet; cases hRet
    | none =>
      rw [hstmt] at hRet
      cases hterm : bb.terminator with
      | goto _ | unreachable | callAtomicLoad _ _ _ _ | switchInt _ _ _
      | assertNotOverflow _ _ | callPure2 _ _ _ _ _ =>
        rw [hterm] at hRet; cases hRet
      | return_ =>
        rw [hterm] at hRet
        dsimp at hRet
        cases hloc0 : sym.locals 0 with
        | none => rw [hloc0] at hRet; cases hRet
        | some sv0 =>
          rw [hloc0] at hRet
          have ⟨mv0, hconc0, hval0⟩ := hState.localRel 0 sv0 hloc0
          have hmv_eq : mv0 = mv := ValRel.toScalarMirVal_eq hval0 hRet
          subst hmv_eq
          refine SafeAndReturns.of_terminated ?_
          unfold evalMirStep
          rw [hState.block_eq, hbb]
          dsimp
          rw [hState.stmtIdx_eq, hstmt]
          dsimp
          rw [hterm]
          dsimp [evalMirTerminator]
          rw [hconc0]

/-- Soundness of symbolic single-statement execution (`evalSymStmt`). -/
theorem evalSymStmt_sound {loanLoc : Nat → Option Nat} {sharedLoc : Nat → Nat → Prop}
    {sym sym' : SymState} {conc : MirState} {stmt : Stmt}
    (hState : StateRel loanLoc sharedLoc sym conc)
    (hStmt : evalSymStmt sym stmt = some sym') :
    ∃ conc',
      evalMirStmt conc stmt = .step () conc' ∧
      StateRel loanLoc sharedLoc sym' conc' := by
  cases stmt with
  | assign dst rv =>
    cases rv with
    | use op =>
      dsimp [evalSymStmt] at hStmt
      cases hOp : evalSymOperand sym.locals op with
      | none => rw [hOp] at hStmt; cases hStmt
      | some p =>
        cases p with
        | mk sv locals' =>
          rw [hOp] at hStmt
          injection hStmt with hsym'
          subst hsym'
          have ⟨mv, concLocals', hConcOp, hVal, hLocRel'⟩ :=
            evalSymOperand_sound hState.localRel hOp
          have hBor := evalSymOperand_borrows hState.localBorrows hOp
          refine ⟨{ conc with
            locals := updateLocal concLocals' dst.index (some mv)
            stmtIdx := conc.stmtIdx + 1
          }, ?_, ?_⟩
          · dsimp [evalMirStmt]
            rw [hConcOp]
          · exact {
              block_eq := hState.block_eq
              stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
              localBorrows := localBorrows_update_some dst.index hBor.2 hBor.1
              localRel := LocalRel.update_some hLocRel' dst.index hVal
              loanRel := hState.loanRel
            }
    | deref src =>
      dsimp [evalSymStmt] at hStmt
      cases hsrc : sym.locals src.index with
      | none => rw [hsrc] at hStmt; cases hStmt
      | some svSrc =>
        rw [hsrc] at hStmt
        cases svSrc with
        | usize _ | bool _ | unit | tupleUsizeBool _ _ => cases hStmt
        | refShared n =>
          dsimp at hStmt
          injection hStmt with hsym'
          subst hsym'
          have ⟨mvSrc, hconcSrc, hvalSrc⟩ := hState.localRel src.index (.refShared n) hsrc
          have ⟨loc, hshLoc, hmvSrc⟩ := hvalSrc
          subst hmvSrc
          have hReadOwn := hState.loanRel.sharedOwn loc n hshLoc
          have hRead := ReadOwnLoc.readNA_eq hReadOwn
          refine ⟨{ conc with
            locals := updateLocal conc.locals dst.index (some (.usize n))
            mem := { conc.mem with naReadTs := View.bump conc.mem.naReadTs loc (conc.mem.curView loc) }
            stmtIdx := conc.stmtIdx + 1
          }, ?_, ?_⟩
          · dsimp [evalMirStmt]
            rw [hconcSrc]
            dsimp
            rw [hRead]
          · exact {
              block_eq := hState.block_eq
              stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
              localBorrows := localBorrows_update_some dst.index hState.localBorrows
                (fun _ heq => by cases heq)
              localRel := LocalRel.update_some hState.localRel dst.index rfl
              loanRel := LoanRel.of_readNA loc hState.loanRel
            }
        | borrow lid =>
          dsimp at hStmt
          cases hloan : sym.loans lid with
          | none => rw [hloan] at hStmt; cases hStmt
          | some entry =>
            rw [hloan] at hStmt
            dsimp at hStmt
            cases hact : entry.active with
            | false => rw [hact] at hStmt; cases hStmt
            | true =>
              rw [hact] at hStmt
              cases hfrz : entry.frozen with
              | true => rw [hfrz] at hStmt; cases hStmt
              | false =>
                rw [hfrz] at hStmt
                dsimp at hStmt
                injection hStmt with hsym'
                subst hsym'
                have ⟨mvSrc, hconcSrc, hvalSrc⟩ := hState.localRel src.index (.borrow lid) hsrc
                have ⟨loc1, hloc1, hmvSrc⟩ := hvalSrc
                subst hmvSrc
                have ⟨⟨loc, mv, hloc, hsc, hown⟩, _⟩ :=
                  hState.loanRel.activeOwn lid entry hloan hact hfrz
                rw [hloc] at hloc1
                injection hloc1 with hloc_eq
                subst hloc_eq
                have hRead := OwnLoc.readNA_eq hown
                refine ⟨{ conc with
                  locals := updateLocal conc.locals dst.index (some mv)
                  mem := { conc.mem with naReadTs := View.bump conc.mem.naReadTs loc (conc.mem.curView loc) }
                  stmtIdx := conc.stmtIdx + 1
                }, ?_, ?_⟩
                · dsimp [evalMirStmt]
                  rw [hconcSrc]
                  dsimp
                  rw [hRead]
                · exact {
                    block_eq := hState.block_eq
                    stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
                    localBorrows := localBorrows_update_some dst.index hState.localBorrows
                      (fun lid' heq => False.elim (SymVal.not_borrow_of_toScalarMirVal hsc lid' heq))
                    localRel := LocalRel.update_some hState.localRel dst.index
                      (ValRel.of_toScalarMirVal loanLoc sharedLoc hsc)
                    loanRel := LoanRel.of_readNA loc hState.loanRel
                  }
    | proj0 src =>
      dsimp [evalSymStmt] at hStmt
      cases hsrc : sym.locals src.index with
      | none => rw [hsrc] at hStmt; cases hStmt
      | some svSrc =>
        rw [hsrc] at hStmt
        cases svSrc with
        | usize _ | bool _ | unit | refShared _ | borrow _ => cases hStmt
        | tupleUsizeBool val ov =>
          dsimp at hStmt
          injection hStmt with hsym'
          subst hsym'
          have ⟨mvSrc, hconcSrc, hvalSrc⟩ :=
            hState.localRel src.index (.tupleUsizeBool val ov) hsrc
          subst hvalSrc
          refine ⟨{ conc with
            locals := updateLocal conc.locals dst.index (some (.usize val))
            stmtIdx := conc.stmtIdx + 1
          }, ?_, ?_⟩
          · dsimp [evalMirStmt]
            rw [hconcSrc]
          · exact {
              block_eq := hState.block_eq
              stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
              localBorrows := localBorrows_update_some dst.index hState.localBorrows
                (fun _ heq => by cases heq)
              localRel := LocalRel.update_some hState.localRel dst.index rfl
              loanRel := hState.loanRel
            }
    | proj1 src =>
      dsimp [evalSymStmt] at hStmt
      cases hsrc : sym.locals src.index with
      | none => rw [hsrc] at hStmt; cases hStmt
      | some svSrc =>
        rw [hsrc] at hStmt
        cases svSrc with
        | usize _ | bool _ | unit | refShared _ | borrow _ => cases hStmt
        | tupleUsizeBool val ov =>
          dsimp at hStmt
          injection hStmt with hsym'
          subst hsym'
          have ⟨mvSrc, hconcSrc, hvalSrc⟩ :=
            hState.localRel src.index (.tupleUsizeBool val ov) hsrc
          subst hvalSrc
          refine ⟨{ conc with
            locals := updateLocal conc.locals dst.index (some (.bool ov))
            stmtIdx := conc.stmtIdx + 1
          }, ?_, ?_⟩
          · dsimp [evalMirStmt]
            rw [hconcSrc]
          · exact {
              block_eq := hState.block_eq
              stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
              localBorrows := localBorrows_update_some dst.index hState.localBorrows
                (fun _ heq => by cases heq)
              localRel := LocalRel.update_some hState.localRel dst.index rfl
              loanRel := hState.loanRel
            }
    | binaryOp op lhs rhs =>
      dsimp [evalSymStmt] at hStmt
      cases hOp1 : evalSymOperand sym.locals lhs with
      | none => rw [hOp1] at hStmt; cases hStmt
      | some p1 =>
        cases p1 with
        | mk v1 locals1 =>
          rw [hOp1] at hStmt
          dsimp at hStmt
          cases hOp2 : evalSymOperand locals1 rhs with
          | none => rw [hOp2] at hStmt; cases hStmt
          | some p2 =>
            cases p2 with
            | mk v2 locals2 =>
              rw [hOp2] at hStmt
              dsimp at hStmt
              cases hBin : evalSymBinOp op v1 v2 with
              | none => rw [hBin] at hStmt; cases hStmt
              | some res =>
                rw [hBin] at hStmt
                injection hStmt with hsym'
                subst hsym'
                have ⟨mv1, concLocals1, hConcOp1, hVal1, hLocRel1⟩ :=
                  evalSymOperand_sound hState.localRel hOp1
                have ⟨mv2, concLocals2, hConcOp2, hVal2, hLocRel2⟩ :=
                  evalSymOperand_sound hLocRel1 hOp2
                have ⟨mres, hConcBin, hValRes⟩ :=
                  evalSymBinOp_sound hVal1 hVal2 hBin
                have hBor1 := evalSymOperand_borrows hState.localBorrows hOp1
                have hBor2 := evalSymOperand_borrows hBor1.2 hOp2
                have hResNotBorrow : ∀ lid, res = .borrow lid → False := by
                  intro lid heq
                  subst heq
                  cases v1 with
                  | bool _ | unit | tupleUsizeBool _ _ | refShared _ | borrow _ => cases hBin
                  | usize _ =>
                    cases v2 with
                    | bool _ | unit | tupleUsizeBool _ _ | refShared _ | borrow _ => cases hBin
                    | usize _ =>
                      cases op <;> cases hBin
                refine ⟨{ conc with
                  locals := updateLocal concLocals2 dst.index (some mres)
                  stmtIdx := conc.stmtIdx + 1
                }, ?_, ?_⟩
                · dsimp [evalMirStmt]
                  rw [hConcOp1]
                  dsimp
                  rw [hConcOp2]
                  dsimp
                  rw [hConcBin]
                · exact {
                    block_eq := hState.block_eq
                    stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
                    localBorrows := localBorrows_update_some dst.index hBor2.2
                      (fun lid h => False.elim (hResNotBorrow lid h))
                    localRel := LocalRel.update_some hLocRel2 dst.index hValRes
                    loanRel := hState.loanRel
                  }
    | checkedBinaryOp op lhs rhs =>
      dsimp [evalSymStmt] at hStmt
      cases hOp1 : evalSymOperand sym.locals lhs with
      | none => rw [hOp1] at hStmt; cases hStmt
      | some p1 =>
        cases p1 with
        | mk v1 locals1 =>
          rw [hOp1] at hStmt
          dsimp at hStmt
          cases hOp2 : evalSymOperand locals1 rhs with
          | none => rw [hOp2] at hStmt; cases hStmt
          | some p2 =>
            cases p2 with
            | mk v2 locals2 =>
              rw [hOp2] at hStmt
              dsimp at hStmt
              cases hBin : evalSymCheckedBinOp op v1 v2 with
              | none => rw [hBin] at hStmt; cases hStmt
              | some res =>
                rw [hBin] at hStmt
                injection hStmt with hsym'
                subst hsym'
                have ⟨mv1, concLocals1, hConcOp1, hVal1, hLocRel1⟩ :=
                  evalSymOperand_sound hState.localRel hOp1
                have ⟨mv2, concLocals2, hConcOp2, hVal2, hLocRel2⟩ :=
                  evalSymOperand_sound hLocRel1 hOp2
                have ⟨mres, hConcBin, hValRes⟩ :=
                  evalSymCheckedBinOp_sound hVal1 hVal2 hBin
                have hBor1 := evalSymOperand_borrows hState.localBorrows hOp1
                have hBor2 := evalSymOperand_borrows hBor1.2 hOp2
                have hResNotBorrow : ∀ lid, res = .borrow lid → False := by
                  intro lid heq
                  subst heq
                  cases v1 with
                  | bool _ | unit | tupleUsizeBool _ _ | refShared _ | borrow _ => cases hBin
                  | usize _ =>
                    cases v2 with
                    | bool _ | unit | tupleUsizeBool _ _ | refShared _ | borrow _ => cases hBin
                    | usize _ =>
                      cases op <;> cases hBin
                refine ⟨{ conc with
                  locals := updateLocal concLocals2 dst.index (some mres)
                  stmtIdx := conc.stmtIdx + 1
                }, ?_, ?_⟩
                · dsimp [evalMirStmt]
                  rw [hConcOp1]
                  dsimp
                  rw [hConcOp2]
                  dsimp
                  rw [hConcBin]
                · exact {
                    block_eq := hState.block_eq
                    stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
                    localBorrows := localBorrows_update_some dst.index hBor2.2
                      (fun lid h => False.elim (hResNotBorrow lid h))
                    localRel := LocalRel.update_some hLocRel2 dst.index hValRes
                    loanRel := hState.loanRel
                  }
  | assignDeref dst op =>
    dsimp [evalSymStmt] at hStmt
    cases hOp : evalSymOperand sym.locals op with
    | none => rw [hOp] at hStmt; cases hStmt
    | some p1 =>
      cases p1 with
      | mk sv locals1 =>
        rw [hOp] at hStmt
        dsimp at hStmt
        cases hsc : sv.toScalarMirVal with
        | none => rw [hsc] at hStmt; cases hStmt
        | some mvNew =>
          rw [hsc] at hStmt
          cases hdst : locals1 dst.index with
          | none => rw [hdst] at hStmt; cases hStmt
          | some svDst =>
            rw [hdst] at hStmt
            cases svDst with
            | usize _ | bool _ | unit | tupleUsizeBool _ _ | refShared _ => cases hStmt
            | borrow lid =>
              dsimp at hStmt
              cases hloan : sym.loans lid with
              | none => rw [hloan] at hStmt; cases hStmt
              | some entry =>
                rw [hloan] at hStmt
                dsimp at hStmt
                cases hact : entry.active with
                | false => rw [hact] at hStmt; cases hStmt
                | true =>
                  rw [hact] at hStmt
                  cases hfrz : entry.frozen with
                  | true => rw [hfrz] at hStmt; cases hStmt
                  | false =>
                    rw [hfrz] at hStmt
                    dsimp at hStmt
                    injection hStmt with hsym'
                    subst hsym'
                    have ⟨mvOp, concLocals1, hConcOp, hValOp, hLocRel1⟩ :=
                      evalSymOperand_sound hState.localRel hOp
                    have hmv_eq : mvOp = mvNew := ValRel.toScalarMirVal_eq hValOp hsc
                    subst hmv_eq
                    have ⟨mvDst, hconcDst, hvalDst⟩ := hLocRel1 dst.index (.borrow lid) hdst
                    have ⟨loc1, hloc1, hmvDst⟩ := hvalDst
                    subst hmvDst
                    have ⟨⟨loc, mvOld, hloc, _, hownOld⟩, _⟩ :=
                      hState.loanRel.activeOwn lid entry hloan hact hfrz
                    rw [hloc] at hloc1
                    injection hloc1 with hloc_eq
                    subst hloc_eq
                    have hWrite := OwnLoc.writeNA_eq hownOld mvOp
                    have hBor := evalSymOperand_borrows hState.localBorrows hOp
                    refine ⟨{ conc with
                      locals := concLocals1
                      mem := afterWriteNA conc.mem loc mvOp
                      stmtIdx := conc.stmtIdx + 1
                    }, ?_, ?_⟩
                    · dsimp [evalMirStmt]
                      rw [hConcOp]
                      dsimp
                      rw [hconcDst]
                      dsimp
                      rw [hWrite]
                    · have hentry_eq :
                          { entry with curVal := sv, frozen := false, active := true } =
                          { entry with curVal := sv } := by
                        cases entry; dsimp at hact hfrz; dsimp; subst hact hfrz; rfl
                      exact {
                        block_eq := hState.block_eq
                        stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
                        localBorrows := by
                          dsimp
                          rw [hentry_eq]
                          exact fun i lid' hi =>
                            loans_some_updateLoan lid { entry with curVal := sv } (hBor.2 i lid' hi)
                        localRel := hLocRel1
                        loanRel := by
                          dsimp
                          rw [hentry_eq]
                          exact LoanRel.update_curVal hState.loanRel hloan hact hfrz
                            hloc hownOld hsc
                      }
  | storageLive loc =>
    dsimp [evalSymStmt] at hStmt
    injection hStmt with hsym'
    subst hsym'
    refine ⟨{ conc with
      locals := updateLocal conc.locals loc.index none
      stmtIdx := conc.stmtIdx + 1
    }, rfl, ?_⟩
    exact {
      block_eq := hState.block_eq
      stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
      localBorrows := localBorrows_update_none loc.index hState.localBorrows
      localRel := LocalRel.update_none hState.localRel loc.index
      loanRel := hState.loanRel
    }
  | storageDead loc =>
    dsimp [evalSymStmt] at hStmt
    injection hStmt with hsym'
    subst hsym'
    refine ⟨{ conc with
      locals := updateLocal conc.locals loc.index none
      stmtIdx := conc.stmtIdx + 1
    }, rfl, ?_⟩
    exact {
      block_eq := hState.block_eq
      stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
      localBorrows := localBorrows_update_none loc.index hState.localBorrows
      localRel := LocalRel.update_none hState.localRel loc.index
      loanRel := hState.loanRel
    }
  | nop =>
    dsimp [evalSymStmt] at hStmt
    injection hStmt with hsym'
    subst hsym'
    refine ⟨{ conc with stmtIdx := conc.stmtIdx + 1 }, rfl, ?_⟩
    exact {
      block_eq := hState.block_eq
      stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
      localBorrows := hState.localBorrows
      localRel := hState.localRel
      loanRel := hState.loanRel
    }

/-- Soundness of `evalSymStep` (single statement, `Terminator.goto`, or
    `Terminator.assertNotOverflow` when `overflow = false`). -/
theorem evalSymStep_sound {loanLoc : Nat → Option Nat} {sharedLoc : Nat → Nat → Prop}
    {body : MirBody} {sym sym' : SymState} {conc : MirState}
    (hState : StateRel loanLoc sharedLoc sym conc)
    (hStep : evalSymStep body sym = some (false, sym')) :
    ∃ conc',
      evalMirStep body conc = .step () conc' ∧
      StateRel loanLoc sharedLoc sym' conc' := by
  unfold evalSymStep at hStep
  cases hbb : body.blocks[sym.block]? with
  | none => rw [hbb] at hStep; cases hStep
  | some bb =>
    rw [hbb] at hStep
    dsimp at hStep
    cases hstmt : bb.stmts[sym.stmtIdx]? with
    | some stmt =>
      rw [hstmt] at hStep
      dsimp at hStep
      cases hSymStmt : evalSymStmt sym stmt with
      | none => rw [hSymStmt] at hStep; cases hStep
      | some sym1 =>
        rw [hSymStmt] at hStep
        injection hStep with hpair
        injection hpair with _ hsym'
        subst hsym'
        have ⟨conc', hConcStmt, hState'⟩ := evalSymStmt_sound hState hSymStmt
        refine ⟨conc', ?_, hState'⟩
        unfold evalMirStep
        rw [hState.block_eq, hbb]
        dsimp
        rw [hState.stmtIdx_eq, hstmt]
        exact hConcStmt
    | none =>
      rw [hstmt] at hStep
      dsimp at hStep
      cases hterm : bb.terminator with
      | return_ | unreachable | callAtomicLoad _ _ _ _ | switchInt _ _ _ =>
        rw [hterm] at hStep; cases hStep
      | goto target =>
        rw [hterm] at hStep
        injection hStep with hpair
        injection hpair with _ hsym'
        subst hsym'
        refine ⟨{ conc with block := target.index, stmtIdx := 0 }, ?_, ?_⟩
        · unfold evalMirStep
          rw [hState.block_eq, hbb]
          dsimp
          rw [hState.stmtIdx_eq, hstmt]
          dsimp
          rw [hterm]
          rfl
        · exact {
            block_eq := rfl
            stmtIdx_eq := rfl
            localBorrows := hState.localBorrows
            localRel := hState.localRel
            loanRel := hState.loanRel
          }
      | assertNotOverflow tupleLocal target =>
        rw [hterm] at hStep
        dsimp at hStep
        cases hloc : sym.locals tupleLocal.index with
        | none => rw [hloc] at hStep; cases hStep
        | some sv =>
          rw [hloc] at hStep
          cases sv with
          | usize _ | bool _ | unit | refShared _ | borrow _ => cases hStep
          | tupleUsizeBool val ov =>
            dsimp at hStep
            injection hStep with hpair
            injection hpair with hov hsym'
            subst hov hsym'
            have ⟨mv, hconcLoc, hVal⟩ :=
              hState.localRel tupleLocal.index (.tupleUsizeBool val false) hloc
            subst hVal
            refine ⟨{ conc with block := target.index, stmtIdx := 0 }, ?_, ?_⟩
            · unfold evalMirStep
              rw [hState.block_eq, hbb]
              dsimp
              rw [hState.stmtIdx_eq, hstmt]
              dsimp
              rw [hterm]
              dsimp [evalMirTerminator]
              rw [hconcLoc]
            · exact {
                block_eq := rfl
                stmtIdx_eq := rfl
                localBorrows := hState.localBorrows
                localRel := hState.localRel
                loanRel := hState.loanRel
              }
      | callPure2 dst callee arg1 arg2 target =>
        rw [hterm] at hStep
        dsimp at hStep
        cases hOp1 : evalSymOperand sym.locals arg1 with
        | none => rw [hOp1] at hStep; cases hStep
        | some p1 =>
          cases p1 with
          | mk v1 locals1 =>
            rw [hOp1] at hStep
            dsimp at hStep
            cases hOp2 : evalSymOperand locals1 arg2 with
            | none => rw [hOp2] at hStep; cases hStep
            | some p2 =>
              cases p2 with
              | mk v2 locals2 =>
                rw [hOp2] at hStep
                dsimp at hStep
                cases hCall : evalSymPureCallee2 callee v1 v2 with
                | none => rw [hCall] at hStep; cases hStep
                | some res =>
                  rw [hCall] at hStep
                  injection hStep with hpair
                  injection hpair with _ hsym'
                  subst hsym'
                  have ⟨mv1, concLocals1, hConcOp1, hVal1, hLocRel1⟩ :=
                    evalSymOperand_sound hState.localRel hOp1
                  have ⟨mv2, concLocals2, hConcOp2, hVal2, hLocRel2⟩ :=
                    evalSymOperand_sound hLocRel1 hOp2
                  have ⟨mres, hConcCall, hValRes⟩ :=
                    evalSymPureCallee2_sound hVal1 hVal2 hCall
                  have hBor1 := evalSymOperand_borrows hState.localBorrows hOp1
                  have hBor2 := evalSymOperand_borrows hBor1.2 hOp2
                  have hResNotBorrow : ∀ lid, res = .borrow lid → False := by
                    intro lid heq
                    subst heq
                    cases v1 with
                    | bool _ | unit | tupleUsizeBool _ _ | refShared _ | borrow _ => cases hCall
                    | usize _ =>
                      cases v2 with
                      | bool _ | unit | tupleUsizeBool _ _ | refShared _ | borrow _ => cases hCall
                      | usize _ =>
                        cases callee <;> cases hCall
                  refine ⟨{ conc with
                    locals := updateLocal concLocals2 dst.index (some mres)
                    block := target.index
                    stmtIdx := 0
                  }, ?_, ?_⟩
                  · unfold evalMirStep
                    rw [hState.block_eq, hbb]
                    dsimp
                    rw [hState.stmtIdx_eq, hstmt]
                    dsimp
                    rw [hterm]
                    dsimp [evalMirTerminator]
                    rw [hConcOp1]
                    dsimp
                    rw [hConcOp2]
                    dsimp
                    rw [hConcCall]
                  · exact {
                      block_eq := rfl
                      stmtIdx_eq := rfl
                      localBorrows := localBorrows_update_some dst.index hBor2.2
                        (fun lid h => False.elim (hResNotBorrow lid h))
                      localRel := LocalRel.update_some hLocRel2 dst.index hValRes
                      loanRel := hState.loanRel
                    }

/-- Soundness of `evalBranchStep` (`Terminator.switchInt`). -/
theorem evalBranchStep_sound {loanLoc : Nat → Option Nat} {sharedLoc : Nat → Nat → Prop}
    {body : MirBody} {sym symFalse symTrue : SymState}
    {conc : MirState} {cond : Bool}
    (hState : StateRel loanLoc sharedLoc sym conc)
    (hBranch : evalBranchStep body sym = some (cond, symFalse, symTrue)) :
    ∃ concNext,
      evalMirStep body conc = .step () concNext ∧
      StateRel loanLoc sharedLoc (if cond then symTrue else symFalse) concNext := by
  unfold evalBranchStep at hBranch
  cases hbb : body.blocks[sym.block]? with
  | none => rw [hbb] at hBranch; cases hBranch
  | some bb =>
    rw [hbb] at hBranch
    dsimp at hBranch
    cases hstmt : bb.stmts[sym.stmtIdx]? with
    | some _ => rw [hstmt] at hBranch; cases hBranch
    | none =>
      rw [hstmt] at hBranch
      cases hterm : bb.terminator with
      | return_ | goto _ | unreachable | callAtomicLoad _ _ _ _
      | assertNotOverflow _ _ | callPure2 _ _ _ _ _ =>
        rw [hterm] at hBranch; cases hBranch
      | switchInt discr falseTarget trueTarget =>
        rw [hterm] at hBranch
        dsimp at hBranch
        cases hOp : evalSymOperand sym.locals discr with
        | none => rw [hOp] at hBranch; cases hBranch
        | some p =>
          cases p with
          | mk sv locals' =>
            rw [hOp] at hBranch
            cases sv with
            | usize _ | unit | tupleUsizeBool _ _ | refShared _ | borrow _ => cases hBranch
            | bool b =>
              dsimp at hBranch
              injection hBranch with htuple
              injection htuple with hb hpair
              injection hpair with hF hT
              subst hb hF hT
              have ⟨mv, concLocals', hConcOp, hVal, hLocRel'⟩ :=
                evalSymOperand_sound hState.localRel hOp
              subst hVal
              have hBor := evalSymOperand_borrows hState.localBorrows hOp
              cases b with
              | false =>
                refine ⟨{ conc with
                  locals := concLocals'
                  block := falseTarget.index
                  stmtIdx := 0
                }, ?_, ?_⟩
                · unfold evalMirStep
                  rw [hState.block_eq, hbb]
                  dsimp
                  rw [hState.stmtIdx_eq, hstmt]
                  dsimp
                  rw [hterm]
                  dsimp [evalMirTerminator]
                  rw [hConcOp]
                · exact {
                    block_eq := rfl
                    stmtIdx_eq := rfl
                    localBorrows := hBor.2
                    localRel := hLocRel'
                    loanRel := hState.loanRel
                  }
              | true =>
                refine ⟨{ conc with
                  locals := concLocals'
                  block := trueTarget.index
                  stmtIdx := 0
                }, ?_, ?_⟩
                · unfold evalMirStep
                  rw [hState.block_eq, hbb]
                  dsimp
                  rw [hState.stmtIdx_eq, hstmt]
                  dsimp
                  rw [hterm]
                  dsimp [evalMirTerminator]
                  rw [hConcOp]
                · exact {
                    block_eq := rfl
                    stmtIdx_eq := rfl
                    localBorrows := hBor.2
                    localRel := hLocRel'
                    loanRel := hState.loanRel
                  }

/-- Soundness of `evalEndLoan`: ending an active joined loan `lid` updates and
    unfreezes its parent loans `[.loan falseLid, .loan trueLid]` via
    `entry.back entry.curVal` and preserves `StateRel` with zero concrete
    machine steps. -/
theorem evalEndLoan_sound {loanLoc : Nat → Option Nat} {sharedLoc : Nat → Nat → Prop}
    {sym sym' : SymState} {conc : MirState} {lid : Nat}
    (hState : StateRel loanLoc sharedLoc sym conc)
    (hEnd : evalEndLoan sym lid = some sym') :
    StateRel loanLoc sharedLoc sym' conc := by
  unfold evalEndLoan at hEnd
  cases hloan : sym.loans lid with
  | none => rw [hloan] at hEnd; cases hEnd
  | some entry =>
    rw [hloan] at hEnd
    dsimp at hEnd
    cases hact : entry.active with
    | false => rw [hact] at hEnd; cases hEnd
    | true =>
      rw [hact] at hEnd
      cases hfrz : entry.frozen with
      | true => rw [hfrz] at hEnd; cases hEnd
      | false =>
        rw [hfrz] at hEnd
        dsimp at hEnd
        have ⟨⟨loc, mv, hloc, hsc, hown⟩, hkind⟩ :=
          hState.loanRel.activeOwn lid entry hloan hact hfrz
        cases hkind with
        | inl hroot =>
          rw [hroot] at hEnd; cases hEnd
        | inr hjoin =>
          have ⟨falseLid, trueLid, howners, hinv⟩ := hjoin
          rw [howners] at hEnd
          have ⟨loc0, locFalse, locTrue, falseEntry, trueEntry,
            mvFalseOrig, mvTrueOrig, hneFT, hneFL, hneTL, hloc0, hlocF, hlocT,
            hneLoc, hloansF, hloansT, hfrozenF, hfrozenT, hownF, hownT, hbranch,
            hother, hback⟩ := hinv
          have hloc0_eq : loc0 = loc := by
            rw [hloc0] at hloc; injection hloc
          subst hloc0_eq
          have ⟨vFalse, vTrue, mvFalse, mvTrue, hbackEq, hscF, hscT, hbrF, hbrT⟩ :=
            hback entry.curVal mv hsc
          rw [hbackEq] at hEnd
          dsimp at hEnd
          rw [hloansF, hloansT] at hEnd
          dsimp at hEnd
          injection hEnd with hsym'
          subst hsym'
          have hOwnFalse : OwnLoc conc.mem locFalse mvFalse := by
            cases hbranch with
            | inl h =>
              have hEq := (hbrF h.1).1
              rw [hEq, ← h.1]
              exact hown
            | inr h =>
              have hEq := (hbrT h.1).1
              rw [hEq]
              exact h.2
          have hOwnTrue : OwnLoc conc.mem locTrue mvTrue := by
            cases hbranch with
            | inl h =>
              have hEq := (hbrF h.1).2
              rw [hEq]
              exact h.2
            | inr h =>
              have hEq := (hbrT h.1).2
              rw [hEq, ← h.1]
              exact hown
          let loans1 := updateLoan sym.loans lid
            (some { entry with owners := [OwnerId.loan falseLid, OwnerId.loan trueLid], active := false, frozen := true })
          let loans2 := updateLoan loans1 falseLid (some { falseEntry with curVal := vFalse, frozen := false })
          let loans3 := updateLoan loans2 trueLid (some { trueEntry with curVal := vTrue, frozen := false })
          have hClassify :
              ∀ l e,
                loans3 l = some e →
                e.active = true →
                e.frozen = false →
                (l = trueLid ∧ e = { trueEntry with curVal := vTrue, frozen := false }) ∨
                (l = falseLid ∧ e = { falseEntry with curVal := vFalse, frozen := false }) ∨
                (l ≠ trueLid ∧ l ≠ falseLid ∧ l ≠ lid ∧ sym.loans l = some e) := by
            intro l e hl ha hf
            unfold loans3 loans2 loans1 updateLoan at hl
            cases hbT : (l == trueLid) with
            | true =>
              rw [hbT] at hl
              injection hl with he
              exact Or.inl ⟨of_decide_eq_true hbT, he.symm⟩
            | false =>
              rw [hbT] at hl
              cases hbF : (l == falseLid) with
              | true =>
                rw [hbF] at hl
                injection hl with he
                exact Or.inr (Or.inl ⟨of_decide_eq_true hbF, he.symm⟩)
              | false =>
                rw [hbF] at hl
                cases hbL : (l == lid) with
                | true =>
                  rw [hbL] at hl
                  injection hl with he
                  subst he
                  cases ha
                | false =>
                  rw [hbL] at hl
                  exact Or.inr (Or.inr ⟨of_decide_eq_false hbT, of_decide_eq_false hbF,
                    of_decide_eq_false hbL, hl⟩)
          refine {
            block_eq := hState.block_eq
            stmtIdx_eq := hState.stmtIdx_eq
            localBorrows := fun i lid' hi =>
              loans_some_updateLoan trueLid _
                (loans_some_updateLoan falseLid _
                  (loans_some_updateLoan lid _ (hState.localBorrows i lid' hi)))
            localRel := hState.localRel
            loanRel := {
              activeOwn := by
                intro l e hl ha hf
                cases hClassify l e hl ha hf with
                | inl hT =>
                  have ⟨hl_eq, he_eq⟩ := hT
                  subst hl_eq he_eq
                  exact ⟨⟨locTrue, mvTrue, hlocT, hscT, hOwnTrue⟩, Or.inl hownT⟩
                | inr hRest =>
                  cases hRest with
                  | inl hF =>
                    have ⟨hl_eq, he_eq⟩ := hF
                    subst hl_eq he_eq
                    exact ⟨⟨locFalse, mvFalse, hlocF, hscF, hOwnFalse⟩, Or.inl hownF⟩
                  | inr hO =>
                    have ⟨_, _, hneL, horig⟩ := hO
                    have ⟨hownOrig, _⟩ := hState.loanRel.activeOwn l e horig ha hf
                    exact ⟨hownOrig, Or.inl (hother l e hneL horig ha hf).1⟩
              disjointActive := by
                intro l1 l2 e1 e2 loc1 loc2 hne12 hl1 ha1 hf1 hl2 ha2 hf2 hloc1 hloc2
                cases hClassify l1 e1 hl1 ha1 hf1 with
                | inl h1T =>
                  have ⟨hl1_eq, _⟩ := h1T
                  subst hl1_eq
                  cases hClassify l2 e2 hl2 ha2 hf2 with
                  | inl h2T =>
                    have ⟨hl2_eq, _⟩ := h2T
                    subst hl2_eq
                    exact False.elim (hne12 rfl)
                  | inr h2Rest =>
                    cases h2Rest with
                    | inl h2F =>
                      have ⟨hl2_eq, _⟩ := h2F
                      subst hl2_eq
                      rw [hlocT] at hloc1; injection hloc1 with h1
                      rw [hlocF] at hloc2; injection hloc2 with h2
                      subst h1 h2; exact hneLoc.symm
                    | inr h2O =>
                      have ⟨_, _, hneL2, horig2⟩ := h2O
                      rw [hlocT] at hloc1; injection hloc1 with h1; subst h1
                      exact ((hother l2 e2 hneL2 horig2 ha2 hf2).2 loc2 hloc2).2.symm
                | inr h1Rest =>
                  cases h1Rest with
                  | inl h1F =>
                    have ⟨hl1_eq, _⟩ := h1F
                    subst hl1_eq
                    cases hClassify l2 e2 hl2 ha2 hf2 with
                    | inl h2T =>
                      have ⟨hl2_eq, _⟩ := h2T
                      subst hl2_eq
                      rw [hlocF] at hloc1; injection hloc1 with h1
                      rw [hlocT] at hloc2; injection hloc2 with h2
                      subst h1 h2; exact hneLoc
                    | inr h2Rest =>
                      cases h2Rest with
                      | inl h2F =>
                        have ⟨hl2_eq, _⟩ := h2F
                        subst hl2_eq
                        exact False.elim (hne12 rfl)
                      | inr h2O =>
                        have ⟨_, _, hneL2, horig2⟩ := h2O
                        rw [hlocF] at hloc1; injection hloc1 with h1; subst h1
                        exact ((hother l2 e2 hneL2 horig2 ha2 hf2).2 loc2 hloc2).1.symm
                  | inr h1O =>
                    have ⟨_, _, hneL1, horig1⟩ := h1O
                    cases hClassify l2 e2 hl2 ha2 hf2 with
                    | inl h2T =>
                      have ⟨hl2_eq, _⟩ := h2T
                      subst hl2_eq
                      rw [hlocT] at hloc2; injection hloc2 with h2; subst h2
                      exact ((hother l1 e1 hneL1 horig1 ha1 hf1).2 loc1 hloc1).2
                    | inr h2Rest =>
                      cases h2Rest with
                      | inl h2F =>
                        have ⟨hl2_eq, _⟩ := h2F
                        subst hl2_eq
                        rw [hlocF] at hloc2; injection hloc2 with h2; subst h2
                        exact ((hother l1 e1 hneL1 horig1 ha1 hf1).2 loc1 hloc1).1
                      | inr h2O =>
                        have ⟨_, _, hneL2, horig2⟩ := h2O
                        exact hState.loanRel.disjointActive l1 l2 e1 e2 loc1 loc2
                          hne12 horig1 ha1 hf1 horig2 ha2 hf2 hloc1 hloc2
              noJoinOwners := by
                intro _ l e hl ha hf
                cases hClassify l e hl ha hf with
                | inl hT =>
                  have ⟨hl_eq, he_eq⟩ := hT
                  subst hl_eq he_eq
                  exact hownT
                | inr hRest =>
                  cases hRest with
                  | inl hF =>
                    have ⟨hl_eq, he_eq⟩ := hF
                    subst hl_eq he_eq
                    exact hownF
                  | inr hO =>
                    have ⟨_, _, hneL, horig⟩ := hO
                    exact (hother l e hneL horig ha hf).1
              sharedOwn := hState.loanRel.sharedOwn
              disjointShared := hState.loanRel.disjointShared
            }
          }

theorem loanLoc_update_eq_of_some {loanLoc : Nat → Option Nat}
    {loans : Nat → Option LoanEntry} {joinedLid : Nat} (locJoined : Nat)
    (hNone : loans joinedLid = none) {lid : Nat}
    (hSome : ∃ e, loans lid = some e) :
    (if lid == joinedLid then some locJoined else loanLoc lid) = loanLoc lid := by
  cases hbeq : (lid == joinedLid) with
  | false => rfl
  | true =>
    have heq : lid = joinedLid := of_decide_eq_true hbeq
    subst heq
    cases hSome with
    | intro e he =>
      rw [hNone] at he
      cases he

theorem LocalRel.extend_fresh_loan {loanLoc : Nat → Option Nat} {sharedLoc : Nat → Nat → Prop}
    {loans : Nat → Option LoanEntry}
    {symLocals : Nat → Option SymVal} {concLocals : Nat → Option MirVal}
    {joinedLid : Nat} (locJoined : Nat)
    (hNone : loans joinedLid = none)
    (hBorrows : ∀ i lid, symLocals i = some (.borrow lid) → ∃ e, loans lid = some e)
    (hRel : LocalRel loanLoc sharedLoc symLocals concLocals) :
    LocalRel (fun l => if l == joinedLid then some locJoined else loanLoc l) sharedLoc
      symLocals concLocals := by
  intro i sv hlookup
  have ⟨mv, hconc, hval⟩ := hRel i sv hlookup
  refine ⟨mv, hconc, ?_⟩
  cases sv with
  | usize _ | bool _ | unit | tupleUsizeBool _ _ | refShared _ => exact hval
  | borrow lid =>
    have ⟨loc, hloc, hmv⟩ := hval
    refine ⟨loc, ?_, hmv⟩
    dsimp
    rw [loanLoc_update_eq_of_some locJoined hNone (hBorrows i lid hlookup)]
    exact hloc

theorem matchBorrowArm_eq_some {bb : BasicBlock} {dst src joinBlk : Nat}
    (h : matchBorrowArm bb = some (dst, src, joinBlk)) :
    bb.stmts = [.assign ⟨dst⟩ (.use (.copy ⟨src⟩))] ∧
    bb.terminator = .goto ⟨joinBlk⟩ := by
  unfold matchBorrowArm at h
  cases hstmts : bb.stmts with
  | nil => rw [hstmts] at h; cases h
  | cons s rest =>
    rw [hstmts] at h
    cases hrest : rest with
    | cons _ _ => rw [hrest] at h; cases h
    | nil =>
      rw [hrest] at h
      dsimp at h
      cases s with
      | assignDeref _ _ | storageLive _ | storageDead _ | nop => cases h
      | assign dstPlace rv =>
        cases rv with
        | deref _ | proj0 _ | proj1 _ | binaryOp _ _ _ | checkedBinaryOp _ _ _ => cases h
        | use op =>
          cases op with
          | move _ | constVal _ => cases h
          | copy srcPlace =>
            dsimp at h
            cases hterm : bb.terminator with
            | return_ | unreachable | callAtomicLoad _ _ _ _ | switchInt _ _ _
            | assertNotOverflow _ _ | callPure2 _ _ _ _ _ =>
              rw [hterm] at h; cases h
            | goto jBlk =>
              rw [hterm] at h
              dsimp at h
              injection h with htuple
              injection htuple with hdst hrest2
              injection hrest2 with hsrc hjoin
              subst hdst hsrc hjoin
              cases dstPlace; cases srcPlace; cases jBlk
              exact ⟨rfl, rfl⟩

/-- Soundness of `evalJoinBorrow`: executing a diamond conditional reborrow
    advances the concrete machine in 3 deterministic steps to `joinBlock` and
    establishes `StateRel` with the newly allocated joined loan `joinedLid`. -/
theorem evalJoinBorrow_sound {loanLoc : Nat → Option Nat} {sharedLoc : Nat → Nat → Prop}
    {body : MirBody} {sym symJoined : SymState} {conc : MirState}
    {dstLocal falseSrc trueSrc joinBlock joinedLid : Nat}
    (hState : StateRel loanLoc sharedLoc sym conc)
    (hJoin : evalJoinBorrow body sym dstLocal falseSrc trueSrc joinBlock joinedLid = some symJoined) :
    ∃ loanLoc' concJoined,
      StateRel loanLoc' sharedLoc symJoined concJoined ∧
      ∀ ret, SafeAndReturns body concJoined ret → SafeAndReturns body conc ret := by
  unfold evalJoinBorrow at hJoin
  cases hhas : sym.hasActiveJoin with
  | true => rw [hhas] at hJoin; cases hJoin
  | false =>
    rw [hhas] at hJoin
    dsimp at hJoin
    cases hbb : body.blocks[sym.block]? with
    | none => rw [hbb] at hJoin; cases hJoin
    | some bb =>
      rw [hbb] at hJoin
      dsimp at hJoin
      cases hstmt : bb.stmts[sym.stmtIdx]? with
      | some _ => rw [hstmt] at hJoin; cases hJoin
      | none =>
        rw [hstmt] at hJoin
        cases hterm : bb.terminator with
        | return_ | goto _ | unreachable | callAtomicLoad _ _ _ _
        | assertNotOverflow _ _ | callPure2 _ _ _ _ _ =>
          rw [hterm] at hJoin; cases hJoin
        | switchInt discr falseTarget trueTarget =>
          rw [hterm] at hJoin
          dsimp at hJoin
          cases hOp : evalSymOperand sym.locals discr with
          | none => rw [hOp] at hJoin; cases hJoin
          | some pDiscr =>
            cases pDiscr with
            | mk svDiscr localsAfterDiscr =>
              rw [hOp] at hJoin
              cases svDiscr with
              | usize _ | unit | tupleUsizeBool _ _ | refShared _ | borrow _ => cases hJoin
              | bool cond =>
                dsimp at hJoin
                cases hbbF : body.blocks[falseTarget.index]? with
                | none => rw [hbbF] at hJoin; cases hJoin
                | some bbFalse =>
                  rw [hbbF] at hJoin
                  cases hbbT : body.blocks[trueTarget.index]? with
                  | none => rw [hbbT] at hJoin; cases hJoin
                  | some bbTrue =>
                    rw [hbbT] at hJoin
                    dsimp at hJoin
                    cases harmF : matchBorrowArm bbFalse with
                    | none => rw [harmF] at hJoin; cases hJoin
                    | some armF =>
                      cases armF with
                      | mk dstF restArmF =>
                        cases restArmF with
                        | mk srcF joinF =>
                          rw [harmF] at hJoin
                          cases harmT : matchBorrowArm bbTrue with
                          | none => rw [harmT] at hJoin; cases hJoin
                          | some armT =>
                            cases armT with
                            | mk dstT restArmT =>
                              cases restArmT with
                              | mk srcT joinT =>
                                rw [harmT] at hJoin
                                dsimp at hJoin
                                cases hchk1 : (dstF == dstLocal && dstT == dstLocal &&
                                  srcF == falseSrc && srcT == trueSrc &&
                                  joinF == joinBlock && joinT == joinBlock) with
                                | false => rw [hchk1] at hJoin; cases hJoin
                                | true =>
                                  rw [hchk1] at hJoin
                                  dsimp at hJoin
                                  cases hsrcF : localsAfterDiscr falseSrc with
                                  | none => rw [hsrcF] at hJoin; cases hJoin
                                  | some svF =>
                                    rw [hsrcF] at hJoin
                                    cases svF with
                                    | usize _ | bool _ | unit | tupleUsizeBool _ _ | refShared _ => cases hJoin
                                    | borrow falseLid =>
                                      cases hsrcT : localsAfterDiscr trueSrc with
                                      | none => rw [hsrcT] at hJoin; cases hJoin
                                      | some svT =>
                                        rw [hsrcT] at hJoin
                                        cases svT with
                                        | usize _ | bool _ | unit | tupleUsizeBool _ _ | refShared _ => cases hJoin
                                        | borrow trueLid =>
                                          dsimp at hJoin
                                          cases hchk2 : (!(falseLid == trueLid) &&
                                            !(falseLid == joinedLid) &&
                                            !(trueLid == joinedLid)) with
                                          | false => rw [hchk2] at hJoin; cases hJoin
                                          | true =>
                                            rw [hchk2] at hJoin
                                            dsimp at hJoin
                                            cases hloanF : sym.loans falseLid with
                                            | none => rw [hloanF] at hJoin; cases hJoin
                                            | some falseEntry =>
                                              rw [hloanF] at hJoin
                                              cases hloanT : sym.loans trueLid with
                                              | none => rw [hloanT] at hJoin; cases hJoin
                                              | some trueEntry =>
                                                rw [hloanT] at hJoin
                                                cases hloanJ : sym.loans joinedLid with
                                                | some _ => rw [hloanJ] at hJoin; cases hJoin
                                                | none =>
                                                  rw [hloanJ] at hJoin
                                                  dsimp at hJoin
                                                  cases hactF : falseEntry.active with
                                                  | false => rw [hactF] at hJoin; cases hJoin
                                                  | true =>
                                                    rw [hactF] at hJoin
                                                    cases hfrzF : falseEntry.frozen with
                                                    | true => rw [hfrzF] at hJoin; cases hJoin
                                                    | false =>
                                                      rw [hfrzF] at hJoin
                                                      cases hactT : trueEntry.active with
                                                      | false => rw [hactT] at hJoin; cases hJoin
                                                      | true =>
                                                        rw [hactT] at hJoin
                                                        cases hfrzT : trueEntry.frozen with
                                                        | true => rw [hfrzT] at hJoin; cases hJoin
                                                        | false =>
                                                          rw [hfrzT] at hJoin
                                                          dsimp at hJoin
                                                          injection hJoin with hsymJoined
                                                          have h1a := Eq.mp (Bool.and_eq_true _ _) hchk1
                                                          have h1b := Eq.mp (Bool.and_eq_true _ _) h1a.1
                                                          have h1c := Eq.mp (Bool.and_eq_true _ _) h1b.1
                                                          have h1d := Eq.mp (Bool.and_eq_true _ _) h1c.1
                                                          have h1e := Eq.mp (Bool.and_eq_true _ _) h1d.1
                                                          have hdstF_eq : dstF = dstLocal := of_decide_eq_true h1e.1
                                                          have hdstT_eq : dstT = dstLocal := of_decide_eq_true h1e.2
                                                          have hsrcF_eq : srcF = falseSrc := of_decide_eq_true h1d.2
                                                          have hsrcT_eq : srcT = trueSrc := of_decide_eq_true h1c.2
                                                          have hjoinF_eq : joinF = joinBlock := of_decide_eq_true h1b.2
                                                          have hjoinT_eq : joinT = joinBlock := of_decide_eq_true h1a.2
                                                          rw [hdstF_eq, hsrcF_eq, hjoinF_eq] at harmF
                                                          rw [hdstT_eq, hsrcT_eq, hjoinT_eq] at harmT
                                                          have ⟨hstmtsF, htermF⟩ := matchBorrowArm_eq_some harmF
                                                          have ⟨hstmtsT, htermT⟩ := matchBorrowArm_eq_some harmT
                                                          have h2a := Eq.mp (Bool.and_eq_true _ _) hchk2
                                                          have h2b := Eq.mp (Bool.and_eq_true _ _) h2a.1
                                                          have hneFT : falseLid ≠ trueLid := by
                                                            intro heq
                                                            have hb : (falseLid == trueLid) = true := decide_eq_true heq
                                                            rw [hb] at h2b
                                                            cases h2b.1
                                                          have hneFJ : falseLid ≠ joinedLid := by
                                                            intro heq
                                                            have hb : (falseLid == joinedLid) = true := decide_eq_true heq
                                                            rw [hb] at h2b
                                                            cases h2b.2
                                                          have hneTJ : trueLid ≠ joinedLid := by
                                                            intro heq
                                                            have hb : (trueLid == joinedLid) = true := decide_eq_true heq
                                                            rw [hb] at h2a
                                                            cases h2a.2
                                                          have ⟨mvDiscr, concLocalsAfterDiscr, hConcOp, hValDiscr, hLocRelAfter⟩ :=
                                                            evalSymOperand_sound hState.localRel hOp
                                                          subst hValDiscr
                                                          have hBorAfter := (evalSymOperand_borrows hState.localBorrows hOp).2
                                                          have ⟨mvFRef, hconcFRef, hvalFRef⟩ :=
                                                            hLocRelAfter falseSrc (.borrow falseLid) hsrcF
                                                          have ⟨locFalse0, hlocF0, hmvFRef⟩ := hvalFRef
                                                          subst hmvFRef
                                                          have ⟨mvTRef, hconcTRef, hvalTRef⟩ :=
                                                            hLocRelAfter trueSrc (.borrow trueLid) hsrcT
                                                          have ⟨locTrue0, hlocT0, hmvTRef⟩ := hvalTRef
                                                          subst hmvTRef
                                                          have ⟨⟨locFalse, mvFalseOrig, hlocF, hscF, hownF⟩, _⟩ :=
                                                            hState.loanRel.activeOwn falseLid falseEntry hloanF hactF hfrzF
                                                          have ⟨⟨locTrue, mvTrueOrig, hlocT, hscT, hownT⟩, _⟩ :=
                                                            hState.loanRel.activeOwn trueLid trueEntry hloanT hactT hfrzT
                                                          rw [hlocF] at hlocF0; injection hlocF0 with hlocF_eq; subst hlocF_eq
                                                          rw [hlocT] at hlocT0; injection hlocT0 with hlocT_eq; subst hlocT_eq
                                                          have hneLocFT : locFalse ≠ locTrue :=
                                                            hState.loanRel.disjointActive falseLid trueLid falseEntry trueEntry
                                                              locFalse locTrue hneFT hloanF hactF hfrzF hloanT hactT hfrzT hlocF hlocT
                                                          have hownersF : falseEntry.owners = [] :=
                                                            hState.loanRel.noJoinOwners hhas falseLid falseEntry hloanF hactF hfrzF
                                                          have hownersT : trueEntry.owners = [] :=
                                                            hState.loanRel.noJoinOwners hhas trueLid trueEntry hloanT hactT hfrzT
                                                          let locJoined := if cond then locTrue else locFalse
                                                          let loanLoc' : Nat → Option Nat :=
                                                            fun l => if l == joinedLid then some locJoined else loanLoc l
                                                          let concJoined : MirState := {
                                                            conc with
                                                            locals := updateLocal concLocalsAfterDiscr dstLocal (some (.refMutLoc locJoined))
                                                            block := joinBlock
                                                            stmtIdx := 0
                                                          }
                                                          have hStepChain : ∀ ret, SafeAndReturns body concJoined ret → SafeAndReturns body conc ret := by
                                                            intro ret hSafeJoined
                                                            cases cond with
                                                            | false =>
                                                              have hStep1 :
                                                                  evalMirStep body conc =
                                                                    .step () { conc with
                                                                      locals := concLocalsAfterDiscr
                                                                      block := falseTarget.index
                                                                      stmtIdx := 0 } := by
                                                                unfold evalMirStep
                                                                rw [hState.block_eq, hbb]
                                                                dsimp
                                                                rw [hState.stmtIdx_eq, hstmt]
                                                                dsimp
                                                                rw [hterm]
                                                                dsimp [evalMirTerminator]
                                                                rw [hConcOp]
                                                              have hStep2 :
                                                                  evalMirStep body { conc with
                                                                    locals := concLocalsAfterDiscr
                                                                    block := falseTarget.index
                                                                    stmtIdx := 0 } =
                                                                    .step () { conc with
                                                                      locals := updateLocal concLocalsAfterDiscr dstLocal (some (.refMutLoc locFalse))
                                                                      block := falseTarget.index
                                                                      stmtIdx := 1 } := by
                                                                have h0 : bbFalse.stmts[0]? = some (.assign ⟨dstLocal⟩ (.use (.copy ⟨falseSrc⟩))) := by
                                                                  rw [hstmtsF]; rfl
                                                                unfold evalMirStep
                                                                dsimp
                                                                rw [hbbF]
                                                                dsimp
                                                                rw [h0]
                                                                dsimp [evalMirStmt, evalOperand]
                                                                rw [hconcFRef]
                                                              have hStep3 :
                                                                  evalMirStep body { conc with
                                                                    locals := updateLocal concLocalsAfterDiscr dstLocal (some (.refMutLoc locFalse))
                                                                    block := falseTarget.index
                                                                    stmtIdx := 1 } =
                                                                    .step () concJoined := by
                                                                unfold evalMirStep
                                                                dsimp
                                                                rw [hbbF]
                                                                dsimp
                                                                rw [hstmtsF, htermF]
                                                                rfl
                                                              exact SafeAndReturns.of_step hStep1
                                                                (SafeAndReturns.of_step hStep2
                                                                  (SafeAndReturns.of_step hStep3 hSafeJoined))
                                                            | true =>
                                                              have hStep1 :
                                                                  evalMirStep body conc =
                                                                    .step () { conc with
                                                                      locals := concLocalsAfterDiscr
                                                                      block := trueTarget.index
                                                                      stmtIdx := 0 } := by
                                                                unfold evalMirStep
                                                                rw [hState.block_eq, hbb]
                                                                dsimp
                                                                rw [hState.stmtIdx_eq, hstmt]
                                                                dsimp
                                                                rw [hterm]
                                                                dsimp [evalMirTerminator]
                                                                rw [hConcOp]
                                                              have hStep2 :
                                                                  evalMirStep body { conc with
                                                                    locals := concLocalsAfterDiscr
                                                                    block := trueTarget.index
                                                                    stmtIdx := 0 } =
                                                                    .step () { conc with
                                                                      locals := updateLocal concLocalsAfterDiscr dstLocal (some (.refMutLoc locTrue))
                                                                      block := trueTarget.index
                                                                      stmtIdx := 1 } := by
                                                                have h0 : bbTrue.stmts[0]? = some (.assign ⟨dstLocal⟩ (.use (.copy ⟨trueSrc⟩))) := by
                                                                  rw [hstmtsT]; rfl
                                                                unfold evalMirStep
                                                                dsimp
                                                                rw [hbbT]
                                                                dsimp
                                                                rw [h0]
                                                                dsimp [evalMirStmt, evalOperand]
                                                                rw [hconcTRef]
                                                              have hStep3 :
                                                                  evalMirStep body { conc with
                                                                    locals := updateLocal concLocalsAfterDiscr dstLocal (some (.refMutLoc locTrue))
                                                                    block := trueTarget.index
                                                                    stmtIdx := 1 } =
                                                                    .step () concJoined := by
                                                                unfold evalMirStep
                                                                dsimp
                                                                rw [hbbT]
                                                                dsimp
                                                                rw [hstmtsT, htermT]
                                                                rfl
                                                              exact SafeAndReturns.of_step hStep1
                                                                (SafeAndReturns.of_step hStep2
                                                                  (SafeAndReturns.of_step hStep3 hSafeJoined))
                                                          let joinedEntry : LoanEntry := {
                                                            owners := [.loan falseLid, .loan trueLid]
                                                            curVal := zipSymVal cond trueEntry.curVal falseEntry.curVal
                                                            frozen := false
                                                            active := true
                                                            back := fun newVal => [
                                                              zipSymVal cond falseEntry.curVal newVal,
                                                              zipSymVal cond newVal trueEntry.curVal
                                                            ]
                                                          }
                                                          let loans1 := updateLoan sym.loans falseLid (some { falseEntry with frozen := true, active := true })
                                                          let loans2 := updateLoan loans1 trueLid (some { trueEntry with frozen := true, active := true })
                                                          let loans3 := updateLoan loans2 joinedLid (some joinedEntry)
                                                          have hClassifyJ :
                                                              ∀ l e,
                                                                loans3 l = some e →
                                                                e.active = true →
                                                                e.frozen = false →
                                                                (l = joinedLid ∧ e = joinedEntry) ∨
                                                                (l ≠ joinedLid ∧ l ≠ trueLid ∧ l ≠ falseLid ∧ sym.loans l = some e) := by
                                                            intro l e hl ha hf
                                                            unfold loans3 loans2 loans1 updateLoan at hl
                                                            cases hbJ : (l == joinedLid) with
                                                            | true =>
                                                              rw [hbJ] at hl
                                                              injection hl with he
                                                              exact Or.inl ⟨of_decide_eq_true hbJ, he.symm⟩
                                                            | false =>
                                                              rw [hbJ] at hl
                                                              cases hbT : (l == trueLid) with
                                                              | true =>
                                                                rw [hbT] at hl
                                                                injection hl with he
                                                                subst he
                                                                cases hf
                                                              | false =>
                                                                rw [hbT] at hl
                                                                cases hbF : (l == falseLid) with
                                                                | true =>
                                                                  rw [hbF] at hl
                                                                  injection hl with he
                                                                  subst he
                                                                  cases hf
                                                                | false =>
                                                                  rw [hbF] at hl
                                                                  exact Or.inr ⟨of_decide_eq_false hbJ,
                                                                    of_decide_eq_false hbT,
                                                                    of_decide_eq_false hbF, hl⟩
                                                          have hloanLocJ : loanLoc' joinedLid = some locJoined := by
                                                            dsimp [loanLoc']
                                                            have hb : (joinedLid == joinedLid) = true := decide_eq_true rfl
                                                            rw [hb]; rfl
                                                          have hloanLocF' : loanLoc' falseLid = some locFalse := by
                                                            dsimp [loanLoc']
                                                            have hb : (falseLid == joinedLid) = false := decide_eq_false hneFJ
                                                            rw [hb]
                                                            exact hlocF
                                                          have hloanLocT' : loanLoc' trueLid = some locTrue := by
                                                            dsimp [loanLoc']
                                                            have hb : (trueLid == joinedLid) = false := decide_eq_false hneTJ
                                                            rw [hb]
                                                            exact hlocT
                                                          have hJoinInv : JoinInv loanLoc' loans3 conc.mem joinedLid joinedEntry falseLid trueLid := by
                                                            refine ⟨locJoined, locFalse, locTrue,
                                                              { falseEntry with frozen := true, active := true },
                                                              { trueEntry with frozen := true, active := true },
                                                              mvFalseOrig, mvTrueOrig,
                                                              hneFT, hneFJ, hneTJ, hloanLocJ, hloanLocF', hloanLocT',
                                                              hneLocFT, ?_, ?_, rfl, rfl, hownersF, hownersT, ?_, ?_, ?_⟩
                                                            · unfold loans3 loans2 loans1 updateLoan
                                                              have hb1 : (falseLid == joinedLid) = false := decide_eq_false hneFJ
                                                              have hb2 : (falseLid == trueLid) = false := decide_eq_false hneFT
                                                              have hb3 : (falseLid == falseLid) = true := decide_eq_true rfl
                                                              rw [hb1, hb2, hb3]; rfl
                                                            · unfold loans3 loans2 loans1 updateLoan
                                                              have hb1 : (trueLid == joinedLid) = false := decide_eq_false hneTJ
                                                              have hb2 : (trueLid == trueLid) = true := decide_eq_true rfl
                                                              rw [hb1, hb2]; rfl
                                                            · cases cond with
                                                              | false => exact Or.inl ⟨rfl, hownT⟩
                                                              | true => exact Or.inr ⟨rfl, hownF⟩
                                                            · intro otherLid otherEntry hneO hlO haO hfO
                                                              cases hClassifyJ otherLid otherEntry hlO haO hfO with
                                                              | inl hJ =>
                                                                have ⟨hbad, _⟩ := hJ
                                                                exact False.elim (hneO hbad)
                                                              | inr hO =>
                                                                have ⟨_, hneOT, hneOF, horigO⟩ := hO
                                                                refine ⟨hState.loanRel.noJoinOwners hhas otherLid otherEntry horigO haO hfO, ?_⟩
                                                                intro locOther hlocO'
                                                                dsimp [loanLoc'] at hlocO'
                                                                rw [loanLoc_update_eq_of_some locJoined hloanJ ⟨otherEntry, horigO⟩] at hlocO'
                                                                exact ⟨
                                                                  hState.loanRel.disjointActive otherLid falseLid otherEntry falseEntry
                                                                    locOther locFalse hneOF horigO haO hfO hloanF hactF hfrzF hlocO' hlocF,
                                                                  hState.loanRel.disjointActive otherLid trueLid otherEntry trueEntry
                                                                    locOther locTrue hneOT horigO haO hfO hloanT hactT hfrzT hlocO' hlocT
                                                                ⟩
                                                            · intro v mv hv
                                                              cases cond with
                                                              | false =>
                                                                refine ⟨zipSymVal false falseEntry.curVal v,
                                                                  zipSymVal false v trueEntry.curVal,
                                                                  mv, mvTrueOrig, rfl, ?_, ?_, ?_, ?_⟩
                                                                · rw [zipSymVal_eq_ite]; exact hv
                                                                · rw [zipSymVal_eq_ite]; exact hscT
                                                                · intro _; exact ⟨rfl, rfl⟩
                                                                · intro hbad; exact False.elim (hneLocFT hbad)
                                                              | true =>
                                                                refine ⟨zipSymVal true falseEntry.curVal v,
                                                                  zipSymVal true v trueEntry.curVal,
                                                                  mvFalseOrig, mv, rfl, ?_, ?_, ?_, ?_⟩
                                                                · rw [zipSymVal_eq_ite]; exact hscF
                                                                · rw [zipSymVal_eq_ite]; exact hv
                                                                · intro hbad; exact False.elim (hneLocFT hbad.symm)
                                                                · intro _; exact ⟨rfl, rfl⟩
                                                          refine ⟨loanLoc', concJoined, ?_, hStepChain⟩
                                                          rw [← hsymJoined]
                                                          refine {
                                                            block_eq := rfl
                                                            stmtIdx_eq := rfl
                                                            localBorrows := localBorrows_update_some dstLocal
                                                              (fun i lid' hi =>
                                                                loans_some_updateLoan joinedLid _
                                                                  (loans_some_updateLoan trueLid _
                                                                    (loans_some_updateLoan falseLid _
                                                                      (hBorAfter i lid' hi))))
                                                              (fun lid' heq => by
                                                                injection heq with hlid'
                                                                subst hlid'
                                                                refine ⟨joinedEntry, ?_⟩
                                                                dsimp [updateLoan]
                                                                have hb : (joinedLid == joinedLid) = true := decide_eq_true rfl
                                                                rw [hb]; rfl)
                                                            localRel := LocalRel.update_some
                                                              (LocalRel.extend_fresh_loan locJoined hloanJ hBorAfter hLocRelAfter)
                                                              dstLocal
                                                              (show ValRel loanLoc' sharedLoc (.borrow joinedLid) (.refMutLoc locJoined) from
                                                                ⟨locJoined, hloanLocJ, rfl⟩)
                                                            loanRel := {
                                                              activeOwn := by
                                                                intro l e hl ha hf
                                                                cases hClassifyJ l e hl ha hf with
                                                                | inl hJ =>
                                                                  have ⟨hl_eq, he_eq⟩ := hJ
                                                                  subst hl_eq he_eq
                                                                  refine ⟨?_, Or.inr ⟨falseLid, trueLid, rfl, hJoinInv⟩⟩
                                                                  cases cond with
                                                                  | false =>
                                                                    refine ⟨locFalse, mvFalseOrig, hloanLocJ, ?_, hownF⟩
                                                                    dsimp [joinedEntry]
                                                                    rw [zipSymVal_eq_ite]
                                                                    exact hscF
                                                                  | true =>
                                                                    refine ⟨locTrue, mvTrueOrig, hloanLocJ, ?_, hownT⟩
                                                                    dsimp [joinedEntry]
                                                                    rw [zipSymVal_eq_ite]
                                                                    exact hscT
                                                                | inr hO =>
                                                                  have ⟨_, hneOT, hneOF, horig⟩ := hO
                                                                  have ⟨⟨locO, mvO, hlocO, hscO, hownO⟩, _⟩ :=
                                                                    hState.loanRel.activeOwn l e horig ha hf
                                                                  have hlocO' : loanLoc' l = some locO := by
                                                                    dsimp [loanLoc']
                                                                    rw [loanLoc_update_eq_of_some locJoined hloanJ ⟨e, horig⟩]
                                                                    exact hlocO
                                                                  exact ⟨⟨locO, mvO, hlocO', hscO, hownO⟩,
                                                                    Or.inl (hState.loanRel.noJoinOwners hhas l e horig ha hf)⟩
                                                              disjointActive := by
                                                                intro l1 l2 e1 e2 loc1 loc2 hne12 hl1 ha1 hf1 hl2 ha2 hf2 hloc1 hloc2
                                                                cases hClassifyJ l1 e1 hl1 ha1 hf1 with
                                                                | inl h1J =>
                                                                  have ⟨hl1_eq, _⟩ := h1J
                                                                  subst hl1_eq
                                                                  cases hClassifyJ l2 e2 hl2 ha2 hf2 with
                                                                  | inl h2J =>
                                                                    have ⟨hl2_eq, _⟩ := h2J
                                                                    subst hl2_eq
                                                                    exact False.elim (hne12 rfl)
                                                                  | inr h2O =>
                                                                    have ⟨_, hne2T, hne2F, horig2⟩ := h2O
                                                                    rw [hloanLocJ] at hloc1; injection hloc1 with h1; subst h1
                                                                    dsimp [loanLoc'] at hloc2
                                                                    rw [loanLoc_update_eq_of_some locJoined hloanJ ⟨e2, horig2⟩] at hloc2
                                                                    cases cond with
                                                                    | false =>
                                                                      exact hState.loanRel.disjointActive falseLid l2 falseEntry e2
                                                                        locFalse loc2 hne2F.symm hloanF hactF hfrzF horig2 ha2 hf2 hlocF hloc2
                                                                    | true =>
                                                                      exact hState.loanRel.disjointActive trueLid l2 trueEntry e2
                                                                        locTrue loc2 hne2T.symm hloanT hactT hfrzT horig2 ha2 hf2 hlocT hloc2
                                                                | inr h1O =>
                                                                  have ⟨_, hne1T, hne1F, horig1⟩ := h1O
                                                                  cases hClassifyJ l2 e2 hl2 ha2 hf2 with
                                                                  | inl h2J =>
                                                                    have ⟨hl2_eq, _⟩ := h2J
                                                                    subst hl2_eq
                                                                    rw [hloanLocJ] at hloc2; injection hloc2 with h2; subst h2
                                                                    dsimp [loanLoc'] at hloc1
                                                                    rw [loanLoc_update_eq_of_some locJoined hloanJ ⟨e1, horig1⟩] at hloc1
                                                                    cases cond with
                                                                    | false =>
                                                                      exact hState.loanRel.disjointActive l1 falseLid e1 falseEntry
                                                                        loc1 locFalse hne1F horig1 ha1 hf1 hloanF hactF hfrzF hloc1 hlocF
                                                                    | true =>
                                                                      exact hState.loanRel.disjointActive l1 trueLid e1 trueEntry
                                                                        loc1 locTrue hne1T horig1 ha1 hf1 hloanT hactT hfrzT hloc1 hlocT
                                                                  | inr h2O =>
                                                                    have ⟨_, hne2T, hne2F, horig2⟩ := h2O
                                                                    dsimp [loanLoc'] at hloc1 hloc2
                                                                    rw [loanLoc_update_eq_of_some locJoined hloanJ ⟨e1, horig1⟩] at hloc1
                                                                    rw [loanLoc_update_eq_of_some locJoined hloanJ ⟨e2, horig2⟩] at hloc2
                                                                    exact hState.loanRel.disjointActive l1 l2 e1 e2 loc1 loc2
                                                                      hne12 horig1 ha1 hf1 horig2 ha2 hf2 hloc1 hloc2
                                                              noJoinOwners := fun hbad => by cases hbad
                                                              sharedOwn := hState.loanRel.sharedOwn
                                                              disjointShared := by
                                                                intro l locMut locShared n hlocM hsh
                                                                dsimp [loanLoc'] at hlocM
                                                                cases hbJ : (l == joinedLid) with
                                                                | true =>
                                                                  rw [hbJ] at hlocM
                                                                  injection hlocM with hlocM_eq
                                                                  subst hlocM_eq
                                                                  cases cond with
                                                                  | false =>
                                                                    exact hState.loanRel.disjointShared falseLid locFalse locShared n hlocF hsh
                                                                  | true =>
                                                                    exact hState.loanRel.disjointShared trueLid locTrue locShared n hlocT hsh
                                                                | false =>
                                                                  rw [hbJ] at hlocM
                                                                  exact hState.loanRel.disjointShared l locMut locShared n hlocM hsh
                                                            }
                                                          }

/-- Soundness of `evalSymState` by structural induction on `plan :
    TransPlan`. -/
theorem evalSymState_sound (plan : TransPlan) (body : MirBody) :
    ∀ {loanLoc : Nat → Option Nat} {sharedLoc : Nat → Nat → Prop}
      {sym : SymState} {conc : MirState} {ret : MirVal},
      StateRel loanLoc sharedLoc sym conc →
      evalSymState plan body sym = .ok ret →
      SafeAndReturns body conc ret := by
  induction plan with
  | fail =>
    intro _ _ _ _ _ _ hEval
    cases hEval
  | ret =>
    intro _ _ sym conc ret hState hEval
    unfold evalSymState at hEval
    cases hRet : evalReturn body sym with
    | none => rw [hRet] at hEval; cases hEval
    | some mv =>
      rw [hRet] at hEval
      injection hEval with hmv
      subst hmv
      exact evalReturn_sound hState hRet
  | step next ih =>
    intro _ _ sym conc ret hState hEval
    unfold evalSymState at hEval
    cases hStep : evalSymStep body sym with
    | none => rw [hStep] at hEval; cases hEval
    | some p =>
      cases p with
      | mk ov sym' =>
        rw [hStep] at hEval
        dsimp at hEval
        cases ov with
        | true => cases hEval
        | false =>
          dsimp at hEval
          have ⟨conc', hConcStep, hState'⟩ := evalSymStep_sound hState hStep
          exact SafeAndReturns.of_step hConcStep (ih hState' hEval)
  | endLoan lid next ih =>
    intro _ _ sym conc ret hState hEval
    unfold evalSymState at hEval
    cases hEnd : evalEndLoan sym lid with
    | none => rw [hEnd] at hEval; cases hEval
    | some sym' =>
      rw [hEnd] at hEval
      exact ih (evalEndLoan_sound hState hEnd) hEval
  | branch falsePlan truePlan ihFalse ihTrue =>
    intro _ _ sym conc ret hState hEval
    unfold evalSymState at hEval
    cases hBr : evalBranchStep body sym with
    | none => rw [hBr] at hEval; cases hEval
    | some brTuple =>
      have ⟨cond, symFalse, symTrue⟩ := brTuple
      rw [hBr] at hEval
      dsimp at hEval
      rw [zipAeneasRes_eq_ite] at hEval
      have ⟨concNext, hConcStep, hStateNext⟩ := evalBranchStep_sound hState hBr
      cases cond with
      | false =>
        exact SafeAndReturns.of_step hConcStep (ihFalse hStateNext hEval)
      | true =>
        exact SafeAndReturns.of_step hConcStep (ihTrue hStateNext hEval)
  | joinBorrow dstLocal falseSrc trueSrc joinBlock joinedLid afterJoin ihAfter =>
    intro _ _ sym conc ret hState hEval
    unfold evalSymState at hEval
    cases hJoin : evalJoinBorrow body sym dstLocal falseSrc trueSrc joinBlock joinedLid with
    | none => rw [hJoin] at hEval; cases hEval
    | some symJoined =>
      rw [hJoin] at hEval
      have ⟨loanLoc', concJoined, hStateJoined, hStepChain⟩ :=
        evalJoinBorrow_sound hState hJoin
      exact hStepChain ret (ihAfter hStateJoined hEval)

theorem evalSymState_ne_inapplicable (plan : TransPlan) (body : MirBody) :
    ∀ (sym : SymState), evalSymState plan body sym ≠ .inapplicable := by
  induction plan with
  | fail =>
    intro _ h; cases h
  | ret =>
    intro sym
    unfold evalSymState
    cases evalReturn body sym <;> intro h <;> cases h
  | step next ih =>
    intro sym
    unfold evalSymState
    cases evalSymStep body sym with
    | none => intro h; cases h
    | some p =>
      cases p with
      | mk ov sym' =>
        dsimp
        cases ov with
        | true => intro h; cases h
        | false => exact ih sym'
  | endLoan lid next ih =>
    intro sym
    unfold evalSymState
    cases evalEndLoan sym lid with
    | none => intro h; cases h
    | some sym' => exact ih sym'
  | branch falsePlan truePlan ihFalse ihTrue =>
    intro sym
    unfold evalSymState
    cases evalBranchStep body sym with
    | none => intro h; cases h
    | some brTuple =>
      have ⟨cond, symFalse, symTrue⟩ := brTuple
      dsimp
      rw [zipAeneasRes_eq_ite]
      cases cond with
      | false => exact ihFalse symFalse
      | true => exact ihTrue symTrue
  | joinBorrow dstLocal falseSrc trueSrc joinBlock joinedLid afterJoin ihAfter =>
    intro sym
    unfold evalSymState
    cases evalJoinBorrow body sym dstLocal falseSrc trueSrc joinBlock joinedLid with
    | none => intro h; cases h
    | some symJoined => exact ihAfter symJoined

/-- Canonical root loan-location mapping extracted from `init.locals`, guarded
    by `1 ≤ lid` and `noAliasBefore init.locals loc lid`. -/
noncomputable def initLoanLoc (init : MirState) (lid : Nat) : Option Nat :=
  if decide (1 ≤ lid) then
    match init.locals lid with
    | some (.refMutLoc loc) =>
      if noAliasBefore init.locals loc lid then some loc else none
    | _ => none
  else
    none

/-- Canonical shared-reference location predicate extracted from `init`. -/
def initSharedLoc (init : MirState) (loc n : Nat) : Prop :=
  ∃ idx, 1 ≤ idx ∧
    init.locals idx = some (.refSharedLoc loc) ∧
    noMutAliasBefore init.locals loc idx = true ∧
    ReadOwnLoc init.mem loc (.usize n)

theorem noAliasBefore_ne {locals : Nat → Option MirVal} {loc loc' : Nat} :
    ∀ {k i : Nat},
      1 ≤ i →
      i < k →
      noAliasBefore locals loc k = true →
      locals i = some (.refMutLoc loc') →
      loc' ≠ loc
  | 0, _, _, hilt, _, _ => False.elim (Nat.not_lt_zero _ hilt)
  | 1, _, hi1, hilt, _, _ => False.elim (Nat.not_lt_of_ge hi1 hilt)
  | j + 2, i, hi1, hilt, hno, hloc => by
    unfold noAliasBefore at hno
    cases hok : (match locals (j + 1) with
      | some (.refMutLoc loc'') => !(loc'' == loc)
      | some (.refSharedLoc loc'') => !(loc'' == loc)
      | _ => true) with
    | false =>
      rw [hok] at hno
      cases hno
    | true =>
      rw [hok] at hno
      cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hilt) with
      | inl heq =>
        subst heq
        rw [hloc] at hok
        dsimp at hok
        cases hbeq : (loc' == loc) with
        | false => exact of_decide_eq_false hbeq
        | true =>
          rw [hbeq] at hok
          cases hok
      | inr hlt =>
        exact noAliasBefore_ne hi1 hlt hno hloc

theorem noAliasBefore_ne_shared {locals : Nat → Option MirVal} {loc loc' : Nat} :
    ∀ {k i : Nat},
      1 ≤ i →
      i < k →
      noAliasBefore locals loc k = true →
      locals i = some (.refSharedLoc loc') →
      loc' ≠ loc
  | 0, _, _, hilt, _, _ => False.elim (Nat.not_lt_zero _ hilt)
  | 1, _, hi1, hilt, _, _ => False.elim (Nat.not_lt_of_ge hi1 hilt)
  | j + 2, i, hi1, hilt, hno, hloc => by
    unfold noAliasBefore at hno
    cases hok : (match locals (j + 1) with
      | some (.refMutLoc loc'') => !(loc'' == loc)
      | some (.refSharedLoc loc'') => !(loc'' == loc)
      | _ => true) with
    | false =>
      rw [hok] at hno
      cases hno
    | true =>
      rw [hok] at hno
      cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hilt) with
      | inl heq =>
        subst heq
        rw [hloc] at hok
        dsimp at hok
        cases hbeq : (loc' == loc) with
        | false => exact of_decide_eq_false hbeq
        | true =>
          rw [hbeq] at hok
          cases hok
      | inr hlt =>
        exact noAliasBefore_ne_shared hi1 hlt hno hloc

theorem noMutAliasBefore_ne {locals : Nat → Option MirVal} {loc loc' : Nat} :
    ∀ {k i : Nat},
      1 ≤ i →
      i < k →
      noMutAliasBefore locals loc k = true →
      locals i = some (.refMutLoc loc') →
      loc' ≠ loc
  | 0, _, _, hilt, _, _ => False.elim (Nat.not_lt_zero _ hilt)
  | 1, _, hi1, hilt, _, _ => False.elim (Nat.not_lt_of_ge hi1 hilt)
  | j + 2, i, hi1, hilt, hno, hloc => by
    unfold noMutAliasBefore at hno
    cases hok : (match locals (j + 1) with
      | some (.refMutLoc loc'') => !(loc'' == loc)
      | _ => true) with
    | false =>
      rw [hok] at hno
      cases hno
    | true =>
      rw [hok] at hno
      cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hilt) with
      | inl heq =>
        subst heq
        rw [hloc] at hok
        dsimp at hok
        cases hbeq : (loc' == loc) with
        | false => exact of_decide_eq_false hbeq
        | true =>
          rw [hbeq] at hok
          cases hok
      | inr hlt =>
        exact noMutAliasBefore_ne hi1 hlt hno hloc

theorem noAliasBefore_of_forall_ne (locals : Nat → Option MirVal) (loc : Nat) :
    ∀ (k : Nat),
      (∀ i, 1 ≤ i → i < k →
        locals i ≠ some (.refMutLoc loc) ∧ locals i ≠ some (.refSharedLoc loc)) →
      noAliasBefore locals loc k = true
  | 0, _ => rfl
  | 1, _ => rfl
  | j + 2, hne => by
    unfold noAliasBefore
    have hj1_le : 1 ≤ j + 1 := Nat.le_add_left 1 j
    have hj1_lt : j + 1 < j + 2 := Nat.lt_succ_self (j + 1)
    have hnot_here := hne (j + 1) hj1_le hj1_lt
    have hokHere :
        (match locals (j + 1) with
         | some (.refMutLoc loc') => !(loc' == loc)
         | some (.refSharedLoc loc') => !(loc' == loc)
         | _ => true) = true := by
      cases hloc : locals (j + 1) with
      | none => rfl
      | some mv =>
        cases mv with
        | refMutLoc loc' =>
          dsimp
          cases hbeq : (loc' == loc) with
          | false => rfl
          | true =>
            have heq : loc' = loc := of_decide_eq_true hbeq
            subst heq
            exact False.elim (hnot_here.1 hloc)
        | refSharedLoc loc' =>
          dsimp
          cases hbeq : (loc' == loc) with
          | false => rfl
          | true =>
            have heq : loc' = loc := of_decide_eq_true hbeq
            subst heq
            exact False.elim (hnot_here.2 hloc)
        | usize _ | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | ordering _ => rfl
    have hrec : noAliasBefore locals loc (j + 1) = true :=
      noAliasBefore_of_forall_ne locals loc (j + 1) (fun i hi1 hilt =>
        hne i hi1 (Nat.lt_trans hilt hj1_lt))
    rw [hokHere, hrec]
    rfl

theorem noMutAliasBefore_of_forall_ne (locals : Nat → Option MirVal) (loc : Nat) :
    ∀ (k : Nat),
      (∀ i, 1 ≤ i → i < k → locals i ≠ some (.refMutLoc loc)) →
      noMutAliasBefore locals loc k = true
  | 0, _ => rfl
  | 1, _ => rfl
  | j + 2, hne => by
    unfold noMutAliasBefore
    have hj1_le : 1 ≤ j + 1 := Nat.le_add_left 1 j
    have hj1_lt : j + 1 < j + 2 := Nat.lt_succ_self (j + 1)
    have hnot_here : locals (j + 1) ≠ some (.refMutLoc loc) :=
      hne (j + 1) hj1_le hj1_lt
    have hokHere :
        (match locals (j + 1) with
         | some (.refMutLoc loc') => !(loc' == loc)
         | _ => true) = true := by
      cases hloc : locals (j + 1) with
      | none => rfl
      | some mv =>
        cases mv with
        | refMutLoc loc' =>
          dsimp
          cases hbeq : (loc' == loc) with
          | false => rfl
          | true =>
            have heq : loc' = loc := of_decide_eq_true hbeq
            subst heq
            exact False.elim (hnot_here hloc)
        | usize _ | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | ordering _ => rfl
    have hrec : noMutAliasBefore locals loc (j + 1) = true :=
      noMutAliasBefore_of_forall_ne locals loc (j + 1) (fun i hi1 hilt =>
        hne i hi1 (Nat.lt_trans hilt hj1_lt))
    rw [hokHere, hrec]
    rfl

theorem initLoanLoc_disjoint_shared (init : MirState) :
    ∀ lid locMut locShared n,
      initLoanLoc init lid = some locMut →
      initSharedLoc init locShared n →
      locMut ≠ locShared := by
  intro lid locMut locShared n hLoan hShared
  unfold initLoanLoc at hLoan
  cases hpos : decide (1 ≤ lid) with
  | false => rw [hpos] at hLoan; cases hLoan
  | true =>
    rw [hpos] at hLoan
    dsimp at hLoan
    have hlid1 : 1 ≤ lid := of_decide_eq_true hpos
    cases hlocM : init.locals lid with
    | none => rw [hlocM] at hLoan; cases hLoan
    | some mv =>
      rw [hlocM] at hLoan
      cases mv with
      | usize _ | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | ordering _ => cases hLoan
      | refMutLoc locM =>
        dsimp at hLoan
        cases hnoA : noAliasBefore init.locals locM lid with
        | false => rw [hnoA] at hLoan; cases hLoan
        | true =>
          rw [hnoA] at hLoan
          injection hLoan with hlocM_eq
          subst hlocM_eq
          have ⟨idx, hidx1, hlocS, hnoMutS, _⟩ := hShared
          have hneIdx : lid ≠ idx := by
            intro heq
            subst heq
            rw [hlocM] at hlocS
            cases hlocS
          cases Nat.lt_or_gt_of_ne hneIdx with
          | inl hlt =>
            exact noMutAliasBefore_ne hlid1 hlt hnoMutS hlocM
          | inr hgt =>
            exact (noAliasBefore_ne_shared hidx1 hgt hnoA hlocS).symm

theorem extractSymArgsAux_spec :
    ∀ (tys : List MirTy) (idx : Nat) (init : MirState) (args : List SymArg),
      1 ≤ idx →
      extractSymArgsAux idx tys init = some args →
      let (locals, loans, _) := buildPureSymStateAux idx args
      (∀ i, i < idx → locals i = none ∧ loans i = none) ∧
      (∀ i sv, locals i = some sv →
        idx ≤ i ∧
        (∀ lid, sv = .borrow lid → ∃ e, loans lid = some e) ∧
        ∃ mv, init.locals i = some mv ∧ ValRel (initLoanLoc init) (initSharedLoc init) sv mv) ∧
      (∀ lid entry, loans lid = some entry →
        idx ≤ lid ∧
        entry.owners = [] ∧
        entry.active = true ∧
        entry.frozen = false ∧
        ∃ loc n,
          init.locals lid = some (.refMutLoc loc) ∧
          initLoanLoc init lid = some loc ∧
          entry.curVal = .usize n ∧
          OwnLoc init.mem loc (.usize n) ∧
          noAliasBefore init.locals loc lid = true)
  | [], idx, _, args, _, hExt => by
    injection hExt with hargs
    subst hargs
    dsimp [buildPureSymStateAux, emptySymLocals, emptySymLoans]
    exact ⟨fun _ _ => ⟨rfl, rfl⟩, (by intro _ _ h; cases h), (by intro _ _ h; cases h)⟩
  | ty :: restTys, idx, init, args, hIdx1, hExt => by
    dsimp [extractSymArgsAux] at hExt
    have hIdxSucc1 : 1 ≤ idx + 1 := Nat.le_add_left 1 idx
    cases ty with
    | tupleUsizeBool | refAtomicUsize | atomicOrdering => cases hExt
    | usize =>
      cases hloc : init.locals idx with
      | none => rw [hloc] at hExt; cases hExt
      | some mv =>
        rw [hloc] at hExt
        cases mv with
        | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ => cases hExt
        | usize n =>
          dsimp at hExt
          cases hRest : extractSymArgsAux (idx + 1) restTys init with
          | none => rw [hRest] at hExt; cases hExt
          | some restArgs =>
            rw [hRest] at hExt
            injection hExt with hargs
            subst hargs
            have ih := extractSymArgsAux_spec restTys (idx + 1) init restArgs hIdxSucc1 hRest
            dsimp [buildPureSymStateAux]
            dsimp at ih
            refine ⟨?_, ?_, ?_⟩
            · intro i hilt
              have hne : i ≠ idx := Nat.ne_of_lt hilt
              have hb : (i == idx) = false := decide_eq_false hne
              unfold updateSymLocal
              rw [hb]
              exact ih.1 i (Nat.lt_trans hilt (Nat.lt_succ_self idx))
            · intro i sv hlookup
              unfold updateSymLocal at hlookup
              cases hb : (i == idx) with
              | true =>
                rw [hb] at hlookup
                injection hlookup with hsv
                have hi_eq : i = idx := of_decide_eq_true hb
                subst hi_eq hsv
                exact ⟨Nat.le_refl _, (by intro _ h; cases h), ⟨MirVal.usize n, hloc, rfl⟩⟩
              | false =>
                rw [hb] at hlookup
                have ⟨hle, hbor, hval⟩ := ih.2.1 i sv hlookup
                exact ⟨Nat.le_of_succ_le hle, hbor, hval⟩
            · intro lid entry hloan
              have ⟨hle, hrest⟩ := ih.2.2 lid entry hloan
              exact ⟨Nat.le_of_succ_le hle, hrest⟩
    | bool =>
      cases hloc : init.locals idx with
      | none => rw [hloc] at hExt; cases hExt
      | some mv =>
        rw [hloc] at hExt
        cases mv with
        | usize _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ => cases hExt
        | bool b =>
          dsimp at hExt
          cases hRest : extractSymArgsAux (idx + 1) restTys init with
          | none => rw [hRest] at hExt; cases hExt
          | some restArgs =>
            rw [hRest] at hExt
            injection hExt with hargs
            subst hargs
            have ih := extractSymArgsAux_spec restTys (idx + 1) init restArgs hIdxSucc1 hRest
            dsimp [buildPureSymStateAux]
            dsimp at ih
            refine ⟨?_, ?_, ?_⟩
            · intro i hilt
              have hne : i ≠ idx := Nat.ne_of_lt hilt
              have hb : (i == idx) = false := decide_eq_false hne
              unfold updateSymLocal
              rw [hb]
              exact ih.1 i (Nat.lt_trans hilt (Nat.lt_succ_self idx))
            · intro i sv hlookup
              unfold updateSymLocal at hlookup
              cases hb : (i == idx) with
              | true =>
                rw [hb] at hlookup
                injection hlookup with hsv
                have hi_eq : i = idx := of_decide_eq_true hb
                subst hi_eq hsv
                exact ⟨Nat.le_refl _, (by intro _ h; cases h), ⟨MirVal.bool b, hloc, rfl⟩⟩
              | false =>
                rw [hb] at hlookup
                have ⟨hle, hbor, hval⟩ := ih.2.1 i sv hlookup
                exact ⟨Nat.le_of_succ_le hle, hbor, hval⟩
            · intro lid entry hloan
              have ⟨hle, hrest⟩ := ih.2.2 lid entry hloan
              exact ⟨Nat.le_of_succ_le hle, hrest⟩
    | unit =>
      cases hloc : init.locals idx with
      | none => rw [hloc] at hExt; cases hExt
      | some mv =>
        rw [hloc] at hExt
        cases mv with
        | usize _ | bool _ | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ => cases hExt
        | unit =>
          dsimp at hExt
          cases hRest : extractSymArgsAux (idx + 1) restTys init with
          | none => rw [hRest] at hExt; cases hExt
          | some restArgs =>
            rw [hRest] at hExt
            injection hExt with hargs
            subst hargs
            have ih := extractSymArgsAux_spec restTys (idx + 1) init restArgs hIdxSucc1 hRest
            dsimp [buildPureSymStateAux]
            dsimp at ih
            refine ⟨?_, ?_, ?_⟩
            · intro i hilt
              have hne : i ≠ idx := Nat.ne_of_lt hilt
              have hb : (i == idx) = false := decide_eq_false hne
              unfold updateSymLocal
              rw [hb]
              exact ih.1 i (Nat.lt_trans hilt (Nat.lt_succ_self idx))
            · intro i sv hlookup
              unfold updateSymLocal at hlookup
              cases hb : (i == idx) with
              | true =>
                rw [hb] at hlookup
                injection hlookup with hsv
                have hi_eq : i = idx := of_decide_eq_true hb
                subst hi_eq hsv
                exact ⟨Nat.le_refl _, (by intro _ h; cases h), ⟨MirVal.unit, hloc, rfl⟩⟩
              | false =>
                rw [hb] at hlookup
                have ⟨hle, hbor, hval⟩ := ih.2.1 i sv hlookup
                exact ⟨Nat.le_of_succ_le hle, hbor, hval⟩
            · intro lid entry hloan
              have ⟨hle, hrest⟩ := ih.2.2 lid entry hloan
              exact ⟨Nat.le_of_succ_le hle, hrest⟩
    | refSharedUsize =>
      cases hloc : init.locals idx with
      | none => rw [hloc] at hExt; cases hExt
      | some mv =>
        rw [hloc] at hExt
        cases mv with
        | usize _ | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | ordering _ => cases hExt
        | refSharedLoc loc =>
          dsimp at hExt
          cases hchk : (noMutAliasBefore init.locals loc idx &&
            decide (init.mem.naWriteTs loc ≤ init.mem.curView loc)) with
          | false => rw [hchk] at hExt; cases hExt
          | true =>
            rw [hchk] at hExt
            dsimp at hExt
            cases hna : init.mem.naVal loc with
            | none => rw [hna] at hExt; cases hExt
            | some naMv =>
              rw [hna] at hExt
              cases naMv with
              | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ => cases hExt
              | usize n =>
                dsimp at hExt
                cases hRest : extractSymArgsAux (idx + 1) restTys init with
                | none => rw [hRest] at hExt; cases hExt
                | some restArgs =>
                  rw [hRest] at hExt
                  injection hExt with hargs
                  subst hargs
                  have hca := Eq.mp (Bool.and_eq_true _ _) hchk
                  have hnoMut : noMutAliasBefore init.locals loc idx = true := hca.1
                  have hwLe : init.mem.naWriteTs loc ≤ init.mem.curView loc := of_decide_eq_true hca.2
                  have hReadOwn : ReadOwnLoc init.mem loc (.usize n) := ⟨hna, hwLe⟩
                  have hInitShared : initSharedLoc init loc n :=
                    ⟨idx, hIdx1, hloc, hnoMut, hReadOwn⟩
                  have ih := extractSymArgsAux_spec restTys (idx + 1) init restArgs hIdxSucc1 hRest
                  dsimp [buildPureSymStateAux]
                  dsimp at ih
                  refine ⟨?_, ?_, ?_⟩
                  · intro i hilt
                    have hne : i ≠ idx := Nat.ne_of_lt hilt
                    have hb : (i == idx) = false := decide_eq_false hne
                    unfold updateSymLocal
                    rw [hb]
                    exact ih.1 i (Nat.lt_trans hilt (Nat.lt_succ_self idx))
                  · intro i sv hlookup
                    unfold updateSymLocal at hlookup
                    cases hb : (i == idx) with
                    | true =>
                      rw [hb] at hlookup
                      injection hlookup with hsv
                      have hi_eq : i = idx := of_decide_eq_true hb
                      subst hi_eq hsv
                      exact ⟨Nat.le_refl _, (by intro _ h; cases h),
                        ⟨MirVal.refSharedLoc loc, hloc, loc, hInitShared, rfl⟩⟩
                    | false =>
                      rw [hb] at hlookup
                      have ⟨hle, hbor, hval⟩ := ih.2.1 i sv hlookup
                      exact ⟨Nat.le_of_succ_le hle, hbor, hval⟩
                  · intro lid entry hloan
                    have ⟨hle, hrest⟩ := ih.2.2 lid entry hloan
                    exact ⟨Nat.le_of_succ_le hle, hrest⟩
    | refMutUsize =>
      cases hloc : init.locals idx with
      | none => rw [hloc] at hExt; cases hExt
      | some mv =>
        rw [hloc] at hExt
        cases mv with
        | usize _ | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | ordering _ => cases hExt
        | refMutLoc loc =>
          dsimp at hExt
          cases hchk : (noAliasBefore init.locals loc idx &&
            decide (init.mem.naWriteTs loc ≤ init.mem.curView loc) &&
            decide (init.mem.naReadTs loc ≤ init.mem.curView loc)) with
          | false => rw [hchk] at hExt; cases hExt
          | true =>
            rw [hchk] at hExt
            dsimp at hExt
            cases hna : init.mem.naVal loc with
            | none => rw [hna] at hExt; cases hExt
            | some naMv =>
              rw [hna] at hExt
              cases naMv with
              | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ => cases hExt
              | usize n =>
                dsimp at hExt
                cases hRest : extractSymArgsAux (idx + 1) restTys init with
                | none => rw [hRest] at hExt; cases hExt
                | some restArgs =>
                  rw [hRest] at hExt
                  injection hExt with hargs
                  subst hargs
                  have hca := Eq.mp (Bool.and_eq_true _ _) hchk
                  have hcb := Eq.mp (Bool.and_eq_true _ _) hca.1
                  have hnoAlias : noAliasBefore init.locals loc idx = true := hcb.1
                  have hwLe : init.mem.naWriteTs loc ≤ init.mem.curView loc := of_decide_eq_true hcb.2
                  have hrLe : init.mem.naReadTs loc ≤ init.mem.curView loc := of_decide_eq_true hca.2
                  have hOwn : OwnLoc init.mem loc (.usize n) := ⟨hna, hwLe, hrLe⟩
                  have hInitLoan : initLoanLoc init idx = some loc := by
                    unfold initLoanLoc
                    have hpos : decide (1 ≤ idx) = true := decide_eq_true hIdx1
                    rw [hpos]
                    dsimp
                    rw [hloc]
                    dsimp
                    rw [hnoAlias]
                    rfl
                  have ih := extractSymArgsAux_spec restTys (idx + 1) init restArgs hIdxSucc1 hRest
                  dsimp [buildPureSymStateAux]
                  dsimp at ih
                  refine ⟨?_, ?_, ?_⟩
                  · intro i hilt
                    have hne : i ≠ idx := Nat.ne_of_lt hilt
                    have hb : (i == idx) = false := decide_eq_false hne
                    unfold updateSymLocal updateLoan
                    rw [hb]
                    exact ih.1 i (Nat.lt_trans hilt (Nat.lt_succ_self idx))
                  · intro i sv hlookup
                    unfold updateSymLocal at hlookup
                    cases hb : (i == idx) with
                    | true =>
                      rw [hb] at hlookup
                      injection hlookup with hsv
                      have hi_eq : i = idx := of_decide_eq_true hb
                      subst hi_eq hsv
                      refine ⟨Nat.le_refl _, ?_, ⟨MirVal.refMutLoc loc, hloc, loc, hInitLoan, rfl⟩⟩
                      intro lid hlid
                      injection hlid with hlid_eq
                      subst hlid_eq
                      refine ⟨rootLoanEntry n, ?_⟩
                      unfold updateLoan
                      rw [hb]; rfl
                    | false =>
                      rw [hb] at hlookup
                      have ⟨hle, hbor, hval⟩ := ih.2.1 i sv hlookup
                      refine ⟨Nat.le_of_succ_le hle, ?_, hval⟩
                      intro lid hlid
                      exact loans_some_updateLoan idx (rootLoanEntry n) (hbor lid hlid)
                  · intro lid entry hloan
                    unfold updateLoan at hloan
                    cases hb : (lid == idx) with
                    | true =>
                      rw [hb] at hloan
                      injection hloan with hentry
                      have hlid_eq : lid = idx := of_decide_eq_true hb
                      subst hlid_eq hentry
                      exact ⟨Nat.le_refl _, rfl, rfl, rfl, loc, n,
                        hloc, hInitLoan, rfl, hOwn, hnoAlias⟩
                    | false =>
                      rw [hb] at hloan
                      have ⟨hle, hrest⟩ := ih.2.2 lid entry hloan
                      exact ⟨Nat.le_of_succ_le hle, hrest⟩

/-- Soundness of `extractSymArgs`: whenever `extractSymArgs argTys init = some
    args`,
    `StateRel (initLoanLoc init) (initSharedLoc init) (buildPureSymState args)
    init` holds. -/
theorem extractSymArgs_sound (argTys : List MirTy) (init : MirState) (args : List SymArg)
    (hExt : extractSymArgs argTys init = some args) :
    ∃ loanLoc sharedLoc, StateRel loanLoc sharedLoc (buildPureSymState args) init := by
  unfold extractSymArgs at hExt
  cases hblk : (init.block == 0 && init.stmtIdx == 0) with
  | false => rw [hblk] at hExt; cases hExt
  | true =>
    rw [hblk] at hExt
    have hba := Eq.mp (Bool.and_eq_true _ _) hblk
    have hblock : init.block = 0 := of_decide_eq_true hba.1
    have hstmtIdx : init.stmtIdx = 0 := of_decide_eq_true hba.2
    have hSpec := extractSymArgsAux_spec argTys 1 init args (Nat.le_refl 1) hExt
    unfold buildPureSymState
    dsimp at hSpec; dsimp
    refine ⟨initLoanLoc init, initSharedLoc init, {
      block_eq := hblock
      stmtIdx_eq := hstmtIdx
      localBorrows := fun i lid hi => (hSpec.2.1 i (.borrow lid) hi).2.1 lid rfl
      localRel := fun i sv hi => (hSpec.2.1 i sv hi).2.2
      loanRel := {
        activeOwn := by
          intro lid entry hl _ _
          have ⟨_, howners, _, _, loc, n, _, hinitLoc, hcur, hown, _⟩ :=
            hSpec.2.2 lid entry hl
          refine ⟨⟨loc, .usize n, hinitLoc, ?_, hown⟩, Or.inl howners⟩
          rw [hcur]; rfl
        disjointActive := by
          intro lid₁ lid₂ e₁ e₂ loc₁ loc₂ hne hl1 _ _ hl2 _ _ hloc1 hloc2
          have ⟨hle1, _, _, _, loc1', _, hinit1, hloanLoc1, _, _, hno1⟩ :=
            hSpec.2.2 lid₁ e₁ hl1
          have ⟨hle2, _, _, _, loc2', _, hinit2, hloanLoc2, _, _, hno2⟩ :=
            hSpec.2.2 lid₂ e₂ hl2
          rw [hloanLoc1] at hloc1; injection hloc1 with h1; subst h1
          rw [hloanLoc2] at hloc2; injection hloc2 with h2; subst h2
          cases Nat.lt_or_gt_of_ne hne with
          | inl hlt =>
            exact noAliasBefore_ne hle1 hlt hno2 hinit1
          | inr hgt =>
            exact (noAliasBefore_ne hle2 hgt hno1 hinit2).symm
        noJoinOwners := by
          intro _ lid entry hl _ _
          exact (hSpec.2.2 lid entry hl).2.1
        sharedOwn := fun _ _ ⟨_, _, _, _, hReadOwn⟩ => hReadOwn
        disjointShared := initLoanLoc_disjoint_shared init
      }
    }⟩

theorem extractSymArgsAux_of_argsMatchLocals :
    ∀ (tys : List MirTy) (idx : Nat) (init : MirState),
      allSupportedArgTys tys = true →
      List.foldr
        (fun ty rest k => (∃ v, init.locals k = some v ∧ argValidAt init.mem init.locals k v ty) ∧ rest (k + 1))
        (fun k => ∀ j, k ≤ j → init.locals j = none)
        tys idx →
      ∃ args, extractSymArgsAux idx tys init = some args
  | [], _, _, _, _ => ⟨[], rfl⟩
  | ty :: restTys, idx, init, hSupp, hFold => by
    dsimp [allSupportedArgTys, List.all, List.foldr] at hSupp
    have hsa := Eq.mp (Bool.and_eq_true _ _) hSupp
    have ⟨⟨v, hvLoc, hvValid⟩, hRestFold⟩ := hFold
    have ⟨restArgs, hRestExt⟩ :=
      extractSymArgsAux_of_argsMatchLocals restTys (idx + 1) init hsa.2 hRestFold
    cases ty with
    | tupleUsizeBool | refAtomicUsize | atomicOrdering => cases hsa.1
    | usize =>
      cases v with
      | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ => cases hvValid
      | usize n =>
        refine ⟨.usize n :: restArgs, ?_⟩
        dsimp [extractSymArgsAux]
        rw [hvLoc]
        dsimp
        rw [hRestExt]
    | bool =>
      cases v with
      | usize _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ => cases hvValid
      | bool b =>
        refine ⟨.bool b :: restArgs, ?_⟩
        dsimp [extractSymArgsAux]
        rw [hvLoc]
        dsimp
        rw [hRestExt]
    | unit =>
      cases v with
      | usize _ | bool _ | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ => cases hvValid
      | unit =>
        refine ⟨.unit :: restArgs, ?_⟩
        dsimp [extractSymArgsAux]
        rw [hvLoc]
        dsimp
        rw [hRestExt]
    | refSharedUsize =>
      have ⟨hHasTy, hdisj⟩ := hvValid
      cases v with
      | usize _ | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | ordering _ => cases hHasTy
      | refSharedLoc loc =>
        have ⟨n, hna, hw⟩ := hHasTy
        have hnoMut : noMutAliasBefore init.locals loc idx = true :=
          noMutAliasBefore_of_forall_ne init.locals loc idx (fun i hi1 hilt => hdisj loc i rfl hi1 hilt)
        have hwDec : decide (init.mem.naWriteTs loc ≤ init.mem.curView loc) = true :=
          decide_eq_true hw
        refine ⟨.refShared n :: restArgs, ?_⟩
        dsimp [extractSymArgsAux]
        rw [hvLoc]
        dsimp
        rw [hnoMut, hwDec]
        dsimp
        rw [hna]
        dsimp
        rw [hRestExt]
    | refMutUsize =>
      have ⟨hHasTy, hdisj⟩ := hvValid
      cases v with
      | usize _ | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | ordering _ => cases hHasTy
      | refMutLoc loc =>
        have ⟨n, hna, hw, hr⟩ := hHasTy
        have hnoAlias : noAliasBefore init.locals loc idx = true :=
          noAliasBefore_of_forall_ne init.locals loc idx (fun i hi1 hilt => hdisj loc i rfl hi1 hilt)
        have hwDec : decide (init.mem.naWriteTs loc ≤ init.mem.curView loc) = true :=
          decide_eq_true hw
        have hrDec : decide (init.mem.naReadTs loc ≤ init.mem.curView loc) = true :=
          decide_eq_true hr
        refine ⟨.refMut n :: restArgs, ?_⟩
        dsimp [extractSymArgsAux]
        rw [hvLoc]
        dsimp
        rw [hnoAlias, hwDec, hrDec]
        dsimp
        rw [hna]
        dsimp
        rw [hRestExt]

theorem extractSymArgs_of_initMirState {body : MirBody} {init : MirState}
    (hSupp : allSupportedArgTys body.argTys = true)
    (hInit : initMirState body init) :
    ∃ args, extractSymArgs body.argTys init = some args := by
  have hb : (init.block == 0) = true := decide_eq_true hInit.1
  have hs : (init.stmtIdx == 0) = true := decide_eq_true hInit.2.1
  unfold extractSymArgs
  rw [hb, hs]
  dsimp
  exact extractSymArgsAux_of_argsMatchLocals body.argTys 1 init hSupp hInit.2.2.2

/-- **Universal Hint-Independent Soundness Theorem (`evalSym_sound`)**:
    For **every** translation plan `plan : TransPlan` and **every** MIR body
    `body : MirBody`, `evalSym plan body` is a sound functional abstraction of
    `body` (`Abstracts FuncLang MirLang π_func (evalSym plan body) body`, i.e.,
    `MirLang.sem body ≤ π_func (FuncLang.sem (evalSym plan body))`). -/
theorem evalSym_sound (plan : TransPlan) (body : MirBody) :
    Abstracts FuncLang MirLang π_func (evalSym plan body) body := by
  intro q hdef
  have hne : evalSym plan body q.init ≠ .fail := hdef
  unfold evalSym at hne
  cases hSupp : allSupportedArgTys body.argTys with
  | false =>
    rw [hSupp] at hne
    exact False.elim (hne rfl)
  | true =>
    rw [hSupp] at hne
    dsimp at hne
    cases hExt : extractSymArgs body.argTys q.init with
    | none =>
      have hNotInit : ¬ initMirState body q.init := by
        intro hInit
        have ⟨args, hSome⟩ := extractSymArgs_of_initMirState hSupp hInit
        rw [hExt] at hSome
        cases hSome
      refine ⟨fun hInit => False.elim (hNotInit hInit), ?_⟩
      intro out hexec
      exact False.elim (hNotInit hexec.1)
    | some args =>
      rw [hExt] at hne
      dsimp at hne
      cases hRes : translatePure plan body args with
      | fail =>
        rw [hRes] at hne
        exact False.elim (hne rfl)
      | inapplicable =>
        exact False.elim (evalSymState_ne_inapplicable plan body (buildPureSymState args) hRes)
      | ok ret =>
        have ⟨loanLoc, sharedLoc, hState⟩ := extractSymArgs_sound body.argTys q.init args hExt
        have hSafe : SafeAndReturns body q.init ret :=
          evalSymState_sound plan body hState hRes
        have hMirDef : (MirLang.sem body q).defined :=
          fun _ tr out hreach => (hSafe q.init q.steps tr out hreach).1
        refine ⟨hMirDef, ?_⟩
        intro out hexec
        have h := hSafe q.init q.steps out.trace out.outcome hexec.2
        refine ⟨h.1, ?_⟩
        intro r hr
        have hr_eq : r = ret := h.2 r hr
        subst hr_eq
        change evalSym plan body q.init = .ok r
        unfold evalSym
        rw [hSupp]
        dsimp
        rw [hExt]
        exact hRes

/-!
## 8. Untrusted Heuristic Planner (`computePlan`) and `translate`

Because `evalSym_sound` holds for **all** `plan : TransPlan`, the
CFG-structuring
and NLL loan-termination heuristic `computePlan : MirBody → TransPlan` lives
entirely outside the soundness proof obligation (`translate_sound`).
-/

/-- Check whether `op : Operand` reads from local `locIdx`. -/
def operandAccessesLocal (op : Operand) (locIdx : Nat) : Bool :=
  match op with
  | .copy src | .move src => src.index == locIdx
  | .constVal _ => false

/-- Check whether `rv : Rvalue` reads from local `locIdx`. -/
def rvalueAccessesLocal (rv : Rvalue) (locIdx : Nat) : Bool :=
  match rv with
  | .use op => operandAccessesLocal op locIdx
  | .deref src | .proj0 src | .proj1 src => src.index == locIdx
  | .binaryOp _ lhs rhs | .checkedBinaryOp _ lhs rhs =>
    operandAccessesLocal lhs locIdx || operandAccessesLocal rhs locIdx

/-- Check whether `stmt : Stmt` reads from or writes to local `locIdx`.
    Used by `computePlanAux` to schedule `.endLoan` immediately before the
    first statement after a borrow join that accesses either frozen parent
    borrow (`falseSrc` or `trueSrc`). -/
def stmtAccessesLocal (stmt : Stmt) (locIdx : Nat) : Bool :=
  match stmt with
  | .assign dst rv => dst.index == locIdx || rvalueAccessesLocal rv locIdx
  | .assignDeref dst op => dst.index == locIdx || operandAccessesLocal op locIdx
  | .storageLive loc | .storageDead loc => loc.index == locIdx
  | .nop => false

/-- Fuel-bounded untrusted CFG and NLL loan-termination planner.
    - Detects diamond borrow joins (`matchBorrowArm` on both targets of a
      `switchInt` assigning the same destination local and jumping to the same
      join block) for `&mut usize` parameters and emits `.joinBorrow`.
    - Tracks `activeJoin : Option (Nat × Nat × Nat)` (`some (joinedLid,
      falseSrc, trueSrc)`)
      and emits `.endLoan joinedLid` immediately before the first statement in
      the join block that accesses either frozen parent local (`falseSrc` or
      `trueSrc`), or before `.return_`. -/
noncomputable def computePlanAux :
    Nat → MirBody → Nat → Nat → Option (Nat × Nat × Nat) → TransPlan
  | 0, _, _, _, _ => .fail
  | fuel + 1, body, blk, stmtIdx, activeJoin =>
    match body.blocks[blk]? with
    | none => .fail
    | some bb =>
      match bb.stmts[stmtIdx]? with
      | some stmt =>
        match activeJoin with
        | some (joinedLid, falseSrc, trueSrc) =>
          if stmtAccessesLocal stmt falseSrc || stmtAccessesLocal stmt trueSrc then
            .endLoan joinedLid (computePlanAux fuel body blk stmtIdx none)
          else
            .step (computePlanAux fuel body blk (stmtIdx + 1) activeJoin)
        | none =>
          .step (computePlanAux fuel body blk (stmtIdx + 1) none)
      | none =>
        match bb.terminator with
        | .return_ =>
          match body.retTy, activeJoin with
          | .refMutUsize, _ => .ret
          | _, some (joinedLid, _, _) => .endLoan joinedLid .ret
          | _, none => .ret
        | .goto target | .assertNotOverflow _ target | .callPure2 _ _ _ _ target =>
          .step (computePlanAux fuel body target.index 0 activeJoin)
        | .switchInt _ falseTarget trueTarget =>
          match activeJoin, body.blocks[falseTarget.index]?, body.blocks[trueTarget.index]? with
          | none, some bbFalse, some bbTrue =>
            match matchBorrowArm bbFalse, matchBorrowArm bbTrue with
            | some (dstF, srcF, joinF), some (dstT, srcT, joinT) =>
              match body.argTys[srcF - 1]?, body.argTys[srcT - 1]? with
              | some .refMutUsize, some .refMutUsize =>
                if dstF == dstT && joinF == joinT then
                  let joinedLid := dstF
                  .joinBorrow dstF srcF srcT joinF joinedLid
                    (computePlanAux fuel body joinF 0 (some (joinedLid, srcF, srcT)))
                else
                  .branch
                    (computePlanAux fuel body falseTarget.index 0 none)
                    (computePlanAux fuel body trueTarget.index 0 none)
              | _, _ =>
                .branch
                  (computePlanAux fuel body falseTarget.index 0 none)
                  (computePlanAux fuel body trueTarget.index 0 none)
            | _, _ =>
              .branch
                (computePlanAux fuel body falseTarget.index 0 none)
                (computePlanAux fuel body trueTarget.index 0 none)
          | _, _, _ =>
            .branch
              (computePlanAux fuel body falseTarget.index 0 activeJoin)
              (computePlanAux fuel body trueTarget.index 0 activeJoin)
        | .unreachable | .callAtomicLoad _ _ _ _ => .fail

/-- Untrusted heuristic planner computing a `TransPlan` for `body : MirBody`. -/
noncomputable def computePlan (body : MirBody) : TransPlan :=
  computePlanAux 64 body 0 0 none

/-- Top-level Aeneas-inspired functional translator mapping a `MirBody` to a
    `FuncLang.Prog` by pairing the untrusted `computePlan` with the verified
    evaluator `evalSym`. -/
noncomputable def translate (body : MirBody) : FuncLang.Prog :=
  evalSym (computePlan body) body

/-- **Soundness of `translate`**: immediate 1-line specialization of
    `evalSym_sound` to `computePlan body`, requiring zero proof obligations on
    `computePlan`. -/
theorem translate_sound (body : MirBody) :
    Abstracts FuncLang MirLang π_func (translate body) body :=
  evalSym_sound (computePlan body) body

/-!
## 9. Verification of `max_assign` and `update_min`
-/

/-- Exact `Runtime(PostCleanup)` MIR body emitted by `rustc --edition=2024
    --emit=mir`
    for:
    ```rust
    pub fn max_assign(x: &mut usize, y: usize) -> usize {
        if *x < y {
            *x = y;
        }
        *x
    }
    ```
    - `_0: usize` (return place), `_1: &mut usize` (`x`), `_2: usize` (`y`),
      `_3: bool`, `_4: usize`.
    - `bb0`: `_4 = copy (*_1); _3 = Lt(move _4, copy _2); switchInt(move _3) ->
      [0: bb2, otherwise: bb1];`
    - `bb1`: `(*_1) = copy _2; goto -> bb2;`
    - `bb2`: `_0 = copy (*_1); return;` -/
def maxAssignBody : MirBody where
  argTys := [.refMutUsize, .usize]
  retTy := .usize
  localCount := 5
  blocks := [
    { stmts := [
        .assign ⟨4⟩ (.deref ⟨1⟩),
        .assign ⟨3⟩ (.binaryOp .lt (.move ⟨4⟩) (.copy ⟨2⟩))
      ]
      terminator := .switchInt (.move ⟨3⟩) ⟨2⟩ ⟨1⟩ },
    { stmts := [
        .assignDeref ⟨1⟩ (.copy ⟨2⟩)
      ]
      terminator := .goto ⟨2⟩ },
    { stmts := [
        .assign ⟨0⟩ (.deref ⟨1⟩)
      ]
      terminator := .return_ }
  ]

/-- Exact `Runtime(PostCleanup)` MIR body emitted by `rustc --edition=2024
    --emit=mir`
    for:
    ```rust
    pub fn update_min(x: &mut usize, y: &mut usize, v: usize) -> usize {
        let r = if *x <= *y { &mut *x } else { &mut *y };
        *r = v;
        *x
    }
    ```
    - `_0: usize` (return place), `_1: &mut usize` (`x`), `_2: &mut usize`
      (`y`),
      `_3: usize` (`v`), `_4: &mut usize` (`r`), `_5: bool`, `_6: usize`, `_7:
      usize`.
    - `bb0`: `_6 = copy (*_1); _7 = copy (*_2); _5 = Le(move _6, move _7);
      switchInt(move _5) -> [0: bb2, otherwise: bb1];`
    - `bb1`: `_4 = copy _1; goto -> bb3;`
    - `bb2`: `_4 = copy _2; goto -> bb3;`
    - `bb3`: `(*_4) = copy _3; _0 = copy (*_1); return;` -/
def updateMinBody : MirBody where
  argTys := [.refMutUsize, .refMutUsize, .usize]
  retTy := .usize
  localCount := 8
  blocks := [
    { stmts := [
        .assign ⟨6⟩ (.deref ⟨1⟩),
        .assign ⟨7⟩ (.deref ⟨2⟩),
        .assign ⟨5⟩ (.binaryOp .le (.move ⟨6⟩) (.move ⟨7⟩))
      ]
      terminator := .switchInt (.move ⟨5⟩) ⟨2⟩ ⟨1⟩ },
    { stmts := [
        .assign ⟨4⟩ (.use (.copy ⟨1⟩))
      ]
      terminator := .goto ⟨3⟩ },
    { stmts := [
        .assign ⟨4⟩ (.use (.copy ⟨2⟩))
      ]
      terminator := .goto ⟨3⟩ },
    { stmts := [
        .assignDeref ⟨4⟩ (.copy ⟨3⟩),
        .assign ⟨0⟩ (.deref ⟨1⟩)
      ]
      terminator := .return_ }
  ]

/-- `computePlan maxAssignBody` automatically structures `bb0`'s `switchInt`
    into a `.branch` over the false path (`bb2`) and true path (`bb1 → bb2`). -/
theorem computePlan_maxAssignBody_eq :
    computePlan maxAssignBody =
      .step (.step (.branch (.step .ret) (.step (.step (.step .ret))))) :=
  rfl

/-- `computePlan updateMinBody` automatically detects the diamond borrow join
    (`bb2` copying `_2`, `bb1` copying `_1` into `_4` and jumping to `bb3`) and
    schedules `.endLoan 4` immediately before `_0 = copy (*_1)` in `bb3`. -/
theorem computePlan_updateMinBody_eq :
    computePlan updateMinBody =
      .step (.step (.step
        (.joinBorrow 4 2 1 3 4
          (.step (.endLoan 4 (.step .ret)))))) :=
  rfl

/-- **First Futamura Projection for `max_assign`**:
    Evaluating `translatePure (computePlan maxAssignBody) maxAssignBody` on
    universally quantified symbolic inputs `x0 y0 : Nat` reduces by kernel
    `rfl` directly to `.ok (.usize (if decide (x0 < y0) then y0 else x0))`. -/
theorem translatePure_maxAssign_rfl (x0 y0 : Nat) :
    translatePure (computePlan maxAssignBody) maxAssignBody [.refMut x0, .usize y0] =
      .ok (.usize (if decide (x0 < y0) then y0 else x0)) :=
  rfl

/-- **First Futamura Projection for `update_min`**:
    Evaluating `translatePure (computePlan updateMinBody) updateMinBody` on
    universally quantified symbolic inputs `x0 y0 v0 : Nat` reduces by kernel
    `rfl` directly to `.ok (.usize (if decide (x0 ≤ y0) then v0 else x0))`. -/
theorem translatePure_updateMin_rfl (x0 y0 v0 : Nat) :
    translatePure (computePlan updateMinBody) updateMinBody [.refMut x0, .refMut y0, .usize v0] =
      .ok (.usize (if decide (x0 ≤ y0) then v0 else x0)) :=
  rfl

/-- Pure functional specification extracted from `maxAssignBody`. -/
def pureMaxAssign (x0 y0 : Nat) : Nat :=
  if decide (x0 < y0) then y0 else x0

/-- Pure functional return specification extracted from `updateMinBody`. -/
def pureUpdateMinRet (x0 y0 v0 : Nat) : Nat :=
  if decide (x0 ≤ y0) then v0 else x0

/-- Pure functional post-state pair `(x', y')` for `update_min`. -/
def pureUpdateMinPair (x0 y0 v0 : Nat) : Nat × Nat :=
  (if decide (x0 ≤ y0) then v0 else x0,
   if decide (x0 ≤ y0) then y0 else v0)

/-- Non-trivial property 1 (`max_assign` left upper bound):
    `x0 ≤ pureMaxAssign x0 y0`. -/
theorem pureMaxAssign_ge_left (x0 y0 : Nat) :
    x0 ≤ pureMaxAssign x0 y0 := by
  unfold pureMaxAssign
  cases h : decide (x0 < y0) with
  | false => exact Nat.le_refl x0
  | true => exact Nat.le_of_lt (of_decide_eq_true h)

/-- Non-trivial property 2 (`max_assign` right upper bound):
    `y0 ≤ pureMaxAssign x0 y0`. -/
theorem pureMaxAssign_ge_right (x0 y0 : Nat) :
    y0 ≤ pureMaxAssign x0 y0 := by
  unfold pureMaxAssign
  cases h : decide (x0 < y0) with
  | false => exact Nat.le_of_not_lt (of_decide_eq_false h)
  | true => exact Nat.le_refl y0

/-- Non-trivial property 3 (`max_assign` choice):
    `pureMaxAssign x0 y0` is always equal to either `x0` or `y0`. -/
theorem pureMaxAssign_eq_left_or_right (x0 y0 : Nat) :
    pureMaxAssign x0 y0 = x0 ∨ pureMaxAssign x0 y0 = y0 := by
  unfold pureMaxAssign
  cases decide (x0 < y0) with
  | false => exact Or.inl rfl
  | true => exact Or.inr rfl

/-- Non-trivial property 4 (`max_assign` least upper bound):
    Any common upper bound `z` of `x0` and `y0` bounds `pureMaxAssign x0 y0`. -/
theorem pureMaxAssign_least_upper_bound (x0 y0 z : Nat)
    (hx : x0 ≤ z) (hy : y0 ≤ z) :
    pureMaxAssign x0 y0 ≤ z := by
  unfold pureMaxAssign
  cases decide (x0 < y0) with
  | false => exact hx
  | true => exact hy

/-- Non-trivial property 5 (`max_assign` idempotence):
    `pureMaxAssign x0 x0 = x0`. -/
theorem pureMaxAssign_idempotent (x0 : Nat) :
    pureMaxAssign x0 x0 = x0 := by
  unfold pureMaxAssign
  have h : decide (x0 < x0) = false := decide_eq_false (Nat.lt_irrefl x0)
  rw [h]; rfl

/-- Non-trivial property 6 (`max_assign` commutativity):
    `pureMaxAssign x0 y0 = pureMaxAssign y0 x0`. -/
theorem pureMaxAssign_comm (x0 y0 : Nat) :
    pureMaxAssign x0 y0 = pureMaxAssign y0 x0 := by
  unfold pureMaxAssign
  cases h1 : decide (x0 < y0) with
  | true =>
    have hlt : x0 < y0 := of_decide_eq_true h1
    have h2 : decide (y0 < x0) = false :=
      decide_eq_false (Nat.not_lt_of_gt hlt)
    rw [h2]; rfl
  | false =>
    have hnot1 : ¬ (x0 < y0) := of_decide_eq_false h1
    cases h2 : decide (y0 < x0) with
    | true => rfl
    | false =>
      have hnot2 : ¬ (y0 < x0) := of_decide_eq_false h2
      exact Nat.le_antisymm (Nat.le_of_not_lt hnot2) (Nat.le_of_not_lt hnot1)

/-- Non-trivial property 7 (`update_min` active mutation when `x0 ≤ y0`):
    When `x0 ≤ y0`, `r` borrows `x`, so `*r = v0` updates `*x` to `v0`. -/
theorem pureUpdateMinRet_of_le (x0 y0 v0 : Nat) (hle : x0 ≤ y0) :
    pureUpdateMinRet x0 y0 v0 = v0 := by
  unfold pureUpdateMinRet
  have h : decide (x0 ≤ y0) = true := decide_eq_true hle
  rw [h]; rfl

/-- Non-trivial property 8 (`update_min` frame preservation when `y0 < x0`):
    When `y0 < x0`, `r` borrows `y` instead of `x`, so `*r = v0` leaves `*x`
    unchanged at `x0` regardless of `v0`. -/
theorem pureUpdateMinRet_frame_of_gt (x0 y0 v0 : Nat) (hgt : y0 < x0) :
    pureUpdateMinRet x0 y0 v0 = x0 := by
  unfold pureUpdateMinRet
  have h : decide (x0 ≤ y0) = false := decide_eq_false (Nat.not_le_of_gt hgt)
  rw [h]; rfl

/-- Non-trivial property 9 (`update_min` sum conservation law):
    The sum of the post-state pair `(x', y')` plus the overwritten minimum
    (`if decide (x0 ≤ y0) then x0 else y0`) equals `x0 + y0 + v0`. -/
theorem pureUpdateMinPair_sum_conservation (x0 y0 v0 : Nat) :
    (pureUpdateMinPair x0 y0 v0).1 + (pureUpdateMinPair x0 y0 v0).2 +
      (if decide (x0 ≤ y0) then x0 else y0) =
      v0 + y0 + x0 ∨
    (pureUpdateMinPair x0 y0 v0).1 + (pureUpdateMinPair x0 y0 v0).2 +
      (if decide (x0 ≤ y0) then x0 else y0) =
      x0 + v0 + y0 := by
  unfold pureUpdateMinPair
  cases decide (x0 ≤ y0) with
  | true => exact Or.inl rfl
  | false => exact Or.inr rfl

/-- Non-trivial property 10 (`update_min` monotonicity under upper-bound `v0`):
    Whenever `x0 ≤ v0` and `y0 ≤ v0`, both components of `pureUpdateMinPair`
    are at least their initial values (`x0 ≤ x' ∧ y0 ≤ y'`). -/
theorem pureUpdateMinPair_ge_initial (x0 y0 v0 : Nat)
    (hx : x0 ≤ v0) (hy : y0 ≤ v0) :
    x0 ≤ (pureUpdateMinPair x0 y0 v0).1 ∧
    y0 ≤ (pureUpdateMinPair x0 y0 v0).2 := by
  unfold pureUpdateMinPair
  cases decide (x0 ≤ y0) with
  | true => exact ⟨hx, Nat.le_refl y0⟩
  | false => exact ⟨Nat.le_refl x0, hy⟩

/-- Functional postcondition for `max_assign` in `FuncLang`. -/
def FuncPostMaxAssign (init : MirState) (ret : MirVal) : Prop :=
  ∀ loc x0 y0,
    init.locals 1 = some (.refMutLoc loc) →
    init.mem.naVal loc = some (.usize x0) →
    init.locals 2 = some (.usize y0) →
    ret = .usize (if decide (x0 < y0) then y0 else x0)

/-- Functional postcondition for `update_min` in `FuncLang`. -/
def FuncPostUpdateMin (init : MirState) (ret : MirVal) : Prop :=
  ∀ locX locY x0 y0 v0,
    init.locals 1 = some (.refMutLoc locX) →
    init.mem.naVal locX = some (.usize x0) →
    init.locals 2 = some (.refMutLoc locY) →
    init.mem.naVal locY = some (.usize y0) →
    init.locals 3 = some (.usize v0) →
    ret = .usize (if decide (x0 ≤ y0) then v0 else x0)

/-- Pointwise elimination of `FuncLang.sem p ≤ FuncLang.Spec Post` into a plain
    `AeneasRes MirVal` obligation at each `init : MirState`. -/
theorem funcSem_le_spec {p : MirState → AeneasRes MirVal}
    {Post : MirState → MirVal → Prop}
    (hEval : ∀ init, p init ≠ .fail ∧ (∀ ret, p init = .ok ret → Post init ret)) :
    FuncLang.sem p ≤ FuncLang.Spec Post :=
  fun init _ => ⟨(hEval init).1, (hEval init).2⟩

/-- `translate maxAssignBody` satisfies `FuncLang.Spec FuncPostMaxAssign`:
    proved purely in `FuncLang` by reducing `translatePure` via `rfl`
    (`translatePure_maxAssign_rfl`). -/
theorem translate_maxAssignBody_spec :
    FuncLang.sem (translate maxAssignBody) ≤ FuncLang.Spec FuncPostMaxAssign := by
  refine funcSem_le_spec (fun init => ?_)
  unfold translate evalSym
  have hSupp : allSupportedArgTys maxAssignBody.argTys = true := rfl
  rw [hSupp]
  dsimp
  cases hExt : extractSymArgs maxAssignBody.argTys init with
  | none =>
    refine ⟨(by intro h; cases h), ?_⟩
    intro ret hok
    cases hok
  | some args =>
    unfold extractSymArgs at hExt
    cases hblk : (init.block == 0 && init.stmtIdx == 0) with
    | false => rw [hblk] at hExt; cases hExt
    | true =>
      rw [hblk] at hExt
      dsimp [ maxAssignBody, extractSymArgsAux ] at hExt
      cases hloc1 : init.locals 1 with
      | none => rw [hloc1] at hExt; cases hExt
      | some mv1 =>
        rw [hloc1] at hExt
        cases mv1 with
        | usize _ | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | ordering _ => cases hExt
        | refMutLoc loc1 =>
          dsimp at hExt
          cases hchk1 : (noAliasBefore init.locals loc1 1 &&
            decide (init.mem.naWriteTs loc1 ≤ init.mem.curView loc1) &&
            decide (init.mem.naReadTs loc1 ≤ init.mem.curView loc1)) with
          | false => rw [hchk1] at hExt; cases hExt
          | true =>
            rw [hchk1] at hExt
            dsimp at hExt
            cases hna1 : init.mem.naVal loc1 with
            | none => rw [hna1] at hExt; cases hExt
            | some naMv1 =>
              rw [hna1] at hExt
              cases naMv1 with
              | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ => cases hExt
              | usize x0' =>
                dsimp at hExt
                cases hloc2 : init.locals 2 with
                | none => rw [hloc2] at hExt; cases hExt
                | some mv2 =>
                  rw [hloc2] at hExt
                  cases mv2 with
                  | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ => cases hExt
                  | usize y0' =>
                    dsimp at hExt
                    injection hExt with hargs
                    subst hargs
                    dsimp
                    rw [translatePure_maxAssign_rfl x0' y0']
                    refine ⟨(by intro h; cases h), ?_⟩
                    intro ret hok loc x0 y0 hl1 hm1 hl2
                    injection hok with hret
                    rw [hloc1] at hl1; injection hl1 with hloc_mv; injection hloc_mv with hloc_eq; subst hloc_eq
                    rw [hna1] at hm1; injection hm1 with hx_mv; injection hx_mv with hx_eq; subst hx_eq
                    rw [hloc2] at hl2; injection hl2 with hy_mv; injection hy_mv with hy_eq; subst hy_eq
                    exact hret.symm

/-- `translate updateMinBody` satisfies `FuncLang.Spec FuncPostUpdateMin`:
    proved purely in `FuncLang` by reducing `translatePure` via `rfl`
    (`translatePure_updateMin_rfl`). -/
theorem translate_updateMinBody_spec :
    FuncLang.sem (translate updateMinBody) ≤ FuncLang.Spec FuncPostUpdateMin := by
  refine funcSem_le_spec (fun init => ?_)
  unfold translate evalSym
  have hSupp : allSupportedArgTys updateMinBody.argTys = true := rfl
  rw [hSupp]
  dsimp
  cases hExt : extractSymArgs updateMinBody.argTys init with
  | none =>
    refine ⟨(by intro h; cases h), ?_⟩
    intro ret hok
    cases hok
  | some args =>
    unfold extractSymArgs at hExt
    cases hblk : (init.block == 0 && init.stmtIdx == 0) with
    | false => rw [hblk] at hExt; cases hExt
    | true =>
      rw [hblk] at hExt
      dsimp [ updateMinBody, extractSymArgsAux ] at hExt
      cases hloc1 : init.locals 1 with
      | none => rw [hloc1] at hExt; cases hExt
      | some mv1 =>
        rw [hloc1] at hExt
        cases mv1 with
        | usize _ | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | ordering _ => cases hExt
        | refMutLoc loc1 =>
          dsimp at hExt
          cases hchk1 : (noAliasBefore init.locals loc1 1 &&
            decide (init.mem.naWriteTs loc1 ≤ init.mem.curView loc1) &&
            decide (init.mem.naReadTs loc1 ≤ init.mem.curView loc1)) with
          | false => rw [hchk1] at hExt; cases hExt
          | true =>
            rw [hchk1] at hExt
            dsimp at hExt
            cases hna1 : init.mem.naVal loc1 with
            | none => rw [hna1] at hExt; cases hExt
            | some naMv1 =>
              rw [hna1] at hExt
              cases naMv1 with
              | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ => cases hExt
              | usize x0' =>
                dsimp at hExt
                cases hloc2 : init.locals 2 with
                | none => rw [hloc2] at hExt; cases hExt
                | some mv2 =>
                  rw [hloc2] at hExt
                  cases mv2 with
                  | usize _ | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | ordering _ => cases hExt
                  | refMutLoc loc2 =>
                    dsimp at hExt
                    cases hchk2 : (noAliasBefore init.locals loc2 2 &&
                      decide (init.mem.naWriteTs loc2 ≤ init.mem.curView loc2) &&
                      decide (init.mem.naReadTs loc2 ≤ init.mem.curView loc2)) with
                    | false => rw [hchk2] at hExt; cases hExt
                    | true =>
                      rw [hchk2] at hExt
                      dsimp at hExt
                      cases hna2 : init.mem.naVal loc2 with
                      | none => rw [hna2] at hExt; cases hExt
                      | some naMv2 =>
                        rw [hna2] at hExt
                        cases naMv2 with
                        | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ => cases hExt
                        | usize y0' =>
                          dsimp at hExt
                          cases hloc3 : init.locals 3 with
                          | none => rw [hloc3] at hExt; cases hExt
                          | some mv3 =>
                            rw [hloc3] at hExt
                            cases mv3 with
                            | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ => cases hExt
                            | usize v0' =>
                              dsimp at hExt
                              injection hExt with hargs
                              subst hargs
                              dsimp
                              rw [translatePure_updateMin_rfl x0' y0' v0']
                              refine ⟨(by intro h; cases h), ?_⟩
                              intro ret hok locX locY x0 y0 v0 hl1 hm1 hl2 hm2 hl3
                              injection hok with hret
                              rw [hloc1] at hl1; injection hl1 with h1_mv; injection h1_mv with h1; subst h1
                              rw [hna1] at hm1; injection hm1 with hx_mv; injection hx_mv with hx; subst hx
                              rw [hloc2] at hl2; injection hl2 with h2_mv; injection h2_mv with h2; subst h2
                              rw [hna2] at hm2; injection hm2 with hy_mv; injection hy_mv with hy; subst hy
                              rw [hloc3] at hl3; injection hl3 with hv_mv; injection hv_mv with hv; subst hv
                              exact hret.symm

/-- `π_func (FuncLang.Spec FuncPostMaxAssign)` refines `EnsuresMaxAssign`. -/
theorem π_func_maxAssign_le_ensures :
    π_func (FuncLang.Spec FuncPostMaxAssign) ≤ EnsuresMaxAssign := by
  refine Preorder.le_trans (π_func_spec_le FuncPostMaxAssign) ?_
  intro q _
  refine ⟨True.intro, ?_⟩
  intro out hpost ret loc x0 y0 hterm hl1 hm1 hl2
  exact hpost ret hterm loc x0 y0 hl1 hm1 hl2

/-- `π_func (FuncLang.Spec FuncPostUpdateMin)` refines `EnsuresUpdateMin`. -/
theorem π_func_updateMin_le_ensures :
    π_func (FuncLang.Spec FuncPostUpdateMin) ≤ EnsuresUpdateMin := by
  refine Preorder.le_trans (π_func_spec_le FuncPostUpdateMin) ?_
  intro q _
  refine ⟨True.intro, ?_⟩
  intro out hpost ret locX locY x0 y0 v0 hterm hl1 hm1 hl2 hm2 hl3
  exact hpost ret hterm locX locY x0 y0 v0 hl1 hm1 hl2 hm2 hl3

/-- `EnsuresMaxAssign` refines baseline `MirLang.WellFormed`. -/
theorem ensuresMaxAssign_le_wellFormed :
    EnsuresMaxAssign ≤ MirLang.WellFormed :=
  fun _ _ => ⟨True.intro, fun _ _ => True.intro⟩

/-- `EnsuresUpdateMin` refines baseline `MirLang.WellFormed`. -/
theorem ensuresUpdateMin_le_wellFormed :
    EnsuresUpdateMin ≤ MirLang.WellFormed :=
  fun _ _ => ⟨True.intro, fun _ _ => True.intro⟩

/-- **Source MIR Correctness of `max_assign`**:
    `MirSem maxAssignBody ≤ EnsuresMaxAssign`, transferred across `π_func` from
    `translate_maxAssignBody_spec` via `translate_sound maxAssignBody`. -/
theorem maxAssignBody_satisfies_ensures :
    MirSem maxAssignBody ≤ EnsuresMaxAssign :=
  Preorder.le_trans
    (Preorder.le_trans
      (translate_sound maxAssignBody)
      (monotone_π_func translate_maxAssignBody_spec))
    π_func_maxAssign_le_ensures

/-- `maxAssignBody` satisfies baseline `MirLang.WellFormed`. -/
theorem maxAssignBody_satisfies_wellFormed :
    MirSem maxAssignBody ≤ MirLang.WellFormed :=
  Preorder.le_trans maxAssignBody_satisfies_ensures ensuresMaxAssign_le_wellFormed

/-- **Source MIR Correctness of `update_min`**:
    `MirSem updateMinBody ≤ EnsuresUpdateMin`, transferred across `π_func` from
    `translate_updateMinBody_spec` via `translate_sound updateMinBody`. -/
theorem updateMinBody_satisfies_ensures :
    MirSem updateMinBody ≤ EnsuresUpdateMin :=
  Preorder.le_trans
    (Preorder.le_trans
      (translate_sound updateMinBody)
      (monotone_π_func translate_updateMinBody_spec))
    π_func_updateMin_le_ensures

/-- `updateMinBody` satisfies baseline `MirLang.WellFormed`. -/
theorem updateMinBody_satisfies_wellFormed :
    MirSem updateMinBody ≤ MirLang.WellFormed :=
  Preorder.le_trans updateMinBody_satisfies_ensures ensuresUpdateMin_le_wellFormed

/-- End-to-end `CrateTheorem` witness for `max_assign` with `EnsuresMaxAssign`,
    discharged through `verify_through_passes` using `translate_sound`. -/
theorem prove_max_assign_ensures_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := maxAssignBody
        specs := [EnsuresMaxAssign]
      }]
      tcb := [.rustcLowering fnName maxAssignBody]
    } := by
  refine ⟨(by intro h; cases h), ⟨⟨True.intro, True.intro⟩, ?_⟩, True.intro⟩
  intro hAssumptions
  have hVerFunc :
      RustcCompiler.Verified maxAssignBody (π_func (FuncLang.Spec FuncPostMaxAssign)) :=
    verify_through_passes
      translate_maxAssignBody_spec
      (translate_sound maxAssignBody)
      monotone_π_func
      hAssumptions.1
  have hVerEnsures : RustcCompiler.Verified maxAssignBody EnsuresMaxAssign :=
    Compiler.Verified.mono hVerFunc π_func_maxAssign_le_ensures hAssumptions.1.1
  exact Compiler.Verified.with_wellFormedOn
    hVerEnsures
    ensuresMaxAssign_le_wellFormed
    hAssumptions.1.1

/-- End-to-end `CrateTheorem` witness for `max_assign` with baseline
    `WellFormed`. -/
theorem prove_max_assign_wf_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := maxAssignBody
        specs := []
      }]
      tcb := [.rustcLowering fnName maxAssignBody]
    } :=
  verify_single_fn_wf_crate fnName maxAssignBody maxAssignBody_satisfies_wellFormed

/-- End-to-end `CrateTheorem` witness for `update_min` with `EnsuresUpdateMin`,
    discharged through `verify_through_passes` using `translate_sound`. -/
theorem prove_update_min_ensures_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := updateMinBody
        specs := [EnsuresUpdateMin]
      }]
      tcb := [.rustcLowering fnName updateMinBody]
    } := by
  refine ⟨(by intro h; cases h), ⟨⟨True.intro, True.intro⟩, ?_⟩, True.intro⟩
  intro hAssumptions
  have hVerFunc :
      RustcCompiler.Verified updateMinBody (π_func (FuncLang.Spec FuncPostUpdateMin)) :=
    verify_through_passes
      translate_updateMinBody_spec
      (translate_sound updateMinBody)
      monotone_π_func
      hAssumptions.1
  have hVerEnsures : RustcCompiler.Verified updateMinBody EnsuresUpdateMin :=
    Compiler.Verified.mono hVerFunc π_func_updateMin_le_ensures hAssumptions.1.1
  exact Compiler.Verified.with_wellFormedOn
    hVerEnsures
    ensuresUpdateMin_le_wellFormed
    hAssumptions.1.1

/-- End-to-end `CrateTheorem` witness for `update_min` with baseline
    `WellFormed`. -/
theorem prove_update_min_wf_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := updateMinBody
        specs := []
      }]
      tcb := [.rustcLowering fnName updateMinBody]
    } :=
  verify_single_fn_wf_crate fnName updateMinBody updateMinBody_satisfies_wellFormed

/-- **Plan-Adequacy Canary (`updateMinBadPlan`)**:
    A defective `TransPlan` for `updateMinBody` that omits `.endLoan 4` before
    reading `_0 = copy (*_1)` in `bb3`.
    1. By `evalSym_sound updateMinBadPlan updateMinBody`, `evalSym` remains
       sound even on this defective plan (universal hint-independent soundness).
    2. Because loan `1` (`x`) is still frozen when `_0 = copy (*_1)` executes,
       `translatePure updateMinBadPlan updateMinBody` evaluates to `.fail`
       (`Partial.ub`), which is rejected by `FuncLang.WellFormed`. -/
def updateMinBadPlan : TransPlan :=
  .step (.step (.step
    (.joinBorrow 4 2 1 3 4
      (.step (.step .ret)))))

theorem updateMinBadPlan_still_sound :
    Abstracts FuncLang MirLang π_func (evalSym updateMinBadPlan updateMinBody) updateMinBody :=
  evalSym_sound updateMinBadPlan updateMinBody

theorem translatePure_updateMinBadPlan_fails (x0 y0 v0 : Nat) :
    translatePure updateMinBadPlan updateMinBody [.refMut x0, .refMut y0, .usize v0] = .fail :=
  rfl

/-- Concrete initial `MirState` witness for `updateMinBody` with `x = 10` at
    location `0`, `y = 20` at location `1`, and `v = 99`. -/
def sampleUpdateMinInit : MirState where
  locals := fun
    | 1 => some (.refMutLoc 0)
    | 2 => some (.refMutLoc 1)
    | 3 => some (.usize 99)
    | _ => none
  mem := {
    curView := fun _ => 0
    naVal := fun
      | 0 => some (.usize 10)
      | 1 => some (.usize 20)
      | _ => none
    naWriteTs := fun _ => 0
    naReadTs := fun _ => 0
    atomicMsgs := []
  }
  block := 0
  stmtIdx := 0

/-- `updateMinBadPlan` is rejected by `FuncLang.WellFormed` because it returns
    `.fail` (`defined := False`) on `sampleUpdateMinInit`. -/
theorem updateMinBadPlan_rejected_by_wellFormed :
    ¬ (FuncLang.sem (evalSym updateMinBadPlan updateMinBody) ≤ FuncLang.WellFormed) := by
  intro hwf
  have ⟨hdef, _⟩ := hwf sampleUpdateMinInit True.intro
  exact hdef rfl

/-!
## 10. Verification of `clamp_assign` and `is_aligned_mask`
-/

/-- Exact `Runtime(PostCleanup)` MIR body emitted by `rustc --edition=2024
    --emit=mir`
    for:
    ```rust
    pub fn clamp_assign(x: &mut usize, lo: usize, hi: usize) -> usize {
        if *x < lo {
            *x = lo;
        } else if *x > hi {
            *x = hi;
        }
        *x
    }
    ``` -/
def clampAssignBody : MirBody where
  argTys := [.refMutUsize, .usize, .usize]
  retTy := .usize
  localCount := 8
  blocks := [
    { stmts := [
        .assign ⟨5⟩ (.deref ⟨1⟩),
        .assign ⟨4⟩ (.binaryOp .lt (.move ⟨5⟩) (.copy ⟨2⟩))
      ]
      terminator := .switchInt (.move ⟨4⟩) ⟨2⟩ ⟨1⟩ },
    { stmts := [
        .assignDeref ⟨1⟩ (.copy ⟨2⟩)
      ]
      terminator := .goto ⟨4⟩ },
    { stmts := [
        .assign ⟨7⟩ (.deref ⟨1⟩),
        .assign ⟨6⟩ (.binaryOp .gt (.move ⟨7⟩) (.copy ⟨3⟩))
      ]
      terminator := .switchInt (.move ⟨6⟩) ⟨4⟩ ⟨3⟩ },
    { stmts := [
        .assignDeref ⟨1⟩ (.copy ⟨3⟩)
      ]
      terminator := .goto ⟨4⟩ },
    { stmts := [
        .assign ⟨0⟩ (.deref ⟨1⟩)
      ]
      terminator := .return_ }
  ]

/-- Exact `Runtime(PostCleanup)` MIR body emitted by `rustc --edition=2024
    --emit=mir`
    for:
    ```rust
    pub fn is_aligned_mask(addr: usize, mask: usize) -> bool {
        (addr & mask) == 0
    }
    ``` -/
def isAlignedMaskBody : MirBody where
  argTys := [.usize, .usize]
  retTy := .bool
  localCount := 4
  blocks := [
    { stmts := [
        .assign ⟨3⟩ (.binaryOp .bitAnd (.copy ⟨1⟩) (.copy ⟨2⟩)),
        .assign ⟨0⟩ (.binaryOp .eq (.move ⟨3⟩) (.constVal (.usize 0)))
      ]
      terminator := .return_ }
  ]

/-- **First Futamura Projection for `clamp_assign`**:
    Evaluating `translatePure (computePlan clampAssignBody) clampAssignBody` on
    universally quantified symbolic inputs `x0 lo hi : Nat` reduces by kernel
    `rfl` directly to `.ok (.usize (if decide (x0 < lo) then lo else if decide
    (hi < x0) then hi else x0))`. -/
theorem translatePure_clampAssign_rfl (x0 lo hi : Nat) :
    translatePure (computePlan clampAssignBody) clampAssignBody [.refMut x0, .usize lo, .usize hi] =
      .ok (.usize (if decide (x0 < lo) then lo else if decide (hi < x0) then hi else x0)) :=
  rfl

/-- **First Futamura Projection for `is_aligned_mask`**:
    Evaluating `translatePure (computePlan isAlignedMaskBody) isAlignedMaskBody`
    on universally quantified symbolic inputs `addr mask : Nat` reduces by
    kernel `rfl` directly to `.ok (.bool (decide (Nat.land addr mask = 0)))`. -/
theorem translatePure_isAlignedMask_rfl (addr mask : Nat) :
    translatePure (computePlan isAlignedMaskBody) isAlignedMaskBody [.usize addr, .usize mask] =
      .ok (.bool (decide (Nat.land addr mask = 0))) :=
  rfl

/-- Pure functional specification extracted from `clampAssignBody`. -/
def pureClampAssign (x0 lo hi : Nat) : Nat :=
  if decide (x0 < lo) then lo else if decide (hi < x0) then hi else x0

/-- Pure functional specification extracted from `isAlignedMaskBody`. -/
def pureIsAlignedMask (addr mask : Nat) : Bool :=
  decide (Nat.land addr mask = 0)

/-- Non-trivial property 1 (`clamp_assign` lower bound when `lo ≤ hi`):
    Whenever `lo ≤ hi`, `lo ≤ pureClampAssign x0 lo hi`. -/
theorem pureClampAssign_ge_lo (x0 lo hi : Nat) (h : lo ≤ hi) :
    lo ≤ pureClampAssign x0 lo hi := by
  unfold pureClampAssign
  cases h1 : decide (x0 < lo) with
  | true => exact Nat.le_refl lo
  | false =>
    have hnot1 : ¬ (x0 < lo) := of_decide_eq_false h1
    cases decide (hi < x0) with
    | true => exact h
    | false => exact Nat.le_of_not_lt hnot1

/-- Non-trivial property 2 (`clamp_assign` upper bound when `lo ≤ hi`):
    Whenever `lo ≤ hi`, `pureClampAssign x0 lo hi ≤ hi`. -/
theorem pureClampAssign_le_hi (x0 lo hi : Nat) (h : lo ≤ hi) :
    pureClampAssign x0 lo hi ≤ hi := by
  unfold pureClampAssign
  cases decide (x0 < lo) with
  | true => exact h
  | false =>
    cases h2 : decide (hi < x0) with
    | true => exact Nat.le_refl hi
    | false => exact Nat.le_of_not_lt (of_decide_eq_false h2)

/-- Non-trivial property 3 (`clamp_assign` identity inside `[lo, hi]`):
    Whenever `lo ≤ x0` and `x0 ≤ hi`, `pureClampAssign x0 lo hi = x0`. -/
theorem pureClampAssign_eq_self_of_in_bounds (x0 lo hi : Nat)
    (hlo : lo ≤ x0) (hhi : x0 ≤ hi) :
    pureClampAssign x0 lo hi = x0 := by
  unfold pureClampAssign
  have h1 : decide (x0 < lo) = false := decide_eq_false (Nat.not_lt_of_ge hlo)
  have h2 : decide (hi < x0) = false := decide_eq_false (Nat.not_lt_of_ge hhi)
  rw [h1, h2]
  rfl

/-- Non-trivial property 4 (`clamp_assign` idempotence when `lo ≤ hi`):
    Clamping an already-clamped value to `[lo, hi]` is a no-op. -/
theorem pureClampAssign_idempotent (x0 lo hi : Nat) (h : lo ≤ hi) :
    pureClampAssign (pureClampAssign x0 lo hi) lo hi = pureClampAssign x0 lo hi :=
  pureClampAssign_eq_self_of_in_bounds
    (pureClampAssign x0 lo hi) lo hi
    (pureClampAssign_ge_lo x0 lo hi h)
    (pureClampAssign_le_hi x0 lo hi h)

/-- Non-trivial property 5 (`is_aligned_mask` exact characterization of
    alignment):
    `pureIsAlignedMask addr mask = true` if and only if all masked low bits of
    `addr` are zero (`Nat.land addr mask = 0`). -/
theorem pureIsAlignedMask_eq_true_iff (addr mask : Nat) :
    pureIsAlignedMask addr mask = true ↔ Nat.land addr mask = 0 := by
  unfold pureIsAlignedMask
  exact ⟨of_decide_eq_true, decide_eq_true⟩

/-- Non-trivial property 6 (`is_aligned_mask` exact characterization of
    misalignment):
    `pureIsAlignedMask addr mask = false` if and only if at least one masked bit
    of `addr` is non-zero (`Nat.land addr mask ≠ 0`). -/
theorem pureIsAlignedMask_eq_false_iff (addr mask : Nat) :
    pureIsAlignedMask addr mask = false ↔ Nat.land addr mask ≠ 0 := by
  unfold pureIsAlignedMask
  exact ⟨of_decide_eq_false, decide_eq_false⟩

/-- Non-trivial property 7 (`is_aligned_mask` power-of-two boundary witnesses):
    `4096` is page-aligned (`mask = 4095`), whereas `4098` is not. -/
theorem pureIsAlignedMask_page_examples :
    pureIsAlignedMask 4096 4095 = true ∧ pureIsAlignedMask 4098 4095 = false :=
  ⟨rfl, rfl⟩

/-- Functional postcondition for `clamp_assign` in `FuncLang`. -/
def FuncPostClampAssign (init : MirState) (ret : MirVal) : Prop :=
  ∀ loc x0 lo hi,
    init.locals 1 = some (.refMutLoc loc) →
    init.mem.naVal loc = some (.usize x0) →
    init.locals 2 = some (.usize lo) →
    init.locals 3 = some (.usize hi) →
    ret = .usize (if decide (x0 < lo) then lo else if decide (hi < x0) then hi else x0)

/-- Functional postcondition for `is_aligned_mask` in `FuncLang`. -/
def FuncPostIsAlignedMask (init : MirState) (ret : MirVal) : Prop :=
  ∀ addr mask,
    init.locals 1 = some (.usize addr) →
    init.locals 2 = some (.usize mask) →
    ret = .bool (decide (Nat.land addr mask = 0))

/-- `translate clampAssignBody` satisfies `FuncLang.Spec
    FuncPostClampAssign`. -/
theorem translate_clampAssignBody_spec :
    FuncLang.sem (translate clampAssignBody) ≤ FuncLang.Spec FuncPostClampAssign := by
  refine funcSem_le_spec (fun init => ?_)
  unfold translate evalSym
  have hSupp : allSupportedArgTys clampAssignBody.argTys = true := rfl
  rw [hSupp]
  dsimp
  cases hExt : extractSymArgs clampAssignBody.argTys init with
  | none =>
    refine ⟨(by intro h; cases h), ?_⟩
    intro ret hok
    cases hok
  | some args =>
    unfold extractSymArgs at hExt
    cases hblk : (init.block == 0 && init.stmtIdx == 0) with
    | false => rw [hblk] at hExt; cases hExt
    | true =>
      rw [hblk] at hExt
      dsimp [clampAssignBody, extractSymArgsAux] at hExt
      cases hloc1 : init.locals 1 with
      | none => rw [hloc1] at hExt; cases hExt
      | some mv1 =>
        rw [hloc1] at hExt
        cases mv1 with
        | usize _ | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | ordering _ => cases hExt
        | refMutLoc loc1 =>
          dsimp at hExt
          cases hchk1 : (noAliasBefore init.locals loc1 1 &&
            decide (init.mem.naWriteTs loc1 ≤ init.mem.curView loc1) &&
            decide (init.mem.naReadTs loc1 ≤ init.mem.curView loc1)) with
          | false => rw [hchk1] at hExt; cases hExt
          | true =>
            rw [hchk1] at hExt
            dsimp at hExt
            cases hna1 : init.mem.naVal loc1 with
            | none => rw [hna1] at hExt; cases hExt
            | some naMv1 =>
              rw [hna1] at hExt
              cases naMv1 with
              | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ => cases hExt
              | usize x0' =>
                dsimp at hExt
                cases hloc2 : init.locals 2 with
                | none => rw [hloc2] at hExt; cases hExt
                | some mv2 =>
                  rw [hloc2] at hExt
                  cases mv2 with
                  | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ => cases hExt
                  | usize lo' =>
                    dsimp at hExt
                    cases hloc3 : init.locals 3 with
                    | none => rw [hloc3] at hExt; cases hExt
                    | some mv3 =>
                      rw [hloc3] at hExt
                      cases mv3 with
                      | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ => cases hExt
                      | usize hi' =>
                        dsimp at hExt
                        injection hExt with hargs
                        subst hargs
                        dsimp
                        rw [translatePure_clampAssign_rfl x0' lo' hi']
                        refine ⟨(by intro h; cases h), ?_⟩
                        intro ret hok loc x0 lo hi hl1 hm1 hl2 hl3
                        injection hok with hret
                        rw [hloc1] at hl1; injection hl1 with h1_mv; injection h1_mv with h1; subst h1
                        rw [hna1] at hm1; injection hm1 with hx_mv; injection hx_mv with hx; subst hx
                        rw [hloc2] at hl2; injection hl2 with h2_mv; injection h2_mv with h2; subst h2
                        rw [hloc3] at hl3; injection hl3 with h3_mv; injection h3_mv with h3; subst h3
                        exact hret.symm

/-- `translate isAlignedMaskBody` satisfies `FuncLang.Spec
    FuncPostIsAlignedMask`. -/
theorem translate_isAlignedMaskBody_spec :
    FuncLang.sem (translate isAlignedMaskBody) ≤ FuncLang.Spec FuncPostIsAlignedMask := by
  refine funcSem_le_spec (fun init => ?_)
  unfold translate evalSym
  have hSupp : allSupportedArgTys isAlignedMaskBody.argTys = true := rfl
  rw [hSupp]
  dsimp
  cases hExt : extractSymArgs isAlignedMaskBody.argTys init with
  | none =>
    refine ⟨(by intro h; cases h), ?_⟩
    intro ret hok
    cases hok
  | some args =>
    unfold extractSymArgs at hExt
    cases hblk : (init.block == 0 && init.stmtIdx == 0) with
    | false => rw [hblk] at hExt; cases hExt
    | true =>
      rw [hblk] at hExt
      dsimp [isAlignedMaskBody, extractSymArgsAux] at hExt
      cases hloc1 : init.locals 1 with
      | none => rw [hloc1] at hExt; cases hExt
      | some mv1 =>
        rw [hloc1] at hExt
        cases mv1 with
        | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ => cases hExt
        | usize addr' =>
          dsimp at hExt
          cases hloc2 : init.locals 2 with
          | none => rw [hloc2] at hExt; cases hExt
          | some mv2 =>
            rw [hloc2] at hExt
            cases mv2 with
            | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ => cases hExt
            | usize mask' =>
              dsimp at hExt
              injection hExt with hargs
              subst hargs
              dsimp
              rw [translatePure_isAlignedMask_rfl addr' mask']
              refine ⟨(by intro h; cases h), ?_⟩
              intro ret hok addr mask hl1 hl2
              injection hok with hret
              rw [hloc1] at hl1; injection hl1 with h1_mv; injection h1_mv with h1; subst h1
              rw [hloc2] at hl2; injection hl2 with h2_mv; injection h2_mv with h2; subst h2
              exact hret.symm

/-- `π_func (FuncLang.Spec FuncPostClampAssign)` refines
    `EnsuresClampAssign`. -/
theorem π_func_clampAssign_le_ensures :
    π_func (FuncLang.Spec FuncPostClampAssign) ≤ EnsuresClampAssign := by
  refine Preorder.le_trans (π_func_spec_le FuncPostClampAssign) ?_
  intro q _
  refine ⟨True.intro, ?_⟩
  intro out hpost ret loc x0 lo hi hterm hl1 hm1 hl2 hl3
  exact hpost ret hterm loc x0 lo hi hl1 hm1 hl2 hl3

/-- `π_func (FuncLang.Spec FuncPostIsAlignedMask)` refines
    `EnsuresIsAlignedMask`. -/
theorem π_func_isAlignedMask_le_ensures :
    π_func (FuncLang.Spec FuncPostIsAlignedMask) ≤ EnsuresIsAlignedMask := by
  refine Preorder.le_trans (π_func_spec_le FuncPostIsAlignedMask) ?_
  intro q _
  refine ⟨True.intro, ?_⟩
  intro out hpost ret addr mask hterm hl1 hl2
  exact hpost ret hterm addr mask hl1 hl2

/-- `EnsuresClampAssign` refines baseline `MirLang.WellFormed`. -/
theorem ensuresClampAssign_le_wellFormed :
    EnsuresClampAssign ≤ MirLang.WellFormed :=
  fun _ _ => ⟨True.intro, fun _ _ => True.intro⟩

/-- `EnsuresIsAlignedMask` refines baseline `MirLang.WellFormed`. -/
theorem ensuresIsAlignedMask_le_wellFormed :
    EnsuresIsAlignedMask ≤ MirLang.WellFormed :=
  fun _ _ => ⟨True.intro, fun _ _ => True.intro⟩

/-- **Source MIR Correctness of `clamp_assign`**:
    `MirSem clampAssignBody ≤ EnsuresClampAssign`, transferred across `π_func`
    from `translate_clampAssignBody_spec` via `translate_sound
    clampAssignBody`. -/
theorem clampAssignBody_satisfies_ensures :
    MirSem clampAssignBody ≤ EnsuresClampAssign :=
  Preorder.le_trans
    (Preorder.le_trans
      (translate_sound clampAssignBody)
      (monotone_π_func translate_clampAssignBody_spec))
    π_func_clampAssign_le_ensures

/-- `clampAssignBody` satisfies baseline `MirLang.WellFormed`. -/
theorem clampAssignBody_satisfies_wellFormed :
    MirSem clampAssignBody ≤ MirLang.WellFormed :=
  Preorder.le_trans clampAssignBody_satisfies_ensures ensuresClampAssign_le_wellFormed

/-- **Source MIR Correctness of `is_aligned_mask`**:
    `MirSem isAlignedMaskBody ≤ EnsuresIsAlignedMask`, transferred across
    `π_func` from `translate_isAlignedMaskBody_spec` via
    `translate_sound isAlignedMaskBody`. -/
theorem isAlignedMaskBody_satisfies_ensures :
    MirSem isAlignedMaskBody ≤ EnsuresIsAlignedMask :=
  Preorder.le_trans
    (Preorder.le_trans
      (translate_sound isAlignedMaskBody)
      (monotone_π_func translate_isAlignedMaskBody_spec))
    π_func_isAlignedMask_le_ensures

/-- `isAlignedMaskBody` satisfies baseline `MirLang.WellFormed`. -/
theorem isAlignedMaskBody_satisfies_wellFormed :
    MirSem isAlignedMaskBody ≤ MirLang.WellFormed :=
  Preorder.le_trans isAlignedMaskBody_satisfies_ensures ensuresIsAlignedMask_le_wellFormed

/-- End-to-end `CrateTheorem` witness for `clamp_assign` with
    `EnsuresClampAssign`. -/
theorem prove_clamp_assign_ensures_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := clampAssignBody
        specs := [EnsuresClampAssign]
      }]
      tcb := [.rustcLowering fnName clampAssignBody]
    } := by
  refine ⟨(by intro h; cases h), ⟨⟨True.intro, True.intro⟩, ?_⟩, True.intro⟩
  intro hAssumptions
  have hVerFunc :
      RustcCompiler.Verified clampAssignBody (π_func (FuncLang.Spec FuncPostClampAssign)) :=
    verify_through_passes
      translate_clampAssignBody_spec
      (translate_sound clampAssignBody)
      monotone_π_func
      hAssumptions.1
  have hVerEnsures : RustcCompiler.Verified clampAssignBody EnsuresClampAssign :=
    Compiler.Verified.mono hVerFunc π_func_clampAssign_le_ensures hAssumptions.1.1
  exact Compiler.Verified.with_wellFormedOn
    hVerEnsures
    ensuresClampAssign_le_wellFormed
    hAssumptions.1.1

/-- End-to-end `CrateTheorem` witness for `clamp_assign` with baseline
    `WellFormed`. -/
theorem prove_clamp_assign_wf_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := clampAssignBody
        specs := []
      }]
      tcb := [.rustcLowering fnName clampAssignBody]
    } :=
  verify_single_fn_wf_crate fnName clampAssignBody clampAssignBody_satisfies_wellFormed

/-- End-to-end `CrateTheorem` witness for `is_aligned_mask` with
    `EnsuresIsAlignedMask`. -/
theorem prove_is_aligned_mask_ensures_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := isAlignedMaskBody
        specs := [EnsuresIsAlignedMask]
      }]
      tcb := [.rustcLowering fnName isAlignedMaskBody]
    } := by
  refine ⟨(by intro h; cases h), ⟨⟨True.intro, True.intro⟩, ?_⟩, True.intro⟩
  intro hAssumptions
  have hVerFunc :
      RustcCompiler.Verified isAlignedMaskBody (π_func (FuncLang.Spec FuncPostIsAlignedMask)) :=
    verify_through_passes
      translate_isAlignedMaskBody_spec
      (translate_sound isAlignedMaskBody)
      monotone_π_func
      hAssumptions.1
  have hVerEnsures : RustcCompiler.Verified isAlignedMaskBody EnsuresIsAlignedMask :=
    Compiler.Verified.mono hVerFunc π_func_isAlignedMask_le_ensures hAssumptions.1.1
  exact Compiler.Verified.with_wellFormedOn
    hVerEnsures
    ensuresIsAlignedMask_le_wellFormed
    hAssumptions.1.1

/-- End-to-end `CrateTheorem` witness for `is_aligned_mask` with baseline
    `WellFormed`. -/
theorem prove_is_aligned_mask_wf_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := isAlignedMaskBody
        specs := []
      }]
      tcb := [.rustcLowering fnName isAlignedMaskBody]
    } :=
  verify_single_fn_wf_crate fnName isAlignedMaskBody isAlignedMaskBody_satisfies_wellFormed

/-!
## 11. Verification of `shared_max` and `max_assign_shared`
-/

/-- Exact `Runtime(PostCleanup)` MIR body emitted by `rustc --edition=2024
    --emit=mir`
    for:
    ```rust
    pub fn shared_max(x: &usize, y: &usize) -> usize {
        let r = if *x < *y { y } else { x };
        *r
    }
    ```
    - `_0: usize` (return place), `_1: &usize` (`x`), `_2: &usize` (`y`),
      `_3: &usize` (`r`), `_4: bool`, `_5: usize`, `_6: usize`.
    - `bb0`: `_5 = copy (*_1); _6 = copy (*_2); _4 = Lt(move _5, move _6);
      switchInt(move _4) -> [0: bb2, otherwise: bb1];`
    - `bb1`: `_3 = copy _2; goto -> bb3;`
    - `bb2`: `_3 = copy _1; goto -> bb3;`
    - `bb3`: `_0 = copy (*_3); return;` -/
def sharedMaxBody : MirBody where
  argTys := [.refSharedUsize, .refSharedUsize]
  retTy := .usize
  localCount := 7
  blocks := [
    { stmts := [
        .assign ⟨5⟩ (.deref ⟨1⟩),
        .assign ⟨6⟩ (.deref ⟨2⟩),
        .assign ⟨4⟩ (.binaryOp .lt (.move ⟨5⟩) (.move ⟨6⟩))
      ]
      terminator := .switchInt (.move ⟨4⟩) ⟨2⟩ ⟨1⟩ },
    { stmts := [
        .assign ⟨3⟩ (.use (.copy ⟨2⟩))
      ]
      terminator := .goto ⟨3⟩ },
    { stmts := [
        .assign ⟨3⟩ (.use (.copy ⟨1⟩))
      ]
      terminator := .goto ⟨3⟩ },
    { stmts := [
        .assign ⟨0⟩ (.deref ⟨3⟩)
      ]
      terminator := .return_ }
  ]

/-- Exact `Runtime(PostCleanup)` MIR body emitted by `rustc --edition=2024
    --emit=mir`
    for:
    ```rust
    pub fn max_assign_shared(dst: &mut usize, src: &usize) -> usize {
        if *dst < *src {
            *dst = *src;
        }
        *dst
    }
    ```
    - `_0: usize` (return place), `_1: &mut usize` (`dst`), `_2: &usize`
      (`src`),
      `_3: bool`, `_4: usize`, `_5: usize`, `_6: usize`.
    - `bb0`: `_4 = copy (*_1); _5 = copy (*_2); _3 = Lt(move _4, move _5);
      switchInt(move _3) -> [0: bb2, otherwise: bb1];`
    - `bb1`: `_6 = copy (*_2); (*_1) = move _6; goto -> bb2;`
    - `bb2`: `_0 = copy (*_1); return;` -/
def maxAssignSharedBody : MirBody where
  argTys := [.refMutUsize, .refSharedUsize]
  retTy := .usize
  localCount := 7
  blocks := [
    { stmts := [
        .assign ⟨4⟩ (.deref ⟨1⟩),
        .assign ⟨5⟩ (.deref ⟨2⟩),
        .assign ⟨3⟩ (.binaryOp .lt (.move ⟨4⟩) (.move ⟨5⟩))
      ]
      terminator := .switchInt (.move ⟨3⟩) ⟨2⟩ ⟨1⟩ },
    { stmts := [
        .assign ⟨6⟩ (.deref ⟨2⟩),
        .assignDeref ⟨1⟩ (.move ⟨6⟩)
      ]
      terminator := .goto ⟨2⟩ },
    { stmts := [
        .assign ⟨0⟩ (.deref ⟨1⟩)
      ]
      terminator := .return_ }
  ]

/-- **First Futamura Projection for `shared_max`**:
    Evaluating `translatePure (computePlan sharedMaxBody) sharedMaxBody` on
    universally quantified symbolic inputs `x0 y0 : Nat` reduces by kernel
    `rfl` directly to `.ok (.usize (if decide (x0 < y0) then y0 else x0))`. -/
theorem translatePure_sharedMax_rfl (x0 y0 : Nat) :
    translatePure (computePlan sharedMaxBody) sharedMaxBody [.refShared x0, .refShared y0] =
      .ok (.usize (if decide (x0 < y0) then y0 else x0)) :=
  rfl

/-- **First Futamura Projection for `max_assign_shared`**:
    Evaluating `translatePure (computePlan maxAssignSharedBody)
    maxAssignSharedBody`
    on universally quantified symbolic inputs `x0 y0 : Nat` reduces by kernel
    `rfl` directly to `.ok (.usize (if decide (x0 < y0) then y0 else x0))`. -/
theorem translatePure_maxAssignShared_rfl (x0 y0 : Nat) :
    translatePure (computePlan maxAssignSharedBody) maxAssignSharedBody [.refMut x0, .refShared y0] =
      .ok (.usize (if decide (x0 < y0) then y0 else x0)) :=
  rfl

/-- Pure functional specification extracted from `sharedMaxBody`. -/
def pureSharedMax (x0 y0 : Nat) : Nat :=
  if decide (x0 < y0) then y0 else x0

/-- Pure functional specification extracted from `maxAssignSharedBody`. -/
def pureMaxAssignShared (x0 y0 : Nat) : Nat :=
  if decide (x0 < y0) then y0 else x0

/-- Non-trivial property 1 (`shared_max` and `max_assign_shared` coincide with
    `pureMaxAssign`): -/
theorem pureSharedMax_eq_pureMaxAssign (x0 y0 : Nat) :
    pureSharedMax x0 y0 = pureMaxAssign x0 y0 ∧
    pureMaxAssignShared x0 y0 = pureMaxAssign x0 y0 :=
  ⟨rfl, rfl⟩

/-- Non-trivial property 2 (`shared_max` commutativity): -/
theorem pureSharedMax_comm (x0 y0 : Nat) :
    pureSharedMax x0 y0 = pureSharedMax y0 x0 :=
  pureMaxAssign_comm x0 y0

/-- Non-trivial property 3 (`shared_max` aliased idempotence `shared_max(&a,
    &a)`): -/
theorem pureSharedMax_idempotent (x0 : Nat) :
    pureSharedMax x0 x0 = x0 :=
  pureMaxAssign_idempotent x0

/-- Functional postcondition for `shared_max` in `FuncLang`. -/
def FuncPostSharedMax (init : MirState) (ret : MirVal) : Prop :=
  ∀ locX locY x0 y0,
    init.locals 1 = some (.refSharedLoc locX) →
    init.mem.naVal locX = some (.usize x0) →
    init.locals 2 = some (.refSharedLoc locY) →
    init.mem.naVal locY = some (.usize y0) →
    ret = .usize (if decide (x0 < y0) then y0 else x0)

/-- Functional postcondition for `max_assign_shared` in `FuncLang`. -/
def FuncPostMaxAssignShared (init : MirState) (ret : MirVal) : Prop :=
  ∀ locDst locSrc x0 y0,
    init.locals 1 = some (.refMutLoc locDst) →
    init.mem.naVal locDst = some (.usize x0) →
    init.locals 2 = some (.refSharedLoc locSrc) →
    init.mem.naVal locSrc = some (.usize y0) →
    ret = .usize (if decide (x0 < y0) then y0 else x0)

/-- `translate sharedMaxBody` satisfies `FuncLang.Spec FuncPostSharedMax`. -/
theorem translate_sharedMaxBody_spec :
    FuncLang.sem (translate sharedMaxBody) ≤ FuncLang.Spec FuncPostSharedMax := by
  refine funcSem_le_spec (fun init => ?_)
  unfold translate evalSym
  have hSupp : allSupportedArgTys sharedMaxBody.argTys = true := rfl
  rw [hSupp]
  dsimp
  cases hExt : extractSymArgs sharedMaxBody.argTys init with
  | none =>
    refine ⟨(by intro h; cases h), ?_⟩
    intro ret hok
    cases hok
  | some args =>
    unfold extractSymArgs at hExt
    cases hblk : (init.block == 0 && init.stmtIdx == 0) with
    | false => rw [hblk] at hExt; cases hExt
    | true =>
      rw [hblk] at hExt
      dsimp [sharedMaxBody, extractSymArgsAux] at hExt
      cases hloc1 : init.locals 1 with
      | none => rw [hloc1] at hExt; cases hExt
      | some mv1 =>
        rw [hloc1] at hExt
        cases mv1 with
        | usize _ | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | ordering _ => cases hExt
        | refSharedLoc loc1 =>
          dsimp at hExt
          cases hchk1 : (noMutAliasBefore init.locals loc1 1 &&
            decide (init.mem.naWriteTs loc1 ≤ init.mem.curView loc1)) with
          | false => rw [hchk1] at hExt; cases hExt
          | true =>
            rw [hchk1] at hExt
            dsimp at hExt
            cases hna1 : init.mem.naVal loc1 with
            | none => rw [hna1] at hExt; cases hExt
            | some naMv1 =>
              rw [hna1] at hExt
              cases naMv1 with
              | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ => cases hExt
              | usize x0' =>
                dsimp at hExt
                cases hloc2 : init.locals 2 with
                | none => rw [hloc2] at hExt; cases hExt
                | some mv2 =>
                  rw [hloc2] at hExt
                  cases mv2 with
                  | usize _ | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | ordering _ => cases hExt
                  | refSharedLoc loc2 =>
                    dsimp at hExt
                    cases hchk2 : (noMutAliasBefore init.locals loc2 2 &&
                      decide (init.mem.naWriteTs loc2 ≤ init.mem.curView loc2)) with
                    | false => rw [hchk2] at hExt; cases hExt
                    | true =>
                      rw [hchk2] at hExt
                      dsimp at hExt
                      cases hna2 : init.mem.naVal loc2 with
                      | none => rw [hna2] at hExt; cases hExt
                      | some naMv2 =>
                        rw [hna2] at hExt
                        cases naMv2 with
                        | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ => cases hExt
                        | usize y0' =>
                          dsimp at hExt
                          injection hExt with hargs
                          subst hargs
                          dsimp
                          rw [translatePure_sharedMax_rfl x0' y0']
                          refine ⟨(by intro h; cases h), ?_⟩
                          intro ret hok locX locY x0 y0 hl1 hm1 hl2 hm2
                          injection hok with hret
                          rw [hloc1] at hl1; injection hl1 with h1_mv; injection h1_mv with h1; subst h1
                          rw [hna1] at hm1; injection hm1 with hx_mv; injection hx_mv with hx; subst hx
                          rw [hloc2] at hl2; injection hl2 with h2_mv; injection h2_mv with h2; subst h2
                          rw [hna2] at hm2; injection hm2 with hy_mv; injection hy_mv with hy; subst hy
                          exact hret.symm

/-- `translate maxAssignSharedBody` satisfies `FuncLang.Spec
    FuncPostMaxAssignShared`. -/
theorem translate_maxAssignSharedBody_spec :
    FuncLang.sem (translate maxAssignSharedBody) ≤ FuncLang.Spec FuncPostMaxAssignShared := by
  refine funcSem_le_spec (fun init => ?_)
  unfold translate evalSym
  have hSupp : allSupportedArgTys maxAssignSharedBody.argTys = true := rfl
  rw [hSupp]
  dsimp
  cases hExt : extractSymArgs maxAssignSharedBody.argTys init with
  | none =>
    refine ⟨(by intro h; cases h), ?_⟩
    intro ret hok
    cases hok
  | some args =>
    unfold extractSymArgs at hExt
    cases hblk : (init.block == 0 && init.stmtIdx == 0) with
    | false => rw [hblk] at hExt; cases hExt
    | true =>
      rw [hblk] at hExt
      dsimp [maxAssignSharedBody, extractSymArgsAux] at hExt
      cases hloc1 : init.locals 1 with
      | none => rw [hloc1] at hExt; cases hExt
      | some mv1 =>
        rw [hloc1] at hExt
        cases mv1 with
        | usize _ | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | ordering _ => cases hExt
        | refMutLoc loc1 =>
          dsimp at hExt
          cases hchk1 : (noAliasBefore init.locals loc1 1 &&
            decide (init.mem.naWriteTs loc1 ≤ init.mem.curView loc1) &&
            decide (init.mem.naReadTs loc1 ≤ init.mem.curView loc1)) with
          | false => rw [hchk1] at hExt; cases hExt
          | true =>
            rw [hchk1] at hExt
            dsimp at hExt
            cases hna1 : init.mem.naVal loc1 with
            | none => rw [hna1] at hExt; cases hExt
            | some naMv1 =>
              rw [hna1] at hExt
              cases naMv1 with
              | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ => cases hExt
              | usize x0' =>
                dsimp at hExt
                cases hloc2 : init.locals 2 with
                | none => rw [hloc2] at hExt; cases hExt
                | some mv2 =>
                  rw [hloc2] at hExt
                  cases mv2 with
                  | usize _ | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | ordering _ => cases hExt
                  | refSharedLoc loc2 =>
                    dsimp at hExt
                    cases hchk2 : (noMutAliasBefore init.locals loc2 2 &&
                      decide (init.mem.naWriteTs loc2 ≤ init.mem.curView loc2)) with
                    | false => rw [hchk2] at hExt; cases hExt
                    | true =>
                      rw [hchk2] at hExt
                      dsimp at hExt
                      cases hna2 : init.mem.naVal loc2 with
                      | none => rw [hna2] at hExt; cases hExt
                      | some naMv2 =>
                        rw [hna2] at hExt
                        cases naMv2 with
                        | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ => cases hExt
                        | usize y0' =>
                          dsimp at hExt
                          injection hExt with hargs
                          subst hargs
                          dsimp
                          rw [translatePure_maxAssignShared_rfl x0' y0']
                          refine ⟨(by intro h; cases h), ?_⟩
                          intro ret hok locDst locSrc x0 y0 hl1 hm1 hl2 hm2
                          injection hok with hret
                          rw [hloc1] at hl1; injection hl1 with h1_mv; injection h1_mv with h1; subst h1
                          rw [hna1] at hm1; injection hm1 with hx_mv; injection hx_mv with hx; subst hx
                          rw [hloc2] at hl2; injection hl2 with h2_mv; injection h2_mv with h2; subst h2
                          rw [hna2] at hm2; injection hm2 with hy_mv; injection hy_mv with hy; subst hy
                          exact hret.symm

/-- `π_func (FuncLang.Spec FuncPostSharedMax)` refines `EnsuresSharedMax`. -/
theorem π_func_sharedMax_le_ensures :
    π_func (FuncLang.Spec FuncPostSharedMax) ≤ EnsuresSharedMax := by
  refine Preorder.le_trans (π_func_spec_le FuncPostSharedMax) ?_
  intro q _
  refine ⟨True.intro, ?_⟩
  intro out hpost ret locX locY x0 y0 hterm hl1 hm1 hl2 hm2
  exact hpost ret hterm locX locY x0 y0 hl1 hm1 hl2 hm2

/-- `π_func (FuncLang.Spec FuncPostMaxAssignShared)` refines
    `EnsuresMaxAssignShared`. -/
theorem π_func_maxAssignShared_le_ensures :
    π_func (FuncLang.Spec FuncPostMaxAssignShared) ≤ EnsuresMaxAssignShared := by
  refine Preorder.le_trans (π_func_spec_le FuncPostMaxAssignShared) ?_
  intro q _
  refine ⟨True.intro, ?_⟩
  intro out hpost ret locDst locSrc x0 y0 hterm hl1 hm1 hl2 hm2
  exact hpost ret hterm locDst locSrc x0 y0 hl1 hm1 hl2 hm2

/-- `EnsuresSharedMax` refines baseline `MirLang.WellFormed`. -/
theorem ensuresSharedMax_le_wellFormed :
    EnsuresSharedMax ≤ MirLang.WellFormed :=
  fun _ _ => ⟨True.intro, fun _ _ => True.intro⟩

/-- `EnsuresMaxAssignShared` refines baseline `MirLang.WellFormed`. -/
theorem ensuresMaxAssignShared_le_wellFormed :
    EnsuresMaxAssignShared ≤ MirLang.WellFormed :=
  fun _ _ => ⟨True.intro, fun _ _ => True.intro⟩

/-- **Source MIR Correctness of `shared_max`**:
    `MirSem sharedMaxBody ≤ EnsuresSharedMax`, transferred across `π_func` from
    `translate_sharedMaxBody_spec` via `translate_sound sharedMaxBody`. -/
theorem sharedMaxBody_satisfies_ensures :
    MirSem sharedMaxBody ≤ EnsuresSharedMax :=
  Preorder.le_trans
    (Preorder.le_trans
      (translate_sound sharedMaxBody)
      (monotone_π_func translate_sharedMaxBody_spec))
    π_func_sharedMax_le_ensures

/-- `sharedMaxBody` satisfies baseline `MirLang.WellFormed`. -/
theorem sharedMaxBody_satisfies_wellFormed :
    MirSem sharedMaxBody ≤ MirLang.WellFormed :=
  Preorder.le_trans sharedMaxBody_satisfies_ensures ensuresSharedMax_le_wellFormed

/-- **Source MIR Correctness of `max_assign_shared`**:
    `MirSem maxAssignSharedBody ≤ EnsuresMaxAssignShared`, transferred across
    `π_func` from `translate_maxAssignSharedBody_spec` via
    `translate_sound maxAssignSharedBody`. -/
theorem maxAssignSharedBody_satisfies_ensures :
    MirSem maxAssignSharedBody ≤ EnsuresMaxAssignShared :=
  Preorder.le_trans
    (Preorder.le_trans
      (translate_sound maxAssignSharedBody)
      (monotone_π_func translate_maxAssignSharedBody_spec))
    π_func_maxAssignShared_le_ensures

/-- `maxAssignSharedBody` satisfies baseline `MirLang.WellFormed`. -/
theorem maxAssignSharedBody_satisfies_wellFormed :
    MirSem maxAssignSharedBody ≤ MirLang.WellFormed :=
  Preorder.le_trans maxAssignSharedBody_satisfies_ensures ensuresMaxAssignShared_le_wellFormed

/-- End-to-end `CrateTheorem` witness for `shared_max` with
    `EnsuresSharedMax`. -/
theorem prove_shared_max_ensures_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := sharedMaxBody
        specs := [EnsuresSharedMax]
      }]
      tcb := [.rustcLowering fnName sharedMaxBody]
    } := by
  refine ⟨(by intro h; cases h), ⟨⟨True.intro, True.intro⟩, ?_⟩, True.intro⟩
  intro hAssumptions
  have hVerFunc :
      RustcCompiler.Verified sharedMaxBody (π_func (FuncLang.Spec FuncPostSharedMax)) :=
    verify_through_passes
      translate_sharedMaxBody_spec
      (translate_sound sharedMaxBody)
      monotone_π_func
      hAssumptions.1
  have hVerEnsures : RustcCompiler.Verified sharedMaxBody EnsuresSharedMax :=
    Compiler.Verified.mono hVerFunc π_func_sharedMax_le_ensures hAssumptions.1.1
  exact Compiler.Verified.with_wellFormedOn
    hVerEnsures
    ensuresSharedMax_le_wellFormed
    hAssumptions.1.1

/-- End-to-end `CrateTheorem` witness for `shared_max` with baseline
    `WellFormed`. -/
theorem prove_shared_max_wf_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := sharedMaxBody
        specs := []
      }]
      tcb := [.rustcLowering fnName sharedMaxBody]
    } :=
  verify_single_fn_wf_crate fnName sharedMaxBody sharedMaxBody_satisfies_wellFormed

/-- End-to-end `CrateTheorem` witness for `max_assign_shared` with
    `EnsuresMaxAssignShared`. -/
theorem prove_max_assign_shared_ensures_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := maxAssignSharedBody
        specs := [EnsuresMaxAssignShared]
      }]
      tcb := [.rustcLowering fnName maxAssignSharedBody]
    } := by
  refine ⟨(by intro h; cases h), ⟨⟨True.intro, True.intro⟩, ?_⟩, True.intro⟩
  intro hAssumptions
  have hVerFunc :
      RustcCompiler.Verified maxAssignSharedBody (π_func (FuncLang.Spec FuncPostMaxAssignShared)) :=
    verify_through_passes
      translate_maxAssignSharedBody_spec
      (translate_sound maxAssignSharedBody)
      monotone_π_func
      hAssumptions.1
  have hVerEnsures : RustcCompiler.Verified maxAssignSharedBody EnsuresMaxAssignShared :=
    Compiler.Verified.mono hVerFunc π_func_maxAssignShared_le_ensures hAssumptions.1.1
  exact Compiler.Verified.with_wellFormedOn
    hVerEnsures
    ensuresMaxAssignShared_le_wellFormed
    hAssumptions.1.1

/-- End-to-end `CrateTheorem` witness for `max_assign_shared` with baseline
    `WellFormed`. -/
theorem prove_max_assign_shared_wf_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := maxAssignSharedBody
        specs := []
      }]
      tcb := [.rustcLowering fnName maxAssignSharedBody]
    } :=
  verify_single_fn_wf_crate fnName maxAssignSharedBody maxAssignSharedBody_satisfies_wellFormed

/-- **Aliasing Adequacy Canary Pair (`shared_max(&a, &a)` vs
    `max_assign_shared(&mut a, &a)`)**:
    1. When two `&usize` parameters alias the same memory location `0`
       (`sampleSharedAliasedInit`), `translate sharedMaxBody` accepts the state
       and evaluates to `.ok (.usize 42)`.
    2. When a `&mut usize` parameter and a `&usize` parameter alias the same
       memory location `0` (`sampleMutSharedAliasedInit`),
       `extractSymArgs maxAssignSharedBody.argTys` rejects the ill-typed state
       with `none`, and `translate maxAssignSharedBody` vacuously returns `.ok
       .unit`
       outside the `argsValid` domain. -/
def sampleSharedAliasedInit : MirState where
  locals := fun
    | 1 => some (.refSharedLoc 0)
    | 2 => some (.refSharedLoc 0)
    | _ => none
  mem := {
    curView := fun _ => 0
    naVal := fun
      | 0 => some (.usize 42)
      | _ => none
    naWriteTs := fun _ => 0
    naReadTs := fun _ => 0
    atomicMsgs := []
  }
  block := 0
  stmtIdx := 0

def sampleMutSharedAliasedInit : MirState where
  locals := fun
    | 1 => some (.refMutLoc 0)
    | 2 => some (.refSharedLoc 0)
    | _ => none
  mem := {
    curView := fun _ => 0
    naVal := fun
      | 0 => some (.usize 42)
      | _ => none
    naWriteTs := fun _ => 0
    naReadTs := fun _ => 0
    atomicMsgs := []
  }
  block := 0
  stmtIdx := 0

theorem sharedMax_aliased_accepted :
    translate sharedMaxBody sampleSharedAliasedInit = .ok (.usize 42) :=
  rfl

theorem maxAssignShared_aliased_rejected :
    extractSymArgs maxAssignSharedBody.argTys sampleMutSharedAliasedInit = none :=
  rfl

/-!
## 12. Verification of `sort_pair` and `two_phase_reborrow`
-/

/-- Exact `Runtime(PostCleanup)` MIR body emitted by `rustc --edition=2024
    --emit=mir`
    for:
    ```rust
    pub fn sort_pair(x: &mut usize, y: &mut usize) -> usize {
        if *x > *y {
            let tmp = *x;
            *x = *y;
            *y = tmp;
        }
        *x
    }
    ```
    - `_0: usize` (return place), `_1: &mut usize` (`x`), `_2: &mut usize`
      (`y`),
      `_3: bool`, `_4: usize`, `_5: usize`, `_6: usize` (`tmp`), `_7: usize`.
    - `bb0`: `_4 = copy (*_1); _5 = copy (*_2); _3 = Gt(move _4, move _5);
      switchInt(move _3) -> [0: bb2, otherwise: bb1];`
    - `bb1`: `_6 = copy (*_1); _7 = copy (*_2); (*_1) = move _7; (*_2) = copy
      _6; goto -> bb2;`
    - `bb2`: `_0 = copy (*_1); return;` -/
def sortPairBody : MirBody where
  argTys := [.refMutUsize, .refMutUsize]
  retTy := .usize
  localCount := 8
  blocks := [
    { stmts := [
        .assign ⟨4⟩ (.deref ⟨1⟩),
        .assign ⟨5⟩ (.deref ⟨2⟩),
        .assign ⟨3⟩ (.binaryOp .gt (.move ⟨4⟩) (.move ⟨5⟩))
      ]
      terminator := .switchInt (.move ⟨3⟩) ⟨2⟩ ⟨1⟩ },
    { stmts := [
        .assign ⟨6⟩ (.deref ⟨1⟩),
        .assign ⟨7⟩ (.deref ⟨2⟩),
        .assignDeref ⟨1⟩ (.move ⟨7⟩),
        .assignDeref ⟨2⟩ (.copy ⟨6⟩)
      ]
      terminator := .goto ⟨2⟩ },
    { stmts := [
        .assign ⟨0⟩ (.deref ⟨1⟩)
      ]
      terminator := .return_ }
  ]

/-- Exact `Runtime(PostCleanup)` MIR body emitted by `rustc --edition=2024
    --emit=mir`
    for:
    ```rust
    pub fn two_phase_reborrow(x: &mut usize, y: &mut usize, a: usize, b: usize) -> usize {
        let r1 = if *x <= *y { &mut *x } else { &mut *y };
        *r1 = a;
        let r2 = if *x <= *y { &mut *y } else { &mut *x };
        *r2 = b;
        *x
    }
    ```
    - `_0: usize` (return place), `_1: &mut usize` (`x`), `_2: &mut usize`
      (`y`),
      `_3: usize` (`a`), `_4: usize` (`b`), `_5: &mut usize` (`r1`), `_6: bool`,
      `_7: usize`, `_8: usize`, `_9: &mut usize` (`r2`), `_10: bool`,
      `_11: usize`, `_12: usize`.
    - `bb0`: `_7 = copy (*_1); _8 = copy (*_2); _6 = Le(move _7, move _8);
      switchInt(move _6) -> [0: bb2, otherwise: bb1];`
    - `bb1`: `_5 = copy _1; goto -> bb3;`
    - `bb2`: `_5 = copy _2; goto -> bb3;`
    - `bb3`: `(*_5) = copy _3; _11 = copy (*_1); _12 = copy (*_2); _10 = Le(move
      _11, move _12); switchInt(move _10) -> [0: bb5, otherwise: bb4];`
    - `bb4`: `_9 = copy _2; goto -> bb6;`
    - `bb5`: `_9 = copy _1; goto -> bb6;`
    - `bb6`: `(*_9) = copy _4; _0 = copy (*_1); return;` -/
def twoPhaseReborrowBody : MirBody where
  argTys := [.refMutUsize, .refMutUsize, .usize, .usize]
  retTy := .usize
  localCount := 13
  blocks := [
    { stmts := [
        .assign ⟨7⟩ (.deref ⟨1⟩),
        .assign ⟨8⟩ (.deref ⟨2⟩),
        .assign ⟨6⟩ (.binaryOp .le (.move ⟨7⟩) (.move ⟨8⟩))
      ]
      terminator := .switchInt (.move ⟨6⟩) ⟨2⟩ ⟨1⟩ },
    { stmts := [
        .assign ⟨5⟩ (.use (.copy ⟨1⟩))
      ]
      terminator := .goto ⟨3⟩ },
    { stmts := [
        .assign ⟨5⟩ (.use (.copy ⟨2⟩))
      ]
      terminator := .goto ⟨3⟩ },
    { stmts := [
        .assignDeref ⟨5⟩ (.copy ⟨3⟩),
        .assign ⟨11⟩ (.deref ⟨1⟩),
        .assign ⟨12⟩ (.deref ⟨2⟩),
        .assign ⟨10⟩ (.binaryOp .le (.move ⟨11⟩) (.move ⟨12⟩))
      ]
      terminator := .switchInt (.move ⟨10⟩) ⟨5⟩ ⟨4⟩ },
    { stmts := [
        .assign ⟨9⟩ (.use (.copy ⟨2⟩))
      ]
      terminator := .goto ⟨6⟩ },
    { stmts := [
        .assign ⟨9⟩ (.use (.copy ⟨1⟩))
      ]
      terminator := .goto ⟨6⟩ },
    { stmts := [
        .assignDeref ⟨9⟩ (.copy ⟨4⟩),
        .assign ⟨0⟩ (.deref ⟨1⟩)
      ]
      terminator := .return_ }
  ]

/-- `computePlan twoPhaseReborrowBody` automatically detects both sequential
    diamond borrow joins (`_5` at `bb3` and `_9` at `bb6`) and schedules
    `.endLoan 5` before `_11 = copy (*_1)` in `bb3` and `.endLoan 9` before
    `_0 = copy (*_1)` in `bb6`. -/
theorem computePlan_twoPhaseReborrowBody_eq :
    computePlan twoPhaseReborrowBody =
      .step (.step (.step
        (.joinBorrow 5 2 1 3 5
          (.step (.endLoan 5
            (.step (.step (.step
              (.joinBorrow 9 1 2 6 9
                (.step (.endLoan 9 (.step .ret)))))))))))) :=
  rfl

/-- **First Futamura Projection for `sort_pair`**:
    Evaluating `translatePure (computePlan sortPairBody) sortPairBody` on
    universally quantified symbolic inputs `x0 y0 : Nat` reduces by kernel
    `rfl` directly to `.ok (.usize (if decide (y0 < x0) then y0 else x0))`. -/
theorem translatePure_sortPair_rfl (x0 y0 : Nat) :
    translatePure (computePlan sortPairBody) sortPairBody [.refMut x0, .refMut y0] =
      .ok (.usize (if decide (y0 < x0) then y0 else x0)) :=
  rfl

/-- **First Futamura Projection for `two_phase_reborrow`**:
    Evaluating `translatePure (computePlan twoPhaseReborrowBody)
    twoPhaseReborrowBody`
    on universally quantified symbolic inputs `x0 y0 a b : Nat` reduces by
    kernel `rfl` directly to the nested two-stage expression. -/
theorem translatePure_twoPhaseReborrow_rfl (x0 y0 a b : Nat) :
    translatePure (computePlan twoPhaseReborrowBody) twoPhaseReborrowBody
      [.refMut x0, .refMut y0, .usize a, .usize b] =
      .ok (.usize
        (if decide ((if decide (x0 ≤ y0) then a else x0) ≤ (if decide (x0 ≤ y0) then y0 else a))
         then (if decide (x0 ≤ y0) then a else x0)
         else b)) :=
  rfl

/-- Pure functional return specification extracted from `sortPairBody`. -/
def pureSortPair (x0 y0 : Nat) : Nat :=
  if decide (y0 < x0) then y0 else x0

/-- Pure functional post-state pair `(x', y')` for `sort_pair`. -/
def pureSortPairPost (x0 y0 : Nat) : Nat × Nat :=
  (if decide (y0 < x0) then y0 else x0,
   if decide (y0 < x0) then x0 else y0)

/-- Pure functional return specification extracted from
    `twoPhaseReborrowBody`. -/
def pureTwoPhaseReborrow (x0 y0 a b : Nat) : Nat :=
  if decide ((if decide (x0 ≤ y0) then a else x0) ≤ (if decide (x0 ≤ y0) then y0 else a))
  then (if decide (x0 ≤ y0) then a else x0)
  else b

/-- Non-trivial property 1 (`sort_pair` left lower bound): -/
theorem pureSortPair_le_left (x0 y0 : Nat) :
    pureSortPair x0 y0 ≤ x0 := by
  unfold pureSortPair
  cases h : decide (y0 < x0) with
  | true => exact Nat.le_of_lt (of_decide_eq_true h)
  | false => exact Nat.le_refl x0

/-- Non-trivial property 2 (`sort_pair` right lower bound): -/
theorem pureSortPair_le_right (x0 y0 : Nat) :
    pureSortPair x0 y0 ≤ y0 := by
  unfold pureSortPair
  cases h : decide (y0 < x0) with
  | true => exact Nat.le_refl y0
  | false => exact Nat.le_of_not_lt (of_decide_eq_false h)

/-- Non-trivial property 3 (`sort_pair` post-state ordering `x' ≤ y'`): -/
theorem pureSortPairPost_ordered (x0 y0 : Nat) :
    (pureSortPairPost x0 y0).1 ≤ (pureSortPairPost x0 y0).2 := by
  unfold pureSortPairPost
  cases h : decide (y0 < x0) with
  | true => exact Nat.le_of_lt (of_decide_eq_true h)
  | false => exact Nat.le_of_not_lt (of_decide_eq_false h)

/-- Non-trivial property 4 (`sort_pair` permutation conservation): -/
theorem pureSortPairPost_perm (x0 y0 : Nat) :
    pureSortPairPost x0 y0 = (x0, y0) ∨ pureSortPairPost x0 y0 = (y0, x0) := by
  unfold pureSortPairPost
  cases decide (y0 < x0) with
  | true => exact Or.inr rfl
  | false => exact Or.inl rfl

/-- Non-trivial property 5 (`two_phase_reborrow` disjoint-target regime when `x0
    ≤ y0` and `a ≤ y0`):
    Phase 1 mutates `*x := a` via `r1`, `.endLoan 5` writes `a` back to `x`,
    and Phase 2 observes `a ≤ y0` so `r2` borrows `y` (`*y := b`), preserving
    `*x = a`. -/
theorem pureTwoPhaseReborrow_when_a_le_y0 (x0 y0 a b : Nat)
    (hxy : x0 ≤ y0) (hay : a ≤ y0) :
    pureTwoPhaseReborrow x0 y0 a b = a := by
  unfold pureTwoPhaseReborrow
  have h1 : decide (x0 ≤ y0) = true := decide_eq_true hxy
  have h2 : decide (a ≤ y0) = true := decide_eq_true hay
  rw [h1]
  change (if decide (a ≤ y0) = true then a else b) = a
  rw [h2]
  rfl

/-- Non-trivial property 6 (`two_phase_reborrow` same-target re-mutation regime
    when `x0 ≤ y0` and `y0 < a`):
    Phase 1 mutates `*x := a` via `r1`, `.endLoan 5` writes `a` back to `x`,
    and Phase 2 observes `y0 < a` (`¬(a ≤ y0)`), so `r2` reborrows `x` a
    second time and overwrites `*x := b`! -/
theorem pureTwoPhaseReborrow_when_y0_lt_a (x0 y0 a b : Nat)
    (hxy : x0 ≤ y0) (hya : y0 < a) :
    pureTwoPhaseReborrow x0 y0 a b = b := by
  unfold pureTwoPhaseReborrow
  have h1 : decide (x0 ≤ y0) = true := decide_eq_true hxy
  have h2 : decide (a ≤ y0) = false := decide_eq_false (Nat.not_le_of_gt hya)
  rw [h1]
  change (if decide (a ≤ y0) = true then a else b) = b
  rw [h2]
  rfl

/-- Functional postcondition for `sort_pair` in `FuncLang`. -/
def FuncPostSortPair (init : MirState) (ret : MirVal) : Prop :=
  ∀ locX locY x0 y0,
    init.locals 1 = some (.refMutLoc locX) →
    init.mem.naVal locX = some (.usize x0) →
    init.locals 2 = some (.refMutLoc locY) →
    init.mem.naVal locY = some (.usize y0) →
    ret = .usize (if decide (y0 < x0) then y0 else x0)

/-- Functional postcondition for `two_phase_reborrow` in `FuncLang`. -/
def FuncPostTwoPhaseReborrow (init : MirState) (ret : MirVal) : Prop :=
  ∀ locX locY x0 y0 a b,
    init.locals 1 = some (.refMutLoc locX) →
    init.mem.naVal locX = some (.usize x0) →
    init.locals 2 = some (.refMutLoc locY) →
    init.mem.naVal locY = some (.usize y0) →
    init.locals 3 = some (.usize a) →
    init.locals 4 = some (.usize b) →
    ret = .usize
      (if decide ((if decide (x0 ≤ y0) then a else x0) ≤ (if decide (x0 ≤ y0) then y0 else a))
       then (if decide (x0 ≤ y0) then a else x0)
       else b)

/-- `translate sortPairBody` satisfies `FuncLang.Spec FuncPostSortPair`. -/
theorem translate_sortPairBody_spec :
    FuncLang.sem (translate sortPairBody) ≤ FuncLang.Spec FuncPostSortPair := by
  refine funcSem_le_spec (fun init => ?_)
  unfold translate evalSym
  have hSupp : allSupportedArgTys sortPairBody.argTys = true := rfl
  rw [hSupp]
  dsimp
  cases hExt : extractSymArgs sortPairBody.argTys init with
  | none =>
    refine ⟨(by intro h; cases h), ?_⟩
    intro ret hok
    cases hok
  | some args =>
    unfold extractSymArgs at hExt
    cases hblk : (init.block == 0 && init.stmtIdx == 0) with
    | false => rw [hblk] at hExt; cases hExt
    | true =>
      rw [hblk] at hExt
      dsimp [sortPairBody, extractSymArgsAux] at hExt
      cases hloc1 : init.locals 1 with
      | none => rw [hloc1] at hExt; cases hExt
      | some mv1 =>
        rw [hloc1] at hExt
        cases mv1 with
        | usize _ | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | ordering _ => cases hExt
        | refMutLoc loc1 =>
          dsimp at hExt
          cases hchk1 : (noAliasBefore init.locals loc1 1 &&
            decide (init.mem.naWriteTs loc1 ≤ init.mem.curView loc1) &&
            decide (init.mem.naReadTs loc1 ≤ init.mem.curView loc1)) with
          | false => rw [hchk1] at hExt; cases hExt
          | true =>
            rw [hchk1] at hExt
            dsimp at hExt
            cases hna1 : init.mem.naVal loc1 with
            | none => rw [hna1] at hExt; cases hExt
            | some naMv1 =>
              rw [hna1] at hExt
              cases naMv1 with
              | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ => cases hExt
              | usize x0' =>
                dsimp at hExt
                cases hloc2 : init.locals 2 with
                | none => rw [hloc2] at hExt; cases hExt
                | some mv2 =>
                  rw [hloc2] at hExt
                  cases mv2 with
                  | usize _ | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | ordering _ => cases hExt
                  | refMutLoc loc2 =>
                    dsimp at hExt
                    cases hchk2 : (noAliasBefore init.locals loc2 2 &&
                      decide (init.mem.naWriteTs loc2 ≤ init.mem.curView loc2) &&
                      decide (init.mem.naReadTs loc2 ≤ init.mem.curView loc2)) with
                    | false => rw [hchk2] at hExt; cases hExt
                    | true =>
                      rw [hchk2] at hExt
                      dsimp at hExt
                      cases hna2 : init.mem.naVal loc2 with
                      | none => rw [hna2] at hExt; cases hExt
                      | some naMv2 =>
                        rw [hna2] at hExt
                        cases naMv2 with
                        | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ => cases hExt
                        | usize y0' =>
                          dsimp at hExt
                          injection hExt with hargs
                          subst hargs
                          dsimp
                          rw [translatePure_sortPair_rfl x0' y0']
                          refine ⟨(by intro h; cases h), ?_⟩
                          intro ret hok locX locY x0 y0 hl1 hm1 hl2 hm2
                          injection hok with hret
                          rw [hloc1] at hl1; injection hl1 with h1_mv; injection h1_mv with h1; subst h1
                          rw [hna1] at hm1; injection hm1 with hx_mv; injection hx_mv with hx; subst hx
                          rw [hloc2] at hl2; injection hl2 with h2_mv; injection h2_mv with h2; subst h2
                          rw [hna2] at hm2; injection hm2 with hy_mv; injection hy_mv with hy; subst hy
                          exact hret.symm

/-- `translate twoPhaseReborrowBody` satisfies `FuncLang.Spec
    FuncPostTwoPhaseReborrow`. -/
theorem translate_twoPhaseReborrowBody_spec :
    FuncLang.sem (translate twoPhaseReborrowBody) ≤ FuncLang.Spec FuncPostTwoPhaseReborrow := by
  refine funcSem_le_spec (fun init => ?_)
  unfold translate evalSym
  have hSupp : allSupportedArgTys twoPhaseReborrowBody.argTys = true := rfl
  rw [hSupp]
  dsimp
  cases hExt : extractSymArgs twoPhaseReborrowBody.argTys init with
  | none =>
    refine ⟨(by intro h; cases h), ?_⟩
    intro ret hok
    cases hok
  | some args =>
    unfold extractSymArgs at hExt
    cases hblk : (init.block == 0 && init.stmtIdx == 0) with
    | false => rw [hblk] at hExt; cases hExt
    | true =>
      rw [hblk] at hExt
      dsimp [twoPhaseReborrowBody, extractSymArgsAux] at hExt
      cases hloc1 : init.locals 1 with
      | none => rw [hloc1] at hExt; cases hExt
      | some mv1 =>
        rw [hloc1] at hExt
        cases mv1 with
        | usize _ | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | ordering _ => cases hExt
        | refMutLoc loc1 =>
          dsimp at hExt
          cases hchk1 : (noAliasBefore init.locals loc1 1 &&
            decide (init.mem.naWriteTs loc1 ≤ init.mem.curView loc1) &&
            decide (init.mem.naReadTs loc1 ≤ init.mem.curView loc1)) with
          | false => rw [hchk1] at hExt; cases hExt
          | true =>
            rw [hchk1] at hExt
            dsimp at hExt
            cases hna1 : init.mem.naVal loc1 with
            | none => rw [hna1] at hExt; cases hExt
            | some naMv1 =>
              rw [hna1] at hExt
              cases naMv1 with
              | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ => cases hExt
              | usize x0' =>
                dsimp at hExt
                cases hloc2 : init.locals 2 with
                | none => rw [hloc2] at hExt; cases hExt
                | some mv2 =>
                  rw [hloc2] at hExt
                  cases mv2 with
                  | usize _ | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | ordering _ => cases hExt
                  | refMutLoc loc2 =>
                    dsimp at hExt
                    cases hchk2 : (noAliasBefore init.locals loc2 2 &&
                      decide (init.mem.naWriteTs loc2 ≤ init.mem.curView loc2) &&
                      decide (init.mem.naReadTs loc2 ≤ init.mem.curView loc2)) with
                    | false => rw [hchk2] at hExt; cases hExt
                    | true =>
                      rw [hchk2] at hExt
                      dsimp at hExt
                      cases hna2 : init.mem.naVal loc2 with
                      | none => rw [hna2] at hExt; cases hExt
                      | some naMv2 =>
                        rw [hna2] at hExt
                        cases naMv2 with
                        | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ => cases hExt
                        | usize y0' =>
                          dsimp at hExt
                          cases hloc3 : init.locals 3 with
                          | none => rw [hloc3] at hExt; cases hExt
                          | some mv3 =>
                            rw [hloc3] at hExt
                            cases mv3 with
                            | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ => cases hExt
                            | usize a' =>
                              dsimp at hExt
                              cases hloc4 : init.locals 4 with
                              | none => rw [hloc4] at hExt; cases hExt
                              | some mv4 =>
                                rw [hloc4] at hExt
                                cases mv4 with
                                | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ => cases hExt
                                | usize b' =>
                                  dsimp at hExt
                                  injection hExt with hargs
                                  subst hargs
                                  dsimp
                                  rw [translatePure_twoPhaseReborrow_rfl x0' y0' a' b']
                                  refine ⟨(by intro h; cases h), ?_⟩
                                  intro ret hok locX locY x0 y0 a b hl1 hm1 hl2 hm2 hl3 hl4
                                  injection hok with hret
                                  rw [hloc1] at hl1; injection hl1 with h1_mv; injection h1_mv with h1; subst h1
                                  rw [hna1] at hm1; injection hm1 with hx_mv; injection hx_mv with hx; subst hx
                                  rw [hloc2] at hl2; injection hl2 with h2_mv; injection h2_mv with h2; subst h2
                                  rw [hna2] at hm2; injection hm2 with hy_mv; injection hy_mv with hy; subst hy
                                  rw [hloc3] at hl3; injection hl3 with ha_mv; injection ha_mv with ha; subst ha
                                  rw [hloc4] at hl4; injection hl4 with hb_mv; injection hb_mv with hb; subst hb
                                  exact hret.symm

/-- `π_func (FuncLang.Spec FuncPostSortPair)` refines `EnsuresSortPair`. -/
theorem π_func_sortPair_le_ensures :
    π_func (FuncLang.Spec FuncPostSortPair) ≤ EnsuresSortPair := by
  refine Preorder.le_trans (π_func_spec_le FuncPostSortPair) ?_
  intro q _
  refine ⟨True.intro, ?_⟩
  intro out hpost ret locX locY x0 y0 hterm hl1 hm1 hl2 hm2
  exact hpost ret hterm locX locY x0 y0 hl1 hm1 hl2 hm2

/-- `π_func (FuncLang.Spec FuncPostTwoPhaseReborrow)` refines
    `EnsuresTwoPhaseReborrow`. -/
theorem π_func_twoPhaseReborrow_le_ensures :
    π_func (FuncLang.Spec FuncPostTwoPhaseReborrow) ≤ EnsuresTwoPhaseReborrow := by
  refine Preorder.le_trans (π_func_spec_le FuncPostTwoPhaseReborrow) ?_
  intro q _
  refine ⟨True.intro, ?_⟩
  intro out hpost ret locX locY x0 y0 a b hterm hl1 hm1 hl2 hm2 hl3 hl4
  exact hpost ret hterm locX locY x0 y0 a b hl1 hm1 hl2 hm2 hl3 hl4

/-- `EnsuresSortPair` refines baseline `MirLang.WellFormed`. -/
theorem ensuresSortPair_le_wellFormed :
    EnsuresSortPair ≤ MirLang.WellFormed :=
  fun _ _ => ⟨True.intro, fun _ _ => True.intro⟩

/-- `EnsuresTwoPhaseReborrow` refines baseline `MirLang.WellFormed`. -/
theorem ensuresTwoPhaseReborrow_le_wellFormed :
    EnsuresTwoPhaseReborrow ≤ MirLang.WellFormed :=
  fun _ _ => ⟨True.intro, fun _ _ => True.intro⟩

/-- **Source MIR Correctness of `sort_pair`**:
    `MirSem sortPairBody ≤ EnsuresSortPair`, transferred across `π_func` from
    `translate_sortPairBody_spec` via `translate_sound sortPairBody`. -/
theorem sortPairBody_satisfies_ensures :
    MirSem sortPairBody ≤ EnsuresSortPair :=
  Preorder.le_trans
    (Preorder.le_trans
      (translate_sound sortPairBody)
      (monotone_π_func translate_sortPairBody_spec))
    π_func_sortPair_le_ensures

/-- `sortPairBody` satisfies baseline `MirLang.WellFormed`. -/
theorem sortPairBody_satisfies_wellFormed :
    MirSem sortPairBody ≤ MirLang.WellFormed :=
  Preorder.le_trans sortPairBody_satisfies_ensures ensuresSortPair_le_wellFormed

/-- **Source MIR Correctness of `two_phase_reborrow`**:
    `MirSem twoPhaseReborrowBody ≤ EnsuresTwoPhaseReborrow`, transferred across
    `π_func` from `translate_twoPhaseReborrowBody_spec` via
    `translate_sound twoPhaseReborrowBody`. -/
theorem twoPhaseReborrowBody_satisfies_ensures :
    MirSem twoPhaseReborrowBody ≤ EnsuresTwoPhaseReborrow :=
  Preorder.le_trans
    (Preorder.le_trans
      (translate_sound twoPhaseReborrowBody)
      (monotone_π_func translate_twoPhaseReborrowBody_spec))
    π_func_twoPhaseReborrow_le_ensures

/-- `twoPhaseReborrowBody` satisfies baseline `MirLang.WellFormed`. -/
theorem twoPhaseReborrowBody_satisfies_wellFormed :
    MirSem twoPhaseReborrowBody ≤ MirLang.WellFormed :=
  Preorder.le_trans twoPhaseReborrowBody_satisfies_ensures ensuresTwoPhaseReborrow_le_wellFormed

/-- End-to-end `CrateTheorem` witness for `sort_pair` with `EnsuresSortPair`. -/
theorem prove_sort_pair_ensures_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := sortPairBody
        specs := [EnsuresSortPair]
      }]
      tcb := [.rustcLowering fnName sortPairBody]
    } := by
  refine ⟨(by intro h; cases h), ⟨⟨True.intro, True.intro⟩, ?_⟩, True.intro⟩
  intro hAssumptions
  have hVerFunc :
      RustcCompiler.Verified sortPairBody (π_func (FuncLang.Spec FuncPostSortPair)) :=
    verify_through_passes
      translate_sortPairBody_spec
      (translate_sound sortPairBody)
      monotone_π_func
      hAssumptions.1
  have hVerEnsures : RustcCompiler.Verified sortPairBody EnsuresSortPair :=
    Compiler.Verified.mono hVerFunc π_func_sortPair_le_ensures hAssumptions.1.1
  exact Compiler.Verified.with_wellFormedOn
    hVerEnsures
    ensuresSortPair_le_wellFormed
    hAssumptions.1.1

/-- End-to-end `CrateTheorem` witness for `sort_pair` with baseline
    `WellFormed`. -/
theorem prove_sort_pair_wf_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := sortPairBody
        specs := []
      }]
      tcb := [.rustcLowering fnName sortPairBody]
    } :=
  verify_single_fn_wf_crate fnName sortPairBody sortPairBody_satisfies_wellFormed

/-- End-to-end `CrateTheorem` witness for `two_phase_reborrow` with
    `EnsuresTwoPhaseReborrow`. -/
theorem prove_two_phase_reborrow_ensures_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := twoPhaseReborrowBody
        specs := [EnsuresTwoPhaseReborrow]
      }]
      tcb := [.rustcLowering fnName twoPhaseReborrowBody]
    } := by
  refine ⟨(by intro h; cases h), ⟨⟨True.intro, True.intro⟩, ?_⟩, True.intro⟩
  intro hAssumptions
  have hVerFunc :
      RustcCompiler.Verified twoPhaseReborrowBody (π_func (FuncLang.Spec FuncPostTwoPhaseReborrow)) :=
    verify_through_passes
      translate_twoPhaseReborrowBody_spec
      (translate_sound twoPhaseReborrowBody)
      monotone_π_func
      hAssumptions.1
  have hVerEnsures : RustcCompiler.Verified twoPhaseReborrowBody EnsuresTwoPhaseReborrow :=
    Compiler.Verified.mono hVerFunc π_func_twoPhaseReborrow_le_ensures hAssumptions.1.1
  exact Compiler.Verified.with_wellFormedOn
    hVerEnsures
    ensuresTwoPhaseReborrow_le_wellFormed
    hAssumptions.1.1

/-- End-to-end `CrateTheorem` witness for `two_phase_reborrow` with baseline
    `WellFormed`. -/
theorem prove_two_phase_reborrow_wf_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := twoPhaseReborrowBody
        specs := []
      }]
      tcb := [.rustcLowering fnName twoPhaseReborrowBody]
    } :=
  verify_single_fn_wf_crate fnName twoPhaseReborrowBody twoPhaseReborrowBody_satisfies_wellFormed

/-- **Multi-Phase Reborrow Plan-Adequacy Canary (`twoPhaseReborrowBadPlan`)**:
    A defective `TransPlan` for `twoPhaseReborrowBody` that omits `.endLoan 5`
    between Phase 1 (`r1`) and Phase 2 (`r2`), leaving loans `1` and `2` frozen
    when `_11 = copy (*_1)` executes in `bb3`.
    - `evalSym_sound` still holds unconditionally
      (`twoPhaseReborrowBadPlan_still_sound`),
    - `translatePure twoPhaseReborrowBadPlan twoPhaseReborrowBody` fails closed
      with `.fail` (`translatePure_twoPhaseReborrowBadPlan_fails`). -/
def twoPhaseReborrowBadPlan : TransPlan :=
  .step (.step (.step
    (.joinBorrow 5 2 1 3 5
      (.step (.step (.step (.step
        (.joinBorrow 9 1 2 6 9
          (.step (.endLoan 9 (.step .ret)))))))))))

theorem twoPhaseReborrowBadPlan_still_sound :
    Abstracts FuncLang MirLang π_func
      (evalSym twoPhaseReborrowBadPlan twoPhaseReborrowBody)
      twoPhaseReborrowBody :=
  evalSym_sound twoPhaseReborrowBadPlan twoPhaseReborrowBody

theorem translatePure_twoPhaseReborrowBadPlan_fails (x0 y0 a b : Nat) :
    translatePure twoPhaseReborrowBadPlan twoPhaseReborrowBody
      [.refMut x0, .refMut y0, .usize a, .usize b] = .fail :=
  rfl

/-!
## 13. Verification of `add_bounded` and `abs_diff`
-/

/-- Exact `Runtime(PostCleanup)` MIR body emitted by `rustc --edition=2024
    --emit=mir`
    for:
    ```rust
    pub fn add_bounded(x: usize, y: usize) -> usize {
        if x <= 1000 && y <= 1000 {
            x + y
        } else {
            0
        }
    }
    ```
    - `_0: usize` (return place), `_1: usize` (`x`), `_2: usize` (`y`),
      `_3: bool`, `_4: bool`, `_5: (usize, bool)`.
    - `bb0`: `_3 = Le(copy _1, const 1000_usize); switchInt(move _3) -> [0: bb4,
      otherwise: bb1];`
    - `bb1`: `_4 = Le(copy _2, const 1000_usize); switchInt(move _4) -> [0: bb4,
      otherwise: bb2];`
    - `bb2`: `_5 = AddWithOverflow(copy _1, copy _2); assert(!move (_5.1: bool),
      ...) -> [success: bb3, unwind continue];`
    - `bb3`: `_0 = move (_5.0: usize); goto -> bb5;`
    - `bb4`: `_0 = const 0_usize; goto -> bb5;`
    - `bb5`: `return;` -/
def addBoundedBody : MirBody where
  argTys := [.usize, .usize]
  retTy := .usize
  localCount := 6
  blocks := [
    { stmts := [
        .assign ⟨3⟩ (.binaryOp .le (.copy ⟨1⟩) (.constVal (.usize 1000)))
      ]
      terminator := .switchInt (.move ⟨3⟩) ⟨4⟩ ⟨1⟩ },
    { stmts := [
        .assign ⟨4⟩ (.binaryOp .le (.copy ⟨2⟩) (.constVal (.usize 1000)))
      ]
      terminator := .switchInt (.move ⟨4⟩) ⟨4⟩ ⟨2⟩ },
    { stmts := [
        .assign ⟨5⟩ (.checkedBinaryOp .add (.copy ⟨1⟩) (.copy ⟨2⟩))
      ]
      terminator := .assertNotOverflow ⟨5⟩ ⟨3⟩ },
    { stmts := [
        .assign ⟨0⟩ (.proj0 ⟨5⟩)
      ]
      terminator := .goto ⟨5⟩ },
    { stmts := [
        .assign ⟨0⟩ (.use (.constVal (.usize 0)))
      ]
      terminator := .goto ⟨5⟩ },
    { stmts := []
      terminator := .return_ }
  ]

/-- Exact `Runtime(PostCleanup)` MIR body emitted by `rustc --edition=2024
    --emit=mir`
    for:
    ```rust
    pub fn abs_diff(x: usize, y: usize) -> usize {
        if x >= y {
            x - y
        } else {
            y - x
        }
    }
    ```
    - `_0: usize` (return place), `_1: usize` (`x`), `_2: usize` (`y`),
      `_3: bool`, `_4: (usize, bool)`, `_5: (usize, bool)`.
    - `bb0`: `_3 = Ge(copy _1, copy _2); switchInt(move _3) -> [0: bb3,
      otherwise: bb1];`
    - `bb1`: `_4 = SubWithOverflow(copy _1, copy _2); assert(!move (_4.1: bool),
      ...) -> [success: bb2, unwind continue];`
    - `bb2`: `_0 = move (_4.0: usize); goto -> bb5;`
    - `bb3`: `_5 = SubWithOverflow(copy _2, copy _1); assert(!move (_5.1: bool),
      ...) -> [success: bb4, unwind continue];`
    - `bb4`: `_0 = move (_5.0: usize); goto -> bb5;`
    - `bb5`: `return;` -/
def absDiffBody : MirBody where
  argTys := [.usize, .usize]
  retTy := .usize
  localCount := 6
  blocks := [
    { stmts := [
        .assign ⟨3⟩ (.binaryOp .ge (.copy ⟨1⟩) (.copy ⟨2⟩))
      ]
      terminator := .switchInt (.move ⟨3⟩) ⟨3⟩ ⟨1⟩ },
    { stmts := [
        .assign ⟨4⟩ (.checkedBinaryOp .sub (.copy ⟨1⟩) (.copy ⟨2⟩))
      ]
      terminator := .assertNotOverflow ⟨4⟩ ⟨2⟩ },
    { stmts := [
        .assign ⟨0⟩ (.proj0 ⟨4⟩)
      ]
      terminator := .goto ⟨5⟩ },
    { stmts := [
        .assign ⟨5⟩ (.checkedBinaryOp .sub (.copy ⟨2⟩) (.copy ⟨1⟩))
      ]
      terminator := .assertNotOverflow ⟨5⟩ ⟨4⟩ },
    { stmts := [
        .assign ⟨0⟩ (.proj0 ⟨5⟩)
      ]
      terminator := .goto ⟨5⟩ },
    { stmts := []
      terminator := .return_ }
  ]

/-- **First Futamura Projection for `add_bounded`**:
    Evaluating `translatePure (computePlan addBoundedBody) addBoundedBody` on
    universally quantified symbolic inputs `x0 y0 : Nat` reduces by kernel
    `rfl` directly to the nested `zipAeneasRes` with the overflow check on the
    guarded branch. -/
theorem translatePure_addBounded_rfl (x0 y0 : Nat) :
    translatePure (computePlan addBoundedBody) addBoundedBody [.usize x0, .usize y0] =
      zipAeneasRes (decide (x0 ≤ 1000))
        (zipAeneasRes (decide (y0 ≤ 1000))
          (if decide (usizeMax < x0 + y0) then .fail else .ok (.usize (x0 + y0)))
          (.ok (.usize 0)))
        (.ok (.usize 0)) :=
  rfl

/-- Path-sensitive discharge of the overflow assertion in `add_bounded`:
    whenever `x0 ≤ 1000` and `y0 ≤ 1000`, `x0 + y0 ≤ 2000 ≤ usizeMax`, so
    `decide (usizeMax < x0 + y0) = false` and `translatePure` evaluates to
    `.ok (.usize (if decide (x0 ≤ 1000) && decide (y0 ≤ 1000) then x0 + y0 else
    0))`. -/
theorem translatePure_addBounded_eq (x0 y0 : Nat) :
    translatePure (computePlan addBoundedBody) addBoundedBody [.usize x0, .usize y0] =
      .ok (.usize (if decide (x0 ≤ 1000) && decide (y0 ≤ 1000) then x0 + y0 else 0)) := by
  rw [translatePure_addBounded_rfl]
  rw [zipAeneasRes_eq_ite]
  cases hx : decide (x0 ≤ 1000) with
  | false => rfl
  | true =>
    rw [zipAeneasRes_eq_ite]
    cases hy : decide (y0 ≤ 1000) with
    | false => rfl
    | true =>
      have hxle : x0 ≤ 1000 := of_decide_eq_true hx
      have hyle : y0 ≤ 1000 := of_decide_eq_true hy
      have hsum : x0 + y0 ≤ 2000 := Nat.add_le_add hxle hyle
      have h2000 : (2000 : Nat) ≤ usizeMax := by decide
      have hle : x0 + y0 ≤ usizeMax := Nat.le_trans hsum h2000
      have hov : decide (usizeMax < x0 + y0) = false :=
        decide_eq_false (Nat.not_lt_of_ge hle)
      rw [hov]
      rfl

/-- **First Futamura Projection for `abs_diff`**:
    Evaluating `translatePure (computePlan absDiffBody) absDiffBody` on
    universally quantified symbolic inputs `x0 y0 : Nat` reduces by kernel
    `rfl` directly to `zipAeneasRes` over both guarded subtraction arms. -/
theorem translatePure_absDiff_rfl (x0 y0 : Nat) :
    translatePure (computePlan absDiffBody) absDiffBody [.usize x0, .usize y0] =
      zipAeneasRes (decide (y0 ≤ x0))
        (if decide (x0 < y0) then .fail else .ok (.usize (x0 - y0)))
        (if decide (y0 < x0) then .fail else .ok (.usize (y0 - x0))) :=
  rfl

/-- Path-sensitive discharge of both underflow assertions in `abs_diff`:
    - on the `y0 ≤ x0` branch, `decide (x0 < y0) = false`,
    - on the `¬ (y0 ≤ x0)` branch, `x0 < y0` so `decide (y0 < x0) = false`. -/
theorem translatePure_absDiff_eq (x0 y0 : Nat) :
    translatePure (computePlan absDiffBody) absDiffBody [.usize x0, .usize y0] =
      .ok (.usize (if decide (y0 ≤ x0) then x0 - y0 else y0 - x0)) := by
  rw [translatePure_absDiff_rfl]
  rw [zipAeneasRes_eq_ite]
  cases h : decide (y0 ≤ x0) with
  | true =>
    have hle : y0 ≤ x0 := of_decide_eq_true h
    have hov : decide (x0 < y0) = false := decide_eq_false (Nat.not_lt_of_ge hle)
    rw [hov]
    rfl
  | false =>
    have hgt : x0 < y0 := Nat.lt_of_not_le (of_decide_eq_false h)
    have hov : decide (y0 < x0) = false := decide_eq_false (Nat.not_lt_of_gt hgt)
    rw [hov]
    rfl

/-- Pure functional specification extracted from `addBoundedBody`. -/
def pureAddBounded (x0 y0 : Nat) : Nat :=
  if decide (x0 ≤ 1000) && decide (y0 ≤ 1000) then x0 + y0 else 0

/-- Pure functional specification extracted from `absDiffBody`. -/
def pureAbsDiff (x0 y0 : Nat) : Nat :=
  if decide (y0 ≤ x0) then x0 - y0 else y0 - x0

/-- Non-trivial property 1 (`add_bounded` global upper bound):
    `pureAddBounded x0 y0 ≤ 2000` for all `x0, y0 : Nat`. -/
theorem pureAddBounded_le_2000 (x0 y0 : Nat) :
    pureAddBounded x0 y0 ≤ 2000 := by
  unfold pureAddBounded
  cases hx : decide (x0 ≤ 1000) with
  | false => exact Nat.zero_le 2000
  | true =>
    cases hy : decide (y0 ≤ 1000) with
    | false => exact Nat.zero_le 2000
    | true =>
      exact Nat.add_le_add (of_decide_eq_true hx) (of_decide_eq_true hy)

/-- Non-trivial property 2 (`add_bounded` commutativity):
    `pureAddBounded x0 y0 = pureAddBounded y0 x0`. -/
theorem pureAddBounded_comm (x0 y0 : Nat) :
    pureAddBounded x0 y0 = pureAddBounded y0 x0 := by
  unfold pureAddBounded
  cases decide (x0 ≤ 1000) <;> cases decide (y0 ≤ 1000) <;> dsimp
  exact Nat.add_comm x0 y0

/-- Non-trivial property 3 (`abs_diff` symmetry / commutativity):
    `pureAbsDiff x0 y0 = pureAbsDiff y0 x0`. -/
theorem pureAbsDiff_symm (x0 y0 : Nat) :
    pureAbsDiff x0 y0 = pureAbsDiff y0 x0 := by
  unfold pureAbsDiff
  cases h1 : decide (y0 ≤ x0) with
  | true =>
    have hle1 : y0 ≤ x0 := of_decide_eq_true h1
    cases h2 : decide (x0 ≤ y0) with
    | true =>
      have hle2 : x0 ≤ y0 := of_decide_eq_true h2
      have heq : x0 = y0 := Nat.le_antisymm hle2 hle1
      subst heq
      rfl
    | false => rfl
  | false =>
    have hgt : x0 < y0 := Nat.lt_of_not_le (of_decide_eq_false h1)
    have h2 : decide (x0 ≤ y0) = true := decide_eq_true (Nat.le_of_lt hgt)
    rw [h2]
    rfl

/-- Non-trivial property 4 (`abs_diff` self-annihilation):
    `pureAbsDiff x0 x0 = 0`. -/
theorem pureAbsDiff_self (x0 : Nat) :
    pureAbsDiff x0 x0 = 0 := by
  unfold pureAbsDiff
  have h : decide (x0 ≤ x0) = true := decide_eq_true (Nat.le_refl x0)
  rw [h]
  exact Nat.sub_self x0

/-- Non-trivial property 5 (`abs_diff` additive reconstruction of the maximum):
    `min(x0, y0) + pureAbsDiff x0 y0 = max(x0, y0)`. -/
theorem pureAbsDiff_add_min_eq_max (x0 y0 : Nat) :
    (if decide (y0 ≤ x0) then y0 else x0) + pureAbsDiff x0 y0 =
      (if decide (y0 ≤ x0) then x0 else y0) := by
  unfold pureAbsDiff
  cases h : decide (y0 ≤ x0) with
  | true =>
    dsimp
    rw [Nat.add_comm]
    exact Nat.sub_add_cancel (of_decide_eq_true h)
  | false =>
    dsimp
    rw [Nat.add_comm]
    exact Nat.sub_add_cancel (Nat.le_of_lt (Nat.lt_of_not_le (of_decide_eq_false h)))

/-- Functional postcondition for `add_bounded` in `FuncLang`. -/
def FuncPostAddBounded (init : MirState) (ret : MirVal) : Prop :=
  ∀ x0 y0,
    init.locals 1 = some (.usize x0) →
    init.locals 2 = some (.usize y0) →
    ret = .usize (if decide (x0 ≤ 1000) && decide (y0 ≤ 1000) then x0 + y0 else 0)

/-- Functional postcondition for `abs_diff` in `FuncLang`. -/
def FuncPostAbsDiff (init : MirState) (ret : MirVal) : Prop :=
  ∀ x0 y0,
    init.locals 1 = some (.usize x0) →
    init.locals 2 = some (.usize y0) →
    ret = .usize (if decide (y0 ≤ x0) then x0 - y0 else y0 - x0)

/-- `translate addBoundedBody` satisfies `FuncLang.Spec FuncPostAddBounded`. -/
theorem translate_addBoundedBody_spec :
    FuncLang.sem (translate addBoundedBody) ≤ FuncLang.Spec FuncPostAddBounded := by
  refine funcSem_le_spec (fun init => ?_)
  unfold translate evalSym
  have hSupp : allSupportedArgTys addBoundedBody.argTys = true := rfl
  rw [hSupp]
  dsimp
  cases hExt : extractSymArgs addBoundedBody.argTys init with
  | none =>
    refine ⟨(by intro h; cases h), ?_⟩
    intro ret hok
    cases hok
  | some args =>
    unfold extractSymArgs at hExt
    cases hblk : (init.block == 0 && init.stmtIdx == 0) with
    | false => rw [hblk] at hExt; cases hExt
    | true =>
      rw [hblk] at hExt
      dsimp [addBoundedBody, extractSymArgsAux] at hExt
      cases hloc1 : init.locals 1 with
      | none => rw [hloc1] at hExt; cases hExt
      | some mv1 =>
        rw [hloc1] at hExt
        cases mv1 with
        | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ => cases hExt
        | usize x0' =>
          dsimp at hExt
          cases hloc2 : init.locals 2 with
          | none => rw [hloc2] at hExt; cases hExt
          | some mv2 =>
            rw [hloc2] at hExt
            cases mv2 with
            | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ => cases hExt
            | usize y0' =>
              dsimp at hExt
              injection hExt with hargs
              subst hargs
              dsimp
              rw [translatePure_addBounded_eq x0' y0']
              refine ⟨(by intro h; cases h), ?_⟩
              intro ret hok x0 y0 hl1 hl2
              injection hok with hret
              rw [hloc1] at hl1; injection hl1 with h1_mv; injection h1_mv with h1; subst h1
              rw [hloc2] at hl2; injection hl2 with h2_mv; injection h2_mv with h2; subst h2
              exact hret.symm

/-- `translate absDiffBody` satisfies `FuncLang.Spec FuncPostAbsDiff`. -/
theorem translate_absDiffBody_spec :
    FuncLang.sem (translate absDiffBody) ≤ FuncLang.Spec FuncPostAbsDiff := by
  refine funcSem_le_spec (fun init => ?_)
  unfold translate evalSym
  have hSupp : allSupportedArgTys absDiffBody.argTys = true := rfl
  rw [hSupp]
  dsimp
  cases hExt : extractSymArgs absDiffBody.argTys init with
  | none =>
    refine ⟨(by intro h; cases h), ?_⟩
    intro ret hok
    cases hok
  | some args =>
    unfold extractSymArgs at hExt
    cases hblk : (init.block == 0 && init.stmtIdx == 0) with
    | false => rw [hblk] at hExt; cases hExt
    | true =>
      rw [hblk] at hExt
      dsimp [absDiffBody, extractSymArgsAux] at hExt
      cases hloc1 : init.locals 1 with
      | none => rw [hloc1] at hExt; cases hExt
      | some mv1 =>
        rw [hloc1] at hExt
        cases mv1 with
        | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ => cases hExt
        | usize x0' =>
          dsimp at hExt
          cases hloc2 : init.locals 2 with
          | none => rw [hloc2] at hExt; cases hExt
          | some mv2 =>
            rw [hloc2] at hExt
            cases mv2 with
            | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ => cases hExt
            | usize y0' =>
              dsimp at hExt
              injection hExt with hargs
              subst hargs
              dsimp
              rw [translatePure_absDiff_eq x0' y0']
              refine ⟨(by intro h; cases h), ?_⟩
              intro ret hok x0 y0 hl1 hl2
              injection hok with hret
              rw [hloc1] at hl1; injection hl1 with h1_mv; injection h1_mv with h1; subst h1
              rw [hloc2] at hl2; injection hl2 with h2_mv; injection h2_mv with h2; subst h2
              exact hret.symm

/-- `π_func (FuncLang.Spec FuncPostAddBounded)` refines `EnsuresAddBounded`. -/
theorem π_func_addBounded_le_ensures :
    π_func (FuncLang.Spec FuncPostAddBounded) ≤ EnsuresAddBounded := by
  refine Preorder.le_trans (π_func_spec_le FuncPostAddBounded) ?_
  intro q _
  refine ⟨True.intro, ?_⟩
  intro out hpost ret x0 y0 hterm hl1 hl2
  exact hpost ret hterm x0 y0 hl1 hl2

/-- `π_func (FuncLang.Spec FuncPostAbsDiff)` refines `EnsuresAbsDiff`. -/
theorem π_func_absDiff_le_ensures :
    π_func (FuncLang.Spec FuncPostAbsDiff) ≤ EnsuresAbsDiff := by
  refine Preorder.le_trans (π_func_spec_le FuncPostAbsDiff) ?_
  intro q _
  refine ⟨True.intro, ?_⟩
  intro out hpost ret x0 y0 hterm hl1 hl2
  exact hpost ret hterm x0 y0 hl1 hl2

/-- `EnsuresAddBounded` refines baseline `MirLang.WellFormed`. -/
theorem ensuresAddBounded_le_wellFormed :
    EnsuresAddBounded ≤ MirLang.WellFormed :=
  fun _ _ => ⟨True.intro, fun _ _ => True.intro⟩

/-- `EnsuresAbsDiff` refines baseline `MirLang.WellFormed`. -/
theorem ensuresAbsDiff_le_wellFormed :
    EnsuresAbsDiff ≤ MirLang.WellFormed :=
  fun _ _ => ⟨True.intro, fun _ _ => True.intro⟩

/-- **Source MIR Correctness of `add_bounded`**:
    `MirSem addBoundedBody ≤ EnsuresAddBounded`, transferred across `π_func`
    from
    `translate_addBoundedBody_spec` via `translate_sound addBoundedBody`. -/
theorem addBoundedBody_satisfies_ensures :
    MirSem addBoundedBody ≤ EnsuresAddBounded :=
  Preorder.le_trans
    (Preorder.le_trans
      (translate_sound addBoundedBody)
      (monotone_π_func translate_addBoundedBody_spec))
    π_func_addBounded_le_ensures

/-- `addBoundedBody` satisfies baseline `MirLang.WellFormed`. -/
theorem addBoundedBody_satisfies_wellFormed :
    MirSem addBoundedBody ≤ MirLang.WellFormed :=
  Preorder.le_trans addBoundedBody_satisfies_ensures ensuresAddBounded_le_wellFormed

/-- **Source MIR Correctness of `abs_diff`**:
    `MirSem absDiffBody ≤ EnsuresAbsDiff`, transferred across `π_func` from
    `translate_absDiffBody_spec` via `translate_sound absDiffBody`. -/
theorem absDiffBody_satisfies_ensures :
    MirSem absDiffBody ≤ EnsuresAbsDiff :=
  Preorder.le_trans
    (Preorder.le_trans
      (translate_sound absDiffBody)
      (monotone_π_func translate_absDiffBody_spec))
    π_func_absDiff_le_ensures

/-- `absDiffBody` satisfies baseline `MirLang.WellFormed`. -/
theorem absDiffBody_satisfies_wellFormed :
    MirSem absDiffBody ≤ MirLang.WellFormed :=
  Preorder.le_trans absDiffBody_satisfies_ensures ensuresAbsDiff_le_wellFormed

/-- End-to-end `CrateTheorem` witness for `add_bounded` with
    `EnsuresAddBounded`. -/
theorem prove_add_bounded_ensures_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := addBoundedBody
        specs := [EnsuresAddBounded]
      }]
      tcb := [.rustcLowering fnName addBoundedBody]
    } := by
  refine ⟨(by intro h; cases h), ⟨⟨True.intro, True.intro⟩, ?_⟩, True.intro⟩
  intro hAssumptions
  have hVerFunc :
      RustcCompiler.Verified addBoundedBody (π_func (FuncLang.Spec FuncPostAddBounded)) :=
    verify_through_passes
      translate_addBoundedBody_spec
      (translate_sound addBoundedBody)
      monotone_π_func
      hAssumptions.1
  have hVerEnsures : RustcCompiler.Verified addBoundedBody EnsuresAddBounded :=
    Compiler.Verified.mono hVerFunc π_func_addBounded_le_ensures hAssumptions.1.1
  exact Compiler.Verified.with_wellFormedOn
    hVerEnsures
    ensuresAddBounded_le_wellFormed
    hAssumptions.1.1

/-- End-to-end `CrateTheorem` witness for `add_bounded` with baseline
    `WellFormed`. -/
theorem prove_add_bounded_wf_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := addBoundedBody
        specs := []
      }]
      tcb := [.rustcLowering fnName addBoundedBody]
    } :=
  verify_single_fn_wf_crate fnName addBoundedBody addBoundedBody_satisfies_wellFormed

/-- End-to-end `CrateTheorem` witness for `abs_diff` with `EnsuresAbsDiff`. -/
theorem prove_abs_diff_ensures_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := absDiffBody
        specs := [EnsuresAbsDiff]
      }]
      tcb := [.rustcLowering fnName absDiffBody]
    } := by
  refine ⟨(by intro h; cases h), ⟨⟨True.intro, True.intro⟩, ?_⟩, True.intro⟩
  intro hAssumptions
  have hVerFunc :
      RustcCompiler.Verified absDiffBody (π_func (FuncLang.Spec FuncPostAbsDiff)) :=
    verify_through_passes
      translate_absDiffBody_spec
      (translate_sound absDiffBody)
      monotone_π_func
      hAssumptions.1
  have hVerEnsures : RustcCompiler.Verified absDiffBody EnsuresAbsDiff :=
    Compiler.Verified.mono hVerFunc π_func_absDiff_le_ensures hAssumptions.1.1
  exact Compiler.Verified.with_wellFormedOn
    hVerEnsures
    ensuresAbsDiff_le_wellFormed
    hAssumptions.1.1

/-- End-to-end `CrateTheorem` witness for `abs_diff` with baseline
    `WellFormed`. -/
theorem prove_abs_diff_wf_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := absDiffBody
        specs := []
      }]
      tcb := [.rustcLowering fnName absDiffBody]
    } :=
  verify_single_fn_wf_crate fnName absDiffBody absDiffBody_satisfies_wellFormed

/-- **Overflow-Rejection Adequacy Canary (`unguardedSubBody`)**:
    Exact MIR for an unguarded subtraction `pub fn unguarded_sub(x: usize, y:
    usize) -> usize { x - y }`.
    - When `x0 < y0` (e.g., `x0 = 0, y0 = 1`), `SubWithOverflow` sets the
      overflow bit `.1 = true`, so `Terminator.assertNotOverflow` fails closed
      with `.fail` (`translatePure_unguardedSub_underflow_fails`), which is
      rejected by `FuncLang.WellFormed`. -/
def unguardedSubBody : MirBody where
  argTys := [.usize, .usize]
  retTy := .usize
  localCount := 4
  blocks := [
    { stmts := [
        .assign ⟨3⟩ (.checkedBinaryOp .sub (.copy ⟨1⟩) (.copy ⟨2⟩))
      ]
      terminator := .assertNotOverflow ⟨3⟩ ⟨1⟩ },
    { stmts := [
        .assign ⟨0⟩ (.proj0 ⟨3⟩)
      ]
      terminator := .return_ }
  ]

theorem translatePure_unguardedSub_underflow_fails :
    translatePure (computePlan unguardedSubBody) unguardedSubBody [.usize 0, .usize 1] = .fail :=
  rfl

theorem translatePure_unguardedSub_safe :
    translatePure (computePlan unguardedSubBody) unguardedSubBody [.usize 10, .usize 3] = .ok (.usize 7) :=
  rfl

/-!
## 14. Returning `&'a mut usize` via Forward/Backward Lenses (`choose_mut`)
-/

/-- Execute `plan : TransPlan` up to `.ret` at a `Terminator.return_` point,
    returning the terminal `SymState` with its active return borrow and backward
    lens store intact. -/
noncomputable def evalSymStateToReturn (plan : TransPlan) (body : MirBody) (sym : SymState) :
    Option SymState :=
  match plan with
  | .ret =>
    match body.blocks[sym.block]? with
    | none => none
    | some bb =>
      match bb.stmts[sym.stmtIdx]?, bb.terminator with
      | none, .return_ => some sym
      | _, _ => none
  | .step next =>
    match evalSymStep body sym with
    | some (false, sym') => evalSymStateToReturn next body sym'
    | _ => none
  | .endLoan lid next =>
    match evalEndLoan sym lid with
    | some sym' => evalSymStateToReturn next body sym'
    | none => none
  | .joinBorrow dstLocal falseSrc trueSrc joinBlock joinedLid afterJoin =>
    match evalJoinBorrow body sym dstLocal falseSrc trueSrc joinBlock joinedLid with
    | some symJoined => evalSymStateToReturn afterJoin body symJoined
    | none => none
  | _ => none

/-- Extract the Aeneas **forward value** (`SymVal`) of a returned mutable
    reference from a terminal `SymState` whose return place `_0` holds
    `some (.borrow lid)`. -/
def evalMutReturnFwd (sym : SymState) : Option SymVal :=
  match sym.locals 0 with
  | some (.borrow lid) =>
    match sym.loans lid with
    | some entry =>
      if entry.active && !entry.frozen then some entry.curVal else none
    | none => none
  | _ => none

/-- Look up the current `SymVal` of each active unfrozen loan in `lids`. -/
noncomputable def lookupLoanCurVals (loans : Nat → Option LoanEntry) : List Nat → Option (List SymVal)
  | [] => some []
  | lid :: rest =>
    match loans lid with
    | some entry =>
      if entry.active && !entry.frozen then
        match lookupLoanCurVals loans rest with
        | some restVals => some (entry.curVal :: restVals)
        | none => none
      else
        none
    | none => none

/-- Execute the Aeneas **backward lens** (`SymVal → Option (List SymVal)`) on a
    terminal `SymState` whose return place `_0` holds `some (.borrow lid)`:
    writes `retNew` to the returned loan `lid`, ends `lid` via `evalEndLoan`
    (propagating `entry.back retNew` to its parent parameter loans and
    unfreezing them), and extracts the resulting values of `paramLids`. -/
noncomputable def evalMutReturnBack (sym : SymState) (retNew : SymVal) (paramLids : List Nat) :
    Option (List SymVal) :=
  match sym.locals 0 with
  | some (.borrow lid) =>
    match sym.loans lid with
    | some entry =>
      if entry.active && !entry.frozen then
        let symUpdated := {
          sym with
          loans := updateLoan sym.loans lid (some { entry with curVal := retNew })
        }
        match evalEndLoan symUpdated lid with
        | some symEnded => lookupLoanCurVals symEnded.loans paramLids
        | none => none
      else
        none
    | none => none
  | _ => none

/-- Pure Aeneas **forward function** for a function returning `&'a mut
    usize`. -/
noncomputable def translateMutReturnFwd (plan : TransPlan) (body : MirBody)
    (args : List SymArg) : Option SymVal :=
  match evalSymStateToReturn plan body (buildPureSymState args) with
  | some symFinal => evalMutReturnFwd symFinal
  | none => none

/-- Pure Aeneas **backward function (lens)** for a function returning
    `&'a mut usize`. -/
noncomputable def translateMutReturnBack (plan : TransPlan) (body : MirBody)
    (args : List SymArg) (retNew : SymVal) (paramLids : List Nat) : Option (List SymVal) :=
  match evalSymStateToReturn plan body (buildPureSymState args) with
  | some symFinal => evalMutReturnBack symFinal retNew paramLids
  | none => none

/-- Relational soundness of `evalMutReturnFwd` at a `Terminator.return_` point:
    if `StateRel loanLoc sharedLoc sym conc` holds, `sym` is at a `return_`
    terminator, and `evalMutReturnFwd sym = some svFwd` with
    `svFwd.toScalarMirVal = some mvFwd`, then there exist `lid` and `locRet`
    such that `sym.locals 0 = some (.borrow lid)`, `loanLoc lid = some locRet`,
    `SafeAndReturns body conc (.refMutLoc locRet)` holds, and `conc.mem`
    exclusively owns `mvFwd` at `locRet` (`OwnLoc conc.mem locRet mvFwd`). -/
theorem evalMutReturnFwd_sound {loanLoc : Nat → Option Nat} {sharedLoc : Nat → Nat → Prop}
    {body : MirBody} {sym : SymState} {conc : MirState}
    {bb : BasicBlock} {svFwd : SymVal} {mvFwd : MirVal}
    (hState : StateRel loanLoc sharedLoc sym conc)
    (hbb : body.blocks[sym.block]? = some bb)
    (hstmt : bb.stmts[sym.stmtIdx]? = none)
    (hterm : bb.terminator = .return_)
    (hFwd : evalMutReturnFwd sym = some svFwd)
    (hsc : svFwd.toScalarMirVal = some mvFwd) :
    ∃ lid locRet,
      sym.locals 0 = some (.borrow lid) ∧
      loanLoc lid = some locRet ∧
      SafeAndReturns body conc (.refMutLoc locRet) ∧
      OwnLoc conc.mem locRet mvFwd := by
  unfold evalMutReturnFwd at hFwd
  cases hloc0 : sym.locals 0 with
  | none => rw [hloc0] at hFwd; cases hFwd
  | some sv0 =>
    rw [hloc0] at hFwd
    cases sv0 with
    | usize _ | bool _ | unit | tupleUsizeBool _ _ | refShared _ => cases hFwd
    | borrow lid =>
      dsimp at hFwd
      cases hloan : sym.loans lid with
      | none => rw [hloan] at hFwd; cases hFwd
      | some entry =>
        rw [hloan] at hFwd
        dsimp at hFwd
        cases hact : entry.active with
        | false => rw [hact] at hFwd; cases hFwd
        | true =>
          rw [hact] at hFwd
          cases hfrz : entry.frozen with
          | true => rw [hfrz] at hFwd; cases hFwd
          | false =>
            rw [hfrz] at hFwd
            dsimp at hFwd
            injection hFwd with hsvFwd
            subst hsvFwd
            have ⟨mv0, hconc0, hval0⟩ := hState.localRel 0 (.borrow lid) hloc0
            have ⟨locRet, hloanLoc, hmv0⟩ := hval0
            subst hmv0
            have ⟨⟨loc0, mv0', hloanLoc0, hsc0, hown0⟩, _⟩ :=
              hState.loanRel.activeOwn lid entry hloan hact hfrz
            rw [hloanLoc] at hloanLoc0
            injection hloanLoc0 with hloc_eq
            subst hloc_eq
            rw [hsc] at hsc0
            injection hsc0 with hmv_eq
            subst hmv_eq
            refine ⟨lid, locRet, rfl, hloanLoc, ?_, hown0⟩
            refine SafeAndReturns.of_terminated ?_
            unfold evalMirStep
            rw [hState.block_eq, hbb]
            dsimp
            rw [hState.stmtIdx_eq, hstmt]
            dsimp
            rw [hterm]
            dsimp [evalMirTerminator]
            rw [hconc0]

/-- Relational soundness of the backward lens step (`evalMutReturnBack`):
    writing `mvNew` to `locRet` in `conc.mem` (`afterWriteNA conc.mem locRet
    mvNew`)
    and ending `lid` via `evalEndLoan` preserves `StateRel`. -/
theorem evalMutReturnBack_stateRel {loanLoc : Nat → Option Nat} {sharedLoc : Nat → Nat → Prop}
    {sym symEnded : SymState} {conc : MirState}
    {lid : Nat} {entry : LoanEntry} {locRet : Nat}
    {retNew : SymVal} {mvNew : MirVal}
    (hState : StateRel loanLoc sharedLoc sym conc)
    (hloan : sym.loans lid = some entry)
    (hact : entry.active = true)
    (hfrz : entry.frozen = false)
    (hloc : loanLoc lid = some locRet)
    (hscNew : retNew.toScalarMirVal = some mvNew)
    (hEnd :
      evalEndLoan
        { sym with loans := updateLoan sym.loans lid (some { entry with curVal := retNew }) }
        lid = some symEnded) :
    StateRel loanLoc sharedLoc symEnded { conc with mem := afterWriteNA conc.mem locRet mvNew } := by
  have ⟨⟨loc0, mvOld, hloc0, _, hownOld⟩, _⟩ :=
    hState.loanRel.activeOwn lid entry hloan hact hfrz
  rw [hloc] at hloc0
  injection hloc0 with hloc_eq
  subst hloc_eq
  have hStateUpdated :
      StateRel loanLoc sharedLoc
        { sym with loans := updateLoan sym.loans lid (some { entry with curVal := retNew }) }
        { conc with mem := afterWriteNA conc.mem locRet mvNew } := {
    block_eq := hState.block_eq
    stmtIdx_eq := hState.stmtIdx_eq
    localBorrows := fun i lid' hi =>
      loans_some_updateLoan lid { entry with curVal := retNew } (hState.localBorrows i lid' hi)
    localRel := hState.localRel
    loanRel := LoanRel.update_curVal hState.loanRel hloan hact hfrz hloc hownOld hscNew
  }
  exact evalEndLoan_sound hStateUpdated hEnd

/-- Structural soundness of `evalSymStateToReturn`: if `evalSymStateToReturn
    plan body sym = some symFinal`
    and `evalMutReturnFwd symFinal = some svFwd` with `svFwd.toScalarMirVal =
    some mvFwd`,
    then from any related concrete state `conc`, execution is safe and
    terminates
    normally with some `.refMutLoc locRet`. -/
theorem evalSymStateToReturn_sound (plan : TransPlan) (body : MirBody) :
    ∀ {loanLoc : Nat → Option Nat} {sharedLoc : Nat → Nat → Prop}
      {sym symFinal : SymState} {conc : MirState} {svFwd : SymVal} {mvFwd : MirVal},
      StateRel loanLoc sharedLoc sym conc →
      evalSymStateToReturn plan body sym = some symFinal →
      evalMutReturnFwd symFinal = some svFwd →
      svFwd.toScalarMirVal = some mvFwd →
      ∃ locRet, SafeAndReturns body conc (.refMutLoc locRet) := by
  induction plan with
  | fail | branch _ _ =>
    intro _ _ _ _ _ _ _ _ hEval _ _
    cases hEval
  | ret =>
    intro _ _ sym symFinal conc svFwd mvFwd hState hEval hFwd hsc
    unfold evalSymStateToReturn at hEval
    cases hbb : body.blocks[sym.block]? with
    | none => rw [hbb] at hEval; cases hEval
    | some bb =>
      rw [hbb] at hEval
      dsimp at hEval
      cases hstmt : bb.stmts[sym.stmtIdx]? with
      | some _ => rw [hstmt] at hEval; cases hEval
      | none =>
        rw [hstmt] at hEval
        cases hterm : bb.terminator with
        | goto _ | unreachable | callAtomicLoad _ _ _ _ | switchInt _ _ _
        | assertNotOverflow _ _ | callPure2 _ _ _ _ _ =>
          rw [hterm] at hEval; cases hEval
        | return_ =>
          rw [hterm] at hEval
          injection hEval with hsym
          subst hsym
          have ⟨_, locRet, _, _, hSafe, _⟩ :=
            evalMutReturnFwd_sound hState hbb hstmt hterm hFwd hsc
          exact ⟨locRet, hSafe⟩
  | step next ih =>
    intro _ _ sym symFinal conc svFwd mvFwd hState hEval hFwd hsc
    unfold evalSymStateToReturn at hEval
    cases hStep : evalSymStep body sym with
    | none => rw [hStep] at hEval; cases hEval
    | some p =>
      cases p with
      | mk ov sym' =>
        rw [hStep] at hEval
        cases ov with
        | true => cases hEval
        | false =>
          dsimp at hEval
          have ⟨conc', hConcStep, hState'⟩ := evalSymStep_sound hState hStep
          have ⟨locRet, hSafe⟩ := ih hState' hEval hFwd hsc
          exact ⟨locRet, SafeAndReturns.of_step hConcStep hSafe⟩
  | endLoan lid next ih =>
    intro _ _ sym symFinal conc svFwd mvFwd hState hEval hFwd hsc
    unfold evalSymStateToReturn at hEval
    cases hEnd : evalEndLoan sym lid with
    | none => rw [hEnd] at hEval; cases hEval
    | some sym' =>
      rw [hEnd] at hEval
      exact ih (evalEndLoan_sound hState hEnd) hEval hFwd hsc
  | joinBorrow dstLocal falseSrc trueSrc joinBlock joinedLid afterJoin ihAfter =>
    intro _ _ sym symFinal conc svFwd mvFwd hState hEval hFwd hsc
    unfold evalSymStateToReturn at hEval
    cases hJoin : evalJoinBorrow body sym dstLocal falseSrc trueSrc joinBlock joinedLid with
    | none => rw [hJoin] at hEval; cases hEval
    | some symJoined =>
      rw [hJoin] at hEval
      have ⟨loanLoc', concJoined, hStateJoined, hStepChain⟩ :=
        evalJoinBorrow_sound hState hJoin
      have ⟨locRet, hSafeJoined⟩ := ihAfter hStateJoined hEval hFwd hsc
      exact ⟨locRet, hStepChain (.refMutLoc locRet) hSafeJoined⟩

/-- Exact `Runtime(PostCleanup)` MIR body emitted by `rustc --edition=2024
    --emit=mir`
    for:
    ```rust
    pub fn choose_mut<'a>(b: bool, x: &'a mut usize, y: &'a mut usize) -> &'a mut usize {
        if b { x } else { y }
    }
    ``` -/
def chooseMutBody : MirBody where
  argTys := [.bool, .refMutUsize, .refMutUsize]
  retTy := .refMutUsize
  localCount := 5
  blocks := [
    { stmts := []
      terminator := .switchInt (.copy ⟨1⟩) ⟨2⟩ ⟨1⟩ },
    { stmts := [
        .assign ⟨4⟩ (.use (.copy ⟨2⟩))
      ]
      terminator := .goto ⟨3⟩ },
    { stmts := [
        .assign ⟨4⟩ (.use (.copy ⟨3⟩))
      ]
      terminator := .goto ⟨3⟩ },
    { stmts := [
        .assign ⟨0⟩ (.use (.copy ⟨4⟩))
      ]
      terminator := .return_ }
  ]

/-- `translateMutReturnFwd` on `chooseMutBody` with symbolic inputs `(b, x0,
    y0)`
    reduces by `rfl` to `some (.usize (if b then x0 else y0))`. -/
theorem translateMutReturnFwd_chooseMut (b : Bool) (x0 y0 : Nat) :
    translateMutReturnFwd (computePlan chooseMutBody) chooseMutBody
      [.bool b, .refMut x0, .refMut y0] =
      some (.usize (if b then x0 else y0)) :=
  rfl

/-- `translateMutReturnBack` on `chooseMutBody` with symbolic inputs `(b, x0,
    y0)`
    and caller writeback value `v` reduces by `rfl` to
    `some [.usize (if b then v else x0), .usize (if b then y0 else v)]`. -/
theorem translateMutReturnBack_chooseMut (b : Bool) (x0 y0 v : Nat) :
    translateMutReturnBack (computePlan chooseMutBody) chooseMutBody
      [.bool b, .refMut x0, .refMut y0] (.usize v) [2, 3] =
      some [.usize (if b then v else x0), .usize (if b then y0 else v)] :=
  rfl

/-- Pure Aeneas forward function for `choose_mut`. -/
def pureChooseMutFwd (b : Bool) (x0 y0 : Nat) : Nat :=
  if b then x0 else y0

/-- Pure Aeneas backward lens for `choose_mut`. -/
def pureChooseMutBack (b : Bool) (x0 y0 v : Nat) : Nat × Nat :=
  (if b then v else x0, if b then y0 else v)

/-- Non-trivial lens property 1 (**Get-Put** law for `choose_mut`):
    writing back the forward value read from `choose_mut` leaves `(x0, y0)`
    unchanged. -/
theorem pureChooseMut_get_put (b : Bool) (x0 y0 : Nat) :
    pureChooseMutBack b x0 y0 (pureChooseMutFwd b x0 y0) = (x0, y0) := by
  cases b <;> rfl

/-- Non-trivial lens property 2 (**Put-Get** law for `choose_mut`):
    reading via `pureChooseMutFwd` from the pair updated by `pureChooseMutBack`
    with `v` yields `v`. -/
theorem pureChooseMut_put_get (b : Bool) (x0 y0 v : Nat) :
    let p := pureChooseMutBack b x0 y0 v
    pureChooseMutFwd b p.1 p.2 = v := by
  cases b <;> rfl

/-- Non-trivial lens property 3 (**Put-Put** law for `choose_mut`):
    writing `v1` and then `v2` via `pureChooseMutBack` is equivalent to writing
    `v2` directly. -/
theorem pureChooseMut_put_put (b : Bool) (x0 y0 v1 v2 : Nat) :
    let p := pureChooseMutBack b x0 y0 v1
    pureChooseMutBack b p.1 p.2 v2 = pureChooseMutBack b x0 y0 v2 := by
  cases b <;> rfl

/-- `chooseMutBody` satisfies `MirLang.WellFormed`, proved via
    `evalSymStateToReturn_sound` on `computePlan chooseMutBody`. -/
theorem chooseMutBody_satisfies_wellFormed :
    MirLang.sem chooseMutBody ≤ MirLang.WellFormed := by
  intro q _
  refine ⟨?_, fun _ _ => True.intro⟩
  intro hInit tr out hreach
  have hSupp : allSupportedArgTys chooseMutBody.argTys = true := rfl
  have ⟨args, hExt⟩ := extractSymArgs_of_initMirState hSupp hInit
  have ⟨loanLoc, sharedLoc, hState⟩ := extractSymArgs_sound chooseMutBody.argTys q.init args hExt
  unfold extractSymArgs at hExt
  cases hblk : (q.init.block == 0 && q.init.stmtIdx == 0) with
  | false => rw [hblk] at hExt; cases hExt
  | true =>
    rw [hblk] at hExt
    dsimp [chooseMutBody, extractSymArgsAux] at hExt
    cases h1 : q.init.locals 1 with
    | none => rw [h1] at hExt; cases hExt
    | some v1 =>
      rw [h1] at hExt
      cases v1 with
      | usize _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ => cases hExt
      | bool b =>
        dsimp at hExt
        cases h2 : q.init.locals 2 with
        | none => rw [h2] at hExt; cases hExt
        | some v2 =>
          rw [h2] at hExt
          cases v2 with
          | usize _ | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | ordering _ => cases hExt
          | refMutLoc locX =>
            dsimp at hExt
            cases hchk2 : (noAliasBefore q.init.locals locX 2 &&
              decide (q.init.mem.naWriteTs locX ≤ q.init.mem.curView locX) &&
              decide (q.init.mem.naReadTs locX ≤ q.init.mem.curView locX)) with
            | false => rw [hchk2] at hExt; cases hExt
            | true =>
              rw [hchk2] at hExt
              dsimp at hExt
              cases hna2 : q.init.mem.naVal locX with
              | none => rw [hna2] at hExt; cases hExt
              | some mvX =>
                rw [hna2] at hExt
                cases mvX with
                | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ => cases hExt
                | usize x0 =>
                  dsimp at hExt
                  cases h3 : q.init.locals 3 with
                  | none => rw [h3] at hExt; cases hExt
                  | some v3 =>
                    rw [h3] at hExt
                    cases v3 with
                    | usize _ | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | ordering _ => cases hExt
                    | refMutLoc locY =>
                      dsimp at hExt
                      cases hchk3 : (noAliasBefore q.init.locals locY 3 &&
                        decide (q.init.mem.naWriteTs locY ≤ q.init.mem.curView locY) &&
                        decide (q.init.mem.naReadTs locY ≤ q.init.mem.curView locY)) with
                      | false => rw [hchk3] at hExt; cases hExt
                      | true =>
                        rw [hchk3] at hExt
                        dsimp at hExt
                        cases hna3 : q.init.mem.naVal locY with
                        | none => rw [hna3] at hExt; cases hExt
                        | some mvY =>
                          rw [hna3] at hExt
                          cases mvY with
                          | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ => cases hExt
                          | usize y0 =>
                            dsimp at hExt
                            injection hExt with hargs
                            subst hargs
                            have ⟨locRet, hSafe⟩ :=
                              evalSymStateToReturn_sound (computePlan chooseMutBody) chooseMutBody
                                hState rfl rfl (by dsimp [SymVal.toScalarMirVal]; rfl)
                            exact (hSafe q.init q.steps tr out hreach).1

/-- Deterministic 4-step execution of `chooseMutBody` from an initial `MirState`
    where `_1 = some (.bool b)`, `_2 = some (.refMutLoc locX)`, and
    `_3 = some (.refMutLoc locY)`. -/
theorem chooseMutBody_safeAndReturns_of_locals {init : MirState}
    {b : Bool} {locX locY : Nat}
    (hblk : init.block = 0)
    (hstmt : init.stmtIdx = 0)
    (h1 : init.locals 1 = some (.bool b))
    (h2 : init.locals 2 = some (.refMutLoc locX))
    (h3 : init.locals 3 = some (.refMutLoc locY)) :
    SafeAndReturns chooseMutBody init (.refMutLoc (if b then locX else locY)) := by
  have h2' : updateLocal init.locals 4 (some (.refMutLoc locX)) 4 = some (.refMutLoc locX) := by
    dsimp [updateLocal]
  have h3' : updateLocal init.locals 4 (some (.refMutLoc locY)) 4 = some (.refMutLoc locY) := by
    dsimp [updateLocal]
  have h0X : updateLocal (updateLocal init.locals 4 (some (.refMutLoc locX))) 0 (some (.refMutLoc locX)) 0 =
      some (.refMutLoc locX) := by
    dsimp [updateLocal]
  have h0Y : updateLocal (updateLocal init.locals 4 (some (.refMutLoc locY))) 0 (some (.refMutLoc locY)) 0 =
      some (.refMutLoc locY) := by
    dsimp [updateLocal]
  cases b with
  | false =>
    have s1 : evalMirStep chooseMutBody init =
        .step () { init with block := 2, stmtIdx := 0 } := by
      unfold evalMirStep
      rw [hblk, hstmt]
      change evalMirTerminator init (.switchInt (.copy ⟨1⟩) ⟨2⟩ ⟨1⟩) = _
      dsimp [evalMirTerminator, evalOperand]
      rw [h1]
    have s2 : evalMirStep chooseMutBody { init with block := 2, stmtIdx := 0 } =
        .step () { init with locals := updateLocal init.locals 4 (some (.refMutLoc locY)), block := 2, stmtIdx := 1 } := by
      unfold evalMirStep
      change evalMirStmt { init with block := 2, stmtIdx := 0 } (.assign ⟨4⟩ (.use (.copy ⟨3⟩))) = _
      dsimp [evalMirStmt, evalOperand]
      rw [h3]
    have s3 : evalMirStep chooseMutBody
        { init with locals := updateLocal init.locals 4 (some (.refMutLoc locY)), block := 2, stmtIdx := 1 } =
        .step () { init with locals := updateLocal init.locals 4 (some (.refMutLoc locY)), block := 3, stmtIdx := 0 } := by
      rfl
    have s4 : evalMirStep chooseMutBody
        { init with locals := updateLocal init.locals 4 (some (.refMutLoc locY)), block := 3, stmtIdx := 0 } =
        .step () {
          init with
          locals := updateLocal (updateLocal init.locals 4 (some (.refMutLoc locY))) 0 (some (.refMutLoc locY))
          block := 3
          stmtIdx := 1
        } := by
      unfold evalMirStep
      change evalMirStmt
        { init with locals := updateLocal init.locals 4 (some (.refMutLoc locY)), block := 3, stmtIdx := 0 }
        (.assign ⟨0⟩ (.use (.copy ⟨4⟩))) = _
      dsimp [evalMirStmt, evalOperand]
      rw [h3']
    have s5 : evalMirStep chooseMutBody
        { init with
          locals := updateLocal (updateLocal init.locals 4 (some (.refMutLoc locY))) 0 (some (.refMutLoc locY))
          block := 3
          stmtIdx := 1
        } = .terminated (.normal (.refMutLoc locY)) := by
      unfold evalMirStep
      change evalMirTerminator
        { init with
          locals := updateLocal (updateLocal init.locals 4 (some (.refMutLoc locY))) 0 (some (.refMutLoc locY))
          block := 3
          stmtIdx := 1
        } .return_ = _
      dsimp [evalMirTerminator]
      rw [h0Y]
    exact SafeAndReturns.of_step s1
      (SafeAndReturns.of_step s2
        (SafeAndReturns.of_step s3
          (SafeAndReturns.of_step s4
            (SafeAndReturns.of_terminated s5))))
  | true =>
    have s1 : evalMirStep chooseMutBody init =
        .step () { init with block := 1, stmtIdx := 0 } := by
      unfold evalMirStep
      rw [hblk, hstmt]
      change evalMirTerminator init (.switchInt (.copy ⟨1⟩) ⟨2⟩ ⟨1⟩) = _
      dsimp [evalMirTerminator, evalOperand]
      rw [h1]
    have s2 : evalMirStep chooseMutBody { init with block := 1, stmtIdx := 0 } =
        .step () { init with locals := updateLocal init.locals 4 (some (.refMutLoc locX)), block := 1, stmtIdx := 1 } := by
      unfold evalMirStep
      change evalMirStmt { init with block := 1, stmtIdx := 0 } (.assign ⟨4⟩ (.use (.copy ⟨2⟩))) = _
      dsimp [evalMirStmt, evalOperand]
      rw [h2]
    have s3 : evalMirStep chooseMutBody
        { init with locals := updateLocal init.locals 4 (some (.refMutLoc locX)), block := 1, stmtIdx := 1 } =
        .step () { init with locals := updateLocal init.locals 4 (some (.refMutLoc locX)), block := 3, stmtIdx := 0 } := by
      rfl
    have s4 : evalMirStep chooseMutBody
        { init with locals := updateLocal init.locals 4 (some (.refMutLoc locX)), block := 3, stmtIdx := 0 } =
        .step () {
          init with
          locals := updateLocal (updateLocal init.locals 4 (some (.refMutLoc locX))) 0 (some (.refMutLoc locX))
          block := 3
          stmtIdx := 1
        } := by
      unfold evalMirStep
      change evalMirStmt
        { init with locals := updateLocal init.locals 4 (some (.refMutLoc locX)), block := 3, stmtIdx := 0 }
        (.assign ⟨0⟩ (.use (.copy ⟨4⟩))) = _
      dsimp [evalMirStmt, evalOperand]
      rw [h2']
    have s5 : evalMirStep chooseMutBody
        { init with
          locals := updateLocal (updateLocal init.locals 4 (some (.refMutLoc locX))) 0 (some (.refMutLoc locX))
          block := 3
          stmtIdx := 1
        } = .terminated (.normal (.refMutLoc locX)) := by
      unfold evalMirStep
      change evalMirTerminator
        { init with
          locals := updateLocal (updateLocal init.locals 4 (some (.refMutLoc locX))) 0 (some (.refMutLoc locX))
          block := 3
          stmtIdx := 1
        } .return_ = _
      dsimp [evalMirTerminator]
      rw [h0X]
    exact SafeAndReturns.of_step s1
      (SafeAndReturns.of_step s2
        (SafeAndReturns.of_step s3
          (SafeAndReturns.of_step s4
            (SafeAndReturns.of_terminated s5))))

/-- `chooseMutBody` satisfies `EnsuresChooseMut`. -/
theorem chooseMutBody_satisfies_ensures :
    MirLang.sem chooseMutBody ≤ EnsuresChooseMut := by
  intro q _
  refine ⟨(chooseMutBody_satisfies_wellFormed q True.intro).1, ?_⟩
  intro out hexec ret b locX locY hout h1 h2 h3
  have hSafe :=
    chooseMutBody_safeAndReturns_of_locals
      hexec.1.1 hexec.1.2.1 h1 h2 h3
  exact (hSafe q.init q.steps out.trace out.outcome hexec.2).2 ret hout

theorem ensuresChooseMut_le_wellFormed :
    EnsuresChooseMut ≤ MirLang.WellFormed :=
  fun _ h => ⟨h, fun _ _ => True.intro⟩

/-- End-to-end `CrateTheorem` witness for `choose_mut` with
    `EnsuresChooseMut`. -/
theorem prove_choose_mut_ensures_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := chooseMutBody
        specs := [EnsuresChooseMut]
      }]
      tcb := [.rustcLowering fnName chooseMutBody]
    } :=
  verify_single_fn_crate
    fnName
    chooseMutBody
    EnsuresChooseMut
    chooseMutBody_satisfies_ensures
    ensuresChooseMut_le_wellFormed

/-- End-to-end `CrateTheorem` witness for `choose_mut` with baseline
    `WellFormed`. -/
theorem prove_choose_mut_wf_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := chooseMutBody
        specs := []
      }]
      tcb := [.rustcLowering fnName chooseMutBody]
    } :=
  verify_single_fn_wf_crate fnName chooseMutBody chooseMutBody_satisfies_wellFormed

/-!
## 15. Input-Indexed `SymPlan` and Verification of `while` Loops (`count_up`)

To verify functions containing `while` loops whose iteration count depends on
runtime
scalar arguments (such as `pub fn count_up(n: usize) -> usize`), we generalize
static
plans `plan : TransPlan` to input-indexed plans `SymPlan := List SymArg →
TransPlan`.
Because `evalSymState_sound` already holds for every `plan : TransPlan` and
every
symbolic argument vector `args : List SymArg`, `evalSymWith_sound` follows by
instantiating `evalSymState_sound (symPlan args) body` at the extracted argument
vector `args`.
-/

/-- Input-indexed translation plan (`SymPlan`): maps a symbolic argument vector
    `args : List SymArg` to a finite `TransPlan`, enabling unbounded
    input-dependent
    loop unrolling while reusing `evalSymState_sound`. -/
def SymPlan := List SymArg → TransPlan

/-- Pure shallow functional evaluator parameterized by an input-indexed
    `symPlan : SymPlan`. -/
noncomputable def translatePureWith (symPlan : SymPlan) (body : MirBody)
    (args : List SymArg) : AeneasRes MirVal :=
  translatePure (symPlan args) body args

/-- Input-indexed functional evaluator `evalSymWith : SymPlan → MirBody →
    FuncLang.Prog`
    lifting `translatePureWith` to `MirState` via `extractSymArgs`. -/
noncomputable def evalSymWith (symPlan : SymPlan) (body : MirBody) (init : MirState) :
    AeneasRes MirVal :=
  if allSupportedArgTys body.argTys then
    match extractSymArgs body.argTys init with
    | some args => translatePureWith symPlan body args
    | none => .inapplicable
  else
    .fail

/-- **Universal Input-Indexed Soundness Theorem (`evalSymWith_sound`)**:
    For **every** input-indexed plan `symPlan : SymPlan` and **every** MIR body
    `body : MirBody`, `evalSymWith symPlan body` is a sound functional
    abstraction of `body`
    (`Abstracts FuncLang MirLang π_func (evalSymWith symPlan body) body`). -/
theorem evalSymWith_sound (symPlan : SymPlan) (body : MirBody) :
    Abstracts FuncLang MirLang π_func (evalSymWith symPlan body) body := by
  intro q hdef
  have hne : evalSymWith symPlan body q.init ≠ .fail := hdef
  unfold evalSymWith at hne
  cases hSupp : allSupportedArgTys body.argTys with
  | false =>
    rw [hSupp] at hne
    exact False.elim (hne rfl)
  | true =>
    rw [hSupp] at hne
    dsimp at hne
    cases hExt : extractSymArgs body.argTys q.init with
    | none =>
      have hNotInit : ¬ initMirState body q.init := by
        intro hInit
        have ⟨args, hSome⟩ := extractSymArgs_of_initMirState hSupp hInit
        rw [hExt] at hSome
        cases hSome
      refine ⟨fun hInit => False.elim (hNotInit hInit), ?_⟩
      intro out hexec
      exact False.elim (hNotInit hexec.1)
    | some args =>
      rw [hExt] at hne
      dsimp [translatePureWith] at hne
      cases hRes : translatePure (symPlan args) body args with
      | fail =>
        rw [hRes] at hne
        exact False.elim (hne rfl)
      | inapplicable =>
        exact False.elim (evalSymState_ne_inapplicable (symPlan args) body (buildPureSymState args) hRes)
      | ok ret =>
        have ⟨loanLoc, sharedLoc, hState⟩ := extractSymArgs_sound body.argTys q.init args hExt
        have hSafe : SafeAndReturns body q.init ret :=
          evalSymState_sound (symPlan args) body hState hRes
        have hMirDef : (MirLang.sem body q).defined :=
          fun _ tr out hreach => (hSafe q.init q.steps tr out hreach).1
        refine ⟨hMirDef, ?_⟩
        intro out hexec
        have h := hSafe q.init q.steps out.trace out.outcome hexec.2
        refine ⟨h.1, ?_⟩
        intro r hr
        have hr_eq : r = ret := h.2 r hr
        subst hr_eq
        change evalSymWith symPlan body q.init = .ok r
        unfold evalSymWith
        rw [hSupp]
        dsimp
        rw [hExt]
        exact hRes

/-- Exact `Runtime(PostCleanup)` MIR body emitted by `rustc --edition=2024
    --emit=mir`
    for:
    ```rust
    pub fn count_up(n: usize) -> usize {
        let mut i = 0;
        while i < n && i < 1000 {
            i += 1;
        }
        i
    }
    ``` -/
def countUpBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 8
  blocks := [
    { stmts := [
        .assign ⟨2⟩ (.use (.constVal (.usize 0)))
      ]
      terminator := .goto ⟨1⟩ },
    { stmts := [
        .assign ⟨4⟩ (.use (.copy ⟨2⟩)),
        .assign ⟨3⟩ (.binaryOp .lt (.move ⟨4⟩) (.copy ⟨1⟩))
      ]
      terminator := .switchInt (.move ⟨3⟩) ⟨5⟩ ⟨2⟩ },
    { stmts := [
        .assign ⟨6⟩ (.use (.copy ⟨2⟩)),
        .assign ⟨5⟩ (.binaryOp .lt (.move ⟨6⟩) (.constVal (.usize 1000)))
      ]
      terminator := .switchInt (.move ⟨5⟩) ⟨5⟩ ⟨3⟩ },
    { stmts := [
        .assign ⟨7⟩ (.checkedBinaryOp .add (.copy ⟨2⟩) (.constVal (.usize 1)))
      ]
      terminator := .assertNotOverflow ⟨7⟩ ⟨4⟩ },
    { stmts := [
        .assign ⟨2⟩ (.proj0 ⟨7⟩)
      ]
      terminator := .goto ⟨1⟩ },
    { stmts := [
        .assign ⟨0⟩ (.use (.copy ⟨2⟩))
      ]
      terminator := .return_ }
  ]

/-- Loop-unrolling `TransPlan` for `count_up` starting at loop header `bb1`
    with fuel `k`. -/
noncomputable def countUpLoopPlan : Nat → TransPlan
  | 0 => .fail
  | k + 1 =>
    .step (.step (.branch
      (.step .ret)
      (.step (.step (.branch
        (.step .ret)
        (.step (.step (.step (.step (countUpLoopPlan k))))))))))

/-- Input-indexed `SymPlan` for `count_up`: steps through `bb0` (2 steps) and
    invokes `countUpLoopPlan (n + 1)` at `bb1`. -/
noncomputable def countUpSymPlan : SymPlan
  | [.usize n] => .step (.step (countUpLoopPlan (n + 1)))
  | _ => .fail

/-- Symbolic loop invariant at the entry of loop header `bb1` (`block = 1,
    stmtIdx = 0`)
    for `count_up`. -/
structure CountUpLoopInv (i n : Nat) (sym : SymState) : Prop where
  block_eq : sym.block = 1
  stmtIdx_eq : sym.stmtIdx = 0
  local1 : sym.locals 1 = some (.usize n)
  local2 : sym.locals 2 = some (.usize i)

/-- Symbolic local environment after executing `bb1` (`_4 = copy _2; _3 =
    Lt(move _4, copy _1); switchInt(move _3)`). -/
noncomputable def countUpLocalsAfterBb1 (locals : Nat → Option SymVal) (i n : Nat) :
    Nat → Option SymVal :=
  updateSymLocal
    (updateSymLocal
      (updateSymLocal
        (updateSymLocal locals 4 (some (.usize i)))
        4 none)
      3 (some (.bool (decide (i < n)))))
    3 none

/-- Symbolic local environment after executing `bb2` (`_6 = copy _2; _5 =
    Lt(move _6, const 1000); switchInt(move _5)`). -/
noncomputable def countUpLocalsAfterBb2 (locals : Nat → Option SymVal) (i : Nat) :
    Nat → Option SymVal :=
  updateSymLocal
    (updateSymLocal
      (updateSymLocal
        (updateSymLocal locals 6 (some (.usize i)))
        6 none)
      5 (some (.bool (decide (i < 1000)))))
    5 none

/-- Symbolic local environment after executing `bb3 -> bb4` (`_7 =
    AddWithOverflow(copy _2, 1); _2 = move (_7.0)`). -/
noncomputable def countUpLocalsAfterBb4 (locals : Nat → Option SymVal) (i : Nat) :
    Nat → Option SymVal :=
  updateSymLocal
    (updateSymLocal locals 7 (some (.tupleUsizeBool (i + 1) false)))
    2 (some (.usize (i + 1)))

theorem evalSymState_step_of_some {body : MirBody} {sym sym' : SymState} {next : TransPlan}
    (h : evalSymStep body sym = some (false, sym')) :
    evalSymState (.step next) body sym = evalSymState next body sym' := by
  change
    (match evalSymStep body sym with
     | some (ov, sym') => if ov then .fail else evalSymState next body sym'
     | none => .fail) = evalSymState next body sym'
  rw [h]
  rfl

theorem evalSymState_branch_of_some {body : MirBody} {sym symF symT : SymState}
    {cond : Bool} {falsePlan truePlan : TransPlan}
    (h : evalBranchStep body sym = some (cond, symF, symT)) :
    evalSymState (.branch falsePlan truePlan) body sym =
      if cond then evalSymState truePlan body symT else evalSymState falsePlan body symF := by
  change
    (match evalBranchStep body sym with
     | some (cond, symFalse, symTrue) =>
       zipAeneasRes cond (evalSymState truePlan body symTrue) (evalSymState falsePlan body symFalse)
     | none => .fail) = _
  rw [h]
  dsimp
  exact zipAeneasRes_eq_ite cond (evalSymState truePlan body symT) (evalSymState falsePlan body symF)

theorem evalSymState_ret_of_some {body : MirBody} {sym : SymState} {mv : MirVal}
    (h : evalReturn body sym = some mv) :
    evalSymState .ret body sym = .ok mv := by
  unfold evalSymState
  rw [h]

theorem evalSymState_countUp_bb1 {i n : Nat} {sym : SymState}
    (hInv : CountUpLoopInv i n sym)
    (falsePlan truePlan : TransPlan) :
    evalSymState (.step (.step (.branch falsePlan truePlan))) countUpBody sym =
      if decide (i < n) then
        evalSymState truePlan countUpBody
          { sym with locals := countUpLocalsAfterBb1 sym.locals i n, block := 2, stmtIdx := 0 }
      else
        evalSymState falsePlan countUpBody
          { sym with locals := countUpLocalsAfterBb1 sym.locals i n, block := 5, stmtIdx := 0 } := by
  cases sym with
  | mk locals loans nextLoan hasActiveJoin block stmtIdx =>
    have hblk := hInv.block_eq
    have hstmt := hInv.stmtIdx_eq
    have h1 := hInv.local1
    have h2 := hInv.local2
    dsimp at hblk hstmt h1 h2
    subst hblk hstmt
    let sym0 : SymState := {
      locals := locals
      loans := loans
      nextLoan := nextLoan
      hasActiveJoin := hasActiveJoin
      block := 1
      stmtIdx := 0
    }
    let locals1 := updateSymLocal locals 4 (some (.usize i))
    let sym1 : SymState := { sym0 with locals := locals1, stmtIdx := 1 }
    let locals2 := updateSymLocal (updateSymLocal locals1 4 none) 3 (some (.bool (decide (i < n))))
    let sym2 : SymState := { sym0 with locals := locals2, stmtIdx := 2 }
    have s1 : evalSymStep countUpBody sym0 = some (false, sym1) := by
      change (match evalSymStmt sym0 (.assign ⟨4⟩ (.use (.copy ⟨2⟩))) with
        | some sym' => some (false, sym')
        | none => none) = _
      dsimp [sym0, sym1, locals1, evalSymStmt, evalSymOperand]
      rw [h2]
    have s2 : evalSymStep countUpBody sym1 = some (false, sym2) := by
      have h1' : (updateSymLocal locals1 4 none) 1 = some (.usize n) := h1
      have h4 : locals1 4 = some (.usize i) := rfl
      change (match evalSymStmt sym1 (.assign ⟨3⟩ (.binaryOp .lt (.move ⟨4⟩) (.copy ⟨1⟩))) with
        | some sym' => some (false, sym')
        | none => none) = _
      dsimp [sym1, sym0, sym2, locals2, evalSymStmt, evalSymOperand]
      rw [h4]
      dsimp
      rw [h1']
      rfl
    have s3 : evalBranchStep countUpBody sym2 =
        some (decide (i < n),
          { sym0 with locals := countUpLocalsAfterBb1 locals i n, block := 5, stmtIdx := 0 },
          { sym0 with locals := countUpLocalsAfterBb1 locals i n, block := 2, stmtIdx := 0 }) :=
      rfl
    change evalSymState (.step (.step (.branch falsePlan truePlan))) countUpBody sym0 = _
    rw [evalSymState_step_of_some s1, evalSymState_step_of_some s2, evalSymState_branch_of_some s3]

theorem evalSymState_countUp_bb5 {i : Nat} {sym : SymState}
    (hblk : sym.block = 5)
    (hstmt : sym.stmtIdx = 0)
    (h2 : sym.locals 2 = some (.usize i)) :
    evalSymState (.step .ret) countUpBody sym = .ok (.usize i) := by
  cases sym with
  | mk locals loans nextLoan hasActiveJoin block stmtIdx =>
    dsimp at hblk hstmt h2
    subst hblk hstmt
    let sym0 : SymState := {
      locals := locals
      loans := loans
      nextLoan := nextLoan
      hasActiveJoin := hasActiveJoin
      block := 5
      stmtIdx := 0
    }
    let locals1 := updateSymLocal locals 0 (some (.usize i))
    let sym1 : SymState := { sym0 with locals := locals1, stmtIdx := 1 }
    have s1 : evalSymStep countUpBody sym0 = some (false, sym1) := by
      change (match evalSymStmt sym0 (.assign ⟨0⟩ (.use (.copy ⟨2⟩))) with
        | some sym' => some (false, sym')
        | none => none) = _
      dsimp [sym0, sym1, locals1, evalSymStmt, evalSymOperand]
      rw [h2]
    have s2 : evalReturn countUpBody sym1 = some (.usize i) := rfl
    change evalSymState (.step .ret) countUpBody sym0 = _
    rw [evalSymState_step_of_some s1, evalSymState_ret_of_some s2]

theorem evalSymState_countUp_bb2 {i : Nat} {sym : SymState}
    (hblk : sym.block = 2)
    (hstmt : sym.stmtIdx = 0)
    (h2 : sym.locals 2 = some (.usize i))
    (falsePlan truePlan : TransPlan) :
    evalSymState (.step (.step (.branch falsePlan truePlan))) countUpBody sym =
      if decide (i < 1000) then
        evalSymState truePlan countUpBody
          { sym with locals := countUpLocalsAfterBb2 sym.locals i, block := 3, stmtIdx := 0 }
      else
        evalSymState falsePlan countUpBody
          { sym with locals := countUpLocalsAfterBb2 sym.locals i, block := 5, stmtIdx := 0 } := by
  cases sym with
  | mk locals loans nextLoan hasActiveJoin block stmtIdx =>
    dsimp at hblk hstmt h2
    subst hblk hstmt
    let sym0 : SymState := {
      locals := locals
      loans := loans
      nextLoan := nextLoan
      hasActiveJoin := hasActiveJoin
      block := 2
      stmtIdx := 0
    }
    let locals1 := updateSymLocal locals 6 (some (.usize i))
    let sym1 : SymState := { sym0 with locals := locals1, stmtIdx := 1 }
    let locals2 := updateSymLocal (updateSymLocal locals1 6 none) 5 (some (.bool (decide (i < 1000))))
    let sym2 : SymState := { sym0 with locals := locals2, stmtIdx := 2 }
    have s1 : evalSymStep countUpBody sym0 = some (false, sym1) := by
      change (match evalSymStmt sym0 (.assign ⟨6⟩ (.use (.copy ⟨2⟩))) with
        | some sym' => some (false, sym')
        | none => none) = _
      dsimp [sym0, sym1, locals1, evalSymStmt, evalSymOperand]
      rw [h2]
    have s2 : evalSymStep countUpBody sym1 = some (false, sym2) := rfl
    have s3 : evalBranchStep countUpBody sym2 =
        some (decide (i < 1000),
          { sym0 with locals := countUpLocalsAfterBb2 locals i, block := 5, stmtIdx := 0 },
          { sym0 with locals := countUpLocalsAfterBb2 locals i, block := 3, stmtIdx := 0 }) :=
      rfl
    change evalSymState (.step (.step (.branch falsePlan truePlan))) countUpBody sym0 = _
    rw [evalSymState_step_of_some s1, evalSymState_step_of_some s2, evalSymState_branch_of_some s3]

theorem countUp_add_one_no_overflow {i : Nat} (hi : i < 1000) :
    decide (usizeMax < i + 1) = false := by
  apply decide_eq_false
  have h1000 : 1000 ≤ usizeMax := by decide
  exact Nat.not_lt.mpr (Nat.le_trans hi h1000)

theorem evalSymState_countUp_bb3_bb4 {i n : Nat} {sym : SymState}
    (hblk : sym.block = 3)
    (hstmt : sym.stmtIdx = 0)
    (h1 : sym.locals 1 = some (.usize n))
    (h2 : sym.locals 2 = some (.usize i))
    (hi : i < 1000)
    (restPlan : TransPlan) :
    ∃ sym',
      CountUpLoopInv (i + 1) n sym' ∧
      evalSymState (.step (.step (.step (.step restPlan)))) countUpBody sym =
        evalSymState restPlan countUpBody sym' := by
  cases sym with
  | mk locals loans nextLoan hasActiveJoin block stmtIdx =>
    dsimp at hblk hstmt h1 h2
    subst hblk hstmt
    have hov : decide (usizeMax < i + 1) = false := countUp_add_one_no_overflow hi
    let sym0 : SymState := {
      locals := locals
      loans := loans
      nextLoan := nextLoan
      hasActiveJoin := hasActiveJoin
      block := 3
      stmtIdx := 0
    }
    let locals1 := updateSymLocal locals 7 (some (.tupleUsizeBool (i + 1) false))
    let sym1 : SymState := { sym0 with locals := locals1, stmtIdx := 1 }
    let sym2 : SymState := { sym0 with locals := locals1, block := 4, stmtIdx := 0 }
    let locals2 := countUpLocalsAfterBb4 locals i
    let sym3 : SymState := { sym0 with locals := locals2, block := 4, stmtIdx := 1 }
    let sym4 : SymState := { sym0 with locals := locals2, block := 1, stmtIdx := 0 }
    have s1 : evalSymStep countUpBody sym0 = some (false, sym1) := by
      change (match evalSymStmt sym0 (.assign ⟨7⟩ (.checkedBinaryOp .add (.copy ⟨2⟩) (.constVal (.usize 1)))) with
        | some sym' => some (false, sym')
        | none => none) = _
      dsimp [sym0, sym1, locals1, evalSymStmt, evalSymOperand,
        evalSymConst, evalSymCheckedBinOp, updateSymLocal]
      rw [h2]
      dsimp [evalSymCheckedBinOp]
      rw [hov]
    have s2 : evalSymStep countUpBody sym1 = some (false, sym2) := rfl
    have s3 : evalSymStep countUpBody sym2 = some (false, sym3) := rfl
    have s4 : evalSymStep countUpBody sym3 = some (false, sym4) := rfl
    refine ⟨sym4, ⟨rfl, rfl, h1, rfl⟩, ?_⟩
    change evalSymState (.step (.step (.step (.step restPlan)))) countUpBody sym0 = _
    rw [evalSymState_step_of_some s1, evalSymState_step_of_some s2,
      evalSymState_step_of_some s3, evalSymState_step_of_some s4]

/-- Inductive loop invariant proof for `countUpLoopPlan`: from any symbolic
    state
    `sym` at `bb1` satisfying `CountUpLoopInv i n sym` with `i ≤ n`, `i ≤ 1000`,
    and `n - i ≤ k`, `evalSymState (countUpLoopPlan (k + 1)) countUpBody sym`
    evaluates to `.ok (.usize (if decide (n ≤ 1000) then n else 1000))`. -/
theorem evalSymState_countUpLoopPlan :
    ∀ (k i n : Nat) (sym : SymState),
      CountUpLoopInv i n sym →
      i ≤ n →
      i ≤ 1000 →
      n - i ≤ k →
      evalSymState (countUpLoopPlan (k + 1)) countUpBody sym =
        .ok (.usize (if decide (n ≤ 1000) then n else 1000))
  | k, i, n, sym, hInv, hi_le_n, hi_le_1000, hsub_le_k => by
    unfold countUpLoopPlan
    rw [evalSymState_countUp_bb1 hInv]
    cases h1 : decide (i < n) with
    | false =>
      dsimp
      have hge : n ≤ i := Nat.not_lt.mp (of_decide_eq_false h1)
      have hi_eq_n : i = n := Nat.le_antisymm hi_le_n hge
      subst hi_eq_n
      have hdec : decide (i ≤ 1000) = true := decide_eq_true hi_le_1000
      rw [hdec]
      dsimp
      exact evalSymState_countUp_bb5 rfl rfl hInv.local2
    | true =>
      dsimp
      have hilt : i < n := of_decide_eq_true h1
      let symBb2 : SymState := {
        sym with
        locals := countUpLocalsAfterBb1 sym.locals i n
        block := 2
        stmtIdx := 0
      }
      have h2_bb2 : symBb2.locals 2 = some (.usize i) := hInv.local2
      rw [evalSymState_countUp_bb2 (sym := symBb2) rfl rfl h2_bb2]
      cases h2 : decide (i < 1000) with
      | false =>
        dsimp
        have hge1000 : 1000 ≤ i := Nat.not_lt.mp (of_decide_eq_false h2)
        have hi_eq_1000 : i = 1000 := Nat.le_antisymm hi_le_1000 hge1000
        subst hi_eq_1000
        have hnot_le : decide (n ≤ 1000) = false :=
          decide_eq_false (Nat.not_le.mpr hilt)
        rw [hnot_le]
        dsimp
        exact evalSymState_countUp_bb5 rfl rfl hInv.local2
      | true =>
        dsimp
        have hi1000 : i < 1000 := of_decide_eq_true h2
        cases k with
        | zero =>
          have hpos : 0 < n - i := Nat.sub_pos_of_lt hilt
          exact False.elim (Nat.not_lt.mpr hsub_le_k hpos)
        | succ k' =>
          let symBb3 : SymState := {
            symBb2 with
            locals := countUpLocalsAfterBb2 symBb2.locals i
            block := 3
            stmtIdx := 0
          }
          have h1_bb3 : symBb3.locals 1 = some (.usize n) := hInv.local1
          have h2_bb3 : symBb3.locals 2 = some (.usize i) := hInv.local2
          have ⟨symNext, hInvNext, hStepEq⟩ :=
            evalSymState_countUp_bb3_bb4 (sym := symBb3) rfl rfl h1_bb3 h2_bb3 hi1000
              (countUpLoopPlan (k' + 1))
          rw [hStepEq]
          have hsub_le_k' : n - (i + 1) ≤ k' := by
            have hle : n ≤ (k' + 1) + i := Nat.le_add_of_sub_le hsub_le_k
            rw [Nat.add_right_comm k' 1 i] at hle
            exact Nat.sub_le_of_le_add hle
          exact evalSymState_countUpLoopPlan k' (i + 1) n symNext hInvNext
            hilt hi1000 hsub_le_k'

/-- `translatePureWith countUpSymPlan countUpBody [.usize n0]` evaluates to
    `.ok (.usize (if decide (n0 ≤ 1000) then n0 else 1000))` for all `n0 :
    Nat`. -/
theorem translatePureWith_countUp_eq (n0 : Nat) :
    translatePureWith countUpSymPlan countUpBody [.usize n0] =
      .ok (.usize (if decide (n0 ≤ 1000) then n0 else 1000)) := by
  unfold translatePureWith translatePure countUpSymPlan
  let sym0 := buildPureSymState [.usize n0]
  let sym1 : SymState := {
    sym0 with
    locals := updateSymLocal sym0.locals 2 (some (.usize 0))
    stmtIdx := 1
  }
  let sym2 : SymState := {
    sym0 with
    locals := updateSymLocal sym0.locals 2 (some (.usize 0))
    block := 1
    stmtIdx := 0
  }
  have s1 : evalSymStep countUpBody sym0 = some (false, sym1) := rfl
  have s2 : evalSymStep countUpBody sym1 = some (false, sym2) := rfl
  change evalSymState (.step (.step (countUpLoopPlan (n0 + 1)))) countUpBody sym0 = _
  rw [evalSymState_step_of_some s1, evalSymState_step_of_some s2]
  have hInv : CountUpLoopInv 0 n0 sym2 := ⟨rfl, rfl, rfl, rfl⟩
  exact evalSymState_countUpLoopPlan n0 0 n0 sym2 hInv
    (Nat.zero_le n0) (Nat.zero_le 1000)
    (by rw [Nat.sub_zero]; exact Nat.le_refl n0)

/-- Concrete `rfl` sanity checks on `translatePureWith countUpSymPlan
    countUpBody`. -/
theorem translatePureWith_countUp_zero :
    translatePureWith countUpSymPlan countUpBody [.usize 0] = .ok (.usize 0) :=
  rfl

theorem translatePureWith_countUp_five :
    translatePureWith countUpSymPlan countUpBody [.usize 5] = .ok (.usize 5) :=
  rfl

/-- Pure functional model of `count_up`. -/
def pureCountUp (n0 : Nat) : Nat :=
  if decide (n0 ≤ 1000) then n0 else 1000

/-- Non-trivial property 1 (**Upper bound**): `pureCountUp n0 ≤ 1000`. -/
theorem pureCountUp_le_1000 (n0 : Nat) :
    pureCountUp n0 ≤ 1000 := by
  unfold pureCountUp
  cases h : decide (n0 ≤ 1000) with
  | false => exact Nat.le_refl 1000
  | true => exact of_decide_eq_true h

/-- Non-trivial property 2 (**Contraction**): `pureCountUp n0 ≤ n0`. -/
theorem pureCountUp_le_self (n0 : Nat) :
    pureCountUp n0 ≤ n0 := by
  unfold pureCountUp
  cases h : decide (n0 ≤ 1000) with
  | false =>
    exact Nat.le_of_lt (Nat.not_le.mp (of_decide_eq_false h))
  | true =>
    exact Nat.le_refl n0

/-- Non-trivial property 3 (**Idempotence**): `pureCountUp (pureCountUp n0) =
    pureCountUp n0`. -/
theorem pureCountUp_idempotent (n0 : Nat) :
    pureCountUp (pureCountUp n0) = pureCountUp n0 := by
  have hle : pureCountUp n0 ≤ 1000 := pureCountUp_le_1000 n0
  unfold pureCountUp at hle; unfold pureCountUp
  have hdec : decide ((if decide (n0 ≤ 1000) then n0 else 1000) ≤ 1000) = true :=
    decide_eq_true hle
  rw [hdec]
  rfl

/-- Non-trivial property 4 (**Monotonicity**): `a ≤ b → pureCountUp a ≤
    pureCountUp b`. -/
theorem pureCountUp_mono {a b : Nat} (hab : a ≤ b) :
    pureCountUp a ≤ pureCountUp b := by
  unfold pureCountUp
  cases ha : decide (a ≤ 1000) <;> cases hb : decide (b ≤ 1000) <;> dsimp
  · exact Nat.le_refl 1000
  · exact Nat.le_trans (Nat.le_of_lt (Nat.not_le.mp (of_decide_eq_false ha))) hab
  · exact of_decide_eq_true ha
  · exact hab

/-- `evalSymWith countUpSymPlan countUpBody` refines `EnsuresCountUp` under
    `π_func`. -/
theorem countUp_func_refines_ensures :
    π_func (FuncLang.sem (evalSymWith countUpSymPlan countUpBody)) ≤ EnsuresCountUp := by
  intro q _
  have hSupp : allSupportedArgTys countUpBody.argTys = true := rfl
  refine ⟨?_, ?_⟩
  · unfold π_func FuncLang evalSymWith
    dsimp
    rw [hSupp]
    dsimp
    cases hExt : extractSymArgs countUpBody.argTys q.init with
    | none => intro h; cases h
    | some args =>
      dsimp
      unfold extractSymArgs at hExt
      cases hblk : (q.init.block == 0 && q.init.stmtIdx == 0) with
      | false => rw [hblk] at hExt; cases hExt
      | true =>
        rw [hblk] at hExt
        dsimp [countUpBody, extractSymArgsAux] at hExt
        cases h1 : q.init.locals 1 with
        | none => rw [h1] at hExt; cases hExt
        | some v1 =>
          rw [h1] at hExt
          cases v1 with
          | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ => cases hExt
          | usize n0 =>
            dsimp at hExt
            injection hExt with hargs
            subst hargs
            rw [translatePureWith_countUp_eq n0]
            intro h; cases h
  · intro out ⟨_, hOutProp⟩ ret n0 hout h1
    have hPost : evalSymWith countUpSymPlan countUpBody q.init = .ok ret := hOutProp ret hout
    unfold evalSymWith at hPost
    rw [hSupp] at hPost
    dsimp at hPost
    cases hExt : extractSymArgs countUpBody.argTys q.init with
    | none => rw [hExt] at hPost; cases hPost
    | some args =>
      rw [hExt] at hPost
      dsimp at hPost
      unfold extractSymArgs at hExt
      cases hblk : (q.init.block == 0 && q.init.stmtIdx == 0) with
      | false => rw [hblk] at hExt; cases hExt
      | true =>
        rw [hblk] at hExt
        dsimp [countUpBody, extractSymArgsAux] at hExt
        rw [h1] at hExt
        dsimp at hExt
        injection hExt with hargs
        subst hargs
        rw [translatePureWith_countUp_eq n0] at hPost
        injection hPost with hret
        exact hret.symm

/-- `countUpBody` satisfies `EnsuresCountUp`, proved by composing
    `evalSymWith_sound countUpSymPlan countUpBody` with
    `countUp_func_refines_ensures`. -/
theorem countUpBody_satisfies_ensures :
    MirLang.sem countUpBody ≤ EnsuresCountUp :=
  Preorder.le_trans
    (evalSymWith_sound countUpSymPlan countUpBody)
    countUp_func_refines_ensures

theorem ensuresCountUp_le_wellFormed :
    EnsuresCountUp ≤ MirLang.WellFormed :=
  fun _ h => ⟨h, fun _ _ => True.intro⟩

/-- `countUpBody` satisfies `MirLang.WellFormed`. -/
theorem countUpBody_satisfies_wellFormed :
    MirLang.sem countUpBody ≤ MirLang.WellFormed :=
  Preorder.le_trans countUpBody_satisfies_ensures ensuresCountUp_le_wellFormed

/-- End-to-end `CrateTheorem` witness for `count_up` with `EnsuresCountUp`. -/
theorem prove_count_up_ensures_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := countUpBody
        specs := [EnsuresCountUp]
      }]
      tcb := [.rustcLowering fnName countUpBody]
    } :=
  verify_single_fn_crate
    fnName
    countUpBody
    EnsuresCountUp
    countUpBody_satisfies_ensures
    ensuresCountUp_le_wellFormed

/-- End-to-end `CrateTheorem` witness for `count_up` with baseline
    `WellFormed`. -/
theorem prove_count_up_wf_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := countUpBody
        specs := []
      }]
      tcb := [.rustcLowering fnName countUpBody]
    } :=
  verify_single_fn_wf_crate fnName countUpBody countUpBody_satisfies_wellFormed

/-!
## 16. Interprocedural Calls and Multi-Function Crates (`double_bounded`)

In this section we verify interprocedural composition of crate-local functions:
```rust
pub fn add_bounded(x: usize, y: usize) -> usize {
    if x <= 1000 && y <= 1000 {
        x + y
    } else {
        0
    }
}

pub fn double_bounded(x: usize) -> usize {
    add_bounded(x, x)
}
```
1. **Callee Contract Adequacy (`evalPureCallee2_addBounded_eq_translatePure`,
   `evalPureCallee2_absDiff_eq_translatePure`)**:
   We prove that the operational summary `evalPureCallee2` for `.addBounded` and
   `.absDiff` agrees identically with the verified `translatePure` semantics of
   `addBoundedBody` and `absDiffBody`.
2. **Caller Verification (`doubleBoundedBody`)**:
   `translatePure (computePlan doubleBoundedBody) doubleBoundedBody [.usize x0]`
   evaluates by `rfl` to `.ok (.usize (if decide (x0 ≤ 1000) && decide (x0 ≤
   1000) then x0 + x0 else 0))`.
3. **Multi-Function `CrateTheorem` (`prove_add_and_double_bounded_crate`)**:
   We discharge `CrateTheorem` simultaneously over the two-function crate
   `[add_bounded, double_bounded]`.
-/

/-- Callee contract adequacy for `PureCallee2.addBounded`: `evalPureCallee2
    .addBounded`
    matches the verified functional translation `translatePure` of
    `addBoundedBody`. -/
theorem evalPureCallee2_addBounded_eq_translatePure (x0 y0 : Nat) :
    (evalPureCallee2 .addBounded (.usize x0) (.usize y0)).map AeneasRes.ok =
      some (translatePure (computePlan addBoundedBody) addBoundedBody [.usize x0, .usize y0]) := by
  rw [translatePure_addBounded_eq x0 y0]
  rfl

/-- Callee contract adequacy for `PureCallee2.absDiff`: `evalPureCallee2
    .absDiff`
    matches the verified functional translation `translatePure` of
    `absDiffBody`. -/
theorem evalPureCallee2_absDiff_eq_translatePure (x0 y0 : Nat) :
    (evalPureCallee2 .absDiff (.usize x0) (.usize y0)).map AeneasRes.ok =
      some (translatePure (computePlan absDiffBody) absDiffBody [.usize x0, .usize y0]) := by
  rw [translatePure_absDiff_eq x0 y0]
  rfl

/-- Exact `Runtime(PostCleanup)` MIR body emitted by `rustc --edition=2024
    --emit=mir`
    for:
    ```rust
    pub fn double_bounded(x: usize) -> usize {
        add_bounded(x, x)
    }
    ``` -/
def doubleBoundedBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := []
      terminator := .callPure2 ⟨0⟩ .addBounded (.copy ⟨1⟩) (.copy ⟨1⟩) ⟨1⟩ },
    { stmts := []
      terminator := .return_ }
  ]

/-- `translatePure` on `doubleBoundedBody` reduces by `rfl` to
    `.ok (.usize (if decide (x0 ≤ 1000) && decide (x0 ≤ 1000) then x0 + x0 else
    0))`. -/
theorem translatePure_doubleBounded_eq (x0 : Nat) :
    translatePure (computePlan doubleBoundedBody) doubleBoundedBody [.usize x0] =
      .ok (.usize (if decide (x0 ≤ 1000) && decide (x0 ≤ 1000) then x0 + x0 else 0)) :=
  rfl

/-- Pure functional model of `double_bounded`. -/
def pureDoubleBounded (x0 : Nat) : Nat :=
  if decide (x0 ≤ 1000) && decide (x0 ≤ 1000) then x0 + x0 else 0

/-- Non-trivial property 1 (**Doubling under bound**): when `x0 ≤ 1000`,
    `pureDoubleBounded x0 = 2 * x0`. -/
theorem pureDoubleBounded_eq_two_mul {x0 : Nat} (hx : x0 ≤ 1000) :
    pureDoubleBounded x0 = 2 * x0 := by
  unfold pureDoubleBounded
  have hdec : decide (x0 ≤ 1000) = true := decide_eq_true hx
  rw [hdec]
  dsimp
  exact (Nat.two_mul x0).symm

/-- Non-trivial property 2 (**Global upper bound**): `pureDoubleBounded x0 ≤
    2000`
    for all `x0 : Nat`. -/
theorem pureDoubleBounded_le_2000 (x0 : Nat) :
    pureDoubleBounded x0 ≤ 2000 := by
  unfold pureDoubleBounded
  cases hx : decide (x0 ≤ 1000) with
  | false =>
    dsimp
    exact Nat.zero_le 2000
  | true =>
    dsimp
    have hle : x0 ≤ 1000 := of_decide_eq_true hx
    exact Nat.add_le_add hle hle

/-- Non-trivial property 3 (**Parity**): `Nat.mod (pureDoubleBounded x0) 2 = 0` for all
    `x0 : Nat`. -/
theorem pureDoubleBounded_even (x0 : Nat) :
    Nat.mod (pureDoubleBounded x0) 2 = 0 := by
  unfold pureDoubleBounded
  cases hx : decide (x0 ≤ 1000) with
  | false =>
    dsimp
  | true =>
    dsimp
    rw [← Nat.two_mul x0]
    exact Nat.mul_mod_right 2 x0

/-- `translate doubleBoundedBody` refines `EnsuresDoubleBounded` under
    `π_func`. -/
theorem doubleBounded_func_refines_ensures :
    π_func (FuncLang.sem (translate doubleBoundedBody)) ≤ EnsuresDoubleBounded := by
  intro q _
  have hSupp : allSupportedArgTys doubleBoundedBody.argTys = true := rfl
  refine ⟨?_, ?_⟩
  · unfold π_func FuncLang translate evalSym
    dsimp
    rw [hSupp]
    dsimp
    cases hExt : extractSymArgs doubleBoundedBody.argTys q.init with
    | none => intro h; cases h
    | some args =>
      dsimp
      unfold extractSymArgs at hExt
      cases hblk : (q.init.block == 0 && q.init.stmtIdx == 0) with
      | false => rw [hblk] at hExt; cases hExt
      | true =>
        rw [hblk] at hExt
        dsimp [doubleBoundedBody, extractSymArgsAux] at hExt
        cases h1 : q.init.locals 1 with
        | none => rw [h1] at hExt; cases hExt
        | some v1 =>
          rw [h1] at hExt
          cases v1 with
          | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ => cases hExt
          | usize x0 =>
            dsimp at hExt
            injection hExt with hargs
            subst hargs
            rw [translatePure_doubleBounded_eq x0]
            intro h; cases h
  · intro out ⟨_, hOutProp⟩ ret x0 hout h1
    have hPost : translate doubleBoundedBody q.init = .ok ret := hOutProp ret hout
    unfold translate evalSym at hPost
    rw [hSupp] at hPost
    dsimp at hPost
    cases hExt : extractSymArgs doubleBoundedBody.argTys q.init with
    | none => rw [hExt] at hPost; cases hPost
    | some args =>
      rw [hExt] at hPost
      dsimp at hPost
      unfold extractSymArgs at hExt
      cases hblk : (q.init.block == 0 && q.init.stmtIdx == 0) with
      | false => rw [hblk] at hExt; cases hExt
      | true =>
        rw [hblk] at hExt
        dsimp [doubleBoundedBody, extractSymArgsAux] at hExt
        rw [h1] at hExt
        dsimp at hExt
        injection hExt with hargs
        subst hargs
        rw [translatePure_doubleBounded_eq x0] at hPost
        injection hPost with hret
        exact hret.symm

/-- `doubleBoundedBody` satisfies `EnsuresDoubleBounded`, proved by composing
    `translate_sound doubleBoundedBody` with
    `doubleBounded_func_refines_ensures`. -/
theorem doubleBoundedBody_satisfies_ensures :
    MirLang.sem doubleBoundedBody ≤ EnsuresDoubleBounded :=
  Preorder.le_trans
    (translate_sound doubleBoundedBody)
    doubleBounded_func_refines_ensures

theorem ensuresDoubleBounded_le_wellFormed :
    EnsuresDoubleBounded ≤ MirLang.WellFormed :=
  fun _ h => ⟨h, fun _ _ => True.intro⟩

/-- `doubleBoundedBody` satisfies `MirLang.WellFormed`. -/
theorem doubleBoundedBody_satisfies_wellFormed :
    MirLang.sem doubleBoundedBody ≤ MirLang.WellFormed :=
  Preorder.le_trans doubleBoundedBody_satisfies_ensures ensuresDoubleBounded_le_wellFormed

/-- End-to-end `CrateTheorem` witness for `double_bounded` with
    `EnsuresDoubleBounded`. -/
theorem prove_double_bounded_ensures_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := doubleBoundedBody
        specs := [EnsuresDoubleBounded]
      }]
      tcb := [.rustcLowering fnName doubleBoundedBody]
    } :=
  verify_single_fn_crate
    fnName
    doubleBoundedBody
    EnsuresDoubleBounded
    doubleBoundedBody_satisfies_ensures
    ensuresDoubleBounded_le_wellFormed

/-- End-to-end `CrateTheorem` witness for `double_bounded` with baseline
    `WellFormed`. -/
theorem prove_double_bounded_wf_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := doubleBoundedBody
        specs := []
      }]
      tcb := [.rustcLowering fnName doubleBoundedBody]
    } :=
  verify_single_fn_wf_crate fnName doubleBoundedBody doubleBoundedBody_satisfies_wellFormed

/-- Generic two-function `CrateTheorem` discharge for a crate containing two
    verified functions `(fnName1, body1, [spec1])` and `(fnName2, body2,
    [spec2])`. -/
theorem verify_two_fn_crate
    (fnName1 : String) (body1 : MirBody) (spec1 : MirLang.Behavior)
    (fnName2 : String) (body2 : MirBody) (spec2 : MirLang.Behavior)
    (h_proof1 : MirSem body1 ≤ spec1)
    (h_spec1_wf : spec1 ≤ MirLang.WellFormed)
    (h_proof2 : MirSem body2 ≤ spec2)
    (h_spec2_wf : spec2 ≤ MirLang.WellFormed) :
    CrateTheorem {
      functions := [
        { name := fnName1, prog := body1, specs := [spec1] },
        { name := fnName2, prog := body2, specs := [spec2] }
      ]
      tcb := [
        .rustcLowering fnName1 body1,
        .rustcLowering fnName2 body2
      ]
    } := by
  refine ⟨(by intro h; cases h), ⟨⟨⟨True.intro, True.intro, True.intro⟩, ?_⟩, ⟨⟨True.intro, True.intro, True.intro⟩, ?_⟩, True.intro⟩⟩
  · intro hAssumptions
    exact Compiler.Verified.with_wellFormedOn
      (Compiler.SoundOn.verify hAssumptions.1 h_proof1)
      h_spec1_wf hAssumptions.1.1
  · intro hAssumptions
    exact Compiler.Verified.with_wellFormedOn
      (Compiler.SoundOn.verify hAssumptions.2.1 h_proof2)
      h_spec2_wf hAssumptions.2.1.1

/-- Multi-function `CrateTheorem` witness verifying both `add_bounded` and
    `double_bounded` in a single crate. -/
theorem prove_add_and_double_bounded_crate (fnAdd fnDouble : String) :
    CrateTheorem {
      functions := [
        { name := fnAdd, prog := addBoundedBody, specs := [EnsuresAddBounded] },
        { name := fnDouble, prog := doubleBoundedBody, specs := [EnsuresDoubleBounded] }
      ]
      tcb := [
        .rustcLowering fnAdd addBoundedBody,
        .rustcLowering fnDouble doubleBoundedBody
      ]
    } :=
  verify_two_fn_crate
    fnAdd addBoundedBody EnsuresAddBounded
    fnDouble doubleBoundedBody EnsuresDoubleBounded
    addBoundedBody_satisfies_ensures ensuresAddBounded_le_wellFormed
    doubleBoundedBody_satisfies_ensures ensuresDoubleBounded_le_wellFormed


end Anneal.FunctionalTranslation
