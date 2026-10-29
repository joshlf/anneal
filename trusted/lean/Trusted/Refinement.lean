-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra

/-!
# Layer 1A: Refinement Preorder, Partial Behaviors, and Verification Envelope

Anneal models program behaviors and specifications using a single refinement
preorder (`b₁ ≤ b₂`, read "`b₁` refines `b₂`" or "`b₁` permits no more
behaviors than `b₂`"). This module defines that preorder, the `Partial` type
constructor that distinguishes defined behavior from Undefined Behavior (UB),
the carriers for languages and compilers, and the top-level verification
envelope.

## 1. Set Inclusion, Compilation, and Verification

Let `Out` be the universe of observable outcomes for a single query `q : Query`
(such as an initial state, input argument, or finite step budget). When a
program's execution at `q` is well-defined, its behavior at `q` is a subset of
`Out` (`Out → Prop`): the set of outcomes that the program may produce on `q`.

A specification at `q` is also a subset of `Out` (`Out → Prop`), defining which
outcomes are acceptable. Under subset inclusion (`P ≤ Q ↔ ∀ o, P o → Q o`),
"program `b` satisfies `spec`" is simply `b ≤ spec`.

Representing both behaviors and specifications in the same preorder motivates
the two pass relations that Anneal supports: *compilation* (refinement) and
*verification* (abstraction). Compilation shrinks the set of allowed program
behaviors, while verification expands it:

- **Compilation (`Compiles`):** If `spec` holds of a source program `s`, then
  `spec` must also hold of the compiled target program `t`. Compilation may
  shrink the set of possible outcomes (for example, by resolving compiler or
  allocator nondeterminism), but may never add outcomes outside `s`. When the
  source and target languages have different query and outcome universes, a
  monotone mapping `π_c : L_src.Behavior → L_tgt.Behavior` maps source
  behaviors to the target behaviors that validly realize them. Sound compilation
  is then `L_tgt.sem t ≤ π_c (L_src.sem s)`.
- **Verification (`Abstracts`):** When a verifier translates a source program
  `s` into an abstract representation `v` to analyze it, every behavior
  possible in `s` must be covered by the verifier's model `v`:
  `L_src.sem s ≤ π_v (L_v.sem v)` for a monotone mapping
  `π_v : L_v.Behavior → L_src.Behavior`. Any specification `spec` proven of `v`
  (`L_v.sem v ≤ spec`) then transfers to `s` (`L_src.sem s ≤ π_v spec`) and
  down to the compiled target `t`:

    `L_tgt.sem t ≤ π_c (L_src.sem s) ≤ π_c (π_v (L_v.sem v)) ≤ π_c (π_v spec)`

## 2. Why `Partial` Internalizes Undefined Behavior

A subset `Out → Prop` alone cannot distinguish a program that is well-defined at
query `q` (producing outcomes in some set `S ⊆ Out`) from a program that
exhibits Undefined Behavior (UB) at `q`. If UB were modeled merely as the full
subset `fun _ => True`, it would be indistinguishable from a well-defined
program that may nondeterministically return any outcome in `Out`.

Instead, at each query `q : L.Query`, a program's behavior is an element of
`Partial (L.Out → Prop)`, where:

```lean
structure Partial (B : Type u) where
  defined : Prop
  val : defined → B
```

Constructively and without requiring `Classical.choice`, `Partial B` represents
the lifted domain $B \cup \{\mathsf{UB}\}$:
- When `defined` holds (`True`), `val` carries a well-defined value in `B`.
- When `defined` is `False`, the function type `False → B` has a unique
  inhabitant (`False.elim`), representing the single top element
  `Partial.ub` ($\mathsf{UB}$).

We order `Partial B` by:

  `p₁ ≤ p₂  ↔  ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂`

Together with implication on `Prop` (`instPreorderProp`, `P ≤ Q ↔ P → Q`) and
pointwise lifting on functions (`instPreorderFun`, `f ≤ g ↔ ∀ a, f a ≤ g a`),
this induces a `Preorder` on
`Behavior Query Out := Query → Partial (Out → Prop)`.

## 3. How Core Concepts Fall Out Automatically

From the single definition of `≤` on `L.Query → Partial (L.Out → Prop)`, five
properties fall out without extra axioms or guarded-refinement wrappers:

1. **UB is the top element (`Partial.ub`):** Because `Partial.ub.defined` is
   `False`, `p ≤ Partial.ub` holds vacuously for every `p : Partial B`.
   Conversely, `Partial.ub` cannot refine any `p` with `p.defined` (`True`).
2. **Specifications and well-formedness (`L.SpecOn`, `L.Spec`,
   `L.WellFormedOn`, and `L.WellFormed`):** `L.SpecOn pre post` constructs a
   query-indexed specification requiring definedness on `pre q`
   (`defined := pre q`) and restricting outcomes to `post q`
   (`val := fun _ => post q`). All standard specification shapes specialize
   `L.SpecOn`:
   - `L.Spec post` (`L.SpecOn (fun _ => True) post`) requires definedness and
     `post q` at every query `q` (definitionally equal to
     `fun q => Partial.pure (post q)`).
   - `L.WellFormedOn pre` (`L.SpecOn pre (fun _ _ => True)`) requires UB-freedom
     on all queries satisfying `pre` while permitting any outcome (`L.sem s ≤
     L.WellFormedOn pre` unfolds to `∀ q, pre q → (L.sem s q).defined`).
   - `L.WellFormed` (`L.WellFormedOn (fun _ => True)`) sits immediately below
     `Partial.ub` at every query `q` and unfolds `L.sem s ≤ L.WellFormed`
     directly to `∀ q, (L.sem s q).defined`—unconditional UB-freedom.
3. **Unconditional compiler correctness (`Compiles`):**
   `Compiles L_src L_tgt π_c s t` is simply `L_tgt.sem t ≤ π_c (L_src.sem s)`.
   Pointwise at each target query `q`:
   - If `(π_c (L_src.sem s) q).defined` holds, `t` must also be defined at `q`
     and its outcomes must be a subset of `(π_c (L_src.sem s) q).val`.
   - If `(π_c (L_src.sem s) q).defined` is `False` (the source exhibits UB on
     `q`), the implication `False → ...` holds vacuously, leaving `t`
     unconstrained on `q`.
   No external `wf` guard is needed on `Compiles` or `Compiler`. Consequently,
   an `unsafe fn` that exhibits UB on invalid inputs is still compiled by the
   exact same `Compiles` relation and preserves behavior on every valid input
   satisfying its safety precondition.
4. **Backward UB-reflection in verification (`Abstracts`):**
   `Abstracts L_v L_src π_v v s` is `L_src.sem s ≤ π_v (L_v.sem v)`. At every
   query `q` where the verifier model `v` is proven defined
   (`(π_v (L_v.sem v) q).defined`), `s ≤ π_v(v)` forces
   `(L_src.sem s q).defined` to hold as well—reflecting UB-freedom from `v` back
   to the source program `s`—while allowing `v` to fail more often than `s` (for
   example, when `v` adds conservative overflow or aliasing checks that trigger
   `defined = False`).
5. **Pass composition is plain transitivity (`pass_trans`):** Because `Compiles`
   and `Abstracts` are plain inequalities `≤`, composing multi-stage compiler or
   verifier pipelines requires only `Preorder.le_trans` and `Monotone`.

## 4. Verification Guarantees and Explicit Trust (`PRINCIPLES.md`)

This structure directly realizes the verification guarantees and trust rules in
`PRINCIPLES.md`:

- **Separating safety preconditions (`pre`) from functional requirements
  (`specs`) and library conditionality:**
  Consider a safe Rust function
  `fn binary_search<T: Ord>(slice: &[T], target: &T) -> Option<usize>`.
  Its functional correctness requires `slice` to be sorted, but because
  `binary_search` is a safe function, it must never exhibit UB—even when called
  with an unsorted slice. `VerificationResultOn` enforces this separation
  structurally by requiring `C.Verified prog` on every element of the non-empty
  specification list `L_src.WellFormedOn pre :: specs`:
  - **Baseline safety for binaries and libraries (`L_src.WellFormedOn pre` and
    `L_src.WellFormed`):**
    The head obligation `C.Verified prog (L_src.WellFormedOn pre)` governs when
    the program is required to be free of UB in both source and compiled target:
    - For a **binary (whole program)**, `pre` captures any declared input and
      environmental conditions on the outside world (`L_src.WellFormed` when all
      valid initial environments are already scoped by `L_src.Query` or
      `L_src.sem`).
    - For a **library API**, `pre` captures the permitted calling context: for a
      safe API whose type- and invariant-valid inputs are scoped by
      `L_src.Query` or `L_src.sem`, `pre` is `fun _ => True`
      (`L_src.WellFormed`, `VerificationResult`); when type/library invariants
      or an `unsafe` API's explicit `# Safety` preconditions are stated as a
      predicate `safety(q)`, `pre` is `safety`, requiring UB-freedom on all
      queries satisfying `safety(q)`.
  - **Additional functional guarantees (`specs`):** Each `spec ∈ specs` states
    an additional guarantee `C.Verified prog spec`. Functional preconditions
    (`requires`) can be encoded inside `(spec q).val` via `L.SpecOn pre` /
    `L.Spec`
    (`defined := pre q`, `val := fun _ out => sorted q → correct q out`)
    or in `(spec q).defined` via `L.SpecOn sorted` (`defined := sorted q`,
    `val := fun _ out => correct q out`, which evaluates to `Partial.ub` when
    `¬ sorted q`). Because `L_src.WellFormedOn pre` is always proved alongside
    `specs`, even an unsatisfiable functional precondition (such as
    `x > 0 && x < 0`, where `spec = fun _ => Partial.ub`) only makes that
    additional guarantee vacuously true (`ub_top`) and can never weaken the
    baseline `C.Verified prog (L_src.WellFormedOn pre)` obligation.
- **Verifying both source MIR and compiled target:**
  `Compiler.Verified C s spec` requires `L_src.sem s ≤ spec`,
  `Compiles L_src L_tgt C.π s (C.compile s)`, and
  `L_tgt.sem (C.compile s) ≤ C.π spec`. Applied to
  `L_src.WellFormedOn pre :: specs`, this ensures both source MIR and compiled
  machine code satisfy baseline UB-freedom (`L_src.WellFormedOn pre`) and every
  claimed `spec ∈ specs`, preventing a benign target binary from masking demonic
  UB in the source program.
- **Explicit, policy-gated TCB accounting (`PRINCIPLES.md`):**
  `VerificationResultOn` pairs `AllHold (assumptions.map policy.isAllowed)` with
  the implication `AllHold (assumptions.map TrustedAssumption.meaning) →
  AllHold ((L_src.WellFormedOn pre :: specs).map (C.Verified prog))`, so every
  compiler or user assumption is audited against `TrustPolicy` in the theorem
  statement itself.

This module belongs to `trusted/lean/` and contains only definitions, classes,
structures, inductives, and instances (zero theorems). All derived lemmas and
composition theorems (`pass_trans`, `Compiles.comp`, `Abstracts.comp`,
`Compiler.SoundOn.verify`, `verify_through_passes`, `Compiler.Verified.mono`,
and `Compiler.Verified.with_wellFormedOn`) live in
`theory/Anneal/Refinement.lean`.
-/

namespace Trusted

/-- Declaration macro that strips Anneal's in-place trust-tier attributes
    (`@[vetted]` and `@[candidate <feature>]`) from top-level declarations and
    `inductive` constructors after `trusted/audit/TrustedBoundary.lean`
    validates and records them during `preflight`. -/
@[macro Lean.Parser.Command.declaration, macro Lean.Parser.Command.mutual]
def expandTrustDeclaration : Lean.Macro := fun stx =>
  let emptyArr : Array Lean.Syntax := Array.mk List.nil
  let setArg (s : Lean.Syntax) (i : Nat) (v : Lean.Syntax) : Lean.Syntax :=
    match s, i with
    | .node info k (.mk (_ :: r)), 0 => .node info k (.mk (v :: r))
    | .node info k (.mk (a :: _ :: r)), 1 => .node info k (.mk (a :: v :: r))
    | .node info k (.mk (a :: b :: _ :: r)), 2 => .node info k (.mk (a :: b :: v :: r))
    | .node info k (.mk (a :: b :: c :: d :: _ :: r)), 4 => .node info k (.mk (a :: b :: c :: d :: v :: r))
    | other, _ => other
  let stripAttrs (mods : Lean.Syntax) : Bool × Lean.Syntax :=
    let attrsNode := mods.getArg 1
    match attrsNode.getArgs.toList with
    | .nil => (false, mods)
    | inner :: _ =>
      let (changed, kept) := List.foldl (fun (chg, acc) elem =>
        if elem.getKind == `Lean.Parser.Term.attrInstance then
          let attr := elem.getArg 1
          if attr.getKind == `Lean.Parser.Attr.simple &&
              ((attr.getArg 0).getId == `vetted || (attr.getArg 0).getId == `candidate) then
            (true, acc)
          else (chg, acc.push elem)
        else (chg, acc)) (false, emptyArr) (inner.getArg 1).getArgs.toList
      if !changed then (false, mods) else
        match kept.toList with
        | .nil => (true, setArg mods 1 (.node .none `null emptyArr))
        | first :: rest =>
          let sep := List.foldl (fun acc e => (acc.push (.atom .none ",")).push e) (emptyArr.push first) rest
          (true, setArg mods 1 (setArg attrsNode 0 (setArg inner 1 (.node .none `null sep))))
  let stripDecl (s : Lean.Syntax) : Bool × Lean.Syntax :=
    if s.getKind != `Lean.Parser.Command.declaration then (false, s) else
      let (mc, mods') := stripAttrs (s.getArg 0)
      let decl := s.getArg 1
      let (dc, decl') :=
        if decl.getKind != `Lean.Parser.Command.inductive then (false, decl) else
          let (cc, ctors') := List.foldl (fun (c, acc) ctor =>
            let (kc, m') := stripAttrs (ctor.getArg 2)
            (c || kc, acc.push (if kc then setArg ctor 2 m' else ctor))) (false, emptyArr) (decl.getArg 4).getArgs.toList
          (cc, if cc then setArg decl 4 (.node .none `null ctors') else decl)
      (mc || dc, if mc || dc then setArg (setArg s 0 mods') 1 decl' else s)
  if stx.getKind == `Lean.Parser.Command.mutual then
    let (mc, items') := List.foldl (fun (c, acc) item =>
      let (ic, item') := stripDecl item
      (c || ic, acc.push item')) (false, emptyArr) (stx.getArg 1).getArgs.toList
    if mc then pure (setArg stx 1 (.node .none `null items')) else Lean.Macro.throwUnsupported
  else
    let (c, stx') := stripDecl stx
    if c then pure stx' else Lean.Macro.throwUnsupported

/-- Identity marker used inside a `@[vetted]` declaration's body to guard a
    match arm that evaluates a `@[candidate <feature>]` constructor.
    `trusted/audit/TrustedBoundary.lean` recognizes `Trusted.candidate "<feat>"`
    applications in the compiled `.olean` expression tree so that a `@[vetted]`
    function can pattern-match on a `@[vetted]` inductive with
    `@[candidate <feat>]` constructors without contaminating crates that do not
    use `<feat>`. -/
@[vetted, reducible]
def candidate (_feat : String) {α : Sort u} (x : α) : α := x

/-- A reflexive and transitive refinement relation (`b₁ ≤ b₂`). -/
@[candidate refinement]
class Preorder (B : Type u) extends LE B where
  le_refl : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

/-- Implication (`P → Q`) equips `Prop` with a refinement preorder in which
    stronger propositions refine weaker ones. -/
@[candidate refinement]
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
@[candidate refinement]
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
@[candidate refinement]
structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

/-- Embed a unconditionally defined value `b : B` into `Partial B`
    (`defined := True`). -/
@[candidate refinement]
def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

/-- The undefined element ($\mathsf{UB}$) of `Partial B` (`defined := False`),
    which acts as the top element under `instPreorderPartial`. -/
@[candidate refinement]
def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

/-- Map a function `f : B₁ → B₂` over the defined payload of a `Partial B₁`,
    preserving `.defined`. -/
@[candidate refinement]
def Partial.map {B₁ : Type u} {B₂ : Type v} (f : B₁ → B₂) (p : Partial B₁) :
    Partial B₂ where
  defined := p.defined
  val h := f (p.val h)

/-- Refinement preorder on `Partial B`: `p₁ ≤ p₂` holds when, whenever `p₂` is
    defined (`h₂ : p₂.defined`), `p₁` is also defined (`h₁ : p₁.defined`) and
    its value refines `p₂`'s value (`p₁.val h₁ ≤ p₂.val h₂`).

    When `p₂` is undefined (`p₂.defined = False`), `p₁ ≤ p₂` holds vacuously,
    making `Partial.ub` the top element of `Partial B`. -/
@[candidate refinement]
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
@[candidate refinement]
def Monotone {B₁ : Type u} {B₂ : Type v} [Preorder B₁] [Preorder B₂]
    (π : B₁ → B₂) : Prop :=
  ∀ ⦃x y : B₁⦄, x ≤ y → π x ≤ π y

/-- The canonical domain of query-indexed partial behaviors over `Query` and
    `Out` (`Query → Partial (Out → Prop)`), ordered pointwise by
    `instPreorderFun`, `instPreorderPartial`, and `instPreorderProp`. -/
@[candidate refinement]
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- A language bundling a program type `Prog`, a query domain `Query` (such as
    initial states, inputs, step budgets, or external trace prefixes), an
    outcome domain `Out`, and a semantic function
    `sem : Prog → Behavior Query Out`. -/
@[candidate refinement]
structure Language where
  Prog : Type
  Query : Type
  Out : Type
  sem : Prog → Behavior Query Out

/-- The behavior domain of a `Language` (`Behavior L.Query L.Out`). -/
@[candidate refinement]
abbrev Language.Behavior (L : Language) : Type :=
  Trusted.Behavior L.Query L.Out

/-- Query-indexed specification on `L` with domain precondition
    `pre : L.Query → Prop` and outcome postcondition
    `post : L.Query → L.Out → Prop`: requires the program to be defined at
    every query `q` satisfying `pre q` (`defined := pre q`) and restricts its
    outcomes at `q` to `post q` (`val := fun _ => post q`).

    By `instPreorderPartial`, `b ≤ L.SpecOn pre post` unfolds to
    `∀ q, pre q → ∃ h : (b q).defined, ∀ out, (b q).val h out → post q out`.
    Outside `pre` (`¬ pre q`), `(L.SpecOn pre post q).defined` is `False`
    (`Partial.ub`), leaving `b q` unconstrained. -/
@[candidate refinement]
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
@[candidate refinement]
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
@[candidate refinement]
abbrev Language.WellFormedOn (L : Language) (pre : L.Query → Prop) : L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

/-- Unconditional well-formedness specification on `L`
    (`L.WellFormedOn (fun _ => True)`): requires the program to be defined at
    every query `q : L.Query` (`∀ q, (L.sem s q).defined`). Used as the
    mandatory baseline UB-freedom obligation for binaries and safe library APIs
    whose valid initial states or caller inputs are already scoped by `L.Query`
    or `L.sem`. -/
@[candidate refinement]
abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

/-- Compilation (refinement) pass from `L_src` to `L_tgt`: target program `t`
    refines the mapped source behavior `π_c (L_src.sem s)`.

    Because `L_tgt.Behavior` is ordered by `instPreorderPartial`, this single
    inequality enforces that at every target query `q` where
    `π_c (L_src.sem s)` is defined, `t` is also defined and its outcomes refine
    `s`'s outcomes, while leaving `t` unconstrained at queries where `s`
    exhibits UB (`defined = False`). -/
@[candidate refinement]
abbrev Compiles (L_src L_tgt : Language)
    (π_c : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ π_c (L_src.sem s)

/-- Verification (abstraction) pass from `L_src` to verifier language `L_v`:
    source program `s` refines the mapped verifier behavior `π_v (L_v.sem v)`.

    At every source query `q` where `π_v (L_v.sem v)` is defined, `s` is forced
    to be defined (reflecting UB-freedom backwards from `v` to `s`) and its
    outcomes are covered by `v`'s outcomes. -/
@[candidate refinement]
abbrev Abstracts (L_v L_src : Language)
    (π_v : L_v.Behavior → L_src.Behavior)
    (v : L_v.Prog) (s : L_src.Prog) : Prop :=
  L_src.sem s ≤ π_v (L_v.sem v)

/-- A compiler lowering programs from `L_src` to `L_tgt` with behavior mapping
    `π : L_src.Behavior → L_tgt.Behavior`. -/
@[candidate refinement]
structure Compiler (L_src L_tgt : Language) where
  compile : L_src.Prog → L_tgt.Prog
  π : L_src.Behavior → L_tgt.Behavior

/-- Soundness of compiler `C` on an individual source program `s`: `C.π` is
    monotone and `s` compiles to `C.compile s`
    (`Compiles L_src L_tgt C.π s (C.compile s)`). -/
@[candidate refinement]
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
@[candidate refinement]
def Compiler.Verified {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) (spec : L_src.Behavior) : Prop :=
  L_src.sem s ≤ spec ∧
  Compiles L_src L_tgt C.π s (C.compile s) ∧
  L_tgt.sem (C.compile s) ≤ C.π spec

/-- An assumption recorded in a verification unit's Trusted Computing Base,
    equipped with its intrinsic semantic meaning as a `Prop`. -/
@[candidate refinement]
class TrustedAssumption (A : Type) where
  meaning : A → Prop

/-- A policy governing which trusted assumptions of type `A` are permitted. -/
@[candidate refinement]
structure TrustPolicy (A : Type) [TrustedAssumption A] where
  isAllowed : A → Prop

/-- Conjunction of a list of propositions. -/
@[candidate refinement]
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
@[candidate refinement]
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
@[candidate refinement]
abbrev VerificationResult
    {L_src L_tgt : Language}
    {A : Type} [TrustedAssumption A]
    (C : Compiler L_src L_tgt)
    (policy : TrustPolicy A)
    (assumptions : List A)
    (prog : L_src.Prog)
    (specs : List L_src.Behavior := []) : Prop :=
  VerificationResultOn C policy assumptions prog (fun _ => True) specs

end Trusted
