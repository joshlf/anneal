namespace Trusted.Refinement

/-!
Language-agnostic refinement and specification primitives for Layer 1A of
Anneal's Y-diagram architecture (`#100` §3, `#103`).

Rather than defining a bespoke preorder hierarchy, Layer 1A builds directly on
Lean's standard order typeclasses (`LE`, `Std.IsPreorder`, `Std.IsPartialOrder`,
and `Trans` for `calc` chains):

- `b_low ≤ b_high` means `b_low` refines `b_high`: every behavior admitted by
  `b_low` is permitted by `b_high`.
- `Prop` is ordered by logical implication (`P ≤ Q := P → Q`), `A → B` is
  ordered pointwise, and `BehaviorSet α := α → Prop` inherits subset inclusion
  and `Std.IsPartialOrder` automatically.
- `Partial B` adjoins an undefined top element `Partial.ub` (`defined := False`)
  under Smyth refinement (`p₁ ≤ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined,
  p₁.val h₁ ≤ p₂.val h₂`), inheriting both `Std.IsPreorder` and
  `Std.IsPartialOrder`.
-/

/-- Enable native `calc` chains on every `Std.IsPreorder`. -/
instance instTransLE {α : Type u} [LE α] [Std.IsPreorder α] :
    Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·) where
  trans h₁ h₂ := Std.le_trans h₁ h₂

/-- Logical implication orders `Prop` so stronger assertions refine weaker ones. -/
instance instLEProp : LE Prop where
  le P Q := P → Q

instance instIsPartialOrderProp : Std.IsPartialOrder Prop where
  le_refl _ h := h
  le_trans _ _ _ h₁ h₂ hp := h₂ (h₁ hp)
  le_antisymm _ _ h₁ h₂ := propext ⟨h₁, h₂⟩

/-- Pointwise refinement on function spaces `A → B`. -/
instance instLEFun {A : Type u} {B : Type v} [LE B] : LE (A → B) where
  le f g := ∀ a, f a ≤ g a

instance instIsPreorderFun {A : Type u} {B : Type v}
    [LE B] [Std.IsPreorder B] : Std.IsPreorder (A → B) where
  le_refl f a := Std.le_refl (f a)
  le_trans _ _ _ h₁ h₂ a := Std.le_trans (h₁ a) (h₂ a)

instance instIsPartialOrderFun {A : Type u} {B : Type v}
    [LE B] [Std.IsPartialOrder B] : Std.IsPartialOrder (A → B) where
  le_antisymm _ _ h₁ h₂ := funext fun a => Std.le_antisymm (h₁ a) (h₂ a)

/-- Map each program representation in `Prog` to its behavior in `Behavior`. -/
abbrev Semantics (Prog : Type u) (Behavior : Type v) : Type (max u v) :=
  Prog → Behavior

/--
A downward-closed specification over a preordered behavior domain `Behavior`.

Whenever `b_low ≤ b_high` and `holds b_high`, `holds b_low` must also hold.
This single closure law unifies safety (UB-freedom), functional postconditions,
and k-safety hyperproperties.
-/
structure Spec (Behavior : Type u) [LE Behavior] : Type u where
  /-- Predicate selecting behaviors that satisfy the specification. -/
  holds : Behavior → Prop
  /-- Refinement preserves specification satisfaction downward. -/
  downward_closed : ∀ ⦃b_low b_high : Behavior⦄,
    b_low ≤ b_high → holds b_high → holds b_low

/-- An observation map `π` is monotone when it preserves `≤`. -/
def Monotone {BehHigh : Type u} {BehLow : Type v}
    [LE BehHigh] [LE BehLow] (π : BehHigh → BehLow) : Prop :=
  ∀ ⦃b₁ b₂ : BehHigh⦄, b₁ ≤ b₂ → π b₁ ≤ π b₂

/-- Pull a specification back along a monotone observation map `π`. -/
def Spec.pullback {BehHigh : Type u} {BehLow : Type v}
    [LE BehHigh] [LE BehLow]
    {π : BehHigh → BehLow} (h_mono : Monotone π)
    (S : Spec BehLow) : Spec BehHigh where
  holds b_high := S.holds (π b_high)
  downward_closed _ _ h_ref h_holds := S.downward_closed (h_mono h_ref) h_holds

/--
Guarded cross-domain refinement: once `G.holds b_high` is established, `b_low`
refines `π b_high` in `BehLow`.
-/
def GuardedRefines {BehLow : Type u} {BehHigh : Type v}
    [LE BehLow] [LE BehHigh]
    (G : Spec BehHigh) (π : BehHigh → BehLow)
    (b_low : BehLow) (b_high : BehHigh) : Prop :=
  G.holds b_high → b_low ≤ π b_high

/--
A set of execution elements represented as a predicate `α → Prop`.

Inherits subset refinement (`b_low ≤ b_high ↔ ∀ a, b_low a → b_high a`),
`Std.IsPreorder`, and `Std.IsPartialOrder` automatically from `Prop` and `→`.
-/
abbrev BehaviorSet (α : Type u) : Type u := α → Prop

/-- Direct image of a behavior set under `f`. -/
def BehaviorSet.map {α : Type u} {β : Type v}
    (f : α → β) (b : BehaviorSet α) : BehaviorSet β :=
  fun y => ∃ x, b x ∧ f x = y

/-- Universal single-execution safety/postcondition specification. -/
def BehaviorSet.allSpec {α : Type u} (P : α → Prop) : Spec (BehaviorSet α) where
  holds b := ∀ ⦃x : α⦄, b x → P x
  downward_closed _ _ h_ref h_high x hx := h_high (h_ref x hx)

/-- Specification forbidding executions satisfying `isBad`. -/
def BehaviorSet.forbidSpec {α : Type u} (isBad : α → Prop) :
    Spec (BehaviorSet α) :=
  BehaviorSet.allSpec (fun x => ¬ isBad x)

/-- Relational 2-safety hyperproperty specification (e.g., constant-time). -/
def BehaviorSet.twoSafetySpec {α : Type u} (R : α → α → Prop) :
    Spec (BehaviorSet α) where
  holds b := ∀ ⦃x₁ x₂ : α⦄, b x₁ → b x₂ → R x₁ x₂
  downward_closed _ _ h_ref h_high _ _ hx₁ hx₂ :=
    h_high (h_ref _ hx₁) (h_ref _ hx₂)

/--
Constructive partial value $B \cup \{\mathsf{UB}\}$:
- `defined : Prop` records absence of undefined behavior;
- `val : defined → B` extracts the underlying behavior when defined.
-/
structure Partial (B : Type u) : Type u where
  /-- Whether the execution is free of undefined behavior. -/
  defined : Prop
  /-- Underlying behavior when `defined` holds. -/
  val : defined → B

@[ext]
theorem Partial.ext {B : Type u} {p₁ p₂ : Partial B}
    (h_def : p₁.defined ↔ p₂.defined)
    (h_val : ∀ (h₁ : p₁.defined) (h₂ : p₂.defined), p₁.val h₁ = p₂.val h₂) :
    p₁ = p₂ := by
  cases p₁ with | mk d₁ v₁ =>
  cases p₂ with | mk d₂ v₂ =>
  have hd : d₁ = d₂ := propext h_def
  subst hd
  congr
  funext h
  exact h_val h h

/-- Embed an unconditionally defined behavior (`defined := True`). -/
def Partial.pure {B : Type u} (b : B) : Partial B :=
  ⟨True, fun _ => b⟩

/-- Undefined behavior top element (`defined := False`). -/
def Partial.ub {B : Type u} : Partial B :=
  ⟨False, False.elim⟩

/-- Map `f` over the defined payload of `Partial B₁`, preserving `.defined`. -/
def Partial.map {B₁ : Type u} {B₂ : Type v} (f : B₁ → B₂) (p : Partial B₁) :
    Partial B₂ where
  defined := p.defined
  val h := f (p.val h)

/--
Smyth refinement on `Partial B`: whenever `p₂` is defined, `p₁` is also defined
and `p₁.val ≤ p₂.val`. `Partial.ub` is the top element `⊤`.
-/
instance instLEPartial {B : Type u} [LE B] : LE (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂

instance instIsPreorderPartial {B : Type u} [LE B] [Std.IsPreorder B] :
    Std.IsPreorder (Partial B) where
  le_refl p h := ⟨h, Std.le_refl (p.val h)⟩
  le_trans _ _ _ h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Std.le_trans hle₁₂ hle₂₃⟩

instance instIsPartialOrderPartial {B : Type u} [LE B] [Std.IsPartialOrder B] :
    Std.IsPartialOrder (Partial B) where
  le_antisymm _ _ h₁₂ h₂₁ :=
    Partial.ext
      ⟨fun h₁ => (h₂₁ h₁).1, fun h₂ => (h₁₂ h₂).1⟩
      (fun h₁ h₂ =>
        let ⟨_, hle₁₂⟩ := h₁₂ h₂
        let ⟨_, hle₂₁⟩ := h₂₁ h₁
        Std.le_antisymm hle₁₂ hle₂₁)

/--
Contract separating the safety precondition (`defined := safetyPre`) from the
functional implication (`val := fun _ out => funcPre → post out`).
-/
def Partial.contract {Out : Type u}
    (safetyPre funcPre : Prop) (post : Out → Prop) :
    Partial (BehaviorSet Out) where
  defined := safetyPre
  val := fun _ out => funcPre → post out

/--
A language bundling program carrier `Prog`, query domain `Query`, outcome domain
`Out`, and query-indexed partial semantics `sem`.
-/
structure Language : Type 1 where
  /-- Program representation carrier. -/
  Prog : Type
  /-- Per-execution query domain (inputs, initial state, etc.). -/
  Query : Type
  /-- Observable execution outcome domain. -/
  Out : Type
  /-- Query-indexed partial behavior semantics. -/
  sem : Prog → Query → Partial (BehaviorSet Out)

/-- Canonical behavior domain of a `Language`. -/
abbrev Language.Behavior (L : Language) : Type :=
  L.Query → Partial (BehaviorSet L.Out)

/-- Query-indexed specification on `L` requiring definedness on `pre q` and
    outcomes satisfying `post q`. -/
def Language.SpecOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => ⟨pre q, fun _ => post q⟩

/-- Unconditional query-indexed specification on `L`. -/
abbrev Language.Spec (L : Language)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

/-- Conditional UB-freedom specification under `safetyPre`. -/
def Language.WellFormedOn (L : Language) (safetyPre : L.Query → Prop) :
    L.Behavior :=
  fun q => ⟨safetyPre q, fun _ _ => True⟩

/-- Unconditional UB-freedom specification across all queries. -/
abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

/-- Query-indexed contract specification separating `safetyPre` from `funcPre → post`. -/
def Language.ContractSpec (L : Language)
    (safetyPre funcPre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => Partial.contract (safetyPre q) (funcPre q) (post q)

/-- Compilation refinement pass (`L_tgt.sem t ≤ π_c (L_src.sem s)`). -/
abbrev Compiles (L_src L_tgt : Language)
    (π_c : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ π_c (L_src.sem s)

/-- Verification abstraction pass (`L_src.sem s ≤ π_v (L_v.sem v)`). -/
abbrev Abstracts (L_v L_src : Language)
    (π_v : L_v.Behavior → L_src.Behavior)
    (v : L_v.Prog) (s : L_src.Prog) : Prop :=
  L_src.sem s ≤ π_v (L_v.sem v)

/-- Compiler lowering programs from `L_src` to `L_tgt` with behavior map `π`. -/
structure Compiler (L_src L_tgt : Language) : Type 1 where
  compile : L_src.Prog → L_tgt.Prog
  π : L_src.Behavior → L_tgt.Behavior

/-- Per-program compiler soundness (`C.π` is monotone and `s` compiles to `C.compile s`). -/
def Compiler.SoundOn {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) : Prop :=
  Monotone C.π ∧ Compiles L_src L_tgt C.π s (C.compile s)

/-- End-to-end verification of `s` against `spec` across compiler `C`. -/
def Compiler.Verified {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) (spec : L_src.Behavior) : Prop :=
  L_src.sem s ≤ spec ∧
  Compiles L_src L_tgt C.π s (C.compile s) ∧
  L_tgt.sem (C.compile s) ≤ C.π spec

/-- Assumption recorded in a verification unit's TCB with intrinsic `Prop` meaning. -/
class TrustedAssumption (A : Type u) : Type u where
  meaning : A → Prop

/-- Trust policy governing which assumptions of type `A` are permitted (`DESIGN.md`). -/
structure TrustPolicy (A : Type u) [TrustedAssumption A] : Type u where
  isAllowed : A → Prop

/-- Conjunction of a list of propositions. -/
def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

/-- Layer 1A verification-result envelope asserting trust-policy compliance and
    assumption-guarded baseline UB-freedom plus specification satisfaction
    (`DESIGN.md`). -/
def VerificationResultOn
    {L_src L_tgt : Language}
    {A : Type u} [TrustedAssumption A]
    (C : Compiler L_src L_tgt)
    (policy : TrustPolicy A)
    (assumptions : List A)
    (prog : L_src.Prog)
    (pre : L_src.Query → Prop)
    (specs : List L_src.Behavior) : Prop :=
  AllHold (assumptions.map policy.isAllowed) ∧
  (AllHold (assumptions.map TrustedAssumption.meaning) →
    AllHold ((L_src.WellFormedOn pre :: specs).map (C.Verified prog)))

end Trusted.Refinement
