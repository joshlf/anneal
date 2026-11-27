-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Trusted
import Anneal.ITree
import Anneal.FarkasMirCert

/-!
# Asymmetric Overflow-Trap Refinement & Panic-Preserving Elimination (`Anneal.Mir.OverflowTrapRefinement`)

Formalizes asymmetric `Trap`-vs-`UB` refinement directly over
`Trusted.Rustc.V2026_06_01.MirSemantics.stepMirState`, complementing Rust
`-C overflow-checks=on` / `-C panic=abort` / `-C panic=unwind` (`#4329`,
`#4330`, and panic-preserving bounds/overflow-check elimination
`arXiv:2611.33490`):

1. **Asymmetric 4-Outcome Refinement Preorder (`MirOutcomeClass`, `MirOutcomeRefines`)**:
   - `.ub ⊑ y` and `.unsupported ⊑ y` for all `y` (`ThrowUB ⊑ Trap`, `ThrowUB ⊑ Ret v`);
   - `.trap ⊑ .trap` (and never `.trap ⊑ .ret v`, `.trap ⊑ .ub`, or `.trap ⊑ .unsupported`);
   - `.ret v₁ ⊑ .ret v₂ ↔ v₁ = v₂` (and never `.ret v ⊑ .trap`, `.ret v ⊑ .ub`, or `.ret v ⊑ .unsupported`).
   Includes a strategy-exact variant (`MirExactOutcomeClass`, `MirExactOutcomeRefines`)
   distinguishing `.trap .abort` (`-C panic=abort`) from `.trap .panic` (`-C panic=unwind`),
   `Std.IsPreorder` instances, bidirectional equivalence `MirOutcomeEquiv`, and exact
   duality bridges to `Trusted.Refinement.Partial` (`mirOutcomeRefines_iff_partial_le`,
   `mirExactOutcomeRefines_iff_partial_le`).
2. **Multi-Step `stepMirState` Runner & Coinductive `mirCallTree` / `WeakRef` Bridge**:
   `runMirSteps` steps `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirState` with fuel
   monotonicity and exact soundness bridges to `mirTree`, `mirCallTree`, `TauStar`,
   `FaultNow`, `Eutt`, `Anneal.ITree.WeakRef`, and `Trusted.ITree.ITree.toPartial`, including an
   exact characterization of EVERY `.faulted fk` runner result (`runMirSteps_faulted_to_tauStar`).
3. **Exact `stepMirState` Checked-vs-Unchecked Arithmetic Refinement**:
   Parametric `CapturedMir` bodies for all `u : UintTy`, all three unsigned operations
   (`add`, `sub`, `mul`), and both `-C panic=abort` (`UnwindAction.terminate`) and
   `-C panic=unwind` (`UnwindAction.continue_`):
   - **Unconditional forward direction (`unchecked ⊑ checked`)** for all valid unsigned inputs;
   - **Necessary and sufficient reverse direction (`checked ⊑ unchecked ↔ NoOverflow`)**;
   - **One-`rfl` `Anneal.FarkasMirCert` panic-preserving elimination** for `add`, `sub`
     (both range-hypothesized and fully certified), `mul_const` (left and right), and a
     composite multi-statement `add_scaled` (`a + k * b`) body.
   - **Fuel-independence & non-vacuity**: every canonical run classifies to a
     non-`.unsupported` outcome under its own panic strategy for ALL inputs (so no refinement
     verdict ever comes from fuel truncation, an unmodeled construct, or a strategy-mismatched
     trap), and every verdict holds verbatim at any larger fuel.
4. **Explicit Non-Vacuous Negative Soundness Suite**:
   Constructive disproofs of every forbidden refinement edge and concrete `stepMirState`
   overflowing/underflowing counterexamples for `add`, `sub`, `mul`, `add_scaled`, and
   `-C panic=abort` vs. `-C panic=unwind` strategy separation.
-/

namespace Anneal.Mir.OverflowTrapRefinement

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.ITree
open Anneal.LinearArith
open Anneal.AiPcc
open Anneal.FarkasMirCert

/-! ## 1. Outcome Classification, Asymmetric Refinement Preorder, & `Partial` Duality -/

/-- Rust compilation panic strategy (`-C panic=abort` vs. `-C panic=unwind`). -/
inductive PanicStrategy : Type where
  /-- `-C panic=abort`: failed assertions terminate immediately (`UnwindAction.terminate`). -/
  | abort
  /-- `-C panic=unwind`: failed assertions unwind the stack (`UnwindAction.continue_`). -/
  | unwind
  deriving DecidableEq, Repr

/-- Exact deterministic trap outcome kind produced by MIR halting semantics. -/
inductive TrapKind : Type where
  /-- Immediate process abort (`Outcome.abort`). -/
  | abort
  /-- Unwinding panic (`Outcome.panic`). -/
  | panic
  deriving DecidableEq, Repr

/-- `UnwindAction` corresponding to a `PanicStrategy`. -/
def PanicStrategy.toUnwindAction : PanicStrategy → UnwindAction
  | .abort => .terminate
  | .unwind => .continue_

/-- `TrapKind` corresponding to a `PanicStrategy`. -/
def PanicStrategy.toTrapKind : PanicStrategy → TrapKind
  | .abort => .abort
  | .unwind => .panic

/-- Halting `MirOutcome` produced when a root assertion fails under `strat`. -/
def PanicStrategy.toTrapOutcome : PanicStrategy → MirOutcome
  | .abort => .abort
  | .unwind => .panic

/-- Four-outcome semantic classification for asymmetric `Trap`-vs-`UB` refinement. -/
inductive MirOutcomeClass (Val : Type) : Type where
  /-- Normal return yielding `v`. -/
  | ret (v : Val)
  /-- Deterministic, defined trap (panic or abort) — strictly distinct from UB and normal return. -/
  | trap
  /-- Undefined behavior (`FailureKind.ub`). -/
  | ub
  /-- Fail-closed unsupported or fuel-truncated outcome. -/
  | unsupported
  deriving DecidableEq, Repr

/-- Strategy-exact outcome classification separating `.trap .abort` from `.trap .panic`. -/
inductive MirExactOutcomeClass (Val : Type) : Type where
  /-- Normal return yielding `v`. -/
  | ret (v : Val)
  /-- Deterministic trap tagged with its exact `TrapKind` (`.abort` vs. `.panic`). -/
  | trap (kind : TrapKind)
  /-- Undefined behavior (`FailureKind.ub`). -/
  | ub
  /-- Fail-closed unsupported or fuel-truncated outcome. -/
  | unsupported
  deriving DecidableEq, Repr

/-- Forget the distinction between `.abort` and `.panic` traps. -/
def MirExactOutcomeClass.forgetTrapKind {Val : Type} :
    MirExactOutcomeClass Val → MirOutcomeClass Val
  | .ret v => .ret v
  | .trap _ => .trap
  | .ub => .ub
  | .unsupported => .unsupported

/-- Asymmetric refinement relation `spec ⊑ impl` over `MirOutcomeClass Val`:
- `.ub ⊑ y` and `.unsupported ⊑ y` for all `y` (replacing UB with a deterministic trap
  or normal return is sound);
- `.trap ⊑ .trap` (and `.trap` never refines `.ret v`, `.ub`, or `.unsupported`);
- `.ret v₁ ⊑ .ret v₂ ↔ v₁ = v₂` (and `.ret v` never refines `.trap`, `.ub`, or `.unsupported`). -/
def MirOutcomeRefines {Val : Type} : MirOutcomeClass Val → MirOutcomeClass Val → Prop
  | .ub, _ => True
  | .unsupported, _ => True
  | .trap, .trap => True
  | .ret v₁, .ret v₂ => v₁ = v₂
  | _, _ => False

/-- Bidirectional asymmetric refinement equivalence (`x ⊑ y ∧ y ⊑ x`). -/
def MirOutcomeEquiv {Val : Type} (x y : MirOutcomeClass Val) : Prop :=
  MirOutcomeRefines x y ∧ MirOutcomeRefines y x

/-- Strategy-exact asymmetric refinement `spec ⊑ impl` over `MirExactOutcomeClass Val`,
requiring exact match of `TrapKind` (`.abort` vs. `.panic`). -/
def MirExactOutcomeRefines {Val : Type} :
    MirExactOutcomeClass Val → MirExactOutcomeClass Val → Prop
  | .ub, _ => True
  | .unsupported, _ => True
  | .trap k₁, .trap k₂ => k₁ = k₂
  | .ret v₁, .ret v₂ => v₁ = v₂
  | _, _ => False

/-- Bidirectional equivalence over `MirExactOutcomeClass Val`. -/
def MirExactOutcomeEquiv {Val : Type} (x y : MirExactOutcomeClass Val) : Prop :=
  MirExactOutcomeRefines x y ∧ MirExactOutcomeRefines y x

theorem mirOutcomeRefines_refl {Val : Type} (x : MirOutcomeClass Val) :
    MirOutcomeRefines x x := by
  cases x with
  | ret _ => rfl
  | trap => trivial
  | ub => trivial
  | unsupported => trivial

theorem mirOutcomeRefines_trans {Val : Type} {x y z : MirOutcomeClass Val}
    (hxy : MirOutcomeRefines x y) (hyz : MirOutcomeRefines y z) :
    MirOutcomeRefines x z := by
  cases x with
  | ub => trivial
  | unsupported => trivial
  | trap =>
    cases y with
    | trap => exact hyz
    | ret _ | ub | unsupported => exact False.elim hxy
  | ret v₁ =>
    cases y with
    | ret v₂ =>
      cases z with
      | ret v₃ => exact hxy.trans hyz
      | trap | ub | unsupported => exact False.elim hyz
    | trap | ub | unsupported => exact False.elim hxy

theorem mirOutcomeEquiv_refl {Val : Type} (x : MirOutcomeClass Val) :
    MirOutcomeEquiv x x :=
  ⟨mirOutcomeRefines_refl x, mirOutcomeRefines_refl x⟩

theorem mirOutcomeEquiv_symm {Val : Type} {x y : MirOutcomeClass Val}
    (h : MirOutcomeEquiv x y) : MirOutcomeEquiv y x :=
  ⟨h.2, h.1⟩

theorem mirOutcomeEquiv_trans {Val : Type} {x y z : MirOutcomeClass Val}
    (hxy : MirOutcomeEquiv x y) (hyz : MirOutcomeEquiv y z) :
    MirOutcomeEquiv x z :=
  ⟨mirOutcomeRefines_trans hxy.1 hyz.1, mirOutcomeRefines_trans hyz.2 hxy.2⟩

theorem mirExactOutcomeRefines_refl {Val : Type} (x : MirExactOutcomeClass Val) :
    MirExactOutcomeRefines x x := by
  cases x with
  | ret _ => rfl
  | trap _ => rfl
  | ub => trivial
  | unsupported => trivial

theorem mirExactOutcomeRefines_trans {Val : Type} {x y z : MirExactOutcomeClass Val}
    (hxy : MirExactOutcomeRefines x y) (hyz : MirExactOutcomeRefines y z) :
    MirExactOutcomeRefines x z := by
  cases x with
  | ub => trivial
  | unsupported => trivial
  | trap k₁ =>
    cases y with
    | trap k₂ =>
      cases z with
      | trap k₃ => exact hxy.trans hyz
      | ret _ | ub | unsupported => exact False.elim hyz
    | ret _ | ub | unsupported => exact False.elim hxy
  | ret v₁ =>
    cases y with
    | ret v₂ =>
      cases z with
      | ret v₃ => exact hxy.trans hyz
      | trap _ | ub | unsupported => exact False.elim hyz
    | trap _ | ub | unsupported => exact False.elim hxy

theorem mirExactOutcomeRefines_forget {Val : Type} {x y : MirExactOutcomeClass Val}
    (h : MirExactOutcomeRefines x y) :
    MirOutcomeRefines x.forgetTrapKind y.forgetTrapKind := by
  cases x with
  | ub => trivial
  | unsupported => trivial
  | trap _ =>
    cases y with
    | trap _ => trivial
    | ret _ | ub | unsupported => exact False.elim h
  | ret _ =>
    cases y with
    | ret _ => exact h
    | trap _ | ub | unsupported => exact False.elim h

theorem mirExactOutcomeEquiv_refl {Val : Type} (x : MirExactOutcomeClass Val) :
    MirExactOutcomeEquiv x x :=
  ⟨mirExactOutcomeRefines_refl x, mirExactOutcomeRefines_refl x⟩

theorem mirExactOutcomeEquiv_symm {Val : Type} {x y : MirExactOutcomeClass Val}
    (h : MirExactOutcomeEquiv x y) : MirExactOutcomeEquiv y x :=
  ⟨h.2, h.1⟩

theorem mirExactOutcomeEquiv_trans {Val : Type} {x y z : MirExactOutcomeClass Val}
    (hxy : MirExactOutcomeEquiv x y) (hyz : MirExactOutcomeEquiv y z) :
    MirExactOutcomeEquiv x z :=
  ⟨mirExactOutcomeRefines_trans hxy.1 hyz.1, mirExactOutcomeRefines_trans hyz.2 hxy.2⟩

/-- `LE` on `MirOutcomeClass Val` aligned with `Trusted.Refinement` Smyth order:
`impl ≤ spec` iff `MirOutcomeRefines spec impl` (`.ub` and `.unsupported` are top). -/
instance instLEMirOutcomeClass {Val : Type} : LE (MirOutcomeClass Val) where
  le impl spec := MirOutcomeRefines spec impl

instance instIsPreorderMirOutcomeClass {Val : Type} :
    Std.IsPreorder (MirOutcomeClass Val) where
  le_refl x := mirOutcomeRefines_refl x
  le_trans _ _ _ h₁₂ h₂₃ := mirOutcomeRefines_trans h₂₃ h₁₂

/-- `LE` on `MirExactOutcomeClass Val` aligned with `Trusted.Refinement` Smyth order. -/
instance instLEMirExactOutcomeClass {Val : Type} : LE (MirExactOutcomeClass Val) where
  le impl spec := MirExactOutcomeRefines spec impl

instance instIsPreorderMirExactOutcomeClass {Val : Type} :
    Std.IsPreorder (MirExactOutcomeClass Val) where
  le_refl x := mirExactOutcomeRefines_refl x
  le_trans _ _ _ h₁₂ h₂₃ := mirExactOutcomeRefines_trans h₂₃ h₁₂

/-- Defined halting outcomes (non-UB) for the `Trusted.Refinement.Partial` bridge. -/
inductive DefinedOutcome (Val : Type) : Type where
  | ret (v : Val)
  | trap
  deriving DecidableEq, Repr

/-- Strategy-exact defined halting outcomes for the `Trusted.Refinement.Partial` bridge. -/
inductive ExactDefinedOutcome (Val : Type) : Type where
  | ret (v : Val)
  | trap (kind : TrapKind)
  deriving DecidableEq, Repr

/-- Embed `MirOutcomeClass Val` into `Trusted.Refinement.Partial (BehaviorSet (DefinedOutcome Val))`. -/
def MirOutcomeClass.toPartial {Val : Type} :
    MirOutcomeClass Val → Partial (BehaviorSet (DefinedOutcome Val))
  | .ret v => Partial.pure (fun d => d = .ret v)
  | .trap => Partial.pure (fun d => d = .trap)
  | .ub => Partial.ub
  | .unsupported => Partial.ub

/-- Embed `MirExactOutcomeClass Val` into `Trusted.Refinement.Partial (BehaviorSet (ExactDefinedOutcome Val))`. -/
def MirExactOutcomeClass.toPartial {Val : Type} :
    MirExactOutcomeClass Val → Partial (BehaviorSet (ExactDefinedOutcome Val))
  | .ret v => Partial.pure (fun d => d = .ret v)
  | .trap k => Partial.pure (fun d => d = .trap k)
  | .ub => Partial.ub
  | .unsupported => Partial.ub

/-- Exact duality bridge to Layer 1A `Trusted.Refinement.Partial`:
`MirOutcomeRefines spec impl` holds iff `impl.toPartial ≤ spec.toPartial`. -/
theorem mirOutcomeRefines_iff_partial_le {Val : Type}
    (spec impl : MirOutcomeClass Val) :
    MirOutcomeRefines spec impl ↔ impl.toPartial ≤ spec.toPartial := by
  constructor
  · intro hRef hSpecDef
    cases spec with
    | ub => exact False.elim hSpecDef
    | unsupported => exact False.elim hSpecDef
    | trap =>
      cases impl with
      | trap => exact ⟨trivial, fun _ hd => hd⟩
      | ret _ | ub | unsupported => exact False.elim hRef
    | ret v₁ =>
      cases impl with
      | ret v₂ =>
        refine ⟨trivial, fun d hd => ?_⟩
        rw [hd, hRef]
        rfl
      | trap | ub | unsupported => exact False.elim hRef
  · intro hLe
    cases spec with
    | ub => trivial
    | unsupported => trivial
    | trap =>
      have ⟨hImplDef, hSub⟩ := hLe trivial
      cases impl with
      | trap => trivial
      | ub | unsupported => exact False.elim hImplDef
      | ret v =>
        have hEq : DefinedOutcome.ret v = DefinedOutcome.trap := hSub (.ret v) rfl
        nomatch hEq
    | ret v₁ =>
      have ⟨hImplDef, hSub⟩ := hLe trivial
      cases impl with
      | ret v₂ =>
        have hEq : DefinedOutcome.ret v₂ = DefinedOutcome.ret v₁ := hSub (.ret v₂) rfl
        injection hEq with hv
        exact hv.symm
      | trap =>
        have hEq : DefinedOutcome.trap = DefinedOutcome.ret v₁ := hSub .trap rfl
        nomatch hEq
      | ub | unsupported => exact False.elim hImplDef

/-- `MirOutcomeClass.toPartial` is `Trusted.Refinement.Monotone`. -/
theorem mirOutcomeClass_toPartial_monotone {Val : Type} :
    Trusted.Refinement.Monotone (MirOutcomeClass.toPartial (Val := Val)) :=
  fun _ _ h => (mirOutcomeRefines_iff_partial_le _ _).1 h

/-- Exact duality bridge for strategy-exact outcomes (`MirExactOutcomeClass`). -/
theorem mirExactOutcomeRefines_iff_partial_le {Val : Type}
    (spec impl : MirExactOutcomeClass Val) :
    MirExactOutcomeRefines spec impl ↔ impl.toPartial ≤ spec.toPartial := by
  constructor
  · intro hRef hSpecDef
    cases spec with
    | ub => exact False.elim hSpecDef
    | unsupported => exact False.elim hSpecDef
    | trap k₁ =>
      cases impl with
      | trap k₂ =>
        refine ⟨trivial, fun d hd => ?_⟩
        rw [hd, hRef]
        rfl
      | ret _ | ub | unsupported => exact False.elim hRef
    | ret v₁ =>
      cases impl with
      | ret v₂ =>
        refine ⟨trivial, fun d hd => ?_⟩
        rw [hd, hRef]
        rfl
      | trap _ | ub | unsupported => exact False.elim hRef
  · intro hLe
    cases spec with
    | ub => trivial
    | unsupported => trivial
    | trap k₁ =>
      have ⟨hImplDef, hSub⟩ := hLe trivial
      cases impl with
      | trap k₂ =>
        have hEq : ExactDefinedOutcome.trap k₂ = ExactDefinedOutcome.trap k₁ :=
          hSub (.trap k₂) rfl
        injection hEq with hk
        exact hk.symm
      | ret v =>
        have hEq : ExactDefinedOutcome.ret v = ExactDefinedOutcome.trap k₁ :=
          hSub (.ret v) rfl
        nomatch hEq
      | ub | unsupported => exact False.elim hImplDef
    | ret v₁ =>
      have ⟨hImplDef, hSub⟩ := hLe trivial
      cases impl with
      | ret v₂ =>
        have hEq : ExactDefinedOutcome.ret v₂ = ExactDefinedOutcome.ret v₁ :=
          hSub (.ret v₂) rfl
        injection hEq with hv
        exact hv.symm
      | trap k =>
        have hEq : ExactDefinedOutcome.trap k = ExactDefinedOutcome.ret v₁ :=
          hSub (.trap k) rfl
        nomatch hEq
      | ub | unsupported => exact False.elim hImplDef

/-- `MirExactOutcomeClass.toPartial` is `Trusted.Refinement.Monotone`. -/
theorem mirExactOutcomeClass_toPartial_monotone {Val : Type} :
    Trusted.Refinement.Monotone (MirExactOutcomeClass.toPartial (Val := Val)) :=
  fun _ _ h => (mirExactOutcomeRefines_iff_partial_le _ _).1 h

/-! ## 2. Multi-Step `stepMirState` Runner & Coinductive `mirCallTree` / `WeakRef` Bridge -/

/-- Fuel-bounded multi-step operational executor stepping `stepMirState`.
Returns `.halted out` or `.faulted fk` immediately once reached; returns
`.faulted .outOfFuel` if still `.running _` at fuel `0`. -/
def runMirSteps (body : CapturedMir) : Nat → MirExecState → MirExecState
  | 0, st =>
    match st with
    | .running _ => .faulted .outOfFuel
    | .halted out => .halted out
    | .faulted fk => .faulted fk
  | fuel + 1, st =>
    match st with
    | .halted out => .halted out
    | .faulted fk => .faulted fk
    | .running s =>
      match stepMirState body (.running s) with
      | .tau next => runMirSteps body fuel next
      | .ret out => .halted out
      | .vis (.inl (.fail fk)) _ => .faulted fk
      | .vis (.inr _) _ => .faulted .unsupported

/-- Convenience entry state wrapper for `runMirSteps`. -/
def initExecState (body : CapturedMir) (args : List Value) : MirExecState :=
  .running (initMachineState body args)

/-- Fuel-bounded execution starting from `initMachineState body args`. -/
def runMirCall (body : CapturedMir) (fuel : Nat) (args : List Value) : MirExecState :=
  runMirSteps body fuel (initExecState body args)

/-- Strategy-exact classifier mapping a `MirExecState` to `MirExactOutcomeClass Value`. -/
def classifyMirExecStateExact : MirExecState → MirExactOutcomeClass Value
  | .halted (.normal (v, _)) => .ret v
  | .halted .abort => .trap .abort
  | .halted .panic => .trap .panic
  | .faulted .ub => .ub
  | .faulted .unsupported => .unsupported
  | .faulted .outOfFuel => .unsupported
  | .running _ => .unsupported

/-- Full-outcome strategy-exact classifier preserving both the return value and final memory
`(Value × Memory)` so `MirExactOutcomeRefines` corresponds *iff* to Layer 1A `ITree.toPartial`
and coinductive `WeakRef` over `mirCallTree` for every settled execution. -/
def classifyMirOutcomeExact : MirExecState → MirExactOutcomeClass (Value × Memory)
  | .halted (.normal vm) => .ret vm
  | .halted .abort => .trap .abort
  | .halted .panic => .trap .panic
  | .faulted .ub => .ub
  | .faulted .unsupported => .unsupported
  | .faulted .outOfFuel => .unsupported
  | .running _ => .unsupported

/-- Strategy-parameterized classifier mapping `.halted .abort` to `.trap` under `.abort`
and `.halted .panic` to `.trap` under `.unwind`. When comparing two bodies compiled with
different panic strategies, use `classifyMirExecStateExact` so a mismatched trap kind
never collapses to `.unsupported`. -/
def classifyMirExecState (strat : PanicStrategy) : MirExecState → MirOutcomeClass Value
  | .halted (.normal (v, _)) => .ret v
  | .halted .abort =>
    match strat with
    | .abort => .trap
    | .unwind => .unsupported
  | .halted .panic =>
    match strat with
    | .unwind => .trap
    | .abort => .unsupported
  | .faulted .ub => .ub
  | .faulted .unsupported => .unsupported
  | .faulted .outOfFuel => .unsupported
  | .running _ => .unsupported

/-- Strategy-agnostic classifier mapping both `.halted .abort` and `.halted .panic` to `.trap`. -/
def classifyAnyTrap (st : MirExecState) : MirOutcomeClass Value :=
  (classifyMirExecStateExact st).forgetTrapKind

theorem classifyMirExecState_matches_exact_abort (st : MirExecState)
    (hNoPanic : st ≠ .halted .panic) :
    classifyMirExecState .abort st = classifyAnyTrap st := by
  cases st with
  | running _ => rfl
  | faulted fk => cases fk <;> rfl
  | halted out =>
    cases out with
    | normal p => rfl
    | abort => rfl
    | panic => exact False.elim (hNoPanic rfl)

theorem classifyMirExecState_matches_exact_unwind (st : MirExecState)
    (hNoAbort : st ≠ .halted .abort) :
    classifyMirExecState .unwind st = classifyAnyTrap st := by
  cases st with
  | running _ => rfl
  | faulted fk => cases fk <;> rfl
  | halted out =>
    cases out with
    | normal p => rfl
    | abort => exact False.elim (hNoAbort rfl)
    | panic => rfl

/-- Fuel monotonicity for halted executions: once `runMirSteps` halts at `fuel`,
any larger fuel `fuel + extra` yields the exact same `.halted out`. -/
theorem runMirSteps_halted_mono (body : CapturedMir) :
    ∀ (fuel extra : Nat) (st : MirExecState) (out : MirOutcome),
      runMirSteps body fuel st = .halted out →
      runMirSteps body (fuel + extra) st = .halted out
  | 0, extra, st, out, h => by
    cases st with
    | running _ => nomatch h
    | faulted _ => nomatch h
    | halted o =>
      cases extra with
      | zero => exact h
      | succ _ => exact h
  | fuel + 1, extra, st, out, h => by
    cases st with
    | halted o =>
      dsimp only [runMirSteps] at h
      rw [Nat.succ_add]
      exact h
    | faulted _ => nomatch h
    | running s =>
      rw [Nat.succ_add]
      dsimp only [runMirSteps] at h ⊢
      cases hStep : stepMirState body (.running s) with
      | ret o =>
        rw [hStep] at h
        exact h
      | tau next =>
        rw [hStep] at h
        exact runMirSteps_halted_mono body fuel extra next out h
      | vis i k =>
        rw [hStep] at h
        cases i with
        | inl req => cases req; nomatch h
        | inr _ => nomatch h

/-- Fuel monotonicity for UB faults: once `runMirSteps` faults with `.ub` at `fuel`,
any larger fuel `fuel + extra` yields `.faulted .ub`. -/
theorem runMirSteps_ub_mono (body : CapturedMir) :
    ∀ (fuel extra : Nat) (st : MirExecState),
      runMirSteps body fuel st = .faulted .ub →
      runMirSteps body (fuel + extra) st = .faulted .ub
  | 0, extra, st, h => by
    cases st with
    | running _ => nomatch h
    | halted _ => nomatch h
    | faulted fk =>
      cases extra with
      | zero => exact h
      | succ _ => exact h
  | fuel + 1, extra, st, h => by
    cases st with
    | halted _ => nomatch h
    | faulted fk =>
      dsimp only [runMirSteps] at h
      rw [Nat.succ_add]
      exact h
    | running s =>
      rw [Nat.succ_add]
      dsimp only [runMirSteps] at h ⊢
      cases hStep : stepMirState body (.running s) with
      | ret _ => rw [hStep] at h; nomatch h
      | tau next =>
        rw [hStep] at h
        exact runMirSteps_ub_mono body fuel extra next h
      | vis i k =>
        rw [hStep] at h
        cases i with
        | inl req => cases req; exact h
        | inr _ => nomatch h

/-- A `MirExecState` is *settled* when it is a genuine halting outcome or a genuine UB fault
(never an `.outOfFuel` truncation, an `.unsupported` boundary, or a still-`.running` state). -/
def SettledExec : MirExecState → Prop
  | .halted _ => True
  | .faulted .ub => True
  | _ => False

/-- A non-`.unsupported` classification under ANY strategy implies the state is settled. -/
theorem settledExec_of_classify_ne_unsupported {strat : PanicStrategy} {st : MirExecState}
    (h : classifyMirExecState strat st ≠ .unsupported) : SettledExec st := by
  cases st with
  | halted _ => trivial
  | running _ => exact False.elim (h rfl)
  | faulted fk =>
    cases fk with
    | ub => trivial
    | unsupported => exact False.elim (h rfl)
    | outOfFuel => exact False.elim (h rfl)

/-- Settled `runMirSteps` results are invariant under additional fuel. -/
theorem runMirSteps_settled_mono (body : CapturedMir) (fuel extra : Nat) (st : MirExecState)
    (h : SettledExec (runMirSteps body fuel st)) :
    runMirSteps body (fuel + extra) st = runMirSteps body fuel st := by
  generalize hR : runMirSteps body fuel st = r at h ⊢
  cases r with
  | halted o => exact runMirSteps_halted_mono body fuel extra st o hR
  | running _ => exact False.elim h
  | faulted fk =>
    cases fk with
    | ub => exact runMirSteps_ub_mono body fuel extra st hR
    | unsupported => exact False.elim h
    | outOfFuel => exact False.elim h

/-- Settled `runMirCall` results are identical at every larger fuel `fuel' ≥ fuel`. -/
theorem runMirCall_fuel_stable {body : CapturedMir} {fuel fuel' : Nat} {args : List Value}
    (hle : fuel ≤ fuel') (h : SettledExec (runMirCall body fuel args)) :
    runMirCall body fuel' args = runMirCall body fuel args := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact runMirSteps_settled_mono body fuel extra _ h

/-- Coinductive MIR interaction tree starting from an arbitrary `MirExecState`. -/
def mirExecTree (body : CapturedMir) (st : MirExecState) :
    ITree MirEffect MirOutcome :=
  ITree.cofix (stepMirState body) st

theorem mirExecTree_running (body : CapturedMir) (s : MachineState) :
    mirExecTree body (.running s) = mirTree body s :=
  rfl

/-- Step-bounded silent `.tau` reduction: `TauLeN n t u` means `t` reduces to `u` in
at most `n` silent `.tau` steps. -/
inductive TauLeN {E : Effect.{0}} {R : Type} : Nat → ITree E R → ITree E R → Prop where
  | refl (n : Nat) (t : ITree E R) : TauLeN n t t
  | step {n : Nat} {t t' u : ITree E R} :
      t.observe = .tau t' → TauLeN n t' u → TauLeN (n + 1) t u

/-- Erase the step bound of `TauLeN` to `Trusted.ITree.TauStar`. -/
theorem TauLeN.toTauStar {E : Effect.{0}} {R : Type} {n : Nat} {t u : ITree E R}
    (h : TauLeN n t u) : TauStar t u := by
  induction h with
  | refl _ _ => exact .refl _
  | step hObs _ ih => exact .step hObs ih

/-- `TauLeN` is monotone in the step bound `n`. -/
theorem TauLeN.mono {E : Effect.{0}} {R : Type} {n m : Nat} {t u : ITree E R}
    (h : TauLeN n t u) (hle : n ≤ m) : TauLeN m t u := by
  induction h generalizing m with
  | refl _ _ => exact .refl m _
  | @step n' _ _ _ hObs _ ih =>
    cases m with
    | zero => exact False.elim (Nat.not_succ_le_zero n' hle)
    | succ m' => exact .step hObs (ih (Nat.le_of_succ_le_succ hle))

/-- Step-bounded (`≤ fuel`) `TauLeN` bridge for halted executions: if
`runMirSteps body fuel st = .halted out`, then `mirExecTree body st` reduces in at most
`fuel` silent `.tau` steps to a node observing `.ret out`. -/
theorem runMirSteps_halted_to_tauLeN (body : CapturedMir) :
    ∀ (fuel : Nat) (st : MirExecState) (out : MirOutcome),
      runMirSteps body fuel st = .halted out →
      ∃ u : ITree MirEffect MirOutcome,
        TauLeN fuel (mirExecTree body st) u ∧ u.observe = .ret out
  | 0, st, out, h => by
    cases st with
    | running _ => nomatch h
    | faulted _ => nomatch h
    | halted o =>
      injection h with ho
      subst ho
      refine ⟨mirExecTree body (.halted o), .refl 0 _, ?_⟩
      unfold mirExecTree
      rw [ITree.observe_cofix]
      rfl
  | fuel + 1, st, out, h => by
    cases st with
    | halted o =>
      dsimp only [runMirSteps] at h
      injection h with ho
      subst ho
      refine ⟨mirExecTree body (.halted o), .refl (fuel + 1) _, ?_⟩
      unfold mirExecTree
      rw [ITree.observe_cofix]
      rfl
    | faulted _ => nomatch h
    | running s =>
      dsimp only [runMirSteps] at h
      cases hStep : stepMirState body (.running s) with
      | ret o =>
        rw [hStep] at h
        injection h with ho
        subst ho
        refine ⟨mirExecTree body (.running s), .refl (fuel + 1) _, ?_⟩
        unfold mirExecTree
        rw [ITree.observe_cofix, hStep]
        rfl
      | tau next =>
        rw [hStep] at h
        have ⟨u, hTau, hObs⟩ := runMirSteps_halted_to_tauLeN body fuel next out h
        have hStepObs : (mirExecTree body (.running s)).observe = .tau (mirExecTree body next) := by
          unfold mirExecTree
          rw [ITree.observe_cofix, hStep]
          rfl
        exact ⟨u, .step hStepObs hTau, hObs⟩
      | vis i k =>
        rw [hStep] at h
        cases i with
        | inl req => cases req; nomatch h
        | inr _ => nomatch h

/-- Exact `TauStar` bridge for halted executions (corollary of `runMirSteps_halted_to_tauLeN`). -/
theorem runMirSteps_halted_to_tauStar (body : CapturedMir)
    (fuel : Nat) (st : MirExecState) (out : MirOutcome)
    (h : runMirSteps body fuel st = .halted out) :
    ∃ u : ITree MirEffect MirOutcome,
      TauStar (mirExecTree body st) u ∧ u.observe = .ret out :=
  let ⟨u, hLe, hObs⟩ := runMirSteps_halted_to_tauLeN body fuel st out h
  ⟨u, hLe.toTauStar, hObs⟩

/-- Step-bounded (`≤ fuel`) `TauLeN` characterization of EVERY `.faulted fk` result of
`runMirSteps`: `mirExecTree body st` reduces in at most `fuel` silent `.tau` steps to a node
`u` that is either
- the genuine fail node `.vis (.inl (.fail fk)) PEmpty.elim` emitted by `stepMirState`, or
- (only when `fk = .unsupported`) a non-fault observation/call request `.vis (.inr e) k`
  that the fuel-bounded runner conservatively refuses to model, or
- (only when `fk = .outOfFuel`) a still-running state that the runner truncated.
So `runMirSteps` never fabricates a fault: every runner-introduced fault kind is
precisely accounted for within the `≤ fuel` step bound. -/
theorem runMirSteps_faulted_to_tauLeN (body : CapturedMir) :
    ∀ (fuel : Nat) (st : MirExecState) (fk : FailureKind),
      runMirSteps body fuel st = .faulted fk →
      ∃ u : ITree MirEffect MirOutcome,
        TauLeN fuel (mirExecTree body st) u ∧
        (u.observe = .vis (.inl (.fail fk)) PEmpty.elim ∨
         (fk = .unsupported ∧ ∃ e k, u.observe = .vis (.inr e) k) ∨
         (fk = .outOfFuel ∧ ∃ s, u = mirExecTree body (.running s)))
  | 0, st, fk, h => by
    cases st with
    | running s =>
      dsimp only [runMirSteps] at h
      injection h with hfk
      subst hfk
      exact ⟨mirExecTree body (.running s), .refl 0 _, .inr (.inr ⟨rfl, s, rfl⟩)⟩
    | halted _ => nomatch h
    | faulted fk' =>
      dsimp only [runMirSteps] at h
      injection h with hfk
      subst hfk
      refine ⟨mirExecTree body (.faulted fk'), .refl 0 _, .inl ?_⟩
      unfold mirExecTree
      rw [ITree.observe_cofix]
      dsimp only [stepMirState, MirStepNode.fail, ITreeF.map]
      congr
      funext o
      exact PEmpty.elim o
  | fuel + 1, st, fk, h => by
    cases st with
    | halted _ => nomatch h
    | faulted fk' =>
      dsimp only [runMirSteps] at h
      injection h with hfk
      subst hfk
      refine ⟨mirExecTree body (.faulted fk'), .refl (fuel + 1) _, .inl ?_⟩
      unfold mirExecTree
      rw [ITree.observe_cofix]
      dsimp only [stepMirState, MirStepNode.fail, ITreeF.map]
      congr
      funext o
      exact PEmpty.elim o
    | running s =>
      dsimp only [runMirSteps] at h
      cases hStep : stepMirState body (.running s) with
      | ret _ => rw [hStep] at h; nomatch h
      | tau next =>
        rw [hStep] at h
        have ⟨u, hTau, hObs⟩ := runMirSteps_faulted_to_tauLeN body fuel next fk h
        have hStepObs : (mirExecTree body (.running s)).observe = .tau (mirExecTree body next) := by
          unfold mirExecTree
          rw [ITree.observe_cofix, hStep]
          rfl
        exact ⟨u, .step hStepObs hTau, hObs⟩
      | vis i k =>
        rw [hStep] at h
        cases i with
        | inl req =>
          cases req with
          | fail fk' =>
            injection h with hfk
            subst hfk
            refine ⟨mirExecTree body (.running s), .refl (fuel + 1) _, .inl ?_⟩
            unfold mirExecTree
            rw [ITree.observe_cofix, hStep]
            dsimp only [ITreeF.map]
            congr
            funext o
            exact PEmpty.elim o
        | inr e =>
          injection h with hfk
          subst hfk
          refine ⟨mirExecTree body (.running s), .refl (fuel + 1) _,
            .inr (.inl ⟨rfl, e, fun x => mirExecTree body (k x), ?_⟩)⟩
          unfold mirExecTree
          rw [ITree.observe_cofix, hStep]
          rfl

/-- Step-bounded (`≤ fuel`) `TauLeN` + `FaultNow` bridge for `.ub` faults (corollary of
`runMirSteps_faulted_to_tauLeN`). -/
theorem runMirSteps_ub_to_tauLeN (body : CapturedMir)
    (fuel : Nat) (st : MirExecState)
    (h : runMirSteps body fuel st = .faulted .ub) :
    ∃ u : ITree MirEffect MirOutcome,
      TauLeN fuel (mirExecTree body st) u ∧
      u.observe = .vis (.inl (.fail .ub)) PEmpty.elim := by
  have ⟨u, hLe, hCase⟩ := runMirSteps_faulted_to_tauLeN body fuel st .ub h
  rcases hCase with hObs | ⟨hEq, _⟩ | ⟨hEq, _⟩
  · exact ⟨u, hLe, hObs⟩
  · nomatch hEq
  · nomatch hEq

/-- Exact `TauStar` + `FaultNow` bridge for `.ub` faults (corollary of
`runMirSteps_ub_to_tauLeN`). -/
theorem runMirSteps_ub_to_tauStar (body : CapturedMir)
    (fuel : Nat) (st : MirExecState)
    (h : runMirSteps body fuel st = .faulted .ub) :
    ∃ u : ITree MirEffect MirOutcome,
      TauStar (mirExecTree body st) u ∧
      u.observe = .vis (.inl (.fail .ub)) PEmpty.elim :=
  let ⟨u, hLe, hObs⟩ := runMirSteps_ub_to_tauLeN body fuel st h
  ⟨u, hLe.toTauStar, hObs⟩

/-- Exact `TauStar` characterization of EVERY `.faulted fk` result of `runMirSteps`
(corollary of `runMirSteps_faulted_to_tauLeN`). -/
theorem runMirSteps_faulted_to_tauStar (body : CapturedMir)
    (fuel : Nat) (st : MirExecState) (fk : FailureKind)
    (h : runMirSteps body fuel st = .faulted fk) :
    ∃ u : ITree MirEffect MirOutcome,
      TauStar (mirExecTree body st) u ∧
      (u.observe = .vis (.inl (.fail fk)) PEmpty.elim ∨
       (fk = .unsupported ∧ ∃ e k, u.observe = .vis (.inr e) k) ∨
       (fk = .outOfFuel ∧ ∃ s, u = mirExecTree body (.running s))) :=
  let ⟨u, hLe, hCase⟩ := runMirSteps_faulted_to_tauLeN body fuel st fk h
  ⟨u, hLe.toTauStar, hCase⟩

/-- `.faulted .ub` from `runMirCall` implies `FaultNow (mirCallTree body args)`. -/
theorem runMirCall_ub_faultNow {body : CapturedMir} {fuel : Nat}
    {args : List Value}
    (h : runMirCall body fuel args = .faulted .ub) :
    FaultNow (mirCallTree body args) :=
  let ⟨u, hTau, hObs⟩ := runMirSteps_ub_to_tauStar body fuel (initExecState body args) h
  ⟨u, .inl (.fail .ub), PEmpty.elim, hTau, hObs, trivial⟩

/-- A tree silently returning `r` does not fault (`¬ FaultNow t`). -/
theorem not_faultNow_of_tauStar_ret {E : Effect.{0}} {R : Type} [FaultEffect E]
    {t u : ITree E R} {r : R}
    (hs : TauStar t u) (hr : u.observe = .ret r) :
    ¬ FaultNow t := by
  rintro ⟨t', i, k, hst', hvt', _⟩
  have hEq : u = t' :=
    TauStar.unique_nonTau hs hst'
      (fun _ hw => by rw [hr] at hw; nomatch hw)
      (fun _ hw => by rw [hvt'] at hw; nomatch hw)
  rw [hEq, hvt'] at hr
  nomatch hr

/-- Any labeled `Reaches` path from a tree that silently reaches `.ret r` has empty
event trace and remains along the silent `.tau` prefix to `u`. -/
theorem reaches_inv_of_tauStar_ret {E : Effect.{0}} {R : Type} [FaultEffect E]
    {t u w : ITree E R} {r : R} {tr : List (Event E)}
    (hs : TauStar t u) (hr : u.observe = .ret r) (hreach : Reaches t tr w) :
    tr = [] ∧ TauStar w u := by
  induction hreach with
  | refl _ => exact ⟨rfl, hs⟩
  | @tau x x' _ _ htau _ ih =>
    cases hs with
    | refl => rw [htau] at hr; nomatch hr
    | step htau2 hrest =>
      rw [htau] at htau2
      injection htau2 with hEq
      subst hEq
      exact ih hrest
  | @vis x _ _ _ _ hvis _ _ _ =>
    cases hs with
    | refl => rw [hvis] at hr; nomatch hr
    | step htau _ => rw [hvis] at htau; nomatch htau

/-- Constructive `TreeSafe` proof for any tree silently reaching `.ret r`. -/
theorem treeSafe_of_tauStar_ret {E : Effect.{0}} {R : Type} [FaultEffect E]
    {t u : ITree E R} {r : R}
    (hs : TauStar t u) (hr : u.observe = .ret r) :
    TreeSafe t := by
  intro tr w hreach
  have ⟨_, hwu⟩ := reaches_inv_of_tauStar_ret hs hr hreach
  exact not_faultNow_of_tauStar_ret hwu hr

/-- Exact constructive characterization of `ReachesRet` for a tree silently reaching `.ret r`. -/
theorem reachesRet_iff_of_tauStar_ret {E : Effect.{0}} {R : Type} [FaultEffect E]
    {t u : ITree E R} {r : R}
    (hs : TauStar t u) (hr : u.observe = .ret r)
    (tr : List (Event E)) (r' : R) :
    ReachesRet t tr r' ↔ tr = [] ∧ r' = r := by
  constructor
  · rintro ⟨w, hreach, hwr⟩
    have ⟨htr, hwu⟩ := reaches_inv_of_tauStar_ret hs hr hreach
    have hEq : w = u :=
      TauStar.unique_nonTau (.refl w) hwu
        (fun _ hw => by rw [hwr] at hw; nomatch hw)
        (fun _ hw => by rw [hr] at hw; nomatch hw)
    rw [hEq, hr] at hwr
    injection hwr with hrr
    exact ⟨htr, hrr.symm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨u, Reaches.of_tauStar hs (.refl u), hr⟩

/-- Constructive Layer 1A `ITree.toPartial` refinement: any tree refines a `FaultNow` tree. -/
theorem toPartial_le_of_faultNow {E : Effect.{0}} {R : Type} [FaultEffect E]
    {a b : ITree E R} (hf : FaultNow b) :
    a.toPartial ≤ b.toPartial :=
  fun hSafeB => False.elim (hSafeB [] b (.refl b) hf)

/-- Constructive Layer 1A `ITree.toPartial` negative refinement: a `FaultNow` tree never
refines a tree silently reaching `.ret r`. -/
theorem not_toPartial_le_of_faultNow_ret {E : Effect.{0}} {R : Type} [FaultEffect E]
    {a b u : ITree E R} {r : R}
    (hfa : FaultNow a) (hsb : TauStar b u) (hbr : u.observe = .ret r) :
    ¬ (a.toPartial ≤ b.toPartial) := by
  intro hLe
  have ⟨hSafeA, _⟩ := hLe (treeSafe_of_tauStar_ret hsb hbr)
  exact hSafeA [] a (.refl a) hfa

/-- Constructive Layer 1A `ITree.toPartial` negative refinement: two trees silently returning
distinct values `r₁ ≠ r₂` never refine each other. -/
theorem not_toPartial_le_of_distinct_ret {E : Effect.{0}} {R : Type} [FaultEffect E]
    {a b u₁ u₂ : ITree E R} {r₁ r₂ : R}
    (hsa : TauStar a u₁) (har : u₁.observe = .ret r₁)
    (hsb : TauStar b u₂) (hbr : u₂.observe = .ret r₂)
    (hne : r₁ ≠ r₂) :
    ¬ (a.toPartial ≤ b.toPartial) := by
  intro hLe
  have ⟨_, hSub⟩ := hLe (treeSafe_of_tauStar_ret hsb hbr)
  have hRetA : ReachesRet a [] r₁ := (reachesRet_iff_of_tauStar_ret hsa har [] r₁).2 ⟨rfl, rfl⟩
  have hRetB : ReachesRet b [] r₁ := hSub ([], r₁) hRetA
  exact hne ((reachesRet_iff_of_tauStar_ret hsb hbr [] r₁).1 hRetB).2

/-- Constructive mutual Layer 1A `ITree.toPartial` equivalence for two MIR calls halting
with the exact same `MirOutcome`. -/
theorem mirCallTree_toPartial_equiv_of_same_halted {b₁ b₂ : CapturedMir} {f₁ f₂ : Nat}
    {args₁ args₂ : List Value} {out : MirOutcome}
    (h₁ : runMirCall b₁ f₁ args₁ = .halted out)
    (h₂ : runMirCall b₂ f₂ args₂ = .halted out) :
    (mirCallTree b₁ args₁).toPartial ≤ (mirCallTree b₂ args₂).toPartial ∧
    (mirCallTree b₂ args₂).toPartial ≤ (mirCallTree b₁ args₁).toPartial := by
  have ⟨u₁, hTau₁, hObs₁⟩ := runMirSteps_halted_to_tauStar b₁ f₁ (initExecState b₁ args₁) out h₁
  have ⟨u₂, hTau₂, hObs₂⟩ := runMirSteps_halted_to_tauStar b₂ f₂ (initExecState b₂ args₂) out h₂
  refine ⟨fun _ => ⟨treeSafe_of_tauStar_ret hTau₁ hObs₁, fun ⟨tr, r⟩ hRet => ?_⟩,
          fun _ => ⟨treeSafe_of_tauStar_ret hTau₂ hObs₂, fun ⟨tr, r⟩ hRet => ?_⟩⟩
  · exact (reachesRet_iff_of_tauStar_ret hTau₂ hObs₂ tr r).2
      ((reachesRet_iff_of_tauStar_ret hTau₁ hObs₁ tr r).1 hRet)
  · exact (reachesRet_iff_of_tauStar_ret hTau₁ hObs₁ tr r).2
      ((reachesRet_iff_of_tauStar_ret hTau₂ hObs₂ tr r).1 hRet)

/-- Constructive Layer 1A `ITree.toPartial` refinement against a `.ub`-faulting MIR call. -/
theorem mirCallTree_toPartial_refines_ub {bImpl bSpec : CapturedMir} {fSpec : Nat}
    {argsImpl argsSpec : List Value}
    (hUb : runMirCall bSpec fSpec argsSpec = .faulted .ub) :
    (mirCallTree bImpl argsImpl).toPartial ≤ (mirCallTree bSpec argsSpec).toPartial :=
  toPartial_le_of_faultNow (runMirCall_ub_faultNow hUb)

private theorem halted_eq_of_mirExactOutcomeRefines {o₁ o₂ : MirOutcome}
    (h : MirExactOutcomeRefines (classifyMirOutcomeExact (.halted o₁))
      (classifyMirOutcomeExact (.halted o₂))) : o₁ = o₂ := by
  cases o₁ with
  | normal vm₁ =>
    cases o₂ with
    | normal vm₂ => exact congrArg Outcome.normal h
    | abort => exact False.elim h
    | panic => exact False.elim h
  | abort =>
    cases o₂ with
    | abort => rfl
    | normal _ => exact False.elim h
    | panic => nomatch h
  | panic =>
    cases o₂ with
    | panic => rfl
    | normal _ => exact False.elim h
    | abort => nomatch h

/-- **General Operational Equivalence (Constructive Layer 1A `ITree.toPartial`)**:
For ANY two settled `runMirCall` executions (`bSpec` and `bImpl`), strategy-exact outcome
refinement `MirExactOutcomeRefines` holds *if and only if* their coinductive `mirCallTree`
interpretations satisfy Layer 1A Smyth refinement `ITree.toPartial ≤`. -/
theorem mirExactOutcomeRefines_iff_mirCallTree_toPartial_le
    {bSpec bImpl : CapturedMir} {fSpec fImpl : Nat} {argsSpec argsImpl : List Value}
    (hSpecSettled : SettledExec (runMirCall bSpec fSpec argsSpec))
    (hImplSettled : SettledExec (runMirCall bImpl fImpl argsImpl)) :
    MirExactOutcomeRefines
      (classifyMirOutcomeExact (runMirCall bSpec fSpec argsSpec))
      (classifyMirOutcomeExact (runMirCall bImpl fImpl argsImpl))
      ↔ (mirCallTree bImpl argsImpl).toPartial ≤ (mirCallTree bSpec argsSpec).toPartial := by
  generalize hS : runMirCall bSpec fSpec argsSpec = rSpec at hSpecSettled ⊢
  generalize hI : runMirCall bImpl fImpl argsImpl = rImpl at hImplSettled ⊢
  cases rSpec with
  | running _ => exact False.elim hSpecSettled
  | faulted fkS =>
    cases fkS with
    | unsupported => exact False.elim hSpecSettled
    | outOfFuel => exact False.elim hSpecSettled
    | ub =>
      exact ⟨fun _ => mirCallTree_toPartial_refines_ub hS, fun _ => trivial⟩
  | halted oSpec =>
    have ⟨uS, hTauS, hObsS⟩ := runMirSteps_halted_to_tauStar bSpec fSpec _ oSpec hS
    cases rImpl with
    | running _ => exact False.elim hImplSettled
    | faulted fkI =>
      cases fkI with
      | unsupported => exact False.elim hImplSettled
      | outOfFuel => exact False.elim hImplSettled
      | ub =>
        constructor
        · intro hRef
          cases oSpec <;> exact False.elim hRef
        · intro hLe
          exact False.elim (not_toPartial_le_of_faultNow_ret (runMirCall_ub_faultNow hI) hTauS hObsS hLe)
    | halted oImpl =>
      have ⟨uI, hTauI, hObsI⟩ := runMirSteps_halted_to_tauStar bImpl fImpl _ oImpl hI
      constructor
      · intro hRef
        have hEq := halted_eq_of_mirExactOutcomeRefines hRef
        subst hEq
        exact (mirCallTree_toPartial_equiv_of_same_halted hI hS).1
      · intro hLe
        have ⟨_, hSub⟩ := hLe (treeSafe_of_tauStar_ret hTauS hObsS)
        have hRetI : ReachesRet (mirCallTree bImpl argsImpl) [] oImpl :=
          (reachesRet_iff_of_tauStar_ret hTauI hObsI [] oImpl).2 ⟨rfl, rfl⟩
        have hRetS : ReachesRet (mirCallTree bSpec argsSpec) [] oImpl := hSub ([], oImpl) hRetI
        have hEq : oImpl = oSpec := ((reachesRet_iff_of_tauStar_ret hTauS hObsS [] oImpl).1 hRetS).2
        subst hEq
        exact mirExactOutcomeRefines_refl _

/-! ### 2.1 Coinductive `Anneal.ITree.Eutt` & `WeakRef` Bridge Corollaries -/

/-- `TauStar` to a `.ret out` node implies `Eutt t (ITree.ret out)`. -/
theorem eutt_ret_of_tauStar {E : Effect.{0}} {R : Type}
    {t u : ITree E R} {r : R}
    (hs : TauStar t u) (hr : u.observe = .ret r) :
    Eutt t (ITree.ret r) := by
  rw [Eutt.eq_def]
  exact Or.inl ⟨u, ITree.ret r, r, hs, .refl _, hr, ITree.observe_ret r⟩

/-- Halted `runMirCall` implies `Eutt (mirCallTree body args) (ITree.ret out)`. -/
theorem runMirCall_halted_eutt {body : CapturedMir} {fuel : Nat}
    {args : List Value} {out : MirOutcome}
    (h : runMirCall body fuel args = .halted out) :
    Eutt (mirCallTree body args) (ITree.ret out) :=
  let ⟨_, hTau, hObs⟩ := runMirSteps_halted_to_tauStar body fuel (initExecState body args) out h
  eutt_ret_of_tauStar hTau hObs

/-- Any tree refines a tree that immediately faults (`FaultNow b → WeakRef a b`). -/
theorem weakRef_of_faultNow {E : Effect.{0}} {R : Type} [FaultEffect E]
    {a b : ITree E R} (hf : FaultNow b) : WeakRef a b := by
  rw [WeakRef.eq_def]
  intro hnb
  exact False.elim (hnb hf)

/-- A faulting tree does not refine a tree that silently returns `r` under `WeakRef`. -/
theorem not_weakRef_of_faultNow_ret {E : Effect.{0}} {R : Type} [FaultEffect E]
    {a b u : ITree E R} {r : R}
    (hfa : FaultNow a) (hsb : TauStar b u) (hbr : u.observe = .ret r) :
    ¬ WeakRef a b := by
  intro hRef
  rw [WeakRef.eq_def] at hRef
  exact (hRef (not_faultNow_of_tauStar_ret hsb hbr)).1 hfa

/-- Two trees silently returning distinct values `r₁ ≠ r₂` do not refine under `WeakRef`. -/
theorem not_weakRef_of_distinct_ret {E : Effect.{0}} {R : Type} [FaultEffect E]
    {a b u₁ u₂ : ITree E R} {r₁ r₂ : R}
    (hsa : TauStar a u₁) (har : u₁.observe = .ret r₁)
    (hsb : TauStar b u₂) (hbr : u₂.observe = .ret r₂)
    (hne : r₁ ≠ r₂) :
    ¬ WeakRef a b := by
  intro hRef
  rw [WeakRef.eq_def] at hRef
  have ⟨_, hRetSim, _⟩ := hRef (not_faultNow_of_tauStar_ret hsb hbr)
  have ⟨b', hsb', hb'r⟩ := hRetSim u₁ r₁ hsa har
  have hEq : u₂ = b' :=
    TauStar.unique_nonTau hsb hsb'
      (fun _ hw => by rw [hbr] at hw; nomatch hw)
      (fun _ hw => by rw [hb'r] at hw; nomatch hw)
  rw [hEq, hb'r] at hbr
  injection hbr with hrr
  exact hne hrr

/-- Two halting MIR calls returning the same `MirOutcome` are mutually `WeakRef`. -/
theorem mirCallTree_weakRef_equiv_of_same_halted {b₁ b₂ : CapturedMir} {f₁ f₂ : Nat}
    {args₁ args₂ : List Value} {out : MirOutcome}
    (h₁ : runMirCall b₁ f₁ args₁ = .halted out)
    (h₂ : runMirCall b₂ f₂ args₂ = .halted out) :
    WeakRef (mirCallTree b₁ args₁) (mirCallTree b₂ args₂) ∧
    WeakRef (mirCallTree b₂ args₂) (mirCallTree b₁ args₁) := by
  have he₁ := runMirCall_halted_eutt h₁
  have he₂ := runMirCall_halted_eutt h₂
  exact ⟨WeakRef.trans he₁.toWeakRef he₂.symm.toWeakRef,
         WeakRef.trans he₂.toWeakRef he₁.symm.toWeakRef⟩

/-- Any MIR call refines a `.ub`-faulting MIR call under coinductive `WeakRef`. -/
theorem mirCallTree_weakRef_refines_ub {bImpl bSpec : CapturedMir} {fSpec : Nat}
    {argsImpl argsSpec : List Value}
    (hUb : runMirCall bSpec fSpec argsSpec = .faulted .ub) :
    WeakRef (mirCallTree bImpl argsImpl) (mirCallTree bSpec argsSpec) :=
  weakRef_of_faultNow (runMirCall_ub_faultNow hUb)

/-- **General Operational Equivalence (Coinductive `Anneal.ITree.WeakRef`)**:
For ANY two settled `runMirCall` executions (`bSpec` and `bImpl`), strategy-exact outcome
refinement `MirExactOutcomeRefines` holds *if and only if* `WeakRef` holds between their
coinductive `mirCallTree`s. -/
theorem mirExactOutcomeRefines_iff_mirCallTree_weakRef
    {bSpec bImpl : CapturedMir} {fSpec fImpl : Nat} {argsSpec argsImpl : List Value}
    (hSpecSettled : SettledExec (runMirCall bSpec fSpec argsSpec))
    (hImplSettled : SettledExec (runMirCall bImpl fImpl argsImpl)) :
    MirExactOutcomeRefines
      (classifyMirOutcomeExact (runMirCall bSpec fSpec argsSpec))
      (classifyMirOutcomeExact (runMirCall bImpl fImpl argsImpl))
      ↔ WeakRef (mirCallTree bImpl argsImpl) (mirCallTree bSpec argsSpec) := by
  generalize hS : runMirCall bSpec fSpec argsSpec = rSpec at hSpecSettled ⊢
  generalize hI : runMirCall bImpl fImpl argsImpl = rImpl at hImplSettled ⊢
  cases rSpec with
  | running _ => exact False.elim hSpecSettled
  | faulted fkS =>
    cases fkS with
    | unsupported => exact False.elim hSpecSettled
    | outOfFuel => exact False.elim hSpecSettled
    | ub =>
      exact ⟨fun _ => mirCallTree_weakRef_refines_ub hS, fun _ => trivial⟩
  | halted oSpec =>
    have ⟨uS, hTauS, hObsS⟩ := runMirSteps_halted_to_tauStar bSpec fSpec _ oSpec hS
    cases rImpl with
    | running _ => exact False.elim hImplSettled
    | faulted fkI =>
      cases fkI with
      | unsupported => exact False.elim hImplSettled
      | outOfFuel => exact False.elim hImplSettled
      | ub =>
        constructor
        · intro hRef
          cases oSpec <;> exact False.elim hRef
        · intro hW
          exact False.elim (not_weakRef_of_faultNow_ret (runMirCall_ub_faultNow hI) hTauS hObsS hW)
    | halted oImpl =>
      have ⟨uI, hTauI, hObsI⟩ := runMirSteps_halted_to_tauStar bImpl fImpl _ oImpl hI
      constructor
      · intro hRef
        have hEq := halted_eq_of_mirExactOutcomeRefines hRef
        subst hEq
        exact (mirCallTree_weakRef_equiv_of_same_halted hI hS).1
      · intro hW
        rw [WeakRef.eq_def] at hW
        have ⟨_, hRetSim, _⟩ := hW (not_faultNow_of_tauStar_ret hTauS hObsS)
        have ⟨b', hsb', hb'r⟩ := hRetSim uI oImpl hTauI hObsI
        have hU : uS = b' :=
          TauStar.unique_nonTau hTauS hsb'
            (fun _ hw => by rw [hObsS] at hw; nomatch hw)
            (fun _ hw => by rw [hb'r] at hw; nomatch hw)
        rw [hU, hb'r] at hObsS
        injection hObsS with hEq
        subst hEq
        exact mirExactOutcomeRefines_refl _

/-! ## 3. Canonical `CapturedMir` Arithmetic Bodies & Exact `stepMirState` Evaluation -/

/-- Unsigned binary arithmetic operation kind covered by overflow-trap refinement. -/
inductive ArithKind : Type where
  | add
  | sub
  | mul
  deriving DecidableEq, Repr

/-- Unchecked MIR `BinOp` (`*Unchecked`, UB on overflow/underflow). -/
def ArithKind.uncheckedBinOp : ArithKind → BinOp
  | .add => .addUnchecked
  | .sub => .subUnchecked
  | .mul => .mulUnchecked

/-- Checked MIR `BinOp` (`*WithOverflow`, returning `(T, bool)`). -/
def ArithKind.checkedBinOp : ArithKind → BinOp
  | .add => .addWithOverflow
  | .sub => .subWithOverflow
  | .mul => .mulWithOverflow

/-- Wrapping MIR `BinOp` (two's-complement modular wrap, never traps). -/
def ArithKind.wrappingBinOp : ArithKind → BinOp
  | .add => .add
  | .sub => .sub
  | .mul => .mul

/-- MIR `Ty` for an unsigned integer type `u : UintTy`. -/
def uintTy (u : UintTy) : Ty :=
  { kind := .uint u, layoutIdx := 0 }

/-- MIR `Ty` for `bool`. -/
def boolMirTy : Ty :=
  { kind := .bool, layoutIdx := 0 }

/-- MIR `Ty` for checked-arithmetic result tuple `(u, bool)`. -/
def uintBoolPairTy (u : UintTy) : Ty :=
  { kind := .tuple [.uint u, .bool], layoutIdx := 0 }

/-- Constant scalar operand of unsigned type `u` holding bit pattern `n`. -/
def uintConstOp (u : UintTy) (n : Nat) : Operand :=
  .constant { ty := uintTy u, val := .scalar (.int ⟨n, uintBytes u⟩) }

/-- Canonical two-argument unsigned scalar input list `[a, b]` at width `uintBytes u`. -/
def uintArgs2 (u : UintTy) (a b : Nat) : List Value :=
  [.scalar ⟨a, uintBytes u⟩, .scalar ⟨b, uintBytes u⟩]

private def canonLayout : TypeLayout := {
  size := { bytes := 1 }
  align := { bytes := 1 }
  backendRepr := .memory
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

private def canonFnAbi : FnAbi := {
  args := []
  ret := { layout := canonLayout, mode := .direct }
  conv := .rust
  canUnwind := true
}

private def mkLocalDecl (mutability : Mutability) (ty : Ty) : LocalDecl :=
  { mutability, ty, debugName := none }

private def mkMirStmt (kind : StatementKind) : Statement :=
  { kind, span := "OverflowTrapRefinement.lean" }

private def mkMirTerm (kind : TerminatorKind) : Terminator :=
  { kind, span := "OverflowTrapRefinement.lean" }

private def localPlace (idx : Nat) : Place :=
  { local_ := idx, projection := [] }

private def mkCanonBody (defPath : DefPath) (argCount : Nat)
    (localDecls : List LocalDecl) (basicBlocks : List BasicBlockData) : CapturedMir := {
  defPath, argCount, localDecls, basicBlocks
  role := .subject
  phase := .runtimePostCleanup
  fnAbi := canonFnAbi
  layouts := emptyLayoutTable
  allocations := []
}

/-- Initial `Memory` shared identically by every canonical body created via `mkCanonBody`. -/
def canonInitMemory : Memory := {
  nextAllocId := 0
  globals := []
  borrows := []
  nextTag := 1
  callees := []
  callStack := []
  activeCallee := none
  traitImpls := []
}

/-- Canonical unchecked unsigned binary arithmetic `CapturedMir` body:
`bb0: _0 = BinOp::{add,sub,mul}Unchecked(copy _1, copy _2); return`. -/
def mkUncheckedArithBody (u : UintTy) (op : ArithKind) : CapturedMir :=
  mkCanonBody "anneal::arith::unchecked" 2
    [ mkLocalDecl .mut (uintTy u)
    , mkLocalDecl .not (uintTy u)
    , mkLocalDecl .not (uintTy u) ]
    [ { statements :=
          [ mkMirStmt (.assign (localPlace 0)
              (.binaryOp op.uncheckedBinOp
                (.copy (localPlace 1)) (.copy (localPlace 2)))) ]
        terminator := mkMirTerm .return_
        isCleanup := false } ]

/-- Canonical wrapping unsigned binary arithmetic `CapturedMir` body:
`bb0: _0 = BinOp::{add,sub,mul}(copy _1, copy _2); return`. -/
def mkWrappingArithBody (u : UintTy) (op : ArithKind) : CapturedMir :=
  mkCanonBody "anneal::arith::wrapping" 2
    [ mkLocalDecl .mut (uintTy u)
    , mkLocalDecl .not (uintTy u)
    , mkLocalDecl .not (uintTy u) ]
    [ { statements :=
          [ mkMirStmt (.assign (localPlace 0)
              (.binaryOp op.wrappingBinOp
                (.copy (localPlace 1)) (.copy (localPlace 2)))) ]
        terminator := mkMirTerm .return_
        isCleanup := false } ]

/-- Canonical checked unsigned binary arithmetic `CapturedMir` body (`-C overflow-checks=on`):
- `bb0`: `StorageLive(_3); _3 = BinOp::{add,sub,mul}WithOverflow(copy _1, copy _2);`
         `assert(!move (_3.1)) -> [success: bb1, unwind: unwind]`
- `bb1`: `_0 = move (_3.0); StorageDead(_3); return` -/
def mkCheckedArithBody (u : UintTy) (op : ArithKind) (unwind : UnwindAction) : CapturedMir :=
  mkCanonBody "anneal::arith::checked" 2
    [ mkLocalDecl .mut (uintTy u)
    , mkLocalDecl .not (uintTy u)
    , mkLocalDecl .not (uintTy u)
    , mkLocalDecl .mut (uintBoolPairTy u) ]
    [ { statements :=
          [ mkMirStmt (.storageLive 3)
          , mkMirStmt (.assign (localPlace 3)
              (.binaryOp op.checkedBinOp
                (.copy (localPlace 1)) (.copy (localPlace 2)))) ]
        terminator :=
          mkMirTerm (.assert
            (.move { local_ := 3, projection := [.field 1 boolMirTy] })
            false 1 unwind)
        isCleanup := false }
    , { statements :=
          [ mkMirStmt (.assign (localPlace 0)
              (.use (.move { local_ := 3, projection := [.field 0 (uintTy u)] })))
          , mkMirStmt (.storageDead 3) ]
        terminator := mkMirTerm .return_
        isCleanup := false } ]

/-- Composite multi-statement unchecked `add_scaled` (`a + k * b`) `CapturedMir` body:
`bb0: StorageLive(_3); _3 = MulUnchecked(const k, copy _2);`
`     _0 = AddUnchecked(copy _1, copy _3); StorageDead(_3); return`. -/
def mkUncheckedAddScaledBody (u : UintTy) (k : Nat) : CapturedMir :=
  mkCanonBody "anneal::arith::unchecked_add_scaled" 2
    [ mkLocalDecl .mut (uintTy u)
    , mkLocalDecl .not (uintTy u)
    , mkLocalDecl .not (uintTy u)
    , mkLocalDecl .mut (uintTy u) ]
    [ { statements :=
          [ mkMirStmt (.storageLive 3)
          , mkMirStmt (.assign (localPlace 3)
              (.binaryOp .mulUnchecked (uintConstOp u k) (.copy (localPlace 2))))
          , mkMirStmt (.assign (localPlace 0)
              (.binaryOp .addUnchecked (.copy (localPlace 1)) (.copy (localPlace 3))))
          , mkMirStmt (.storageDead 3) ]
        terminator := mkMirTerm .return_
        isCleanup := false } ]

/-- Composite multi-statement checked `add_scaled` (`a + k * b`) `CapturedMir` body:
- `bb0`: `StorageLive(_3); _3 = MulWithOverflow(const k, copy _2); assert(!move (_3.1)) -> bb1`
- `bb1`: `StorageLive(_4); _4 = move (_3.0); StorageDead(_3); StorageLive(_5);`
         `_5 = AddWithOverflow(copy _1, copy _4); assert(!move (_5.1)) -> bb2`
- `bb2`: `_0 = move (_5.0); StorageDead(_5); StorageDead(_4); return` -/
def mkCheckedAddScaledBody (u : UintTy) (k : Nat) (unwind : UnwindAction) : CapturedMir :=
  mkCanonBody "anneal::arith::checked_add_scaled" 2
    [ mkLocalDecl .mut (uintTy u)
    , mkLocalDecl .not (uintTy u)
    , mkLocalDecl .not (uintTy u)
    , mkLocalDecl .mut (uintBoolPairTy u)
    , mkLocalDecl .mut (uintTy u)
    , mkLocalDecl .mut (uintBoolPairTy u) ]
    [ { statements :=
          [ mkMirStmt (.storageLive 3)
          , mkMirStmt (.assign (localPlace 3)
              (.binaryOp .mulWithOverflow (uintConstOp u k) (.copy (localPlace 2)))) ]
        terminator :=
          mkMirTerm (.assert
            (.move { local_ := 3, projection := [.field 1 boolMirTy] })
            false 1 unwind)
        isCleanup := false }
    , { statements :=
          [ mkMirStmt (.storageLive 4)
          , mkMirStmt (.assign (localPlace 4)
              (.use (.move { local_ := 3, projection := [.field 0 (uintTy u)] })))
          , mkMirStmt (.storageDead 3)
          , mkMirStmt (.storageLive 5)
          , mkMirStmt (.assign (localPlace 5)
              (.binaryOp .addWithOverflow (.copy (localPlace 1)) (.copy (localPlace 4)))) ]
        terminator :=
          mkMirTerm (.assert
            (.move { local_ := 5, projection := [.field 1 boolMirTy] })
            false 2 unwind)
        isCleanup := false }
    , { statements :=
          [ mkMirStmt (.assign (localPlace 0)
              (.use (.move { local_ := 5, projection := [.field 0 (uintTy u)] })))
          , mkMirStmt (.storageDead 5)
          , mkMirStmt (.storageDead 4) ]
        terminator := mkMirTerm .return_
        isCleanup := false } ]

/-! ### 3.1 Constructive `Nat.ble` & `evalScalarBinOp` Arithmetic Helpers -/

private theorem nat_ble_false_of_lt {a b : Nat} (h : a < b) :
    Nat.ble b a = false := by
  cases hb : Nat.ble b a with
  | false => rfl
  | true => exact False.elim (Nat.not_le_of_gt h (Nat.le_of_ble_eq_true hb))

private theorem nat_lt_of_ble_false {a b : Nat} (h : Nat.ble b a = false) :
    a < b :=
  Nat.lt_of_not_le (fun hLe => by
    rw [Nat.ble_eq_true_of_le hLe] at h
    nomatch h)

private theorem evalScalarBinOp_uint_addUnchecked_ub
    {u : UintTy} {a b : Nat} (locals : List LocalSlot) (mem : Memory)
    (hOv : modPow2 (uintWidth u) ≤ a + b) :
    evalScalarBinOp .addUnchecked ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem false =
      .ub := by
  have hB : Nat.ble (scalarModulus (uintBytes u)) (Nat.add a b) = true := by
    rw [scalarModulus_uintBytes]
    exact Nat.ble_eq_true_of_le hOv
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl, hB]

private theorem evalScalarBinOp_uint_subUnchecked_ub
    {u : UintTy} {a b : Nat} (locals : List LocalSlot) (mem : Memory)
    (hUnd : a < b) :
    evalScalarBinOp .subUnchecked ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem false =
      .ub := by
  have hB : Nat.ble b a = false := nat_ble_false_of_lt hUnd
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl, hB]

private theorem evalScalarBinOp_uint_mulUnchecked_ub
    {u : UintTy} {a b : Nat} (locals : List LocalSlot) (mem : Memory)
    (hOv : modPow2 (uintWidth u) ≤ a * b) :
    evalScalarBinOp .mulUnchecked ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem false =
      .ub := by
  have hB : Nat.ble (scalarModulus (uintBytes u)) (Nat.mul a b) = true := by
    rw [scalarModulus_uintBytes]
    exact Nat.ble_eq_true_of_le hOv
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl, hB]

private theorem applyUnwindAction_strategy (s : MachineState) (locals : List LocalSlot)
    (strat : PanicStrategy) :
    applyUnwindAction s locals canonInitMemory strat.toUnwindAction =
      .halted strat.toTrapOutcome := by
  cases strat <;> rfl

private def mkCanonState (bb st : Nat) (locals : List LocalSlot) : MachineState :=
  { frame := { blockIdx := bb, stmtIdx := st, locals := locals }, memory := canonInitMemory }

private theorem runMirSteps_step_tau {body : CapturedMir} {fuel : Nat}
    {s : MachineState} {next : MirExecState}
    (h : stepMirState body (.running s) = .tau next) :
    runMirSteps body (fuel + 1) (.running s) = runMirSteps body fuel next := by
  conv => lhs; unfold runMirSteps
  dsimp only
  rw [h]

private theorem runMirSteps_step_ub {body : CapturedMir} {fuel : Nat}
    {s : MachineState} {k : PEmpty → MirExecState}
    (h : stepMirState body (.running s) = .vis (.inl (.fail .ub)) k) :
    runMirSteps body (fuel + 1) (.running s) = .faulted .ub := by
  unfold runMirSteps
  dsimp only
  rw [h]

private theorem evalStmt_assign_local_step
    (s : MachineState) (dst : Nat) (rv : Rvalue)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (val : Value) (locals₁ locals₂ : List LocalSlot)
    (hRv : evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ canonInitMemory)
    (hLive : match get? locals₁ dst with | some .uninit => True | some (.init _) => True | _ => False)
    (hSet : set? locals₁ dst (.init val) = some locals₂) :
    evalStmt s (mkMirStmt (.assign (localPlace dst) rv)) localDecls layouts =
      MirStepNode.step (advanceStmt s locals₂ canonInitMemory) := by
  unfold evalStmt
  dsimp only [mkMirStmt, localPlace, stripLeadingOpaqueCast]
  rw [hRv]
  dsimp only
  cases hGet : get? locals₁ dst with
  | none => rw [hGet] at hLive; exact False.elim hLive
  | some slot =>
    rw [hGet] at hLive
    cases slot with
    | dead => exact False.elim hLive
    | uninit =>
      dsimp only
      rw [hSet]
      rfl
    | init _ =>
      dsimp only
      rw [hSet]
      rfl

private theorem evalStmt_assign_ub
    (s : MachineState) (dst : Place) (rv : Rvalue)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hRv : evalRvalue s.frame.locals rv s.memory localDecls layouts = .ub) :
    evalStmt s (mkMirStmt (.assign dst rv)) localDecls layouts = MirStepNode.fail .ub := by
  unfold evalStmt
  dsimp only [mkMirStmt]
  rw [hRv]

/-! ### 3.2 Exact `stepMirState` Evaluation Lemmas for Unchecked & Checked Bodies -/

/-- Exact evaluation of `mkUncheckedArithBody u .add` when `a + b < 2^w`. -/
theorem runMirCall_unchecked_add_ok (u : UintTy) (a b : Nat)
    (hNoOv : a + b < modPow2 (uintWidth u)) :
    runMirCall (mkUncheckedArithBody u .add) 2 (uintArgs2 u a b) =
      .halted (.normal (.scalar ⟨a + b, uintBytes u⟩, canonInitMemory)) := by
  have hBin := evalScalarBinOp_uint_addUnchecked (u := u) (a := a) (b := b)
    [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩)]
    canonInitMemory hNoOv
  rw [wrapVal_of_lt hNoOv] at hBin
  have hStep1 : stepMirState (mkUncheckedArithBody u .add)
      (.running (initMachineState (mkUncheckedArithBody u .add) (uintArgs2 u a b))) =
      .tau (.running (mkCanonState 0 1
        [.init (.scalar ⟨a + b, uintBytes u⟩),
         .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩)])) :=
    evalStmt_assign_local_step _ 0 _ _ _ _ _ _ hBin trivial rfl
  rw [runMirCall, initExecState, runMirSteps_step_tau hStep1]
  rfl

/-- Exact evaluation of `mkUncheckedArithBody u .add` when `2^w ≤ a + b` (UB). -/
theorem runMirCall_unchecked_add_ub (u : UintTy) (a b : Nat)
    (hOv : modPow2 (uintWidth u) ≤ a + b) :
    runMirCall (mkUncheckedArithBody u .add) 2 (uintArgs2 u a b) = .faulted .ub := by
  have hBin := evalScalarBinOp_uint_addUnchecked_ub (u := u) (a := a) (b := b)
    [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩)]
    canonInitMemory hOv
  have hStep1 : stepMirState (mkUncheckedArithBody u .add)
      (.running (initMachineState (mkUncheckedArithBody u .add) (uintArgs2 u a b))) =
      MirStepNode.fail .ub :=
    evalStmt_assign_ub _ (localPlace 0) _ _ _ hBin
  rw [runMirCall, initExecState]
  exact runMirSteps_step_ub hStep1

/-- Exact evaluation of `mkCheckedArithBody u .add strat.toUnwindAction` when `a + b < 2^w`. -/
theorem runMirCall_checked_add_ok (u : UintTy) (strat : PanicStrategy) (a b : Nat)
    (hNoOv : a + b < modPow2 (uintWidth u)) :
    runMirCall (mkCheckedArithBody u .add strat.toUnwindAction) 6 (uintArgs2 u a b) =
      .halted (.normal (.scalar ⟨a + b, uintBytes u⟩, canonInitMemory)) := by
  have hBin := evalScalarBinOp_uint_addWithOverflow (u := u) (a := a) (b := b)
    [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩), .uninit]
    canonInitMemory
  rw [wrapVal_of_lt hNoOv, nat_ble_false_of_lt hNoOv] at hBin
  have hStep1 : stepMirState (mkCheckedArithBody u .add strat.toUnwindAction)
      (.running (initMachineState (mkCheckedArithBody u .add strat.toUnwindAction) (uintArgs2 u a b))) =
      .tau (.running (mkCanonState 0 1
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩), .uninit])) := rfl
  have hStep2 : stepMirState (mkCheckedArithBody u .add strat.toUnwindAction)
      (.running (mkCanonState 0 1
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩), .uninit])) =
      .tau (.running (mkCanonState 0 2
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩),
         .init (.aggregate 0 [.scalar ⟨a + b, uintBytes u⟩, .scalar ⟨0, 1⟩])])) :=
    evalStmt_assign_local_step _ 3 _ _ _ _ _ _ hBin trivial rfl
  rw [runMirCall, initExecState, runMirSteps_step_tau hStep1, runMirSteps_step_tau hStep2]
  rfl

/-- Exact evaluation of `mkCheckedArithBody u .add strat.toUnwindAction` when `2^w ≤ a + b`
(deterministic trap: `.abort` under `.abort`, `.panic` under `.unwind`). -/
theorem runMirCall_checked_add_trap (u : UintTy) (strat : PanicStrategy) (a b : Nat)
    (hOv : modPow2 (uintWidth u) ≤ a + b) :
    runMirCall (mkCheckedArithBody u .add strat.toUnwindAction) 6 (uintArgs2 u a b) =
      .halted strat.toTrapOutcome := by
  have hBin := evalScalarBinOp_uint_addWithOverflow (u := u) (a := a) (b := b)
    [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩), .uninit]
    canonInitMemory
  rw [Nat.ble_eq_true_of_le hOv] at hBin
  have hStep1 : stepMirState (mkCheckedArithBody u .add strat.toUnwindAction)
      (.running (initMachineState (mkCheckedArithBody u .add strat.toUnwindAction) (uintArgs2 u a b))) =
      .tau (.running (mkCanonState 0 1
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩), .uninit])) := rfl
  have hStep2 : stepMirState (mkCheckedArithBody u .add strat.toUnwindAction)
      (.running (mkCanonState 0 1
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩), .uninit])) =
      .tau (.running (mkCanonState 0 2
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩),
         .init (.aggregate 0
           [.scalar ⟨wrapVal (uintWidth u) (a + b), uintBytes u⟩, .scalar ⟨1, 1⟩])])) :=
    evalStmt_assign_local_step _ 3 _ _ _ _ _ _ hBin trivial rfl
  rw [runMirCall, initExecState, runMirSteps_step_tau hStep1, runMirSteps_step_tau hStep2]
  cases strat <;> rfl

/-- Exact evaluation of `mkUncheckedArithBody u .sub` when `a < 2^w` and `b ≤ a`. -/
theorem runMirCall_unchecked_sub_ok (u : UintTy) (a b : Nat)
    (ha : a < modPow2 (uintWidth u)) (hLe : b ≤ a) :
    runMirCall (mkUncheckedArithBody u .sub) 2 (uintArgs2 u a b) =
      .halted (.normal (.scalar ⟨a - b, uintBytes u⟩, canonInitMemory)) := by
  have hDiff : a - b < modPow2 (uintWidth u) := Nat.lt_of_le_of_lt (Nat.sub_le a b) ha
  have hBin := evalScalarBinOp_uint_subUnchecked (u := u) (a := a) (b := b)
    [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩)]
    canonInitMemory ha hLe
  rw [← wrapVal_sub_of_le hLe ha, wrapVal_of_lt hDiff] at hBin
  have hStep1 : stepMirState (mkUncheckedArithBody u .sub)
      (.running (initMachineState (mkUncheckedArithBody u .sub) (uintArgs2 u a b))) =
      .tau (.running (mkCanonState 0 1
        [.init (.scalar ⟨a - b, uintBytes u⟩),
         .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩)])) :=
    evalStmt_assign_local_step _ 0 _ _ _ _ _ _ hBin trivial rfl
  rw [runMirCall, initExecState, runMirSteps_step_tau hStep1]
  rfl

/-- Exact evaluation of `mkUncheckedArithBody u .sub` when `a < b` (underflow UB). -/
theorem runMirCall_unchecked_sub_ub (u : UintTy) (a b : Nat) (hUnd : a < b) :
    runMirCall (mkUncheckedArithBody u .sub) 2 (uintArgs2 u a b) = .faulted .ub := by
  have hBin := evalScalarBinOp_uint_subUnchecked_ub (u := u) (a := a) (b := b)
    [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩)]
    canonInitMemory hUnd
  have hStep1 : stepMirState (mkUncheckedArithBody u .sub)
      (.running (initMachineState (mkUncheckedArithBody u .sub) (uintArgs2 u a b))) =
      MirStepNode.fail .ub :=
    evalStmt_assign_ub _ (localPlace 0) _ _ _ hBin
  rw [runMirCall, initExecState]
  exact runMirSteps_step_ub hStep1

/-- Exact evaluation of `mkCheckedArithBody u .sub strat.toUnwindAction` when
`a < 2^w`, `b < 2^w`, and `b ≤ a`. -/
theorem runMirCall_checked_sub_ok (u : UintTy) (strat : PanicStrategy) (a b : Nat)
    (ha : a < modPow2 (uintWidth u)) (hb : b < modPow2 (uintWidth u)) (hLe : b ≤ a) :
    runMirCall (mkCheckedArithBody u .sub strat.toUnwindAction) 6 (uintArgs2 u a b) =
      .halted (.normal (.scalar ⟨a - b, uintBytes u⟩, canonInitMemory)) := by
  have hDiff : a - b < modPow2 (uintWidth u) := Nat.lt_of_le_of_lt (Nat.sub_le a b) ha
  have hBin := evalScalarBinOp_uint_subWithOverflow (u := u) (a := a) (b := b)
    [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩), .uninit]
    canonInitMemory ha hb
  rw [← wrapVal_sub_of_le hLe ha, wrapVal_of_lt hDiff, Nat.ble_eq_true_of_le hLe] at hBin
  have hStep1 : stepMirState (mkCheckedArithBody u .sub strat.toUnwindAction)
      (.running (initMachineState (mkCheckedArithBody u .sub strat.toUnwindAction) (uintArgs2 u a b))) =
      .tau (.running (mkCanonState 0 1
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩), .uninit])) := rfl
  have hStep2 : stepMirState (mkCheckedArithBody u .sub strat.toUnwindAction)
      (.running (mkCanonState 0 1
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩), .uninit])) =
      .tau (.running (mkCanonState 0 2
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩),
         .init (.aggregate 0 [.scalar ⟨a - b, uintBytes u⟩, .scalar ⟨0, 1⟩])])) :=
    evalStmt_assign_local_step _ 3 _ _ _ _ _ _ hBin trivial rfl
  rw [runMirCall, initExecState, runMirSteps_step_tau hStep1, runMirSteps_step_tau hStep2]
  rfl

/-- Exact evaluation of `mkCheckedArithBody u .sub strat.toUnwindAction` when
`a < 2^w`, `b < 2^w`, and `a < b` (deterministic trap). -/
theorem runMirCall_checked_sub_trap (u : UintTy) (strat : PanicStrategy) (a b : Nat)
    (ha : a < modPow2 (uintWidth u)) (hb : b < modPow2 (uintWidth u)) (hUnd : a < b) :
    runMirCall (mkCheckedArithBody u .sub strat.toUnwindAction) 6 (uintArgs2 u a b) =
      .halted strat.toTrapOutcome := by
  have hBin := evalScalarBinOp_uint_subWithOverflow (u := u) (a := a) (b := b)
    [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩), .uninit]
    canonInitMemory ha hb
  rw [nat_ble_false_of_lt hUnd] at hBin
  have hStep1 : stepMirState (mkCheckedArithBody u .sub strat.toUnwindAction)
      (.running (initMachineState (mkCheckedArithBody u .sub strat.toUnwindAction) (uintArgs2 u a b))) =
      .tau (.running (mkCanonState 0 1
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩), .uninit])) := rfl
  have hStep2 : stepMirState (mkCheckedArithBody u .sub strat.toUnwindAction)
      (.running (mkCanonState 0 1
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩), .uninit])) =
      .tau (.running (mkCanonState 0 2
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩),
         .init (.aggregate 0
           [.scalar ⟨wrapVal (uintWidth u) (modPow2 (uintWidth u) + a - b), uintBytes u⟩,
            .scalar ⟨1, 1⟩])])) :=
    evalStmt_assign_local_step _ 3 _ _ _ _ _ _ hBin trivial rfl
  rw [runMirCall, initExecState, runMirSteps_step_tau hStep1, runMirSteps_step_tau hStep2]
  cases strat <;> rfl

/-- Exact evaluation of `mkUncheckedArithBody u .mul` when `a * b < 2^w`. -/
theorem runMirCall_unchecked_mul_ok (u : UintTy) (a b : Nat)
    (hNoOv : a * b < modPow2 (uintWidth u)) :
    runMirCall (mkUncheckedArithBody u .mul) 2 (uintArgs2 u a b) =
      .halted (.normal (.scalar ⟨a * b, uintBytes u⟩, canonInitMemory)) := by
  have hBin := evalScalarBinOp_uint_mulUnchecked (u := u) (a := a) (b := b)
    [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩)]
    canonInitMemory hNoOv
  rw [wrapVal_of_lt hNoOv] at hBin
  have hStep1 : stepMirState (mkUncheckedArithBody u .mul)
      (.running (initMachineState (mkUncheckedArithBody u .mul) (uintArgs2 u a b))) =
      .tau (.running (mkCanonState 0 1
        [.init (.scalar ⟨a * b, uintBytes u⟩),
         .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩)])) :=
    evalStmt_assign_local_step _ 0 _ _ _ _ _ _ hBin trivial rfl
  rw [runMirCall, initExecState, runMirSteps_step_tau hStep1]
  rfl

/-- Exact evaluation of `mkUncheckedArithBody u .mul` when `2^w ≤ a * b` (UB). -/
theorem runMirCall_unchecked_mul_ub (u : UintTy) (a b : Nat)
    (hOv : modPow2 (uintWidth u) ≤ a * b) :
    runMirCall (mkUncheckedArithBody u .mul) 2 (uintArgs2 u a b) = .faulted .ub := by
  have hBin := evalScalarBinOp_uint_mulUnchecked_ub (u := u) (a := a) (b := b)
    [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩)]
    canonInitMemory hOv
  have hStep1 : stepMirState (mkUncheckedArithBody u .mul)
      (.running (initMachineState (mkUncheckedArithBody u .mul) (uintArgs2 u a b))) =
      MirStepNode.fail .ub :=
    evalStmt_assign_ub _ (localPlace 0) _ _ _ hBin
  rw [runMirCall, initExecState]
  exact runMirSteps_step_ub hStep1

/-- Exact evaluation of `mkCheckedArithBody u .mul strat.toUnwindAction` when `a * b < 2^w`. -/
theorem runMirCall_checked_mul_ok (u : UintTy) (strat : PanicStrategy) (a b : Nat)
    (hNoOv : a * b < modPow2 (uintWidth u)) :
    runMirCall (mkCheckedArithBody u .mul strat.toUnwindAction) 6 (uintArgs2 u a b) =
      .halted (.normal (.scalar ⟨a * b, uintBytes u⟩, canonInitMemory)) := by
  have hBin := evalScalarBinOp_uint_mulWithOverflow (u := u) (a := a) (b := b)
    [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩), .uninit]
    canonInitMemory
  rw [wrapVal_of_lt hNoOv, nat_ble_false_of_lt hNoOv] at hBin
  have hStep1 : stepMirState (mkCheckedArithBody u .mul strat.toUnwindAction)
      (.running (initMachineState (mkCheckedArithBody u .mul strat.toUnwindAction) (uintArgs2 u a b))) =
      .tau (.running (mkCanonState 0 1
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩), .uninit])) := rfl
  have hStep2 : stepMirState (mkCheckedArithBody u .mul strat.toUnwindAction)
      (.running (mkCanonState 0 1
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩), .uninit])) =
      .tau (.running (mkCanonState 0 2
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩),
         .init (.aggregate 0 [.scalar ⟨a * b, uintBytes u⟩, .scalar ⟨0, 1⟩])])) :=
    evalStmt_assign_local_step _ 3 _ _ _ _ _ _ hBin trivial rfl
  rw [runMirCall, initExecState, runMirSteps_step_tau hStep1, runMirSteps_step_tau hStep2]
  rfl

/-- Exact evaluation of `mkCheckedArithBody u .mul strat.toUnwindAction` when `2^w ≤ a * b`
(deterministic trap). -/
theorem runMirCall_checked_mul_trap (u : UintTy) (strat : PanicStrategy) (a b : Nat)
    (hOv : modPow2 (uintWidth u) ≤ a * b) :
    runMirCall (mkCheckedArithBody u .mul strat.toUnwindAction) 6 (uintArgs2 u a b) =
      .halted strat.toTrapOutcome := by
  have hBin := evalScalarBinOp_uint_mulWithOverflow (u := u) (a := a) (b := b)
    [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩), .uninit]
    canonInitMemory
  rw [Nat.ble_eq_true_of_le hOv] at hBin
  have hStep1 : stepMirState (mkCheckedArithBody u .mul strat.toUnwindAction)
      (.running (initMachineState (mkCheckedArithBody u .mul strat.toUnwindAction) (uintArgs2 u a b))) =
      .tau (.running (mkCanonState 0 1
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩), .uninit])) := rfl
  have hStep2 : stepMirState (mkCheckedArithBody u .mul strat.toUnwindAction)
      (.running (mkCanonState 0 1
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩), .uninit])) =
      .tau (.running (mkCanonState 0 2
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩),
         .init (.aggregate 0
           [.scalar ⟨wrapVal (uintWidth u) (a * b), uintBytes u⟩, .scalar ⟨1, 1⟩])])) :=
    evalStmt_assign_local_step _ 3 _ _ _ _ _ _ hBin trivial rfl
  rw [runMirCall, initExecState, runMirSteps_step_tau hStep1, runMirSteps_step_tau hStep2]
  cases strat <;> rfl

/-- Exact evaluation of `mkWrappingArithBody u .add`. -/
theorem runMirCall_wrapping_add (u : UintTy) (a b : Nat) :
    runMirCall (mkWrappingArithBody u .add) 2 (uintArgs2 u a b) =
      .halted (.normal (.scalar ⟨wrapVal (uintWidth u) (a + b), uintBytes u⟩, canonInitMemory)) := by
  have hBin := evalScalarBinOp_uint_add (u := u) (a := a) (b := b)
    [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩)]
    canonInitMemory
  have hStep1 : stepMirState (mkWrappingArithBody u .add)
      (.running (initMachineState (mkWrappingArithBody u .add) (uintArgs2 u a b))) =
      .tau (.running (mkCanonState 0 1
        [.init (.scalar ⟨wrapVal (uintWidth u) (a + b), uintBytes u⟩),
         .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩)])) :=
    evalStmt_assign_local_step _ 0 _ _ _ _ _ _ hBin trivial rfl
  rw [runMirCall, initExecState, runMirSteps_step_tau hStep1]
  rfl

/-- Exact evaluation of `mkWrappingArithBody u .sub` on in-range operands. -/
theorem runMirCall_wrapping_sub (u : UintTy) (a b : Nat)
    (ha : a < modPow2 (uintWidth u)) (hb : b < modPow2 (uintWidth u)) :
    runMirCall (mkWrappingArithBody u .sub) 2 (uintArgs2 u a b) =
      .halted (.normal
        (.scalar ⟨wrapVal (uintWidth u) (modPow2 (uintWidth u) + a - b), uintBytes u⟩,
         canonInitMemory)) := by
  have hBin := evalScalarBinOp_uint_sub (u := u) (a := a) (b := b)
    [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩)]
    canonInitMemory ha hb
  have hStep1 : stepMirState (mkWrappingArithBody u .sub)
      (.running (initMachineState (mkWrappingArithBody u .sub) (uintArgs2 u a b))) =
      .tau (.running (mkCanonState 0 1
        [.init (.scalar ⟨wrapVal (uintWidth u) (modPow2 (uintWidth u) + a - b), uintBytes u⟩),
         .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩)])) :=
    evalStmt_assign_local_step _ 0 _ _ _ _ _ _ hBin trivial rfl
  rw [runMirCall, initExecState, runMirSteps_step_tau hStep1]
  rfl

/-- Exact evaluation of `mkWrappingArithBody u .mul`. -/
theorem runMirCall_wrapping_mul (u : UintTy) (a b : Nat) :
    runMirCall (mkWrappingArithBody u .mul) 2 (uintArgs2 u a b) =
      .halted (.normal (.scalar ⟨wrapVal (uintWidth u) (a * b), uintBytes u⟩, canonInitMemory)) := by
  have hBin := evalScalarBinOp_uint_mul (u := u) (a := a) (b := b)
    [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩)]
    canonInitMemory
  have hStep1 : stepMirState (mkWrappingArithBody u .mul)
      (.running (initMachineState (mkWrappingArithBody u .mul) (uintArgs2 u a b))) =
      .tau (.running (mkCanonState 0 1
        [.init (.scalar ⟨wrapVal (uintWidth u) (a * b), uintBytes u⟩),
         .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩)])) :=
    evalStmt_assign_local_step _ 0 _ _ _ _ _ _ hBin trivial rfl
  rw [runMirCall, initExecState, runMirSteps_step_tau hStep1]
  rfl

/-! ### 3.3 Exact `stepMirState` Evaluation for Composite `add_scaled` (`a + k * b`) -/

/-- Exact evaluation of `mkUncheckedAddScaledBody u k` when `a + k * b < 2^w`. -/
theorem runMirCall_unchecked_add_scaled_ok (u : UintTy) (k a b : Nat)
    (hNoOv : a + k * b < modPow2 (uintWidth u)) :
    runMirCall (mkUncheckedAddScaledBody u k) 5 (uintArgs2 u a b) =
      .halted (.normal (.scalar ⟨a + k * b, uintBytes u⟩, canonInitMemory)) := by
  have hMulNoOv : k * b < modPow2 (uintWidth u) :=
    Nat.lt_of_le_of_lt (Nat.le_add_left (k * b) a) hNoOv
  have hMul := evalScalarBinOp_uint_mulUnchecked (u := u) (a := k) (b := b)
    [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩), .uninit]
    canonInitMemory hMulNoOv
  rw [wrapVal_of_lt hMulNoOv] at hMul
  have hAdd := evalScalarBinOp_uint_addUnchecked (u := u) (a := a) (b := k * b)
    [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩),
     .init (.scalar ⟨k * b, uintBytes u⟩)]
    canonInitMemory hNoOv
  rw [wrapVal_of_lt hNoOv] at hAdd
  have hStep1 : stepMirState (mkUncheckedAddScaledBody u k)
      (.running (initMachineState (mkUncheckedAddScaledBody u k) (uintArgs2 u a b))) =
      .tau (.running (mkCanonState 0 1
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩), .uninit])) := rfl
  have hStep2 : stepMirState (mkUncheckedAddScaledBody u k)
      (.running (mkCanonState 0 1
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩), .uninit])) =
      .tau (.running (mkCanonState 0 2
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩),
         .init (.scalar ⟨k * b, uintBytes u⟩)])) :=
    evalStmt_assign_local_step _ 3 _ _ _ _ _ _ hMul trivial rfl
  have hStep3 : stepMirState (mkUncheckedAddScaledBody u k)
      (.running (mkCanonState 0 2
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩),
         .init (.scalar ⟨k * b, uintBytes u⟩)])) =
      .tau (.running (mkCanonState 0 3
        [.init (.scalar ⟨a + k * b, uintBytes u⟩),
         .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩),
         .init (.scalar ⟨k * b, uintBytes u⟩)])) :=
    evalStmt_assign_local_step _ 0 _ _ _ _ _ _ hAdd trivial rfl
  rw [runMirCall, initExecState, runMirSteps_step_tau hStep1, runMirSteps_step_tau hStep2,
      runMirSteps_step_tau hStep3]
  rfl

/-- Exact evaluation of `mkUncheckedAddScaledBody u k` when `2^w ≤ a + k * b` (UB). -/
theorem runMirCall_unchecked_add_scaled_ub (u : UintTy) (k a b : Nat)
    (hOv : modPow2 (uintWidth u) ≤ a + k * b) :
    runMirCall (mkUncheckedAddScaledBody u k) 5 (uintArgs2 u a b) = .faulted .ub := by
  have hStep1 : stepMirState (mkUncheckedAddScaledBody u k)
      (.running (initMachineState (mkUncheckedAddScaledBody u k) (uintArgs2 u a b))) =
      .tau (.running (mkCanonState 0 1
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩), .uninit])) := rfl
  cases hMulB : Nat.ble (modPow2 (uintWidth u)) (k * b) with
  | true =>
    have hMulOv : modPow2 (uintWidth u) ≤ k * b := Nat.le_of_ble_eq_true hMulB
    have hMul := evalScalarBinOp_uint_mulUnchecked_ub (u := u) (a := k) (b := b)
      [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩), .uninit]
      canonInitMemory hMulOv
    have hStep2 : stepMirState (mkUncheckedAddScaledBody u k)
        (.running (mkCanonState 0 1
          [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
           .init (.scalar ⟨b, uintBytes u⟩), .uninit])) = MirStepNode.fail .ub :=
      evalStmt_assign_ub _ (localPlace 3) _ _ _ hMul
    rw [runMirCall, initExecState, runMirSteps_step_tau hStep1]
    exact runMirSteps_step_ub hStep2
  | false =>
    have hMulNoOv : k * b < modPow2 (uintWidth u) := nat_lt_of_ble_false hMulB
    have hMul := evalScalarBinOp_uint_mulUnchecked (u := u) (a := k) (b := b)
      [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩), .uninit]
      canonInitMemory hMulNoOv
    rw [wrapVal_of_lt hMulNoOv] at hMul
    have hAdd := evalScalarBinOp_uint_addUnchecked_ub (u := u) (a := a) (b := k * b)
      [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩),
       .init (.scalar ⟨k * b, uintBytes u⟩)]
      canonInitMemory hOv
    have hStep2 : stepMirState (mkUncheckedAddScaledBody u k)
        (.running (mkCanonState 0 1
          [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
           .init (.scalar ⟨b, uintBytes u⟩), .uninit])) =
        .tau (.running (mkCanonState 0 2
          [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
           .init (.scalar ⟨b, uintBytes u⟩),
           .init (.scalar ⟨k * b, uintBytes u⟩)])) :=
      evalStmt_assign_local_step _ 3 _ _ _ _ _ _ hMul trivial rfl
    have hStep3 : stepMirState (mkUncheckedAddScaledBody u k)
        (.running (mkCanonState 0 2
          [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
           .init (.scalar ⟨b, uintBytes u⟩),
           .init (.scalar ⟨k * b, uintBytes u⟩)])) = MirStepNode.fail .ub :=
      evalStmt_assign_ub _ (localPlace 0) _ _ _ hAdd
    rw [runMirCall, initExecState, runMirSteps_step_tau hStep1, runMirSteps_step_tau hStep2]
    exact runMirSteps_step_ub hStep3

/-- Exact evaluation of `mkCheckedAddScaledBody u k strat.toUnwindAction` when
`a + k * b < 2^w`. -/
theorem runMirCall_checked_add_scaled_ok (u : UintTy) (k : Nat) (strat : PanicStrategy)
    (a b : Nat) (hNoOv : a + k * b < modPow2 (uintWidth u)) :
    runMirCall (mkCheckedAddScaledBody u k strat.toUnwindAction) 13 (uintArgs2 u a b) =
      .halted (.normal (.scalar ⟨a + k * b, uintBytes u⟩, canonInitMemory)) := by
  have hMulNoOv : k * b < modPow2 (uintWidth u) :=
    Nat.lt_of_le_of_lt (Nat.le_add_left (k * b) a) hNoOv
  have hMul := evalScalarBinOp_uint_mulWithOverflow (u := u) (a := k) (b := b)
    [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩),
     .uninit, .dead, .dead]
    canonInitMemory
  rw [wrapVal_of_lt hMulNoOv, nat_ble_false_of_lt hMulNoOv] at hMul
  have hAdd := evalScalarBinOp_uint_addWithOverflow (u := u) (a := a) (b := k * b)
    [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩),
     .dead, .init (.scalar ⟨k * b, uintBytes u⟩), .uninit]
    canonInitMemory
  rw [wrapVal_of_lt hNoOv, nat_ble_false_of_lt hNoOv] at hAdd
  have hStep1 : stepMirState (mkCheckedAddScaledBody u k strat.toUnwindAction)
      (.running (initMachineState (mkCheckedAddScaledBody u k strat.toUnwindAction) (uintArgs2 u a b))) =
      .tau (.running (mkCanonState 0 1
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩), .uninit, .dead, .dead])) := rfl
  have hStep2 : stepMirState (mkCheckedAddScaledBody u k strat.toUnwindAction)
      (.running (mkCanonState 0 1
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩), .uninit, .dead, .dead])) =
      .tau (.running (mkCanonState 0 2
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩),
         .init (.aggregate 0 [.scalar ⟨k * b, uintBytes u⟩, .scalar ⟨0, 1⟩]),
         .dead, .dead])) :=
    evalStmt_assign_local_step _ 3 _ _ _ _ _ _ hMul trivial rfl
  have hMid :
      runMirSteps (mkCheckedAddScaledBody u k strat.toUnwindAction) 11
        (.running (mkCanonState 0 2
          [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
           .init (.scalar ⟨b, uintBytes u⟩),
           .init (.aggregate 0 [.scalar ⟨k * b, uintBytes u⟩, .scalar ⟨0, 1⟩]),
           .dead, .dead])) =
      runMirSteps (mkCheckedAddScaledBody u k strat.toUnwindAction) 6
        (.running (mkCanonState 1 4
          [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
           .init (.scalar ⟨b, uintBytes u⟩),
           .dead, .init (.scalar ⟨k * b, uintBytes u⟩), .uninit])) := rfl
  have hStep8 : stepMirState (mkCheckedAddScaledBody u k strat.toUnwindAction)
      (.running (mkCanonState 1 4
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩),
         .dead, .init (.scalar ⟨k * b, uintBytes u⟩), .uninit])) =
      .tau (.running (mkCanonState 1 5
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩),
         .dead, .init (.scalar ⟨k * b, uintBytes u⟩),
         .init (.aggregate 0 [.scalar ⟨a + k * b, uintBytes u⟩, .scalar ⟨0, 1⟩])])) :=
    evalStmt_assign_local_step _ 5 _ _ _ _ _ _ hAdd trivial rfl
  rw [runMirCall, initExecState, runMirSteps_step_tau hStep1, runMirSteps_step_tau hStep2,
      hMid, runMirSteps_step_tau hStep8]
  rfl

/-- Exact evaluation of `mkCheckedAddScaledBody u k strat.toUnwindAction` when
`2^w ≤ a + k * b` (deterministic trap). -/
theorem runMirCall_checked_add_scaled_trap (u : UintTy) (k : Nat) (strat : PanicStrategy)
    (a b : Nat) (hOv : modPow2 (uintWidth u) ≤ a + k * b) :
    runMirCall (mkCheckedAddScaledBody u k strat.toUnwindAction) 13 (uintArgs2 u a b) =
      .halted strat.toTrapOutcome := by
  have hStep1 : stepMirState (mkCheckedAddScaledBody u k strat.toUnwindAction)
      (.running (initMachineState (mkCheckedAddScaledBody u k strat.toUnwindAction) (uintArgs2 u a b))) =
      .tau (.running (mkCanonState 0 1
        [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
         .init (.scalar ⟨b, uintBytes u⟩), .uninit, .dead, .dead])) := rfl
  cases hMulB : Nat.ble (modPow2 (uintWidth u)) (k * b) with
  | true =>
    have hMul := evalScalarBinOp_uint_mulWithOverflow (u := u) (a := k) (b := b)
      [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩),
       .uninit, .dead, .dead]
      canonInitMemory
    rw [hMulB] at hMul
    have hStep2 : stepMirState (mkCheckedAddScaledBody u k strat.toUnwindAction)
        (.running (mkCanonState 0 1
          [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
           .init (.scalar ⟨b, uintBytes u⟩), .uninit, .dead, .dead])) =
        .tau (.running (mkCanonState 0 2
          [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
           .init (.scalar ⟨b, uintBytes u⟩),
           .init (.aggregate 0
             [.scalar ⟨wrapVal (uintWidth u) (k * b), uintBytes u⟩, .scalar ⟨1, 1⟩]),
           .dead, .dead])) :=
      evalStmt_assign_local_step _ 3 _ _ _ _ _ _ hMul trivial rfl
    rw [runMirCall, initExecState, runMirSteps_step_tau hStep1, runMirSteps_step_tau hStep2]
    cases strat <;> rfl
  | false =>
    have hMulNoOv : k * b < modPow2 (uintWidth u) := nat_lt_of_ble_false hMulB
    have hMul := evalScalarBinOp_uint_mulWithOverflow (u := u) (a := k) (b := b)
      [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩),
       .uninit, .dead, .dead]
      canonInitMemory
    rw [wrapVal_of_lt hMulNoOv, hMulB] at hMul
    have hAdd := evalScalarBinOp_uint_addWithOverflow (u := u) (a := a) (b := k * b)
      [.uninit, .init (.scalar ⟨a, uintBytes u⟩), .init (.scalar ⟨b, uintBytes u⟩),
       .dead, .init (.scalar ⟨k * b, uintBytes u⟩), .uninit]
      canonInitMemory
    rw [Nat.ble_eq_true_of_le hOv] at hAdd
    have hStep2 : stepMirState (mkCheckedAddScaledBody u k strat.toUnwindAction)
        (.running (mkCanonState 0 1
          [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
           .init (.scalar ⟨b, uintBytes u⟩), .uninit, .dead, .dead])) =
        .tau (.running (mkCanonState 0 2
          [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
           .init (.scalar ⟨b, uintBytes u⟩),
           .init (.aggregate 0 [.scalar ⟨k * b, uintBytes u⟩, .scalar ⟨0, 1⟩]),
           .dead, .dead])) :=
      evalStmt_assign_local_step _ 3 _ _ _ _ _ _ hMul trivial rfl
    have hMid :
        runMirSteps (mkCheckedAddScaledBody u k strat.toUnwindAction) 11
          (.running (mkCanonState 0 2
            [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
             .init (.scalar ⟨b, uintBytes u⟩),
             .init (.aggregate 0 [.scalar ⟨k * b, uintBytes u⟩, .scalar ⟨0, 1⟩]),
             .dead, .dead])) =
        runMirSteps (mkCheckedAddScaledBody u k strat.toUnwindAction) 6
          (.running (mkCanonState 1 4
            [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
             .init (.scalar ⟨b, uintBytes u⟩),
             .dead, .init (.scalar ⟨k * b, uintBytes u⟩), .uninit])) := rfl
    have hStep8 : stepMirState (mkCheckedAddScaledBody u k strat.toUnwindAction)
        (.running (mkCanonState 1 4
          [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
           .init (.scalar ⟨b, uintBytes u⟩),
           .dead, .init (.scalar ⟨k * b, uintBytes u⟩), .uninit])) =
        .tau (.running (mkCanonState 1 5
          [.uninit, .init (.scalar ⟨a, uintBytes u⟩),
           .init (.scalar ⟨b, uintBytes u⟩),
           .dead, .init (.scalar ⟨k * b, uintBytes u⟩),
           .init (.aggregate 0
             [.scalar ⟨wrapVal (uintWidth u) (a + k * b), uintBytes u⟩,
              .scalar ⟨1, 1⟩])])) :=
      evalStmt_assign_local_step _ 5 _ _ _ _ _ _ hAdd trivial rfl
    rw [runMirCall, initExecState, runMirSteps_step_tau hStep1, runMirSteps_step_tau hStep2,
        hMid, runMirSteps_step_tau hStep8]
    cases strat <;> rfl

/-! ## 4. Unconditional Forward Refinement (`unchecked ⊑ checked`) & Necessary/Sufficient Reverse (`checked ⊑ unchecked`) -/

private theorem classify_trapOutcome_eq (strat : PanicStrategy) :
    classifyMirExecState strat (.halted strat.toTrapOutcome) = .trap := by
  cases strat <;> rfl

private theorem classifyExact_trapOutcome_eq (strat : PanicStrategy) :
    classifyMirExecStateExact (.halted strat.toTrapOutcome) = .trap strat.toTrapKind := by
  cases strat <;> rfl

/-- **Unconditional forward refinement (`unchecked_add ⊑ checked_add`)**:
Replacing unchecked addition (UB on overflow) with checked addition (deterministic trap on
overflow) is ALWAYS sound for ALL `u : UintTy`, ALL `a b : Nat`, and BOTH `-C panic=abort`
and `-C panic=unwind`, constructively under `MirOutcomeRefines`, `MirExactOutcomeRefines`,
and Layer 1A `ITree.toPartial` (`MirLang`). -/
theorem unchecked_add_refines_to_checked (u : UintTy) (strat : PanicStrategy) (a b : Nat) :
    MirOutcomeRefines
      (classifyMirExecState strat (runMirCall (mkUncheckedArithBody u .add) 2 (uintArgs2 u a b)))
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody u .add strat.toUnwindAction) 6 (uintArgs2 u a b))) ∧
    MirExactOutcomeRefines
      (classifyMirExecStateExact (runMirCall (mkUncheckedArithBody u .add) 2 (uintArgs2 u a b)))
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody u .add strat.toUnwindAction) 6 (uintArgs2 u a b))) ∧
    (mirCallTree (mkCheckedArithBody u .add strat.toUnwindAction) (uintArgs2 u a b)).toPartial ≤
      (mirCallTree (mkUncheckedArithBody u .add) (uintArgs2 u a b)).toPartial := by
  cases hB : Nat.ble (modPow2 (uintWidth u)) (a + b) with
  | true =>
    have hOv : modPow2 (uintWidth u) ≤ a + b := Nat.le_of_ble_eq_true hB
    have hU := runMirCall_unchecked_add_ub u a b hOv
    have hT := mirCallTree_toPartial_refines_ub
      (bImpl := mkCheckedArithBody u .add strat.toUnwindAction)
      (argsImpl := uintArgs2 u a b) hU
    rw [hU]
    exact ⟨trivial, trivial, hT⟩
  | false =>
    have hNoOv : a + b < modPow2 (uintWidth u) := nat_lt_of_ble_false hB
    have hU := runMirCall_unchecked_add_ok u a b hNoOv
    have hC := runMirCall_checked_add_ok u strat a b hNoOv
    have hEq := mirCallTree_toPartial_equiv_of_same_halted hC hU
    rw [hU, hC]
    exact ⟨rfl, rfl, hEq.1⟩

/-- Coinductive `WeakRef` corollary for unconditional forward `unchecked_add ⊑ checked_add`. -/
theorem unchecked_add_weakRef_to_checked (u : UintTy) (strat : PanicStrategy) (a b : Nat) :
    WeakRef
      (mirCallTree (mkCheckedArithBody u .add strat.toUnwindAction) (uintArgs2 u a b))
      (mirCallTree (mkUncheckedArithBody u .add) (uintArgs2 u a b)) := by
  cases hB : Nat.ble (modPow2 (uintWidth u)) (a + b) with
  | true =>
    exact mirCallTree_weakRef_refines_ub
      (runMirCall_unchecked_add_ub u a b (Nat.le_of_ble_eq_true hB))
  | false =>
    have hNoOv : a + b < modPow2 (uintWidth u) := nat_lt_of_ble_false hB
    exact (mirCallTree_weakRef_equiv_of_same_halted
      (runMirCall_checked_add_ok u strat a b hNoOv)
      (runMirCall_unchecked_add_ok u a b hNoOv)).1

/-- **Unconditional forward refinement (`unchecked_sub ⊑ checked_sub`)**:
Valid for ALL `u : UintTy`, ALL `a b < 2^w`, and BOTH `-C panic=abort` and `-C panic=unwind`. -/
theorem unchecked_sub_refines_to_checked (u : UintTy) (strat : PanicStrategy) (a b : Nat)
    (ha : a < modPow2 (uintWidth u)) (hb : b < modPow2 (uintWidth u)) :
    MirOutcomeRefines
      (classifyMirExecState strat (runMirCall (mkUncheckedArithBody u .sub) 2 (uintArgs2 u a b)))
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody u .sub strat.toUnwindAction) 6 (uintArgs2 u a b))) ∧
    MirExactOutcomeRefines
      (classifyMirExecStateExact (runMirCall (mkUncheckedArithBody u .sub) 2 (uintArgs2 u a b)))
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody u .sub strat.toUnwindAction) 6 (uintArgs2 u a b))) ∧
    (mirCallTree (mkCheckedArithBody u .sub strat.toUnwindAction) (uintArgs2 u a b)).toPartial ≤
      (mirCallTree (mkUncheckedArithBody u .sub) (uintArgs2 u a b)).toPartial := by
  cases hB : Nat.ble b a with
  | true =>
    have hLe : b ≤ a := Nat.le_of_ble_eq_true hB
    have hU := runMirCall_unchecked_sub_ok u a b ha hLe
    have hC := runMirCall_checked_sub_ok u strat a b ha hb hLe
    have hEq := mirCallTree_toPartial_equiv_of_same_halted hC hU
    rw [hU, hC]
    exact ⟨rfl, rfl, hEq.1⟩
  | false =>
    have hUnd : a < b := nat_lt_of_ble_false hB
    have hU := runMirCall_unchecked_sub_ub u a b hUnd
    have hT := mirCallTree_toPartial_refines_ub
      (bImpl := mkCheckedArithBody u .sub strat.toUnwindAction)
      (argsImpl := uintArgs2 u a b) hU
    rw [hU]
    exact ⟨trivial, trivial, hT⟩

/-- Coinductive `WeakRef` corollary for unconditional forward `unchecked_sub ⊑ checked_sub`. -/
theorem unchecked_sub_weakRef_to_checked (u : UintTy) (strat : PanicStrategy) (a b : Nat)
    (ha : a < modPow2 (uintWidth u)) (hb : b < modPow2 (uintWidth u)) :
    WeakRef
      (mirCallTree (mkCheckedArithBody u .sub strat.toUnwindAction) (uintArgs2 u a b))
      (mirCallTree (mkUncheckedArithBody u .sub) (uintArgs2 u a b)) := by
  cases hB : Nat.ble b a with
  | true =>
    have hLe : b ≤ a := Nat.le_of_ble_eq_true hB
    exact (mirCallTree_weakRef_equiv_of_same_halted
      (runMirCall_checked_sub_ok u strat a b ha hb hLe)
      (runMirCall_unchecked_sub_ok u a b ha hLe)).1
  | false =>
    exact mirCallTree_weakRef_refines_ub
      (runMirCall_unchecked_sub_ub u a b (nat_lt_of_ble_false hB))

/-- **Unconditional forward refinement (`unchecked_mul ⊑ checked_mul`)**:
Valid for ALL `u : UintTy`, ALL `a b : Nat`, and BOTH `-C panic=abort` and `-C panic=unwind`. -/
theorem unchecked_mul_refines_to_checked (u : UintTy) (strat : PanicStrategy) (a b : Nat) :
    MirOutcomeRefines
      (classifyMirExecState strat (runMirCall (mkUncheckedArithBody u .mul) 2 (uintArgs2 u a b)))
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody u .mul strat.toUnwindAction) 6 (uintArgs2 u a b))) ∧
    MirExactOutcomeRefines
      (classifyMirExecStateExact (runMirCall (mkUncheckedArithBody u .mul) 2 (uintArgs2 u a b)))
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody u .mul strat.toUnwindAction) 6 (uintArgs2 u a b))) ∧
    (mirCallTree (mkCheckedArithBody u .mul strat.toUnwindAction) (uintArgs2 u a b)).toPartial ≤
      (mirCallTree (mkUncheckedArithBody u .mul) (uintArgs2 u a b)).toPartial := by
  cases hB : Nat.ble (modPow2 (uintWidth u)) (a * b) with
  | true =>
    have hOv : modPow2 (uintWidth u) ≤ a * b := Nat.le_of_ble_eq_true hB
    have hU := runMirCall_unchecked_mul_ub u a b hOv
    have hT := mirCallTree_toPartial_refines_ub
      (bImpl := mkCheckedArithBody u .mul strat.toUnwindAction)
      (argsImpl := uintArgs2 u a b) hU
    rw [hU]
    exact ⟨trivial, trivial, hT⟩
  | false =>
    have hNoOv : a * b < modPow2 (uintWidth u) := nat_lt_of_ble_false hB
    have hU := runMirCall_unchecked_mul_ok u a b hNoOv
    have hC := runMirCall_checked_mul_ok u strat a b hNoOv
    have hEq := mirCallTree_toPartial_equiv_of_same_halted hC hU
    rw [hU, hC]
    exact ⟨rfl, rfl, hEq.1⟩

/-- Coinductive `WeakRef` corollary for unconditional forward `unchecked_mul ⊑ checked_mul`. -/
theorem unchecked_mul_weakRef_to_checked (u : UintTy) (strat : PanicStrategy) (a b : Nat) :
    WeakRef
      (mirCallTree (mkCheckedArithBody u .mul strat.toUnwindAction) (uintArgs2 u a b))
      (mirCallTree (mkUncheckedArithBody u .mul) (uintArgs2 u a b)) := by
  cases hB : Nat.ble (modPow2 (uintWidth u)) (a * b) with
  | true =>
    exact mirCallTree_weakRef_refines_ub
      (runMirCall_unchecked_mul_ub u a b (Nat.le_of_ble_eq_true hB))
  | false =>
    have hNoOv : a * b < modPow2 (uintWidth u) := nat_lt_of_ble_false hB
    exact (mirCallTree_weakRef_equiv_of_same_halted
      (runMirCall_checked_mul_ok u strat a b hNoOv)
      (runMirCall_unchecked_mul_ok u a b hNoOv)).1

/-- **Unconditional forward refinement for composite `add_scaled` (`a + k * b`)**. -/
theorem unchecked_add_scaled_refines_to_checked (u : UintTy) (k : Nat)
    (strat : PanicStrategy) (a b : Nat) :
    MirOutcomeRefines
      (classifyMirExecState strat (runMirCall (mkUncheckedAddScaledBody u k) 5 (uintArgs2 u a b)))
      (classifyMirExecState strat
        (runMirCall (mkCheckedAddScaledBody u k strat.toUnwindAction) 13 (uintArgs2 u a b))) ∧
    (mirCallTree (mkCheckedAddScaledBody u k strat.toUnwindAction) (uintArgs2 u a b)).toPartial ≤
      (mirCallTree (mkUncheckedAddScaledBody u k) (uintArgs2 u a b)).toPartial := by
  cases hB : Nat.ble (modPow2 (uintWidth u)) (a + k * b) with
  | true =>
    have hOv : modPow2 (uintWidth u) ≤ a + k * b := Nat.le_of_ble_eq_true hB
    have hU := runMirCall_unchecked_add_scaled_ub u k a b hOv
    have hT := mirCallTree_toPartial_refines_ub
      (bImpl := mkCheckedAddScaledBody u k strat.toUnwindAction)
      (argsImpl := uintArgs2 u a b) hU
    rw [hU]
    exact ⟨trivial, hT⟩
  | false =>
    have hNoOv : a + k * b < modPow2 (uintWidth u) := nat_lt_of_ble_false hB
    have hU := runMirCall_unchecked_add_scaled_ok u k a b hNoOv
    have hC := runMirCall_checked_add_scaled_ok u k strat a b hNoOv
    have hEq := mirCallTree_toPartial_equiv_of_same_halted hC hU
    rw [hU, hC]
    exact ⟨rfl, hEq.1⟩

/-- **Necessary & sufficient reverse refinement (`checked_add ⊑ unchecked_add`)**:
Eliminating the overflow check is panic-preserving iff `a + b < 2^w`. -/
theorem checked_add_refines_unchecked_iff (u : UintTy) (strat : PanicStrategy) (a b : Nat) :
    MirOutcomeRefines
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody u .add strat.toUnwindAction) 6 (uintArgs2 u a b)))
      (classifyMirExecState strat (runMirCall (mkUncheckedArithBody u .add) 2 (uintArgs2 u a b)))
      ↔ a + b < modPow2 (uintWidth u) := by
  constructor
  · intro hRef
    cases hB : Nat.ble (modPow2 (uintWidth u)) (a + b) with
    | false => exact nat_lt_of_ble_false hB
    | true =>
      have hOv : modPow2 (uintWidth u) ≤ a + b := Nat.le_of_ble_eq_true hB
      rw [runMirCall_checked_add_trap u strat a b hOv,
          runMirCall_unchecked_add_ub u a b hOv,
          classify_trapOutcome_eq strat] at hRef
      exact False.elim hRef
  · intro hNoOv
    rw [runMirCall_checked_add_ok u strat a b hNoOv,
        runMirCall_unchecked_add_ok u a b hNoOv]
    rfl

/-- **Necessary & sufficient reverse refinement (`checked_sub ⊑ unchecked_sub`)**:
For `a, b < 2^w`, eliminating the underflow check is panic-preserving iff `b ≤ a`. -/
theorem checked_sub_refines_unchecked_iff (u : UintTy) (strat : PanicStrategy) (a b : Nat)
    (ha : a < modPow2 (uintWidth u)) (hb : b < modPow2 (uintWidth u)) :
    MirOutcomeRefines
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody u .sub strat.toUnwindAction) 6 (uintArgs2 u a b)))
      (classifyMirExecState strat (runMirCall (mkUncheckedArithBody u .sub) 2 (uintArgs2 u a b)))
      ↔ b ≤ a := by
  constructor
  · intro hRef
    cases hB : Nat.ble b a with
    | true => exact Nat.le_of_ble_eq_true hB
    | false =>
      have hUnd : a < b := nat_lt_of_ble_false hB
      rw [runMirCall_checked_sub_trap u strat a b ha hb hUnd,
          runMirCall_unchecked_sub_ub u a b hUnd,
          classify_trapOutcome_eq strat] at hRef
      exact False.elim hRef
  · intro hLe
    rw [runMirCall_checked_sub_ok u strat a b ha hb hLe,
        runMirCall_unchecked_sub_ok u a b ha hLe]
    rfl

/-- **Necessary & sufficient reverse refinement (`checked_mul ⊑ unchecked_mul`)**:
Eliminating the overflow check is panic-preserving iff `a * b < 2^w`. -/
theorem checked_mul_refines_unchecked_iff (u : UintTy) (strat : PanicStrategy) (a b : Nat) :
    MirOutcomeRefines
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody u .mul strat.toUnwindAction) 6 (uintArgs2 u a b)))
      (classifyMirExecState strat (runMirCall (mkUncheckedArithBody u .mul) 2 (uintArgs2 u a b)))
      ↔ a * b < modPow2 (uintWidth u) := by
  constructor
  · intro hRef
    cases hB : Nat.ble (modPow2 (uintWidth u)) (a * b) with
    | false => exact nat_lt_of_ble_false hB
    | true =>
      have hOv : modPow2 (uintWidth u) ≤ a * b := Nat.le_of_ble_eq_true hB
      rw [runMirCall_checked_mul_trap u strat a b hOv,
          runMirCall_unchecked_mul_ub u a b hOv,
          classify_trapOutcome_eq strat] at hRef
      exact False.elim hRef
  · intro hNoOv
    rw [runMirCall_checked_mul_ok u strat a b hNoOv,
        runMirCall_unchecked_mul_ok u a b hNoOv]
    rfl

/-- **Necessary & sufficient reverse refinement for composite `add_scaled` (`a + k * b`)**. -/
theorem checked_add_scaled_refines_unchecked_iff (u : UintTy) (k : Nat)
    (strat : PanicStrategy) (a b : Nat) :
    MirOutcomeRefines
      (classifyMirExecState strat
        (runMirCall (mkCheckedAddScaledBody u k strat.toUnwindAction) 13 (uintArgs2 u a b)))
      (classifyMirExecState strat
        (runMirCall (mkUncheckedAddScaledBody u k) 5 (uintArgs2 u a b)))
      ↔ a + k * b < modPow2 (uintWidth u) := by
  constructor
  · intro hRef
    cases hB : Nat.ble (modPow2 (uintWidth u)) (a + k * b) with
    | false => exact nat_lt_of_ble_false hB
    | true =>
      have hOv : modPow2 (uintWidth u) ≤ a + k * b := Nat.le_of_ble_eq_true hB
      rw [runMirCall_checked_add_scaled_trap u k strat a b hOv,
          runMirCall_unchecked_add_scaled_ub u k a b hOv,
          classify_trapOutcome_eq strat] at hRef
      exact False.elim hRef
  · intro hNoOv
    rw [runMirCall_checked_add_scaled_ok u k strat a b hNoOv,
        runMirCall_unchecked_add_scaled_ok u k a b hNoOv]
    rfl

/-! ## 5. Direct `Anneal.FarkasMirCert` Panic-Preserving Check Elimination (One-`rfl` Discharge) -/

/-- One-`rfl` constructive Farkas discharge of panic-preserving checked-to-unchecked addition
elimination (`checked_add ⊑ unchecked_add` plus Layer 1A `ITree.toPartial` refinement). -/
theorem checked_add_refines_unchecked_of_farkas_cert
    (u : UintTy) (strat : PanicStrategy)
    (hyps : List NatCutIneq) (lhsExpr rhsExpr : NatLinExpr) (steps : List CutStep)
    (hChk : checkNatCutGoal
      ⟨hyps, ⟨.add (.add lhsExpr rhsExpr) (.cst 1), .cst (modPow2 (uintWidth u))⟩⟩
      steps = true)
    (env : List Nat) :
    HypsImp (NatCutIneq.holds env) hyps
      (MirOutcomeRefines
        (classifyMirExecState strat
          (runMirCall (mkCheckedArithBody u .add strat.toUnwindAction) 6
            (uintArgs2 u (lhsExpr.eval env) (rhsExpr.eval env))))
        (classifyMirExecState strat
          (runMirCall (mkUncheckedArithBody u .add) 2
            (uintArgs2 u (lhsExpr.eval env) (rhsExpr.eval env)))) ∧
       (mirCallTree (mkUncheckedArithBody u .add)
         (uintArgs2 u (lhsExpr.eval env) (rhsExpr.eval env))).toPartial ≤
         (mirCallTree (mkCheckedArithBody u .add strat.toUnwindAction)
           (uintArgs2 u (lhsExpr.eval env) (rhsExpr.eval env))).toPartial) :=
  hypsImp_concl_mono (fun hFarkas => by
    have hLt : lhsExpr.eval env + rhsExpr.eval env < modPow2 (uintWidth u) := hFarkas.1
    have hC := runMirCall_checked_add_ok u strat (lhsExpr.eval env) (rhsExpr.eval env) hLt
    have hU := runMirCall_unchecked_add_ok u (lhsExpr.eval env) (rhsExpr.eval env) hLt
    have hTree := mirCallTree_toPartial_equiv_of_same_halted hU hC
    exact ⟨(checked_add_refines_unchecked_iff u strat _ _).2 hLt, hTree.1⟩)
    (farkas_discharges_uint_add_no_overflow u hyps lhsExpr rhsExpr steps hChk env [] canonInitMemory)

/-- One-`rfl` constructive Farkas bidirectional equivalence between checked and unchecked addition. -/
theorem checked_add_equiv_unchecked_of_farkas_cert
    (u : UintTy) (strat : PanicStrategy)
    (hyps : List NatCutIneq) (lhsExpr rhsExpr : NatLinExpr) (steps : List CutStep)
    (hChk : checkNatCutGoal
      ⟨hyps, ⟨.add (.add lhsExpr rhsExpr) (.cst 1), .cst (modPow2 (uintWidth u))⟩⟩
      steps = true)
    (env : List Nat) :
    HypsImp (NatCutIneq.holds env) hyps
      (MirOutcomeEquiv
        (classifyMirExecState strat
          (runMirCall (mkCheckedArithBody u .add strat.toUnwindAction) 6
            (uintArgs2 u (lhsExpr.eval env) (rhsExpr.eval env))))
        (classifyMirExecState strat
          (runMirCall (mkUncheckedArithBody u .add) 2
            (uintArgs2 u (lhsExpr.eval env) (rhsExpr.eval env))))) :=
  hypsImp_concl_mono (fun hRev =>
    ⟨hRev.1, (unchecked_add_refines_to_checked u strat _ _).1⟩)
    (checked_add_refines_unchecked_of_farkas_cert u strat hyps lhsExpr rhsExpr steps hChk env)

/-- One-`rfl` constructive Farkas discharge of panic-preserving checked-to-unchecked subtraction
elimination given an operand range proof `lhs < 2^w`. -/
theorem checked_sub_refines_unchecked_of_farkas_cert
    (u : UintTy) (strat : PanicStrategy)
    (hyps : List NatCutIneq) (lhsExpr rhsExpr : NatLinExpr) (steps : List CutStep)
    (hChk : checkNatCutGoal ⟨hyps, ⟨rhsExpr, lhsExpr⟩⟩ steps = true)
    (env : List Nat)
    (hLhsLt : lhsExpr.eval env < modPow2 (uintWidth u)) :
    HypsImp (NatCutIneq.holds env) hyps
      (MirOutcomeEquiv
        (classifyMirExecState strat
          (runMirCall (mkCheckedArithBody u .sub strat.toUnwindAction) 6
            (uintArgs2 u (lhsExpr.eval env) (rhsExpr.eval env))))
        (classifyMirExecState strat
          (runMirCall (mkUncheckedArithBody u .sub) 2
            (uintArgs2 u (lhsExpr.eval env) (rhsExpr.eval env)))) ∧
       (mirCallTree (mkUncheckedArithBody u .sub)
         (uintArgs2 u (lhsExpr.eval env) (rhsExpr.eval env))).toPartial ≤
         (mirCallTree (mkCheckedArithBody u .sub strat.toUnwindAction)
           (uintArgs2 u (lhsExpr.eval env) (rhsExpr.eval env))).toPartial) :=
  hypsImp_concl_mono (fun hFarkas => by
    have hLe : rhsExpr.eval env ≤ lhsExpr.eval env := hFarkas.1
    have hRhsLt : rhsExpr.eval env < modPow2 (uintWidth u) := Nat.lt_of_le_of_lt hLe hLhsLt
    have hC := runMirCall_checked_sub_ok u strat (lhsExpr.eval env) (rhsExpr.eval env)
      hLhsLt hRhsLt hLe
    have hU := runMirCall_unchecked_sub_ok u (lhsExpr.eval env) (rhsExpr.eval env) hLhsLt hLe
    have hTree := mirCallTree_toPartial_equiv_of_same_halted hU hC
    exact ⟨⟨(checked_sub_refines_unchecked_iff u strat _ _ hLhsLt hRhsLt).2 hLe,
            (unchecked_sub_refines_to_checked u strat _ _ hLhsLt hRhsLt).1⟩,
           hTree.1⟩)
    (farkas_discharges_uint_sub_no_underflow u hyps lhsExpr rhsExpr steps hChk env
      [] canonInitMemory hLhsLt)

/-- Fully certified one-`rfl` constructive Farkas discharge of checked-to-unchecked subtraction
elimination (both `rhs ≤ lhs` AND `lhs < 2^w` discharged by Farkas certificates). -/
theorem checked_sub_refines_unchecked_of_farkas_cert_certified
    (u : UintTy) (strat : PanicStrategy)
    (hyps : List NatCutIneq) (lhsExpr rhsExpr : NatLinExpr)
    (stepsLe stepsRange : List CutStep)
    (hChkLe : checkNatCutGoal ⟨hyps, ⟨rhsExpr, lhsExpr⟩⟩ stepsLe = true)
    (hChkRange : checkNatCutGoal
      ⟨hyps, ⟨.add lhsExpr (.cst 1), .cst (modPow2 (uintWidth u))⟩⟩ stepsRange = true)
    (env : List Nat) :
    HypsImp (NatCutIneq.holds env) hyps
      (MirOutcomeEquiv
        (classifyMirExecState strat
          (runMirCall (mkCheckedArithBody u .sub strat.toUnwindAction) 6
            (uintArgs2 u (lhsExpr.eval env) (rhsExpr.eval env))))
        (classifyMirExecState strat
          (runMirCall (mkUncheckedArithBody u .sub) 2
            (uintArgs2 u (lhsExpr.eval env) (rhsExpr.eval env)))) ∧
       (mirCallTree (mkUncheckedArithBody u .sub)
         (uintArgs2 u (lhsExpr.eval env) (rhsExpr.eval env))).toPartial ≤
         (mirCallTree (mkCheckedArithBody u .sub strat.toUnwindAction)
           (uintArgs2 u (lhsExpr.eval env) (rhsExpr.eval env))).toPartial) :=
  hypsImp_concl_mono (fun hFarkas => by
    have hLhsLt : lhsExpr.eval env < modPow2 (uintWidth u) := hFarkas.1
    have hLe : rhsExpr.eval env ≤ lhsExpr.eval env := hFarkas.2.1
    have hRhsLt : rhsExpr.eval env < modPow2 (uintWidth u) := Nat.lt_of_le_of_lt hLe hLhsLt
    have hC := runMirCall_checked_sub_ok u strat (lhsExpr.eval env) (rhsExpr.eval env)
      hLhsLt hRhsLt hLe
    have hU := runMirCall_unchecked_sub_ok u (lhsExpr.eval env) (rhsExpr.eval env) hLhsLt hLe
    have hTree := mirCallTree_toPartial_equiv_of_same_halted hU hC
    exact ⟨⟨(checked_sub_refines_unchecked_iff u strat _ _ hLhsLt hRhsLt).2 hLe,
            (unchecked_sub_refines_to_checked u strat _ _ hLhsLt hRhsLt).1⟩,
           hTree.1⟩)
    (farkas_discharges_uint_sub_no_underflow_certified u hyps lhsExpr rhsExpr
      stepsLe stepsRange hChkLe hChkRange env [] canonInitMemory)

/-- One-`rfl` constructive Farkas discharge of panic-preserving checked-to-unchecked
constant-scaled multiplication elimination (`k * x`). -/
theorem checked_mul_const_refines_unchecked_of_farkas_cert
    (u : UintTy) (strat : PanicStrategy)
    (hyps : List NatCutIneq) (k : Nat) (xExpr : NatLinExpr) (steps : List CutStep)
    (hKRange : Nat.blt k (modPow2 (uintWidth u)) = true)
    (hChk : checkNatCutGoal
      ⟨hyps, ⟨.add (.mulC k xExpr) (.cst 1), .cst (modPow2 (uintWidth u))⟩⟩
      steps = true)
    (env : List Nat) :
    HypsImp (NatCutIneq.holds env) hyps
      (UintScalarInRange u ⟨k, uintBytes u⟩ ∧
       MirOutcomeEquiv
        (classifyMirExecState strat
          (runMirCall (mkCheckedArithBody u .mul strat.toUnwindAction) 6
            (uintArgs2 u k (xExpr.eval env))))
        (classifyMirExecState strat
          (runMirCall (mkUncheckedArithBody u .mul) 2
            (uintArgs2 u k (xExpr.eval env)))) ∧
       (mirCallTree (mkUncheckedArithBody u .mul) (uintArgs2 u k (xExpr.eval env))).toPartial ≤
         (mirCallTree (mkCheckedArithBody u .mul strat.toUnwindAction)
           (uintArgs2 u k (xExpr.eval env))).toPartial) :=
  hypsImp_concl_mono (fun hFarkas => by
    have hKIn : UintScalarInRange u ⟨k, uintBytes u⟩ := hFarkas.1
    have hProdLt : k * xExpr.eval env < modPow2 (uintWidth u) := hFarkas.2.1
    have hC := runMirCall_checked_mul_ok u strat k (xExpr.eval env) hProdLt
    have hU := runMirCall_unchecked_mul_ok u k (xExpr.eval env) hProdLt
    have hTree := mirCallTree_toPartial_equiv_of_same_halted hU hC
    exact ⟨hKIn,
           ⟨(checked_mul_refines_unchecked_iff u strat k _).2 hProdLt,
            (unchecked_mul_refines_to_checked u strat k _).1⟩,
           hTree.1⟩)
    (farkas_discharges_uint_mul_const_no_overflow u hyps k xExpr steps hKRange hChk env
      [] canonInitMemory)

/-- Right-constant variant (`x * k`) of `checked_mul_const_refines_unchecked_of_farkas_cert`:
the SAME `k * x + 1 ≤ 2^w` certificate eliminates the checked multiplication when the constant
is the right operand (`uintArgs2 u x k`), via
`Anneal.FarkasMirCert.farkas_discharges_uint_mul_const_right_no_overflow`. -/
theorem checked_mul_const_right_refines_unchecked_of_farkas_cert
    (u : UintTy) (strat : PanicStrategy)
    (hyps : List NatCutIneq) (xExpr : NatLinExpr) (k : Nat) (steps : List CutStep)
    (hKRange : Nat.blt k (modPow2 (uintWidth u)) = true)
    (hChk : checkNatCutGoal
      ⟨hyps, ⟨.add (.mulC k xExpr) (.cst 1), .cst (modPow2 (uintWidth u))⟩⟩
      steps = true)
    (env : List Nat) :
    HypsImp (NatCutIneq.holds env) hyps
      (UintScalarInRange u ⟨k, uintBytes u⟩ ∧
       MirOutcomeEquiv
        (classifyMirExecState strat
          (runMirCall (mkCheckedArithBody u .mul strat.toUnwindAction) 6
            (uintArgs2 u (xExpr.eval env) k)))
        (classifyMirExecState strat
          (runMirCall (mkUncheckedArithBody u .mul) 2
            (uintArgs2 u (xExpr.eval env) k))) ∧
       (mirCallTree (mkUncheckedArithBody u .mul) (uintArgs2 u (xExpr.eval env) k)).toPartial ≤
         (mirCallTree (mkCheckedArithBody u .mul strat.toUnwindAction)
           (uintArgs2 u (xExpr.eval env) k)).toPartial) :=
  hypsImp_concl_mono (fun hFarkas => by
    have hKIn : UintScalarInRange u ⟨k, uintBytes u⟩ := hFarkas.1
    have hProdLt : xExpr.eval env * k < modPow2 (uintWidth u) := hFarkas.2.1
    have hC := runMirCall_checked_mul_ok u strat (xExpr.eval env) k hProdLt
    have hU := runMirCall_unchecked_mul_ok u (xExpr.eval env) k hProdLt
    have hTree := mirCallTree_toPartial_equiv_of_same_halted hU hC
    exact ⟨hKIn,
           ⟨(checked_mul_refines_unchecked_iff u strat _ k).2 hProdLt,
            (unchecked_mul_refines_to_checked u strat _ k).1⟩,
           hTree.1⟩)
    (farkas_discharges_uint_mul_const_right_no_overflow u hyps xExpr k steps hKRange hChk env
      [] canonInitMemory)

/-- One-`rfl` constructive Farkas discharge of composite multi-statement `add_scaled`
(`a + k * b`) checked-to-unchecked elimination: a single Farkas certificate for
`a + k * b + 1 ≤ 2^w` eliminates BOTH the checked multiplication and the checked addition
while preserving exact semantics under `MirOutcomeEquiv` and Layer 1A `ITree.toPartial`. -/
theorem checked_add_scaled_refines_unchecked_of_farkas_cert
    (u : UintTy) (k : Nat) (strat : PanicStrategy)
    (hyps : List NatCutIneq) (aExpr bExpr : NatLinExpr) (steps : List CutStep)
    (hKRange : Nat.blt k (modPow2 (uintWidth u)) = true)
    (hChk : checkNatCutGoal
      ⟨hyps, ⟨.add (.add aExpr (.mulC k bExpr)) (.cst 1), .cst (modPow2 (uintWidth u))⟩⟩
      steps = true)
    (env : List Nat) :
    HypsImp (NatCutIneq.holds env) hyps
      (UintScalarInRange u ⟨k, uintBytes u⟩ ∧
       MirOutcomeEquiv
        (classifyMirExecState strat
          (runMirCall (mkCheckedAddScaledBody u k strat.toUnwindAction) 13
            (uintArgs2 u (aExpr.eval env) (bExpr.eval env))))
        (classifyMirExecState strat
          (runMirCall (mkUncheckedAddScaledBody u k) 5
            (uintArgs2 u (aExpr.eval env) (bExpr.eval env)))) ∧
       (mirCallTree (mkUncheckedAddScaledBody u k)
         (uintArgs2 u (aExpr.eval env) (bExpr.eval env))).toPartial ≤
         (mirCallTree (mkCheckedAddScaledBody u k strat.toUnwindAction)
           (uintArgs2 u (aExpr.eval env) (bExpr.eval env))).toPartial) :=
  hypsImp_concl_mono (fun hFarkas => by
    have hKIn : UintScalarInRange u ⟨k, uintBytes u⟩ := ⟨rfl, lt_of_blt_true hKRange⟩
    have hSumLt : aExpr.eval env + k * bExpr.eval env < modPow2 (uintWidth u) := hFarkas.1
    have hC := runMirCall_checked_add_scaled_ok u k strat (aExpr.eval env) (bExpr.eval env) hSumLt
    have hU := runMirCall_unchecked_add_scaled_ok u k (aExpr.eval env) (bExpr.eval env) hSumLt
    have hTree := mirCallTree_toPartial_equiv_of_same_halted hU hC
    exact ⟨hKIn,
           ⟨(checked_add_scaled_refines_unchecked_iff u k strat _ _).2 hSumLt,
            (unchecked_add_scaled_refines_to_checked u k strat _ _).1⟩,
           hTree.1⟩)
    (farkas_discharges_uint_add_no_overflow u hyps aExpr (.mulC k bExpr) steps hChk env
      [] canonInitMemory)

/-- Coinductive `WeakRef` corollary for Farkas-certified `add_scaled` elimination. -/
theorem checked_add_scaled_weakRef_unchecked_of_farkas_cert
    (u : UintTy) (k : Nat) (strat : PanicStrategy)
    (hyps : List NatCutIneq) (aExpr bExpr : NatLinExpr) (steps : List CutStep)
    (hChk : checkNatCutGoal
      ⟨hyps, ⟨.add (.add aExpr (.mulC k bExpr)) (.cst 1), .cst (modPow2 (uintWidth u))⟩⟩
      steps = true)
    (env : List Nat) :
    HypsImp (NatCutIneq.holds env) hyps
      (WeakRef
        (mirCallTree (mkUncheckedAddScaledBody u k)
          (uintArgs2 u (aExpr.eval env) (bExpr.eval env)))
        (mirCallTree (mkCheckedAddScaledBody u k strat.toUnwindAction)
          (uintArgs2 u (aExpr.eval env) (bExpr.eval env)))) :=
  hypsImp_concl_mono (fun hFarkas => by
    have hSumLt : aExpr.eval env + k * bExpr.eval env < modPow2 (uintWidth u) := hFarkas.1
    exact (mirCallTree_weakRef_equiv_of_same_halted
      (runMirCall_unchecked_add_scaled_ok u k (aExpr.eval env) (bExpr.eval env) hSumLt)
      (runMirCall_checked_add_scaled_ok u k strat (aExpr.eval env) (bExpr.eval env) hSumLt)).1)
    (farkas_discharges_uint_add_no_overflow u hyps aExpr (.mulC k bExpr) steps hChk env
      [] canonInitMemory)

/-! ## 5.1 Fuel-Independence & Non-Vacuity of Every Canonical Run

`.unsupported` is a top element of `MirOutcomeRefines` (like `.ub`), so a fuel-truncated
(`.outOfFuel`), still-`.running`, unmodeled (`.unsupported`), or strategy-mismatched trap on the
SPEC side would make a refinement claim hold vacuously. Using `SettledExec` and
`runMirCall_fuel_stable` from Section 2, this section proves that this NEVER happens for any
canonical body: every canonical run classifies to a non-`.unsupported` outcome under its own
panic strategy, for ALL inputs, and is therefore *settled* (a genuine halting outcome or a
genuine `.ub` fault). Settled runs are fuel-independent, so every refinement theorem above holds
verbatim at ANY fuel at least the canonical step count. -/

private theorem classify_ret_ne_unsupported (strat : PanicStrategy) (v : Value) (m : Memory) :
    classifyMirExecState strat (.halted (.normal (v, m))) ≠ .unsupported :=
  fun h => nomatch h

private theorem classify_ub_ne_unsupported (strat : PanicStrategy) :
    classifyMirExecState strat (.faulted .ub) ≠ .unsupported :=
  fun h => nomatch h

private theorem classify_trap_ne_unsupported (strat : PanicStrategy) :
    classifyMirExecState strat (.halted strat.toTrapOutcome) ≠ .unsupported := by
  rw [classify_trapOutcome_eq strat]
  exact fun h => nomatch h

/-- Non-vacuity of the canonical `add` pair: for ALL `u`, `a`, `b`, and BOTH strategies,
neither run classifies to `.unsupported` (no fuel truncation, no unmodeled construct, no
strategy-mismatched trap). -/
theorem canonical_add_runs_nonvacuous (u : UintTy) (strat : PanicStrategy) (a b : Nat) :
    classifyMirExecState strat
      (runMirCall (mkUncheckedArithBody u .add) 2 (uintArgs2 u a b)) ≠ .unsupported ∧
    classifyMirExecState strat
      (runMirCall (mkCheckedArithBody u .add strat.toUnwindAction) 6 (uintArgs2 u a b)) ≠
      .unsupported := by
  cases hB : Nat.ble (modPow2 (uintWidth u)) (a + b) with
  | true =>
    have hOv := Nat.le_of_ble_eq_true hB
    rw [runMirCall_unchecked_add_ub u a b hOv, runMirCall_checked_add_trap u strat a b hOv]
    exact ⟨classify_ub_ne_unsupported strat, classify_trap_ne_unsupported strat⟩
  | false =>
    have hNoOv := nat_lt_of_ble_false hB
    rw [runMirCall_unchecked_add_ok u a b hNoOv, runMirCall_checked_add_ok u strat a b hNoOv]
    exact ⟨classify_ret_ne_unsupported _ _ _, classify_ret_ne_unsupported _ _ _⟩

/-- Non-vacuity of the canonical `sub` pair for ALL in-range `a`, `b` and BOTH strategies. -/
theorem canonical_sub_runs_nonvacuous (u : UintTy) (strat : PanicStrategy) (a b : Nat)
    (ha : a < modPow2 (uintWidth u)) (hb : b < modPow2 (uintWidth u)) :
    classifyMirExecState strat
      (runMirCall (mkUncheckedArithBody u .sub) 2 (uintArgs2 u a b)) ≠ .unsupported ∧
    classifyMirExecState strat
      (runMirCall (mkCheckedArithBody u .sub strat.toUnwindAction) 6 (uintArgs2 u a b)) ≠
      .unsupported := by
  cases hB : Nat.ble b a with
  | true =>
    have hLe := Nat.le_of_ble_eq_true hB
    rw [runMirCall_unchecked_sub_ok u a b ha hLe, runMirCall_checked_sub_ok u strat a b ha hb hLe]
    exact ⟨classify_ret_ne_unsupported _ _ _, classify_ret_ne_unsupported _ _ _⟩
  | false =>
    have hUnd := nat_lt_of_ble_false hB
    rw [runMirCall_unchecked_sub_ub u a b hUnd, runMirCall_checked_sub_trap u strat a b ha hb hUnd]
    exact ⟨classify_ub_ne_unsupported strat, classify_trap_ne_unsupported strat⟩

/-- Non-vacuity of the canonical `mul` pair for ALL `u`, `a`, `b` and BOTH strategies. -/
theorem canonical_mul_runs_nonvacuous (u : UintTy) (strat : PanicStrategy) (a b : Nat) :
    classifyMirExecState strat
      (runMirCall (mkUncheckedArithBody u .mul) 2 (uintArgs2 u a b)) ≠ .unsupported ∧
    classifyMirExecState strat
      (runMirCall (mkCheckedArithBody u .mul strat.toUnwindAction) 6 (uintArgs2 u a b)) ≠
      .unsupported := by
  cases hB : Nat.ble (modPow2 (uintWidth u)) (a * b) with
  | true =>
    have hOv := Nat.le_of_ble_eq_true hB
    rw [runMirCall_unchecked_mul_ub u a b hOv, runMirCall_checked_mul_trap u strat a b hOv]
    exact ⟨classify_ub_ne_unsupported strat, classify_trap_ne_unsupported strat⟩
  | false =>
    have hNoOv := nat_lt_of_ble_false hB
    rw [runMirCall_unchecked_mul_ok u a b hNoOv, runMirCall_checked_mul_ok u strat a b hNoOv]
    exact ⟨classify_ret_ne_unsupported _ _ _, classify_ret_ne_unsupported _ _ _⟩

/-- Non-vacuity of the composite `add_scaled` pair for ALL `u`, `k`, `a`, `b` and BOTH strategies. -/
theorem canonical_add_scaled_runs_nonvacuous (u : UintTy) (k : Nat) (strat : PanicStrategy)
    (a b : Nat) :
    classifyMirExecState strat
      (runMirCall (mkUncheckedAddScaledBody u k) 5 (uintArgs2 u a b)) ≠ .unsupported ∧
    classifyMirExecState strat
      (runMirCall (mkCheckedAddScaledBody u k strat.toUnwindAction) 13 (uintArgs2 u a b)) ≠
      .unsupported := by
  cases hB : Nat.ble (modPow2 (uintWidth u)) (a + k * b) with
  | true =>
    have hOv := Nat.le_of_ble_eq_true hB
    rw [runMirCall_unchecked_add_scaled_ub u k a b hOv,
        runMirCall_checked_add_scaled_trap u k strat a b hOv]
    exact ⟨classify_ub_ne_unsupported strat, classify_trap_ne_unsupported strat⟩
  | false =>
    have hNoOv := nat_lt_of_ble_false hB
    rw [runMirCall_unchecked_add_scaled_ok u k a b hNoOv,
        runMirCall_checked_add_scaled_ok u k strat a b hNoOv]
    exact ⟨classify_ret_ne_unsupported _ _ _, classify_ret_ne_unsupported _ _ _⟩

/-- Fuel-independent necessary & sufficient reverse refinement for `add`: holds verbatim at
EVERY fuel `fC ≥ 6` (checked) and `fU ≥ 2` (unchecked). -/
theorem checked_add_refines_unchecked_iff_of_fuel (u : UintTy) (strat : PanicStrategy)
    (a b : Nat) {fC fU : Nat} (hfC : 6 ≤ fC) (hfU : 2 ≤ fU) :
    MirOutcomeRefines
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody u .add strat.toUnwindAction) fC (uintArgs2 u a b)))
      (classifyMirExecState strat (runMirCall (mkUncheckedArithBody u .add) fU (uintArgs2 u a b)))
      ↔ a + b < modPow2 (uintWidth u) := by
  have hNV := canonical_add_runs_nonvacuous u strat a b
  rw [runMirCall_fuel_stable hfC (settledExec_of_classify_ne_unsupported hNV.2),
      runMirCall_fuel_stable hfU (settledExec_of_classify_ne_unsupported hNV.1)]
  exact checked_add_refines_unchecked_iff u strat a b

/-- Fuel-independent necessary & sufficient reverse refinement for `sub`. -/
theorem checked_sub_refines_unchecked_iff_of_fuel (u : UintTy) (strat : PanicStrategy)
    (a b : Nat) (ha : a < modPow2 (uintWidth u)) (hb : b < modPow2 (uintWidth u))
    {fC fU : Nat} (hfC : 6 ≤ fC) (hfU : 2 ≤ fU) :
    MirOutcomeRefines
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody u .sub strat.toUnwindAction) fC (uintArgs2 u a b)))
      (classifyMirExecState strat (runMirCall (mkUncheckedArithBody u .sub) fU (uintArgs2 u a b)))
      ↔ b ≤ a := by
  have hNV := canonical_sub_runs_nonvacuous u strat a b ha hb
  rw [runMirCall_fuel_stable hfC (settledExec_of_classify_ne_unsupported hNV.2),
      runMirCall_fuel_stable hfU (settledExec_of_classify_ne_unsupported hNV.1)]
  exact checked_sub_refines_unchecked_iff u strat a b ha hb

/-- Fuel-independent necessary & sufficient reverse refinement for `mul`. -/
theorem checked_mul_refines_unchecked_iff_of_fuel (u : UintTy) (strat : PanicStrategy)
    (a b : Nat) {fC fU : Nat} (hfC : 6 ≤ fC) (hfU : 2 ≤ fU) :
    MirOutcomeRefines
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody u .mul strat.toUnwindAction) fC (uintArgs2 u a b)))
      (classifyMirExecState strat (runMirCall (mkUncheckedArithBody u .mul) fU (uintArgs2 u a b)))
      ↔ a * b < modPow2 (uintWidth u) := by
  have hNV := canonical_mul_runs_nonvacuous u strat a b
  rw [runMirCall_fuel_stable hfC (settledExec_of_classify_ne_unsupported hNV.2),
      runMirCall_fuel_stable hfU (settledExec_of_classify_ne_unsupported hNV.1)]
  exact checked_mul_refines_unchecked_iff u strat a b

/-- Fuel-independent necessary & sufficient reverse refinement for composite `add_scaled`. -/
theorem checked_add_scaled_refines_unchecked_iff_of_fuel (u : UintTy) (k : Nat)
    (strat : PanicStrategy) (a b : Nat) {fC fU : Nat} (hfC : 13 ≤ fC) (hfU : 5 ≤ fU) :
    MirOutcomeRefines
      (classifyMirExecState strat
        (runMirCall (mkCheckedAddScaledBody u k strat.toUnwindAction) fC (uintArgs2 u a b)))
      (classifyMirExecState strat
        (runMirCall (mkUncheckedAddScaledBody u k) fU (uintArgs2 u a b)))
      ↔ a + k * b < modPow2 (uintWidth u) := by
  have hNV := canonical_add_scaled_runs_nonvacuous u k strat a b
  rw [runMirCall_fuel_stable hfC (settledExec_of_classify_ne_unsupported hNV.2),
      runMirCall_fuel_stable hfU (settledExec_of_classify_ne_unsupported hNV.1)]
  exact checked_add_scaled_refines_unchecked_iff u k strat a b

/-- Fuel-independent unconditional forward refinement (`unchecked ⊑ checked`) for all three
binary operations and composite `add_scaled`, at EVERY fuel at least the canonical step count. -/
theorem unchecked_refines_to_checked_of_fuel (u : UintTy) (strat : PanicStrategy) (a b k : Nat)
    {fC fU fCs fUs : Nat} (hfC : 6 ≤ fC) (hfU : 2 ≤ fU) (hfCs : 13 ≤ fCs) (hfUs : 5 ≤ fUs) :
    MirOutcomeRefines
      (classifyMirExecState strat (runMirCall (mkUncheckedArithBody u .add) fU (uintArgs2 u a b)))
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody u .add strat.toUnwindAction) fC (uintArgs2 u a b))) ∧
    MirOutcomeRefines
      (classifyMirExecState strat (runMirCall (mkUncheckedArithBody u .mul) fU (uintArgs2 u a b)))
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody u .mul strat.toUnwindAction) fC (uintArgs2 u a b))) ∧
    MirOutcomeRefines
      (classifyMirExecState strat
        (runMirCall (mkUncheckedAddScaledBody u k) fUs (uintArgs2 u a b)))
      (classifyMirExecState strat
        (runMirCall (mkCheckedAddScaledBody u k strat.toUnwindAction) fCs (uintArgs2 u a b))) := by
  have hA := canonical_add_runs_nonvacuous u strat a b
  have hM := canonical_mul_runs_nonvacuous u strat a b
  have hS := canonical_add_scaled_runs_nonvacuous u k strat a b
  rw [runMirCall_fuel_stable hfC (settledExec_of_classify_ne_unsupported hA.2),
      runMirCall_fuel_stable hfU (settledExec_of_classify_ne_unsupported hA.1),
      runMirCall_fuel_stable hfC (settledExec_of_classify_ne_unsupported hM.2),
      runMirCall_fuel_stable hfU (settledExec_of_classify_ne_unsupported hM.1),
      runMirCall_fuel_stable hfCs (settledExec_of_classify_ne_unsupported hS.2),
      runMirCall_fuel_stable hfUs (settledExec_of_classify_ne_unsupported hS.1)]
  exact ⟨(unchecked_add_refines_to_checked u strat a b).1,
         (unchecked_mul_refines_to_checked u strat a b).1,
         (unchecked_add_scaled_refines_to_checked u k strat a b).1⟩

/-- Fuel-independent unconditional forward refinement for in-range `sub`. -/
theorem unchecked_sub_refines_to_checked_of_fuel (u : UintTy) (strat : PanicStrategy) (a b : Nat)
    (ha : a < modPow2 (uintWidth u)) (hb : b < modPow2 (uintWidth u))
    {fC fU : Nat} (hfC : 6 ≤ fC) (hfU : 2 ≤ fU) :
    MirOutcomeRefines
      (classifyMirExecState strat (runMirCall (mkUncheckedArithBody u .sub) fU (uintArgs2 u a b)))
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody u .sub strat.toUnwindAction) fC (uintArgs2 u a b))) := by
  have hNV := canonical_sub_runs_nonvacuous u strat a b ha hb
  rw [runMirCall_fuel_stable hfC (settledExec_of_classify_ne_unsupported hNV.2),
      runMirCall_fuel_stable hfU (settledExec_of_classify_ne_unsupported hNV.1)]
  exact (unchecked_sub_refines_to_checked u strat a b ha hb).1

/-! ## 5.2 Tree-Level (Layer 1A `ITree.toPartial` & Coinductive `WeakRef`) Reverse `iff`

The classifier-level reverse `iff` theorems above are lifted here to the coinductive
`mirCallTree` semantics: eliminating the overflow check (`unchecked` impl refining `checked`
spec) is sound at the ITree level *if and only if* the no-overflow condition holds, for ALL
`u`, ALL inputs (in range for `sub`), and BOTH panic strategies. -/

private theorem toPartial_reverse_iff_of_dichotomy {bC bU : CapturedMir} {fC fU : Nat}
    {args : List Value} {P : Prop} (hDec : P ∨ ¬ P)
    (hYes : P → ∃ o, runMirCall bC fC args = .halted o ∧ runMirCall bU fU args = .halted o)
    (hNo : ¬ P → ∃ o, runMirCall bC fC args = .halted o ∧ runMirCall bU fU args = .faulted .ub) :
    (mirCallTree bU args).toPartial ≤ (mirCallTree bC args).toPartial ↔ P := by
  constructor
  · intro hLe
    cases hDec with
    | inl hp => exact hp
    | inr hnp =>
      have ⟨o, hC, hU⟩ := hNo hnp
      have ⟨uC, hTauC, hObsC⟩ := runMirSteps_halted_to_tauStar _ fC _ o hC
      exact False.elim (not_toPartial_le_of_faultNow_ret (runMirCall_ub_faultNow hU) hTauC hObsC hLe)
  · intro hp
    have ⟨_, hC, hU⟩ := hYes hp
    exact (mirCallTree_toPartial_equiv_of_same_halted hU hC).1

/-- Generic coinductive `WeakRef` reverse-refinement dichotomy `iff` helper. -/
theorem weakRef_reverse_iff_of_dichotomy {bC bU : CapturedMir} {fC fU : Nat}
    {args : List Value} {P : Prop} (hDec : P ∨ ¬ P)
    (hYes : P → ∃ o, runMirCall bC fC args = .halted o ∧ runMirCall bU fU args = .halted o)
    (hNo : ¬ P → ∃ o, runMirCall bC fC args = .halted o ∧ runMirCall bU fU args = .faulted .ub) :
    WeakRef (mirCallTree bU args) (mirCallTree bC args) ↔ P := by
  constructor
  · intro hW
    cases hDec with
    | inl hp => exact hp
    | inr hnp =>
      have ⟨o, hC, hU⟩ := hNo hnp
      have ⟨uC, hTauC, hObsC⟩ := runMirSteps_halted_to_tauStar _ fC _ o hC
      exact False.elim (not_weakRef_of_faultNow_ret (runMirCall_ub_faultNow hU) hTauC hObsC hW)
  · intro hp
    have ⟨_, hC, hU⟩ := hYes hp
    exact (mirCallTree_weakRef_equiv_of_same_halted hU hC).1

private theorem lt_dec (x y : Nat) : x < y ∨ ¬ x < y :=
  (Nat.lt_or_ge x y).imp_right Nat.not_lt_of_ge

private theorem le_dec (x y : Nat) : x ≤ y ∨ ¬ x ≤ y :=
  (Nat.lt_or_ge y x).symm.imp_right Nat.not_le_of_gt

/-- **Tree-level panic-preserving check elimination `iff` for `add`**: the unchecked tree
refines the checked tree under Layer 1A `ITree.toPartial` iff `a + b < 2^w`. -/
theorem checked_add_toPartial_refines_unchecked_iff (u : UintTy) (strat : PanicStrategy)
    (a b : Nat) :
    (mirCallTree (mkUncheckedArithBody u .add) (uintArgs2 u a b)).toPartial ≤
      (mirCallTree (mkCheckedArithBody u .add strat.toUnwindAction) (uintArgs2 u a b)).toPartial
      ↔ a + b < modPow2 (uintWidth u) :=
  toPartial_reverse_iff_of_dichotomy (fC := 6) (fU := 2) (lt_dec _ _)
    (fun h => ⟨_, runMirCall_checked_add_ok u strat a b h, runMirCall_unchecked_add_ok u a b h⟩)
    (fun h => ⟨_, runMirCall_checked_add_trap u strat a b (Nat.not_lt.mp h),
                  runMirCall_unchecked_add_ub u a b (Nat.not_lt.mp h)⟩)

/-- **Tree-level panic-preserving check elimination `iff` for in-range `sub`** (`↔ b ≤ a`). -/
theorem checked_sub_toPartial_refines_unchecked_iff (u : UintTy) (strat : PanicStrategy)
    (a b : Nat) (ha : a < modPow2 (uintWidth u)) (hb : b < modPow2 (uintWidth u)) :
    (mirCallTree (mkUncheckedArithBody u .sub) (uintArgs2 u a b)).toPartial ≤
      (mirCallTree (mkCheckedArithBody u .sub strat.toUnwindAction) (uintArgs2 u a b)).toPartial
      ↔ b ≤ a :=
  toPartial_reverse_iff_of_dichotomy (fC := 6) (fU := 2) (le_dec _ _)
    (fun h => ⟨_, runMirCall_checked_sub_ok u strat a b ha hb h,
                  runMirCall_unchecked_sub_ok u a b ha h⟩)
    (fun h => ⟨_, runMirCall_checked_sub_trap u strat a b ha hb (Nat.not_le.mp h),
                  runMirCall_unchecked_sub_ub u a b (Nat.not_le.mp h)⟩)

/-- **Tree-level panic-preserving check elimination `iff` for `mul`** (`↔ a * b < 2^w`). -/
theorem checked_mul_toPartial_refines_unchecked_iff (u : UintTy) (strat : PanicStrategy)
    (a b : Nat) :
    (mirCallTree (mkUncheckedArithBody u .mul) (uintArgs2 u a b)).toPartial ≤
      (mirCallTree (mkCheckedArithBody u .mul strat.toUnwindAction) (uintArgs2 u a b)).toPartial
      ↔ a * b < modPow2 (uintWidth u) :=
  toPartial_reverse_iff_of_dichotomy (fC := 6) (fU := 2) (lt_dec _ _)
    (fun h => ⟨_, runMirCall_checked_mul_ok u strat a b h, runMirCall_unchecked_mul_ok u a b h⟩)
    (fun h => ⟨_, runMirCall_checked_mul_trap u strat a b (Nat.not_lt.mp h),
                  runMirCall_unchecked_mul_ub u a b (Nat.not_lt.mp h)⟩)

/-- **Tree-level panic-preserving check elimination `iff` for composite `add_scaled`**
(`↔ a + k * b < 2^w`). -/
theorem checked_add_scaled_toPartial_refines_unchecked_iff (u : UintTy) (k : Nat)
    (strat : PanicStrategy) (a b : Nat) :
    (mirCallTree (mkUncheckedAddScaledBody u k) (uintArgs2 u a b)).toPartial ≤
      (mirCallTree (mkCheckedAddScaledBody u k strat.toUnwindAction) (uintArgs2 u a b)).toPartial
      ↔ a + k * b < modPow2 (uintWidth u) :=
  toPartial_reverse_iff_of_dichotomy (fC := 13) (fU := 5) (lt_dec _ _)
    (fun h => ⟨_, runMirCall_checked_add_scaled_ok u k strat a b h,
                  runMirCall_unchecked_add_scaled_ok u k a b h⟩)
    (fun h => ⟨_, runMirCall_checked_add_scaled_trap u k strat a b (Nat.not_lt.mp h),
                  runMirCall_unchecked_add_scaled_ub u k a b (Nat.not_lt.mp h)⟩)

/-- Coinductive `WeakRef` tree-level reverse `iff` for `add`, `in-range sub`, `mul`, and
composite `add_scaled`. -/
theorem checked_toWeakRef_refines_unchecked_iff (u : UintTy) (strat : PanicStrategy)
    (a b k : Nat) (ha : a < modPow2 (uintWidth u)) (hb : b < modPow2 (uintWidth u)) :
    (WeakRef (mirCallTree (mkUncheckedArithBody u .add) (uintArgs2 u a b))
        (mirCallTree (mkCheckedArithBody u .add strat.toUnwindAction) (uintArgs2 u a b))
      ↔ a + b < modPow2 (uintWidth u)) ∧
    (WeakRef (mirCallTree (mkUncheckedArithBody u .sub) (uintArgs2 u a b))
        (mirCallTree (mkCheckedArithBody u .sub strat.toUnwindAction) (uintArgs2 u a b))
      ↔ b ≤ a) ∧
    (WeakRef (mirCallTree (mkUncheckedArithBody u .mul) (uintArgs2 u a b))
        (mirCallTree (mkCheckedArithBody u .mul strat.toUnwindAction) (uintArgs2 u a b))
      ↔ a * b < modPow2 (uintWidth u)) ∧
    (WeakRef (mirCallTree (mkUncheckedAddScaledBody u k) (uintArgs2 u a b))
        (mirCallTree (mkCheckedAddScaledBody u k strat.toUnwindAction) (uintArgs2 u a b))
      ↔ a + k * b < modPow2 (uintWidth u)) :=
  ⟨weakRef_reverse_iff_of_dichotomy (fC := 6) (fU := 2) (lt_dec _ _)
    (fun h => ⟨_, runMirCall_checked_add_ok u strat a b h, runMirCall_unchecked_add_ok u a b h⟩)
    (fun h => ⟨_, runMirCall_checked_add_trap u strat a b (Nat.not_lt.mp h),
                  runMirCall_unchecked_add_ub u a b (Nat.not_lt.mp h)⟩),
   weakRef_reverse_iff_of_dichotomy (fC := 6) (fU := 2) (le_dec _ _)
    (fun h => ⟨_, runMirCall_checked_sub_ok u strat a b ha hb h,
                  runMirCall_unchecked_sub_ok u a b ha h⟩)
    (fun h => ⟨_, runMirCall_checked_sub_trap u strat a b ha hb (Nat.not_le.mp h),
                  runMirCall_unchecked_sub_ub u a b (Nat.not_le.mp h)⟩),
   weakRef_reverse_iff_of_dichotomy (fC := 6) (fU := 2) (lt_dec _ _)
    (fun h => ⟨_, runMirCall_checked_mul_ok u strat a b h, runMirCall_unchecked_mul_ok u a b h⟩)
    (fun h => ⟨_, runMirCall_checked_mul_trap u strat a b (Nat.not_lt.mp h),
                  runMirCall_unchecked_mul_ub u a b (Nat.not_lt.mp h)⟩),
   weakRef_reverse_iff_of_dichotomy (fC := 13) (fU := 5) (lt_dec _ _)
    (fun h => ⟨_, runMirCall_checked_add_scaled_ok u k strat a b h,
                  runMirCall_unchecked_add_scaled_ok u k a b h⟩)
    (fun h => ⟨_, runMirCall_checked_add_scaled_trap u k strat a b (Nat.not_lt.mp h),
                  runMirCall_unchecked_add_scaled_ub u k a b (Nat.not_lt.mp h)⟩)⟩

/-! ## 6. Explicit Non-Vacuous Negative Soundness Theorems (17 Theorems) -/

/-- Negative Soundness #1: a deterministic trap never refines a normal return. -/
theorem trap_not_refines_ret {Val : Type} (v : Val) :
    ¬ MirOutcomeRefines .trap (.ret v) :=
  fun h => False.elim h

/-- Negative Soundness #2: a deterministic trap never refines undefined behavior. -/
theorem trap_not_refines_ub {Val : Type} :
    ¬ MirOutcomeRefines (Val := Val) .trap .ub :=
  fun h => False.elim h

/-- Negative Soundness #3: a deterministic trap never refines an unsupported outcome. -/
theorem trap_not_refines_unsupported {Val : Type} :
    ¬ MirOutcomeRefines (Val := Val) .trap .unsupported :=
  fun h => False.elim h

/-- Negative Soundness #4: a normal return never refines undefined behavior. -/
theorem ret_not_refines_ub {Val : Type} (v : Val) :
    ¬ MirOutcomeRefines (.ret v) .ub :=
  fun h => False.elim h

/-- Negative Soundness #5: a normal return never refines a deterministic trap. -/
theorem ret_not_refines_trap {Val : Type} (v : Val) :
    ¬ MirOutcomeRefines (.ret v) .trap :=
  fun h => False.elim h

/-- Negative Soundness #6: a normal return never refines an unsupported outcome. -/
theorem ret_not_refines_unsupported {Val : Type} (v : Val) :
    ¬ MirOutcomeRefines (.ret v) .unsupported :=
  fun h => False.elim h

/-- Negative Soundness #7: distinct normal return values never refine each other. -/
theorem ret_distinct_not_refines {Val : Type} {v₁ v₂ : Val} (hne : v₁ ≠ v₂) :
    ¬ MirOutcomeRefines (.ret v₁) (.ret v₂) :=
  fun h => hne h

/-- Negative Soundness #8: concrete `stepMirState` counterexample on `u8` (`200 + 100 = 300 ≥ 256`):
checked addition traps while unchecked addition faults `.ub`, so `checked ⊑ unchecked` is FALSE
under both `-C panic=abort` and `-C panic=unwind` (and under Layer 1A `ITree.toPartial`). -/
theorem checked_add_overflow_not_refines_unchecked (strat : PanicStrategy) :
    runMirCall (mkCheckedArithBody .u8 .add strat.toUnwindAction) 6 (uintArgs2 .u8 200 100) =
      .halted strat.toTrapOutcome ∧
    runMirCall (mkUncheckedArithBody .u8 .add) 2 (uintArgs2 .u8 200 100) = .faulted .ub ∧
    ¬ MirOutcomeRefines
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody .u8 .add strat.toUnwindAction) 6 (uintArgs2 .u8 200 100)))
      (classifyMirExecState strat
        (runMirCall (mkUncheckedArithBody .u8 .add) 2 (uintArgs2 .u8 200 100))) ∧
    ¬ ((mirCallTree (mkUncheckedArithBody .u8 .add) (uintArgs2 .u8 200 100)).toPartial ≤
       (mirCallTree (mkCheckedArithBody .u8 .add strat.toUnwindAction) (uintArgs2 .u8 200 100)).toPartial) := by
  have hOv : modPow2 (uintWidth .u8) ≤ 200 + 100 := Nat.le_of_ble_eq_true rfl
  have hC := runMirCall_checked_add_trap .u8 strat 200 100 hOv
  have hU := runMirCall_unchecked_add_ub .u8 200 100 hOv
  have ⟨uC, hTauC, hObsC⟩ := runMirSteps_halted_to_tauStar _ 6 _ _ hC
  refine ⟨hC, hU, ?_, ?_⟩
  · rw [hC, hU, classify_trapOutcome_eq strat]
    exact trap_not_refines_ub
  · exact not_toPartial_le_of_faultNow_ret (runMirCall_ub_faultNow hU) hTauC hObsC

/-- Negative Soundness #9: concrete `stepMirState` counterexample on `u8` (`200 + 100`):
checked addition traps while wrapping addition returns `44` (`300 mod 256`), so replacing
checked addition with wrapping addition violates panic preservation (`¬ (checked ⊑ wrapping)`
and `¬ toPartial ≤`). -/
theorem checked_add_overflow_not_refines_wrapping (strat : PanicStrategy) :
    runMirCall (mkCheckedArithBody .u8 .add strat.toUnwindAction) 6 (uintArgs2 .u8 200 100) =
      .halted strat.toTrapOutcome ∧
    runMirCall (mkWrappingArithBody .u8 .add) 2 (uintArgs2 .u8 200 100) =
      .halted (.normal (.scalar ⟨44, 1⟩, canonInitMemory)) ∧
    ¬ MirOutcomeRefines
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody .u8 .add strat.toUnwindAction) 6 (uintArgs2 .u8 200 100)))
      (classifyMirExecState strat
        (runMirCall (mkWrappingArithBody .u8 .add) 2 (uintArgs2 .u8 200 100))) ∧
    ¬ ((mirCallTree (mkWrappingArithBody .u8 .add) (uintArgs2 .u8 200 100)).toPartial ≤
       (mirCallTree (mkCheckedArithBody .u8 .add strat.toUnwindAction) (uintArgs2 .u8 200 100)).toPartial) := by
  have hOv : modPow2 (uintWidth .u8) ≤ 200 + 100 := Nat.le_of_ble_eq_true rfl
  have hC := runMirCall_checked_add_trap .u8 strat 200 100 hOv
  have hW : runMirCall (mkWrappingArithBody .u8 .add) 2 (uintArgs2 .u8 200 100) =
      .halted (.normal (.scalar ⟨44, 1⟩, canonInitMemory)) :=
    runMirCall_wrapping_add .u8 200 100
  have ⟨uC, hTauC, hObsC⟩ := runMirSteps_halted_to_tauStar _ 6 _ _ hC
  have ⟨uW, hTauW, hObsW⟩ := runMirSteps_halted_to_tauStar _ 2 _ _ hW
  refine ⟨hC, hW, ?_, ?_⟩
  · rw [hC, hW, classify_trapOutcome_eq strat]
    exact trap_not_refines_ret _
  · refine not_toPartial_le_of_distinct_ret hTauW hObsW hTauC hObsC ?_
    cases strat <;> intro hEq <;> nomatch hEq

/-- Negative Soundness #10: concrete `stepMirState` counterexample on `u8` (`3 - 5`):
checked subtraction traps while wrapping subtraction returns `254`, so `¬ (checked ⊑ wrapping)`
and `¬ toPartial ≤`. -/
theorem checked_sub_underflow_not_refines_wrapping (strat : PanicStrategy) :
    runMirCall (mkCheckedArithBody .u8 .sub strat.toUnwindAction) 6 (uintArgs2 .u8 3 5) =
      .halted strat.toTrapOutcome ∧
    runMirCall (mkWrappingArithBody .u8 .sub) 2 (uintArgs2 .u8 3 5) =
      .halted (.normal (.scalar ⟨254, 1⟩, canonInitMemory)) ∧
    ¬ MirOutcomeRefines
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody .u8 .sub strat.toUnwindAction) 6 (uintArgs2 .u8 3 5)))
      (classifyMirExecState strat
        (runMirCall (mkWrappingArithBody .u8 .sub) 2 (uintArgs2 .u8 3 5))) ∧
    ¬ ((mirCallTree (mkWrappingArithBody .u8 .sub) (uintArgs2 .u8 3 5)).toPartial ≤
       (mirCallTree (mkCheckedArithBody .u8 .sub strat.toUnwindAction) (uintArgs2 .u8 3 5)).toPartial) := by
  have ha : 3 < modPow2 (uintWidth .u8) := Nat.le_of_ble_eq_true rfl
  have hb : 5 < modPow2 (uintWidth .u8) := Nat.le_of_ble_eq_true rfl
  have hUnd : 3 < 5 := Nat.le_of_ble_eq_true rfl
  have hC := runMirCall_checked_sub_trap .u8 strat 3 5 ha hb hUnd
  have hW : runMirCall (mkWrappingArithBody .u8 .sub) 2 (uintArgs2 .u8 3 5) =
      .halted (.normal (.scalar ⟨254, 1⟩, canonInitMemory)) :=
    runMirCall_wrapping_sub .u8 3 5 ha hb
  have ⟨uC, hTauC, hObsC⟩ := runMirSteps_halted_to_tauStar _ 6 _ _ hC
  have ⟨uW, hTauW, hObsW⟩ := runMirSteps_halted_to_tauStar _ 2 _ _ hW
  refine ⟨hC, hW, ?_, ?_⟩
  · rw [hC, hW, classify_trapOutcome_eq strat]
    exact trap_not_refines_ret _
  · refine not_toPartial_le_of_distinct_ret hTauW hObsW hTauC hObsC ?_
    cases strat <;> intro hEq <;> nomatch hEq

/-- Negative Soundness #11: concrete `stepMirState` counterexample on `u8` (`20 * 20 = 400`):
checked multiplication traps while wrapping multiplication returns `144` (`400 mod 256`),
so `¬ (checked ⊑ wrapping)` and `¬ toPartial ≤`. -/
theorem checked_mul_overflow_not_refines_wrapping (strat : PanicStrategy) :
    runMirCall (mkCheckedArithBody .u8 .mul strat.toUnwindAction) 6 (uintArgs2 .u8 20 20) =
      .halted strat.toTrapOutcome ∧
    runMirCall (mkWrappingArithBody .u8 .mul) 2 (uintArgs2 .u8 20 20) =
      .halted (.normal (.scalar ⟨144, 1⟩, canonInitMemory)) ∧
    ¬ MirOutcomeRefines
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody .u8 .mul strat.toUnwindAction) 6 (uintArgs2 .u8 20 20)))
      (classifyMirExecState strat
        (runMirCall (mkWrappingArithBody .u8 .mul) 2 (uintArgs2 .u8 20 20))) ∧
    ¬ ((mirCallTree (mkWrappingArithBody .u8 .mul) (uintArgs2 .u8 20 20)).toPartial ≤
       (mirCallTree (mkCheckedArithBody .u8 .mul strat.toUnwindAction) (uintArgs2 .u8 20 20)).toPartial) := by
  have hOv : modPow2 (uintWidth .u8) ≤ 20 * 20 := Nat.le_of_ble_eq_true rfl
  have hC := runMirCall_checked_mul_trap .u8 strat 20 20 hOv
  have hW : runMirCall (mkWrappingArithBody .u8 .mul) 2 (uintArgs2 .u8 20 20) =
      .halted (.normal (.scalar ⟨144, 1⟩, canonInitMemory)) :=
    runMirCall_wrapping_mul .u8 20 20
  have ⟨uC, hTauC, hObsC⟩ := runMirSteps_halted_to_tauStar _ 6 _ _ hC
  have ⟨uW, hTauW, hObsW⟩ := runMirSteps_halted_to_tauStar _ 2 _ _ hW
  refine ⟨hC, hW, ?_, ?_⟩
  · rw [hC, hW, classify_trapOutcome_eq strat]
    exact trap_not_refines_ret _
  · refine not_toPartial_le_of_distinct_ret hTauW hObsW hTauC hObsC ?_
    cases strat <;> intro hEq <;> nomatch hEq

/-- Negative Soundness #12: concrete `stepMirState` counterexample on `u8` (`3 - 5`):
checked subtraction traps while unchecked subtraction faults `.ub`, so `¬ (checked ⊑ unchecked)`
and `¬ toPartial ≤`. -/
theorem checked_sub_underflow_not_refines_unchecked (strat : PanicStrategy) :
    runMirCall (mkCheckedArithBody .u8 .sub strat.toUnwindAction) 6 (uintArgs2 .u8 3 5) =
      .halted strat.toTrapOutcome ∧
    runMirCall (mkUncheckedArithBody .u8 .sub) 2 (uintArgs2 .u8 3 5) = .faulted .ub ∧
    ¬ MirOutcomeRefines
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody .u8 .sub strat.toUnwindAction) 6 (uintArgs2 .u8 3 5)))
      (classifyMirExecState strat
        (runMirCall (mkUncheckedArithBody .u8 .sub) 2 (uintArgs2 .u8 3 5))) ∧
    ¬ ((mirCallTree (mkUncheckedArithBody .u8 .sub) (uintArgs2 .u8 3 5)).toPartial ≤
       (mirCallTree (mkCheckedArithBody .u8 .sub strat.toUnwindAction) (uintArgs2 .u8 3 5)).toPartial) := by
  have ha : 3 < modPow2 (uintWidth .u8) := Nat.le_of_ble_eq_true rfl
  have hb : 5 < modPow2 (uintWidth .u8) := Nat.le_of_ble_eq_true rfl
  have hUnd : 3 < 5 := Nat.le_of_ble_eq_true rfl
  have hC := runMirCall_checked_sub_trap .u8 strat 3 5 ha hb hUnd
  have hU := runMirCall_unchecked_sub_ub .u8 3 5 hUnd
  have ⟨uC, hTauC, hObsC⟩ := runMirSteps_halted_to_tauStar _ 6 _ _ hC
  refine ⟨hC, hU, ?_, ?_⟩
  · rw [hC, hU, classify_trapOutcome_eq strat]
    exact trap_not_refines_ub
  · exact not_toPartial_le_of_faultNow_ret (runMirCall_ub_faultNow hU) hTauC hObsC

/-- Negative Soundness #13: concrete `stepMirState` counterexample on `u8` (`20 * 20 = 400`):
checked multiplication traps while unchecked multiplication faults `.ub`, so
`¬ (checked ⊑ unchecked)` and `¬ toPartial ≤`. -/
theorem checked_mul_overflow_not_refines_unchecked (strat : PanicStrategy) :
    runMirCall (mkCheckedArithBody .u8 .mul strat.toUnwindAction) 6 (uintArgs2 .u8 20 20) =
      .halted strat.toTrapOutcome ∧
    runMirCall (mkUncheckedArithBody .u8 .mul) 2 (uintArgs2 .u8 20 20) = .faulted .ub ∧
    ¬ MirOutcomeRefines
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody .u8 .mul strat.toUnwindAction) 6 (uintArgs2 .u8 20 20)))
      (classifyMirExecState strat
        (runMirCall (mkUncheckedArithBody .u8 .mul) 2 (uintArgs2 .u8 20 20))) ∧
    ¬ ((mirCallTree (mkUncheckedArithBody .u8 .mul) (uintArgs2 .u8 20 20)).toPartial ≤
       (mirCallTree (mkCheckedArithBody .u8 .mul strat.toUnwindAction) (uintArgs2 .u8 20 20)).toPartial) := by
  have hOv : modPow2 (uintWidth .u8) ≤ 20 * 20 := Nat.le_of_ble_eq_true rfl
  have hC := runMirCall_checked_mul_trap .u8 strat 20 20 hOv
  have hU := runMirCall_unchecked_mul_ub .u8 20 20 hOv
  have ⟨uC, hTauC, hObsC⟩ := runMirSteps_halted_to_tauStar _ 6 _ _ hC
  refine ⟨hC, hU, ?_, ?_⟩
  · rw [hC, hU, classify_trapOutcome_eq strat]
    exact trap_not_refines_ub
  · exact not_toPartial_le_of_faultNow_ret (runMirCall_ub_faultNow hU) hTauC hObsC

/-- Negative Soundness #14: `-C panic=abort` (`UnwindAction.terminate`) vs. `-C panic=unwind`
(`UnwindAction.continue_`) produce strictly distinct trap outcomes (`.trap .abort` vs.
`.trap .panic`) on overflowing `u8` addition `200 + 100`: neither refines the other under
`MirExactOutcomeRefines` nor under Layer 1A `ITree.toPartial`. -/
theorem panic_strategy_abort_vs_unwind_distinct :
    runMirCall (mkCheckedArithBody .u8 .add .terminate) 6 (uintArgs2 .u8 200 100) =
      .halted .abort ∧
    runMirCall (mkCheckedArithBody .u8 .add .continue_) 6 (uintArgs2 .u8 200 100) =
      .halted .panic ∧
    ¬ MirExactOutcomeRefines
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u8 .add .terminate) 6 (uintArgs2 .u8 200 100)))
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u8 .add .continue_) 6 (uintArgs2 .u8 200 100))) ∧
    ¬ MirExactOutcomeRefines
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u8 .add .continue_) 6 (uintArgs2 .u8 200 100)))
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u8 .add .terminate) 6 (uintArgs2 .u8 200 100))) ∧
    ¬ ((mirCallTree (mkCheckedArithBody .u8 .add .continue_) (uintArgs2 .u8 200 100)).toPartial ≤
       (mirCallTree (mkCheckedArithBody .u8 .add .terminate) (uintArgs2 .u8 200 100)).toPartial) ∧
    ¬ ((mirCallTree (mkCheckedArithBody .u8 .add .terminate) (uintArgs2 .u8 200 100)).toPartial ≤
       (mirCallTree (mkCheckedArithBody .u8 .add .continue_) (uintArgs2 .u8 200 100)).toPartial) := by
  have hOv : modPow2 (uintWidth .u8) ≤ 200 + 100 := Nat.le_of_ble_eq_true rfl
  have hA := runMirCall_checked_add_trap .u8 .abort 200 100 hOv
  have hP := runMirCall_checked_add_trap .u8 .unwind 200 100 hOv
  dsimp only [PanicStrategy.toUnwindAction, PanicStrategy.toTrapOutcome] at hA hP
  have ⟨uA, hTauA, hObsA⟩ := runMirSteps_halted_to_tauStar _ 6 _ _ hA
  have ⟨uP, hTauP, hObsP⟩ := runMirSteps_halted_to_tauStar _ 6 _ _ hP
  refine ⟨hA, hP, ?_, ?_, ?_, ?_⟩
  · rw [hA, hP]
    intro hEq
    nomatch hEq
  · rw [hA, hP]
    intro hEq
    nomatch hEq
  · exact not_toPartial_le_of_distinct_ret hTauP hObsP hTauA hObsA (fun h => nomatch h)
  · exact not_toPartial_le_of_distinct_ret hTauA hObsA hTauP hObsP (fun h => nomatch h)

/-- Negative Soundness #15: composite `add_scaled` (`a + 4 * b`) overflow counterexample on `u8`
(`200 + 4 * 20 = 280 ≥ 256`, where the inner multiplication `4 * 20 = 80` succeeds while the
outer addition overflows): checked traps, unchecked faults `.ub`, so `¬ (checked ⊑ unchecked)`
and `¬ toPartial ≤`. -/
theorem checked_add_scaled_overflow_not_refines_unchecked (strat : PanicStrategy) :
    runMirCall (mkCheckedAddScaledBody .u8 4 strat.toUnwindAction) 13 (uintArgs2 .u8 200 20) =
      .halted strat.toTrapOutcome ∧
    runMirCall (mkUncheckedAddScaledBody .u8 4) 5 (uintArgs2 .u8 200 20) = .faulted .ub ∧
    ¬ MirOutcomeRefines
      (classifyMirExecState strat
        (runMirCall (mkCheckedAddScaledBody .u8 4 strat.toUnwindAction) 13 (uintArgs2 .u8 200 20)))
      (classifyMirExecState strat
        (runMirCall (mkUncheckedAddScaledBody .u8 4) 5 (uintArgs2 .u8 200 20))) ∧
    ¬ ((mirCallTree (mkUncheckedAddScaledBody .u8 4) (uintArgs2 .u8 200 20)).toPartial ≤
       (mirCallTree (mkCheckedAddScaledBody .u8 4 strat.toUnwindAction) (uintArgs2 .u8 200 20)).toPartial) := by
  have hOv : modPow2 (uintWidth .u8) ≤ 200 + 4 * 20 := Nat.le_of_ble_eq_true rfl
  have hC := runMirCall_checked_add_scaled_trap .u8 4 strat 200 20 hOv
  have hU := runMirCall_unchecked_add_scaled_ub .u8 4 200 20 hOv
  have ⟨uC, hTauC, hObsC⟩ := runMirSteps_halted_to_tauStar _ 13 _ _ hC
  refine ⟨hC, hU, ?_, ?_⟩
  · rw [hC, hU, classify_trapOutcome_eq strat]
    exact trap_not_refines_ub
  · exact not_toPartial_le_of_faultNow_ret (runMirCall_ub_faultNow hU) hTauC hObsC

/-- Negative Soundness #16: tightness of the LHS range hypothesis `ha : a < 2^w` in
`checked_sub_refines_unchecked_iff`. On `u8` with `a = 300 ≥ 256` and `b = 10`, `b ≤ a` holds,
yet `subWithOverflow` wraps `300 - 10 = 290` to `34` with `ov = false` and returns `34`, whereas
`subUnchecked` checks `256 ≤ 290` and faults `.ub`. Hence `¬ (checked_sub ⊑ unchecked_sub)` and
`¬ toPartial ≤`, proving the range hypothesis (or certified range proof) is strictly necessary. -/
theorem checked_sub_out_of_range_lhs_not_refines_unchecked (strat : PanicStrategy) :
    10 ≤ 300 ∧
    runMirCall (mkCheckedArithBody .u8 .sub strat.toUnwindAction) 6 (uintArgs2 .u8 300 10) =
      .halted (.normal (.scalar ⟨34, 1⟩, canonInitMemory)) ∧
    runMirCall (mkUncheckedArithBody .u8 .sub) 2 (uintArgs2 .u8 300 10) = .faulted .ub ∧
    ¬ MirOutcomeRefines
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody .u8 .sub strat.toUnwindAction) 6 (uintArgs2 .u8 300 10)))
      (classifyMirExecState strat
        (runMirCall (mkUncheckedArithBody .u8 .sub) 2 (uintArgs2 .u8 300 10))) ∧
    ¬ ((mirCallTree (mkUncheckedArithBody .u8 .sub) (uintArgs2 .u8 300 10)).toPartial ≤
       (mirCallTree (mkCheckedArithBody .u8 .sub strat.toUnwindAction)
         (uintArgs2 .u8 300 10)).toPartial) := by
  have hC : runMirCall (mkCheckedArithBody .u8 .sub strat.toUnwindAction) 6 (uintArgs2 .u8 300 10) =
      .halted (.normal (.scalar ⟨34, 1⟩, canonInitMemory)) := by
    cases strat <;> rfl
  have hU : runMirCall (mkUncheckedArithBody .u8 .sub) 2 (uintArgs2 .u8 300 10) =
      .faulted .ub := rfl
  have ⟨uC, hTauC, hObsC⟩ := runMirSteps_halted_to_tauStar _ 6 _ _ hC
  refine ⟨Nat.le_of_ble_eq_true rfl, hC, hU, ?_, ?_⟩
  · rw [hC, hU]
    exact ret_not_refines_ub _
  · exact not_toPartial_le_of_faultNow_ret (runMirCall_ub_faultNow hU) hTauC hObsC

/-- Negative Soundness #17: inner-multiplication failure site of composite `add_scaled`
(`a + 4 * b`) on `u8` (`a = 1, b = 70`, where the inner product `4 * 70 = 280 ≥ 256` overflows
at `bb0` BEFORE `bb1`'s outer addition is ever reached): checked traps at `bb0`'s assert,
unchecked faults `.ub` at `bb0`'s `mulUnchecked`, so `¬ (checked ⊑ unchecked)` and
`¬ toPartial ≤`. Complements #15 (which triggers the outer-add failure site in `bb1`). -/
theorem checked_add_scaled_inner_mul_overflow_not_refines_unchecked (strat : PanicStrategy) :
    modPow2 (uintWidth .u8) ≤ 4 * 70 ∧
    runMirCall (mkCheckedAddScaledBody .u8 4 strat.toUnwindAction) 13 (uintArgs2 .u8 1 70) =
      .halted strat.toTrapOutcome ∧
    runMirCall (mkUncheckedAddScaledBody .u8 4) 5 (uintArgs2 .u8 1 70) = .faulted .ub ∧
    ¬ MirOutcomeRefines
      (classifyMirExecState strat
        (runMirCall (mkCheckedAddScaledBody .u8 4 strat.toUnwindAction) 13 (uintArgs2 .u8 1 70)))
      (classifyMirExecState strat
        (runMirCall (mkUncheckedAddScaledBody .u8 4) 5 (uintArgs2 .u8 1 70))) ∧
    ¬ ((mirCallTree (mkUncheckedAddScaledBody .u8 4) (uintArgs2 .u8 1 70)).toPartial ≤
       (mirCallTree (mkCheckedAddScaledBody .u8 4 strat.toUnwindAction)
         (uintArgs2 .u8 1 70)).toPartial) := by
  have hInnerOv : modPow2 (uintWidth .u8) ≤ 4 * 70 := Nat.le_of_ble_eq_true rfl
  have hOv : modPow2 (uintWidth .u8) ≤ 1 + 4 * 70 := Nat.le_of_ble_eq_true rfl
  have hC := runMirCall_checked_add_scaled_trap .u8 4 strat 1 70 hOv
  have hU := runMirCall_unchecked_add_scaled_ub .u8 4 1 70 hOv
  have ⟨uC, hTauC, hObsC⟩ := runMirSteps_halted_to_tauStar _ 13 _ _ hC
  refine ⟨hInnerOv, hC, hU, ?_, ?_⟩
  · rw [hC, hU, classify_trapOutcome_eq strat]
    exact trap_not_refines_ub
  · exact not_toPartial_le_of_faultNow_ret (runMirCall_ub_faultNow hU) hTauC hObsC

set_option maxHeartbeats 4000000 in
/-- Exact failure-site pinning for composite `add_scaled` (strengthening #15 and #17, whose
generic trap/UB lemmas do not by themselves identify WHICH check fires). Fuel acts as a
step counter, so the exact step at which each run settles identifies the failing statement:
- inner-mul site (`1 + 4 * 70`): checked is still running after 2 steps and traps at step 3
  (`bb0`'s assert); unchecked is still running after 1 step and faults `.ub` at step 2
  (`bb0`'s `MulUnchecked`);
- outer-add site (`200 + 4 * 20`): checked passes `bb0`'s assert, is still running after 8
  steps and traps at step 9 (`bb1`'s assert); unchecked is still running after 2 steps and
  faults `.ub` at step 3 (`bb0`'s `AddUnchecked`). -/
theorem add_scaled_failure_sites_pinned (strat : PanicStrategy) :
    runMirCall (mkCheckedAddScaledBody .u8 4 strat.toUnwindAction) 2 (uintArgs2 .u8 1 70) =
      .faulted .outOfFuel ∧
    runMirCall (mkCheckedAddScaledBody .u8 4 strat.toUnwindAction) 3 (uintArgs2 .u8 1 70) =
      .halted strat.toTrapOutcome ∧
    runMirCall (mkUncheckedAddScaledBody .u8 4) 1 (uintArgs2 .u8 1 70) = .faulted .outOfFuel ∧
    runMirCall (mkUncheckedAddScaledBody .u8 4) 2 (uintArgs2 .u8 1 70) = .faulted .ub ∧
    runMirCall (mkCheckedAddScaledBody .u8 4 strat.toUnwindAction) 8 (uintArgs2 .u8 200 20) =
      .faulted .outOfFuel ∧
    runMirCall (mkCheckedAddScaledBody .u8 4 strat.toUnwindAction) 9 (uintArgs2 .u8 200 20) =
      .halted strat.toTrapOutcome ∧
    runMirCall (mkUncheckedAddScaledBody .u8 4) 2 (uintArgs2 .u8 200 20) = .faulted .outOfFuel ∧
    runMirCall (mkUncheckedAddScaledBody .u8 4) 3 (uintArgs2 .u8 200 20) = .faulted .ub := by
  cases strat <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- Coinductive `WeakRef` negative soundness corollaries (overflowing add & strategy separation). -/
theorem checked_add_overflow_not_weakRef_corollaries (strat : PanicStrategy) :
    ¬ WeakRef
      (mirCallTree (mkUncheckedArithBody .u8 .add) (uintArgs2 .u8 200 100))
      (mirCallTree (mkCheckedArithBody .u8 .add strat.toUnwindAction) (uintArgs2 .u8 200 100)) ∧
    ¬ WeakRef
      (mirCallTree (mkWrappingArithBody .u8 .add) (uintArgs2 .u8 200 100))
      (mirCallTree (mkCheckedArithBody .u8 .add strat.toUnwindAction) (uintArgs2 .u8 200 100)) ∧
    ¬ WeakRef
      (mirCallTree (mkCheckedArithBody .u8 .add .continue_) (uintArgs2 .u8 200 100))
      (mirCallTree (mkCheckedArithBody .u8 .add .terminate) (uintArgs2 .u8 200 100)) := by
  have hOv : modPow2 (uintWidth .u8) ≤ 200 + 100 := Nat.le_of_ble_eq_true rfl
  have hC := runMirCall_checked_add_trap .u8 strat 200 100 hOv
  have hU := runMirCall_unchecked_add_ub .u8 200 100 hOv
  have hW := runMirCall_wrapping_add .u8 200 100
  have hA := runMirCall_checked_add_trap .u8 .abort 200 100 hOv
  have hP := runMirCall_checked_add_trap .u8 .unwind 200 100 hOv
  dsimp only [PanicStrategy.toUnwindAction, PanicStrategy.toTrapOutcome] at hA hP
  have ⟨uC, hTauC, hObsC⟩ := runMirSteps_halted_to_tauStar _ 6 _ _ hC
  have ⟨uW, hTauW, hObsW⟩ := runMirSteps_halted_to_tauStar _ 2 _ _ hW
  have ⟨uA, hTauA, hObsA⟩ := runMirSteps_halted_to_tauStar _ 6 _ _ hA
  have ⟨uP, hTauP, hObsP⟩ := runMirSteps_halted_to_tauStar _ 6 _ _ hP
  refine ⟨not_weakRef_of_faultNow_ret (runMirCall_ub_faultNow hU) hTauC hObsC, ?_, ?_⟩
  · refine not_weakRef_of_distinct_ret hTauW hObsW hTauC hObsC ?_
    cases strat <;> intro hEq <;> nomatch hEq
  · exact not_weakRef_of_distinct_ret hTauP hObsP hTauA hObsA (fun h => nomatch h)

end Anneal.Mir.OverflowTrapRefinement
